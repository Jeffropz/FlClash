//! The icon belongs to a hidden top-level window on a thread of its own: a
//! message-only window would miss `TaskbarCreated` and power broadcasts, and
//! `TrackPopupMenu` blocks the thread it runs on.

use super::emit;
use crate::api::tray::{TrayContent, TrayItem, TrayItemKind, TraySignalKind};
use std::mem::{size_of, zeroed};
use std::ptr::{null, null_mut};
use std::sync::{mpsc, Mutex, MutexGuard, OnceLock, PoisonError};

use windows_sys::core::PCSTR;
use windows_sys::Win32::Foundation::{
    ERROR_SUCCESS, HWND, LPARAM, LRESULT, POINT, RECT, SIZE, WPARAM,
};
use windows_sys::Win32::Globalization::lstrcmpW;
use windows_sys::Win32::Graphics::Gdi::{
    CreateCompatibleDC, CreateDIBSection, CreateFontW, DeleteDC, DeleteObject, DrawTextW, GdiFlush,
    GetDC, ReleaseDC, SelectObject, SetBkMode, SetTextColor, ValidateRect, AC_SRC_ALPHA,
    AC_SRC_OVER, ANTIALIASED_QUALITY, BITMAPINFO, BITMAPINFOHEADER, BI_RGB, BLENDFUNCTION,
    CLIP_DEFAULT_PRECIS, DEFAULT_CHARSET, DEFAULT_PITCH, DIB_RGB_COLORS, DT_NOPREFIX, DT_RIGHT,
    DT_SINGLELINE, DT_VCENTER, FF_DONTCARE, OUT_DEFAULT_PRECIS, TRANSPARENT,
};
use windows_sys::Win32::System::LibraryLoader::{
    GetModuleHandleW, GetProcAddress, LoadLibraryExW, LOAD_LIBRARY_SEARCH_SYSTEM32,
};
use windows_sys::Win32::System::Registry::{RegGetValueW, HKEY_CURRENT_USER, RRF_RT_REG_DWORD};
use windows_sys::Win32::System::SystemInformation::OSVERSIONINFOW;
use windows_sys::Win32::UI::HiDpi::GetDpiForWindow;
use windows_sys::Win32::UI::Shell::{
    Shell_NotifyIconW, NIF_ICON, NIF_MESSAGE, NIF_TIP, NIM_ADD, NIM_DELETE, NIM_MODIFY,
    NOTIFYICONDATAW,
};
use windows_sys::Win32::UI::WindowsAndMessaging::{
    AppendMenuW, CreatePopupMenu, CreateWindowExW, DefWindowProcW, DestroyIcon, DestroyMenu,
    DispatchMessageW, FindWindowExW, FindWindowW, GetCursorPos, GetMessageW, GetSystemMetrics,
    GetWindowRect, IsChild, IsWindowVisible, KillTimer, LoadImageW, PostMessageW, RegisterClassW,
    RegisterWindowMessageW, SetForegroundWindow, SetTimer, ShowWindow, TrackPopupMenu,
    TranslateMessage, UpdateLayeredWindow, WindowFromPoint, HICON, HMENU, IMAGE_ICON,
    LR_LOADFROMFILE, MF_CHECKED, MF_GRAYED, MF_POPUP, MF_SEPARATOR, MF_STRING, MF_UNCHECKED, MSG,
    PBT_APMRESUMEAUTOMATIC, PBT_APMRESUMESUSPEND, SM_CXSMICON, SM_CYSCREEN, SM_CYSMICON, SW_HIDE,
    SW_SHOWNOACTIVATE, TPM_BOTTOMALIGN, TPM_LEFTALIGN, TPM_RETURNCMD, TPM_RIGHTBUTTON, ULW_ALPHA,
    WM_APP, WM_ERASEBKGND, WM_LBUTTONUP, WM_NULL, WM_PAINT, WM_POWERBROADCAST, WM_RBUTTONUP,
    WM_SETTINGCHANGE, WM_TIMER, WNDCLASSW, WS_EX_LAYERED, WS_EX_NOACTIVATE, WS_EX_TOOLWINDOW,
    WS_EX_TOPMOST, WS_OVERLAPPED, WS_POPUP,
};

const WM_TRAY: u32 = WM_APP + 1;
const WM_OPEN_MENU: u32 = WM_APP + 2;
const WM_RETRY: u32 = WM_APP + 3;
const WM_TITLE: u32 = WM_APP + 4;
const ICON_ID: u32 = 1;
const RETRY_TIMER: usize = 1;
const TITLE_TIMER: usize = 2;
const RETRY_INTERVAL_MS: u32 = 2000;
const TITLE_INTERVAL_MS: u32 = 1000;
const TITLE_WIDTH: i32 = 128;
const TITLE_HEIGHT: i32 = 38;
const TITLE_GAP: i32 = 6;
const TITLE_FONT_HEIGHT: i32 = 12;
// SetPreferredAppMode and FlushMenuThemes, the undocumented uxtheme ordinals
// Explorer uses for dark Win32 menus, exist from 1903 on.
const FIRST_DARK_MENU_BUILD: u32 = 18362;
const SET_PREFERRED_APP_MODE: usize = 135;
const FLUSH_MENU_THEMES: usize = 136;
const ALLOW_DARK: i32 = 1;

struct Icon(HICON);

// An HICON is a process-wide handle, not tied to the thread that loaded it.
unsafe impl Send for Icon {}

impl Drop for Icon {
    fn drop(&mut self) {
        unsafe { DestroyIcon(self.0) };
    }
}

#[derive(Default)]
struct State {
    icon: Option<Icon>,
    tool_tip: String,
    title: String,
    menu: Vec<TrayItem>,
    // An add the shell timed out on may still have landed, so `hide` deletes
    // whenever one was attempted.
    requested: bool,
    visible: bool,
}

static STATE: Mutex<State> = Mutex::new(State {
    icon: None,
    tool_tip: String::new(),
    title: String::new(),
    menu: Vec::new(),
    requested: false,
    visible: false,
});
static WINDOW: OnceLock<Option<usize>> = OnceLock::new();
static TITLE_WINDOW: OnceLock<Option<usize>> = OnceLock::new();
static TASKBAR_CREATED: OnceLock<u32> = OnceLock::new();
static FLUSH_MENUS: OnceLock<Option<unsafe extern "system" fn()>> = OnceLock::new();

pub fn show(content: TrayContent) -> bool {
    let Some(window) = window() else {
        return false;
    };
    let Some(icon) = load_icon(&content.image.path) else {
        return false;
    };
    let mut state = lock();
    state.icon = Some(icon);
    state.tool_tip = content.tool_tip;
    state.title = content.title;
    state.menu = content.menu;
    state.requested = true;
    let applied =
        notify(window, &state, !state.visible) || (state.visible && notify(window, &state, true));
    if applied {
        state.visible = true;
    } else {
        unsafe { PostMessageW(window, WM_RETRY, 0, 0) };
    }
    drop(state);
    unsafe { PostMessageW(window, WM_TITLE, 0, 0) };
    true
}

pub fn set_title(title: String) -> bool {
    let Some(window) = existing_window() else {
        return false;
    };
    lock().title = title;
    unsafe { PostMessageW(window, WM_TITLE, 0, 0) != 0 }
}

pub fn hide() {
    let Some(window) = existing_window() else {
        return;
    };
    let mut state = lock();
    if state.requested {
        let mut data = icon_data(window);
        data.uFlags = 0;
        unsafe { Shell_NotifyIconW(NIM_DELETE, &data) };
    }
    *state = State::default();
    drop(state);
    unsafe { PostMessageW(window, WM_TITLE, 0, 0) };
}

pub fn open_menu() -> bool {
    let Some(window) = existing_window() else {
        return false;
    };
    if !lock().visible {
        return false;
    }
    unsafe { PostMessageW(window, WM_OPEN_MENU, 0, 0) != 0 }
}

fn lock() -> MutexGuard<'static, State> {
    STATE.lock().unwrap_or_else(PoisonError::into_inner)
}

fn wide(text: &str) -> Vec<u16> {
    text.encode_utf16().chain(std::iter::once(0)).collect()
}

fn existing_window() -> Option<HWND> {
    WINDOW.get().copied().flatten().map(|window| window as HWND)
}

fn window() -> Option<HWND> {
    WINDOW
        .get_or_init(|| {
            let (ready, window) = mpsc::channel();
            std::thread::Builder::new()
                .name("tray".into())
                .spawn(move || run_window(ready))
                .ok()?;
            window.recv().ok().flatten()
        })
        .map(|window| window as HWND)
}

fn run_window(ready: mpsc::Sender<Option<usize>>) {
    let _ = TASKBAR_CREATED.set(unsafe { RegisterWindowMessageW(wide("TaskbarCreated").as_ptr()) });
    let _ = FLUSH_MENUS.set(allow_dark_menus());
    unsafe {
        let instance = GetModuleHandleW(null());
        let class = wide("FlClashTray");
        let window_class = WNDCLASSW {
            lpfnWndProc: Some(window_proc),
            hInstance: instance,
            lpszClassName: class.as_ptr(),
            ..zeroed()
        };
        RegisterClassW(&window_class);
        let title_class = wide("FlClashTrayTitle");
        let title_window_class = WNDCLASSW {
            lpfnWndProc: Some(title_proc),
            hInstance: instance,
            lpszClassName: title_class.as_ptr(),
            ..zeroed()
        };
        RegisterClassW(&title_window_class);
        let window = CreateWindowExW(
            0,
            class.as_ptr(),
            null(),
            WS_OVERLAPPED,
            0,
            0,
            0,
            0,
            null_mut(),
            null_mut(),
            instance,
            null(),
        );
        let created = !window.is_null();
        let title = CreateWindowExW(
            WS_EX_LAYERED | WS_EX_NOACTIVATE | WS_EX_TOOLWINDOW | WS_EX_TOPMOST,
            title_class.as_ptr(),
            null(),
            WS_POPUP,
            0,
            0,
            0,
            0,
            null_mut(),
            null_mut(),
            instance,
            null(),
        );
        let _ = TITLE_WINDOW.set((!title.is_null()).then_some(title as usize));
        let _ = ready.send(created.then_some(window as usize));
        if !created {
            return;
        }
        SetTimer(window, TITLE_TIMER, TITLE_INTERVAL_MS, None);
        let mut message: MSG = zeroed();
        while GetMessageW(&mut message, null_mut(), 0, 0) > 0 {
            TranslateMessage(&message);
            DispatchMessageW(&message);
        }
    }
}

unsafe extern "system" fn window_proc(
    window: HWND,
    message: u32,
    wparam: WPARAM,
    lparam: LPARAM,
) -> LRESULT {
    match message {
        WM_TRAY => {
            match lparam as u32 {
                WM_LBUTTONUP => emit(TraySignalKind::IconActivated, 0),
                WM_RBUTTONUP => emit(TraySignalKind::MenuRequested, 0),
                _ => {}
            }
            return 0;
        }
        WM_OPEN_MENU => {
            popup_menu(window);
            return 0;
        }
        WM_TITLE => {
            sync_title();
            return 0;
        }
        WM_RETRY => {
            SetTimer(window, RETRY_TIMER, RETRY_INTERVAL_MS, None);
            return 0;
        }
        WM_TIMER if wparam == RETRY_TIMER => {
            restore(window);
            return 0;
        }
        WM_TIMER if wparam == TITLE_TIMER => {
            sync_title();
            return 0;
        }
        WM_SETTINGCHANGE if is_color_set_change(lparam) => {
            if let Some(flush) = FLUSH_MENUS.get().copied().flatten() {
                flush();
            }
        }
        WM_POWERBROADCAST
            if wparam == PBT_APMRESUMEAUTOMATIC as usize
                || wparam == PBT_APMRESUMESUSPEND as usize =>
        {
            restore(window);
        }
        _ if Some(&message) == TASKBAR_CREATED.get() => restore(window),
        _ => {}
    }
    DefWindowProcW(window, message, wparam, lparam)
}

fn icon_data(window: HWND) -> NOTIFYICONDATAW {
    let mut data: NOTIFYICONDATAW = unsafe { zeroed() };
    data.cbSize = size_of::<NOTIFYICONDATAW>() as u32;
    data.hWnd = window;
    data.uID = ICON_ID;
    data
}

fn notify(window: HWND, state: &State, add: bool) -> bool {
    let Some(icon) = &state.icon else {
        return false;
    };
    let mut data = icon_data(window);
    data.uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP;
    data.uCallbackMessage = WM_TRAY;
    data.hIcon = icon.0;
    let tip: Vec<u16> = state
        .tool_tip
        .encode_utf16()
        .take(data.szTip.len() - 1)
        .collect();
    data.szTip[..tip.len()].copy_from_slice(&tip);
    let action = if add { NIM_ADD } else { NIM_MODIFY };
    unsafe { Shell_NotifyIconW(action, &data) != 0 }
}

// An add that timed out may still have landed, so modify goes first.
fn restore(window: HWND) {
    let mut state = lock();
    if !state.requested {
        unsafe { KillTimer(window, RETRY_TIMER) };
        return;
    }
    if notify(window, &state, false) || notify(window, &state, true) {
        state.visible = true;
        unsafe { KillTimer(window, RETRY_TIMER) };
    } else {
        unsafe { SetTimer(window, RETRY_TIMER, RETRY_INTERVAL_MS, None) };
    }
}

fn title_window() -> Option<HWND> {
    TITLE_WINDOW
        .get()
        .copied()
        .flatten()
        .map(|window| window as HWND)
}

fn sync_title() {
    let Some(window) = title_window() else {
        return;
    };
    let title = {
        let state = lock();
        if state.visible {
            state.title.clone()
        } else {
            String::new()
        }
    };
    let Some(layout) = (!title.is_empty()).then(title_layout).flatten() else {
        unsafe { ShowWindow(window, SW_HIDE) };
        return;
    };
    if render_title(window, &title, &layout) {
        if unsafe { IsWindowVisible(window) } == 0 {
            unsafe { ShowWindow(window, SW_SHOWNOACTIVATE) };
        }
    } else {
        unsafe { ShowWindow(window, SW_HIDE) };
    }
}

fn taskbar_is_visible(taskbar: HWND, rect: &RECT) -> bool {
    // A fullscreen window covers the taskbar while Shell_TrayWnd keeps its
    // rect, and the title itself may cover the centre of a narrow taskbar.
    let y = (rect.top + rect.bottom) / 2;
    [rect.left + 1, (rect.left + rect.right) / 2, rect.right - 1]
        .into_iter()
        .any(|x| unsafe {
            let hit = WindowFromPoint(POINT { x, y });
            hit == taskbar || IsChild(taskbar, hit) != 0
        })
}

struct TitleLayout {
    x: i32,
    y: i32,
    width: i32,
    height: i32,
    dpi: u32,
}

fn title_layout() -> Option<TitleLayout> {
    let taskbar = unsafe { FindWindowW(wide("Shell_TrayWnd").as_ptr(), null()) };
    if taskbar.is_null() {
        return None;
    }
    let mut taskbar_rect: RECT = unsafe { zeroed() };
    if unsafe { GetWindowRect(taskbar, &mut taskbar_rect) } == 0 {
        return None;
    }
    let taskbar_width = taskbar_rect.right - taskbar_rect.left;
    let taskbar_height = taskbar_rect.bottom - taskbar_rect.top;
    if taskbar_width <= taskbar_height || taskbar_height < 16 {
        return None;
    }
    let screen_height = unsafe { GetSystemMetrics(SM_CYSCREEN) };
    let visible_height = taskbar_rect.bottom.min(screen_height) - taskbar_rect.top.max(0);
    if visible_height < 8 || !taskbar_is_visible(taskbar, &taskbar_rect) {
        return None;
    }
    let dpi = unsafe { GetDpiForWindow(taskbar) };
    let dpi = if dpi == 0 { 96 } else { dpi };
    let width = TITLE_WIDTH * dpi as i32 / 96;
    let height = TITLE_HEIGHT * dpi as i32 / 96;
    let gap = TITLE_GAP * dpi as i32 / 96;
    let anchor = unsafe {
        let tray = FindWindowExW(taskbar, null_mut(), wide("TrayNotifyWnd").as_ptr(), null());
        let mut tray_rect: RECT = zeroed();
        if !tray.is_null() && GetWindowRect(tray, &mut tray_rect) != 0 {
            tray_rect.left
        } else {
            taskbar_rect.right
        }
    };
    let x = anchor - gap - width;
    if x < taskbar_rect.left {
        return None;
    }
    Some(TitleLayout {
        x,
        y: taskbar_rect.top + (taskbar_height - height) / 2,
        width,
        height,
        dpi,
    })
}

fn render_title(window: HWND, title: &str, layout: &TitleLayout) -> bool {
    let light = taskbar_is_light();
    let screen = unsafe { GetDC(null_mut()) };
    if screen.is_null() {
        return false;
    }
    let memory = unsafe { CreateCompatibleDC(screen) };
    if memory.is_null() {
        unsafe { ReleaseDC(null_mut(), screen) };
        return false;
    }
    let mut info: BITMAPINFO = unsafe { zeroed() };
    info.bmiHeader = unsafe {
        BITMAPINFOHEADER {
            biSize: size_of::<BITMAPINFOHEADER>() as u32,
            biWidth: layout.width,
            biHeight: -layout.height,
            biPlanes: 1,
            biBitCount: 32,
            biCompression: BI_RGB,
            ..zeroed()
        }
    };
    let mut bits = null_mut();
    let bitmap =
        unsafe { CreateDIBSection(memory, &info, DIB_RGB_COLORS, &mut bits, null_mut(), 0) };
    if bitmap.is_null() || bits.is_null() {
        unsafe {
            DeleteDC(memory);
            ReleaseDC(null_mut(), screen);
        }
        return false;
    }
    let previous = unsafe { SelectObject(memory, bitmap) };
    let pixels = unsafe {
        std::slice::from_raw_parts_mut(
            bits.cast::<u32>(),
            layout.width as usize * layout.height as usize,
        )
    };
    pixels.fill(if light { 0x00ff_ffff } else { 0 });
    let face = wide("Segoe UI");
    let font = unsafe {
        CreateFontW(
            -(TITLE_FONT_HEIGHT * layout.dpi as i32 / 96),
            0,
            0,
            0,
            600,
            0,
            0,
            0,
            DEFAULT_CHARSET as u32,
            OUT_DEFAULT_PRECIS as u32,
            CLIP_DEFAULT_PRECIS as u32,
            ANTIALIASED_QUALITY as u32,
            (DEFAULT_PITCH | FF_DONTCARE) as u32,
            face.as_ptr(),
        )
    };
    let old_font = if font.is_null() {
        null_mut()
    } else {
        unsafe { SelectObject(memory, font) }
    };
    unsafe {
        SetBkMode(memory, TRANSPARENT as i32);
        SetTextColor(memory, if light { 0 } else { 0x00ff_ffff });
    }
    let lines = title_lines(title);
    let line_height = layout.height / 2;
    for (index, line) in lines.iter().enumerate() {
        let mut rect = RECT {
            left: 0,
            top: index as i32 * line_height,
            right: layout.width,
            bottom: (index as i32 + 1) * line_height,
        };
        let text: Vec<u16> = line.encode_utf16().collect();
        unsafe {
            DrawTextW(
                memory,
                text.as_ptr(),
                text.len() as i32,
                &mut rect,
                DT_SINGLELINE | DT_VCENTER | DT_RIGHT | DT_NOPREFIX,
            );
        }
    }
    if !font.is_null() {
        unsafe {
            SelectObject(memory, old_font);
            DeleteObject(font);
        }
    }
    unsafe { GdiFlush() };
    // GDI leaves the alpha byte untouched in a 32-bit DIB, so derive it from
    // the glyph coverage and write premultiplied pixels.
    for pixel in pixels.iter_mut() {
        let [blue, green, red, _] = pixel.to_le_bytes();
        let coverage = red.max(green).max(blue);
        *pixel = if light {
            let alpha = 255 - coverage;
            (alpha as u32) << 24
        } else {
            let alpha = coverage as u32;
            (alpha << 24) | (alpha << 16) | (alpha << 8) | alpha
        };
    }
    let blend = BLENDFUNCTION {
        BlendOp: AC_SRC_OVER as u8,
        BlendFlags: 0,
        SourceConstantAlpha: 255,
        AlphaFormat: AC_SRC_ALPHA as u8,
    };
    let destination = POINT {
        x: layout.x,
        y: layout.y,
    };
    let size = SIZE {
        cx: layout.width,
        cy: layout.height,
    };
    let source = POINT { x: 0, y: 0 };
    let applied = unsafe {
        UpdateLayeredWindow(
            window,
            screen,
            &destination,
            &size,
            memory,
            &source,
            0,
            &blend,
            ULW_ALPHA,
        ) != 0
    };
    unsafe {
        SelectObject(memory, previous);
        DeleteObject(bitmap);
        DeleteDC(memory);
        ReleaseDC(null_mut(), screen);
    }
    applied
}

fn title_lines(title: &str) -> [String; 2] {
    let mut lines = title.lines();
    let up = with_arrow('↑', lines.next().unwrap_or_default());
    let down = with_arrow('↓', lines.next().unwrap_or_default());
    [up, down]
}

fn with_arrow(arrow: char, line: &str) -> String {
    let line = line.trim();
    if line.starts_with('↑') || line.starts_with('↓') {
        line.to_owned()
    } else {
        format!("{arrow} {line}")
    }
}

// The taskbar follows SystemUsesLightTheme; the app theme can differ.
fn taskbar_is_light() -> bool {
    let path = wide("Software\\Microsoft\\Windows\\CurrentVersion\\Themes\\Personalize");
    let name = wide("SystemUsesLightTheme");
    let mut value: u32 = 0;
    let mut size = size_of::<u32>() as u32;
    let status = unsafe {
        RegGetValueW(
            HKEY_CURRENT_USER,
            path.as_ptr(),
            name.as_ptr(),
            RRF_RT_REG_DWORD,
            null_mut(),
            (&mut value as *mut u32).cast(),
            &mut size,
        )
    };
    status == ERROR_SUCCESS && value != 0
}

unsafe extern "system" fn title_proc(
    window: HWND,
    message: u32,
    wparam: WPARAM,
    lparam: LPARAM,
) -> LRESULT {
    match message {
        WM_LBUTTONUP => {
            emit(TraySignalKind::IconActivated, 0);
            return 0;
        }
        WM_RBUTTONUP => {
            emit(TraySignalKind::MenuRequested, 0);
            return 0;
        }
        WM_ERASEBKGND => return 1,
        WM_PAINT => {
            ValidateRect(window, null());
            return 0;
        }
        _ => {}
    }
    DefWindowProcW(window, message, wparam, lparam)
}

fn load_icon(path: &str) -> Option<Icon> {
    let icon = unsafe {
        LoadImageW(
            null_mut(),
            wide(path).as_ptr(),
            IMAGE_ICON,
            GetSystemMetrics(SM_CXSMICON),
            GetSystemMetrics(SM_CYSMICON),
            LR_LOADFROMFILE,
        )
    };
    (!icon.is_null()).then_some(Icon(icon))
}

fn popup_menu(window: HWND) {
    let items = {
        let state = lock();
        if !state.visible {
            return;
        }
        state.menu.clone()
    };
    unsafe {
        let menu = build_menu(&items);
        let mut cursor = POINT { x: 0, y: 0 };
        GetCursorPos(&mut cursor);
        // Without the foreground the menu does not close when clicked away from.
        SetForegroundWindow(window);
        let command = TrackPopupMenu(
            menu,
            TPM_BOTTOMALIGN | TPM_LEFTALIGN | TPM_RETURNCMD | TPM_RIGHTBUTTON,
            cursor.x,
            cursor.y,
            0,
            window,
            null(),
        );
        PostMessageW(window, WM_NULL, 0, 0);
        DestroyMenu(menu);
        if command > 0 {
            emit(TraySignalKind::ItemSelected, command as u32);
        }
    }
}

unsafe fn build_menu(items: &[TrayItem]) -> HMENU {
    let menu = CreatePopupMenu();
    for item in items {
        if item.kind == TrayItemKind::Separator {
            AppendMenuW(menu, MF_SEPARATOR, 0, null());
            continue;
        }
        let mut flags = MF_STRING;
        if !item.enabled {
            flags |= MF_GRAYED;
        }
        let mut id = item.id as usize;
        match item.kind {
            TrayItemKind::Checkbox if item.checked => flags |= MF_CHECKED,
            TrayItemKind::Checkbox => flags |= MF_UNCHECKED,
            TrayItemKind::Submenu => {
                flags |= MF_POPUP;
                id = build_menu(&item.items) as usize;
            }
            _ => {}
        }
        AppendMenuW(menu, flags, id, wide(&menu_text(item)).as_ptr());
    }
    menu
}

// Win32 menus read `&` as a mnemonic marker, so a literal one is doubled.
fn menu_text(item: &TrayItem) -> String {
    let label = item.label.replace('&', "&&");
    match item.detail.as_deref() {
        Some(detail) if !detail.is_empty() => format!("{label}\t{}", detail.replace('&', "&&")),
        _ => label,
    }
}

fn is_color_set_change(lparam: LPARAM) -> bool {
    lparam != 0
        && unsafe { lstrcmpW(lparam as *const u16, wide("ImmersiveColorSet").as_ptr()) } == 0
}

fn allow_dark_menus() -> Option<unsafe extern "system" fn()> {
    if os_build()? < FIRST_DARK_MENU_BUILD {
        return None;
    }
    unsafe {
        let uxtheme = LoadLibraryExW(
            wide("uxtheme.dll").as_ptr(),
            null_mut(),
            LOAD_LIBRARY_SEARCH_SYSTEM32,
        );
        if uxtheme.is_null() {
            return None;
        }
        let set_mode = GetProcAddress(uxtheme, SET_PREFERRED_APP_MODE as PCSTR)?;
        let flush = GetProcAddress(uxtheme, FLUSH_MENU_THEMES as PCSTR)?;
        let set_mode: unsafe extern "system" fn(i32) -> i32 = std::mem::transmute(set_mode);
        let flush: unsafe extern "system" fn() = std::mem::transmute(flush);
        set_mode(ALLOW_DARK);
        flush();
        Some(flush)
    }
}

fn os_build() -> Option<u32> {
    unsafe {
        let ntdll = GetModuleHandleW(wide("ntdll.dll").as_ptr());
        if ntdll.is_null() {
            return None;
        }
        let get_version = GetProcAddress(ntdll, c"RtlGetVersion".as_ptr().cast())?;
        let get_version: unsafe extern "system" fn(*mut OSVERSIONINFOW) -> i32 =
            std::mem::transmute(get_version);
        let mut info: OSVERSIONINFOW = zeroed();
        info.dwOSVersionInfoSize = size_of::<OSVERSIONINFOW>() as u32;
        (get_version(&mut info) == 0).then_some(info.dwBuildNumber)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn item(label: &str, detail: Option<&str>) -> TrayItem {
        TrayItem {
            id: 1024,
            kind: TrayItemKind::Action,
            label: label.into(),
            detail: detail.map(Into::into),
            enabled: true,
            checked: false,
            items: Vec::new(),
        }
    }

    #[test]
    fn a_detail_goes_to_the_accelerator_column() {
        assert_eq!(menu_text(&item("Show", Some("Ctrl+S"))), "Show\tCtrl+S");
        assert_eq!(menu_text(&item("Show", Some(""))), "Show");
        assert_eq!(menu_text(&item("Show", None)), "Show");
    }

    #[test]
    fn an_ampersand_is_shown_rather_than_read_as_a_mnemonic() {
        assert_eq!(menu_text(&item("R&D", Some("A&B"))), "R&&D\tA&&B");
    }

    #[test]
    fn the_title_stays_two_lines_with_direction_arrows() {
        assert_eq!(
            title_lines("1 KB/s\n2 KB/s"),
            ["↑ 1 KB/s".to_owned(), "↓ 2 KB/s".to_owned()]
        );
        assert_eq!(
            title_lines("1 KB/s"),
            ["↑ 1 KB/s".to_owned(), "↓ ".to_owned()]
        );
    }

    #[test]
    fn an_existing_direction_arrow_is_not_doubled() {
        assert_eq!(
            title_lines("↑ 1 KB/s\n↓ 2 KB/s"),
            ["↑ 1 KB/s".to_owned(), "↓ 2 KB/s".to_owned()]
        );
    }
}
