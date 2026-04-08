use std::io::IsTerminal;
use std::sync::OnceLock;

static COLOR_ENABLED: OnceLock<bool> = OnceLock::new();

pub fn enabled() -> bool {
    *COLOR_ENABLED.get_or_init(|| std::io::stderr().is_terminal())
}

fn wrap(code: &str, text: &str) -> String {
    if enabled() {
        format!("\x1b[{}m{}\x1b[0m", code, text)
    } else {
        text.to_string()
    }
}

pub fn red(text: &str) -> String {
    wrap("31", text)
}

pub fn green(text: &str) -> String {
    wrap("32", text)
}

pub fn yellow(text: &str) -> String {
    wrap("33", text)
}

pub fn cyan(text: &str) -> String {
    wrap("36", text)
}

pub fn dim(text: &str) -> String {
    wrap("2", text)
}
