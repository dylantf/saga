#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntrinsicId {
    PrintStdout,
    PrintStderr,
    Dbg,
    CatchPanic,
}

pub fn intrinsic_id_for_canonical_name(name: &str) -> Option<IntrinsicId> {
    match name {
        "Std.IO.Unsafe.print_stdout" => Some(IntrinsicId::PrintStdout),
        "Std.IO.Unsafe.print_stderr" => Some(IntrinsicId::PrintStderr),
        "Std.IO.dbg" => Some(IntrinsicId::Dbg),
        "Std.Process.catch_panic" => Some(IntrinsicId::CatchPanic),
        _ => None,
    }
}
