// Fixture for meld's wasip2 exit-import check (Rust 1.100.0, wasm32-wasip2).
// Prints one line, then exits with code 7 through wasi:cli/exit.
fn main() {
    println!("hello from rust 1.100");
    std::process::exit(7);
}
