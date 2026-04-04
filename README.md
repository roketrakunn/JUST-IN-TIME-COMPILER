# JIT Compiler

A Just-In-Time compiler written in Rust that parses a custom language and generates x86-64 machine code for direct execution at runtime.

## Features

- **Full expression parsing** - Arithmetic with correct operator precedence
- **Variables** - Assignment and retrieval via stack-allocated slots
- **Control flow** - `if/else` and `while` with backpatching
- **Functions** - Definitions with parameters, isolated scope, return values via `eax`, recursion
- **Globals** - Top-level variables stored in a dedicated `mmap`'d region, accessible from any function
- **Comparison operators** - `==`, `!=`, `<`, `>`, `<=`, `>=`
- **Unary operators** - Negation (`-x`)
- **Runtime code generation** - Emits x86-64 machine code on-the-fly
- **Direct execution** - Runs generated code via `mmap` with `PROT_EXEC`

## Building

```bash
cd jit_rs
cargo run
```

**Requirements:**
- Rust (stable)
- Linux x86-64

## Examples

```
2 + 3                                        → 5
x = 10; x + 3                                → 13
x = 5; if (x > 3) { x = 99; }               → 99
x = 2; if (x > 3) { x = 99; } else { x = 0; }  → 0
x = 0; y = 0; while (y < 5) { x = x + 2; y = y + 1; }; x   → 10
fn add(a, b) { a + b; } add(3, 7)           → 10
fn add(a, b) { a + b; } if (add(2, 3) == 5) { 99; } else { 0; }  → 99
x = 10; fn double() { x + x; } double()                          → 20  (global access)
fn fact(n) { if (n < 2) { 1; } else { n * fact(n - 1); }; } fact(5)  → 120  (recursion)
```

## How It Works

1. **Lexer** (`lexer.rs`) — tokenizes source into `Vec<Token>`
2. **Parser** (`parser.rs`) — recursive descent, builds an AST of `Expr` / `Stmt` nodes
3. **Codegen** (`codegen.rs`) — walks the AST, emits x86-64 bytes into a `CodeBuffer`
4. **Executor** (`executor.rs`) — `mmap`s executable memory, copies bytes in, calls it as a function

### Codegen architecture

- `SymbolTable` — maps local variable names to `rbp`-relative negative stack offsets
- `GlobalTable` — maps global variable names to offsets in a dedicated `mmap`'d 256-byte region
- `FnNode` — each function compiles into its own isolated buffer with its own symbol table
- `CodeGen` holds both tables, a function registry (`fn_table`), and the master buffer
- Function bodies are stitched into the master buffer first; a `jmp` at byte 0 skips over them to main code
- Parameters are passed on the stack and read via positive `rbp` offsets (`+16`, `+24`, ...)
- Globals use absolute 64-bit addressing via `rcx` as intermediary
- Recursive self-calls use backpatching (`self_call_patches` on `FnNode`)
- Control flow (`if/else`, `while`) uses `je`/`jmp` with backpatching

## Development Status

✅ Phase 1: x86 code generation and execution  
✅ Phase 2: Lexer and tokenizer  
✅ Phase 3: Full expression parser with precedence  
✅ Phase 4: Division and modulo  
✅ Phase 5: Unary operators  
✅ Phase 6: Variables and assignment  
✅ Phase 7: Control flow — if/else and while  
✅ Phase 8: Functions with isolated scope and argument passing  
✅ Phase 9: Globals via mmap'd region + recursive functions  
⏳ Phase 10: Mutual recursion + interpreter integration  
