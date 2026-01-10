# JIT Compiler

A simple Just-In-Time compiler that parses arithmetic expressions and generates x86 machine code for direct execution at runtime.

## Features

- **Full expression parsing** - Supports complex arithmetic expressions with proper operator precedence
- **Runtime code generation** - Generates x86 machine code on-the-fly
- **Arithmetic operations** - Addition, subtraction, and multiplication
- **Operator precedence** - Correctly handles `*` before `+` and `-`
- **Parentheses support** - Group expressions with `(` and `)`
- **Direct execution** - Executes generated machine code directly on the CPU using `mmap`

## Building

```bash
gcc -o jit jit.c -Wall -Wextra -m32
./jit
```

**Requirements:**
- GCC compiler
- 32-bit compilation support (`gcc-multilib` on 64-bit Linux)
- x86 architecture

## Examples

The compiler can parse and execute expressions like:

```
5 + 10          → 15
20 - 5          → 15
5 * 3           → 15
(5 + 10) * 2    → 30
10 + 5 * 2      → 20  (multiplication first!)
100 - 50 - 25   → 25  (left-to-right evaluation)
100 / 5 
(100 + 5) % 10
(-5 + 3 ) % 2   This is new 
```

## How It Works

1. **Lexer** - Tokenizes the input string into numbers and operators
2. **Parser** - Builds an Abstract Syntax Tree (AST) with proper precedence
3. **Code Generator** - Walks the AST and emits x86 machine code
4. **Executor** - Allocates executable memory and runs the generated code

## Technical Details

- Uses recursive descent parsing for expression evaluation
- Generates 32-bit x86 machine code (targeting EAX/EBX registers)
- Stack-based evaluation for nested expressions
- Memory-mapped executable pages via `mmap` with `PROT_EXEC`

## Development Status

✅ Phase 1: Code generation and execution (COMPLETE)  
✅ Phase 2: Lexer and tokenizer (COMPLETE)  
✅ Phase 3: Full expression parser with precedence (COMPLETE)  
✅ Phase 4: Division operator  + modulo oparator (%) (COMPLETE) 
✅ Phase 5: Unary operation awareness ("-5 + 3 = -2") (COMPLETE)
⏳ Phase 6: Variables and assignment  (currently working on this)
⏳ Phase 7: Control flow (if/else, loops)

## Future Enhancements

- ✅ Division and modulo operators
- ✅ Unary operators (negation)
- [ ] Variable storage and retrieval
- [ ] Function definitions
- [ ] Comparison operators and conditionals
- [ ] Optimization passes

## Learning Resources

This project demonstrates:
- Compiler design principles
- x86 assembly programming
- Memory management and system calls
- Abstract syntax trees
- Recursive descent parsing


