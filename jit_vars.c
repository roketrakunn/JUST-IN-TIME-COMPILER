#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/mman.h>
#include <unistd.h>

//======================== CODE BUFFER ========================
typedef struct {
    uint8_t* code;
    size_t size;
    size_t capacity;
} CodeBuffer;

CodeBuffer* code_buffer_new(size_t initial_capacity) {
    CodeBuffer* buf = malloc(sizeof(CodeBuffer));
    buf->capacity = initial_capacity;
    buf->code = malloc(buf->capacity);
    buf->size = 0;
    return buf;
}

void code_buffer_free(CodeBuffer* buf) {
    free(buf->code);
    free(buf);
}

//======================== SYMBOL TABLE (Register Allocator) ========================
// We have 4 registers available: EAX(0), EBX(1), ECX(2), EDX(3)

typedef struct {
    char* name;          // Variable name "x", "y", etc.
    int reg_num;         // Which register? 0=EAX, 1=EBX, 2=ECX, 3=EDX
    int allocated;       // Is this slot in use?
} SymbolEntry;

typedef struct {
    SymbolEntry vars[4]; // Max 4 variables (one per register)
    int reg_free[4];     // 1=free, 0=in use
} SymbolTable;

void symtab_init(SymbolTable* st) {
    for (int i = 0; i < 4; i++) {
        st->vars[i].name = NULL;
        st->vars[i].reg_num = i;
        st->vars[i].allocated = 0;
        st->reg_free[i] = 1;  // All registers start free
    }
}

// Find a variable by name, return register number (-1 if not found)
int symtab_lookup(SymbolTable* st, char* name) {
    for (int i = 0; i < 4; i++) {
        if (st->vars[i].allocated && strcmp(st->vars[i].name, name) == 0) {
            return st->vars[i].reg_num;
        }
    }
    return -1;  // Not found
}

// Allocate a register for a variable (returns reg num, or -1 if all full)
int symtab_allocate(SymbolTable* st, char* name) {
    // First check if variable already exists
    int existing = symtab_lookup(st, name);
    if (existing != -1) {
        return existing;  // Reuse existing register
    }
    
    // Find a free register
    for (int i = 0; i < 4; i++) {
        if (st->reg_free[i]) {
            st->vars[i].name = strdup(name);  // Copy the name
            st->vars[i].allocated = 1;
            st->reg_free[i] = 0;
            return i;
        }
    }
    
    return -1;  // Out of registers!
}

void symtab_free(SymbolTable* st) {
    for (int i = 0; i < 4; i++) {
        if (st->vars[i].name) {
            free(st->vars[i].name);
        }
    }
}

//======================== TOKENS ========================
typedef enum {
    TOKEN_NUMBER,
    TOKEN_IDENTIFIER,  // NEW: variable names
    TOKEN_EQUALS,      // NEW: =
    TOKEN_PLUS,
    TOKEN_MINUS,
    TOKEN_STAR,
    TOKEN_SLASH,
    TOKEN_PERCENT,
    TOKEN_LPAREN,
    TOKEN_RPAREN,
    TOKEN_SEMICOLON,   // NEW: ; (statement separator)
    TOKEN_EOF,
    TOKEN_ERROR   
} TokenType;

typedef struct {
    TokenType type;
    int value;         // For numbers
    char* identifier;  // For variable names
    char* start;
    int length;
} Token;

//======================== AST NODES ========================
typedef enum {
    NODE_NUMBER,
    NODE_BINARY_OP,
    NODE_UNARY_OP,
    NODE_ASSIGNMENT,   // NEW: x = expr
    NODE_VARIABLE      // NEW: reference to x
} NodeType;

typedef struct ASTNode {
    NodeType type;
    int value;
    char op;
    char* var_name;
    struct ASTNode* left;
    struct ASTNode* right;
} ASTNode;

//======================== EMIT FUNCTIONS ========================
void emit_byte(CodeBuffer* buf, uint8_t byte) {
    if (buf->size >= buf->capacity) {
        buf->capacity *= 2;
        buf->code = realloc(buf->code, buf->capacity);
    }
    buf->code[buf->size++] = byte;
}

void emit_u32(CodeBuffer* buf, uint32_t value) {
    emit_byte(buf, value & 0xFF);
    emit_byte(buf, (value >> 8) & 0xFF);
    emit_byte(buf, (value >> 16) & 0xFF);
    emit_byte(buf, (value >> 24) & 0xFF);
}

// Register encoding: 0=EAX, 1=EBX, 2=ECX, 3=EDX
uint8_t reg_to_opcode_offset(int reg) {
    return (uint8_t)reg;
}

// mov imm32, %reg
void emit_mov_reg_imm(CodeBuffer* buf, int reg, uint32_t value) {
    emit_byte(buf, 0xB8 + reg_to_opcode_offset(reg));  // B8+reg for mov
    emit_u32(buf, value);
}

// mov %src, %dst
void emit_mov_reg_reg(CodeBuffer* buf, int src, int dst) {
    emit_byte(buf, 0x89);  // MOV r/m32, r32
    emit_byte(buf, 0xC0 | (src << 3) | dst);  // ModRM byte
}

// add %src, %dst (dst = dst + src)
void emit_add_reg_reg(CodeBuffer* buf, int src, int dst) {
    emit_byte(buf, 0x01);  // ADD r/m32, r32
    emit_byte(buf, 0xC0 | (src << 3) | dst);
}

// sub %src, %dst (dst = dst - src)
void emit_sub_reg_reg(CodeBuffer* buf, int src, int dst) {
    emit_byte(buf, 0x29);  // SUB r/m32, r32
    emit_byte(buf, 0xC0 | (src << 3) | dst);
}

// imul %src, %dst (dst = dst * src)
void emit_imul_reg_reg(CodeBuffer* buf, int src, int dst) {
    emit_byte(buf, 0x0F);
    emit_byte(buf, 0xAF);
    emit_byte(buf, 0xC0 | (dst << 3) | src);
}

// neg %reg (reg = -reg)
void emit_neg_reg(CodeBuffer* buf, int reg) {
    emit_byte(buf, 0xF7);
    emit_byte(buf, 0xD8 + reg_to_opcode_offset(reg));
}

// For division: we need EAX and EDX specifically
void emit_cdq(CodeBuffer* buf) {
    emit_byte(buf, 0x99);
}

void emit_idiv_reg(CodeBuffer* buf, int reg) {
    emit_byte(buf, 0xF7);
    emit_byte(buf, 0xF8 + reg_to_opcode_offset(reg));
}

void emit_ret(CodeBuffer* buf) {
    emit_byte(buf, 0xC3);
}

//======================== LEXER ========================
typedef struct {
    char* source;
    char* current;
} Lexer;

void lexer_init(Lexer* lex, char* source) {
    lex->source = source;
    lex->current = source;
}

char lexer_peek(Lexer* lex) {
    return *lex->current;
}

char lexer_advance(Lexer* lex) {
    char c = *lex->current;
    if (c != '\0') lex->current++;
    return c;
}

void lexer_skip_whitespace(Lexer* lex) {
    while (lexer_peek(lex) == ' ' || lexer_peek(lex) == '\t' || 
           lexer_peek(lex) == '\n' || lexer_peek(lex) == '\r') {
        lexer_advance(lex);
    }
}

int is_digit(char c) {
    return c >= '0' && c <= '9';
}

int is_alpha(char c) {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
}

int is_alnum(char c) {
    return is_alpha(c) || is_digit(c);
}

Token lexer_next_token(Lexer* lex) {
    Token token;
    lexer_skip_whitespace(lex);
    token.start = lex->current;
    token.length = 1;
    token.identifier = NULL;

    char c = lexer_peek(lex);
    if (c == '\0') {
        token.type = TOKEN_EOF;
        return token;
    }

    // Numbers
    if (is_digit(c)) {
        token.type = TOKEN_NUMBER;
        token.value = 0;
        while (is_digit(lexer_peek(lex))) {
            token.value = token.value * 10 + (lexer_advance(lex) - '0');
            token.length++;
        }
        token.length--;
        return token;
    }

    // Identifiers (variable names)
    if (is_alpha(c)) {
        token.type = TOKEN_IDENTIFIER;
        char* start = lex->current;
        int len = 0;
        while (is_alnum(lexer_peek(lex))) {
            lexer_advance(lex);
            len++;
        }
        token.identifier = strndup(start, len);
        token.length = len;
        return token;
    }

    // Single-character tokens
    lexer_advance(lex);
    switch (c) {
        case '=': token.type = TOKEN_EQUALS; break;
        case '+': token.type = TOKEN_PLUS; break;
        case '-': token.type = TOKEN_MINUS; break;
        case '*': token.type = TOKEN_STAR; break;
        case '/': token.type = TOKEN_SLASH; break;
        case '%': token.type = TOKEN_PERCENT; break;
        case '(': token.type = TOKEN_LPAREN; break;
        case ')': token.type = TOKEN_RPAREN; break;
        case ';': token.type = TOKEN_SEMICOLON; break;
        default: token.type = TOKEN_ERROR; break;
    }
    return token;
}

//======================== PARSER ========================
typedef struct {
    Lexer* lexer;
    Token current;
    Token previous;
} Parser;

void parser_init(Parser* p, Lexer* lex) {
    p->lexer = lex;
    p->current = lexer_next_token(lex);
}

void parser_advance(Parser* p) {
    p->previous = p->current;
    p->current = lexer_next_token(p->lexer);
}

int parser_check(Parser* p, TokenType type) {
    return p->current.type == type;
}

int parser_match(Parser* p, TokenType type) {
    if (parser_check(p, type)) {
        parser_advance(p);
        return 1;
    }
    return 0;
}

// Forward declarations
ASTNode* parse_statement(Parser* p);
ASTNode* parse_expression(Parser* p);
ASTNode* parse_term(Parser* p);
ASTNode* parse_term_with_left(Parser* p, ASTNode* left);
ASTNode* parse_factor(Parser* p);
ASTNode* parse_unary(Parser* p);
ASTNode* parse_primary(Parser* p);

// Primary: number, variable, or (expression)
ASTNode* parse_primary(Parser* p) {
    if (parser_match(p, TOKEN_NUMBER)) {
        ASTNode* node = malloc(sizeof(ASTNode));
        node->type = NODE_NUMBER;
        node->value = p->previous.value;
        node->var_name = NULL;
        node->left = NULL;
        node->right = NULL;
        return node;
    }

    if (parser_match(p, TOKEN_IDENTIFIER)) {
        ASTNode* node = malloc(sizeof(ASTNode));
        node->type = NODE_VARIABLE;
        node->var_name = p->previous.identifier;
        node->left = NULL;
        node->right = NULL;
        return node;
    }

    if (parser_match(p, TOKEN_LPAREN)) {
        ASTNode* expr = parse_expression(p);
        parser_match(p, TOKEN_RPAREN);
        return expr;
    }

    return NULL;
}

// Unary: -expr, +expr
ASTNode* parse_unary(Parser* p) {
    if (parser_match(p, TOKEN_MINUS) || parser_match(p, TOKEN_PLUS)) {
        Token op = p->previous;
        ASTNode* right = parse_unary(p);

        ASTNode* node = malloc(sizeof(ASTNode));
        node->type = NODE_UNARY_OP;
        node->op = (op.type == TOKEN_MINUS) ? '-' : '+';
        node->var_name = NULL;
        node->left = NULL;
        node->right = right;
        return node;
    }

    return parse_primary(p);
}

// Factor: *, /, %
ASTNode* parse_factor(Parser* p) {
    ASTNode* left = parse_unary(p);

    while (parser_match(p, TOKEN_STAR) || 
           parser_match(p, TOKEN_SLASH) || 
           parser_match(p, TOKEN_PERCENT)) {
        Token op = p->previous;
        ASTNode* right = parse_unary(p);

        ASTNode* node = malloc(sizeof(ASTNode));
        node->type = NODE_BINARY_OP;
        node->op = (op.type == TOKEN_STAR) ? '*' : 
                   (op.type == TOKEN_SLASH) ? '/' : '%';
        node->var_name = NULL;
        node->left = left;
        node->right = right;
        left = node;
    }

    return left;
}

// Term: +, -
ASTNode* parse_term(Parser* p) {
    ASTNode* left = parse_factor(p);

    while (parser_match(p, TOKEN_PLUS) || parser_match(p, TOKEN_MINUS)) {
        Token op = p->previous;
        ASTNode* right = parse_factor(p);

        ASTNode* node = malloc(sizeof(ASTNode));
        node->type = NODE_BINARY_OP;
        node->op = (op.type == TOKEN_PLUS) ? '+' : '-';
        node->var_name = NULL;
        node->left = left;
        node->right = right;
        left = node;
    }

    return left;
}

// Expression: same as term for now
ASTNode* parse_expression(Parser* p) {
    return parse_term(p);
}

// Statement: assignment or expression
ASTNode* parse_statement(Parser* p) {
    // Look ahead to see if this is an assignment
    if (parser_check(p, TOKEN_IDENTIFIER)) {
        // Save the identifier
        Token id_token = p->current;
        parser_advance(p);
        
        if (parser_check(p, TOKEN_EQUALS)) {
            // It's an assignment!
            parser_advance(p);  // consume '='
            ASTNode* expr = parse_expression(p);
            
            ASTNode* node = malloc(sizeof(ASTNode));
            node->type = NODE_ASSIGNMENT;
            node->var_name = strdup(id_token.identifier);
            if (id_token.identifier) free(id_token.identifier);
            node->left = NULL;
            node->right = expr;
            return node;
        } else {
            // Not an assignment - it's an expression starting with identifier
            // We need to put this identifier back into the parsing stream
            // Create a variable node and check if there's more to the expression
            ASTNode* var_node = malloc(sizeof(ASTNode));
            var_node->type = NODE_VARIABLE;
            var_node->var_name = id_token.identifier;
            var_node->left = NULL;
            var_node->right = NULL;
            
            // Now check if there's an operator following (like "x + 5")
            if (parser_check(p, TOKEN_PLUS) || parser_check(p, TOKEN_MINUS) ||
                parser_check(p, TOKEN_STAR) || parser_check(p, TOKEN_SLASH) ||
                parser_check(p, TOKEN_PERCENT)) {
                // Continue parsing as a binary expression
                // Put var_node as the left side
                return parse_term_with_left(p, var_node);
            }
            
            // Just a standalone variable reference
            return var_node;
        }
    }

    // Otherwise it's just an expression
    return parse_expression(p);
}

// Helper to continue parsing a term when we already have the left side
ASTNode* parse_term_with_left(Parser* p, ASTNode* left) {
    // We already have left, now check for + or -
    while (parser_match(p, TOKEN_PLUS) || parser_match(p, TOKEN_MINUS)) {
        Token op = p->previous;
        ASTNode* right = parse_factor(p);

        ASTNode* node = malloc(sizeof(ASTNode));
        node->type = NODE_BINARY_OP;
        node->op = (op.type == TOKEN_PLUS) ? '+' : '-';
        node->var_name = NULL;
        node->left = left;
        node->right = right;
        left = node;
    }

    return left;
}

void free_ast(ASTNode* node) {
    if (!node) return;
    if (node->var_name) free(node->var_name);
    free_ast(node->left);
    free_ast(node->right);
    free(node);
}

//======================== CODE GENERATOR ========================
// Track which registers are used for temporaries vs variables
int temp_reg_counter = 0;

// Get a temporary register (for intermediate calculations)
int allocate_temp_reg(SymbolTable* st) {
    // Use registers that aren't allocated to variables
    for (int i = 0; i < 4; i++) {
        if (st->reg_free[i]) {
            return i;
        }
    }
    // If all allocated, use EAX as default temp (might clobber, but it's temp)
    return 0;
}

// Returns which register holds the result
int code_gen(ASTNode* node, CodeBuffer* buf, SymbolTable* st) {
    if (node->type == NODE_NUMBER) {
        // Allocate a temporary register for the number
        int temp_reg = allocate_temp_reg(st);
        emit_mov_reg_imm(buf, temp_reg, node->value);
        return temp_reg;
    }

    if (node->type == NODE_VARIABLE) {
        // Look up variable in symbol table
        int reg = symtab_lookup(st, node->var_name);
        if (reg == -1) {
            fprintf(stderr, "ERROR: Undefined variable '%s'\n", node->var_name);
            exit(1);
        }
        return reg;  // Variable is already in this register
    }

    if (node->type == NODE_ASSIGNMENT) {
        // Generate code for right-hand side
        int rhs_reg = code_gen(node->right, buf, st);
        
        // Allocate register for this variable
        int var_reg = symtab_allocate(st, node->var_name);
        if (var_reg == -1) {
            fprintf(stderr, "ERROR: Out of registers! Max 4 variables supported.\n");
            exit(1);
        }
        
        // Move result to variable's register (if different)
        if (rhs_reg != var_reg) {
            emit_mov_reg_reg(buf, rhs_reg, var_reg);
        }
        
        return var_reg;
    }

    if (node->type == NODE_UNARY_OP) {
        int reg = code_gen(node->right, buf, st);
        
        switch (node->op) {
            case '-':
                emit_neg_reg(buf, reg);
                break;
            case '+':
                // No-op
                break;
        }
        return reg;
    }

    // Binary operation - THIS IS THE TRICKY PART
    // We need to be careful about register usage
    
    // Strategy: 
    // 1. Compute left, result in some register
    // 2. If right is a simple value/var, we're good
    // 3. If right is complex expr, it might clobber left's register
    // 4. Solution: for simple cases without variables, use stack-based approach
    
    int left_reg = code_gen(node->left, buf, st);
    
    // Save left result to a safe place if needed
    // For now, assume left is either in a variable register (safe) or temp
    // Check if left is a variable (safe) or temp (needs saving)
    int left_is_temp = 1;
    for (int i = 0; i < 4; i++) {
        if (st->vars[i].allocated && st->vars[i].reg_num == left_reg) {
            left_is_temp = 0;  // It's a variable, safe
            break;
        }
    }
    
    // If left is in a temp register, it might get clobbered by right computation
    // Simple solution: use push/pop (like we did in arithmetic-only JIT)
    if (left_is_temp && (node->right->type != NODE_NUMBER && 
                          node->right->type != NODE_VARIABLE)) {
        // Right is a complex expression, save left on stack
        emit_byte(buf, 0x50 + left_reg);  // push reg
    }
    
    int right_reg = code_gen(node->right, buf, st);
    
    // Restore left if we saved it
    if (left_is_temp && (node->right->type != NODE_NUMBER && 
                          node->right->type != NODE_VARIABLE)) {
        // Pop left back, but we need a free register
        // Use a temp register that's not right_reg
        int restore_reg = (right_reg == 0) ? 1 : 0;
        emit_byte(buf, 0x58 + restore_reg);  // pop reg
        left_reg = restore_reg;
    }
    
    // Perform operation: left_reg = left_reg OP right_reg
    switch (node->op) {
        case '+':
            emit_add_reg_reg(buf, right_reg, left_reg);
            break;
        case '-':
            emit_sub_reg_reg(buf, right_reg, left_reg);
            break;
        case '*':
            emit_imul_reg_reg(buf, right_reg, left_reg);
            break;
        case '/':
        case '%':
            // Division is tricky - needs EAX and EDX
            if (left_reg != 0) {
                emit_mov_reg_reg(buf, left_reg, 0);  // Move to EAX
            }
            emit_cdq(buf);
            emit_idiv_reg(buf, right_reg);
            
            if (node->op == '%') {
                emit_mov_reg_reg(buf, 2, 0);  // EDX to EAX
            }
            return 0;
    }
    
    return left_reg;
}

//======================== EXECUTION ========================
void* allocate_executable_memory(size_t size) {
    void* mem = mmap(NULL, size, PROT_READ | PROT_WRITE | PROT_EXEC,
                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mem == MAP_FAILED) {
        perror("mmap");
        return NULL;
    }
    return mem;
}

void free_executable_memory(void* mem, size_t size) {
    munmap(mem, size);
}

int execute_code(CodeBuffer* buf) {
    void* exec_mem = allocate_executable_memory(buf->size);
    if (!exec_mem) {
        fprintf(stderr, "Failed to allocate executable memory\n");
        return -1;
    }

    memcpy(exec_mem, buf->code, buf->size);
    int (*func)() = (int (*)())exec_mem;
    int result = func();

    free_executable_memory(exec_mem, buf->size);
    return result;
}

//======================== MAIN ========================
int compile_and_run(char* source) {
    SymbolTable st;
    symtab_init(&st);
    
    Lexer lexer;
    lexer_init(&lexer, source);
    
    Parser parser;
    parser_init(&parser, &lexer);
    
    CodeBuffer* buf = code_buffer_new(1024);
    
    // Parse and compile statements until EOF
    int last_reg = 0;
    while (!parser_check(&parser, TOKEN_EOF)) {
        ASTNode* stmt = parse_statement(&parser);
        if (!stmt) {
            fprintf(stderr, "Parse error\n");
            return -1;
        }
        
        last_reg = code_gen(stmt, buf, &st);
        free_ast(stmt);
        
        // Skip optional semicolons
        parser_match(&parser, TOKEN_SEMICOLON);
    }
    
    // Make sure result is in EAX for return
    if (last_reg != 0) {
        emit_mov_reg_reg(buf, last_reg, 0);
    }
    
    emit_ret(buf);
    
    int result = execute_code(buf);
    
    code_buffer_free(buf);
    symtab_free(&st);
    
    return result;
}

int main() {
    printf("=== JIT Compiler v0.6 - Variables with Register Allocation ===\n");
    printf("Max 4 variables (EAX, EBX, ECX, EDX)\n\n");
    
    char* tests[] = {
        "5 + 10",
        "x = 5",
        "x = 5; x",
        "x = 5; y = 10; x + y",
        "x = 5; y = x + 10; y",
        "x = 5; y = 10; z = x + y; z",
        "x = 5; y = 10; z = x * y; w = z - 20; w",
        "a = 10; b = 20; c = a + b; d = c * 2; d",
        NULL
    };
    
    int expected[] = {15, 5, 5, 15, 15, 15, 30, 60};
    
    for (int i = 0; tests[i] != NULL; i++) {
        printf("Test %d: %s\n", i + 1, tests[i]);
        int result = compile_and_run(tests[i]);
        printf("Result: %d (expected %d)\n", result, expected[i]);
        
        if (result == expected[i]) {
            printf("✓ PASS\n\n");
        } else {
            printf("✗ FAIL\n\n");
        }
    }
    
    printf("=== All tests complete ===\n");
    
    return 0;
}
