
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>
#include <sys/mman.h>
#include <unistd.h>
#include <stddef.h>
#include <stdarg.h>


//The code buffer-------------
//size => size of code you are trying to exec 
//capacity => how much can the buffer contain
typedef struct {
    uint8_t* code;
    size_t size;
    size_t capacity;
} CodeBuffer;

//New buffer
//Returns a new buffer
//Params: 
//       inttial_capacity(number of bytes you want) e.g 1024
CodeBuffer* code_buffer_new(size_t initial_capacity) {
    CodeBuffer* buf = malloc(sizeof(CodeBuffer));
    buf->capacity = initial_capacity;
    buf->code = malloc(buf->capacity);
    buf->size = 0;
    return buf;
}

//Free the bytes that were given to you .. pass the adress of the buffer and it will be gone...later
//Coz linux is ...lazy to do things now.
void code_buffer_free(CodeBuffer* buf) {
    free(buf->code);
    free(buf);
}

//========LEXER(PARSER STRUCTURES)==============
typedef enum {
    TOKEN_NUMBER, // 0..9
    TOKEN_PLUS,   // +
    TOKEN_MINUS,  // -
    TOKEN_STAR,   // *
    TOKEN_SLASH,  // /
    TOKEN_LPAREN, // (
    TOKEN_RPAREN, // )
    TOKEN_EOF,    //"0\"
    TOKEN_ERROR   
} TokenType;

//Token
typedef struct {
    TokenType type;
    int value;
    char* start;
    int length;
} Token;

//----AST NODE TYPES
typedef enum {
    NODE_NUMBER, //0..0
    NODE_BINARY_OP //math arithmetics e.g +
} NodeType;

//----AST NODE
typedef struct ASTNode {
    NodeType type; //Does this node contain a nunber or an operation
    int value;      //Its value 0..9
    char op;        //its char '+'
    struct ASTNode* left;   //Pointer to left
    struct ASTNode* right;  //Pointer to right
} ASTNode;

//-------EMIT FUNCTIONS---THE FUN STUFF(FOR ME.) 
// ------=THIS HAS ALOT OF BYTCODE ... I NEVER MEMORIZED ALL OF THIS(FOR NOW) , I USED THE objdumps
//Just fills the buffer with bytcode 
// The byte code is what the CPU gets and runs.
// How it works: 
//             Check if buffer size is greater than or less than the allocated mem we asked for 
//             if so we double the allocated mem .. if we had 2004 bytes we will then have 4008 
//             we then reallcate that amound
//            if all was good and the capacity was sufficient you increment and insert the byte 
void emit_byte(CodeBuffer* buf, uint8_t byte) {
    if (buf->size >= buf->capacity) {
        buf->capacity *= 2;
        buf->code = realloc(buf->code, buf->capacity);
    }
    buf->code[buf->size++] = byte;
}

//This is my favourite
// It takes a buffer and an unsinged integer of 32 bits 
// conevets the number to 4 bytes via bit maskings
// If you do not knwo what bit masking is .. then you should no be reading this code.

void emit_u32(CodeBuffer* buf, uint32_t value) {
    emit_byte(buf, value & 0xFF); //last ... at the end 
    emit_byte(buf, (value >> 8) & 0xFF);//second last byte
    emit_byte(buf, (value >> 16) & 0xFF);//second byte 
    emit_byte(buf, (value >> 24) & 0xFF);//First byte 
}

//instrution : mov imm_value , %eax
void emit_mov_eax_imm(CodeBuffer* buf, uint32_t value) {
    emit_byte(buf, 0xB8); //uses our emit byte to insert the bytecode for mov <imm> eax 
    emit_u32(buf, value); //also uses the emit_32 func to convert the immidiate 32
}

//instrution : mov imm_value , %ebx => emit functio
void emit_mov_ebx_imm(CodeBuffer* buf, uint32_t value) {
    emit_byte(buf, 0xBB); 
    emit_u32(buf, value);
}

//emit add imm8 , %eax
void emit_add_eax_imm8(CodeBuffer* buf, uint8_t value) {
    emit_byte(buf, 0x83);   
    emit_byte(buf, 0xC0);
    emit_byte(buf, value);
}

//add ebx , eax
void emit_add_eax_ebx(CodeBuffer* buf) {
    emit_byte(buf, 0x01);
    emit_byte(buf, 0xD8);
}

//sub imm8 , eax
void emit_sub_eax_imm8(CodeBuffer* buf, uint8_t value) {
    emit_byte(buf, 0x83);
    emit_byte(buf, 0xE8);
    emit_byte(buf, value);
}

//sub ebx , eax
void emit_sub_eax_ebx(CodeBuffer* buf) {
    emit_byte(buf, 0x29);
    emit_byte(buf, 0xD8);
}

//emit imul %ebx , %eax
void emit_imul_eax_ebx(CodeBuffer* buf) {
    emit_byte(buf, 0x0F);
    emit_byte(buf, 0xAF);
    emit_byte(buf, 0xC3);
}

//emit push %eax
void emit_push_eax(CodeBuffer* buf) {
    emit_byte(buf, 0x50);
}

//pop %eax
void emit_pop_eax(CodeBuffer* buf) {
    emit_byte(buf, 0x58);
}

//pop %ebx
void emit_pop_ebx(CodeBuffer* buf) {
    emit_byte(buf, 0x5B);
}

//mov %eax , %ebx
void emit_mov_ebx_eax(CodeBuffer* buf) {
    emit_byte(buf, 0x89);
    emit_byte(buf, 0xC3);
}

//ret
void emit_ret(CodeBuffer* buf) {
    emit_byte(buf, 0xC3);
}

// sub %eax, %ebx (ebx = ebx - eax)
void emit_sub_ebx_eax(CodeBuffer* buf) {
    emit_byte(buf, 0x29);
    emit_byte(buf, 0xC3);
}

// mov %ebx, %eax
void emit_mov_eax_ebx(CodeBuffer* buf) {
    emit_byte(buf, 0x89);
    emit_byte(buf, 0xD8);
}

//=========THE LEXER ===========
typedef struct {
    char* source;
    char* current;
} Lexer;

void lexer_init(Lexer* lex, char* source) {
    lex->source = source;
    lex->current = source;
}

char lexer_peak(Lexer* lex) {
    return *lex->current;
}

char lexer_advance(Lexer* lex) {
    char c = *lex->current;
    if (c != '\0') lex->current++;
    return c;
}

void lexer_skip_whitespace(Lexer* lex) {
    while (lexer_peak(lex) == ' ' || lexer_peak(lex) == '\t' || 
           lexer_peak(lex) == '\n' || lexer_peak(lex) == '\r') {
        lexer_advance(lex);
    }
}

int is_digit(char c) {
    return c >= '0' && c <= '9';
}

Token lexer_next_token(Lexer* lex) {
    Token token;
    lexer_skip_whitespace(lex);
    token.start = lex->current;
    token.length = 1;

    char c = lexer_peak(lex);
    if (c == '\0') {
        token.type = TOKEN_EOF;
        return token;
    }

    if (is_digit(c)) {
        token.type = TOKEN_NUMBER;
        token.value = 0;
        while (isdigit(lexer_peak(lex))) {
            token.value = token.value * 10 + (lexer_advance(lex) - '0');
            token.length++;
        }
        token.length--;
        return token;
    }

    lexer_advance(lex);
    switch (c) {
        case '+': token.type = TOKEN_PLUS; break;
        case '-': token.type = TOKEN_MINUS; break;
        case '*': token.type = TOKEN_STAR; break;
        case '/': token.type = TOKEN_SLASH; break;
        case '(': token.type = TOKEN_LPAREN; break;
        case ')': token.type = TOKEN_RPAREN; break;
        default: token.type = TOKEN_ERROR; break;
    }
    return token;
}

//=========PARSER========
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

//ADD FORWARD DECLERATIONS....next
ASTNode* parse_expression(Parser* p);
ASTNode* parse_term(Parser* p);
ASTNode* parse_factor(Parser* p);

//Primary : Number or expressio
ASTNode* parse_primary(Parser* p) {
    if (parser_match(p, TOKEN_NUMBER)) {
        ASTNode* node = malloc(sizeof(ASTNode));
        node->type = NODE_NUMBER;
        node->value = p->previous.value;
        node->left = NULL;
        node->right = NULL;
        return node;
    }

    if (parser_match(p, TOKEN_LPAREN)) {
        ASTNode* expr = parse_expression(p);
        parser_match(p, TOKEN_RPAREN);
        return expr;
    }

    //error
    return NULL;
}

// Factor handles * and / (higher precedence)
ASTNode* parse_factor(Parser* p) {
    ASTNode* left = parse_primary(p);

    while (parser_match(p, TOKEN_STAR) || parser_match(p, TOKEN_SLASH)) {
        Token op = p->previous;
        ASTNode* right = parse_primary(p);

        ASTNode* node = malloc(sizeof(ASTNode));
        node->type = NODE_BINARY_OP;
        node->op = (op.type == TOKEN_STAR) ? '*' : '/';
        node->left = left;
        node->right = right;
        left = node;
    }

    return left;
}

// Term handles + and - (lower precedence)
ASTNode* parse_term(Parser* p) {
    ASTNode* left = parse_factor(p);

    while (parser_match(p, TOKEN_PLUS) || parser_match(p, TOKEN_MINUS)) {
        Token op = p->previous;
        ASTNode* right = parse_factor(p);

        ASTNode* node = malloc(sizeof(ASTNode));
        node->type = NODE_BINARY_OP;
        node->op = (op.type == TOKEN_PLUS) ? '+' : '-';
        node->left = left;
        node->right = right;
        left = node;
    }

    return left;
}

// Expression: term
ASTNode* parse_expression(Parser* p) {
    return parse_term(p);
}

// Parse entire input
ASTNode* parse(char* source) {
    Lexer lexer;
    lexer_init(&lexer, source);
    Parser parser;
    parser_init(&parser, &lexer);
    return parse_expression(&parser);
}

// Free AST
void free_ast(ASTNode* node) {
    if (!node) return;
    free_ast(node->left);
    free_ast(node->right);
    free(node);
}

//=========CODE GENERATOR================
void code_gen(ASTNode* node, CodeBuffer* buf) {
    if (node->type == NODE_NUMBER) {
        emit_mov_eax_imm(buf, node->value);
        return;
    }

    // Binary operation
    // Evaluate left subtree
    code_gen(node->left, buf);
    emit_push_eax(buf);  // Save left result

    // Evaluate right subtree
    code_gen(node->right, buf);
    
    // Now: eax = right, stack top = left
    emit_mov_ebx_eax(buf);  // ebx = right
    emit_pop_eax(buf);      // eax = left
    
    // Now: eax = left, ebx = right
    // Perform operations
    switch (node->op) {
        case '+':
            emit_add_eax_ebx(buf);  // eax = left + right
            break;
        case '-':
            emit_sub_eax_ebx(buf);  // eax = left - right
            break;
        case '*':
            emit_imul_eax_ebx(buf); // eax = left * right
            break;
        case '/':
            printf("Division not implemented yet\n");
            break;
    }
}

// -----EXECUTABLE MEMORY------//
void* allocate_executable_memory(size_t size) {
    void* mem = mmap(
        NULL,
        size,
        PROT_READ | PROT_WRITE | PROT_EXEC,
        MAP_PRIVATE | MAP_ANONYMOUS,
        -1,
        0
    );
    if (mem == MAP_FAILED) {
        perror("mmap");
        return NULL;
    }
    return mem;
}

//FREE EXECUTABLE MEMORY
void free_executable_memory(void* mem, size_t size) {
    munmap(mem, size);
}

//==========EXECUTION=========///
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

//=======COMPILE AND RUN ==========
int compile_and_run(char* source) {
    ASTNode* ast = parse(source);
    if (!ast) {
        fprintf(stderr, "Parse error\n");
        return -1;
    }

    //GENERATE THE CODE.....
    CodeBuffer* buf = code_buffer_new(1024);
    code_gen(ast, buf);
    emit_ret(buf);

    int results = execute_code(buf);

    //clean up
    free_ast(ast);
    code_buffer_free(buf);

    return results;
}


int main() {
    printf("=== JIT Compiler v0.2 - With Parser ===\n\n");
    
    // Test expressions
    char* tests[] = {
        "5 + 10",
        "20 - 5",
        "5 * 3",
        "(5 + 10) * 2",
        "10 + 5 * 2",
        "100 - 50 - 25",
        NULL
    };
    
    int expected[] = {15, 15, 15, 30, 20, 25};
    
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
