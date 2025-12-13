#include <ctype.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <unistd.h>


//The code buffer-------------

typedef struct { 
    uint8_t* code;
    size_t size;
    size_t capacity;

} CodeBuffer;

//New buffer 
//Returns a new buffer 
CodeBuffer* code_buffer_new(size_t initial_capacity) { 
    CodeBuffer* buf = malloc(sizeof(CodeBuffer));
    buf -> capacity = initial_capacity ; 
    buf -> code = malloc(buf -> capacity);
    buf -> size = 0; 
    return buf;
}


void code_buffer_free( CodeBuffer * buf ){ 
    free(buf -> code);
    free(buf);
}

//========LEXER(PARSER STRUCTURES)==============

typedef enum { 

    TOKEN_NUMBER, 
    TOKEN_PLUS,
    TOKEN_MINUS,
    TOKEN_STAR,
    TOKEN_SLASH, 
    TOKEN_LPAREN, 
    TOKEN_RPAREN,
    TOKEN_EOF, //end of file (null terminator)
    TOKEN_ERROR
}TokenType ;

//Token 

typedef struct { 
    TokenType type;
    int value;          //Token number
    char* start;         //For error messages 
    int length;
}Token;

//----AST NODE TYPES

typedef enum { 
    NODE_NUMBER, 
    NODE_BINARY_OP
} NodeType;


//----AST NODE 

typedef struct{ 
    NodeType type;              //Number or binary op
    int value;                  //For node number
    char op;                    //includes the basic math ops for now .. + , - , / ,* 
    struct ASTNode* left;
    struct ASTNode* right;
} ASTNode;


//-------EMIT FUNCTIONS---THE FUN STUFF(FOR ME.)
void emit_byte(CodeBuffer* buf , uint8_t byte){ 
    if (buf -> size >= buf -> capacity){ 
        buf -> capacity *= 2; 
        buf -> code = realloc(buf -> code, buf -> capacity);
    }
    buf -> code[buf -> size++] = byte;
}

void emit_u32(CodeBuffer* buf , uint32_t value){ 
    emit_byte(buf , value & 0xFF);
    emit_byte(buf , (value >> 8) & 0xFF);
    emit_byte(buf , (value >> 16) & 0xFF);
    emit_byte(buf , (value >> 24) & 0xFF);
}

//instrution : mov imm_value , %eax
void emit_mov_eax_imm(CodeBuffer* buf , uint32_t value){ 
    emit_byte(buf, 0xB8);
    emit_u32(buf, value);
}

//instrution : mov imm_value , %ebx => emit functio
void emit_mov_ebx_imm(CodeBuffer* buf , uint32_t value){ 
    emit_byte(buf, 0xBB);
    emit_u32(buf, value);
}

//emit add imm8 , %eax 

void emit_add_eax_imm8(CodeBuffer* buf , uint8_t value){ 
    emit_byte(buf, 0x83);
    emit_byte(buf, 0xC0);
    emit_byte(buf, value);
}

//add ebx , eax 

void emit_add_eax_ebx(CodeBuffer* buf){ 
    emit_byte(buf, 0x01);
    emit_byte(buf, 0xD8);
}

//sub imm8 , eax

void emit_sub_eax_imm8(CodeBuffer* buf , uint8_t value){ 
    emit_byte(buf, 0x83);
    emit_byte(buf, 0xE8);
    emit_byte(buf, value);
}

//sub ebx , eax

void emit_sub_eax_ebx(CodeBuffer* buf){ 
    emit_byte(buf, 0x29);
    emit_byte(buf, 0xD8);
}

//emit imul %ebx , %eax

void emit_imul_eax_ebx(CodeBuffer* buf){ 
    emit_byte(buf, 0x0F);
    emit_byte(buf, 0xAF);
    emit_byte(buf, 0xC3);
}

//emit push %eax

void emit_push_eax(CodeBuffer* buf){ 
    emit_byte(buf, 0x50);
}

//pop %eax
void emit_pop_eax(CodeBuffer* buf){ 
    emit_byte(buf, 0x58);
}

//mov %eax , %ebx

void emit_mov_ebx_eax(CodeBuffer* buf){
    emit_byte(buf, 0x89);
    emit_byte(buf, 0xC3);
}

//ret

void emit_ret(CodeBuffer* buf){ 
    emit_byte(buf, 0xC3);
}


//=========THE LEXER ===========

typedef struct{ 
    char* source;
    char* current;
} Lexer;

void lexer_init(Lexer* lex , char* source){ 
    lex->source = source ; 
    lex->current = source;
}

char lexer_peak(Lexer* lex){ 
    return *lex->current;
}

char lexer_advance(Lexer* lex){
    char c = *lex->current; 

    if (c != '\0') lex-> current++;
    return c;
}

void lexer_skip_whitespace(Lexer* lex){ 
    while ( lexer_peak(lex) ==' ' ||
            lexer_peak(lex) =='\t' ||
            lexer_peak(lex) =='\n' ||
            lexer_peak(lex) =='\r'
            ) {
        lexer_advance(lex);
    }
}

int is_digit(char c){
    return c >= '0' && c <= '9';
}

Token lexer_next_token(Lexer* lex){
    Token token; 
    lexer_skip_whitespace(lex); 

    token.start = lex -> current; 
    token.length = 1; 

    char c = lexer_peak(lex); 

    if (c == '\0'){ 
        token.type = TOKEN_EOF; 
        return token;
    }

    if (is_digit(c)){ 
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
        default:
            token.type = TOKEN_ERROR;
            break;
    }
    return token;
}

//=========PARSER========

typedef struct{ 
    Lexer* lexer;
    Token current;
    Token previous;
}Parser;

void parser_init(Parser* p , Lexer* lex){ 
    p -> lexer = lex; 
    p -> current = lexer_next_token(lex);
}

void parser_advance(Parser* p){ 
    p -> previous = p -> current; 
    p -> current = lexer_next_token(p -> lexer); 
}

int parser_check(Parser* p, TokenType type){ 
    return p->current.type == type;
}

int parser_match(Parser* p , TokenType type){ 
    if (parser_check(p, type)) {
        parser_advance(p);

        return 1;
    }
    return 0;
}

//ADD FORWARD DECLERATIONS....next




























// -----EXECUTABLE MEMORY------//

void* allocate_executable_memory(size_t size){
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
void free_executable_memory(void* mem , size_t size){ 
    munmap(mem , size);
}

//==========EXECUTION=========///

int execute_code(CodeBuffer* buf){ 

    void* exec_mem = allocate_executable_memory(buf -> size); 
    
    if (!exec_mem) {
        fprintf(stderr,"Failed to allocate executable memory \n");
        return -1;
    }

    memcpy(exec_mem, buf->code, buf->size);
    
    int (*func)() = (int (*)())exec_mem;
    
    int result = func();

    free_executable_memory(exec_mem , buf->size);

    return result;
}


int main() {
    printf("=== JIT Compiler v0.1 ===\n\n");
    
    CodeBuffer* buf = code_buffer_new(1024);
    
    // Test 1: 5 + 10
    printf("Test 1: 5 + 10\n");
    buf->size = 0;  // Reset buffer
    
    emit_mov_eax_imm(buf, 5);
    emit_add_eax_imm8(buf, 10);
    emit_ret(buf);
    
    printf("Generated bytes: ");
    for (size_t i = 0; i < buf->size; i++) {
        printf("%02X ", buf->code[i]);
    }
    printf("\n");
    
    int result = execute_code(buf);
    printf("Result: %d (expected 15)\n", result);
    printf("%s\n\n", result == 15 ? "PASS" : "FAIL");
    
    // Test 2: 20 - 5
    printf("Test 2: 20 - 5\n");
    buf->size = 0;
    
    emit_mov_eax_imm(buf, 20);
    emit_sub_eax_imm8(buf, 5);
    emit_ret(buf);
    
    printf("Generated bytes: ");
    for (size_t i = 0; i < buf->size; i++) {
        printf("%02X ", buf->code[i]);
    }
    printf("\n");
    
    result = execute_code(buf);
    printf("Result: %d (expected 15)\n", result);
    printf("%s\n\n", result == 15 ? "PASS" : "FAIL");
    
    // Test 3: 5 * 3 (using registers)
    printf("Test 3: 5 * 3\n");
    buf->size = 0;
    
    emit_mov_eax_imm(buf, 5);      // eax = 5
    emit_mov_ebx_imm(buf, 3);      // ebx = 3
    emit_imul_eax_ebx(buf);        // eax = eax * ebx
    emit_ret(buf);
    
    printf("Generated bytes: ");
    for (size_t i = 0; i < buf->size; i++) {
        printf("%02X ", buf->code[i]);
    }
    printf("\n");
    
    result = execute_code(buf);
    printf("Result: %d (expected 15)\n", result);
    printf("%s\n\n", result == 15 ? "PASS" : "FAIL");
    
    // Test 4: (5 + 10) * 2 - complex expression using stack
    printf("Test 4: (5 + 10) * 2\n");
    buf->size = 0;
    
    emit_mov_eax_imm(buf, 5);      // eax = 5
    emit_add_eax_imm8(buf, 10);    // eax = 15
    emit_push_eax(buf);            // save result
    emit_mov_eax_imm(buf, 2);      // eax = 2
    emit_mov_ebx_eax(buf);         // ebx = 2
    emit_pop_eax(buf);             // eax = 15
    emit_imul_eax_ebx(buf);        // eax = 15 * 2
    emit_ret(buf);
    
    printf("Generated bytes: ");
    for (size_t i = 0; i < buf->size; i++) {
        printf("%02X ", buf->code[i]);
    }
    printf("\n");
    
    result = execute_code(buf);
    printf("Result: %d (expected 30)\n", result);
    printf("%s\n\n", result == 30 ? "PASS" : "FAIL");
    
    code_buffer_free(buf);
    
    printf("=== All tests complete ===\n");
    
    return 0;
}
