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

//========SYMBOL TABLE (NEW!)============
//This tracks all variables in your program
//Each variable gets a stack slot (offset from %ebp)
#define MAX_VARS 256

typedef struct {
    char name[64];      // Variable name like "x" or "foo"
    int stack_offset;   // Where on stack? -4, -8, -12, etc.
} Variable;

typedef struct {
    Variable vars[MAX_VARS];
    int count;          // How many variables we have
    int next_offset;    // Next available stack slot
} SymbolTable;

// Initialize the symbol table
void symbol_table_init(SymbolTable* st) {
    st->count = 0;
    st->next_offset = -4;  // Stack grows down, start at -4(%ebp)
}

// Add a variable (or return existing offset if already exists)
// Returns the stack offset for this variable
int symbol_table_add(SymbolTable* st, const char* name, int length) {
    // Check if variable already exists
    for (int i = 0; i < st->count; i++) {
        if (strncmp(st->vars[i].name, name, length) == 0 && 
            st->vars[i].name[length] == '\0') {
            return st->vars[i].stack_offset;  // Already exists, return its offset
        }
    }
    
    // Add new variable
    strncpy(st->vars[st->count].name, name, length);
    st->vars[st->count].name[length] = '\0';
    st->vars[st->count].stack_offset = st->next_offset;
    
    int offset = st->next_offset;
    st->next_offset -= 4;  // Next variable goes 4 bytes lower on stack
    st->count++;
    
    return offset;
}

// Look up a variable by name
// Returns stack offset, or 0 if it is not found
int symbol_table_lookup(SymbolTable* st, const char* name, int length) {
    for (int i = 0; i < st->count; i++) {
        if (strncmp(st->vars[i].name, name, length) == 0 && 
            st->vars[i].name[length] == '\0') {
            return st->vars[i].stack_offset;
        }
    }
    fprintf(stderr, "ERROR: Undefined variable '");
    fwrite(name, 1, length, stderr);
    fprintf(stderr, "'\n");
    return 0;  // Not found
}

//========LEXER(PARSER STRUCTURES)==============
typedef enum {
    TOKEN_NUMBER,     // 0..9
    TOKEN_PLUS,       // +
    TOKEN_MINUS,      // -
    TOKEN_STAR,       // *
    TOKEN_PERCENT,    // % (modulo division)
    TOKEN_SLASH,      // /
    TOKEN_LPAREN,     // (
    TOKEN_RPAREN,     // )
    TOKEN_IDENTIFIER, // NEW: variable names (x, foo, myVar)
    TOKEN_EQUALS,     // NEW: =
    TOKEN_SEMICOLON,  // NEW: ;
    TOKEN_EOF,        //"0\"
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
    NODE_NUMBER,         // 0..9
    NODE_BINARY_OP,      // math arithmetics e.g +
    NODE_UNARY_OP,       // - +
    NODE_ASSIGNMENT,     // NEW: x = 5
    NODE_VARIABLE,       // NEW: x (when you use it)
    NODE_STATEMENT_LIST  // NEW: multiple statements separated by ;
} NodeType;

//----AST NODE
typedef struct ASTNode {
    NodeType type;      // Does this node contain a number or an operation
    int value;          // Its value 0..9
    char op;            // its char '+'
    
    // NEW: For variables and assignments
    char var_name[64];  // Variable name
    int stack_offset;   // Where it lives on the stack
    
    struct ASTNode* left;   // Pointer to left
    struct ASTNode* right;  // Pointer to right
    
    // NEW: For statement lists
    struct ASTNode** statements;  // Array of statement nodes
    int statement_count;          // How many statements
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

void emit_cdq(CodeBuffer *buf){ 
    emit_byte(buf,0x99); //0x99 is op code for CDQ
}

//idiv - singed integer division.
//0xF7 => idiv , %ebx division family instruction
//0xFB divide by %ebx ( by whatever is in this register)
void emit_idiv_ebx(CodeBuffer * buf){ 
    emit_byte(buf,0xF7);
    emit_byte(buf,0xFB);
}

//move the remainder in edx after idiv to eax
//0x89 0xd0 => mov %edx , %eax
void emit_mov_eax_edx(CodeBuffer *buf){ 
    emit_byte(buf,0x89);
    emit_byte(buf,0xD0);
}

//emit func => negattin - eax = -eax
// 0xF7 0xD8 => neg %eax ( asmx86)
// How it works: 
//          before eax = -5 
//          after eax = 5 
//      + uses two complements =>> the num e.g 0x00000005 and not = 0xFFFFFFFFA then plus 1 
//      = 0xFFFFFFFB = - 5

void emit_neg_eax(CodeBuffer* buf){ 
    emit_byte(buf,0xF7); 
    emit_byte(buf,0xD8);
}

//==== NEW EMIT FUNCTIONS FOR STACK FRAME ====

// push %ebp - save old base pointer
void emit_push_ebp(CodeBuffer* buf) {
    emit_byte(buf, 0x55);
}

// pop %ebp - restore base pointer
void emit_pop_ebp(CodeBuffer* buf) {
    emit_byte(buf, 0x5D);
}

// mov %esp, %ebp - set up new stack frame
void emit_mov_ebp_esp(CodeBuffer* buf) {
    emit_byte(buf, 0x89);
    emit_byte(buf, 0xE5);
}

// mov %ebp, %esp - restore stack pointer
void emit_mov_esp_ebp(CodeBuffer* buf) {
    emit_byte(buf, 0x89);
    emit_byte(buf, 0xEC);
}

// sub $N, %esp - allocate N bytes on stack for local variables
void emit_sub_esp_imm8(CodeBuffer* buf, uint8_t value) {
    emit_byte(buf, 0x83);
    emit_byte(buf, 0xEC);
    emit_byte(buf, value);
}

// mov %eax, offset(%ebp) - store eax to stack at offset
// offset is SIGNED (negative for local vars)
void emit_mov_to_stack(CodeBuffer* buf, int offset) {
    emit_byte(buf, 0x89);
    emit_byte(buf, 0x45);  // ModRM byte for [%ebp + disp8]
    emit_byte(buf, offset & 0xFF);  // Offset (signed 8-bit)
}

// mov offset(%ebp), %eax - load from stack to eax
void emit_mov_from_stack(CodeBuffer* buf, int offset) {
    emit_byte(buf, 0x8B);
    emit_byte(buf, 0x45);  // ModRM byte for [%ebp + disp8]
    emit_byte(buf, offset & 0xFF);  // Offset (signed 8-bit)
}

// Function prologue - sets up stack frame
// total_vars = number of local variables (we allocate 4 bytes each)
void emit_prologue(CodeBuffer* buf, int total_vars) {
    emit_push_ebp(buf);        // Save old base pointer
    emit_mov_ebp_esp(buf);     // Set up new frame
    
    // Allocate space for local variables if needed
    if (total_vars > 0) {
        emit_sub_esp_imm8(buf, total_vars * 4);
    }
}

// Function epilogue - tears down stack frame
void emit_epilogue(CodeBuffer* buf) {
    emit_mov_esp_ebp(buf);     // Restore stack pointer
    emit_pop_ebp(buf);         // Restore base pointer
    emit_ret(buf);             // Return
}


typedef struct {
    char* source; //Original string parsed "5 + 10" points to the beginning of this
    char* current; //where the current pointer is ... 
} Lexer;

//Initiate lxer
void lexer_init(Lexer* lex, char* source) {
    lex->source = source;
    lex->current = source;
}

//returns adress of current char from source
char lexer_peak(Lexer* lex) {
    return *lex->current;
}

//Steping on the bytes .. basic str reading
//read until EOF 
//returns current char  e.g .. space or a number or a op( + or _ ... ) 
char lexer_advance(Lexer* lex) {
    char c = *lex->current;
    if (c != '\0') lex->current++;
    return c;
}
//SKIPS TABS SPACES AND NEW LINES AND ALL TO PRORESS TO THE NEXT VALID CHAR .. LIKE A NUMBER OR OP
void lexer_skip_whitespace(Lexer* lex) {
    while (lexer_peak(lex) == ' ' || lexer_peak(lex) == '\t' || 
           lexer_peak(lex) == '\n' || lexer_peak(lex) == '\r') {
        lexer_advance(lex);
    }
}

//check if char is a digit or what .. 
//uses asci code bounds ( learn them if you do not get them)
int is_digit(char c) {
    return c >= '0' && c <= '9';
}

// NEW: Check if character is alphabetic or underscore
int is_alpha(char c) {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
}

// NEW: Check if character is alphanumeric
int is_alphanumeric(char c) {
    return is_alpha(c) || is_digit(c);
}

//Reads the source and returns the next "token"
//Token is ... a token .. in this case its a didgit or the op .. or paranthesis
//Still skipping the white spaces and tabs and all 
//peak the source to get the char
//and do basic checks like of end of file or mapping it to a number if it is or an op or paren
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

    // NEW: Handle identifiers (variable names)
    if (is_alpha(c)) {
        token.type = TOKEN_IDENTIFIER;
        token.start = lex->current;
        token.length = 0;
        
        while (is_alphanumeric(lexer_peak(lex))) {
            lexer_advance(lex);
            token.length++;
        }
        
        return token;
    }

    lexer_advance(lex);
    switch (c) {
        case '+': token.type = TOKEN_PLUS; break;
        case '-': token.type = TOKEN_MINUS; break;
        case '*': token.type = TOKEN_STAR; break;
        case '/': token.type = TOKEN_SLASH; break;
        case '%': token.type = TOKEN_PERCENT; break; 
        case '(': token.type = TOKEN_LPAREN; break;
        case ')': token.type = TOKEN_RPAREN; break;
        case '=': token.type = TOKEN_EQUALS; break;      // NEW
        case ';': token.type = TOKEN_SEMICOLON; break;   // NEW
        default: token.type = TOKEN_ERROR; break;
    }
    return token;
}

//=========PARSER========
typedef struct {
    Lexer* lexer;
    Token current;
    Token previous;
    SymbolTable* symbols;  // NEW: Need access to symbol table
} Parser;


//Initialise parser 
//Params: 
//      parser adress
//      lexer adress
//      symbol table address (NEW)

void parser_init(Parser* p, Lexer* lex, SymbolTable* st) {
    p->lexer = lex;
    p->symbols = st;
    p->current = lexer_next_token(lex);
}


//what does this do: 
//                  consumes a token and gets the next one
//                  parse current to prev and then the next becomes current
void parser_advance(Parser* p) {
    p->previous = p->current;
    p->current = lexer_next_token(p->lexer);
}

//helper for the method bellow
int parser_check(Parser* p, TokenType type) {
    return p->current.type == type;
}

//checks token type... .kinda like confirm 
//         e.g => parser_check( plus , TOKEN_TYPE_PLUS)
//          returns 1 ( true) if not returns 0 ( false)
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
ASTNode* parse_unary(Parser* p);
ASTNode* parse_statement(Parser* p);  // NEW

//Primary : Number or expression or VARIABLE (NEW)
//if its a number create a new node of that number (when created it has null childs( left == right ==nul))
//allocates that size of node ( basic c stuff)
//sets value as previous ( consumed .. look for the next one)
//curr is "prev"
//returns adress to that node
//
ASTNode* parse_primary(Parser* p) {
    if (parser_match(p, TOKEN_NUMBER)) {
        ASTNode* node = malloc(sizeof(ASTNode));
        node->type = NODE_NUMBER;
        node->value = p->previous.value;
        node->left = NULL;
        node->right = NULL;
        return node;
    }

    // NEW: Handle variable usage (like "x" in "x + 5")
    if (parser_match(p, TOKEN_IDENTIFIER)) {
        ASTNode* node = malloc(sizeof(ASTNode));
        node->type = NODE_VARIABLE;
        
        Token var = p->previous;
        strncpy(node->var_name, var.start, var.length);
        node->var_name[var.length] = '\0';
        
        // Look up variable in symbol table
        node->stack_offset = symbol_table_lookup(p->symbols, var.start, var.length);
        
        node->left = NULL;
        node->right = NULL;
        return node;
    }

    //check expressions ( left_paran ( ")") and the other one as well)
    //returns that expr
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
    ASTNode* left = parse_unary(p);

    while (parser_match(p, TOKEN_STAR) || parser_match(p, TOKEN_SLASH) || parser_match(p, TOKEN_PERCENT)) { 
        Token op = p->previous;
        ASTNode* right = parse_unary(p);

        ASTNode* node = malloc(sizeof(ASTNode));;

        node->type = NODE_BINARY_OP;
        node->op = (op.type == TOKEN_STAR) ? '*' : (op.type == TOKEN_SLASH) ? '/' : '%';
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

ASTNode* parse_unary(Parser* p) { 
    if (parser_match(p, TOKEN_MINUS) || parser_match(p, TOKEN_PLUS)) {
        Token op = p->previous; 
        ASTNode* right = parse_unary(p); 

        ASTNode* node = malloc(sizeof(ASTNode));
    
        node->type = NODE_UNARY_OP;
        node->op = (op.type == TOKEN_MINUS) ? '-' : '+';
        node->left = NULL; 
        node->right = right; 

        return node;
    }

    return parse_primary(p);
}


//helper
Token parser_peek_next(Parser* p) {
    Lexer tmp = *(p->lexer);              // copy lexer state
    return lexer_next_token(&tmp);        // read next token from the copy
}

ASTNode* parse_statement(Parser* p) {
    if (parser_check(p, TOKEN_IDENTIFIER)) {
        Token var = p->current;
        Token next = parser_peek_next(p);

        if (next.type == TOKEN_EQUALS) {
            parser_advance(p);
            parser_match(p, TOKEN_EQUALS);

            ASTNode* node = malloc(sizeof(ASTNode));
            node->type = NODE_ASSIGNMENT;

            strncpy(node->var_name, var.start, var.length);
            node->var_name[var.length] = '\0';

            node->stack_offset = symbol_table_add(p->symbols, var.start, var.length);
            node->right = parse_expression(p);
            node->left = NULL;
            return node;
        }
    }
    return parse_expression(p);
}



// NEW: Parse entire program (multiple statements separated by semicolons)
ASTNode* parse_program(Parser* p) {
    ASTNode* root = malloc(sizeof(ASTNode));
    root->type = NODE_STATEMENT_LIST;
    root->statements = malloc(sizeof(ASTNode*) * 256);  // Max 256 statements
    root->statement_count = 0;
    
    while (!parser_check(p, TOKEN_EOF)) {
        ASTNode* stmt = parse_statement(p);
        if (stmt) {
            root->statements[root->statement_count++] = stmt;
        }
        

        //fix : if not at at eof , epect semicolon betwem statements.
        if (!parser_check(p, TOKEN_EOF)) {
            if (!parser_match(p, TOKEN_SEMICOLON)) {
                fprintf(stderr, "ERROR: Expected ';' between statements\n");
                break;
            }
        }
        
        if (root->statement_count >= 256) break;
    }
    root->left = NULL;
    root->right = NULL;
    
    return root;
}

// Parse entire input (UPDATED to use symbol table)
ASTNode* parse(char* source, SymbolTable* st) {
    Lexer lexer;
    lexer_init(&lexer, source);
    Parser parser;
    parser_init(&parser, &lexer, st);
    return parse_program(&parser);
}

// Free AST (UPDATED to handle new node types)
void free_ast(ASTNode* node) {
    if (!node) return;
    
    if (node->type == NODE_STATEMENT_LIST) {
        for (int i = 0; i < node->statement_count; i++) {
            free_ast(node->statements[i]);
        }
        free(node->statements);
    }
    
    free_ast(node->left);
    free_ast(node->right);
    free(node);
}
//gdb
void print_ast(ASTNode* node, int depth) {
    if (!node) {
        printf("%*sNULL\n", depth * 2, "");
        return;
    }
    
    if (node->type == NODE_NUMBER) {
        printf("%*sNUMBER: %d\n", depth * 2, "", node->value);
    } else if (node->type == NODE_VARIABLE) {
        printf("%*sVARIABLE: %s (offset: %d)\n", depth * 2, "", node->var_name, node->stack_offset);
    } else if (node->type == NODE_ASSIGNMENT) {
        printf("%*sASSIGNMENT: %s (offset: %d)\n", depth * 2, "", node->var_name, node->stack_offset);
        print_ast(node->right, depth + 1);
    } else if (node->type == NODE_UNARY_OP) {
        printf("%*sUNARY: %c\n", depth * 2, "", node->op);
        print_ast(node->right, depth + 1);
    } else if (node->type == NODE_STATEMENT_LIST) {
        printf("%*sSTATEMENT_LIST (%d statements):\n", depth * 2, "", node->statement_count);
        for (int i = 0; i < node->statement_count; i++) {
            print_ast(node->statements[i], depth + 1);
        }
    } else {
        printf("%*sBINARY: %c\n", depth * 2, "", node->op);
        print_ast(node->left, depth + 1);
        print_ast(node->right, depth + 1);
    }
}

//=========CODE GENERATOR (UPDATED)================
void code_gen(ASTNode* node, CodeBuffer* buf) {
    if (node->type == NODE_NUMBER) {
        emit_mov_eax_imm(buf, node->value);
        return;
    }

    // NEW: Load variable from stack
    if (node->type == NODE_VARIABLE) {
        emit_mov_from_stack(buf, node->stack_offset);
        return;
    }

    // NEW: Store to variable
    if (node->type == NODE_ASSIGNMENT) {
        // Evaluate the right side (value being assigned)
        code_gen(node->right, buf);
        // Store result (in eax) to stack
        emit_mov_to_stack(buf, node->stack_offset);
        // Assignment returns the value too (in eax)
        return;
    }

    // NEW: Handle statement list
    if (node->type == NODE_STATEMENT_LIST) {
        for (int i = 0; i < node->statement_count; i++) {
            code_gen(node->statements[i], buf);
        }
        // Last statement's result stays in eax (our return value)
        return;
    }

    if (node->type == NODE_UNARY_OP) {
        code_gen(node->right, buf);
        
        switch (node->op) {
            case '-': 
                emit_neg_eax(buf);
                break;
            case '+': 
                break;
        }
        return;
    }

    // Binary operation - same as before!
    code_gen(node->left, buf);
    emit_push_eax(buf);
    
    code_gen(node->right, buf);
    emit_mov_ebx_eax(buf);
    emit_pop_eax(buf);
    
    switch (node->op) {
        case '+':
            emit_add_eax_ebx(buf);
            break;
        case '-':
            emit_sub_eax_ebx(buf);
            break;
        case '*':
            emit_imul_eax_ebx(buf);
            break;
        case '/':
            emit_cdq(buf);
            emit_idiv_ebx(buf);
            break;
        case '%': 
            emit_cdq(buf);
            emit_idiv_ebx(buf);
            emit_mov_eax_edx(buf);
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

void free_executable_memory(void* mem, size_t size) {
    munmap(mem, size);
}

//==========EXECUTION (UPDATED)=========//
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

//=======COMPILE AND RUN (UPDATED)==========
int compile_and_run(char* source) {
    // NEW: Create symbol table
    SymbolTable symbols;
    symbol_table_init(&symbols);
    
    // Parse with symbol table
    ASTNode* ast = parse(source, &symbols);
    if (!ast) {
        fprintf(stderr, "Parse error\n");
        return -1;
    }

    printf("AST for '%s':\n", source);
    print_ast(ast, 0);
    printf("\n");

    // Generate code
    CodeBuffer* buf = code_buffer_new(1024);
    
    // NEW: Emit function prologue (sets up stack frame)
    emit_prologue(buf, symbols.count);
    
    // Generate code for the AST
    code_gen(ast, buf);
    
    // NEW: Emit function epilogue (cleans up and returns)
    emit_epilogue(buf);

    int result = execute_code(buf);

    // Clean up
    free_ast(ast);
    code_buffer_free(buf);

    return result;
}


int main() {
    printf("=== JIT Compiler v0.3 - With Variables ===\n\n");
    
    // Test expressions with variables!
    char* tests[] = {
        "5 + 10",           // Old test - still works
        "x = 5",            // NEW: assignment
        "x = 5; x",         // NEW: assign then use
        "x = 5; y = 10; x + y",  // NEW: multiple vars
        "x = 5; x * 2",     // NEW: use in expression
        "a = 10; b = 20; a + b * 2",  // NEW: precedence with vars
        "x = -5; x + 10",   // NEW: negative assignment
        "x = 10; y = 3; x % y",  // NEW: modulo with vars
        NULL
    };
    
    int expected[] = {15, 5, 5, 15, 10, 50, 5, 1};
    
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
