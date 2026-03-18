
/**
 * ---------THE CODE GENERATOR-------
 * First of all wgy is it called a code generator 
 * well because it emits x86 byte codes 
 * Imagine you want to add two numbers 
 * So you will have some function that emits bytecode for that
 * using the x86 syn 
 * for example  
 * add(7 + 9)
 * will be "mapped into something like" 
 * emit_add_eax_ebx() where eax is the first arg and ebx is secon
 *
 */

use crate::{interpreter::Value, parser::{BinOpKind, Expr, Program, Stmt, UnaryOpKind}};

/**
 * --- THE CODE BUFFER , 
 * A  growable list of bytesc
 * these are the bytes that the CPU will execute.
 * 
 */

pub  struct CodeBuffer { 
    pub bytes : Vec<u8>,
}

impl  CodeBuffer {
    // create a new buffer.....
    fn new() -> Self { 
        CodeBuffer { bytes: Vec::with_capacity(1024)}
    }
    //push one byte
    pub  fn emit(&mut self , byte : u8) {
        self.bytes.push(byte);
    }

    //push a 32 bit value in little-endian order
    //because x86 is little-edian(least significant byte first)

    pub fn emit_u32(&mut self , value : u32) {
        self.emit((value & 0xFF) as u8); // first byte least sign
        self.emit(((value >> 8) & 0xFF ) as u8); // byte 1 
        self.emit(((value >> 16) & 0xFF ) as u8); // byte 2
        self.emit(((value >> 24) & 0xFF ) as u8); // last byte(most sig)
    }

    /** ------ INSTRUCTION EMITTERS--------
     * Each one is named after its own x86 instruction it emits 
     * The comments you see are the the actual x86 asm instructions.
     */

    //mov $imm32 , %eax     [B8 imm32]

    pub fn mov_eax_imm(&mut self , val :  u32) {
        self.emit(0xB8);
        self.emit_u32(val);
    }

    //mov $imm32 , %ebx      [BB imm32]
     pub fn mov_ebx_imm(&mut self , val :  u32) {
        self.emit(0xBB);
        self.emit_u32(val);
     } 

     // add %ebx , %eax         [01 D8]
     pub  fn add_eax_ebx(&mut self) {
         self.emit(0x01);
         self.emit(0xD8);
     }
    
    // sub %ebx , %eax         [29 D8]
     pub  fn sub_eax_ebx(&mut self) {
         self.emit(0x29);
         self.emit(0xD8);
     }

     //imul , %ebx , %eax       [0F AF C3]
     pub fn imul_eax_ebx(&mut self){ 
         self.emit(0x0F);
         self.emit(0xAF);
         self.emit(0xC3);
     }

     //push , %eax      [50]
     pub  fn push_eax(&mut self) { self.emit(0x50);}

     //pop %eax         [58]
     pub  fn pop_eax(&mut self) {
         self.emit(0x58); }
     
     //pop &ebx         [5B]
     pub fn pop_ebx(&mut self) { self.emit(0x5b);}

     // mov %eax , %ebx     [89 C3]
     pub fn mov_ebx_eax(&mut self) {
         self.emit(0x89);
         self.emit(0xC3);
     }
     
    // mov %eax , %ebx     [89 D8]
     pub fn mov_eax_ebx(&mut self) {
         self.emit(0x89);
         self.emit(0xD8);
     }


     //neg % eax        [F7 D8]
     fn neg_eax(&mut self) {
         self.emit(0xF7);
         self.emit(0xD8);
     }

     //convert double to quad.
     //sign exented eax  into edx:eax   [99]
     fn cdq(&mut self) { 
         self.emit(0x99);
     }
    
     //idiv %ebx        [F7 FB]
     fn idiv_ebx(&mut self) {
         self.emit(0xF7);
         self.emit(0xFB);
     }

     //mov %edc , %eax      [89 F0]
     //move the remainder to eax after division 
     //iseful in lke mod divs 
     fn mov_eax_edx(&mut self) { 
         self.emit(0x89);
         self.emit(0xD0);
     }


     // ret     [C3]
     fn ret (&mut self) {
         self.emit(0xC3);
     }

      // ----------STACK INSTRUCTIONS--------

     //push ebp             [55]

     fn push_ebp(&mut self) { 
         self.emit(0x55); 
     }
     
    //pop ebp             [5D]

     fn pop_ebp(&mut self) { 
         self.emit(0x5D); 
     }

     // mov rbp, rsp        [48 89 E5]  (REX.W for 64-bit operands)
     fn mov_ebp_esp(&mut self) {
         self.emit(0x48); // REX.W
         self.emit(0x89);
         self.emit(0xE5);
     }

     // mov rsp, rbp        [48 89 EC]  (REX.W for 64-bit operands)
     fn mov_esp_ebp(&mut self) {
         self.emit(0x48); // REX.W
         self.emit(0x89);
         self.emit(0xEC);
     }

     // sub rsp, imm8       [48 83 EC imm8]  (REX.W for 64-bit operands)
     fn sub_esp_imm8(&mut self , n :u8) {
         self.emit(0x48); // REX.W
         self.emit(0x83);
         self.emit(0xEC);
         self.emit(n);
     }


    // mov %eax, disp8(%ebp)   [89 45 disp]   — store to stack slot
    
     fn  mov_to_stack(&mut self ,offset: i8) {
         self.emit(0x89);
         self.emit(0x45);
         self.emit(offset as u8);
     }

    // mov disp8(%ebp), %eax   [8B 45 disp]   — load from stack slot


     fn  mov_from_stack(&mut self ,offset: i8) {
         self.emit(0x8B);
         self.emit(0x45);
         self.emit(offset as u8);
     }

     // functon prologue

     fn prologue(&mut self , n_vars : usize) {
         self.push_ebp();
        self.mov_ebp_esp();

         if n_vars > 0 { 
             self.sub_esp_imm8((n_vars * 4) as u8);
         }
     }

     //emit function epilogue

     fn epilogue(&mut self) {
         self.mov_esp_ebp();
         self.pop_ebp();
         self.ret();
     }

     pub fn emit_je_rel32(&mut self) -> usize {
         self.emit(0x0F);
         self.emit(0x84);
         let patch_pos = self.current_pos(); 
         self.emit_u32(0);
         patch_pos
     }

     pub  fn emit_jmp_rel32(&mut self) -> usize {
         self.emit(0xE9);
         let patch_pos = self.current_pos(); 
         self.emit_u32(0);
         patch_pos
     }

     pub fn current_pos(&self) -> usize { 
         self.bytes.len()
     }

     pub fn patch_u32(&mut self , pos: usize , val :  u32) {
         self.bytes[pos]    =(val & 0xFF) as u8;
         self.bytes[pos+1]  = ((val >> 8) & 0xFF) as u8;
         self.bytes[pos+2]  = ((val >> 16) & 0xFF) as u8;
         self.bytes[pos+3]  = ((val >> 24) & 0xFF) as u8;
     }

     pub  fn cmp_eax_ebx(&mut self){ 
        self.emit(0x39);
        self.emit(0xD8);
     }

     // equals to
     pub fn sete_al(&mut self) {
         self.emit(0x0F);
         self.emit(0x94);
         self.emit(0xC0);
     }

     //not equals to.
     pub fn setne_al(&mut self) {
         self.emit(0x0F);
         self.emit(0x95);
         self.emit(0xC0);
     }

     //less than 
     pub fn setl_al(&mut self) {
         self.emit(0x0F);
         self.emit(0x9C);
         self.emit(0xC0);
     }

     // greater than
     pub fn setg_al(&mut self) {
         self.emit(0x0F);
         self.emit(0x9F);
         self.emit(0xC0);
     }

     //less of equal to
     pub fn setle_al(&mut self) {
         self.emit(0x0F);
         self.emit(0x9E);
         self.emit(0xC0); 
     }

     //greater or equal to
     pub fn setge_al(&mut self) {
         self.emit(0x0F);
         self.emit(0x9D);
         self.emit(0xC0);
     }

     //move Z flag value from al to eax
     pub fn movzx_eax_al(&mut self) {
         self.emit(0x0F);
         self.emit(0xB6);
         self.emit(0xC0);
     }

     pub fn test_eax_eax(&mut self) { 
         self.emit(0x85);
         self.emit(0xC0); 
     }
}


// ------------- SYMBOL TABLE-------------
// Uses varibles in stack offests 
// uses hashmap  to build the table and store variables as keys 
// offests as value.

use std::{collections::HashMap, i32, mem::offset_of,usize};

pub struct  SymbolTable { 
    vars :HashMap<String , i8>,
    next_offest : i8,
}

impl SymbolTable {
    //constructor....
    pub fn new() ->Self {
        SymbolTable {
            vars: HashMap::new(),
            next_offest: -4
        }
    }
    //Add a new variable , if it exists , get its offest.

    pub fn add(&mut self , name :&str)-> i8 {
        if let Some(&offset) = self.vars.get(name) { 
            return offset
        }

        let offset  = self.next_offest;
        self.vars.insert(name.to_string(), offset);
        self.next_offest -= 4;
        offset
    }

    //gets a variable
    //returns its offset on the stack if it exist s
    //else panic and say its not defined in that env /scope
    pub  fn get(&mut self, name :&str) -> i8 {
        *self.vars.get(name)
            .unwrap_or_else(|| panic!("Undefined variable '{}' ", name))
    }

    pub fn count(&self) -> usize {
        self.vars.len()
    }
}

// ----------THE CODE GENERATOR-------------

pub struct CodeGen { 
    pub buf :CodeBuffer , 
    pub symbols : SymbolTable,
}

impl CodeGen {
    //new code buffer...
    pub  fn new() -> Self{
        CodeGen {
            buf: CodeBuffer::new(),
            symbols: SymbolTable::new()
        }
    }
    // First pass :scan the AST  and collect all variable names
    // so we can knwo how much stack space to we have to reserve
    // for them

    fn collect_vars(&mut self , program :&Program){
        for stmt in program { 
            self.collect_var_stmt(stmt);
        }
    }

    //helper functio to collect variables
    fn collect_var_stmt(&mut self , stmt : &Stmt) {
        match stmt {
            Stmt::Expr(e) | Stmt::Return(e) => self.collect_vars_expr(e),
            Stmt::FnDef {body ,..} => { 
                for s in body { self.collect_var_stmt(s);}
            }
        }
    }

    fn collect_vars_expr(&mut self, expr : &Expr) {
        match expr {
            Expr::Assign { name, value } => { 
                self.symbols.add(name);
                self.collect_vars_expr(value);
            }

            Expr::BinOp { left, right,.. } => { 
                self.collect_vars_expr(left);
                self.collect_vars_expr(right);
            }

            Expr::UnaryOp {expr,..} => { 
                self.collect_vars_expr(expr)
            }

            Expr::If { cond, then_block, else_block } => {
                self.collect_vars_expr(cond);
                for s in then_block { self.collect_var_stmt(s);}

                if let Some(eb)  = else_block { 
                    for s in eb {self.collect_var_stmt(s);}
                }
            }

            Expr::While { cond, body } => { 
                self.collect_vars_expr(cond);
                for s in body {self.collect_var_stmt(s);}
            }
            _ => {}

        }
    }

    //Main entry : generating code for the whole program
    fn generate(&mut self , program :&Program) {
        //first pass , collect all varible names
        self.collect_vars(program);
        let n_vars = self.symbols.count(); //number of variables

        //emit prologue 
        self.buf.prologue(n_vars);
        
        //emit code for each statement

        for stmt in program { 
            self.gen_stmt(stmt);
        } 
        //emit epilogue
        self.buf.epilogue();
    }

    fn  gen_stmt(&mut self , stmt :&Stmt) {
        match stmt {
            Stmt::Expr(e) => {self.gen_expr(e);}
            Stmt::Return(e) => { 
                self.gen_expr(e);
                self.buf.epilogue();
            }

            Stmt::FnDef {..} => { 
                //for the jit part .. function definitions are
                //not supported
                //inteprter handles them : TO BE DONE LATER.
                eprintln!("Warning: fn definitions not yet supported in JIT path");
            }
        }
    }
    fn gen_stmts(&mut self , stmts : &[Stmt]) { 
        for stmt in stmts { 
            self.gen_stmt(stmt);
        }
    }
    //generate code for one expression 
    //convenrtion = results is always on the left (eax) 
    //after this call

    fn gen_expr(&mut self  ,expr :&Expr){
        match expr {
        
            //load immediate into eax
            Expr::Number(n) => { 
                self.buf.mov_eax_imm(*n as u32);
            }

            //load varible from stack into eax
            Expr::Var(name) => { 
                let offset = self.symbols.get(name);
                self.buf.mov_from_stack(offset);
            }

            //evaluate rhs and store to stack

            Expr::Assign { name, value } => { 
                self.gen_expr(value);
                let offset  = self.symbols.get(name);
                self.buf.mov_to_stack(offset);
            }

            //Unary 
            Expr::UnaryOp { op, expr } => { 
                self.gen_expr(expr);
                match op {
                    UnaryOpKind::Neg => self.buf.neg_eax(),
                    UnaryOpKind::Pos => {} //ignore + ,
                }
            }

            // ----BINARY OPERATIONS---
            // 1.   Evaluate left -> results in eax
            // 2.   Push eax into the stack(saving it).
            // 3.   Evaluate right -> results overwrite saved eax
            // 4.   Mov eax -> ebx (right operand).
            // 5.   Pop stack(get eax back) (left operand)
            // 6.   Apply opration left(eax) OP right(ebx)

            Expr::BinOp { op, left, right } => { 
                self.gen_expr(left);
                self.buf.push_eax();

                self.gen_expr(right);
                self.buf.mov_ebx_eax(); 
                self.buf.pop_eax();


                match op {
                    BinOpKind::Add =>  self.buf.add_eax_ebx(),
                    BinOpKind::Sub =>  self.buf.sub_eax_ebx(),
                    BinOpKind::Mul =>  self.buf.imul_eax_ebx(),
                    BinOpKind::Div => {
                        self.buf.cdq();
                        self.buf.idiv_ebx();
                    }
                    BinOpKind::Mod => { 
                        self.buf.cdq();
                        self.buf.idiv_ebx();
                        self.buf.mov_eax_ebx(); // get remainder
                    }

                    BinOpKind::EqEq => { 
                        self.buf.cmp_eax_ebx();
                        self.buf.sete_al();
                        self.buf.movzx_eax_al();
                    }

                    BinOpKind::NotEq=> { 
                        self.buf.cmp_eax_ebx();
                        self.buf.setne_al();
                        self.buf.movzx_eax_al();
                    }

                    BinOpKind::Lt=> { 
                        self.buf.cmp_eax_ebx();
                        self.buf.setl_al();
                        self.buf.movzx_eax_al();
                    }
                    BinOpKind::Gt=> { 
                        self.buf.cmp_eax_ebx();
                        self.buf.setg_al();
                        self.buf.movzx_eax_al();
                    }
                    BinOpKind::LtEq=> { 
                        self.buf.cmp_eax_ebx();
                        self.buf.setle_al();
                        self.buf.movzx_eax_al();
                    }
                    BinOpKind::GtEq=> { 
                        self.buf.cmp_eax_ebx();
                        self.buf.setge_al();
                        self.buf.movzx_eax_al();
                    }

                }
            }
            Expr::If { cond, then_block, else_block } => { 

                self.gen_expr(cond); // eval condition

                self.buf.test_eax_eax(); // test eax ZF is eax is 0 ( False)

                let je_patch = self.buf.emit_je_rel32();
                self.gen_stmts(then_block);

                let jmp_patch = self.buf.emit_jmp_rel32();
                let else_start = self.buf.current_pos();

                self.buf.patch_u32(je_patch,(else_start as i32 -(je_patch as i32 + 4)) as u32);

                if let Some(else_stmts) = else_block { 
                    self.gen_stmts(else_stmts);
                }

                let end = self.buf.current_pos();

                self.buf.patch_u32(jmp_patch,(end as i32 -(jmp_patch as i32 + 4)) as u32);
            }
            Expr::While { cond, body } => {
                // record where the loop starts — we jump back here each iteration
                let loop_start = self.buf.current_pos();
                
                // evaluate condition → eax
                self.gen_expr(cond);
                self.buf.test_eax_eax();

                // je  end  (exit loop if condition is false)
                let je_patch = self.buf.emit_je_rel32();

                // emit loop body
                self.gen_stmts(body);

                // jmp  loop_start  (go back — offset will be negative)
                let jmp_patch = self.buf.emit_jmp_rel32();
                let back = loop_start as i32 - (jmp_patch as i32 + 4);
                self.buf.patch_u32(jmp_patch, back as u32);

                // patch je  here (after the jmp, loop is done)
                let end = self.buf.current_pos();
                self.buf.patch_u32(je_patch, (end as i32 - (je_patch as i32 + 4)) as u32);
            }

            Expr::FnCall { .. } => { 
                                eprintln!("Warning: function calls not yet in JIT path");
                self.buf.mov_eax_imm(0);
            }
        }
    }
}

//public convinient function 

pub fn compile(source : &str) -> CodeBuffer {

    let program = crate::parser::parse(source);
    let mut cg = CodeGen::new();
    cg.generate(&program);
    cg.buf
}




