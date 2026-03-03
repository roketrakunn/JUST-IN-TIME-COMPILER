
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

use crate::parser::{Expr , BinOpKind , Stmt, UnaryOpKind , Program};

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

     //mov esp , ebp         [89 E5]
     fn mov_ebp_esp(&mut self) {
         self.emit(0x89);
         self.emit(0xE5);
     }

      //mov esp , ebp         [89 EC]
     fn mov_esp_ebp(&mut self) {
         self.emit(0x89);
         self.emit(0xEC);
     }
     // sub imm8 , %esp     [83 EC imm8]

     fn sub_esp_imm8(&mut self , n :u8) {
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
}

// ------------- SYMBOL TABLE-------------
// Uses varibles in stack offests 
// uses hashmap  to build the table and store variables as keys 
// offests as value.

use std::{collections::HashMap, thread::panicking};


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




