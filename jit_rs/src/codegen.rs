use std::{slice, thread::sleep_ms};

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
         self.emit(0x28);
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

    // TO BE CONTINUED.......
    //

}







