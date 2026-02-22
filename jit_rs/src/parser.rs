/**
 * This is the parser
 * Just liek the name says , "parser" it passes from a list of tokens tokens to an AST
 * This tree matters alot because of things like precedence(i hope i got that right) 
 * for example 2 + 3 * 4 is not the same as (2+3) * 4
 * 2 + 3 * 4          (2 + 3) * 4

    ADD                  MUL
   /   \                /   \
  2    MUL            ADD    4
      /   \          /   \
     3     4        2     3


 * "x = 5 + 3 * 2" becomes:

        ASSIGN(x)
            |
           ADD
          /   \
         5    MUL
             /   \
            3     2
 * Notice: multiplication is DEEPER in the tree = higher precedence. 

 * The tree is from down to top as I hope you can see.
 * Below it my spaggethi code ( god is that spageti is spelt?)*/






