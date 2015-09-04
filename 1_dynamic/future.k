require "kool-typed-dynamic.k"

module FUTURE-SYNTAX
  imports KOOL-TYPED-DYNAMIC-SYNTAX
  
  syntax Exp ::= // ... | 
                 Exp "!" Id "(" Exps ")" [avoid]
               | Guard
  syntax Guard ::= "wait" | Id "?"
  syntax Type ::= "!" Type
  syntax Stmt ::= "await" Exp ";"
                | Block "[]" Block [right]
                | Block "||" Block [right]                
endmodule

module FUTURE
  imports FUTURE-SYNTAX
  imports KOOL-TYPED-DYNAMIC
endmodule
