{
  open Parser
  open Lexing 

(* next_line copied from  Ch. 16 of "Real World Ocaml" *) 
let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }

}

let newline = ('\010' | "\013\010" )
let ident_reg_exp = ['A'-'Z' 'a'-'z']+ ['0'-'9' 'A'-'Z' 'a'-'z' '_' '\'']* 
let int_reg_exp = ['0'-'9']+

rule token = parse
  | [' ' '\t']    { token lexbuf }
  | '('           { LPAREN    }
  | ')'           { RPAREN    }
  | ","           { COMMA     }
  | ":"           { COLON     }
  | ";"           { SEMICOLON }
  | "+"           { ADD       }
  | "-"           { SUB       }
  | "*"           { MUL       }
  | "/"           { DIV       }
  | "%"           { MOD       }
  | "~"           { NOT       }
  | "="           { EQUAL     }
  | "=i"          { INT_EQ    }
  | "=b"          { BOOL_EQ   }
  | ":="          { ASSIGN    }
  | "<"           { LT        }
  | "&&"          { ANDOP     }
  | "||"          { OROP      }
  | "|"           { BAR       }
  | "->"          { ARROW     }
  | "?"           { WHAT      }
  | "!"           { BANG      }
  | "()"          { UNIT      }
  | "rec"         { REC       }
  | "and"         { AND       }
  | "true"        { TRUE      }
  | "false"       { FALSE     }
  | "ref"         { REF       }
  | "inl"         { INL       }
  | "inr"         { INR       }
  | "fst"         { FST       }
  | "snd"         { SND       }
  | "case"        { CASE      }
  | "of"          { OF        }
  | "if"          { IF        }
  | "then"        { THEN      }
  | "else"        { ELSE      }
  | "let"         { LET       }
  | "fun"         { FUN       }
  | "and"         { AND       }
  | "in"          { IN        }
  | "begin"       { BEGIN     }
  | "end"         { END       }
  | "while"       { WHILE     }
  | "do"          { DO        }
  | "bool"        { BOOL      }
  | "int"         { INTTYPE   }
  | "unit"        { UNITTYPE  }
  | int_reg_exp   { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | ident_reg_exp { IDENT (Lexing.lexeme lexbuf)               }
  | "(*"          { comment 1 lexbuf                           }
  | "//"          { linecomment lexbuf                         }
  | newline       { next_line lexbuf; token lexbuf             }
  | eof           { EOF                                        }
  | _             { Errors.complain ("Lexer : Illegal character " ^ (Char.escaped(Lexing.lexeme_char lexbuf 0)))
}

(* note : now handling nested comments *) 
and comment n = parse
  | "(*" { comment (n+1) lexbuf}
  | "*)" { if n=1 then token lexbuf else comment (n-1) lexbuf } 
  | newline { next_line lexbuf; comment n lexbuf } 
  | _ { comment n lexbuf }

and linecomment = parse
  | newline { next_line lexbuf; token lexbuf } 
  | _  { linecomment lexbuf }
