{
module Parser where
import Lexer	
}

%name parseProof Expr
%name parseExpr 

%tokentype { Token }
%error { parseError }

%token
    "->"    { TArrow }
    '!'     { TNot   }
    '&'     { TAnd   }
    '|'     { TOr    }
    var     { TVar $$}
    '('     { TOpBr  }
    ')'     { TClBr  }
    "|-"    { TTurn  }
    ','     { TCommo }

%%

Expr:
    Disj "->" Expr      { $1 :->: $3 }
    | Disj              { $1         }

Disj:
    Disj '|' Conj       { $1 :|: $3  }
    | Conj              { $1         }

Conj: 
    Conj '&' Unary      { $1 :&: $3  }
    | Unary             { $1         }

Unary:
    '!' Unary           { Neg $2     }
    | var               { Var $1     }
    | '(' Expr ')'      { $2   }

{
parseError :: [Token] -> a
parseError _  = error "Parse error"

data Expr = Expr :&: Expr | Expr :|: Expr | Expr :->: Expr | Neg Expr | Var String | Bottom deriving (Ord, Eq)
}

