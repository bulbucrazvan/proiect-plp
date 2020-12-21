Require Import String.
Open Scope string_scope.

Inductive AExp :=
  | aVar : string -> AExp
  | aCons : nat -> AExp
  | aPlus : AExp -> AExp -> AExp
  | aMinus : AExp -> AExp -> AExp
  | aDiv : AExp -> AExp -> AExp
  | aMod : AExp -> AExp -> AExp
  | aMul : AExp -> AExp -> AExp.

Coercion aVar : string >-> AExp.
Coercion aCons : nat >-> AExp.
Notation "A +' B" := (aPlus A B) (at level 60).
Notation "A *' B" := (aMul A B) ( at level 58, left associativity).
Notation "A -' B" := (aMinus A B) ( at level 60).
Notation "A /' B" := (aDiv A B) (at level 58, left associativity).
Notation "A %' B" := (aMod A B) (at level 58, left associativity).
Check ("x" +' 5 /' (25 -' "y")).

Inductive BExp :=
  | bTrue : BExp
  | bFalse : BExp
  | bLess : AExp -> AExp -> BExp
  | bGreater : AExp -> AExp -> BExp
  | bEqual : AExp -> AExp -> BExp
  | bLessEqual : AExp -> AExp -> BExp
  | bGreaterEqual : AExp -> AExp -> BExp
  | bOr : BExp -> BExp -> BExp
  | bAnd : BExp -> BExp -> BExp
  | bNot : BExp -> BExp.

Notation "A <' B" := (bLess A B)(at level 62).
Notation "A >' B" := (bGreater A B)(at level 62).
Notation "A ==' B" := (bEqual A B)(at level 62).
Notation "A <=' B" := (bLessEqual A B) (at level 62).
Notation "A >=' B" := (bGreaterEqual A B) (at level 62).
Infix "&&'" := bAnd (at level 65, left associativity).
Infix "||'" := bOr (at level 65, left associativity).
Notation " '!' A" := (bNot A) (at level 63).
Check (bTrue &&' bFalse).
Check ("x" >=' 5 ||' ! "y" <=' 25).
Check ("x" >' 5 &&' "y" ==' 25).

Inductive Declaration :=
  | declEmpty : Declaration
  | declInt : string -> AExp -> Declaration
  | declBool : string -> BExp -> Declaration
  | declIntEmpty : string -> Declaration
  | declBoolEmpty : string -> Declaration
  | declSequence : Declaration -> Declaration -> Declaration.
Notation "'int'' X" := (declIntEmpty X)(at level 81).
Notation "'int''' X '='' A" := (declInt X A)(at level 82).
Notation "'bool'' X" := (declBoolEmpty X)(at level 81).
Notation "'bool''' X '='' A" := (declBool X A)(at level 82).
Notation "A ','' B" := (declSequence A B)(at level 83).

Inductive Stmt := 
  | stSkip : Stmt
  | stVarDecl : Declaration -> Stmt
  | stFuncDecl : string -> Declaration -> Stmt -> Stmt
  | stFuncExec : string -> AExp -> Stmt  
  | stAssignment : string -> AExp -> Stmt
  | stSequence : Stmt -> Stmt -> Stmt
  | stWhile : BExp -> Stmt -> Stmt
  | stIfStmt : BExp -> Stmt -> Stmt
  | stIfElseStmt : BExp -> Stmt -> Stmt -> Stmt
  | stForLoop : Declaration -> BExp -> Stmt -> Stmt -> Stmt.
Coercion stVarDecl : Declaration >-> Stmt.

Notation "X ':='' A" := (stAssignment X A)(at level 83).
Notation "S1 ;' S2" := (stSequence S1 S2)(at level 90).
Notation "'if'' '(' A ')' '{'' B ''}'" := (stIfStmt A B) (at level 82).
Notation "'if'' '(' A ')' '{'' B ''}' 'else'' '{'' C ''}'" := (stIfElseStmt A B C) (at level 82).
Notation "X '('' A '')' '{'' S ''}'" := (stFuncDecl X A S)(at level 82).
Notation "X '('' A '')'" := (stFuncExec X A)(at level 82).
Notation "'while'' '('' A '')' '{'' S ''}'" := (stWhile A S)(at level 82).
Notation "'for'' '('' A ';;'' B ';;'' C '')' '{'' S ''}'" := (stForLoop A B C S)(at level 82).


Check bool'' "x" =' bTrue.
Check int'' "x" =' 5,' bool' "y";' "x" :=' 5.
Check if' (5 ==' 2) {' "x" :=' 5;' "y" :=' 3 '} else'{' "x" :=' 6 '}.
Check "x"(' int' "a",' bool' "b" '){'
          "a" :=' 5 
      '};'
      "f"(' int' "c",' int' "d" '){' 
          "c" :=' "d" *' 25 
      '};'
      "main"(' declEmpty '){'
          if' (5 ==' 2) {' "x" :=' 5;' "y" :=' 3 '} else' {' "x" :=' 6 '};'
          "f"('"x"');'
          "x"(' 5 +' 2 ');'
          while' (' 5 >=' 2 ') {' "x" :=' 5 '};'
          for' (' (int'' "x" =' 1) ;;' ("x" <=' 2) ;;' ("x" :=' 1) ') {' "x" :=' 5 '}
     '}.






