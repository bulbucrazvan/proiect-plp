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
Scheme Equality for Declaration.
Notation "'int'' X" := (declIntEmpty X)(at level 81).
Notation "'int''' X '='' A" := (declInt X A)(at level 82).
Notation "'bool'' X" := (declBoolEmpty X)(at level 81).
Notation "'bool''' X '='' A" := (declBool X A)(at level 82).
Notation "A ','' B" := (declSequence A B)(at level 83).

Inductive ExpSequence :=
  | expEmpty : ExpSequence
  | expAExp : AExp -> ExpSequence
  | expBExp : BExp -> ExpSequence
  | expSeq : ExpSequence -> ExpSequence -> ExpSequence.
Scheme Equality for ExpSequence.
Coercion expAExp : AExp >-> ExpSequence.
Coercion expBExp : BExp >-> ExpSequence.
Notation "A ',,'' B" := (expSeq A B)(at level 83).

Inductive Stmt := 
  | stSkip : Stmt
  | stVarDecl : Declaration -> Stmt
  | stFuncDecl : string -> Declaration -> Stmt -> Stmt
  | stFuncExec : string -> ExpSequence -> Stmt  
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

Inductive EnvList :=
  | envNil : EnvList
  | envCons : string -> nat -> EnvList -> EnvList.

Definition EnvAdd (str : string) (currentList : EnvList) :=
  match currentList with
    | envNil => (envCons str 0 envNil)
    | (envCons str' addr l1) => (envCons str (addr + 1) (envCons str' addr l1))
  end.

Fixpoint EnvContains (str : string) (currentList : EnvList) : bool :=
  match currentList with
    | envNil => false
    | envCons str' addr l1 => if (string_dec str str') then true
                              else (EnvContains str l1)
  end. 

Fixpoint EnvGetAddress (str : string) (currentList : EnvList) : nat :=
  match currentList with 
    | envNil => 0
    | envCons str' addr l1 => if (string_dec str str') then addr
                              else (EnvGetAddress str l1)
  end. 

Inductive ValueType :=
  | valFunction : Declaration -> Stmt -> ValueType
  | valNat : nat -> ValueType
  | valBool : bool -> ValueType.

Inductive MemList :=
  | memNil : MemList
  | memCons : nat -> ValueType -> MemList -> MemList.

Fixpoint MemAppend (l1 l2 : MemList) : MemList :=
  match l1 with
    | memNil => l2
    | memCons addr val l => memCons addr val (MemAppend l l2)
  end.

Fixpoint MemGetValue (addr : nat) (currentList : MemList) : ValueType :=
  match currentList with
    | memNil => (valNat 0)
    | memCons addr' val l => if (Nat.eqb addr addr') then val
                             else (MemGetValue addr l)
  end.
Definition test := (valFunction (declEmpty) (stSkip)).

Inductive StackList :=
  | stackNil : StackList
  | stackCons : string -> ValueType -> StackList -> StackList.

Fixpoint StackContains (str' : string) (stack : StackList) : bool :=
  match stack with
    | stackNil => false
    | stackCons str val next => if (string_dec str str') then true else (StackContains str' next)
  end.

Fixpoint StackGetValue (name : string) (stack : StackList) : ValueType :=
  match stack with
    | stackNil => (valNat 0)
    | stackCons name' value next => if (string_dec name name') then value else (StackGetValue name next)
  end.

Inductive ExpType : Type := Nat | Bool | Multiple | Empty | Function.
Definition test2 := (expAExp 5).
Definition GetExpType (exp : ExpSequence) : ExpType := 
  match exp with
    | expAExp a => Nat
    | expBExp b => Bool
    | expSeq c d => Multiple
    | expEmpty => Empty
  end.
Definition GetValueType (value : ValueType) : ExpType :=
  match value with
    | valNat n => Nat
    | valBool b => Bool
    | valFunction decl st => Function
  end.
Scheme Equality for ExpType.

Fixpoint DeclarationCorresponds (decl : Declaration) (args : ExpSequence) : bool :=
  match decl with
    | declEmpty => if (ExpType_beq (GetExpType args) Empty) then true
                                                            else false
    | declInt name val =>  if (ExpType_beq (GetExpType args) Nat) then true
                                                                  else false
    | declBool name val => if (ExpType_beq (GetExpType args) Bool) then true
                                                                   else false
    | declIntEmpty name => if (ExpType_beq (GetExpType args) Nat) then true
                                                                  else false
    | declBoolEmpty name => if (ExpType_beq (GetExpType args) Bool) then true
                                                                    else false
    | declSequence decl1 decl2 => match args with
                                    | expAExp a => false
                                    | expBExp a => false
                                    | expEmpty => false
                                    | expSeq a b => andb (DeclarationCorresponds decl1 a)
                                                         (DeclarationCorresponds decl2 b)
                                  end
  end.

Compute DeclarationCorresponds (declSequence (declIntEmpty "x") (declSequence (declBoolEmpty "y") (declIntEmpty "z"))) (expSeq (expAExp 5) (expSeq (expBExp bTrue) (expAExp 6))).

Reserved Notation "A =[ E , M , S ]=> N" (at level 60).
Inductive aeval : AExp -> EnvList -> MemList -> StackList -> nat -> Prop :=
  | a_const : forall n env mem stack, aCons n =[ env , mem, stack ]=> n
  | a_varStack : forall v x y env mem stack, 
      (StackContains v stack) = true -> 
      x = (StackGetValue v stack) ->
      (ExpType_beq (GetValueType x) Nat) = true ->
      (valNat y) = x ->     
      aVar v =[ env , mem , stack ]=> y
  | a_varEnv : forall v x y env mem stack,
      (StackContains v stack) = false ->
      (EnvContains v env) = true ->
      x = (MemGetValue (EnvGetAddress v env) mem) ->
      (ExpType_beq (GetValueType x) Nat) = true ->
      (valNat y) = x ->
      aVar v =[ env , mem , stack ]=> y
  | a_add : forall a1 a2 i1 i2 n env mem stack,
      a1 =[ env , mem , stack ]=> i1 ->
      a2 =[ env , mem , stack ]=> i2 ->
      n = i1 + i2 ->
      a1 +' a2 =[ env , mem , stack ]=> n
  | a_times : forall a1 a2 i1 i2 n env mem stack,
      a1 =[ env , mem , stack ]=> i1 ->
      a2 =[ env , mem , stack ]=> i2 ->
      n = i1 * i2 ->
      a1 *' a2 =[ env , mem , stack ]=> n
  | a_minus : forall a1 a2 i1 i2 n env mem stack,
      a1 =[ env , mem , stack ]=> i1 ->
      a2 =[ env , mem , stack ]=> i2 ->
      Nat.leb i2 i1 = true ->
      n = i1 - i2 ->
      a1 -' a2 =[ env , mem, stack ]=> n
  | a_div : forall a1 a2 i1 i2 n env mem stack,
      a1 =[ env , mem , stack ]=> i1 ->
      a2 =[ env , mem , stack ]=> i2 ->
      Nat.ltb 0 i2 = true ->
      n = Nat.div i1 i2 ->
      a1 /' a2 =[ env , mem , stack ]=> n
  | a_mod : forall a1 a2 i1 i2 n env mem stack,
      a1 =[ env , mem , stack ]=> i1 ->
      a2 =[ env , mem , stack ]=> i2 ->
      Nat.ltb 0 i2 = true ->
      n = Nat.modulo i1 i2 ->
      a1 %' a2 =[ env , mem , stack ]=> n
  where "a =[ env , mem , stack ]=> n " := (aeval a env mem stack n).

Example e1: 5 +' "x" =[ envNil , memNil , (stackCons "x" (valNat 5) stackNil) ]=> 10.
Proof.
  eapply a_add.
  - apply a_const.
  - eapply a_varStack.
    + reflexivity.
    + reflexivity.  
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Reserved Notation "B ={ E , M , S }=> B'" (at level 70).
Inductive beval : BExp -> EnvList -> MemList -> StackList -> bool -> Prop :=
  | b_true : forall env mem stack, bTrue ={ env , mem , stack }=> true
  | b_false : forall env mem stack, bFalse ={ env , mem , stack }=> false
  | b_lessthan : forall a1 a2 i1 i2 b env mem stack, 
      a1 =[ env , mem , stack ]=> i1 ->
      a2 =[ env , mem , stack ]=> i2 ->      
      b = Nat.ltb i1 i2 ->
      a1 <' a2 ={ env , mem , stack }=> b
  | b_greaterthan : forall a1 a2 i1 i2 b env mem stack, 
      a1 =[ env , mem , stack ]=> i1 ->
      a2 =[ env , mem , stack ]=> i2 ->      
      b = Nat.ltb i2 i1 ->
      a1 >' a2 ={ env , mem , stack }=> b
  | b_greaterequalthan : forall a1 a2 i1 i2 b env mem stack, 
      a1 =[ env , mem , stack ]=> i1 ->
      a2 =[ env , mem , stack ]=> i2 ->      
      b = Nat.leb i2 i1 ->
      a1 >=' a2 ={ env , mem , stack }=> b
  | b_lessequalthan : forall a1 a2 i1 i2 b env mem stack, 
      a1 =[ env , mem , stack ]=> i1 ->
      a2 =[ env , mem , stack ]=> i2 ->      
      b = Nat.leb i1 i2 ->
      a1 <=' a2 ={ env , mem , stack }=> b
  | b_equal : forall a1 a2 i1 i2 b env mem stack, 
      a1 =[ env , mem , stack ]=> i1 ->
      a2 =[ env , mem , stack ]=> i2 ->      
      b = Nat.eqb i1 i2 ->
      a1 ==' a2 ={ env , mem , stack }=> b
  | b_nottrue : forall b env mem stack,
      b ={ env , mem , stack }=> true ->
      (bNot b) ={ env , mem , stack }=> false
  | b_notfalse : forall b env mem stack,
      b ={ env , mem , stack }=> false ->
      (bNot b) ={ env , mem , stack }=> true
  | b_andtrue : forall b1 b2 t env mem stack,
      b1 ={ env , mem , stack }=> true ->
      b2 ={ env , mem , stack }=> t ->
      bAnd b1 b2 ={ env , mem , stack }=> t
  | b_andfalse : forall b1 b2 env mem stack,
      b1 ={ env , mem , stack }=> false ->
      bAnd b1 b2 ={ env , mem , stack }=> false
  | b_ortrue : forall b1 b2 env mem stack,
      b1 ={ env , mem , stack }=> true ->
      bOr b1 b2 ={ env , mem , stack }=> true
  | b_orfalse : forall b1 b2 t env mem stack,
      b1 ={ env , mem , stack }=> false ->
      b2 ={ env , mem , stack }=> t ->
      bOr b1 b2 ={ env , mem , stack }=> t
  where "B ={ E , M , S }=> B'" := (beval B E M S B').

Example e2: "x" <=' 10 ={ (envCons "x" 0 envNil) , (memCons 0 (valNat 8) memNil) , stackNil }=> true.
Proof.
  eapply b_lessequalthan.
  - eapply a_varEnv.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - apply a_const.
  - reflexivity.
Qed.

Reserved Notation "S -{ sigma , list }->[ sigma' , list' ]" (at level 60).
Inductive eval : Stmt -> Env -> Env -> List -> List -> Prop :=
  | e_decl: forall x i i' sigma sigma' list list',
      (partof x list) = false -> (* daca variabila deja e in environment, nu returnam; altfel returnam env si lista in care avem variabila noua*)
      list' = (append list (cons x nil)) ->
      i =[ sigma , list' ]=> i' ->
      sigma' = (update sigma x i') ->
      (decl x i) -{ sigma , list }->[ sigma' , list' ]
  | e_assignment: forall a i x sigma sigma' list,
      a =[ sigma , list ]=> i ->
      sigma' = (update sigma x i) ->
      (x ::= a) -{ sigma , list }->[ sigma' , list ]
  | e_seq : forall s1 s2 sigma sigma1 sigma2 list list1 list2,
      s1 -{ sigma , list }->[ sigma1 , list1 ] ->
      s2 -{ sigma1 , list1 }->[ sigma2 , list2 ]->
      (s1 ;; s2) -{ sigma , list }->[ sigma2 , list2 ]
  | e_whilefalse : forall b s sigma list,
      b ={ sigma , list }=> false ->
      while b s -{ sigma , list }->[ sigma , list ]
  | e_whiletrue : forall b s sigma sigma' list,
      b ={ sigma , list }=> true ->
      (s ;; while b s) -{ sigma , list }->[ sigma' , list] ->
      while b s -{ sigma , list }->[ sigma' , list ]
  | e_ifTrue : forall b s sigma sigma' list,
      b ={ sigma , list }=> true ->
      s -{ sigma , list }->[ sigma' , list] -> 
      ifStmt b s -{ sigma , list }->[ sigma' , list ]
  | e_ifFalse : forall b s sigma list,
      b ={ sigma , list }=> false ->
      ifStmt b s -{ sigma , list }->[ sigma , list ]
  | e_ifElseFalse : forall b s s' sigma sigma' list,
      b ={ sigma , list }=> false ->
      s' -{ sigma , list }->[ sigma' , list] ->
      ifElseStmt b s s' -{ sigma , list }->[ sigma' , list ]
  | e_ifElseTrue : forall b s s' sigma sigma' list,
      b ={ sigma , list }=> true ->
      s -{ sigma , list }->[ sigma' , list ] ->
      ifElseStmt b s s' -{ sigma , list }->[ sigma' , list ]
where "s '-{' sigma , list }->[ sigma' , list' ]" := (eval s sigma sigma' list list').



