Require Import Strings.String.
Delimit Scope string_scope with string.
Local Open Scope string_scope.
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Scheme Equality for string.


Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive ErrorString :=
  | error_string : ErrorString
  | stringg : string -> ErrorString.
 

Coercion num : nat >-> ErrorNat.
Coercion boolean : bool >-> ErrorBool.
Coercion stringg : string >-> ErrorString.

Inductive ValueTypes :=
| default_nat : ValueTypes
| default_bool : ValueTypes
| default_string : ValueTypes
| err_undeclared : ValueTypes
| err_assignment : ValueTypes
| natural : ErrorNat -> ValueTypes
| res_boolean : ErrorBool -> ValueTypes
| res_stringg : ErrorString -> ValueTypes.


Check 7.
Check true.
Check "ana".

Scheme Equality for ValueTypes.

Definition Env := string -> ValueTypes.


Definition env : Env := fun x => err_undeclared.
Compute (env "x").

Definition check_eq_over_types (t1 : ValueTypes) (t2 : ValueTypes) : bool :=
  match t1 with
    | err_undeclared => match t2 with 
                     | err_undeclared => true
                     | _ => false
                     end
    | default_nat => match t2 with 
                  | default_nat => true
                  | _ => false
                  end
    | default_bool => match t2 with 
                  | default_bool => true
                  | _ => false
                  end
    | default_string => match t2 with 
                  | default_string => true
                  | _ => false
                  end
    | err_assignment => match t2 with 
                  | err_assignment => true
                  | _ => false
                  end
    | natural x => match t2 with
                  | natural x => true
                  | _ => false
                  end
    | res_boolean x => match t2 with 
                  | res_boolean x => true
                  | _ => false
                  end
    | res_stringg x => match t2 with
                  | res_stringg x => true
                  | _ => false
                  end
  end.

Compute (check_eq_over_types (err_undeclared) (natural 10)).
Compute (check_eq_over_types (natural 1) (natural 2)).
Compute (check_eq_over_types (res_stringg "a") (res_boolean true)).

Definition update (env : Env) (x : string) (v : ValueTypes) : Env :=
 fun y =>
  if (string_beq y x) 
   then
     if(andb (check_eq_over_types err_undeclared (env y)) (negb (check_eq_over_types default_nat v)))
       then err_undeclared
       else 
           if (andb (check_eq_over_types err_undeclared (env y)) (negb (check_eq_over_types default_bool v)))
           then err_undeclared
           else 
              if(andb (check_eq_over_types err_undeclared (env y)) (negb (check_eq_over_types default_string v)))
              then err_undeclared
       else 
           if (andb (check_eq_over_types err_undeclared (env y)) ((check_eq_over_types default_nat v)))
           then default_nat
           else 
             if (andb (check_eq_over_types err_undeclared (env y)) ((check_eq_over_types default_bool v))) 
             then default_bool
             else
                if (andb (check_eq_over_types err_undeclared (env y)) ((check_eq_over_types default_string v)))
                then default_string
        else 
           if(orb (check_eq_over_types default_nat (env y)) (check_eq_over_types v (env y)))
           then v
           else 
              if(orb (check_eq_over_types default_bool (env y)) (check_eq_over_types v (env y)))
              then v
              else
                 if(orb (check_eq_over_types default_string (env y)) (check_eq_over_types v (env y)))
                 then v
                 else err_assignment

  else (env y).

Compute (env "y").
Compute (update (update env "y" (default_bool)) "y" (res_boolean true) "y").
Compute ((update (update (update env "y" default_string) "y" (natural 10)) "y" (res_boolean true)) "y").

Notation "S [ V // X ]" := (update S X V) (at level 0).


Inductive AExp :=
| avar : string -> AExp
| anum : ErrorNat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amodulo : AExp -> AExp -> AExp.


Coercion anum : ErrorNat >-> AExp.
Coercion avar : string >-> AExp.

Notation "A +' B" := (aplus A B) (at level 60, right associativity).
Notation "A *' B" := (amul A B) (at level 58, left associativity).
Notation "A -' B" := (aminus A B) (at level 50, left associativity).
Notation "A /' B" := (adiv A B) (at level 40, left associativity).
Notation "A %' B" := (amodulo A B) (at level 50, left associativity).

Compute 1 +' 2.
Compute "x" -' 6.
Compute 5 *' "x" /' 8.
Compute 35 %' "i".


Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.

Definition minus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else num (n1 - n2)
    end.

Definition mul_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition modulo_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (Nat.modulo v1 v2)
    end.


Inductive BExp :=
| berror : BExp
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp
| bvar: string -> BExp.

Coercion bvar : string >-> BExp.

Notation "! A" := (bnot A) (at level 70).
Notation "A 'and'' B" := (band A B) (at level 80).
Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A >' B" := (bgreaterthan A B) (at level 70).
Notation "A 'or'' B" := (bor A B) (at level 85, right associativity).

Check btrue or' ! bfalse.
Check ! ("x" <' 10). 
Check btrue and' ("n" >' 0).
Check "x" >' 10 and' (15 <' "m" -' 2).



Definition blessthan_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
    end.

Definition greaterthan_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (negb (Nat.ltb v1 v2))
    end.

Definition bnot_ErrorBool (n :ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Definition band_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition bor_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.



(*OPERATII PE STRING-URI*)

Inductive Strings :=
| string_var : string -> Strings
| string_string : ErrorString -> Strings
| strlen : ErrorString -> Strings
| strcat : ErrorString -> ErrorString -> Strings
| strcmp : ErrorString -> ErrorString -> Strings.


Coercion string_var: string >->Strings.

Notation " ~ A ~ ":=(strlen A) (at level 60).
Notation " A +/ B " :=(strcat A B) (at level 60).
Notation " A ? B ":=(strcmp A B) (at level 60).


Check " ~ tema ~ ".
Check "proiect" +/ "plp".
Check "a" ? "b".

Definition string_length (s : ErrorString) : ErrorNat :=
  match s with 
    | error_string => error_nat
    | stringg v1 => length v1
end.

Compute string_length "mama".



Definition concat_string (s1 : ErrorString) (s2 : ErrorString) : ErrorString :=
    match s1,s2 with 
    | error_string, _ => error_string
    | _, error_string => error_string
    | stringg v1, stringg v2 => v1 ++ v2
end.

Compute concat_string "a" "b".


Definition strcmp_string (s1 : ErrorString) (s2 : ErrorString) : ErrorString :=
    match s1,s2 with 
    | error_string, _ => error_string
    | _, error_string => error_string
    | stringg v1 , stringg v2 =>if (Nat.leb(length v1) (length v2))
                                then v2
                                else v1
end.
Compute strcmp_string "abcd" "abc".




(*VECTORI*)

Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.
Set Implicit Arguments.
Open Scope list_scope.

Inductive ErrorArray :=
| err_array : ErrorArray
| nat_array : string -> (list nat) -> ErrorArray
| bool_array : string -> (list bool) -> ErrorArray
| string_array : string -> (list string) -> ErrorArray.


Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope. 
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope. 
Section Lists. 
Check [ 1 , 2 , 3 , 4 ]. 
Check [ ]. 
Check [true , false]. 
Check ["a" , "b"]. 
Notation "A n:= S ":=(nat_array A S) (at level 20).
Notation "A b:= S ":=(bool_array A S) (at level 20).
Notation "A s:= S ":=(string_array A S) (at level 20).

Check ("v" n:= [ 1 , 2 , 3 ]).






(*POINTERI SI REFERINTE*)

Inductive Stmt :=
| nat_decl : string -> AExp -> Stmt
| bool_decl : string -> BExp -> Stmt
| string_decl : string -> string -> Stmt
| nat_assignment : string -> AExp -> Stmt
| bool_assignment : string -> BExp -> Stmt
| string_assignment : string -> string -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| FOR : Stmt -> BExp -> Stmt -> Stmt
| nat_array_decl : string -> (list nat) -> Stmt
| bool_array_decl : string -> (list bool) -> Stmt
| string_array_decl : string -> (list string) -> Stmt
| nat_array_assign : string -> (list nat) -> Stmt
| bool_array_assign : string -> (list bool) -> Stmt
| string_array_assign : string -> (list string) -> Stmt.


Notation "X :n= A" := (nat_assignment X A)(at level 90).
Check "x" :n= 5 +' 10.
Notation "X :b= A" := (bool_assignment X A)(at level 90).
Check "ok" :b= btrue.
Notation "X :s= A" := (string_assignment X A)(at level 90).
Check "m" :s= "mama".
Notation "'Nat' X ::= A" := (nat_decl X A)(at level 90).
Check Nat "i" ::= 10.
Notation "'Bool' X ::= A" := (bool_decl X A)(at level 90).
Check Bool "ok" ::= bfalse.
Notation "'String' X ::= A" := (string_decl X A)(at level 90).
Check String "ab" ::= "ba".
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Check ( Nat "n" ::= 10 ;; String "y" ::= "ab" ).
Notation "'If' B 'Then' S1 'Else' S2 'End'" := (ifthenelse B S1 S2) (at level 97).
Notation "while '(' A ')' '(' B ')' " := (while A B) (at level 50).
Notation "'If' B 'Then' S  'End'" := (ifthen B S) (at level 97).
Notation "'For' ( A ; B ; C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).
Notation "X n:== A ":=(nat_array_decl X A)(at level 90).
Check "v" n:== [ 1 , 2 ].
Notation "X b:== A ":=(bool_array_decl X A)(at level 90).
Check "b" b:== [ true , false ].
Notation "X s:== A ":=(string_array_decl X A)(at level 90).
Check "s" s:== [ "a" , "b" ].
Notation "X n:-> A ":=(nat_array_assign X A)(at level 90).
Check "v" n:-> [ 1 , 2 ].
Notation "X b:-> A ":=(bool_array_assign X A)(at level 90).
Check "b" b:-> [ true , false ].
Notation "X s:-> A ":=(string_array_assign X A)(at level 90).
Check "s" s:-> [ "a" , "b" ].









