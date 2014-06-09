
(* based on http://siek.blogspot.ch/2013/05/type-safety-in-three-easy-lemmas.html
 and https://gist.github.com/dkrustev/5890291

*)

(* lib *********************)

Require Import Arith List Bool.

Inductive Id : Type :=  
   id : nat -> Id.

Theorem eq_id_dec : forall id1 id2 : Id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   (* Case n1 = n2 *)
     left. rewrite Heq. reflexivity.
   (* Case n1 <> n2 *)
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined. 


(* begin ********************)

Inductive Ty: Set := tyNat | tyBool | tyArrow (T1 T2: Ty).

Inductive Op := opPlus | opMinus | opEq.

Inductive Const := constNat (n: nat) | constBool (b: bool).

Inductive Exp := 
   expConst (c: Const) 
 | expOp (op: Op) (e1 e2: Exp)
 | expVar (x: Id)
 | expFun (f: Id) (x: Id) (T1: Ty) (T2: Ty) (body: Exp)
 | expApp (e1 e2: Exp)
 | expIf (cond etrue efalse: Exp). (* without this, we cannot express finite recursion *)

Inductive Val : Set := 
   valConst (c: Const) 
 | valClos (f: Id) (x: Id) (T1: Ty) (T2: Ty) (body: Exp) (env: list (Id * Val)).

Definition TEnv := list (Id * Ty).
Definition VEnv := list (Id * Val).

(* only the first matching id is considered (not the same as `In` from library) *)
Inductive Lookup{V: Set}: Id -> V -> list (Id * V) -> Prop :=
  | lookupFound: forall (x: Id) (v: V) (rest: list (Id * V)), Lookup x v ((x, v) :: rest)
  | lookupSkip: forall (x x': Id) (v v': V) (rest: list (Id * V)), 
                x <> x' -> Lookup x v rest -> Lookup x v ((x', v') :: rest).

Inductive TyOp : Op -> Ty -> Ty -> Ty -> Prop :=
  | tyopPlus:  TyOp opPlus  tyNat tyNat tyNat
  | tyopMinus: TyOp opMinus tyNat tyNat tyNat
  | tyopEq:    TyOp opEq    tyNat tyNat tyBool.

Inductive TyConst : Const -> Ty -> Prop :=
  | tyconstNat:  forall n, TyConst (constNat n)  tyNat
  | tyconstBool: forall b, TyConst (constBool b) tyBool.

Inductive Types : TEnv -> Exp -> Ty -> Prop :=
  | typesConst: forall G c T, TyConst c T -> Types G (expConst c) T
  | typesOp:    forall (G: TEnv) (o: Op) (e1 e2: Exp) (T1 T2 T: Ty),
                TyOp o T1 T2 T -> Types G e1 T1 -> Types G e2 T2
                -> Types G (expOp o e1 e2) T
  | typesVar:   forall (G: list (Id * Ty)) (x: Id) (T: Ty),
                Lookup x T G -> Types G (expVar x) T
  | typesFun:   forall (G: TEnv) (f x: Id) (T1 T2: Ty) (e: Exp),
                Types ((x, T1) :: (f, tyArrow T1 T2) :: G) e T2
                -> Types G (expFun f x T1 T2 e) (tyArrow T1 T2)
  | typesApp:   forall (G: TEnv) (e1 e2: Exp) (TA TR: Ty),
                Types G e1 (tyArrow TA TR) -> Types G e2 TA
                -> Types G (expApp e1 e2) TR
  | typesIf:    forall (G: TEnv) (cond e1 e2: Exp) (T: Ty),
                Types G cond tyBool -> Types G e1 T -> Types G e2 T 
                -> Types G (expIf cond e1 e2) T.


Definition ETypes (G: TEnv) (e: Exp): Prop :=
  exists T, Types G e T.


Definition  𝑓  := id 1.
Definition  𝑎 := id 2.
Definition  𝑏 := id 3.
Definition  𝑥 := id 4.
Definition  𝑦 := id 5.
Definition  𝑧 := id 6.

Definition e_plus_test: Exp := 
  (expOp opPlus (expConst (constNat 23)) (expConst (constNat 5))).

Fact e_plus_test_types: Types nil e_plus_test tyNat.
Proof.
  unfold e_plus_test.
  assert (Types nil (expConst (constNat 23)) tyNat).
  apply typesConst.
  apply tyconstNat.
  assert (Types nil (expConst (constNat 5)) tyNat).
  apply typesConst.
  apply tyconstNat.
  assert (TyOp opPlus tyNat tyNat tyNat).
  apply tyopPlus.
  apply typesOp with (T1 := tyNat) (T2 := tyNat); assumption.
Qed.

Definition e_minus_test: Exp := 
  (expOp opMinus (expConst (constNat 23)) (expConst (constNat 5))).

Definition e_dec_test: Exp := (expApp
  (expFun 𝑓  𝑥  tyNat tyNat (expOp opMinus (expVar 𝑥) (expConst (constNat 1))))
  (expConst (constNat 5))
).

(* calculates 1+2+...+x *)
Definition e_sum_test: Exp := (expApp
(expFun 𝑓  𝑥  tyNat tyNat (expIf 
   (expOp opEq (expVar 𝑥) (expConst (constNat 1)))
   (expConst (constNat 1))
   (expOp opPlus
      (expApp (expVar 𝑓) (expOp opMinus (expVar 𝑥) (expConst (constNat 1))))
      (expVar 𝑥))))
(expConst (constNat 7))
).

Ltac prove_lookup :=
  lazymatch goal with
  | [ |- Lookup ?x ?v ((?x, ?v) :: ?rest) ] => 
    apply (lookupFound x v rest)
  | [ |- Lookup ?x ?v nil ] => 
    fail "lookup did not find key" x
  | [ |- Lookup ?x ?v ((?x, ?v') :: ?rest) ] => 
    fail "lookup expected to find value" v "for key" x ", but found value" v'
  | [ |- Lookup ?x ?v ((?x', ?v') :: ?rest) ] => 
    apply (lookupSkip x x' v v' rest); 
      [ discriminate | prove_lookup ]
  end.

Fact prove_lookup_test_1:
  Lookup (id 4) 42 (((id 3), 33) :: ((id 4), 42) :: ((id 2), 22) :: nil).
Proof.
  prove_lookup.
Qed.

Ltac do_lookup x G :=
  lazymatch G with
  | (x, ?T) :: ?rest =>
      assert (Lookup x T G) by apply (lookupFound x T rest)
  | nil => 
    fail 100 "lookup did not find key" x
  | (?x', ?T') :: ?rest =>
     do_lookup x rest; 
     lazymatch goal with
     | [Hrest: Lookup x ?T rest |- _] => 
         assert (Lookup x T G) by 
           (apply (lookupSkip x x' T T' rest);
              [ discriminate | apply Hrest ])
     | _ => fail "expected hypothesis not found"
     end
  | _ => fail "no match for" G
  end.

Fact do_lookup_test_1:
  Lookup (id 4) 42 (((id 3), 33) :: ((id 4), 42) :: ((id 2), 22) :: nil).
Proof.
  do_lookup (id 4) (((id 3), 33) :: ((id 4), 42) :: ((id 2), 22) :: nil).
  assumption.
Qed.


Fact do_lookup_test_2:
  Lookup 𝑥   42 ((𝑎, 33) :: (𝑥, 42) :: (𝑏, 22) :: nil).
Proof.
  do_lookup 𝑥   ((𝑎, 33) :: (𝑥, 42) :: (𝑏, 22) :: nil).
  assumption.
Qed.


Fact test1: ETypes nil (expConst (constNat 23)).
Proof.
  unfold ETypes.
  exists tyNat.
  apply (typesConst nil (constNat 23) tyNat (tyconstNat 23)).
Qed.

Ltac tc :=
  lazymatch goal with
  | [ |- Types ?G ?e ?T ] => ta G e; tc_finish
  | [ |- ?H ] => idtac "tc cannot prove" H
  end
with tc_finish := 
  lazymatch goal with
  | [ _ : Types ?G ?e ?T |- Types ?G ?e ?T ] =>
      assumption
  | [ _ : Types ?G ?e ?T1 |- Types ?G ?e ?T2 ] =>
      fail "type mismatch:" e "has type" T1 "while it is expected to have type" T2
  | [ |- ?H ] => idtac "tc_finish cannot prove" H
  end
(* type assignment, takes "goal" as arg, returns result as hypothesis *)
with ta G e := 
  lazymatch e with    
  | expConst (constNat ?n) =>
      assert (Types G e tyNat) by apply (typesConst G (constNat n) tyNat (tyconstNat n))
  | expConst (constBool ?b) => 
      assert (Types G e tyBool) by apply (typesConst G (constBool b) tyBool (tyconstBool b))
  | expOp opPlus ?e1 ?e2 =>
      assert (Types G e tyNat);
      [ (apply (typesOp G opPlus e1 e2 tyNat tyNat tyNat tyopPlus); tc) | ]
  | expOp opMinus ?e1 ?e2 =>
      assert (Types G e tyNat);
      [ (apply (typesOp G opMinus e1 e2 tyNat tyNat tyNat tyopMinus); tc) | ]
  | expOp opEq ?e1 ?e2 =>
      assert (Types G e tyBool);
      [ (apply (typesOp G opEq e1 e2 tyNat tyNat tyBool tyopEq); tc) | ]
  | expVar ?x =>
      do_lookup x G; 
      lazymatch goal with
      | [Hfound: Lookup x ?T G |- _] =>
           assert (Types G e T) by apply (typesVar G x T Hfound)
      | _ => idtac "expVar is stuck"
      end
  | expFun ?f ?x ?T1 ?T2 ?body =>
      assert (Types G e (tyArrow T1 T2)); 
      [ (apply (typesFun G f x T1 T2 body); tc) | ]
  | expApp ?e1 ?e2 => 
      ta G e1;
      ta G e2;
      lazymatch goal with 
      | [ H1: Types G e1 (tyArrow ?TA ?TR), H2: Types G e2 ?TA |- _ ] => 
          assert (Types G e TR) by apply (typesApp G e1 e2 TA TR H1 H2)
      | [ H1: Types G e1 ?T1, H2: Types G e2 ?T2 |- _ ] =>
          fail "cannot apply" e1 "of type" T1
                "to argument" e2 "of type" T2
      | _ => idtac "unexpected match error in expApp"
      end
  | expIf ?cond ?e1 ?e2 =>
      assert (Types G cond tyBool); [ tc | (
        ta G e1;
        ta G e2;
        lazymatch goal with
        | [ Hc: Types G cond tyBool, H1: Types G e1 ?T, H2: Types G e2 ?T |- _ ] => 
            assert (Types G e T) by apply (typesIf G cond e1 e2 T Hc H1 H2)
        | [ H1: Types G e1 ?T1, H2: Types G e2 ?T2 |- _ ] => 
            fail "then-branch" e1 "has type" T1 "while else-branch" e2 "has type" T2
        | _ => idtac "expIf is stuck"
        end
      )]
  | _ => fail "no match for" e (* shouldn't happen *)
  end
.

(* Examples: Typechecking big expressions easily *)

Fact e_sum_test_types: Types nil e_sum_test tyNat.
Proof.
  unfold e_sum_test.
  tc.
Qed.

Fact e_minus_test_types: Types nil e_minus_test tyNat.
Proof.
  unfold e_minus_test.
  tc.
Qed.

Fact e_dec_test_types: Types nil e_dec_test tyNat.
Proof.
  unfold e_dec_test.
  tc.
Qed.

(* Examples: Precise error messages for untypable expressions *)
Fact err_1: Types nil (expApp (expConst (constNat 1)) (expConst (constNat 1))) tyNat.
Proof.
  (* tc. *)
Abort.

Fact err_2: Types nil (expApp (expFun 𝑓  𝑥  tyNat tyNat (expVar 𝑥)) 
                              (expConst (constBool true)))
                  tyNat.
Proof.
  (* tc. *)
Abort.
