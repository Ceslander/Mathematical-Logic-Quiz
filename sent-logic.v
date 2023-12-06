From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

Import List.ListNotations.

(** * Formulas and Proof Rules in Natural Deduction *)

(** Define the well-formed formulas *)
Inductive Wff : Type :=
| Lsymb: string -> Wff
| Land:   Wff -> Wff -> Wff
| Lor:    Wff -> Wff -> Wff
| Lnot:   Wff -> Wff
| Limply: Wff -> Wff -> Wff.

(** Define proof rules *)
Inductive Prv : list Wff -> Wff -> Prop :=
| Plem: forall hyps f,
    Prv hyps (Lor f (Lnot f))
| Pbase: forall f hyps, 
    In f hyps -> Prv hyps f
| Pand_intro: forall hyps f1 f2,
    Prv hyps f1 -> Prv hyps f2 ->
    Prv hyps (Land f1 f2)
| Pand_elim1: forall hyps f1 f2,
    Prv hyps (Land f1 f2) ->
    Prv hyps f1
| Pand_elim2: forall hyps f1 f2,
    Prv hyps (Land f1 f2) ->
    Prv hyps f2
| Por_intro1: forall hyps f1 f2,
    Prv hyps f1 ->
    Prv hyps (Lor f1 f2)
| Por_intro2: forall hyps f1 f2,
    Prv hyps f2 ->
    Prv hyps (Lor f1 f2)
| Por_elim: forall hyps f1 f2 g,
    Prv hyps (Lor f1 f2) ->
    Prv (f1 :: hyps) g ->
    Prv (f2 :: hyps) g ->
    Prv hyps g
| Pnot_intro: forall hyps f g,
    Prv (f :: hyps) (Land g (Lnot g)) ->
    Prv hyps (Lnot f)
| Pnot_elim: forall hyps g f,
    Prv hyps g ->
    Prv hyps (Lnot g) ->
    Prv hyps f
| Pimply_intro: forall hyps f g,
    Prv (f :: hyps) g ->
    Prv hyps (Limply f g)
| Pimply_elim: forall hyps f g,
    Prv hyps f ->
    Prv hyps (Limply f g) ->
    Prv hyps g.

(** * Construction of Proofs *)

Let A := Lsymb "A".
Let B := Lsymb "B".
Let C := Lsymb "C".

(** A -> B -> A /\ B *)
Example ex1 : Prv [] (Limply A (Limply B (Land A B))).
  apply Pimply_intro.
  apply Pimply_intro.
  apply Pand_intro.
  - apply Pbase.
    red. tauto.
  - apply Pbase.
    red. tauto.
Defined.

Print ex1.

(** Ltac for automating the proof for base cases *)
Ltac prove_base := apply Pbase; red; tauto.

(** ((A -> B) -> C) -> (A -> B -> C) *)
Example ex2 : Prv [] (Limply (Limply (Limply A B) C) (Limply A (Limply B C))).
  apply Pimply_intro.
  apply Pimply_intro.
  apply Pimply_intro.
  apply Pimply_elim with (f := (Limply A B)).
  - apply Pimply_intro.
    prove_base.
  - prove_base.
Defined.

(** ~~A -> A *)
Example ex3 : Prv [] (Limply (Lnot (Lnot A)) A).
  apply Pimply_intro.
  apply Por_elim with (f1 := A) (f2 := (Lnot A)).
  - apply Plem.
  - prove_base.
  - apply Pnot_elim with (g := (Lnot A)).
    + prove_base.
    + prove_base.
Defined.

(** An example of universally quantified propositions: *)
(** ~~\alpha -> \alpha *)
Proposition ex3' : forall (a: Wff), Prv [] (Limply (Lnot (Lnot a)) a).
  intros.
  apply Pimply_intro.
  apply Por_elim with (f1 := a) (f2 := (Lnot a)).
  - apply Plem.
  - prove_base.
  - apply Pnot_elim with (g := (Lnot a)).
    + prove_base.
    + prove_base.
Defined.

Eval compute in (ex3' A).

(** An example of partial proof trees: *)
(** A; B |- (A -> C) \/ (B -> C) -> C *)
Example ex4 : Prv [A; B] (Limply (Lor (Limply A C) (Limply B C)) C).
  apply Pimply_intro.
  apply Por_elim with (f1 := Limply A C) (f2 := Limply B C).
  - prove_base.
  - apply Pimply_elim with (f := A).
    + prove_base.
    + prove_base.
  - apply Pimply_elim with (f := B).
    + prove_base.
    + prove_base.
Defined.

(** * Notations *)

(** Notations for formulas *)
Notation "@ id" := (Lsymb id) (at level 10, no associativity).
Notation "! a" := (Lnot a) (at level 15, right associativity).
Notation "a &&& b" := (Land a b) (at level 20, right associativity).
Notation "a ||| b" := (Lor a b) (at level 25, right associativity).
Notation "a ~> b" := (Limply a b) (at level 30, right associativity).

(** Notations for provability *)
Notation "g |- a" := (Prv g a) (at level 40, no associativity).
Notation " |- a" := ([] |- a) (at level 40, no associativity).

(** ~~A -> A *)
Example ex5 : |- !!A ~> A.
  apply Pimply_intro.
  apply Por_elim with (f1 := A) (f2 := !A).
  - apply Plem.
  - prove_base.
  - apply Pnot_elim with (g := !A).
    + prove_base.
    + prove_base.
Defined.

(** ((A -> B) -> C) -> (A -> B -> C) *)
Example ex6 : |- ((A ~> B) ~> C) ~> (A ~> B ~> C).
  apply Pimply_intro.
  apply Pimply_intro.
  apply Pimply_intro.
  apply Pimply_elim with (f := (Limply A B)).
  - apply Pimply_intro.
    prove_base.
  - prove_base.
Defined.

(** ** Exercise 1 *)

Let P := @"P".
Let Q := @"Q".

(** [5 Points] *)
(** A /\ (B \/ C) -> (A /\ B) \/ (A /\ C) *)
Example exerc1 : |- A &&& (B ||| C) ~> (A &&& B) ||| (A &&& C).
  apply Pimply_intro.
  apply Por_elim with (f1 := B) (f2 := C).
  - apply Pand_elim2 with (f1:= A).
    prove_base.
  - apply Por_intro1.
    apply Pand_intro.
    -- apply Pand_elim1 with (f2 := (Lor B C)).
       prove_base.
    -- prove_base.
  - apply Por_intro2.
    apply Pand_intro.
    -- apply Pand_elim1 with (f2 := (Lor B C)).
       prove_base.
    -- prove_base.
Defined.

(** [5 Points] *)
(** (P -> Q) -> P) -> P *)
 Example exerc2: |- ((P ~> Q) ~> P) ~> P.
  apply Pimply_intro.
  apply Por_elim with (f1 := P) (f2 := !P).
  - apply Plem.
  - prove_base.
  - apply Pimply_elim with (f := (Limply P Q)).
    -- apply Pimply_intro.
       apply Pnot_elim with (g := P).
       + prove_base.
       + prove_base.
    -- prove_base.
Defined.
  


