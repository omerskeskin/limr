(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From LIMR Require Import src.expressions src.header type.local type.lcontext.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations.
Require Import Coq.Program.Equality.
Import ListNotations.


CoInductive coseq (A: Type): Type :=
  | conil : coseq A
  | cocons: A -> coseq A -> coseq A.

Arguments conil {_}.
Arguments cocons {_} _ _.

Definition coseq_id {A: Type} (c: coseq A): coseq A :=
  match c with
    | conil       => conil
    | cocons x xs => cocons x xs
  end.

Lemma coseq_eq: forall {A: Type} (c: coseq A), c = coseq_id c.
Proof. destruct c; easy. Defined.

Notation Path := (coseq (tctx*label)) (only parsing).

Inductive eventually {A: Type} (F: coseq A -> Prop): coseq A -> Prop :=
  | evh: forall xs, F xs -> eventually F xs
  | evc: forall x xs, eventually F xs -> eventually F (cocons x xs).

Definition eventualyP := @eventually (tctx*label).

Inductive alwaysG {A: Type} (F: coseq A -> Prop) (R: coseq A -> Prop): coseq A -> Prop :=
  | alwn: F conil -> alwaysG F R conil
  | alwc: forall x xs, F (cocons x xs) -> R xs -> alwaysG F R (cocons x xs).

Definition alwaysP := @alwaysG (tctx*label).

Definition alwaysC F p := paco1 (alwaysP F) bot1 p.

Definition enabled (F: tctx -> Prop) (pt: Path): Prop :=
  match pt with
    | cocons (g, l) xs => F g
    | _                => False 
  end.

Definition headRecv (p q: part) (pt: Path): Prop :=
  match pt with
    | cocons (g, (lrecv p q (Some s))) xs => True
    | _                                   => False 
  end.

Definition headSend (p q: part) (pt: Path): Prop :=
  match pt with
    | cocons (g, (lsend p q (Some s))) xs => True
    | _                                   => False 
  end.

Definition headComm (p q: part) (pt: Path): Prop :=
  match pt with
    | cocons (g, (lcomm p q)) xs => True
    | _                          => False 
  end.

Definition fairPath (pt: Path): Prop :=
  forall p q, enabled (tctxRE (lcomm p q)) pt -> eventually (headComm p q) pt.

Definition fairness := alwaysC fairPath.

Inductive livePath (pt: Path): Prop :=
  | L1: forall p q s, enabled (tctxRE (lsend p q (Some s))) pt -> eventually (headComm p q) pt -> livePath pt
  | L2: forall p q s, enabled (tctxRE (lrecv q p (Some s))) pt -> eventually (headComm p q) pt -> livePath pt.

Definition liveness := alwaysC livePath.

Inductive safe (R: tctx -> Prop): tctx -> Prop :=
  | sasr  : forall p q s s' c, tctxRE (lsend p q (Some s)) c -> tctxRE (lrecv q p (Some s')) c ->
                               tctxRE (lcomm p q) c -> safe R c
  | saimpl:  forall p q c c', R c -> tctxRF (lcomm p q) c c' -> safe R c'.

Definition safeC c := paco1 safe bot1 c.
