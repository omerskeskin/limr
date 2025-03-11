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
    | cocons (g, (lrecv a b (Some s))) xs => if andb (Nat.eqb p a) (Nat.eqb q b) then True else False
    | _                                   => False 
  end.

Definition headSend (p q: part) (pt: Path): Prop :=
  match pt with
    | cocons (g, (lsend a b (Some s))) xs => if andb (Nat.eqb p a) (Nat.eqb q b) then True else False
    | _                                   => False 
  end.

Definition headComm (p q: part) (pt: Path): Prop :=
  match pt with
    | cocons (g, (lcomm a b)) xs => if andb (Nat.eqb p a) (Nat.eqb q b) then True else False
    | _                          => False 
  end.

Inductive immTrans: part -> part -> Path -> Prop :=
  | immTc: forall p q c pt, immTrans p q (cocons (c,(lcomm p q)) pt).

Lemma eqvL: forall p q pt, immTrans p q pt -> headComm p q pt.
Proof. intros. induction H. cbn. rewrite !Nat.eqb_refl. easy. Qed.

Lemma eqvR: forall p q pt, headComm p q pt -> immTrans p q pt.
Proof. intros.
       destruct pt. simpl in H. easy.
       simpl in H.
       destruct p0, l.
       easy.
       easy.
       case_eq((p =? n)); intros.
       + rewrite Nat.eqb_eq in H0.
         subst.
         case_eq((q =? n0)); intros.
         ++ rewrite Nat.eqb_eq in H0.
            subst.
            constructor.
         ++ rewrite H0 in H. rewrite Nat.eqb_refl in H. simpl in H. easy.
       + rewrite H0 in H. simpl in H. easy.
Qed.

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
