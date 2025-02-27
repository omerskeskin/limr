(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From LIMR Require Import src.expressions src.header type.local.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations.
Import ListNotations. 

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

Module M := FMapAVL.Make(Nat_as_OT).

Definition tctx2: Type := M.t ltt.

Definition find (p: part) (m: tctx2) := 
  M.find p m.

Definition add (p: part) (T: ltt) (m: tctx2) :=
  M.add p T m.

Definition empty := M.empty (ltt).

Notation tctx := (list (part*ltt)) (only parsing).

Class ctx: Type :=
  mkCt
  { und: tctx;
    reg: NoDup (map fst und)
  }.

(*shadows*)
Fixpoint typeof (c: tctx) (p: part): option ltt :=
  match c with
    | nil         => None
    | (q,t) :: c' => if Nat.eqb p q then Some t else typeof c' p
  end. 

Fixpoint dom (c: tctx): list part :=
  match c with
    | nil         => nil
    | (p,t) :: c' => p :: dom c'
  end.

Fixpoint appc (c1 c2: tctx): tctx :=
  match c1 with
    | nil => c2
    | (p,t) :: ts => (p,t) :: (appc ts c2)
  end.

Inductive label: Type :=
  | lrecv: part -> part -> option sort -> label
  | lsend: part -> part -> option sort -> label
  | lcomm: part -> part -> label.

Check onth.

Inductive tctxR: tctx -> label -> tctx -> Prop :=
  | Rsend: forall p q xs n s T,
           p <> q ->
           onth n xs = Some (s, T) ->
           tctxR [(p,(ltt_send q xs))] (lsend p q (Some s)) [(p,T)]
  | Rrecv: forall p q xs n s T,
           p <> q ->
           onth n xs = Some (s, T) ->
           tctxR [(p,(ltt_recv q xs))] (lrecv p q (Some s)) [(p,T)]
  | Rcomm: forall p q g1 g1' g2 g2' s s', 
           p <> q ->
           tctxR g1 (lsend p q (Some s)) g1'  ->
           tctxR g2 (lrecv q p (Some s')) g2' ->
           subsort s s' ->
           tctxR (g1 ++ g2) (lcomm p q) (g1' ++ g2')
  | RvarI: forall g l g' p T,
           (In p (map fst g) -> False) ->
           (In p (map fst g') -> False) ->
           tctxR g l g' ->
           tctxR ((p,T)::g) l ((p,T)::g')
  | RvarO: forall g l g' p T,
           (In p (map fst g) -> False) ->
           (In p (map fst g') -> False) ->
           tctxR g l g' ->
           tctxR (g++[(p,T)]) l (g'++[(p,T)]).

Lemma nilDec: forall (g1 g2: tctx), g1 ++ g2 = nil -> g1 = nil /\ g2 = nil.
Proof. intro g1.
       induction g1; intros.
       - simpl in H. subst. easy.
       - simpl in H. destruct a. easy.
Qed.

Lemma nNil: forall {A: Type} (g: list A) a, (g ++ [a]) = [] -> False.
Proof. intros A g.
       induction g; intros.
       - simpl in H. easy.
       - simpl in H. easy.
Qed.

Lemma eCHL: forall l x xs, tctxR [] l (x :: xs) -> False.
Proof. intros.
       inversion H. subst.
       apply nilDec in H0.
       destruct H0 as (Ha, Hb).
       subst.
       inversion H3. apply nNil in H0. easy.
       apply nNil in H0. easy.
Qed.

Lemma eCHR: forall l x xs, tctxR (x :: xs) l [] -> False.
Proof. intros.
       inversion H. subst.
       apply nilDec in H1.
       destruct H1 as (Ha, Hb).
       subst.
       inversion H3.
       apply nNil in H1. easy.
       apply nNil in H1. easy.
Qed.

Lemma eCHB: forall l, tctxR [] l [] -> False.
Proof. intros.
       inversion H. subst.
       apply nilDec in H0.
       destruct H0 as (Ha, Hb).
       subst.
       inversion H3.
       apply nNil in H0. easy.
       apply nNil in H0. easy.
Qed.

Definition tctxRE l c := exists c', tctxR c l c'.

Definition tctxRF l c c' := tctxR c l c'.

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

Inductive CextP (F: tctx -> Prop): Path -> Prop :=
  | holdc: forall c l p, F c -> CextP F (cocons (c,l) p).

Inductive immTrans: part -> part -> Path -> Prop :=
  | immTc: forall p q c pt, immTrans p q (cocons (c,(lcomm p q)) pt).

Definition fairness_inner (pt: Path): Prop :=
  forall p q, CextP (tctxRE (lcomm p q)) pt -> eventually (immTrans p q) pt.

Definition fair_gfp := alwaysC (fairness_inner).

Definition liveness_inner (pt: Path): Prop :=
  (forall p q s, CextP (tctxRE (lsend p q (Some s))) pt -> eventually (immTrans p q) pt) /\
  (forall p q s, CextP (tctxRE (lrecv q p (Some s))) pt -> eventually (immTrans p q) pt).

Definition live_gfp := alwaysC (liveness_inner).

(* example *)
CoFixpoint inf_path := cocons ((@nil (nat * ltt)), (lcomm 0 1)) inf_path.

Lemma appcNnil: forall g p T, appc g [(p,T)] = nil -> False.
Proof. intro g.
       induction g; intros.
       - simpl in H. easy.
       - simpl in H. destruct a. easy.
Qed.

Theorem inf_fair: fair_gfp inf_path.
Proof. red.
       pcofix CIH.
       rewrite(coseq_eq inf_path). simpl.
       pfold.
       constructor.
       constructor.
       inversion H. subst.
       inversion H1.
       inversion H0. subst.
       rewrite H2.
       apply nilDec in H2.
       destruct H2 as (H2a, H2b).
       subst.
       case_eq g1'; intros.
       + subst. apply eCHB in H6. easy.
       + subst. apply eCHL in H6. easy.
       apply nNil in H2. easy.
       right. exact CIH.
Qed.

Inductive safe (R: tctx -> Prop): tctx -> Prop :=
  | sasr  : forall p q s s' c, tctxRE (lsend p q (Some s)) c -> tctxRE (lrecv q p (Some s')) c ->
                               tctxRE (lcomm p q) c -> safe R c
  | saimpl:  forall p q c c', R c -> tctxRF (lcomm p q) c c' -> safe R c'.

Definition safeC c := paco1 safe bot1 c.

Lemma dom_app: forall c c', dom (c ++ c') = dom c ++ dom c'.
Proof. intro c.
       induction c; intros.
       - simpl. easy.
       - simpl. destruct a. simpl. rewrite IHc. easy.
Qed.

Lemma _6_9: forall c c' l, tctxR c l c' -> dom c = dom c'.
Proof. intros.
       induction H; intros.
       - simpl. easy.
       - simpl. easy.
       - simpl.
         inversion H1. subst.
         + inversion H0. 
           ++ subst. simpl. easy.
           ++ subst. simpl. simpl in *.
              inversion IHtctxR2. subst.
              rewrite dom_app.
              simpl.
              rewrite dom_app. simpl.
              rewrite !app_comm_cons. 
              rewrite IHtctxR1. easy.
              rewrite <- H10, <- H6 in IHtctxR1.
              rewrite !dom_app in IHtctxR1.
              simpl in IHtctxR1.
              rewrite !dom_app. simpl.
              simpl.
              rewrite IHtctxR1. easy.
              rewrite !dom_app. simpl.
              rewrite IHtctxR1. 
              rewrite <- H8, <- H6 in IHtctxR2.
              simpl in IHtctxR2.
              rewrite IHtctxR2. easy.
              rewrite dom_app.
              setoid_rewrite dom_app at 2.
              rewrite H6.
              rewrite H8.
              rewrite IHtctxR1, IHtctxR2. easy.
              simpl. rewrite IHtctxR. easy.
              rewrite !dom_app. rewrite IHtctxR. easy.
Qed.


Lemma _6_11a: forall p q (c c': ctx) s, tctxR (@und c) (lsend p q (Some s)) (@und c') -> 
 exists xs n T, typeof (@und c) p = Some (ltt_send q xs) /\ onth n xs = Some (s, T). 
Proof. intros.
       inversion H.
       - subst. simpl. rewrite Nat.eqb_refl.
         exists xs. exists n. exists T. easy.
       - subst. simpl.
         inversion H5.
Admitted.

