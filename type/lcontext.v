From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From LIMR Require Import src.expressions src.header type.local.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations.
Import ListNotations. 

Inductive tctx: Type :=
  | tnil : tctx
  | tcons: part -> ltt -> tctx -> tctx.

Fixpoint appc (c1 c2: tctx): tctx :=
  match c1 with
    | tnil => c2
    | tcons p t ts => tcons p t (appc ts c2)
  end.

Inductive label: Type :=
  | lrecv: part -> part -> option sort -> label
  | lsend: part -> part -> option sort -> label
  | lcomm: part -> part -> label.

Check onth.

Inductive tctxR: tctx -> label -> tctx -> Prop :=
  | Rsend: forall p q xs n s T,
           onth n xs = Some (s, T) ->
           tctxR (tcons p (ltt_send q xs) tnil) (lsend p q (Some s)) (tcons p T tnil)
  | Rrecv: forall p q xs n s T,
           onth n xs = Some (s, T) ->
           tctxR (tcons p (ltt_recv q xs) tnil) (lrecv p q (Some s)) (tcons p T tnil)
  | Rcomm: forall p q g1 g1' g2 g2' s s', 
           tctxR g1 (lsend p q (Some s)) g1'  ->
           tctxR g2 (lsend p q (Some s')) g2' ->
           subsort s s' ->
           tctxR (appc g1 g2) (lcomm p q) (appc g1' g2')
  | Rvar : forall g l g' p T,
           tctxR g l g' ->
           tctxR (tcons p T g) l (tcons p T g').

Definition tctxRE c l := exists c', tctxR c l c'.

CoInductive lbl_stream (A: Type) (B:Type): Type :=
  | cnil : lbl_stream A B
  | ccons: A -> B -> lbl_stream A B -> lbl_stream A B.

Definition lblst_unf (A:Type) (B:Type) (pt:lbl_stream A B): lbl_stream A B :=
  match pt with
  | cnil => cnil A B
  | ccons c l p => ccons A B c l p end.
Arguments ccons {A} {B}.
Arguments lblst_unf {A} {B}.

Fixpoint onths {A} {B} (n: nat) (w: lbl_stream A B): option A :=
  match (n, w) with
    | (_, cnil)         => None
    | (O, ccons x _ xs)   => Some x
    | (S k, ccons x _ xs) => onths k xs
  end.

Notation path := (lbl_stream tctx label) (only parsing).

Lemma lblst_unf_eq : forall (s:path), s=lblst_unf s.
Proof.
  intros.
  destruct s.
  auto. reflexivity.
Qed.


Definition fair (pt: path): Prop :=
  forall n p q c c' c'', 
  (onths n pt) = Some c -> tctxRE c (lcomm p q) -> 
  exists k, 
    (onths k pt)     = Some c'  ->
    (onths (S k) pt) = Some c'' ->
    k >= n /\ tctxR c' (lcomm p q) c''.
    
Definition path_prop := path -> Prop.
Definition context_prop := tctx -> Prop.
Inductive eventually (F : path_prop) : path_prop:=
    | ev_head : forall p: path, F p -> eventually F p
    | ev_cons : forall (c:tctx) (p:path) (l:label), eventually F p -> eventually F (ccons c l p).

(* imm_trans pth l p q <-> the immediate next transition in pth is between p and q*)
Inductive imm_trans (p:part) (q:part) : path_prop :=
  imm_trans_c : forall (pt:path) (c:tctx), imm_trans p q (ccons c (lcomm p q) pt). 

Variant always_gen (F:path_prop) (alw_rel: path_prop): path_prop :=
  | alw_gc: forall (c:tctx) (p:path) (l:label), F (ccons c l p) -> alw_rel p -> always_gen F alw_rel (ccons c l p).

Hint Constructors always_gen.
Definition always (F:path_prop) (p:path):= paco1 (always_gen F) bot1 p.
Hint Unfold always.
Lemma always_gen_mon: forall (F:path_prop), monotone1 (always_gen F).
Proof.
  pmonauto.
Qed.
Hint Resolve always_gen_mon:paco.
(*simple always example*)
Variant not_nil : path_prop :=
  | nnn : forall c l p, not_nil (ccons c l p).

Definition always_not_nil := always not_nil.
CoFixpoint inf_path := ccons tnil (lcomm "p" "q") inf_path. 
Theorem inf_path_not_nil : always_not_nil inf_path.
Proof.
  pcofix CIH. pfold.
  rewrite (lblst_unf_eq inf_path). simpl.
  split.
  {
    constructor.
  }
  {
    right. apply CIH.
  }
Qed.
(*convert ctx prop to path prop i.e. for path p = c -l-> p', ctx_to_path_prop F p  iff F c*)
(*a context prop holds for a path if it holds for the head of the path*)
Variant ctx_to_path_prop (cp:context_prop): path_prop :=
  | pt_head : forall c l p, cp c -> ctx_to_path_prop cp (ccons c l p).

(*the transition enabled relation extended to paths*)
Definition trans_enabled_path (l:label) : path_prop :=ctx_to_path_prop (flip tctxRE l).
(* fairness= always (enabled (p,q) -> eventually (transmitted p q))*)
Definition fairness_inner (pt:path) : Prop := 
  forall p q, trans_enabled_path (lcomm p q) pt -> eventually (imm_trans p q) pt.

Definition fair_gfp := always (fairness_inner).

Theorem inf_fair : fair_gfp inf_path.
Proof.
  pcofix CIH.
  pfold.
  rewrite (lblst_unf_eq inf_path). simpl.
  split.
  {
    unfold fairness_inner.
    intros.
    apply ev_head.
    (*for demonstration purposes i pretend tnil is actually the context obtained from projecting 
    (mu t. p->q{l:t}) and i admit that the only comm transition possible from that context is (p,q)*)
    assert(hax_0:p=("p":string)). admit.
    assert(hax_1:q=("q":string)). admit.
    subst.
    apply imm_trans_c.
  }
  {
    right.
    apply CIH.
  }
Qed.