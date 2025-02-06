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

CoInductive stream (A: Type): Type :=
  | cnil : stream A
  | ccons: A -> stream A -> stream A.

Fixpoint onths {A} (n: nat) (w: stream A): option A :=
  match (n, w) with
    | (_, cnil)         => None
    | (O, ccons x xs)   => Some x
    | (S k, ccons x xs) => onths k xs
  end.

Notation path := (stream tctx) (only parsing).

Definition fair (pt: path): Prop :=
  forall n p q c c' c'', 
  (onths n pt) = Some c -> tctxRE c (lcomm p q) -> 
  exists k, 
    (onths k pt)     = Some c'  ->
    (onths (S k) pt) = Some c'' ->
    k >= n /\ tctxR c' (lcomm p q) c''.
    
  



