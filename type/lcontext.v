(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From LIMR Require Import src.expressions src.header type.local.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations.
Require Import Coq.Program.Equality.
Import ListNotations.


Inductive label: Type :=
  | lrecv: part -> part -> option sort -> label
  | lsend: part -> part -> option sort -> label
  | lcomm: part -> part -> label.

From MMaps Require Import MMaps.

Module M := MMaps.RBT.Make(Nat).
Module MF := MMaps.Facts.Properties Nat M.

Definition tctx: Type := M.t ltt.

Definition both (z: nat) (o:option ltt) (o':option ltt) :=
 match o,o' with 
   | Some _, None   => o
   | None, Some _   => o'
   | _,_            => None
 end.

(*
Definition e1 := M.add 0 ltt_end (M.add 1 ltt_end M.empty).
Definition e2 := M.add 2 (ltt_send 1 [Some(sint, ltt_end)]) (M.add 4 ltt_end M.empty).
Definition e3 := M.merge both e1 e2.
Compute M.bindings e1.
Compute M.bindings e2.
Compute M.bindings e3.

Print M.
 *)

Definition disj_merge (g1 g2:tctx) (H:MF.Disjoint g1 g2) : tctx := 
  M.merge both g1 g2.  



Inductive tctxR: tctx -> label -> tctx -> Prop :=
  | Rsend: forall p q xs n s T,
            p <> q ->
            onth n xs = Some (s, T) ->
            tctxR (M.add p (ltt_send q xs) M.empty) (lsend p q (Some s)) (M.add p T M.empty)
  | Rrecv: forall p q xs n s T,
            p <> q ->
            onth n xs = Some (s, T) ->
            tctxR (M.add p (ltt_recv q xs) M.empty) (lrecv p q (Some s)) (M.add p T M.empty)
  | Rcomm: forall p q g1 g1' g2 g2' s s' (H1: MF.Disjoint g1 g2) (H2: MF.Disjoint g1' g2'), 
            p <> q ->
            tctxR g1 (lsend p q (Some s)) g1'  ->
            tctxR g2 (lrecv q p (Some s')) g2' ->
            subsort s s' ->
            tctxR (disj_merge g1 g2 H1) (lcomm p q) (disj_merge g1' g2' H2)
  | RvarI: forall g l g' p T,
            tctxR g l g' ->
            M.mem p g = false ->
            tctxR (M.add p T g) l (M.add p T g')
  | Rstruct: forall g1 g1' g2 g2' l,
    tctxR g1' l g2' ->
    M.Equal g1 g1' ->
    M.Equal g2 g2' ->
    tctxR g1 l g2.



Definition tctxRE l c := exists c', tctxR c l c'.

Definition tctxRF l c c' := tctxR c l c'.

Lemma opt_lem1 : forall A (x:option A), x <> None -> exists y, x=Some y.
Proof.
  intros; destruct x; try easy. exists a. reflexivity.  
Qed.

Lemma opt_lem2 : forall A (x:option A) (y:A), x=Some y -> x<> None.
Proof.
  intros; destruct x; try easy.  
Qed.

Lemma in_find_sm : forall x (m:tctx), M.In x m <-> exists y, M.find x m =Some y. 
Proof.
  intros.
  split.
  {
    intros. apply MF.in_find in H. apply opt_lem1 in H. easy.
  }
  {
    intros.
    destruct H.
    apply opt_lem2 in H.
    apply MF.in_find in H. easy.
  }
Qed.
Lemma spc_merge_spec1: forall (g g': tctx) x (Hdisj: MF.Disjoint g g'),  M.In x g\/ M.In x g' -> (M.In x (disj_merge g g' Hdisj)).
Proof.
  intros.
  destruct H.
  {
    specialize (M.merge_spec1 both (@or_introl (M.In x g) (M.In x g') H)) as H_spc.
    destruct H_spc. destruct H0. subst.
    Check MF.in_find.
    apply MF.in_find.
    unfold disj_merge.
    (*prove: both x (M.find x g) (M.find x g') <>=None*)
    assert(Hres:both x (M.find x g) (M.find x g') <> None).
    {
      apply MF.in_find in H.
      unfold MF.Disjoint in Hdisj.
      specialize (Hdisj x).
      apply MF.in_find in H.
      destruct (M.find x g') eqn:H'.
      {
        assert(M.find x g' <> None). {
          apply opt_lem2 with (y:=l).  assumption.
        }
        apply MF.in_find in H0. exfalso.
        apply Hdisj. easy.
      }
      {
        apply MF.in_find in H.
        apply opt_lem1 in H. destruct H. unfold both. rewrite H. easy.
      }
    } 
    apply opt_lem1 in Hres.
    destruct Hres. rewrite H0 in H1. rewrite H1. easy.
  }
  {
    specialize (M.merge_spec1 both (@or_intror (M.In x g) (M.In x g') H)) as H_spc.
    destruct H_spc. destruct H0. subst.
    Check MF.in_find.
    apply MF.in_find.
    unfold disj_merge.
    (*prove: both x (M.find x g) (M.find x g') <>=None*)
    assert(Hres:both x (M.find x g) (M.find x g') <> None).
    {
      apply MF.in_find in H.
      unfold MF.Disjoint in Hdisj.
      specialize (Hdisj x).
      apply MF.in_find in H.
      destruct (M.find x g) eqn:H'.
      {
        assert(M.find x g <> None). {
          apply opt_lem2 with (y:=l).  assumption.
        }
        apply MF.in_find in H0. exfalso.
        apply Hdisj. easy.
      }
      {
        apply MF.in_find in H.
        apply opt_lem1 in H. destruct H. unfold both. rewrite H. easy.
      }
    } 
    apply opt_lem1 in Hres.
    destruct Hres. rewrite H0 in H1. rewrite H1. easy.
  }
Qed.

Lemma spc_merge_find1: forall (g1 g2:tctx) p H_disj x, M.find p g1 = Some x ->
  M.find p (disj_merge g1 g2 H_disj)=Some x.
Proof.
  intros.
  Search M.merge M.find.
  unfold disj_merge.
  rewrite MF.merge_spec1mn; try easy.
  unfold MF.Disjoint in H_disj.
  specialize (H_disj p).
  destruct (M.find p g2) eqn:H_2. 2: {rewrite H. simpl. reflexivity. }
  apply opt_lem2 in H.
  apply opt_lem2 in H_2.
  apply MF.in_find in H.
  apply MF.in_find in H_2. exfalso. exact (H_disj (conj H H_2)). 
Qed.

Lemma spc_merge_find2: forall (g1 g2:tctx) p H_disj x, M.find p g2 = Some x ->
  M.find p (disj_merge g1 g2 H_disj)=Some x.
Proof.
  intros.
  Search M.merge M.find.
  unfold disj_merge.
  rewrite MF.merge_spec1mn; try easy.
  unfold MF.Disjoint in H_disj.
  specialize (H_disj p).
  destruct (M.find p g1) eqn:H_2. 2: {rewrite H. simpl. reflexivity. }
  apply opt_lem2 in H.
  apply opt_lem2 in H_2.
  apply MF.in_find in H.
  apply MF.in_find in H_2. exfalso. exact (H_disj (conj H_2 H)). 
Qed.

Lemma empty_disjoint : forall (g:tctx), MF.Disjoint g M.empty.
Proof.
  intros.
  unfold MF.Disjoint. unfold not. intros.
  destruct H. 
  Search M.In M.empty.
  apply MF.empty_in_iff in H0. assumption.
Qed.

Lemma disj_merge_unit: forall (g:tctx), M.Equal g (disj_merge g M.empty (empty_disjoint g)).
Proof.
  intros. unfold M.Equal. intros. unfold disj_merge.
  Check MF.merge_spec1mn.
  rewrite MF.merge_spec1mn.
  unfold M.find at 3.
  simpl. unfold both. 
  destruct (M.find y g);reflexivity.
  Check Proper.
  unfold Proper.
  unfold "==>".
  intros. subst. reflexivity. intros. unfold both. simpl. reflexivity. 
Qed.


Lemma dom_preservation_6_9: forall g l g', tctxR g l g' -> M.Eqdom g g'.
Proof.
  intros.
  split.
  {
    induction H.
    {
      intros.
      apply MF.add_in_iff in H1.
      destruct H1.
      {
        subst.
        apply MF.add_in_iff. left. reflexivity.
      }
      {
        apply MF.empty_in_iff in H1. easy.
      }
    }
    {

      intros.
      apply MF.add_in_iff in H1.
      destruct H1.
      {
        subst.
        apply MF.add_in_iff. left. reflexivity.
      }
      {
        apply MF.empty_in_iff in H1. easy.
      }
    }
    {
      intros.
      apply M.merge_spec2 in H5.
      destruct H5.
      {
        apply  IHtctxR1 in H5.
        apply spc_merge_spec1.
        left. easy.
      }
      {
        apply  IHtctxR2 in H5.
        apply spc_merge_spec1.
        right. easy.
      }
    }
    {
      intros.
      rewrite MF.add_in_iff in H1.
      rewrite MF.add_in_iff.
      destruct H1.
      {
        left. easy.
      }
      {
        right. apply  IHtctxR. easy.
      }
    }
    {
      intros.
      unfold M.Equal in H0.
      specialize (H0 y).
      destruct(M.find y g1) eqn:H_mfind.
      {
        apply eq_sym in H0.
        apply (opt_lem2 _ (M.find y g1') _) in H0.
        apply MF.in_find in H0.
        apply IHtctxR in H0.
        unfold M.equal in H1.
        specialize (H1 y).
        apply MF.in_find in H0.
        apply opt_lem1 in H0.
        destruct H0.
        rewrite H0 in H1.
        apply opt_lem2 in H1.
        apply MF.in_find in H1.
        assumption.
      }
      {
        apply MF.not_in_find in H_mfind.
        exfalso. apply H_mfind in H2. assumption.
      }
    }
  }
  {
    induction H.
    {
      intros.
      apply MF.add_in_iff in H1.
      destruct H1.
      {
        subst.
        apply MF.add_in_iff. left. reflexivity.
      }
      {
        apply MF.empty_in_iff in H1. easy.
      }
    }
    {

      intros.
      apply MF.add_in_iff in H1.
      destruct H1.
      {
        subst.
        apply MF.add_in_iff. left. reflexivity.
      }
      {
        apply MF.empty_in_iff in H1. easy.
      }
    }
    {
      intros.
      apply M.merge_spec2 in H5.
      destruct H5.
      {
        apply  IHtctxR1 in H5.
        apply spc_merge_spec1.
        left. easy.
      }
      {
        apply  IHtctxR2 in H5.
        apply spc_merge_spec1.
        right. easy.
      }
    }
    {
      intros.
      rewrite MF.add_in_iff in H1.
      rewrite MF.add_in_iff.
      destruct H1.
      {
        left. easy.
      }
      {
        right. apply  IHtctxR. easy.
      }
    }
    {
      intros.
      unfold M.Equal in H1.
      specialize (H1 y).
      destruct(M.find y g2) eqn:H_mfind.
      {
        apply eq_sym in H1.
        apply (opt_lem2 _ (M.find y g2') _) in H1.
        apply MF.in_find in H1.
        apply IHtctxR in H1.
        specialize (H0 y).
        apply MF.in_find in H1.
        apply opt_lem1 in H1.
        destruct H1.
        rewrite H1 in H0.
        apply opt_lem2 in H0.
        apply MF.in_find in H0.
        assumption.
      }
      {
        apply MF.not_in_find in H_mfind.
        exfalso. apply H_mfind in H2. assumption.
      }
    }
  }
Qed. 

Lemma tctx_lsend_inv_1 : forall g p q g' s, tctxR g (lsend p q (Some s)) g' ->
  exists xs, (M.find p g=Some (ltt_send q xs)).
Proof.
  intros.
  dependent induction H.
  {
    subst. exists xs. apply M.add_spec1.
  }
  {
    subst.
    specialize (IHtctxR p q s). 
    set (H_rf:=eq_refl (lsend p q (Some s))). 
    apply IHtctxR in H_rf.
    destruct H_rf.
    destruct (Nat.eq_dec p p0).
    {
      subst. 
      rewrite MF.not_mem_find in H0. rewrite -> H0 in H1. discriminate H1.
    }
    {
       exists x.
       apply not_eq_sym in n.
       apply M.add_spec2 with (m:=g) (e:=T) in n. rewrite H1 in n. assumption.
    }
  }
  {
    specialize (IHtctxR p q s). 
    set (H_rf:=eq_refl (lsend p q (Some s))). 
    apply IHtctxR in H_rf.
    destruct H_rf. exists x.
    unfold M.Equal in H0. specialize (H0 p). 
    rewrite <- H0 in H2. assumption.
  }
Qed.  

Lemma tctx_lrecv_inv_1 : forall g p q g' s, tctxR g (lrecv p q (Some s)) g' ->
  exists xs, (M.find p g=Some (ltt_recv q xs)).
Proof.
  intros.
  dependent induction H.
  {
    subst. exists xs. apply M.add_spec1.
  }
  {
    subst.
    specialize (IHtctxR p q s). 
    set (H_rf:=eq_refl (lrecv p q (Some s))). 
    apply IHtctxR in H_rf.
    destruct H_rf.
    destruct (Nat.eq_dec p p0).
    {
      subst. 
      rewrite MF.not_mem_find in H0. rewrite -> H0 in H1. discriminate H1.
    }
    {
       exists x.
       apply not_eq_sym in n.
       apply M.add_spec2 with (m:=g) (e:=T) in n. rewrite H1 in n. assumption.
    }
  }
  {
    specialize (IHtctxR p q s). 
    set (H_rf:=eq_refl (lrecv p q (Some s))). 
    apply IHtctxR in H_rf.
    destruct H_rf. exists x.
    unfold M.Equal in H0. specialize (H0 p). 
    rewrite <- H0 in H2. assumption.
  }
Qed.  


Lemma tctx_lcomm_inv_1 : forall g p q g' lb, tctxR g lb g' ->
  (lb=lcomm p q -> (exists xs, M.find p g=Some (ltt_send q xs))/\
  (exists xs, (M.find q g=Some (ltt_recv p xs)))) /\
  (forall s, lb=lrecv p q (Some s) ->
  tctxR g (lrecv p q (Some s)) g' ->
  exists xs, (M.find p g=Some (ltt_recv q xs)))/\
  (forall s, lb=lsend p q (Some s) -> 
  tctxR g (lsend p q (Some s)) g' ->
  exists xs, (M.find p g=Some (ltt_send q xs))).
Proof.
  intros.
  generalize dependent q.
  generalize dependent p.
  induction H.
  {
    split; [|split]; try (intros; easy).
    intros.
    inversion H1. subst.
    apply tctx_lsend_inv_1 in H2. exact H2.
  }
  {
    split; [|split]; try (intros; easy).
    intros.
    inversion H1. subst.
    apply tctx_lrecv_inv_1 in H2. exact H2.
  }
  {
    split; [|split]. intros. 
    split.
    {
      inversion H5. subst.
      specialize (IHtctxR1 p0 q0).
      destruct IHtctxR1 as [IH1_comm  IH2];destruct IH2 as [IH1_recv IH1_sendv].
      inversion H5. subst.
      specialize (IH1_sendv s (eq_refl (lsend p0 q0 (Some s)))).
      apply IH1_sendv in H0.
      destruct H0.
      exists x.
      apply spc_merge_find1 with (g2:=g2) (H_disj:=H1) in H0. assumption.
    }
    {
      inversion H5. subst.
      specialize (IHtctxR2 q0 p0).
      destruct IHtctxR2 as [IH2_comm  IH2];destruct IH2 as [IH2_recv IH2_sendv].
      specialize (IH2_recv s' (eq_refl (lrecv q0 p0 (Some s')))).
      apply IH2_recv in H3. destruct H3. exists x.
      apply spc_merge_find2 with (g1:=g1) (H_disj:=H1) in H3. assumption.      
    }
    1-2:intros; discriminate H5.
  }
  {
    intros.
    split; [|split].
    {
      generalize dependent q.
      generalize dependent p.
      intros.
      subst.
      specialize (IHtctxR p0 q). 
      destruct IHtctxR as [IH_comm  IH];destruct IH as [IH_recv IH_sendv].
      specialize (IH_comm (eq_refl (lcomm p0 q))).
      split.
      {
        destruct IH_comm.
        destruct H1.
        exists x.
        rewrite MF.add_o.
        destruct (Nat.eq_dec p p0).
        - subst. apply MF.not_mem_find in H0. rewrite H1 in H0. discriminate H0.
        - assumption.
      }
      {
        destruct IH_comm.
        destruct H2.
        exists x.
        rewrite MF.add_o.
        destruct (Nat.eq_dec p q).
        - subst. apply MF.not_mem_find in H0. rewrite H2 in H0. discriminate H0.
        - assumption.
      }
    }
    {
      intros.
      subst.
      specialize (IHtctxR p0 q). 
      destruct IHtctxR as [IH_comm  IH];destruct IH as [IH_recv IH_sendv].
      specialize (IH_recv s (eq_refl (lrecv p0 q (Some s))) H).
      destruct IH_recv.
      exists x.
      rewrite M.add_spec2. assumption. rewrite MF.not_mem_find in H0.
      unfold not.
      intros.
      subst. rewrite H0 in H1. discriminate H1. 
    }
    {
      intros.
      subst.
      specialize (IHtctxR p0 q). 
      destruct IHtctxR as [IH_comm  IH];destruct IH as [IH_recv IH_sendv].
      specialize (IH_sendv s (eq_refl (lsend p0 q (Some s))) H).
      destruct IH_sendv.
      exists x.
      rewrite M.add_spec2. assumption. rewrite MF.not_mem_find in H0.
      unfold not.
      intros.
      subst. rewrite H0 in H1. discriminate H1. 
    }
  }
  {
    intros. split; [|split]. intros. subst.   
    specialize (IHtctxR p q). 
    destruct IHtctxR as [IH_comm  IH];destruct IH as [IH_recv IH_sendv].
    specialize (IH_comm (eq_refl (lcomm p q ))).
    destruct IH_comm.
    {
      split.
      {
        destruct H2.
        exists x.
        rewrite MF.find_m in H2.
        exact H2. reflexivity. apply MF.Equal_equiv. assumption. 
      }
      {
        destruct H3.
        exists x.
        rewrite MF.find_m in H3.
        exact H3. reflexivity. apply MF.Equal_equiv. assumption. 
      }
    }
    {
      intros.
      specialize (IHtctxR p q). 
      destruct IHtctxR as [IH_comm  IH];destruct IH as [IH_recv IH_sendv].
      subst.
      specialize (IH_recv s (eq_refl (lrecv p q (Some s))) H).
      destruct IH_recv. exists x.
      rewrite MF.find_m in H2. exact H2. reflexivity. apply MF.Equal_equiv. assumption.
    }
    {
      
      intros.
      specialize (IHtctxR p q). 
      destruct IHtctxR as [IH_comm  IH];destruct IH as [IH_recv IH_sendv].
      subst.
      specialize (IH_sendv s (eq_refl (lsend p q (Some s))) H).
      destruct IH_sendv. exists x.
      rewrite MF.find_m in H2. exact H2. reflexivity. apply MF.Equal_equiv. assumption.
    }
  }
Qed.  


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

Inductive safe (R: tctx -> Prop): tctx -> Prop :=
  | sasr  : forall p q s s' c, tctxRE (lsend p q (Some s)) c -> tctxRE (lrecv q p (Some s')) c ->
                               tctxRE (lcomm p q) c -> safe R c
  | saimpl:  forall p q c c', R c -> tctxRF (lcomm p q) c c' -> safe R c'.

Definition safeC c := paco1 safe bot1 c.
