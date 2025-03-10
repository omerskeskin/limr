From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From LIMR Require Import src.expressions src.header type.local type.lcontext type.path_props .
Require Import List String Coq.Arith.PeanoNat Morphisms Relations.
Import ListNotations. 
Print ltt.

Open Scope string_scope.
Definition prt_p:=0.
Definition prt_q:=1.
Definition prt_r:=2.

CoFixpoint T_p := ltt_send prt_q [Some (sint,T_p); Some (sint,ltt_end)].
CoFixpoint T_q := ltt_recv prt_p [Some (sint,T_q); Some (sint, ltt_send prt_r [Some (sint,ltt_end)])].
Definition T_r := ltt_recv prt_q [Some (sint,ltt_end)].

Definition gamma := M.add prt_p T_p (M.add prt_q T_q (M.add prt_r T_r M.empty)).

Lemma red_1 : tctxR gamma (lsend prt_p prt_q (Some sint)) gamma.
Proof.
    set (gmp:=(M.add prt_q T_q (M.add prt_r T_r (M.add prt_p T_p M.empty)))).
    assert (H_perm:M.Equal gamma gmp).
    {
        unfold gamma.
        apply MF.add_add_2 with (x:=prt_p) (x':=prt_q). easy.
    }
    apply Rstruct with (g1':=gmp) (g2':=gmp); try assumption.
    apply RvarI.
    {
        apply RvarI; try (unfold M.mem;reflexivity).
        rewrite (ltt_eq T_p).
        apply Rsend with (n:=0). easy. fold T_p. rewrite <- (ltt_eq T_p). reflexivity. 
    }
    {
        unfold M.mem.
        reflexivity.
    }
Qed.
Lemma red_2 : tctxR gamma  (lrecv prt_q prt_p (Some sint)) (gamma).
Proof.
    set (gmp:=(M.add prt_p T_p (M.add prt_r T_r (M.add prt_q T_q M.empty)))).
    assert (H_perm:M.Equal gamma gmp). easy.
    apply Rstruct with (g1':=gmp) (g2':=gmp); try assumption.
    apply RvarI.
    {
        apply RvarI; try (unfold M.mem;reflexivity).
        rewrite (ltt_eq T_q).
        apply Rrecv with (n:=0). easy. fold T_p. rewrite <- (ltt_eq T_q). reflexivity. 
    }
    {
        unfold M.mem.
        reflexivity.
    }
Qed.

Lemma red_3 : tctxR gamma  (lcomm prt_p prt_q) gamma.
Proof.
    set (gmp:=(M.add prt_r T_r (M.add prt_p T_p (M.add prt_q T_q M.empty)))).
    assert (H_perm:M.Equal gamma gmp). easy.
    apply Rstruct with (g1':=gmp) (g2':=gmp); try assumption.
    set (p_only:=(M.add prt_p T_p M.empty)).
    set (q_only:=(M.add prt_q T_q M.empty)).
    assert(H_disj:MF.Disjoint p_only q_only).
    {
        unfold MF.Disjoint. unfold not.
        intros.
        destruct H.
        apply MF.add_in_iff in H.
        destruct H.
        {
            subst. apply MF.in_find in H0.
            unfold M.find in H0. simpl in H0. easy.
        }
        {
            apply MF.not_in_empty in H. assumption.
        }
    }
    assert(p_trans:tctxR p_only (lsend prt_p prt_q (Some sint)) p_only).
    {
        unfold p_only.
        rewrite (ltt_eq T_p).
        apply Rsend with (n:=0). easy. fold T_p.
        rewrite <- (ltt_eq T_p). reflexivity.
    }
    
    assert(q_trans:tctxR q_only (lrecv prt_q prt_p (Some sint)) q_only).
    {
        unfold q_only.
        rewrite (ltt_eq T_q).
        apply Rrecv with (n:=0). easy. fold T_p.
        rewrite <- (ltt_eq T_q). reflexivity.
    }
    assert(H_eqn: M.Equal (disj_merge p_only q_only H_disj) (M.add prt_p T_p (M.add prt_q T_q M.empty))).
    {
        unfold M.Equal.
        intros.
        unfold disj_merge.
        rewrite MF.merge_spec1mn; try easy.
        unfold p_only. unfold q_only.
        do 4 rewrite MF.add_o.
        Search M.find M.empty.
        rewrite M.empty_spec.
        destruct (Nat.eq_dec prt_p y); destruct (Nat.eq_dec prt_q y); try (simpl; easy).
        subst. discriminate.
    }
    apply RvarI; try (unfold M.mem; reflexivity).
    Search MF.Disjoint.
    apply Rstruct with (g1':=disj_merge p_only q_only H_disj) (g2':=disj_merge p_only q_only H_disj).
    apply Rcomm with (g1:=p_only) (g1':=p_only) (g2:=q_only) (g2':=q_only) (H1:= H_disj) (H2:=H_disj) (s:=sint) (s':=sint); try easy.
    apply srefl.
    apply MF.Equal_equiv. assumption.
    apply MF.Equal_equiv. assumption.
Qed.

Lemma red_4 : tctxR gamma (lrecv prt_r prt_q (Some sint)) (M.add prt_p  T_p (M.add prt_q T_q (M.add prt_r ltt_end M.empty))).
Proof.
    apply RvarI.
    apply RvarI.
    rewrite (ltt_eq T_r). simpl.
    apply Rrecv with (n:=0). easy. simpl. reflexivity. 1-2:unfold M.mem. 1-2:reflexivity.
Qed.

CoFixpoint inf_pq_path := cocons (gamma,(lcomm prt_p prt_q)) inf_pq_path.

Theorem inf_pq_path_fair : fairness inf_pq_path.
Proof.
    red.
    pcofix CIH.
    rewrite (coseq_eq inf_pq_path). simpl.
    pfold.
    constructor.
    unfold fairPath.
    intros.
    assert(H_p:p=prt_p).
    {   
        destruct (Nat.eq_dec p prt_p). assumption.
        simpl in H.
        inversion H. subst. 
        specialize (tctx_lcomm_inv_1 gamma p q x (lcomm p q)).
        intros.
        apply H1 in H0.
        destruct H0 as [H_comm  Hh];destruct Hh as [H_recv  Hsend].
        assert(H_eq: lcomm p q =lcomm p q). reflexivity.
        apply  H_comm in H_eq.
        destruct H_eq.
        destruct H0.
        destruct (Nat.eq_dec p prt_p);
        destruct (Nat.eq_dec p prt_q);
        destruct (Nat.eq_dec p prt_r); try (subst; easy).
        {
            pose proof H0 as H_t.
            unfold gamma in H0.
            clear H2.
            rewrite M.add_spec2 in H0; try easy.
            rewrite M.add_spec2 in H0.
            rewrite M.add_spec2 in H0.
            rewrite M.empty_spec in H0. discriminate H0. easy.
            unfold gamma in H_t. subst. 
            rewrite M.add_spec2 in H_t.
            rewrite M.add_spec1 in H_t.
            rewrite (ltt_eq T_q) in H_t.
            simpl in H_t.
            discriminate H_t. try easy.
        }
        {
            unfold gamma in H0.
            rewrite M.add_spec2 in H0.
            rewrite M.add_spec2 in H0.
            rewrite M.add_spec2 in H0.
            rewrite M.empty_spec in H0. discriminate H0. 
            easy. easy. easy. 
        }
    }
    assert(H_q:q=prt_q).
    {
        destruct (Nat.eq_dec q prt_q). assumption.
        simpl in H.
        inversion H.
        subst.
        specialize (tctx_lcomm_inv_1 gamma prt_p q x (lcomm prt_p q)).
        intros.
        apply H1 in H0.
        destruct H0 as [H_comm  Hh];destruct Hh as [H_recv  Hsend].
        assert(H_eq: lcomm prt_p q =lcomm prt_p q). reflexivity.
        apply  H_comm in H_eq.
        destruct H_eq.
        destruct H2.
        destruct (Nat.eq_dec q prt_p);
        destruct (Nat.eq_dec q prt_q);
        destruct (Nat.eq_dec q prt_r); try (subst; easy).
        {
            pose proof H2 as H_t.
            unfold gamma in H2.
            rewrite M.add_spec2 in H2; try easy.
            rewrite M.add_spec2 in H2.
            rewrite M.add_spec2 in H2.
            rewrite M.empty_spec in H2. discriminate H2. easy. easy.
            subst.
            unfold gamma in H_t. 
            rewrite M.add_spec1 in H_t.
            rewrite (ltt_eq T_p) in H_t.
            simpl in H_t. discriminate H_t.
        }
        {
            unfold gamma in H2.
            rewrite M.add_spec2 in H2.
            rewrite M.add_spec2 in H2.
            rewrite M.add_spec2 in H2.
            rewrite M.empty_spec in H2. discriminate H2. 
            easy. easy. easy. 
        }
    }
    apply evh. subst. simpl. easy.
    right. assumption.
Qed.

Theorem inf_pq_path_fairA: fairness inf_pq_path.
Proof.
    red.
    pcofix CIH.
    rewrite (coseq_eq inf_pq_path). simpl.
    pfold.
    constructor.
    unfold fairPath.
    intros.
    simpl in H.
    constructor.
    simpl. easy.
    right.
    easy.
Qed.
    
