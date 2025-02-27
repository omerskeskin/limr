From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From LIMR Require Import src.expressions src.header type.local type.lcontext.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations.
Import ListNotations. 
Print ltt.

Open Scope string_scope.
Definition prt_p:="p".
Definition prt_q:="q".
Definition prt_r:="r".
Check [Some prt_p].
Check ltt_send.

Check (sint,ltt_end).
CoFixpoint T_p := ltt_send prt_q [Some (sint,T_p); Some (sint,ltt_end)].
CoFixpoint T_q := ltt_recv prt_p [Some (sint,T_q); Some (sint, ltt_send prt_r [Some (sint,ltt_end)])].
CoFixpoint T_r := ltt_recv prt_q [Some (sint,ltt_end)].

Definition gamma_lst := [(prt_p,T_p); (prt_q,T_q); (prt_r,T_r)].
Theorem no_dup_gamma : NoDup (map fst gamma_lst).
Proof.
    constructor.
    {
        simpl. unfold not. intros. destruct H.
        inversion H.
        destruct H. inversion H. auto. 
    }
    {
        constructor. simpl. unfold not. intros. destruct H. inversion H. auto. 
        constructor. auto. constructor.
    }
Qed.

Ltac triv_app_rvar rv x y H:= apply (rv x _ y  _ _);
simpl; try intro; repeat (try destruct H; try easy).

Definition gamma := mkCt gamma_lst no_dup_gamma.

Lemma red_1 : tctxR (gamma_lst)  (lsend prt_p prt_q (Some sint)) (gamma_lst).
Proof.
    triv_app_rvar RvarO [(prt_p, T_p); (prt_q, T_q)] [(prt_p, T_p); (prt_q, T_q)] H. 
    triv_app_rvar RvarO [(prt_p, T_p)] [(prt_p, T_p)]  H. 
    rewrite (ltt_eq T_p).
    apply Rsend with (n:=0).
    easy. fold T_p.
    rewrite <- (ltt_eq T_p).
    simpl. reflexivity.
Qed.

Lemma red_2 : tctxR (gamma_lst)  (lrecv prt_q prt_p (Some sint)) (gamma_lst).
Proof.
   triv_app_rvar RvarO [(prt_p, T_p); (prt_q, T_q)] [(prt_p, T_p); (prt_q, T_q)] H.
   triv_app_rvar RvarI [(prt_q, T_q)] [(prt_q, T_q)] H.
   rewrite (ltt_eq T_q).
   apply Rrecv with (n:=0).
   easy. fold T_q. 
   rewrite <- (ltt_eq T_q). reflexivity.
Qed.

Lemma red_3 : tctxR (gamma_lst)  (lcomm prt_p prt_q) (gamma_lst).
Proof.
   triv_app_rvar RvarO [(prt_p, T_p); (prt_q, T_q)] [(prt_p, T_p); (prt_q, T_q)] H.
   
   apply (Rcomm prt_p prt_q [(prt_p,T_p)] [(prt_p,T_p)] [(prt_q,T_q)] [(prt_q,T_q)] sint sint).
   easy.
   {
    rewrite (ltt_eq T_p).
    apply Rsend with (n:=0). easy. fold T_p. 
    rewrite <- (ltt_eq T_p). reflexivity. 
   }
   {
    rewrite (ltt_eq T_q).
    apply Rrecv with (n:=0). easy. fold T_q. 
    rewrite <- (ltt_eq T_q). reflexivity.
   }
   constructor.
Qed.

Lemma red_4 : tctxR (gamma_lst) (lrecv prt_r prt_q (Some sint)) [(prt_p,T_p);(prt_q,T_q);(prt_r,ltt_end)].
Proof.
    triv_app_rvar RvarI [(prt_q,T_q);(prt_r,T_r)] [(prt_q,T_q);(prt_r,ltt_end)] H.
    triv_app_rvar RvarI [(prt_r,T_r)] [(prt_r,ltt_end)] H.
    rewrite (ltt_eq T_r). simpl.
    apply Rrecv with (n:=0). easy. reflexivity.
Qed.

CoFixpoint inf_pq_path := cocons (gamma_lst,(lcomm prt_p prt_q)) inf_pq_path.

Theorem inf_pq_path_fair : fair_gfp inf_pq_path.
Proof.
    red.
    pcofix CIH.
    rewrite (coseq_eq inf_pq_path). simpl.
    pfold.
    constructor.
    constructor.
Admitted.