Require Export A_2_1.

Module A2_2.

(* 2.2 收敛数列的性质 *)


(* 定理2.2: 唯一性 *)
Theorem Theorem2_2 : ∀ (x : Seq) (a b : R),
  limit_seq x a -> limit_seq x b -> a = b.
Proof.
  intros x a b H0 H1. apply NNPP. intro H2. apply EqualLimit in H0 as H3.
  unfold limit_seq' in H3. destruct H3 as [H3 H4].
  assert (H5 : Abs[b-a]/2 > 0).
  { assert (I1 : a > b \/ a < b).
    { destruct (total_order_T a b) as [[I2 | I2] | I2]; auto.
      exfalso; auto. }
    destruct I1 as [I1 | I1].
    - apply Rplus_lt_compat_l with (r := -a) in I1 as I2.
      rewrite Rplus_comm in I2. pattern (-a + a) at 1 in I2.
      rewrite Rplus_comm in I2. rewrite Rplus_opp_r in I2.
      apply Abs_lt in I2 as I3. rewrite Ropp_plus_distr in I3.
      rewrite Ropp_involutive in I3.
      apply Rplus_lt_compat_l with (r := -b) in I1 as I4.
      rewrite Rplus_comm in I4. rewrite Rplus_opp_r in I4.
      unfold Rminus. rewrite I3. assert (I5 : 0 < 2).
      { apply Rlt_0_2. }
      apply Rinv_0_lt_compat in I5. unfold Rdiv.
      apply Rmult_lt_compat_l with (r := /2) in I4; auto.
      rewrite Rmult_0_r in I4. rewrite Rmult_comm in I4. auto.
    - apply Rplus_lt_compat_l with (r := -a) in I1 as I2.
      rewrite Rplus_comm in I2. pattern (-a + b) at 1 in I2.
      rewrite Rplus_comm in I2. rewrite Rplus_opp_r in I2.
      unfold Rminus. assert (I3 : Abs[b + -a] = b + -a).
      { apply Abs_ge. left; auto. }
      rewrite I3. assert (I4 : /2 > 0).
      { apply Rinv_0_lt_compat. apply Rlt_0_2. }
      apply Rmult_lt_compat_l with (r := /2) in I2; auto.
      rewrite Rmult_0_r in I2. rewrite Rmult_comm in I2.
      unfold Rdiv. auto. }
  apply H4 in H5 as H6.
  assert (H7 : \{ λ u, x [u] ∈ (Neighbor b (Abs [b - a] / 2)) \} ⊂
    \{ λ u, x [u] ∉ (Neighbor a (Abs [b - a] / 2)) \}).
  { intros z I1. applyAxiomII I1. apply <- AxiomII.
    applyAxiomII I1. intro I2. applyAxiomII I2.
    apply Abs_R in I1. apply Abs_R in I2.
    destruct I1 as [I1 I3]. destruct I2 as [I2 I4].
    assert (I5 : b-a>=0 \/ b-a<0).
    { destruct (total_order_T (b-a) 0) as [[I5 | I5] | I5].
      - right; auto.
      - left; right; auto.
      - left; left; auto. }
    assert (I6 : Abs[b-a] = a-b \/ Abs[b-a] = b-a).
    { destruct I5 as [I5 | I5].
      - right. apply Abs_ge. auto.
      - left. apply Abs_lt in I5. rewrite I5. apply Ropp_minus_distr. }
    destruct I6 as [I6 | I6].
    - rewrite I6 in *. unfold Rminus in *.
      apply Rplus_lt_compat_r with (r := b) in I3.
      rewrite Rplus_assoc in I3. rewrite Rplus_opp_l in I3.
      rewrite Rplus_0_r in I3. unfold Rdiv in *.
      assert (I7 : b = 2 * b * /2).
      { assert ( I7 : b * 2 = 2 * b).
        { apply Rmult_comm. }
        apply Rmult_eq_compat_r with (r := /2) in I7.
        assert (I8 : 2 <> 0).
        { apply Rgt_not_eq. apply Rlt_0_2. }
        rewrite Rinv_r_simpl_l in I7; auto. }
      pattern b at 2 in I3. rewrite I7 in I3.
      rewrite <- Rmult_plus_distr_r in I3.
      assert (I8 : a + -b + 2 * b = a + b).
      { assert (J1 : a + -b + 2 * b = a + (-b + 2 * b)).
        { apply Rplus_assoc. }
        rewrite J1. apply Rplus_eq_compat_l.
        assert (J2 : 2 * b = b + b).
        { apply double. }
        apply Rplus_eq_compat_l with (r := -b) in J2.
        rewrite <- Rplus_assoc in J2.
        rewrite Rplus_opp_l in J2. rewrite Rplus_0_l in J2. auto. }
      rewrite I8 in I3.
      apply Rplus_lt_compat_r with (r := a) in I2.
      pattern (x [z] + - a + a) at 1 in I2. rewrite Rplus_assoc in I2.
      rewrite Rplus_opp_l in I2. rewrite Rplus_0_r in I2.
      assert (I9 : - ((a + - b) * / 2) + a = (a + b) * / 2).
      { assert (I9 : a = 2 * a * /2).
        { assert ( I9 : a * 2 = 2 * a).
          { apply Rmult_comm. }
          apply Rmult_eq_compat_r with (r := /2) in I9.
          assert (I10 : 2 <> 0).
          { apply Rgt_not_eq. apply Rlt_0_2. }
          rewrite Rinv_r_simpl_l in I9; auto. }
        rewrite Ropp_mult_distr_l. pattern a at 2.
        rewrite I9. rewrite <- Rmult_plus_distr_r.
        rewrite Ropp_plus_distr. rewrite Ropp_involutive.
        rewrite Rplus_assoc. pattern (b + 2 * a) at 1.
        rewrite Rplus_comm. rewrite <- Rplus_assoc.
        assert (I10 : - a + 2 * a = a).
        { assert (J1 : 2 * a = a + a).
          { apply double. }
          apply Rplus_eq_compat_l with (r := -a) in J1.
          rewrite <- Rplus_assoc in J1.
          rewrite Rplus_opp_l in J1. rewrite Rplus_0_l in J1. auto. }
        rewrite I10. auto. }
      rewrite I9 in I2. apply Rlt_asym in I3. auto.
    - rewrite I6 in *. unfold Rminus in *. unfold Rdiv in *.
      apply Rplus_lt_compat_r with (r := b) in I1.
      pattern (x [z] + - b + b) at 1 in I1. rewrite Rplus_assoc in I1.
      rewrite Rplus_opp_l in I1. rewrite Rplus_0_r in I1.
      assert (I9 : - ((b + - a) * / 2) + b = (b + a) * / 2).
      { assert (I9 : b = 2 * b * /2).
        { assert ( I9 : b * 2 = 2 * b).
          { apply Rmult_comm. }
          apply Rmult_eq_compat_r with (r := /2) in I9.
          assert (I10 : 2 <> 0).
          { apply Rgt_not_eq. apply Rlt_0_2. }
          rewrite Rinv_r_simpl_l in I9; auto. }
        rewrite Ropp_mult_distr_l. pattern b at 2.
        rewrite I9. rewrite <- Rmult_plus_distr_r.
        rewrite Ropp_plus_distr. rewrite Ropp_involutive.
        rewrite Rplus_assoc. pattern (a + 2 * b) at 1.
        rewrite Rplus_comm. rewrite <- Rplus_assoc.
        assert (I10 : - b + 2 * b = b).
        { assert (J1 : 2 * b = b + b).
          { apply double. }
          apply Rplus_eq_compat_l with (r := -b) in J1.
          rewrite <- Rplus_assoc in J1.
          rewrite Rplus_opp_l in J1. rewrite Rplus_0_l in J1. auto. }
        rewrite I10. auto. }
      rewrite I9 in I1.
      apply Rplus_lt_compat_r with (r := a) in I4.
      rewrite Rplus_assoc in I4. rewrite Rplus_opp_l in I4.
      rewrite Rplus_0_r in I4.
      assert (I7 : a = 2 * a * /2).
      { assert ( I7 : a * 2 = 2 * a).
        { apply Rmult_comm. }
        apply Rmult_eq_compat_r with (r := /2) in I7.
        assert (I8 : 2 <> 0).
        { apply Rgt_not_eq. apply Rlt_0_2. }
        rewrite Rinv_r_simpl_l in I7; auto. }
      pattern a at 2 in I4. rewrite I7 in I4.
      rewrite <- Rmult_plus_distr_r in I4.
      assert (I8 : b + - a + 2 * a = b + a).
      { assert (J1 : b + - a + 2 * a = b + (-a + 2 * a)).
        { apply Rplus_assoc. }
        rewrite J1. apply Rplus_eq_compat_l.
        assert (J2 : 2 * a = a + a).
        { apply double. }
        apply Rplus_eq_compat_l with (r := -a) in J2.
        rewrite <- Rplus_assoc in J2.
        rewrite Rplus_opp_l in J2. rewrite Rplus_0_l in J2. auto. }
      rewrite I8 in I4. apply Rlt_asym in I4. auto. }
  apply SubSetFinite_N in H7 as H8; auto.
  unfold limit_seq in H1. destruct H1 as [H1 H10]. apply H10 in H5 as H11.
  destruct H8 as [H8 | H8].
  - apply finite_maxN in H8 as H9. destruct H9 as [N1 H9].
    destruct H11 as [N2 H11].
    unfold maxN in H9. destruct H9 as [H9 H12]. applyAxiomII H9.
    destruct (Nat.le_gt_cases N1 N2) as [I1 | I1].
    + apply le_lt_n_Sm in I1 as I2. assert (I3 : ((S N2) > N2)%nat).
      { apply gt_Sn_n. }
      apply H11 in I3 as I4.
      assert (I5 : (S N2) ∈ \{ λ u, x [u] ∈ (Neighbor b (Abs [b - a] / 2)) \}).
      { apply <- AxiomII. apply <- AxiomII. auto. }
      apply H12 in I5 as I6. apply le_not_gt in I6. auto.
    + assert (I2 : ((S N1) > N2)%nat).
      { apply le_gt_S. apply Nat.lt_le_incl. auto. }
      apply H11 in I2 as I3.
      assert (I4 : (S N1) ∈ \{ λ u, x [u] ∈ (Neighbor b (Abs [b - a] / 2)) \}).
      { apply <- AxiomII. apply <- AxiomII. auto. }
      apply H12 in I4. assert (I5 : (N1 < (S N1))%nat).
      { apply Nat.lt_succ_diag_r. }
      apply le_not_gt in I4. auto.
  - destruct H11 as [N H11]. assert (H12 : ((S N) > N)%nat).
    { apply gt_Sn_n. }
    apply H11 in H12 as H13.
    assert (H14 : (S N) ∈ \{ λ u, x [u] ∈ (Neighbor b (Abs [b - a] / 2)) \}).
    { apply <- AxiomII. apply <- AxiomII. auto. }
    rewrite H8 in H14. applyAxiomII H14. auto.
Qed.

Theorem lim_a : ∀ (x : Seq) (a : R), limit_seq x a -> lim x = a.
Proof.
  intros x a H0. assert (H1 : lim x ∈ \{ λ a, limit_seq x a \}).
  { assert (H1 : NotEmpty \{ λ a, limit_seq x a \}).
    { unfold NotEmpty. exists a. apply <- AxiomII. auto. }
    apply AxiomcR in H1. apply H1. }
  applyAxiomII H1. apply Theorem2_2 with (x := x); auto.
Qed.

(* 定理2.3: 有界性 *)
Theorem Theorem2_3' : ∀ (x : Seq), Convergence x
    -> (∃ M, ∀ n, Abs[x[n]] <= M).
Proof.
  intros x H0. unfold Convergence in H0. destruct H0 as [a H0].
  unfold limit_seq in H0. destruct H0 as [H0 H1]. assert (H2 : 1 > 0).
  { apply Rlt_0_1. }
  apply H1 in H2 as H3. destruct H3 as [N H3].
  assert (H4 : ∀ N2, ∃ M1, ∀ n : nat, (n <= N2)%nat -> Abs[x[n]] <= M1).
  { intro N2. induction N2 as [|N2 H4].
    - exists (Abs[x[0%nat]]). intros n I1. apply le_n_0_eq in I1 as I2.
      rewrite <- I2. right; auto.
    - destruct H4 as [M1 H4]. destruct (Rge_lt M1 (Abs[x[S N2]])) as [I1 | I1].
      + exists M1. intros n I2. apply Nat.le_succ_r in I2.
        destruct I2 as [I2 | I2]; auto. rewrite I2. destruct I1 as [I1 | I1];
        [left | right]; auto.
      + exists (Abs[x[S N2]]). intros n I2. apply Nat.le_succ_r in I2.
        destruct I2 as [I2 | I2].
        * apply H4 in I2. left. destruct I2 as [I2 | I2].
          -- apply Rlt_trans with (r2 := M1); auto.
          -- rewrite I2; auto.
        * rewrite I2. right; auto. }
  assert (H5 : ∃ M1, ∀ n : nat, (n <= N)%nat -> Abs[x[n]] <= M1). auto.
  destruct H5 as [M1 H5]. destruct (Rge_lt a 0) as [H6 | H6].
  - assert (H7 : ∀n : nat,(n > N)%nat -> Abs [x[n]] < 1 + a).
    { intros n I1. apply H3 in I1. apply Abs_R in I1 as I2.
      destruct I2 as [I2 I3]. apply Abs_R.
      apply Rplus_lt_compat_r with (r := a) in I3. unfold Rminus in I3.
      rewrite Rplus_assoc in I3. rewrite Rplus_opp_l in I3.
      rewrite Rplus_0_r in I3. split; auto.
      apply Rplus_lt_compat_r with (r := a) in I2. unfold Rminus in I2.
      rewrite Rplus_assoc in I2. rewrite Rplus_opp_l in I2.
      rewrite Rplus_0_r in I2. rewrite Ropp_plus_distr.
      apply Rge_le in H6 as I4. apply Ropp_0_le_ge_contravar in I4 as I5.
      apply Rge_le in I5 as I6.
      assert (I7 : -a <= a).
      { apply Rle_trans with (r2 := 0); auto. }
      apply Rplus_le_compat_l with (r := -(1)) in I7.
      destruct I7 as [I7 | I7].
      - apply Rlt_trans with (r2 := - (1) + a); auto.
      - rewrite I7. auto. }
    destruct (Rge_lt M1 (1 + a)) as [H8 | H8].
    + exists M1. intro n. destruct (Nat.le_gt_cases n N) as [H9 | H9]; auto.
      apply H7 in H9. destruct H8 as [H8 | H8].
      * left. apply Rlt_trans with (r2 := 1 + a); auto.
      * rewrite H8. left; auto.
    + exists (1 + a). intro n. destruct (Nat.le_gt_cases n N) as [H9 | H9].
      * apply H5 in H9. left. destruct H9 as [H9 | H9].
        -- apply Rlt_trans with (r2 := M1); auto.
        -- rewrite H9; auto.
      * apply H7 in H9. left; auto.
  - assert (H7 : ∀n : nat,(n > N)%nat -> Abs [x[n]] < 1 - a).
    { intros n I1. apply H3 in I1. apply Abs_R in I1 as I2.
      destruct I2 as [I2 I3]. apply Abs_R.
      apply Rplus_lt_compat_r with (r := a) in I2. unfold Rminus in I2.
      rewrite Rplus_assoc in I2. rewrite Rplus_opp_l in I2.
      rewrite Rplus_0_r in I2. unfold Rminus. rewrite Ropp_plus_distr.
      rewrite Ropp_involutive. split; auto.
      apply Rplus_lt_compat_r with (r := a) in I3. unfold Rminus in I3.
      rewrite Rplus_assoc in I3. rewrite Rplus_opp_l in I3.
      rewrite Rplus_0_r in I3. apply Ropp_gt_lt_0_contravar in H6 as I4.
      assert (I5 : a < -a).
      { apply Rlt_trans with (r2 := 0); auto. }
      apply Rplus_lt_compat_l with (r := 1) in I5.
      apply Rlt_trans with (r2 := 1 + a); auto. }
    destruct (Rge_lt M1 (1 - a)) as [H8 | H8].
    + exists M1. intro n. destruct (Nat.le_gt_cases n N) as [H9 | H9]; auto.
      apply H7 in H9. destruct H8 as [H8 | H8].
      * left. apply Rlt_trans with (r2 := 1 - a); auto.
      * rewrite H8. left; auto.
    + exists (1 - a). intro n. destruct (Nat.le_gt_cases n N) as [H9 | H9].
      * apply H5 in H9. left. destruct H9 as [H9 | H9].
        -- apply Rlt_trans with (r2 := M1); auto.
        -- rewrite H9; auto.
      * apply H7 in H9. left; auto.
Qed.

Theorem Theorem2_3 : ∀ (x : Seq), Convergence x ->
  (∃ M, M > 0 /\ (∀ n, Abs[x[n]] <= M)).
Proof.
  intros x H0. apply Theorem2_3' in H0 as H1. destruct H1 as [M H1].
  assert (H2 : M >= 0).
  { generalize (H1 0%nat). intro H2. apply Rle_ge.
    apply Rle_trans with (r2 := Abs [x [0%nat]]); auto. apply Rge_le.
    apply Abs_Rge0. }
  destruct H2 as [H2 | H2].
  - exists M. split; auto.
  - exists (M+1). split.
    + rewrite H2. rewrite Rplus_0_l. apply Rlt_0_1.
    + intro n. generalize (H1 n). intro H3.
      apply Rle_trans with (r2 := M); auto.
      left. apply Rlt_n_Sn.
Qed.

(* 定理2.4: 保号性 *)
Theorem Theorem2_4_1 : ∀ (x : Seq) (a : R), limit_seq x a -> a > 0 ->
  (∀ a' : R, a' ∈ \(0, a\) -> (∃ N, (∀ n, (n > N)%nat -> x[n] > a'))).
Proof.
  intros x a H0 H1 a' H2. applyAxiomII H2. destruct H2 as [H2 H3].
  unfold limit_seq in H0. destruct H0 as [H0 H4].
  assert (H5 : a - a' > 0).
  { apply Rgt_minus. auto. }
  apply H4 in H5 as H6. destruct H6 as [N H6]. exists N. intros n H7.
  apply H6 in H7 as H8. apply Abs_R in H8. destruct H8 as [H8 H9].
  rewrite Ropp_minus_distr in H8. apply Rplus_lt_reg_r with (r := -a).
  apply H8.
Qed.

Theorem Theorem2_4_2 : ∀ (x : Seq) (a : R), limit_seq x a -> a < 0 ->
  (∀ a' : R, a' ∈ \(a, 0\) -> (∃ N, (∀ n, (n > N)%nat -> x[n] < a'))).
Proof.
  intros x a H0 H1 a' H2. applyAxiomII H2. destruct H2 as [H2 H3].
  unfold limit_seq in H0. destruct H0 as [H0 H4].
  assert (H5 : a' - a > 0).
  { apply Rgt_minus. auto. }
  apply H4 in H5 as H6. destruct H6 as [N H6]. exists N. intros n H7.
  apply H6 in H7 as H8. apply Abs_R in H8. destruct H8 as [H8 H9].
  apply Rplus_lt_reg_r with (r := -a). auto.
Qed.

Lemma Max_nat_3 : ∀ (N0 N1 N2 : nat), ∃ N, (N > N0 /\ N > N1 /\ N > N2)%nat.
Proof.
  intros N0 N1 N2.
  destruct (Nat.le_gt_cases N0 N1) as [H6 | H6].
  - destruct (Nat.le_gt_cases N1 N2) as [H7 | H7].
    + exists (S N2). generalize (gt_Sn_n N2).
      intro H8. assert (H9 : ((S N2) > N1)%nat).
      { apply Nat.le_lt_trans with (m := N2); auto. }
      repeat split; auto. apply Nat.le_lt_trans with (m := N1); auto.
    + exists (S N1). generalize (gt_Sn_n N1). intro H8. repeat split; auto.
      apply Nat.le_lt_trans with (m := N1); auto.
  - destruct (Nat.le_gt_cases N0 N2) as [H7 | H7].
    + exists (S N2). generalize (gt_Sn_n N2).
      intro H8. assert (H9 : ((S N2) > N0)%nat).
      { apply Nat.le_lt_trans with (m := N2); auto. }
      repeat split; auto. apply Nat.lt_trans with (m := N0); auto.
    + exists (S N0). generalize (gt_Sn_n N0). intro H8.
      repeat split; auto.
Qed.

Lemma Max_nat_2 : ∀ (N0 N1 : nat), ∃ N, (N > N0 /\ N > N1)%nat.
Proof.
  intros N0 N1. generalize (Max_nat_3 N0 N1 N1). intro H0.
  destruct H0 as [N [H0 [H1 H2]]]. exists N. split; auto.
Qed.


(* 定理2.5: 保不等式性 *)
Theorem Theorem2_5 : ∀ (x : Seq) (y : Seq), Convergence x -> Convergence y ->
  (∃ N0 : nat, ∀ n, (n > N0)%nat -> x[n] <= y[n]) -> lim x <= lim y.
Proof.
  intros x y H0 H1 H2. destruct H2 as [N0 H2].
  destruct H0 as [a H0]. destruct H1 as [b H1].
  assert (H3 : ∀ ε, ε > 0 -> a < b + (ε + ε)).
  { intros ε H3. apply H0 in H3 as H4. destruct H4 as [N1 H4].
    apply H1 in H3 as H5. destruct H5 as [N2 H5].
    destruct (Max_nat_3 N0 N1 N2) as [N [H6 [H7 H8]]].
    apply H2 in H6. apply H4 in H7.
    apply H5 in H8. apply Abs_R in H7. apply Abs_R in H8.
    destruct H7 as [H7 H9]. destruct H8 as [H8 H10].
    apply Rplus_lt_compat_r with (r := a) in H7.
    unfold Rminus in H7. rewrite Rplus_assoc in H7. rewrite Rplus_opp_l in H7.
    rewrite Rplus_0_r in H7. apply Rplus_lt_compat_r with (r := b) in H10.
    unfold Rminus in H10. rewrite Rplus_assoc in H10.
    rewrite Rplus_opp_l in H10. rewrite Rplus_0_r in H10.
    assert (H11 : x[N] < ε + b).
    { apply Rle_lt_trans with (r2 := y[N]); auto. }
    rewrite <- Rplus_assoc. assert (H12 : - ε + a < ε + b).
    { apply Rlt_trans with (r2 := x[N]); auto. }
    rewrite Rplus_comm in H12. pattern (ε + b) in H12.
    rewrite Rplus_comm in H12. apply Rplus_lt_compat_r with (r := ε) in H12.
    rewrite Rplus_assoc in H12. rewrite Rplus_opp_l in H12.
    rewrite Rplus_0_r in H12. auto. }
  apply lim_a in H0 as H4. apply lim_a in H1 as H5.
  rewrite H4. rewrite H5. apply NNPP. intro H6. apply Rnot_le_gt in H6 as H7.
  generalize Rlt_0_2. intro H8.
  apply Rplus_gt_compat_l with (r := a) in H7 as H9.
  generalize (double b). intro H10.
  apply Rplus_eq_compat_r with (r := -b) in H10.
  pattern (b + b + - b) in H10. rewrite Rplus_assoc in H10.
  rewrite Rplus_opp_r in H10. rewrite Rplus_0_r in H10.
  rewrite <- H10 in H9. rewrite <- (double a) in H9.
  rewrite <- Rplus_assoc in H9. pattern (a + 2 * b) in H9.
  rewrite Rplus_comm in H9. rewrite Rplus_assoc in H9.
  apply Rinv_0_lt_compat in H8 as H11.
  apply Rmult_gt_compat_r with (r := /2) in H9 as H12; auto.
  apply Rgt_not_eq in H8 as H13. rewrite Rinv_r_simpl_m in H12; auto.
  rewrite Rmult_plus_distr_r in H12. rewrite Rinv_r_simpl_m in H12; auto.
  assert (H14 : (a + - b) > 0).
  { apply Rplus_gt_compat_r with (r := -b) in H7 as H14.
    rewrite Rplus_opp_r in H14. auto. }
  assert (H15 : (a + - b) * /2 > 0).
  { apply Rmult_gt_0_compat; auto. }
  assert (H16 : (a + - b) * /2 * /2 > 0).
  { apply Rmult_gt_0_compat; auto. }
  apply H3 in H16 as H17. rewrite <- double in H17.
  rewrite <- Rmult_assoc in H17. rewrite Rinv_r_simpl_m in H17; auto.
  apply Rlt_asym in H17. auto.
Qed.

Theorem Theorem2_5_1 : ∀ (x : Seq) (x0 a : R), limit_seq x x0
  -> (∃ N0, ∀ n, (N0 < n)%nat -> a <= x[n]) -> a <= x0.
Proof.
  intros x x0 a H0 [N0 H1].
  assert (H2 : ∃ y, y = {` λ (n : nat) v, v = a `}).
  { exists ({` λ (n : nat) v, v = a `}); reflexivity. }
  destruct H2 as [y H2]. assert (H3 : IsSeq y).
  { split.
    - intros n v1 v2 I1 I2. rewrite H2 in I1; rewrite H2 in I2.
      applyAxiomII' I1; applyAxiomII' I2. rewrite I2. assumption.
    - apply AxiomI. intro n; split; intro I1.
      + apply AxiomII. reflexivity.
      + apply AxiomII. exists a. rewrite H2. apply AxiomII'.
        reflexivity. }
  assert (H7 : ∀ n, y[n] = a).
  { intro n. apply f_x; try apply H3. rewrite H2. apply AxiomII'.
    reflexivity. }
  assert (H4 : limit_seq y a).
  { split; auto. intros ε I1. exists 0%nat. intros n I2.
    rewrite H7. unfold Rminus. rewrite Rplus_opp_r.
    rewrite Abs_ge; lra. }
  apply lim_a in H0 as H5. apply lim_a in H4 as H6.
  rewrite <- H5; rewrite <- H6. apply Theorem2_5.
  - exists a. assumption.
  - exists x0. assumption.
  - exists N0. intros n H8. rewrite H7. apply H1. assumption.
Qed.

Theorem Theorem2_5_2 : ∀ (x : Seq) (x0 a : R), limit_seq x x0
  -> (∃ N0, ∀ n, (N0 < n)%nat -> x[n] <= a) -> x0 <= a.
Proof.
  intros x x0 a H0 [N0 H1].
  assert (H2 : ∃ y, y = {` λ (n : nat) v, v = a `}).
  { exists ({` λ (n : nat) v, v = a `}); reflexivity. }
  destruct H2 as [y H2]. assert (H3 : IsSeq y).
  { split.
    - intros n v1 v2 I1 I2. rewrite H2 in I1; rewrite H2 in I2.
      applyAxiomII' I1; applyAxiomII' I2. rewrite I2. assumption.
    - apply AxiomI. intro n; split; intro I1.
      + apply AxiomII. reflexivity.
      + apply AxiomII. exists a. rewrite H2. apply AxiomII'.
        reflexivity. }
  assert (H7 : ∀ n, y[n] = a).
  { intro n. apply f_x; try apply H3. rewrite H2. apply AxiomII'.
    reflexivity. }
  assert (H4 : limit_seq y a).
  { split; auto. intros ε I1. exists 0%nat. intros n I2.
    rewrite H7. unfold Rminus. rewrite Rplus_opp_r.
    rewrite Abs_ge; lra. }
  apply lim_a in H0 as H5. apply lim_a in H4 as H6.
  rewrite <- H5; rewrite <- H6. apply Theorem2_5.
  - exists x0. assumption.
  - exists a. assumption.
  - exists N0. intros n H8. rewrite H7. apply H1. assumption.
Qed.

(* 定理2.6 迫敛性*)
Theorem Theorem2_6 : ∀ (x y z : Seq) (a : R), limit_seq x a -> limit_seq y a ->
  IsSeq z -> (∃ N : nat, ∀ n : nat, (n > N)%nat -> x[n] <= z[n] <= y[n]) ->
  limit_seq z a.
Proof.
  intros x y z a H1 H2 H3 H4. destruct H4 as [N H4]. unfold limit_seq in *.
  split; auto. intros ε H5. destruct H1 as [H1 H6]. destruct H2 as [H2 H7].
  apply H6 in H5 as H8. apply H7 in H5 as H9.
  destruct H9 as [N2 H9]. destruct H8 as [N1 H8].
  destruct (Max_nat_3 N N1 N2) as [N0 [H10 [H11 H12]]].
  exists N0. intros n H13.
  apply gt_trans with (n := n) in H10 as H14; auto.
  apply gt_trans with (n := n) in H11 as H15; auto.
  apply gt_trans with (n := n) in H12 as H16; auto.
  apply H4 in H14 as H17. apply H9 in H16 as H19. apply H8 in H15 as H18.
  apply Abs_R. apply Abs_R in H18. apply Abs_R in H19.
  destruct H17 as [H17 H20]. destruct H18 as [H18 H21].
  apply Rplus_lt_compat_r with (r := a) in H18. destruct H19 as [H19 H22].
  apply Rplus_lt_compat_r with (r := a) in H22.
  unfold Rminus in *. rewrite Rplus_assoc in H18. rewrite Rplus_opp_l in H18.
  rewrite Rplus_0_r in H18. rewrite Rplus_assoc in H22.
  rewrite Rplus_opp_l in H22. rewrite Rplus_0_r in H22. split.
  - apply Rplus_lt_reg_r with (r := a). rewrite Rplus_assoc.
    rewrite Rplus_opp_l. rewrite Rplus_0_r.
    apply Rlt_le_trans with (r2 := x[n]); auto.
  - apply Rplus_lt_reg_r with (r := a). rewrite Rplus_assoc.
    rewrite Rplus_opp_l. rewrite Rplus_0_r.
    apply Rle_lt_trans with (r2 := y[n]); auto.
Qed.

(* 定理2.7 四则运算法则 *)
(* x,y是收敛数列,则 x+y 收敛,且有 lim(x+y) = limx+limy *)
Theorem Theorem2_7_1 : ∀ (x y : Seq), Convergence x -> Convergence y ->
  Convergence {` λ n v, v = x[n] + y[n] `} /\
  lim {` λ n v, v = x[n] + y[n] `} = lim x + lim y.
Proof.
  intros x y H0 H1. destruct H0 as [a H0]. destruct H1 as [b H1].
  assert (H2 : ∀ ε, ε > 0 -> (∃ N : nat, ∀ n : nat, (n > N)%nat ->
    Abs[(x[n]+y[n]) - (a+b)] < 2 * ε)).
  { intros ε H2. apply H0 in H2 as H3. destruct H3 as [N1 H3].
    apply H1 in H2 as H4. destruct H4 as [N2 H4].
    generalize (Max_nat_2 N1 N2). intro H5.
    destruct H5 as [N [H5 H6]]. exists N. intros n H7.
    apply gt_trans with (n := n) in H5 as H8; auto.
    apply gt_trans with (n := n) in H6 as H9; auto.
    apply H3 in H8 as H10. apply H4 in H9 as H11.
    assert (H12 : Abs[x [n] - a] + Abs[y [n] - b] < ε + ε).
    { apply Rplus_lt_compat; auto. }
    rewrite <- double in H12.
    assert (H13 : x [n] + y [n] - (a + b) = x[n] - a + (y[n] - b)). field.
    rewrite H13. generalize (Abs_plus_le (x[n]-a) (y[n]-b)).
    intro H14. eapply Rle_lt_trans; eauto. }
  assert (H3 : limit_seq {` λ n v, v = x[n] + y[n] `} (a+b)).
  { unfold limit_seq. assert (H3 : Function {` λ n v, v = x[n] + y[n] `}).
    { unfold Function. intros x0 y0 z0 I1 I2. applyAxiomII' I1.
      applyAxiomII' I2. rewrite I2; auto. }
    split.
    - split; auto. apply AxiomI. intro z; split; intro I1.
      + apply <- AxiomII. auto.
      + apply <- AxiomII. exists (x[z] + y[z]). apply <- AxiomII'.
        auto.
    - intros ε I1. generalize Rlt_0_2. intro I2.
      apply Rinv_0_lt_compat in I2 as I3.
      apply Rmult_gt_compat_r with (r := /2) in I1 as I4; auto.
      rewrite Rmult_0_l in I4. apply H2 in I4 as I5.
      destruct I5 as [N I5]. exists N. rewrite <- Rmult_assoc in I5.
      apply Rgt_not_eq in I2 as I6. rewrite Rinv_r_simpl_m in I5; auto.
      intros n I7.
      assert (I8 : {` λ n v, v = x[n] + y[n] `} [n] = x[n] + y[n] ).
      { apply f_x; auto. apply <- AxiomII'. auto. }
      rewrite I8. auto. }
  split.
  - exists (a+b). auto.
  - apply lim_a in H0 as H4. apply lim_a in H1 as H5.
    rewrite H4; rewrite H5. apply lim_a. auto.
Qed.

Theorem Theorem2_7_1' : ∀ (x y : Seq) (a b : R), limit_seq x a ->
  limit_seq y b -> limit_seq {` λ n v, v = x[n] + y[n] `} (a + b).
Proof.
  intros x y a b H0 H1.
  apply lim_a in H0 as H3.
  apply lim_a in H1 as H4.
  assert (H5 : Convergence x).
  { exists a; auto. }
  assert (H6 : Convergence y).
  { exists b; assumption. }
  generalize (Theorem2_7_1 x y H5 H6). intros [H7 H8].
  rewrite H3 in H8; rewrite H4 in H8.
  unfold lim in H8.
  assert (H9 : NotEmpty \{  λ c, limit_seq
    {` λ(n : nat)(v : R), v = x [n] + y [n] `} c \}).
  { unfold NotEmpty. destruct H7 as [c H7].
    exists c. apply AxiomII. assumption. }
  apply AxiomcR in H9. rewrite H8 in H9. applyAxiomII H9.
  assumption.
Qed.

(* x,y是收敛数列,则 x-y 收敛,且有 lim(x-y) = limx-limy *)
Theorem Theorem2_7_2 : ∀ (x y : Seq), Convergence x -> Convergence y ->
  Convergence {` λ n v, v = x[n] - y[n] `} /\
  lim {` λ n v, v = x[n] - y[n] `} = lim x - lim y.
Proof.
  intros x y H0 H1. assert (H2 : ∃ y', y' = {` λ n v, v = -(y[n]) `} ).
  { exists {` λ n v, v = -(y[n]) `}; auto. }
  destruct H2 as [y' H2].
  assert (H3 : IsSeq y').
  { split.
    - unfold Function. intros x0 y0 z0 I1 I2. rewrite H2 in *.
      applyAxiomII' I1. applyAxiomII' I2. rewrite I2. auto.
    - apply AxiomI. intro z; split; intro I1.
      + apply <- AxiomII. auto.
      + apply <- AxiomII. rewrite H2. exists (-y[z]). apply <- AxiomII'.
        auto. }
  assert (H4 : {` λ n v, v = x[n] - y[n] `} =
    {` λ n v, v = x[n] + y'[n] `}).
  { assert (I0 : ∀ x0, y'[x0] = -y[x0]).
    { intro x0. destruct H3 as [H3 I1]. apply f_x; auto. rewrite H2.
      apply <- AxiomII'. auto. }
    apply AxiomI. intro z; split; intro I1.
    - applyAxiomII I1. destruct I1 as [x0 [y0 [I2 I3]]]. rewrite I2 in *.
      apply <- AxiomII'. rewrite I0. auto.
    - applyAxiomII I1. destruct I1 as [x0 [y0 [I2 I3]]]. rewrite I2 in *.
      apply <- AxiomII'. rewrite I0 in I3. auto. }
  rewrite H4. generalize H1. intro H5. unfold limit_seq in H1.
  destruct H1 as [b H1]. assert (H6 : limit_seq y' (-b)).
  { split; auto. destruct H1 as [H1 I1]. intros ε I2. apply I1 in I2 as I3.
    destruct I3 as [N I3]. exists N. intros n I4.
    assert (I5 : y'[n] = -y[n]).
    { apply f_x; try apply H3. rewrite H2. apply <- AxiomII'. auto. }
    rewrite I5. assert (I6 : -y[n] - -b = -(y[n] - b)). field.
    rewrite I6. rewrite <- Abs_eq_neg. auto. }
  assert (H7 : Convergence y').
  { exists (-b). auto. }
  apply (Theorem2_7_1 x y') in H7 as H8; auto. destruct H8 as [H8 H9].
  split; auto. assert (H10 : lim y' = - lim y).
  { apply lim_a in H1 as I1. rewrite I1. apply lim_a. auto. }
  rewrite H10 in H9. auto.
Qed.

(* x,y是收敛数列,则 x*y 收敛,且有 lim(x*y) = limx*limy *)
Theorem Theorem2_7_3 : ∀ (x y : Seq), Convergence x -> Convergence y ->
  Convergence {` λ n v, v = x[n] * y[n] `} /\
  lim {` λ n v, v = x[n] * y[n] `} = lim x * lim y.
Proof.
  intros x y H0 H1. apply Theorem2_3 in H1 as H2.
  destruct H2 as [M [I1 H2]].
  destruct H0 as [a H0]. destruct H1 as [b H1].
  assert (H3 : ∀ ε, ε > 0 -> (∃ N : nat, ∀ n : nat, (n > N)%nat ->
    Abs[(x[n]*y[n]) - (a*b)] < (M + Abs[a]) * ε)).
  { intros ε H3. apply H0 in H3 as H4. destruct H4 as [N1 H4].
    apply H1 in H3 as H5. destruct H5 as [N2 H5].
    generalize (Max_nat_2 N1 N2). intro H6. destruct H6 as [N [H6 H7]].
    exists N. intros n H8.
    assert (H9 : x [n] * y [n] - a * b = (x[n] - a) * y[n] + a * (y[n] - b)).
    field. rewrite H9.
    generalize (Abs_plus_le ((x[n] - a) * y[n]) (a * (y[n] - b))). intro H10.
    apply Rle_lt_trans with (r2 :=
      Abs [(x [n] - a) * y [n]] + Abs [a * (y [n] - b)]); auto.
    repeat rewrite Abs_mult.
    assert (H11 : Abs [x [n] - a] * Abs [y [n]] < M * ε).
    { generalize (H2 n). intro H11.
      assert (H12 : (n > N1)%nat).
      { apply gt_trans with (m := N); auto. }
      apply H4 in H12 as H13. assert (H14 : 0 <= Abs[y[n]]).
      { apply Rge_le. apply Abs_Rge0. }
      assert (H15 : 0 <= Abs [x [n] - a]).
      { apply Rge_le. apply Abs_Rge0. }
      rewrite (Rmult_comm M ε). destruct H11 as [H11 | H11].
      - apply Rmult_le_0_lt_compat; auto.
      - rewrite H11. apply Rmult_lt_compat_r; auto. }
    assert (H13 : (n > N2)%nat).
    { apply gt_trans with (m := N); auto. }
    apply H5 in H13 as H14. generalize (Abs_Rge0 a). intro H15.
    assert (H16 : Abs [a] * Abs [y [n] - b] <= Abs [a] * ε).
    { destruct H15 as [H15 | H15].
      - left. apply Rmult_lt_compat_l; auto.
      - rewrite H15. repeat rewrite Rmult_0_l. right; auto. }
    rewrite Rmult_plus_distr_r. apply Rplus_lt_le_compat; auto. }
  assert (H4 : IsSeq {` λ n v, v = x[n] * y[n] `} ).
  { unfold IsSeq. split.
    - unfold Function. intros x0 y0 z0 I2 I3. applyAxiomII' I2.
      applyAxiomII' I3. rewrite I3. auto.
    - apply AxiomI. intro z; split; intro I2.
      + apply <- AxiomII. auto.
      + apply <- AxiomII. exists (x[z] * y[z]). apply <- AxiomII'. auto. }
  assert (H5 : limit_seq {` λ n v, v = x[n] * y[n] `} (a*b) ).
  { split; auto. intros ε I2. assert (I3 : (M + Abs [a]) > 0).
    { rewrite <- (Rplus_0_l 0). apply Rplus_gt_ge_compat; auto.
      apply Abs_Rge0. }
    apply Rinv_0_lt_compat in I3 as I4.
    apply Rdiv_lt_0_compat with (a := ε) in I3 as I5; auto.
    apply H3 in I5 as I6.
    assert ( I7 : (M + Abs [a]) * (ε / (M + Abs [a])) = ε).
    { field. apply Rgt_not_eq. auto. }
    rewrite I7 in I6. destruct I6 as [N I6]. exists N. intros n I8.
    apply I6 in I8 as I9.
    assert (I10 : {` λ n v, v = x[n] * y[n] `} [n] = x [n] * y [n] ).
    { apply f_x; try apply H4. apply <- AxiomII'. auto. }
    rewrite I10. auto. }
  split.
  - exists (a*b). auto.
  - apply lim_a in H0 as H6. apply lim_a in H1 as H7. rewrite H6.
    rewrite H7. apply lim_a. auto.
Qed.

(* y是收敛数列,y(n),lim y均不等于0,则lim /y[n] = /(lim y)  *)
Theorem Theorem2_7_4' : ∀ (y : Seq), Convergence y ->
  (∀ n : nat, y[n] <> 0) -> lim y <> 0 ->
  limit_seq ({` λ n v, v = /y[n] `}) (/(lim y)).
Proof.
  intros y H0 H1 H2. destruct H0 as [b H0].
  apply lim_a in H0 as H3. rewrite H3 in *.
  assert (H4 : ∃ N3 : nat, ∀ n : nat, (n > N3)%nat -> Abs[y[n]] > Abs[b] / 2).
  { apply Rdichotomy in H2 as H4. destruct H4 as [H4 | H4].
    - assert (H5 : (b / 2) ∈ \(b, 0\)).
      { apply <- AxiomII. split.
        - unfold Rdiv. pattern b at 2. rewrite <- (Rmult_1_r b).
          assert (H5 : /2 < 1).
          { assert (H6 : 2 > 1).
            { generalize Rlt_0_1. intro H5.
              apply Rplus_lt_compat_l with (r := 1) in H5.
              rewrite Rplus_0_r in H5. assert (H6 : 1+1=2). field.
              rewrite H6 in H5. auto. }
            assert (H7 : 1 = /1). field. rewrite H7.
            apply Rinv_lt_contravar; auto. rewrite Rmult_1_l. apply Rlt_0_2. }
          apply Rmult_lt_gt_compat_neg_l; auto.
        - assert (H5 : /2 > 0).
          { apply Rinv_0_lt_compat. apply Rlt_0_2. }
          unfold Rdiv. rewrite <- (Rmult_0_l (/2)).
          apply Rmult_lt_compat_r; auto. }
      assert (H6 : (∀ a' : R, a' ∈ \(b, 0\) ->
        (∃ N, (∀ n, (n > N)%nat -> y[n] < a')))).
      { apply Theorem2_4_2; auto. }
      apply H6 in H5 as H7. destruct H7 as [N H7]. exists N. intros n H8.
      assert (H9 : y[n] < 0).
      { apply H7 in H8. applyAxiomII H5. destruct H5 as [H5 H9].
        apply Rlt_trans with (r2 := b/2); auto. }
      apply Abs_lt in H4 as H10. apply Abs_lt in H9 as H11.
      rewrite H10; rewrite H11. rewrite Ropp_div. apply Ropp_lt_gt_contravar.
      auto.
    - assert (H5 : (b / 2) ∈ \(0, b\)).
      { apply <- AxiomII. split.
        - assert (H5 : /2 > 0).
          { apply Rinv_0_lt_compat. apply Rlt_0_2. }
          unfold Rdiv. apply Rmult_gt_0_compat; auto.
        - unfold Rdiv. pattern b at 2. rewrite <- (Rmult_1_r b).
          assert (H5 : /2 < 1).
          { assert (H6 : 2 > 1).
            { generalize Rlt_0_1. intro H5.
              apply Rplus_lt_compat_l with (r := 1) in H5.
              rewrite Rplus_0_r in H5. assert (H6 : 1+1=2). field.
              rewrite H6 in H5. auto. }
            assert (H7 : 1 = /1). field. rewrite H7.
            apply Rinv_lt_contravar; auto. rewrite Rmult_1_l. apply Rlt_0_2. }
          apply Rmult_lt_compat_l; auto. }
      assert (H6 : (∀ a' : R, a' ∈ \(0, b\) ->
        (∃ N, (∀ n, (n > N)%nat -> y[n] > a')))).
      { apply Theorem2_4_1; auto. }
      apply H6 in H5 as H7. destruct H7 as [N H7]. exists N. intros n H8.
      assert (H9 : y[n] > 0).
      { apply H7 in H8. applyAxiomII H5. destruct H5 as [H5 H9].
        apply Rlt_trans with (r2 := b/2); auto. }
      apply Abs_gt in H4 as H10. apply Abs_gt in H9 as H11.
      rewrite H10; rewrite H11. auto. }
  assert (H5 : ∀ ε, ε > 0 -> (∃ N : nat, ∀ n : nat, (n > N)%nat ->
    Abs[(/y[n]) - (/b)] < 2 * ε / (b*b))).
  { intros ε H5. apply H0 in H5 as H6. destruct H6 as [N2 H6].
    destruct H4 as [N3 H4]. generalize (Max_nat_2 N2 N3). intro H7.
    destruct H7 as [N [H7 H8]]. exists N. intros n H9.
    assert (H10 : (n > N2)%nat).
    { apply gt_trans with (m := N); auto. }
    assert (H11 : (n > N3)%nat).
    { apply gt_trans with (m := N); auto. }
    apply H4 in H11 as H12. apply H6 in H10 as H13.
    generalize (H1 n). intro H14.
    assert (H15 : / y [n] - / b = -((y[n] - b) / (y[n] * b))).
    { field; split; auto. }
    rewrite H15. rewrite <- Abs_eq_neg.
    generalize (Rmult_integral_contrapositive_currified y[n] b H14 H2).
    intro H16. rewrite Abs_div; auto. rewrite Abs_mult.
    assert (H17 :  (Abs [b] / 2) * Abs [y [n]] > 0).
    { apply Abs_not_eq_0 in H14 as I1. apply Abs_not_eq_0 in H2 as I2.
      apply Rmult_gt_0_compat; auto. apply Rmult_gt_0_compat; auto.
      apply Rinv_0_lt_compat. apply Rlt_0_2. }
    apply Rinv_lt_contravar in H12 as H18; auto.
    unfold Rdiv in *. assert (H19 : Abs[b] <> 0).
    { apply Rgt_not_eq. apply Abs_not_eq_0; auto. }
    assert (H20 : /2 <>0).
    { apply Rinv_neq_0_compat. apply Rgt_not_eq. apply Rlt_0_2. }
    rewrite Rinv_mult_distr in H18; auto.
    assert (H21 : 2 <> 0).
    { apply Rgt_not_eq. apply Rlt_0_2. }
    rewrite Rinv_involutive in H18; auto. assert (H22 : Abs[y[n]] <> 0).
    { apply Rgt_not_eq. apply Abs_not_eq_0. auto. }
    assert (H23 : / (Abs [y [n]] * Abs [b]) > 0).
    { apply Rinv_0_lt_compat.
      apply Rmult_gt_0_compat; apply Abs_not_eq_0; auto. }
    apply Rmult_lt_compat_r with (r := / (Abs [y [n]] * Abs [b]))
      in H13 as H24; auto.
    apply Rlt_trans with (r2 := ε * / (Abs [y [n]] * Abs [b])); auto.
    rewrite Rinv_mult_distr; auto. rewrite <- Rmult_assoc.
    rewrite (Rmult_comm ε (/ Abs [y [n]])). rewrite Rmult_assoc.
    assert (H25 : ε * / Abs [b] > 0).
    { apply Rmult_gt_0_compat; auto. apply Rinv_0_lt_compat.
      apply Abs_not_eq_0. auto. }
    apply Rmult_lt_compat_r with (r := ε * / Abs [b]) in H18 as H26; auto.
    assert (H27 : / Abs [b] * 2 * (ε * / Abs [b]) =
      2 * ε * / (Abs [b] * Abs [b])).
    { field; auto. }
    rewrite H27 in H26. assert (H28 : Abs [b] * Abs [b] = b * b).
    { apply Rdichotomy in H2 as I1. destruct I1 as [I1 | I1].
      - apply Abs_lt in I1 as I2. rewrite I2. field.
      - apply Abs_gt in I1 as I2. rewrite I2. auto. }
    rewrite <- H28. auto. }
  assert (I0 : IsSeq {` λ n v, v = /y[n] `} ).
  { split.
    - unfold Function. intros x0 y0 z0 H6 H7. applyAxiomII' H6.
      applyAxiomII' H7. rewrite H7; auto.
    - apply AxiomI. intro z; split; intro H6.
      + apply <- AxiomII; auto.
      + apply AxiomII. exists (/y[z]). apply AxiomII'. auto. }
  split; auto.
  intros ε H6. assert (H7 : ε * (b * b) / 2 > 0).
  { unfold Rdiv. rewrite (Rmult_assoc ε (b*b) (/2)).
    apply Rmult_gt_0_compat; auto. assert (H7 : b * b > 0).
    { apply Rdichotomy in H2 as I1. destruct I1 as [I1 | I1].
      - apply Ropp_gt_lt_0_contravar in I1 as I2.
        assert (I3 : b*b = (-b)*(-b)). field. rewrite I3.
        apply Rmult_gt_0_compat; auto.
      - apply Rmult_gt_0_compat; auto. }
    apply Rmult_gt_0_compat; auto. apply Rinv_0_lt_compat. apply Rlt_0_2. }
  apply H5 in H7 as H8. assert (H9 : 2 * (ε * (b * b) / 2) / (b * b) = ε ).
  { field; auto. }
  rewrite H9 in H8. destruct H8 as [N H10]. exists N. intros n H11.
  assert (H12 : {` λ(n0 : nat)(v : R),v = / y [n0] `} [n] = /y[n]).
  { destruct I0 as [I0 I1]. apply f_x; auto. apply AxiomII'. auto. }
  rewrite H12. auto.
Qed.

(* x y是收敛数列,y(n),lim y 均不为0,lim(x/y) = limx/limy *)
Theorem Theorem2_7_4 : ∀ (x y : Seq), Convergence x -> Convergence y ->
  (∀ n : nat, y[n] <> 0) -> lim y <> 0 ->
  Convergence {` λ n v, v = x[n] / y[n] `} /\
  lim {` λ n v, v = x[n] / y[n] `} = lim x / lim y.
Proof.
  intros x y H0 H1 H2 H3. 
  assert (H4 : limit_seq {` λ n v, v = /y[n] `} (/(lim y)) ).
  { apply Theorem2_7_4'; auto. }
  assert (H5 : ∃ y', y' = {` λ n v, v = /y[n] `} ).
  { exists {` λ n v, v = /y[n] `}. auto. }
  destruct H5 as [y' H5].
  assert (H6 : {` λ n v, v = x[n] / y[n] `} =
    {` λ n v, v = x[n] * y'[n] `}).
  { apply AxiomI. intro z; split; intro I1.
    - applyAxiomII I1. destruct I1 as [x0 [y0 [I1 I2]]]. rewrite I1 in *.
      apply AxiomII'. assert (I3 : y'[x0] = /y[x0]).
      { rewrite H5. apply f_x; try apply H4. apply AxiomII'. auto. }
      rewrite I3. auto.
    - applyAxiomII I1. destruct I1 as [x0 [y0 [I1 I2]]]. rewrite I1 in *.
      apply AxiomII'. assert (I3 : y'[x0] = /y[x0]).
      { rewrite H5. apply f_x; try apply H4. apply AxiomII'. auto. }
      rewrite I3 in I2. auto. }
  rewrite H6. assert (H7 : Convergence y').
  { rewrite H5. exists (/ lim y). auto. }
  assert (H8 : lim y' = / lim y).
  { rewrite H5. apply lim_a. auto. }
  unfold Rdiv. rewrite <- H8. apply Theorem2_7_3; auto.
Qed.

(* 定义: nat型的严格增函数 *)
Definition StrictlyIncreaseFun_nat (f : set (prod nat nat)) : Prop :=
    Function f /\ (∀ x1 y1 x2 y2 : nat, [x1, y1] ∈ f -> [x2, y2] ∈ f
    -> x1 < x2 -> y1 < y2)%nat.

Theorem fn_ge_n : ∀ (f : set (prod nat nat)) n, dom[f] = Full nat ->
  StrictlyIncreaseFun_nat f -> (f\[n\] >= n)%nat.
Proof.
  intros f n H0. induction n as [|n IHn]; intro H1.
  - apply Nat.le_0_l.
  - apply IHn in H1 as H2. generalize (Nat.lt_succ_diag_r n). intro H3.
    assert (H4 : n ∈ dom[f]).
    { rewrite H0. apply AxiomII. auto. }
    assert (H5 : S n ∈ dom[f]).
    { rewrite H0. apply AxiomII. auto. }
    apply x_fx_N in H4 as H6; try apply H1.
    apply x_fx_N in H5 as H7; try apply H1.
    assert (H8 : (f\[n\] < f\[S n\])%nat).
    { destruct H1 as [H1 H8]. apply (H8 n f\[n\] (S n) f\[S n\]); auto. }
    apply lt_le_S. apply Nat.le_lt_trans with (m := f\[n\]); auto.
Qed.

(* 定义1 子列(y 是 x 的子列) *)
Definition SubSeq (x y : Seq) : Prop := IsSeq x /\ IsSeq y /\
  (∃ f : set (prod nat nat), StrictlyIncreaseFun_nat f /\
    dom[f] = Full nat /\ (∀ n : nat, y[n] = x[f\[n\]])).

(* 定理2.8 数列收敛的充要条件 *)
Theorem Theorem2_8 : ∀ (x : Seq), IsSeq x -> (Convergence x <->
  (∀ (y : Seq), SubSeq x y -> Convergence y)).
Proof.
  intros x H12. split.
  - intros H0 y H1. destruct H0 as [a H0].
    destruct H1 as [H1 [H2 [f [H3 [H4 H5]]]]].
    exists a. unfold limit_seq. split; auto. intros ε H6.
    destruct H0 as [H0 H7]. apply H7 in H6 as H8.
    destruct H8 as [N H8]. exists N. intros n H9.
    rewrite H5. assert (H10 : (f\[n\] >= n)%nat).
    { apply fn_ge_n; auto. }
    assert (H11 : (f\[n\] > N)%nat).
    { apply Nat.lt_le_trans with (m := n); auto. }
    auto.
  - intro H0. assert (H1 : SubSeq x x).
    { split; auto; split; auto. exists ({` λ (u v : nat), u = v `}).
      assert (H1 : Function {` λ (u v : nat), u = v `} ).
      { unfold Function. intros x0 y0 z0 I1 I2.
        applyAxiomII' I1. applyAxiomII' I2. rewrite <- I1. auto. }
      split; [idtac | split].
      - split; auto. intros x1 y1 x2 y2 I1 I2 I3.
        applyAxiomII' I1. applyAxiomII' I2.
        rewrite <- I1; rewrite <- I2. auto.
      - apply AxiomI; split; intro I1.
        + apply AxiomII; auto.
        + apply AxiomII. exists z. apply AxiomII'; auto.
      - intro n. assert (H2 : {` λ (u v : nat), u = v `} \[n\] = n).
        { apply f_x_N; auto. apply AxiomII'. auto. }
        rewrite H2. auto. }
    apply H0 in H1. auto.
Qed.

(* 收敛数列的任意子列具有相同极限 *)
Lemma SubSeqEqual : ∀ (x : Seq) (a : R), limit_seq x a ->
    (∀ (y : Seq), SubSeq x y -> limit_seq y a).
Proof.
  intros x a H0 y H1. unfold SubSeq in H1.
  destruct H1 as [H1 [H2 [f [H3 [H4 H5]]]]].
  split; auto. intros ε H6.
  destruct H0 as [H0 H7]. apply H7 in H6 as [N H8].
  exists N. intros n H9. rewrite H5.
  generalize (fn_ge_n f n H4 H3). intro H10.
  apply H8. generalize (Nat.lt_le_trans N n f\[n\] H9 H10).
  intro H11. apply H11.
Qed.

End A2_2.

Export A2_2.