Require Export A_4_1.

Module A4_2.

(* 4.2 连续函数的性质 *)

(* 局部有界性 *)
Theorem Theorem4_2 : ∀ (f : Fun) (x0 : R), Continuous f x0 ->
  (∃ δ, δ > 0 /\ IntervalBoundedFun f (Neighbor x0 δ)).
Proof.
  intros f x0 [H0 H1].
  assert (H2 : ∃ A, limit f x0 A).
  { exists f[x0]. assumption. }
  apply Theorem3_3 in H2 as [δ [H3 H4]]. exists δ.
  split; auto. unfold IntervalBoundedFun in *.
  destruct H4 as [H4 [H5 [M H6]]].
  assert (H7 : ∀ x : R, x ∈ Neighbor x0 δ ->
    (x ∈ Neighbor0 x0 δ \/ x = x0)).
  { intros x I1. applyAxiomII I1.
    generalize (Abs_Rge0 (x - x0)); intro I2.
    destruct I2 as [I2 | I2].
    - left. apply AxiomII. split; auto.
    - right. apply NNPP. intro I3.
      assert (I4 : x - x0 <> 0). lra.
      apply Abs_not_eq_0 in I4. lra. }
  assert (H8 : Neighbor x0 δ ⊂ dom[ f]).
  { intros x I1. apply H7 in I1.
    generalize (Abs_Rge0 (x - x0)); intro I2.
    destruct I1 as [I1 | I1]; auto.
    rewrite I1. assumption. }
  repeat split; auto.
  destruct (Rlt_or_le M f[x0]) as [H9 | H9].
  - exists f[x0]. intros x I1. apply H7 in I1 as [I2 | I2].
    + apply H6 in I2. lra.
    + rewrite I2. assert (I3 : x0 + δ/2 ∈ Neighbor0 x0 δ).
      { apply AxiomII. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. }
      apply H6 in I3 as I4.
      generalize (Abs_Rge0 (f [x0 + δ / 2])); intro I5.
      assert (I6 : f[x0] >= 0). lra.
      rewrite Abs_ge; lra.
  - destruct (Rlt_or_le (-M) f[x0]) as [H10 | H10].
    + exists M. intros x I1. apply H7 in I1 as [I2 | I2].
      * apply H6. assumption.
      * rewrite I2. apply Abs_le_R. lra.
    + assert (I1 : M <= -f[x0]). lra.
      exists (-f[x0]). intros x I2. apply H7 in I2 as [I3 | I3].
      * apply H6 in I3. lra.
      * rewrite I3. apply Abs_le_R. lra.
Qed.

(* 局部保号性 *)
Theorem Theorem4_3_1 : ∀ (f : Fun) (x0 A : R), Continuous f x0 -> f[x0] > 0 ->
  (∀ r, 0 < r < f[x0] -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (Neighbor x0 δ) -> 0 < r < f[x]))).
Proof.
  intros f x0 A [H0 H1] H2 r H3.
  apply Theorem3_4_1 with (r := r) in H1 as [δ [H4 H5]]; auto.
  exists δ. split; auto. intros x H6.
  assert (H7 : x ∈ Neighbor0 x0 δ \/ x = x0).
  { applyAxiomII H6.
    generalize (Abs_Rge0 (x - x0)); intro I2.
    destruct I2 as [I2 | I2].
    - left. apply AxiomII. split; auto.
    - right. apply NNPP. intro I3.
      assert (I4 : x - x0 <> 0). lra.
      apply Abs_not_eq_0 in I4. lra. }
  destruct H7 as [H7 | H7]; auto.
  rewrite H7. assumption.
Qed.

Theorem Theorem4_3_1' : ∀ (f : Fun) (x0: R),
  ContinuousLeft f x0 -> f[x0] > 0 ->
  (∀ r, 0 < r < f[x0] -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (leftNeighbor x0 δ) -> 0 < r < f[x]))).
Proof.
  intros f x0 [H H0] H1 r H2.
  destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : f[x0] - r > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  assert (H11 : x0 - δ < x < x0 \/ x = x0).
  { destruct H9 as [H9 [I1 | I1]].
    - left; lra.
    - right; assumption. }
  destruct H11 as [H11 | H11].
  - apply H8 in H11 as H10. apply Abs_R in H10. lra.
  - rewrite H11. assumption.
Qed.

Theorem Theorem4_3_1'' : ∀ (f : Fun) (x0: R),
  ContinuousRight f x0 -> f[x0] > 0 ->
  (∀ r, 0 < r < f[x0] -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (rightNeighbor x0 δ) -> 0 < r < f[x]))).
Proof.
  intros f x0 [H H0] H1 r H2.
  destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : f[x0] - r > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  assert (H11 : x0 < x < x0 + δ \/ x = x0).
  { destruct H9 as [[I1 | I1] H9].
    - left; lra.
    - right; assumption. }
  destruct H11 as [H11 | H11].
  - apply H8 in H11 as H10. apply Abs_R in H10. lra.
  - rewrite H11. assumption.
Qed.

Theorem Theorem4_3_2 : ∀ (f : Fun) (x0 A : R), Continuous f x0 -> f[x0] < 0 ->
  (∀ r, 0 < r < -f[x0] -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (Neighbor x0 δ) -> f[x] < -r < 0))).
Proof.
  intros f x0 A [H0 H1] H2 r H3.
  apply Theorem3_4_2 with (r := r) in H1 as [δ [H4 H5]]; auto.
  exists δ. split; auto. intros x H6.
  assert (H7 : x ∈ Neighbor0 x0 δ \/ x = x0).
  { applyAxiomII H6.
    generalize (Abs_Rge0 (x - x0)); intro I2.
    destruct I2 as [I2 | I2].
    - left. apply AxiomII. split; auto.
    - right. apply NNPP. intro I3.
      assert (I4 : x - x0 <> 0). lra.
      apply Abs_not_eq_0 in I4. lra. }
  destruct H7 as [H7 | H7]; auto.
  rewrite H7. lra.
Qed.

Theorem Theorem4_3_2' : ∀ (f : Fun) (x0: R),
  ContinuousLeft f x0 -> f[x0] < 0 ->
  (∀ r, 0 < r < -f[x0] -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (leftNeighbor x0 δ) -> f[x] < -r < 0))).
Proof.
  intros f x0 [H H0] H1 r H2.
  destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : -(f[x0] + r) > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  assert (H11 : x0 - δ < x < x0 \/ x = x0).
  { destruct H9 as [H9 [I1 | I1]].
    - left; lra.
    - right; assumption. }
  destruct H11 as [H11 | H11].
  - apply H8 in H11 as H10. apply Abs_R in H10. lra.
  - rewrite H11. lra.
Qed.

Theorem Theorem4_3_2'' : ∀ (f : Fun) (x0: R),
  ContinuousRight f x0 -> f[x0] < 0 ->
  (∀ r, 0 < r < -f[x0] -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (rightNeighbor x0 δ) -> f[x] < -r < 0))).
Proof.
  intros f x0 [H H0] H1 r H2.
  destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : -(f[x0] + r) > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  assert (H11 : x0 < x < x0 + δ \/ x = x0).
  { destruct H9 as [[I1 | I1] H9 ].
    - left; lra.
    - right; assumption. }
  destruct H11 as [H11 | H11].
  - apply H8 in H11 as H10. apply Abs_R in H10. lra.
  - rewrite H11. lra.
Qed.

(* 有界性定理 *)
Theorem Theorem4_6' : ∀ (f : Fun) (a b : R), ContinuousClose f a b
  -> IntervalBoundedFun f (\[ a, b \]).
Proof.
  intros f a b [H1 [[H2 H3] [H4 H5]]]. unfold ContinuousOpen in H1.
  destruct H3 as [H3 [δ1' [H6 [H7 H8]]]].
  destruct H5 as [H5 [δ2' [H9 [H10 H11]]]].
  split; auto. assert (H12 : (CloseInterval a b) ⊂ dom[ f]).
  { intros x I1. applyAxiomII I1.
    assert (I2 : a < x < b \/ x = a \/ x = b). lra.
    destruct I2 as [I2 | [I2 | I2]].
    - apply H1 in I2 as I3. apply I3.
    - rewrite I2. assumption.
    - rewrite I2. assumption. }
  split; auto. apply NNPP. intro H13.
  assert (H14 : ∀ M, ~ (∀x : R, x ∈ \[ a, b \] -> Abs [f [x]] <= M)).
  { apply not_ex_all_not. assumption. }
  assert (H15 : ∀ M, (∃ x, x ∈ \[ a, b \] /\ M < Abs [f [x]])).
  { intro M. generalize (H14 M). intro H15.
    assert (I1 : ∃ x, ~ (x ∈ \[ a, b \] -> Abs [f [x]] <= M)).
    { apply not_all_not_ex. intro J1. apply H15.
      intros x. apply NNPP. apply J1. }
    destruct I1 as [x I1]. exists x. apply imply_to_and in I1.
    destruct I1 as [I1 I2]. split; auto. lra. }
  assert (H16 : (∀ M, (∃ x, x ∈ \[ a, b \] /\ M < f [x]))
    \/ (∀ M, (∃ x, x ∈ \[ a, b \] /\ f[x] < - M))).
  { apply NNPP. intro I1. apply not_or_and in I1.
    destruct I1 as [I1 I2]. apply not_all_ex_not in I1.
    apply not_all_ex_not in I2. destruct I1 as [M1 I1].
    destruct I2 as [M2 I2]. apply H13.
    assert (I3 : ∀ x, x ∈ \[ a, b \] -> f[x] <= M1).
    { intro x. apply or_to_imply.
      assert (J1 : ∀ x, ~ ((x ∈ \[ a, b \]) /\ M1 < f [x])).
      { apply not_ex_all_not. assumption. }
      generalize (J1 x). intro J2. apply not_and_or in J2.
      destruct J2 as [J2 | J2].
      - left; assumption.
      - right; lra. }
    assert (I4 : ∀ x, x ∈ \[ a, b \] -> - M2 <= f[x]).
    { intro x. apply or_to_imply.
      assert (J1 : ∀ x, ~ ((x ∈ \[ a, b \]) /\ f [x] < - M2)).
      { apply not_ex_all_not. assumption. }
      generalize (J1 x). intro J2. apply not_and_or in J2.
      destruct J2 as [J2 | J2].
      - left; assumption.
      - right; lra. }
    assert (I5 : ∃ M, Abs[M1] < M /\ Abs[-M2] < M).
    { destruct (Rlt_or_le (Abs[M1]) (Abs[-M2])) as [J1 | J1].
      - exists (Abs[-M2] + 1). lra.
      - exists (Abs[M1] + 1). lra. }
    destruct I5 as [M [I5 I6]].
    exists M. intros x I7.
    destruct (Rlt_or_le f[x] 0) as [I8 | I8].
    - rewrite Abs_lt; auto. apply I4 in I7.
      assert (I9 : -M2 < 0). lra. rewrite Abs_lt in I6; auto. lra.
    - apply Rle_ge in I8. rewrite Abs_ge; auto.
      apply I3 in I7. assert (I9 : M1 >= 0). lra.
      rewrite Abs_ge in I5; auto. lra. }
  destruct H16 as [H16 | H16].
  - assert (H17 : ∃ s, s = {` λ n v, v = cR \{ λ xn, xn ∈ \[ a, b \]
      /\ (INR n) < f [xn] \} `}).
    { exists ({` λ n v, v = cR \{ λ xn, xn ∈ \[ a, b \]
      /\ (INR n) < f [xn] \} `}); reflexivity. }
    destruct H17 as [s H17].
    assert (H18 : Function s).
    { unfold Function. rewrite H17. intros n v1 v2 I1 I2.
      applyAxiomII' I1. applyAxiomII' I2. rewrite I2; assumption. }
    assert (H19 : IsSeq s).
    { split; auto.
      apply AxiomI. intro n; split; intro I1.
      - apply AxiomII. reflexivity.
      - apply AxiomII. exists (cR \{ λ xn, xn ∈ \[ a, b \]
          /\ (INR n) < f [xn] \}). rewrite H17.
        apply AxiomII'. reflexivity. }
    assert (H20 : ∀ n, s[n] ∈ \[ a, b \] /\ (INR n) < f [s[n]]).
    { intro n. assert (I1 : [n, s[n]] ∈ s).
      { apply x_fx; auto. destruct H19 as [H19 I1].
        rewrite I1. apply AxiomII. reflexivity. }
      pattern s at 2 in I1.
      rewrite H17 in I1. applyAxiomII' I1.
      assert (I2 : NotEmpty \{ λ xn, xn ∈ \[ a, b \]
          /\ (INR n) < f [xn] \}).
      { unfold NotEmpty. generalize (H16 (INR n)). intros [x I2].
        exists x. apply AxiomII. assumption. }
      apply AxiomcR in I2. rewrite <- I1 in I2.
      applyAxiomII I2. assumption. }
    assert (H21 : BoundedSeq s).
    { split; auto. assert (I5 : ∃ M, Abs[a] < M /\ Abs[b] < M).
      { destruct (Rlt_or_le (Abs[a]) (Abs[b])) as [J1 | J1].
        - exists (Abs[b] + 1). lra.
        - exists (Abs[a] + 1). lra. }
      destruct I5 as [M [I5 I6]].
      exists M. intros n. generalize (H20 n). intro I7.
      destruct I7 as [I7 I10]. applyAxiomII I7.
      destruct (Rlt_or_le s[n] 0) as [I8 | I8].
      - rewrite Abs_lt; auto.
        assert (I9 : a < 0). lra. rewrite Abs_lt in I5; auto. lra.
      - apply Rle_ge in I8. rewrite Abs_ge; auto.
        assert (I9 : b >= 0). lra.
        rewrite Abs_ge in I6; auto. lra. }
    apply Theorem2_10 in H21 as H22.
    destruct H22 as [t [H22 H23]]. unfold SubSeq in H22.
    destruct H22 as [H22 [H27 [k [H24 [H25 H26]]]]].
    unfold Convergence in H23. destruct H23 as [ξ H23].
    assert (H28 : a <= ξ <= b).
    { split; [apply Theorem2_5_1 with (x := t); auto
        | apply Theorem2_5_2 with (x := t); auto];
      exists 0%nat; intros n I1; rewrite H26;
      generalize (H20 (k\[n\])); intros [I2 I3];
      applyAxiomII I2; apply Rge_le;
      destruct I2 as [I2 I4]; auto;
      apply Rle_ge; assumption. }
    assert (H29 : ∃ fn, fn = {` λ n v, v = f[t[n]] `}).
    { exists {` λ n v, v = f[t[n]] `}; reflexivity. }
    destruct H29 as [fn H29].
    assert (H30 : limit_seq fn f[ξ]).
    { assert (I1 : a < ξ < b \/ ξ = a \/ ξ = b). lra.
      rewrite H29.
      destruct I1 as [I1 | [I1 | I1]].
      - apply H1 in I1 as I2. destruct I2 as [I2 I3].
        apply (Theorem3_8' f ξ); auto. intros x J1.
        applyAxiomII J1. destruct J1 as [t0 J1].
        apply f_x in J1; try apply H27. rewrite H26 in J1.
        apply H12. rewrite <- J1. apply H20.
      - rewrite I1 in *. apply (Theorem3_8_1' f a); auto.
        + split; auto. exists δ1'. split; auto.
        + intros x J1.
          applyAxiomII J1. destruct J1 as [t0 J1].
          apply f_x in J1; try apply H27. rewrite H26 in J1.
          apply H12. rewrite <- J1. apply H20.
        + intro n. rewrite H26. generalize (H20 k \[ n \]);
          intros [I2 I3]. applyAxiomII I2. lra.
      - rewrite I1 in *. apply (Theorem3_8_2' f b); auto.
        + split; auto. exists δ2'. split; auto.
        + intros x J1.
          applyAxiomII J1. destruct J1 as [t0 J1].
          apply f_x in J1; try apply H27. rewrite H26 in J1.
          apply H12. rewrite <- J1. apply H20.
        + intro n. rewrite H26. generalize (H20 k \[ n \]);
          intros [I2 I3]. applyAxiomII I2. lra. }
    assert (H31 : ∀ n, INR n < f [t [n]]).
    { intro n. rewrite H26. generalize (H20 k\[n\]); intros [I1 I2].
      generalize (fn_ge_n k n H25 H24). intro I3.
      apply le_INR in I3 as I4. lra. }
    assert (H32 : Convergence fn).
    { exists f[ξ]. assumption. }
    apply Theorem2_3 in H32 as [M [H33 H34]].
    assert (H35 : ∃ (N : nat), (INR N) > M).
    { assert (I1 : ∃ (N : nat), (INR N) * 1 > M).
      { apply Archimedes; lra. }
      destruct I1 as [N I1].
      exists N. lra. }
    destruct H35 as [N H35]. generalize (H31 N); intro H36.
    generalize (H34 N); intro H37. apply Abs_le_R in H37.
    assert (H38 : fn[N] = f[t[N]]).
    { apply f_x; try apply H30. rewrite H29. apply AxiomII'.
      reflexivity. }
    rewrite H38 in H37. lra.
  - assert (H17 : ∃ s, s = {` λ n v, v = cR \{ λ xn, xn ∈ \[ a, b \]
      /\ (f [xn] < - INR n) \} `}).
    { exists ({` λ n v, v = cR \{ λ xn, xn ∈ \[ a, b \]
      /\ (f [xn] < - INR n) \} `}); reflexivity. }
    destruct H17 as [s H17].
    assert (H18 : Function s).
    { unfold Function. rewrite H17. intros n v1 v2 I1 I2.
      applyAxiomII' I1. applyAxiomII' I2. rewrite I2; assumption. }
    assert (H19 : IsSeq s).
    { split; auto.
      apply AxiomI. intro n; split; intro I1.
      - apply AxiomII. reflexivity.
      - apply AxiomII. exists (cR \{ λ xn, xn ∈ \[ a, b \]
          /\ (f [xn] < - INR n) \}). rewrite H17.
        apply AxiomII'. reflexivity. }
    assert (H20 : ∀ n, s[n] ∈ \[ a, b \] /\ f [s[n]] < - INR n).
    { intro n. assert (I1 : [n, s[n]] ∈ s).
      { apply x_fx; auto. destruct H19 as [H19 I1].
        rewrite I1. apply AxiomII. reflexivity. }
      pattern s at 2 in I1.
      rewrite H17 in I1. applyAxiomII' I1.
      assert (I2 : NotEmpty \{ λ xn, xn ∈ \[ a, b \]
          /\ (f [xn] < - INR n) \}).
      { unfold NotEmpty. generalize (H16 (INR n)). intros [x I2].
        exists x. apply AxiomII. assumption. }
      apply AxiomcR in I2. rewrite <- I1 in I2.
      applyAxiomII I2. assumption. }
    assert (H21 : BoundedSeq s).
    { split; auto. assert (I5 : ∃ M, Abs[a] < M /\ Abs[b] < M).
      { destruct (Rlt_or_le (Abs[a]) (Abs[b])) as [J1 | J1].
        - exists (Abs[b] + 1). lra.
        - exists (Abs[a] + 1). lra. }
      destruct I5 as [M [I5 I6]].
      exists M. intros n. generalize (H20 n). intro I7.
      destruct I7 as [I7 I10]. applyAxiomII I7.
      destruct (Rlt_or_le s[n] 0) as [I8 | I8].
      - rewrite Abs_lt; auto.
        assert (I9 : a < 0). lra. rewrite Abs_lt in I5; auto. lra.
      - apply Rle_ge in I8. rewrite Abs_ge; auto.
        assert (I9 : b >= 0). lra.
        rewrite Abs_ge in I6; auto. lra. }
    apply Theorem2_10 in H21 as H22.
    destruct H22 as [t [H22 H23]]. unfold SubSeq in H22.
    destruct H22 as [H22 [H27 [k [H24 [H25 H26]]]]].
    unfold Convergence in H23. destruct H23 as [ξ H23].
    assert (H28 : a <= ξ <= b).
    { split; [apply Theorem2_5_1 with (x := t); auto
        | apply Theorem2_5_2 with (x := t); auto];
      exists 0%nat; intros n I1; rewrite H26;
      generalize (H20 (k\[n\])); intros [I2 I3];
      applyAxiomII I2; apply Rge_le;
      destruct I2 as [I2 I4]; auto;
      apply Rle_ge; assumption. }
    assert (H29 : ∃ fn, fn = {` λ n v, v = f[t[n]] `}).
    { exists {` λ n v, v = f[t[n]] `}; reflexivity. }
    destruct H29 as [fn H29].
    assert (H30 : limit_seq fn f[ξ]).
    { assert (I1 : a < ξ < b \/ ξ = a \/ ξ = b). lra.
      rewrite H29.
      destruct I1 as [I1 | [I1 | I1]].
      - apply H1 in I1 as I2. destruct I2 as [I2 I3].
        apply (Theorem3_8' f ξ); auto. intros x J1.
        applyAxiomII J1. destruct J1 as [t0 J1].
        apply f_x in J1; try apply H27. rewrite H26 in J1.
        apply H12. rewrite <- J1. apply H20.
      - rewrite I1 in *. apply (Theorem3_8_1' f a); auto.
        + split; auto. exists δ1'. split; auto.
        + intros x J1.
          applyAxiomII J1. destruct J1 as [t0 J1].
          apply f_x in J1; try apply H27. rewrite H26 in J1.
          apply H12. rewrite <- J1. apply H20.
        + intro n. rewrite H26. generalize (H20 k \[ n \]);
          intros [I2 I3]. applyAxiomII I2. lra.
      - rewrite I1 in *. apply (Theorem3_8_2' f b); auto.
        + split; auto. exists δ2'. split; auto.
        + intros x J1.
          applyAxiomII J1. destruct J1 as [t0 J1].
          apply f_x in J1; try apply H27. rewrite H26 in J1.
          apply H12. rewrite <- J1. apply H20.
        + intro n. rewrite H26. generalize (H20 k \[ n \]);
          intros [I2 I3]. applyAxiomII I2. lra. }
    assert (H31 : ∀ n,  f [t [n]] < - INR n).
    { intro n. rewrite H26. generalize (H20 k\[n\]); intros [I1 I2].
      generalize (fn_ge_n k n H25 H24). intro I3.
      apply le_INR in I3 as I4. lra. }
    assert (H32 : Convergence fn).
    { exists f[ξ]. assumption. }
    apply Theorem2_3 in H32 as [M [H33 H34]].
    assert (H35 : ∃ (N : nat), (INR N) > M).
    { assert (I1 : ∃ (N : nat), (INR N) * 1 > M).
      { apply Archimedes; lra. }
      destruct I1 as [N I1].
      exists N. lra. }
    destruct H35 as [N H35]. generalize (H31 N); intro H36.
    generalize (H34 N); intro H37. apply Abs_le_R in H37.
    assert (H38 : fn[N] = f[t[N]]).
    { apply f_x; try apply H30. rewrite H29. apply AxiomII'.
      reflexivity. }
    rewrite H38 in H37. lra.
Qed.

(* 最大、最小值定理 *)
Theorem Theorem4_6 : ∀ (f : Fun) (a b : R), a < b
  -> ContinuousClose f a b
  -> (∃ max, MaxValue f (\[ a, b \]) max) /\
      (∃ min, MinValue f (\[ a, b \]) min).
Proof.
  intros f a b H0 H1. apply Theorem4_6' in H1 as H2.
  unfold IntervalBoundedFun in H2. destruct H2 as [H2 [H3 [M H4]]].
  assert (H5 : ∀ x, a <= x <= b -> -M <= f[x] <= M).
  { intros x I1. apply Abs_le_R. apply H4.
    apply AxiomII. lra. }
  assert (H6 : ∃ U, U = \{ λ y, ∃ x, a <= x <= b /\ [x, y] ∈ f \}).
  { exists \{ λ y, ∃ x, a <= x <= b /\ [x, y] ∈ f \}; reflexivity. }
  destruct H6 as [U H6].
  assert (H7 : NotEmpty U).
  { exists f[a]. rewrite H6. apply AxiomII. exists a.
    split; try lra. apply x_fx; auto. apply H3.
    apply AxiomII. lra. }
  apply Sup_inf_principle in H7 as [H8 H9].
  assert (H10 : ∃ η : R, sup U η).
  { apply H8. exists M. unfold Upper. intros y I1. rewrite H6 in I1.
    applyAxiomII I1. destruct I1 as [x [I1 I2]].
    apply f_x in I2; auto. rewrite <- I2.
    apply H5. assumption. }
  assert (H11 : ∃ ξ : R, inf U ξ).
  { apply H9. exists (-M). unfold Lower. intros y I1. rewrite H6 in I1.
    applyAxiomII I1. destruct I1 as [x [I1 I2]].
    apply f_x in I2; auto. rewrite <- I2.
    apply Rle_ge. apply H5. assumption. }
  destruct H10 as [η H10]; destruct H11 as [ξ H11].
  split.
  - exists η. unfold sup in H10. destruct H10 as [H10 I1].
    unfold Upper in H10. repeat split; auto.
    + intros x J1. apply H10. rewrite H6.
      apply AxiomII. exists x. split.
      * applyAxiomII J1. lra.
      * apply x_fx; auto.
    + apply NNPP. intro J1.
      assert (J2 : ∀ x0, ~ ((x0 ∈ \[ a, b \]) /\ f [x0] = η)).
      apply not_ex_all_not. assumption.
      assert (J3 : ∀ x, (x ∈ \[ a, b \]) -> f[x] < η).
      { intros x K1. generalize (J2 x); intro K2.
        apply not_and_or in K2.
        assert (K3 : f [x] <> η).
        { destruct K2 as [K2 | K2]; auto. }
        apply Rdichotomy in K3. destruct K3 as [K3 | K3]; auto.
        exfalso. assert (K4 : f[x] <= η).
        { apply H10. rewrite H6. apply AxiomII. exists x. split.
          - applyAxiomII K1. lra.
          - apply x_fx; auto. }
        lra. }
      assert (J4 : ∃ g, g = {` λ x y, a <= x <= b /\ y = / (η - f[x]) `}).
      { exists {` λ x y, a <= x <= b /\ y = / (η - f[x]) `}; reflexivity. }
      destruct J4 as [g J4].
      assert (J5 : Function g).
      { rewrite J4. intros x y z K1 K2. applyAxiomII' K1; applyAxiomII' K2.
        destruct K2 as [K2 K3]. rewrite K3. apply K1. }
      assert (J6 : ∀ x, a <= x <= b -> g[x] = / (η - f [x])).
      { intros x K1. apply f_x; auto. rewrite J4.
        apply AxiomII'. split; auto. }
      assert (J7 : ContinuousClose g a b).
      { destruct H1 as [H1 [J7 J8]].
        split; [idtac | split].
        - intros x K1. assert (K2 : x ∈ dom[g]).
          { apply AxiomII. exists (/ (η - f[x])).
            rewrite J4. apply AxiomII'. lra. }
          split; auto. split; auto.
          generalize (H1 x K1); intro K3.
          destruct K3 as [K3 [K4 [δ' [K5 [K6 K7]]]]].
          assert (K8 : ∃ δ0', δ0' > 0 /\ δ0' < x - a /\ δ0' < b - x).
          { destruct (Rlt_or_le (x - a) (b - x)) as [L1 | L1].
            - exists ((x - a) / 2). split; lra.
            - exists ((b - x) / 2). split; lra. }
          destruct K8 as [δ0' [K8 [K9 K10]]].
          exists δ0'. assert (K11 : Neighbor0 x δ0' ⊂ dom[ g]).
          { intros x0 L1. applyAxiomII L1. apply AxiomII.
            exists (/ (η - f[x0])). rewrite J4.
            apply AxiomII'. split; auto.
            destruct L1 as [L1 L2].
            apply Abs_R in L2. lra. }
          repeat split; auto. assert (K12 : (η - f [x]) / 2 > 0).
          { assert (L1 : x ∈ \[ a, b \]).
            { apply AxiomII. lra. }
            generalize (J3 x L1); intro L2. lra. }
          generalize (K7 ((η - f [x]) / 2) K12); intro K13.
          destruct K13 as [δ0 [K13 K14]].
          intros ε K15.
          assert (K16 : f[x] < η).
          { apply J3. apply AxiomII. lra. }
          assert (K17 : ε * (η - f [x]) * (η - f [x]) / 2 > 0).
          { apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra. }
          apply K7 in K17 as [δ2 [K18 K19]].
          assert (K20 : ∃ δ, δ > 0 /\ δ < δ0' /\ δ < δ2 /\ δ < δ0).
          { destruct (Rlt_or_le δ0' δ2) as [L1 | L1].
            - destruct (Rlt_or_le δ0' δ0) as [L2 | L2].
              + exists (δ0' / 2). lra.
              + exists (δ0 / 2). lra.
            - destruct (Rlt_or_le δ2 δ0) as [L2 | L2].
              + exists (δ2 / 2). lra.
              + exists (δ0 / 2). lra. }
          destruct K20 as [δ [K20 [K21 [K22 K23]]]].
          exists δ. split; try lra. intros x0 K24.
          assert (K25 : a <= x <= b). lra.
          destruct K24 as [K24 K26]. apply Abs_R in K26.
          assert (K27 : a <= x0 <= b). lra.
          rewrite J6; auto. rewrite J6; auto.
          assert (K28 : f[x0] < η).
          { apply J3. apply AxiomII. lra. }
          assert (K29 : / (η - f [x0]) - / (η - f [x])
            = (f[x0] - f[x]) / ((η - f [x0]) * (η - f [x]))).
          { field. lra. }
          rewrite K29.
          assert (K30 : 0 < ((η - f [x0]) * (η - f [x]))).
          { apply Rmult_lt_0_compat; lra. }
          assert (K31 : ((η - f [x0]) * (η - f [x])) <> 0). lra.
          rewrite Abs_div; auto.
          pattern (Abs [(η - f [x0]) * (η - f [x])]).
          rewrite Abs_gt; auto.
          assert (K32 : 0 < Abs [x0 - x] < δ2).
          { split; auto. apply Abs_R. lra. }
          generalize (K19 x0 K32); intro K33.
          assert (K34 : 0 < Abs [x0 - x] < δ0).
          { split; auto. apply Abs_R. lra. }
          generalize (K14 x0 K34); intro K35.
          apply Abs_R in K35.
          assert (K36 : 0 < (η - f [x]) / 2 < (η - f [x0])). lra.
          assert (K37 : ε * (η - f [x]) * (η - f [x]) / 2
            < ε * (η - f [x]) * (η - f [x0])).
          { assert (L1 : ε * (η - f [x]) * (η - f [x]) / 2
              = ε * (η - f [x]) * ((η - f [x]) / 2)). field.
            rewrite L1. apply Rmult_lt_compat_l; try apply K36.
            apply Rmult_lt_0_compat; lra. }
          assert (K38 : Abs [f [x0] - f [x]] <
            ε * (η - f [x]) * (η - f [x0])). lra.
          apply Rmult_lt_reg_r with
            (r := ((η - f [x0]) * (η - f [x]))); auto.
          assert (K39 : Abs [f [x0] - f [x]] /
            ((η - f [x0]) * (η - f [x])) * ((η - f [x0]) * (η - f [x]))
            = Abs [f [x0] - f [x]]). field. split; lra.
          rewrite K39.
          assert (K40 : ε * ((η - f [x0]) * (η - f [x]))
            = ε * (η - f [x]) * (η - f [x0])).
          field. rewrite K40. assumption.
        - assert (K2 : a ∈ dom[g]).
          { apply AxiomII. exists (/ (η - f[a])).
            rewrite J4. apply AxiomII'. lra. }
          split; auto. split; auto.
          destruct J7 as [K3 [K4 [δ' [K5 [K6 K7]]]]].
          exists (b - a). assert (K11 : rightNeighbor0 a (b - a) ⊂ dom[ g]).
          { intros x0 L1. applyAxiomII L1. apply AxiomII.
            exists (/ (η - f[x0])). rewrite J4.
            apply AxiomII'. split; auto.
            destruct L1 as [L1 L2]. lra. }
          repeat split; auto; try lra. assert (K12 : (η - f [a]) / 2 > 0).
          { assert (L1 : a ∈ \[ a, b \]).
            { apply AxiomII. lra. }
            generalize (J3 a L1); intro L2. lra. }
          generalize (K7 ((η - f [a]) / 2) K12); intro K13.
          destruct K13 as [δ0 [K13 K14]].
          intros ε K15.
          assert (K16 : f[a] < η).
          { apply J3. apply AxiomII. lra. }
          assert (K17 : ε * (η - f [a]) * (η - f [a]) / 2 > 0).
          { apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra. }
          apply K7 in K17 as [δ2 [K18 K19]].
          assert (K20 : ∃ δ, δ > 0 /\ δ < (b - a) /\ δ < δ2 /\ δ < δ0).
          { destruct (Rlt_or_le (b - a) δ2) as [L1 | L1].
            - destruct (Rlt_or_le (b - a) δ0) as [L2 | L2].
              + exists ((b - a) / 2). lra.
              + exists (δ0 / 2). lra.
            - destruct (Rlt_or_le δ2 δ0) as [L2 | L2].
              + exists (δ2 / 2). lra.
              + exists (δ0 / 2). lra. }
          destruct K20 as [δ [K20 [K21 [K22 K23]]]].
          exists δ. split; try lra. intros x0 K24.
          assert (K25 : a <= a <= b). lra.
          destruct K24 as [K24 K26].
          assert (K27 : a <= x0 <= b). lra.
          rewrite J6; auto. rewrite J6; auto.
          assert (K28 : f[x0] < η).
          { apply J3. apply AxiomII. lra. }
          assert (K29 : / (η - f [x0]) - / (η - f [a])
            = (f[x0] - f[a]) / ((η - f [x0]) * (η - f [a]))).
          { field. lra. }
          rewrite K29.
          assert (K30 : 0 < ((η - f [x0]) * (η - f [a]))).
          { apply Rmult_lt_0_compat; lra. }
          assert (K31 : ((η - f [x0]) * (η - f [a])) <> 0). lra.
          rewrite Abs_div; auto.
          pattern (Abs [(η - f [x0]) * (η - f [a])]).
          rewrite Abs_gt; auto.
          assert (K32 : a < x0 < a + δ2). lra.
          generalize (K19 x0 K32); intro K33.
          assert (K34 : a < x0 < a + δ0). lra.
          generalize (K14 x0 K34); intro K35.
          apply Abs_R in K35.
          assert (K36 : 0 < (η - f [a]) / 2 < (η - f [x0])). lra.
          assert (K37 : ε * (η - f [a]) * (η - f [a]) / 2
            < ε * (η - f [a]) * (η - f [x0])).
          { assert (L1 : ε * (η - f [a]) * (η - f [a]) / 2
              = ε * (η - f [a]) * ((η - f [a]) / 2)). field.
            rewrite L1. apply Rmult_lt_compat_l; try apply K36.
            apply Rmult_lt_0_compat; lra. }
          assert (K38 : Abs [f [x0] - f [a]] <
            ε * (η - f [a]) * (η - f [x0])). lra.
          apply Rmult_lt_reg_r with
            (r := ((η - f [x0]) * (η - f [a]))); auto.
          assert (K39 : Abs [f [x0] - f [a]] /
            ((η - f [x0]) * (η - f [a])) * ((η - f [x0]) * (η - f [a]))
            = Abs [f [x0] - f [a]]). field. split; lra.
          rewrite K39.
          assert (K40 : ε * ((η - f [x0]) * (η - f [a]))
            = ε * (η - f [a]) * (η - f [x0])).
          field. rewrite K40. assumption.
        - assert (K2 : b ∈ dom[g]).
          { apply AxiomII. exists (/ (η - f[b])).
            rewrite J4. apply AxiomII'. lra. }
          split; auto. split; auto.
          destruct J8 as [K3 [K4 [δ' [K5 [K6 K7]]]]].
          exists (b - a). assert (K11 : leftNeighbor0 b (b - a) ⊂ dom[ g]).
          { intros x0 L1. applyAxiomII L1. apply AxiomII.
            exists (/ (η - f[x0])). rewrite J4.
            apply AxiomII'. split; auto.
            destruct L1 as [L1 L2]. lra. }
          repeat split; auto; try lra. assert (K12 : (η - f [b]) / 2 > 0).
          { assert (L1 : b ∈ \[ a, b \]).
            { apply AxiomII. lra. }
            generalize (J3 b L1); intro L2. lra. }
          generalize (K7 ((η - f [b]) / 2) K12); intro K13.
          destruct K13 as [δ0 [K13 K14]].
          intros ε K15.
          assert (K16 : f[b] < η).
          { apply J3. apply AxiomII. lra. }
          assert (K17 : ε * (η - f [b]) * (η - f [b]) / 2 > 0).
          { apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra. }
          apply K7 in K17 as [δ2 [K18 K19]].
          assert (K20 : ∃ δ, δ > 0 /\ δ < (b - a) /\ δ < δ2 /\ δ < δ0).
          { destruct (Rlt_or_le (b - a) δ2) as [L1 | L1].
            - destruct (Rlt_or_le (b - a) δ0) as [L2 | L2].
              + exists ((b - a) / 2). lra.
              + exists (δ0 / 2). lra.
            - destruct (Rlt_or_le δ2 δ0) as [L2 | L2].
              + exists (δ2 / 2). lra.
              + exists (δ0 / 2). lra. }
          destruct K20 as [δ [K20 [K21 [K22 K23]]]].
          exists δ. split; try lra. intros x0 K24.
          assert (K25 : a <= b <= b). lra.
          destruct K24 as [K24 K26].
          assert (K27 : a <= x0 <= b). lra.
          rewrite J6; auto. rewrite J6; auto.
          assert (K28 : f[x0] < η).
          { apply J3. apply AxiomII. lra. }
          assert (K29 : / (η - f [x0]) - / (η - f [b])
            = (f[x0] - f[b]) / ((η - f [x0]) * (η - f [b]))).
          { field. lra. }
          rewrite K29.
          assert (K30 : 0 < ((η - f [x0]) * (η - f [b]))).
          { apply Rmult_lt_0_compat; lra. }
          assert (K31 : ((η - f [x0]) * (η - f [b])) <> 0). lra.
          rewrite Abs_div; auto.
          pattern (Abs [(η - f [x0]) * (η - f [b])]).
          rewrite Abs_gt; auto.
          assert (K32 : b - δ2 < x0 < b). lra.
          generalize (K19 x0 K32); intro K33.
          assert (K34 : b - δ0 < x0 < b). lra.
          generalize (K14 x0 K34); intro K35.
          apply Abs_R in K35.
          assert (K36 : 0 < (η - f [b]) / 2 < (η - f [x0])). lra.
          assert (K37 : ε * (η - f [b]) * (η - f [b]) / 2
            < ε * (η - f [b]) * (η - f [x0])).
          { assert (L1 : ε * (η - f [b]) * (η - f [b]) / 2
              = ε * (η - f [b]) * ((η - f [b]) / 2)). field.
            rewrite L1. apply Rmult_lt_compat_l; try apply K36.
            apply Rmult_lt_0_compat; lra. }
          assert (K38 : Abs [f [x0] - f [b]] <
            ε * (η - f [b]) * (η - f [x0])). lra.
          apply Rmult_lt_reg_r with
            (r := ((η - f [x0]) * (η - f [b]))); auto.
          assert (K39 : Abs [f [x0] - f [b]] /
            ((η - f [x0]) * (η - f [b])) * ((η - f [x0]) * (η - f [b]))
            = Abs [f [x0] - f [b]]). field. split; lra.
          rewrite K39.
          assert (K40 : ε * ((η - f [x0]) * (η - f [b]))
            = ε * (η - f [b]) * (η - f [x0])).
          field. rewrite K40. assumption. }
      apply Theorem4_6' in J7 as J8.
      unfold IntervalBoundedFun in J8.
      destruct J8 as [J8 [J9 [G J10]]].
      assert (J11 : 0 < G).
      { assert (K1 : a ∈ \[ a, b \]).
        { apply AxiomII. lra. }
        apply J10 in K1 as K2. apply Abs_le_R in K2.
        generalize K1; intro K4.
        applyAxiomII K1. rewrite J6 in K2; auto.
        assert (K3 : 0 < / (η - f [a])).
        { apply Rinv_0_lt_compat. apply J3 in K4. lra. }
        lra. }
      assert (J12 : ∀ x, x ∈ \[ a, b \] -> f[x] <= η - / G).
      { intros x K1. apply J10 in K1 as K2. apply Abs_le_R in K2.
        assert (K3 : a <= x <= b).
        { applyAxiomII K1; lra. }
        apply J6 in K3. destruct K2 as [K2 K4].
        rewrite K3 in K4.
        assert (K5 : 0 < η - f [x]).
        { apply J3 in K1. lra. }
        apply Rinv_0_lt_compat in K5 as K6.
        apply Rinv_le_contravar in K4 as K7; auto.
        rewrite Rinv_involutive in K7; lra. }
      assert (J13 : η - / G < η).
      { apply Rinv_0_lt_compat in J11. lra. }
      apply I1 in J13 as [y0 [J14 J15]].
      rewrite H6 in J14. applyAxiomII J14.
      destruct J14 as [x0 [J14 J16]].
      apply f_x in J16; auto. rewrite <- J16 in J15.
      assert (J17 : x0 ∈ \[ a, b \]).
      { apply AxiomII. lra. }
      apply J12 in J17. lra.
  - exists ξ. unfold inf in H11. destruct H11 as [H11 I1].
    unfold Lower in H11. repeat split; auto.
    + intros x J1. apply Rge_le. apply H11. rewrite H6.
      apply AxiomII. exists x. split.
      * applyAxiomII J1. lra.
      * apply x_fx; auto.
    + apply NNPP. intro J1.
      assert (J2 : ∀ x0, ~ ((x0 ∈ \[ a, b \]) /\ f [x0] = ξ)).
      apply not_ex_all_not. assumption.
      assert (J3 : ∀ x, (x ∈ \[ a, b \]) -> f[x] > ξ).
      { intros x K1. generalize (J2 x); intro K2.
        apply not_and_or in K2.
        assert (K3 : f [x] <> ξ).
        { destruct K2 as [K2 | K2]; auto. }
        apply Rdichotomy in K3. destruct K3 as [K3 | K3]; auto.
        exfalso. assert (K4 : f[x] >= ξ).
        { apply H11. rewrite H6. apply AxiomII. exists x. split.
          - applyAxiomII K1. lra.
          - apply x_fx; auto. }
        lra. }
      assert (J4 : ∃ g, g = {` λ x y, a <= x <= b /\ y = / (ξ - f[x]) `}).
      { exists {` λ x y, a <= x <= b /\ y = / (ξ - f[x]) `}; reflexivity. }
      destruct J4 as [g J4].
      assert (J5 : Function g).
      { rewrite J4. intros x y z K1 K2. applyAxiomII' K1; applyAxiomII' K2.
        destruct K2 as [K2 K3]. rewrite K3. apply K1. }
      assert (J6 : ∀ x, a <= x <= b -> g[x] = / (ξ - f[x])).
      { intros x K1. apply f_x; auto. rewrite J4.
        apply AxiomII'. split; auto. }
      assert (J7 : ContinuousClose g a b).
      { destruct H1 as [H1 [J7 J8]].
        split; [idtac | split].
        - intros x K1. assert (K2 : x ∈ dom[g]).
          { apply AxiomII. exists (/ (ξ - f[x])).
            rewrite J4. apply AxiomII'. lra. }
          split; auto. split; auto.
          generalize (H1 x K1); intro K3.
          destruct K3 as [K3 [K4 [δ' [K5 [K6 K7]]]]].
          assert (K8 : ∃ δ0', δ0' > 0 /\ δ0' < x - a /\ δ0' < b - x).
          { destruct (Rlt_or_le (x - a) (b - x)) as [L1 | L1].
            - exists ((x - a) / 2). split; lra.
            - exists ((b - x) / 2). split; lra. }
          destruct K8 as [δ0' [K8 [K9 K10]]].
          exists δ0'. assert (K11 : Neighbor0 x δ0' ⊂ dom[ g]).
          { intros x0 L1. applyAxiomII L1. apply AxiomII.
            exists (/ (ξ - f[x0])). rewrite J4.
            apply AxiomII'. split; auto.
            destruct L1 as [L1 L2].
            apply Abs_R in L2. lra. }
          repeat split; auto. assert (K12 : (f [x] - ξ) / 2 > 0).
          { assert (L1 : x ∈ \[ a, b \]).
            { apply AxiomII. lra. }
            generalize (J3 x L1); intro L2. lra. }
          generalize (K7 ((f [x] - ξ) / 2) K12); intro K13.
          destruct K13 as [δ0 [K13 K14]].
          intros ε K15.
          assert (K16 : f[x] > ξ).
          { apply J3. apply AxiomII. lra. }
          assert (K17 : ε * (f [x] - ξ) * (f [x] - ξ) / 2 > 0).
          { apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra. }
          apply K7 in K17 as [δ2 [K18 K19]].
          assert (K20 : ∃ δ, δ > 0 /\ δ < δ0' /\ δ < δ2 /\ δ < δ0).
          { destruct (Rlt_or_le δ0' δ2) as [L1 | L1].
            - destruct (Rlt_or_le δ0' δ0) as [L2 | L2].
              + exists (δ0' / 2). lra.
              + exists (δ0 / 2). lra.
            - destruct (Rlt_or_le δ2 δ0) as [L2 | L2].
              + exists (δ2 / 2). lra.
              + exists (δ0 / 2). lra. }
          destruct K20 as [δ [K20 [K21 [K22 K23]]]].
          exists δ. split; try lra. intros x0 K24.
          assert (K25 : a <= x <= b). lra.
          destruct K24 as [K24 K26]. apply Abs_R in K26.
          assert (K27 : a <= x0 <= b). lra.
          rewrite J6; auto. rewrite J6; auto.
          assert (K28 : f[x0] > ξ).
          { apply J3. apply AxiomII. lra. }
          assert (K29 : / (ξ - f [x0]) - / (ξ - f [x])
            = (f[x0] - f[x]) / ((f [x0] - ξ) * (f [x] - ξ))).
          { field. lra. }
          rewrite K29.
          assert (K30 : 0 < ((f [x0] - ξ) * (f [x] - ξ))).
          { apply Rmult_lt_0_compat; lra. }
          assert (K31 : ((f [x0] - ξ) * (f [x] - ξ)) <> 0). lra.
          rewrite Abs_div; auto.
          pattern (Abs [(f [x0] - ξ) * (f [x] - ξ)]).
          rewrite Abs_gt; auto.
          assert (K32 : 0 < Abs [x0 - x] < δ2).
          { split; auto. apply Abs_R. lra. }
          generalize (K19 x0 K32); intro K33.
          assert (K34 : 0 < Abs [x0 - x] < δ0).
          { split; auto. apply Abs_R. lra. }
          generalize (K14 x0 K34); intro K35.
          apply Abs_R in K35.
          assert (K36 : 0 < (f [x] - ξ) / 2 < (f [x0] - ξ)). lra.
          assert (K37 : ε * (f [x] - ξ) * (f [x] - ξ) / 2
            < ε * (f [x] - ξ) * (f [x0] - ξ)).
          { assert (L1 : ε * (f [x] - ξ) * (f [x] - ξ) / 2
              = ε * (f [x] - ξ) * ((f [x] - ξ) / 2)). field.
            rewrite L1. apply Rmult_lt_compat_l; try apply K36.
            apply Rmult_lt_0_compat; lra. }
          assert (K38 : Abs [f [x0] - f [x]] <
            ε * (f [x] - ξ) * (f [x0] - ξ)). lra.
          apply Rmult_lt_reg_r with
            (r := ((f [x0] - ξ) * (f [x] - ξ))); auto.
          assert (K39 : Abs [f [x0] - f [x]] /
            ((f [x0] - ξ) * (f [x] - ξ)) * ((f [x0] - ξ) * (f [x] - ξ))
            = Abs [f [x0] - f [x]]). field. split; lra.
          rewrite K39.
          assert (K40 : ε * ((f [x0] - ξ) * (f [x] - ξ))
            = ε * (f [x] - ξ) * (f [x0] - ξ)).
          field. rewrite K40. assumption.
        - assert (K2 : a ∈ dom[g]).
          { apply AxiomII. exists (/ (ξ - f[a])).
            rewrite J4. apply AxiomII'. lra. }
          split; auto. split; auto.
          destruct J7 as [K3 [K4 [δ' [K5 [K6 K7]]]]].
          exists (b - a). assert (K11 : rightNeighbor0 a (b - a) ⊂ dom[ g]).
          { intros x0 L1. applyAxiomII L1. apply AxiomII.
            exists (/ (ξ - f[x0])). rewrite J4.
            apply AxiomII'. split; auto.
            destruct L1 as [L1 L2]. lra. }
          repeat split; auto; try lra. assert (K12 : (f [a] - ξ) / 2 > 0).
          { assert (L1 : a ∈ \[ a, b \]).
            { apply AxiomII. lra. }
            generalize (J3 a L1); intro L2. lra. }
          generalize (K7 ((f [a] - ξ) / 2) K12); intro K13.
          destruct K13 as [δ0 [K13 K14]].
          intros ε K15.
          assert (K16 : f[a] > ξ).
          { apply J3. apply AxiomII. lra. }
          assert (K17 : ε * (f [a] - ξ) * (f [a] - ξ) / 2 > 0).
          { apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra. }
          apply K7 in K17 as [δ2 [K18 K19]].
          assert (K20 : ∃ δ, δ > 0 /\ δ < (b - a) /\ δ < δ2 /\ δ < δ0).
          { destruct (Rlt_or_le (b - a) δ2) as [L1 | L1].
            - destruct (Rlt_or_le (b - a) δ0) as [L2 | L2].
              + exists ((b - a) / 2). lra.
              + exists (δ0 / 2). lra.
            - destruct (Rlt_or_le δ2 δ0) as [L2 | L2].
              + exists (δ2 / 2). lra.
              + exists (δ0 / 2). lra. }
          destruct K20 as [δ [K20 [K21 [K22 K23]]]].
          exists δ. split; try lra. intros x0 K24.
          assert (K25 : a <= a <= b). lra.
          destruct K24 as [K24 K26].
          assert (K27 : a <= x0 <= b). lra.
          rewrite J6; auto. rewrite J6; auto.
          assert (K28 : f[x0] > ξ).
          { apply J3. apply AxiomII. lra. }
          assert (K29 : / (ξ - f [x0]) - / (ξ - f [a])
            = (f[x0] - f[a]) / ((f [x0] - ξ) * (f [a] - ξ))).
          { field. lra. }
          rewrite K29.
          assert (K30 : 0 < ((f [x0] - ξ) * (f [a] - ξ))).
          { apply Rmult_lt_0_compat; lra. }
          assert (K31 : ((f [x0] - ξ) * (f [a] - ξ)) <> 0). lra.
          rewrite Abs_div; auto.
          pattern (Abs [(f [x0] - ξ) * (f [a] - ξ)]).
          rewrite Abs_gt; auto.
          assert (K32 : a < x0 < a + δ2). lra.
          generalize (K19 x0 K32); intro K33.
          assert (K34 : a < x0 < a + δ0). lra.
          generalize (K14 x0 K34); intro K35.
          apply Abs_R in K35.
          assert (K36 : 0 < (f [a] - ξ) / 2 < (f [x0] - ξ)). lra.
          assert (K37 : ε * (f [a] - ξ) * (f [a] - ξ) / 2
            < ε * (f [a] - ξ) * (f [x0] - ξ)).
          { assert (L1 : ε * (f [a] - ξ) * (f [a] - ξ) / 2
              = ε * (f [a] - ξ) * ((f [a] - ξ) / 2)). field.
            rewrite L1. apply Rmult_lt_compat_l; try apply K36.
            apply Rmult_lt_0_compat; lra. }
          assert (K38 : Abs [f [x0] - f [a]] <
            ε * (f [a] - ξ) * (f [x0] - ξ)). lra.
          apply Rmult_lt_reg_r with
            (r := ((f [x0] - ξ) * (f [a] - ξ))); auto.
          assert (K39 : Abs [f [x0] - f [a]] /
            ((f [x0] - ξ) * (f [a] - ξ)) * ((f [x0] - ξ) * (f [a] - ξ))
            = Abs [f [x0] - f [a]]). field. split; lra.
          rewrite K39.
          assert (K40 : ε * ((f [x0] - ξ) * (f [a] - ξ))
            = ε * (f [a] - ξ) * (f [x0] - ξ)).
          field. rewrite K40. assumption.
        - assert (K2 : b ∈ dom[g]).
          { apply AxiomII. exists (/ (ξ - f[b])).
            rewrite J4. apply AxiomII'. lra. }
          split; auto. split; auto.
          destruct J8 as [K3 [K4 [δ' [K5 [K6 K7]]]]].
          exists (b - a). assert (K11 : leftNeighbor0 b (b - a) ⊂ dom[ g]).
          { intros x0 L1. applyAxiomII L1. apply AxiomII.
            exists (/ (ξ - f[x0])). rewrite J4.
            apply AxiomII'. split; auto.
            destruct L1 as [L1 L2]. lra. }
          repeat split; auto; try lra. assert (K12 : (f [b] - ξ) / 2 > 0).
          { assert (L1 : b ∈ \[ a, b \]).
            { apply AxiomII. lra. }
            generalize (J3 b L1); intro L2. lra. }
          generalize (K7 ((f [b] - ξ) / 2) K12); intro K13.
          destruct K13 as [δ0 [K13 K14]].
          intros ε K15.
          assert (K16 : f[b] > ξ).
          { apply J3. apply AxiomII. lra. }
          assert (K17 : ε * (f [b] - ξ) * (f [b] - ξ) / 2 > 0).
          { apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra.
            apply Rmult_gt_0_compat; try lra. }
          apply K7 in K17 as [δ2 [K18 K19]].
          assert (K20 : ∃ δ, δ > 0 /\ δ < (b - a) /\ δ < δ2 /\ δ < δ0).
          { destruct (Rlt_or_le (b - a) δ2) as [L1 | L1].
            - destruct (Rlt_or_le (b - a) δ0) as [L2 | L2].
              + exists ((b - a) / 2). lra.
              + exists (δ0 / 2). lra.
            - destruct (Rlt_or_le δ2 δ0) as [L2 | L2].
              + exists (δ2 / 2). lra.
              + exists (δ0 / 2). lra. }
          destruct K20 as [δ [K20 [K21 [K22 K23]]]].
          exists δ. split; try lra. intros x0 K24.
          assert (K25 : a <= b <= b). lra.
          destruct K24 as [K24 K26].
          assert (K27 : a <= x0 <= b). lra.
          rewrite J6; auto. rewrite J6; auto.
          assert (K28 : f[x0] > ξ).
          { apply J3. apply AxiomII. lra. }
          assert (K29 : / (ξ - f [x0]) - / (ξ - f [b])
            = (f[x0] - f[b]) / ((f [x0] - ξ) * (f [b] - ξ))).
          { field. lra. }
          rewrite K29.
          assert (K30 : 0 < ((f [x0] - ξ) * (f [b] - ξ))).
          { apply Rmult_lt_0_compat; lra. }
          assert (K31 : ((f [x0] - ξ) * (f [b] - ξ)) <> 0). lra.
          rewrite Abs_div; auto.
          pattern (Abs [(f [x0] - ξ) * (f [b] - ξ)]).
          rewrite Abs_gt; auto.
          assert (K32 : b - δ2 < x0 < b). lra.
          generalize (K19 x0 K32); intro K33.
          assert (K34 : b - δ0 < x0 < b). lra.
          generalize (K14 x0 K34); intro K35.
          apply Abs_R in K35.
          assert (K36 : 0 < (f [b] - ξ) / 2 < (f [x0] - ξ)). lra.
          assert (K37 : ε * (f [b] - ξ) * (f [b] - ξ) / 2
            < ε * (f [b] - ξ) * (f [x0] - ξ)).
          { assert (L1 : ε * (f [b] - ξ) * (f [b] - ξ) / 2
              = ε * (f [b] - ξ) * ((f [b] - ξ) / 2)). field.
            rewrite L1. apply Rmult_lt_compat_l; try apply K36.
            apply Rmult_lt_0_compat; lra. }
          assert (K38 : Abs [f [x0] - f [b]] <
            ε * (f [b] - ξ) * (f [x0] - ξ)). lra.
          apply Rmult_lt_reg_r with
            (r := ((f [x0] - ξ) * (f [b] - ξ))); auto.
          assert (K39 : Abs [f [x0] - f [b]] /
            ((f [x0] - ξ) * (f [b] - ξ)) * ((f [x0] - ξ) * (f [b] - ξ))
            = Abs [f [x0] - f [b]]). field. split; lra.
          rewrite K39.
          assert (K40 : ε * ((f [x0] - ξ) * (f [b] - ξ))
            = ε * (f [b] - ξ) * (f [x0] - ξ)).
          field. rewrite K40. assumption. }
      apply Theorem4_6' in J7 as J8.
      unfold IntervalBoundedFun in J8.
      destruct J8 as [J8 [J9 [G J10]]].
      assert (J11 : G > 0).
      { assert (K1 : a ∈ \[ a, b \]).
        { apply AxiomII. lra. }
        apply J10 in K1 as K2. apply Abs_le_R in K2.
        generalize K1; intro K4.
        applyAxiomII K1. rewrite J6 in K2; auto.
        assert (K3 : / (ξ - f [a]) < 0).
        { apply Rinv_lt_0_compat. apply J3 in K4. lra. }
        lra. }
      assert (J12 : ∀ x, x ∈ \[ a, b \] -> ξ + / G <= f[x]).
      { intros x K1. apply J10 in K1 as K2. apply Abs_le_R in K2.
        assert (K3 : a <= x <= b).
        { applyAxiomII K1; lra. }
        apply J6 in K3. destruct K2 as [K2 K4].
        rewrite K3 in K2.
        assert (K5 : f [x] - ξ > 0).
        { apply J3 in K1. lra. }
        apply Rinv_0_lt_compat in K5 as K6.
        assert (K8 : / (ξ - f [x]) = - (/ (f [x] - ξ))). field. lra.
        rewrite K8 in K2. apply Ropp_le_cancel in K2.
        apply Rinv_le_contravar in K2 as K7; auto.
        rewrite Rinv_involutive in K7; lra. }
      assert (J13 : ξ + / G > ξ).
      { apply Rinv_0_lt_compat in J11. lra. }
      apply I1 in J13 as [y0 [J14 J15]].
      rewrite H6 in J14. applyAxiomII J14.
      destruct J14 as [x0 [J14 J16]].
      apply f_x in J16; auto. rewrite <- J16 in J15.
      assert (J17 : x0 ∈ \[ a, b \]).
      { apply AxiomII. lra. }
      apply J12 in J17. lra.
Qed.

(* 介值性定理 *)
Theorem Theorem4_7 : ∀ (f : Fun) (a b μ : R), a < b
  -> ContinuousClose f a b -> (f[a] < μ < f[b] \/ f[b] < μ < f[a])
  -> ∃ x0, a < x0 < b /\ f[x0] = μ.
Proof.
  intros f a b μ H0 H1 H2.
  assert (H3 : ∃ g, g = {` λ x y, y = f[x] - μ `}).
  { exists {` λ x y, y = f[x] - μ `}; reflexivity. }
  destruct H3 as [g H3].
  assert (H4 : Function g).
  { rewrite H3. intros x y z I1 I2.
    applyAxiomII' I1; applyAxiomII' I2.
    rewrite I2. assumption. }
  assert (H5 : ∀ x1, g[x1] = f[x1] - μ).
  { intro x1. apply f_x; auto. rewrite H3.
    apply AxiomII'. reflexivity. }
  assert (H6 : ContinuousClose g a b).
  { split; [idtac | split].
    - intros x I1. assert (I2 : x ∈ dom[g]).
      { apply AxiomII. exists (f[x] - μ).
        rewrite H3. apply AxiomII'. reflexivity. }
      repeat split; auto.
      assert (I3 : ∃ δ0', δ0' > 0 /\ δ0' < x - a /\ δ0' < b - x).
      { destruct (Rlt_or_le (x - a) (b - x)) as [L1 | L1].
        - exists ((x - a) / 2). split; lra.
        - exists ((b - x) / 2). split; lra. }
      destruct I3 as [δ0' [I3 [I4 I5]]].
      exists δ0'. assert (I6 : Neighbor0 x δ0' ⊂ dom[ g]).
      { intros x0 J1. applyAxiomII J1. destruct J1 as [J1 J2].
        apply Abs_R in J2. apply AxiomII. exists (f [x0] - μ).
        rewrite H3. apply AxiomII'. reflexivity. }
      repeat split; auto. intros ε I7.
      destruct H1 as [H1 [I8 I9]].
      apply H1 in I1 as [I10 [I11 [δ' [I12 [I13 I14]]]]].
      apply I14 in I7 as [δ0 [I15 I16]].
      assert (I17 : ∃ δ, δ > 0 /\ δ < δ0' /\ δ < δ0).
      { destruct (Rlt_or_le δ0' δ0) as [L1 | L1].
        - exists (δ0' / 2). split; lra.
        - exists (δ0 / 2). split; lra. }
      destruct I17 as [δ [I17 [I18 I19]]].
      exists δ. split; auto. intros x0 I20.
      rewrite H5. rewrite H5.
      assert (I22 : f [x0] - μ - (f [x] - μ) = f [x0] - f [x]). field.
      rewrite I22. apply I16. lra.
    - assert (I2 : a ∈ dom[g]).
      { apply AxiomII. exists (f[a] - μ).
        rewrite H3. apply AxiomII'. reflexivity. }
      repeat split; auto.
      exists (b - a). assert (I6 : rightNeighbor0 a (b - a) ⊂ dom[ g]).
      { intros x0 J1. applyAxiomII J1. destruct J1 as [J1 J2].
        apply AxiomII. exists (f [x0] - μ).
        rewrite H3. apply AxiomII'. reflexivity. }
      repeat split; auto; try lra. intros ε I7.
      destruct H1 as [H1 [I8 I9]].
      destruct I8 as [I8 [δ' [I12 [I13 [I10 I14]]]]].
      apply I14 in I7 as [δ0 [I15 I16]].
      assert (I17 : ∃ δ, δ > 0 /\ δ < b - a /\ δ < δ0).
      { destruct (Rlt_or_le (b - a) δ0) as [L1 | L1].
        - exists ((b - a) / 2). split; lra.
        - exists (δ0 / 2). split; lra. }
      destruct I17 as [δ [I17 [I18 I19]]].
      exists δ. split; auto. intros x0 I20.
      rewrite H5. rewrite H5.
      assert (I22 : f [x0] - μ - (f [a] - μ) = f [x0] - f [a]). field.
      rewrite I22. apply I16. lra.
    - assert (I2 : b ∈ dom[g]).
      { apply AxiomII. exists (f[b] - μ).
        rewrite H3. apply AxiomII'. reflexivity. }
      repeat split; auto.
      exists (b - a). assert (I6 : leftNeighbor0 b (b - a) ⊂ dom[ g]).
      { intros x0 J1. applyAxiomII J1. destruct J1 as [J1 J2].
        apply AxiomII. exists (f [x0] - μ).
        rewrite H3. apply AxiomII'. reflexivity. }
      repeat split; auto; try lra. intros ε I7.
      destruct H1 as [H1 [I8 I9]].
      destruct I9 as [I9 [δ' [I12 [I13 [I10 I14]]]]].
      apply I14 in I7 as [δ0 [I15 I16]].
      assert (I17 : ∃ δ, δ > 0 /\ δ < b - a /\ δ < δ0).
      { destruct (Rlt_or_le (b - a) δ0) as [L1 | L1].
        - exists ((b - a) / 2). split; lra.
        - exists (δ0 / 2). split; lra. }
      destruct I17 as [δ [I17 [I18 I19]]].
      exists δ. split; auto. intros x0 I20.
      rewrite H5. rewrite H5.
      assert (I22 : f [x0] - μ - (f [b] - μ) = f [x0] - f [b]). field.
      rewrite I22. apply I16. lra. }
  assert (H7 : ∃ E , E = \{ λ x, a <= x <= b /\ 0 < g[x] \}).
  { exists \{ λ x, a <= x <= b /\ 0 < g[x] \}; reflexivity. }
  destruct H7 as [E H7].
  apply Theorem4_6' in H6 as H8.
  destruct H8 as [H8 [H9 [M H10]]].
  assert (H11 : NotEmpty E).
  { destruct H2 as [H2 | H2].
    - exists b. rewrite H7. apply AxiomII. split; try lra.
      rewrite H5. lra.
    - exists a. rewrite H7. apply AxiomII. split; try lra.
      rewrite H5. lra. }
  apply Sup_inf_principle in H11 as H12.
  destruct H12 as [H12 H13].
  destruct H2 as [H2 | H2].
  - assert (I1 : ∃ξ : R,inf E ξ).
    { apply H13. exists a. intros x J1. rewrite H7 in J1.
      applyAxiomII J1. lra. }
    destruct I1 as [x0 I1]. exists x0.
    assert (I2 : a <= x0 <= b).
    { split.
      - apply NNPP. intro J1. apply Rnot_le_lt in J1.
        unfold inf in I1. destruct I1 as [I1 I2].
        assert (J2 : (x0 + a) / 2 > x0). lra.
        apply I2 in J2 as J3. destruct J3 as [x1 [J3 J4]].
        rewrite H7 in J3. applyAxiomII J3. lra.
      - unfold inf in I1. destruct I1 as [I1 I2].
        unfold Lower in I1. apply Rge_le.
        apply I1. rewrite H7. apply AxiomII.
        split; try lra. rewrite H5. lra. }
    assert (I3 : g[a] < 0).
    { rewrite H5. lra. }
    destruct H6 as [H6 [I4 I5]].
    apply Theorem4_3_2'' with (r := -g[a]/2) in I4 as I6; auto; try lra.
    destruct I6 as [δ [I6 I7]].
    assert (I8 : x0 <> a).
    { intro J1. unfold inf in I1. destruct I1 as [I1 J2].
      assert (J3 : x0 + δ/2 > x0). lra.
      apply J2 in J3 as J4. destruct J4 as [x1 [J4 J5]].
      rewrite H7 in J4. applyAxiomII J4.
      assert (J6 : x1 ∈ rightNeighbor a δ).
      { apply AxiomII. lra. }
      apply I7 in J6 as J7. lra. }
    assert (I9 : g[b] > 0).
    { rewrite H5; lra. }
    assert (I10 : x0 < b).
    { apply Theorem4_3_1' with (r := g[b]/2) in I5 as J1; auto; try lra.
      destruct J1 as [δ1 [J1 J2]].
      unfold inf in I1. destruct I1 as [I1 J3].
      unfold Lower in I1.
      assert (J4 : ∃ x2, x2 < b /\ x2 > (b - δ1/2) /\ x2 > a).
      { destruct (Rlt_or_le (b - δ1/2) a) as [K1 | K1].
        - exists ((a + b) / 2). split; lra.
        - exists (b - δ1/4). split; lra. }
      destruct J4 as [x2 [J4 [J5 J6]]].
      assert (J7 : x2 ∈ E).
      { rewrite H7. apply AxiomII. split; try lra.
        assert (K1 : x2 ∈ leftNeighbor b δ1).
        { apply AxiomII. lra. }
        apply J2 in K1 as K2. lra. }
      apply I1 in J7. lra. }
    assert (I11 : a < x0 < b). lra.
    split; auto.
    assert (I12 : g[x0] = 0).
    { apply NNPP. intro J1. apply Rdichotomy in J1 as [J1 | J1].
      - apply H6 in I11 as J2.
        apply Theorem4_3_2 with (r := -(g[x0]/2)) in J2 as J3; auto; try lra.
        destruct J3 as [δ1 [J3 J4]].
        unfold inf in I1. destruct I1 as [I1 J5].
        assert (J6 : x0 + δ1/2 > x0). lra.
        apply J5 in J6 as J7.
        destruct J7 as [x1 [J7 J8]].
        unfold Lower in I1. apply I1 in J7 as J9.
        rewrite H7 in J7. applyAxiomII J7.
        assert (J10 : x1 ∈ Neighbor x0 δ1).
        { apply AxiomII. apply Abs_R. lra. }
        apply J4 in J10. lra.
      - apply H6 in I11 as J2.
        apply Theorem4_3_1 with (r := g[x0]/2) in J2 as J3; auto; try lra.
        destruct J3 as [δ1 [J3 J4]].
        unfold inf in I1. destruct I1 as [I1 J5].
        unfold Lower in I1.
        assert (J6 : ∃ x1, x1 < x0 /\ x1 > a /\ x1 > x0 - δ1).
        { destruct (Rlt_or_le a (x0 - δ1)) as [K1 | K1].
          - exists (x0 - δ1/2). split; lra.
          - exists ((a + x0) / 2). split; lra. }
        destruct J6 as [x1 [J6 [J7 J8]]].
        assert (J9 : x1 ∈ E).
        { rewrite H7. apply AxiomII. split; try lra.
          assert (K1 : x1 ∈ Neighbor x0 δ1).
          { apply AxiomII. apply Abs_R. lra. }
          apply J4 in K1. lra. }
        apply I1 in J9. lra. }
    rewrite H5 in I12. apply Rminus_diag_uniq; assumption.
  - assert (I1 : ∃η : R,sup E η).
    { apply H12. exists b. intros x J1. rewrite H7 in J1.
      applyAxiomII J1. lra. }
    destruct I1 as [x0 I1]. exists x0.
    assert (I2 : a <= x0 <= b).
    { split.
      - unfold sup in I1. destruct I1 as [I1 I2].
        unfold Upper in I1.
        apply I1. rewrite H7. apply AxiomII.
        split; try lra. rewrite H5. lra.
      - apply NNPP. intro J1. apply Rnot_le_lt in J1.
        unfold sup in I1. destruct I1 as [I1 I2].
        assert (J2 : (x0 + b) / 2 < x0). lra.
        apply I2 in J2 as J3. destruct J3 as [x1 [J3 J4]].
        rewrite H7 in J3. applyAxiomII J3. lra. }
    assert (I3 : g[b] < 0).
    { rewrite H5. lra. }
    destruct H6 as [H6 [I4 I5]].
    apply Theorem4_3_2' with (r := -g[b]/2) in I5 as I6; auto; try lra.
    destruct I6 as [δ [I6 I7]].
    assert (I8 : x0 <> b).
    { intro J1. unfold inf in I1. destruct I1 as [I1 J2].
      assert (J3 : x0 - δ/2 < x0). lra.
      apply J2 in J3 as J4. destruct J4 as [x1 [J4 J5]].
      rewrite H7 in J4. applyAxiomII J4.
      assert (J6 : x1 ∈ leftNeighbor b δ).
      { apply AxiomII. lra. }
      apply I7 in J6 as J7. lra. }
    assert (I9 : g[a] > 0).
    { rewrite H5; lra. }
    assert (I10 : x0 > a).
    { apply Theorem4_3_1'' with (r := g[a]/2) in I4 as J1; auto; try lra.
      destruct J1 as [δ1 [J1 J2]].
      unfold sup in I1. destruct I1 as [I1 J3].
      unfold Upper in I1.
      assert (J4 : ∃ x2, x2 > a /\ x2 < (a + δ1/2) /\ x2 < b).
      { destruct (Rlt_or_le (a + δ1/2) b) as [K1 | K1].
        - exists (a + δ1/4). split; lra.
        - exists ((a + b) / 2). split; lra. }
      destruct J4 as [x2 [J4 [J5 J6]]].
      assert (J7 : x2 ∈ E).
      { rewrite H7. apply AxiomII. split; try lra.
        assert (K1 : x2 ∈ rightNeighbor a δ1).
        { apply AxiomII. lra. }
        apply J2 in K1 as K2. lra. }
      apply I1 in J7. lra. }
    assert (I11 : a < x0 < b). lra.
    split; auto.
    assert (I12 : g[x0] = 0).
    { apply NNPP. intro J1. apply Rdichotomy in J1 as [J1 | J1].
      - apply H6 in I11 as J2.
        apply Theorem4_3_2 with (r := -(g[x0]/2)) in J2 as J3; auto; try lra.
        destruct J3 as [δ1 [J3 J4]].
        unfold inf in I1. destruct I1 as [I1 J5].
        assert (J6 : x0 - δ1/2 < x0). lra.
        apply J5 in J6 as J7.
        destruct J7 as [x1 [J7 J8]].
        unfold Lower in I1. apply I1 in J7 as J9.
        rewrite H7 in J7. applyAxiomII J7.
        assert (J10 : x1 ∈ Neighbor x0 δ1).
        { apply AxiomII. apply Abs_R. lra. }
        apply J4 in J10. lra.
      - apply H6 in I11 as J2.
        apply Theorem4_3_1 with (r := g[x0]/2) in J2 as J3; auto; try lra.
        destruct J3 as [δ1 [J3 J4]].
        unfold inf in I1. destruct I1 as [I1 J5].
        unfold Lower in I1.
        assert (J6 : ∃ x1, x1 > x0 /\ x1 < b /\ x1 < x0 + δ1).
        { destruct (Rlt_or_le b (x0 + δ1)) as [K1 | K1].
          - exists ((b + x0) / 2). split; lra.
          - exists (x0 + δ1/2). split; lra. }
        destruct J6 as [x1 [J6 [J7 J8]]].
        assert (J9 : x1 ∈ E).
        { rewrite H7. apply AxiomII. split; try lra.
          assert (K1 : x1 ∈ Neighbor x0 δ1).
          { apply AxiomII. apply Abs_R. lra. }
          apply J4 in K1. lra. }
        apply I1 in J9. lra. }
    rewrite H5 in I12. apply Rminus_diag_uniq; assumption.
Qed.

(* 定义：f在区间I上一致连续 *)
Definition UniCon f I := Function f /\ I ⊂ dom[f] /\
  (∀ ε, ε > 0 -> (∃ δ, δ > 0 /\ (∀ x1 x2, x1 ∈ I -> x2 ∈ I ->
    Abs[x1 - x2] < δ -> Abs[f[x1] - f[x2]] < ε))).

(* 一致连续性定理 *)
Theorem Theorem4_9 : ∀ f a b, ContinuousClose f a b ->
  UniCon f (\[ a, b \]).
Proof.
  intros f a b [H0 [[H1 H2] [H3 H4]]].
  assert (H5 : Function f). apply H2.
  assert (H6 : \[ a, b \] ⊂ dom[f]).
  { intros x I1. applyAxiomII I1.
    destruct I1 as [[I1 | I1] [I2 | I2]].
    - assert (I3 : a < x < b). lra.
      apply H0 in I3. apply I3.
    - rewrite I2. assumption.
    - rewrite I1. assumption.
    - rewrite I1. assumption. }
  split; [assumption | split]; auto.
  destruct (Rtotal_order a b) as [H7 | [H7 | H7]].
  - apply NNPP. intros H8.
    apply not_all_ex_not in H8 as [ε0 H8].
    apply imply_to_and in H8 as [H8 H9].
    assert (H10 : ∀ δ, δ > 0 -> (∃ x1 x2, x1 ∈ \[ a, b \] /\
       x2 ∈ \[ a, b \] /\ Abs [x1 - x2] < δ /\
       Abs [f [x1] - f [x2]] >= ε0)).
    { assert (I1 : ∀ δ, ~ (δ > 0 /\ (∀ x1 x2, x1 ∈ \[ a, b \] ->
       x2 ∈ \[ a, b \] -> Abs [x1 - x2] < δ ->
       Abs [f [x1] - f [x2]] < ε0))).
      { apply not_ex_all_not. assumption. }
      intros δ. generalize (I1 δ); intros I2 I3.
      apply not_and_or in I2.
      destruct I2 as [I2 | I2]; [contradiction | idtac].
      apply not_all_ex_not in I2 as [x1 I2].
      exists x1. apply not_all_ex_not in I2 as [x2 I2].
      exists x2. apply imply_to_and in I2 as [I2 I4].
      apply imply_to_and in I4 as [I4 I5].
      apply imply_to_and in I5 as [I5 I6].
      repeat split; auto. lra. }
    clear H9.
    assert (H9 : ∃ δ, δ = (b - a) / 2).
    { exists ((b - a) / 2). reflexivity. }
    destruct H9 as [δ H9].
    assert (H11 : ∃ xy, xy = {` λ n s, s =
      choose {` λ x y, (x ∈ \[ a, b \]) /\ (y ∈ \[ a, b \])
        /\ Abs[x - y] < δ/(INR (S n)) /\ Abs [f[x] - f[y]] >= ε0 `}
      ([0, 0]) `}).
    { exists {` λ n s, s = choose {` λ x y,
        (x ∈ \[ a, b \]) /\ (y ∈ \[ a, b \])
        /\ Abs[x - y] < δ/(INR (S n)) /\
        Abs [f[x] - f[y]] >= ε0 `} ([0, 0]) `}.
      reflexivity. }
    destruct H11 as [xy H11].
    assert (H12 : ∃ x, x = {` λ n v, v = fst (xy[n | ([0, 0])]) `}).
    { exists {` λ n v, v = fst (xy[n | ([0, 0])]) `}.
      reflexivity. }
    destruct H12 as [x H12].
    assert (H13 : ∃ y, y = {` λ n v, v = snd (xy[n | ([0, 0])]) `}).
    { exists {` λ n v, v = snd (xy[n | ([0, 0])]) `}.
      reflexivity. }
    destruct H13 as [y H13].
    assert (H14 : Function xy).
    { rewrite H11. intros x1 y1 z1 I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2. assumption. }
    assert (H15 : IsSeq x).
    { rewrite H12. split.
      - intros x1 y1 z1 I1 I2.
        applyAxiomII' I1; applyAxiomII' I2.
        rewrite I2. assumption.
      - apply AxiomI; intros n;
        split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII.
          exists (fst xy [n | ([0, 0])]).
          apply AxiomII'. reflexivity. }
    assert (H16 : IsSeq y).
    { rewrite H13. split.
      - intros x1 y1 z1 I1 I2.
        applyAxiomII' I1; applyAxiomII' I2.
        rewrite I2. assumption.
      - apply AxiomI; intros n;
        split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII.
          exists (snd xy [n | ([0, 0])]).
          apply AxiomII'. reflexivity. }
    assert (H17 : ∀ n, x[n] = fst xy[n | ([0, 0])]).
    { intros n. apply f_x; try apply H15.
      rewrite H12. apply AxiomII'.
      reflexivity. }
    assert (H18 : ∀ n, y[n] = snd xy[n | ([0, 0])]).
    { intros n. apply f_x; try apply H16.
      rewrite H13. apply AxiomII'.
      reflexivity. }
    assert (H19 : ∀ n, [x[n], y[n]] = xy[n | ([0, 0])]).
    { intros n. rewrite H17; rewrite H18.
      destruct xy[n | ([0, 0])] as [p q].
      simpl. reflexivity. }
    assert (H20 : ∀ n, [n, [x[n], y[n]]] ∈ xy).
    { intros n. rewrite H19.
      apply x_fx_T; auto. rewrite H11.
      apply AxiomII. exists (choose {` λ x0 y1,
        (x0 ∈ \[ a, b \]) /\ (y1 ∈ \[ a, b \])
        /\ Abs [x0 - y1] < δ / INR (S n) /\
        Abs [f [x0] - f [y1]] >= ε0`} ([0, 0])).
      apply AxiomII'. reflexivity. }
    assert (H21 : ∀ n, (x[n] ∈ \[ a, b \])
      /\ (y[n] ∈ \[ a, b \])
      /\ Abs [x[n] - y[n]] < δ / INR (S n)
      /\ Abs [f [x[n]] - f [y[n]]] >= ε0).
    { intros n. generalize (H20 n); intros I1.
      rewrite H11 in I1.
      apply -> AxiomII' in I1.
      lazy beta in I1.
      assert (I2 : NotEmpty {` λ x0 y1,
        (x0 ∈ \[ a, b \]) /\ (y1 ∈ \[ a, b \])
        /\ Abs [x0 - y1] < δ / INR (S n) /\
        Abs [f [x0] - f [y1]] >= ε0`}).
      { assert (J1 : δ / INR (S n) > 0).
        { apply Rdiv_lt_0_compat; try lra.
          apply lt_0_INR. apply Nat.lt_0_succ. }
        apply H10 in J1 as [x1 [x2 J2]].
        exists [x1, x2]. apply AxiomII'.
        assumption. }
      apply Axiomc with (a := ([0, 0])) in I2.
      rewrite <- I1 in I2. applyAxiomII' I2.
      apply I2. }
    clear H10 H20 H19 H18 H17 H14 H13 H12 H11 xy.
    assert (H22 : 0 < δ). lra.
    assert (H23 : IsSeq {` λ n s, s = x[n] - y[n] `}).
    { split.
      - intros x1 y1 z1 J1 J2.
        applyAxiomII' J1; applyAxiomII' J2.
        rewrite J2; assumption.
      - apply AxiomI; intros n;
        split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII. exists (x[n] - y[n]).
          apply AxiomII'. reflexivity. }
    assert (H24 : ∀ n, {` λ n s, s = x[n] - y[n] `}[n]
      = x[n] - y[n]).
    { intros n. apply f_x; try apply H23.
      apply AxiomII'. reflexivity. }
    assert (H25 : limit_seq {` λ n s, s = x[n] - y[n] `} 0).
    { split; auto. intros ε I1.
      generalize (Archimedes ε δ I1 H22).
      intros [N I2]. exists N. intros n I3.
      rewrite H24. rewrite Rminus_0_r.
      generalize (H21 n). intros [I4 [I5 [I6 I7]]].
      assert (I8 : INR N < INR (S n)).
      { apply lt_INR. apply Nat.lt_lt_succ_r. assumption. }
      apply Rmult_lt_compat_r with (r := ε)
        in I8; auto.
      assert (I9 : 0 < INR (S n)).
      { apply lt_0_INR. apply Nat.lt_0_succ. }
      assert (I10 : δ / INR (S n) < ε).
      { apply Rmult_lt_reg_r with (r := INR (S n)); auto.
        assert (I11 : δ / INR (S n) * INR (S n) = δ).
        { field. lra. }
        rewrite I11. rewrite Rmult_comm. lra. }
      lra. }
    assert (H26 : BoundedSeq x).
    { split; auto.
      destruct (Rlt_or_le a 0) as [I1 | I1].
      - destruct (Rlt_or_le b 0) as [J1 | J1].
        + exists (-a). intros n.
          generalize (H21 n); intros [J2 [J3 [J4 J5]]].
          applyAxiomII J2. assert (J6 : x[n] < 0). lra.
          rewrite Abs_lt; auto. lra.
        + destruct (Rlt_or_le (-a) b) as [J6 | J6].
          * exists b. intros n.
            generalize (H21 n); intros [J2 [J3 [J4 J5]]].
            applyAxiomII J2. apply Abs_le_R.
            lra.
          * exists (-a). intros n.
            generalize (H21 n); intros [J2 [J3 [J4 J5]]].
            applyAxiomII J2. apply Abs_le_R.
            lra.
      - exists b. intros n.
        generalize (H21 n); intros [J2 [J3 [J4 J5]]].
        applyAxiomII J2. apply Abs_le_R. lra. }
    apply Theorem2_10 in H26 as
      [xk [[H26 [H27 [u [H28 [H29 H30]]]]] [x0 H31]]].
    assert (H32 : ∃ yk, yk = {` λ n s, s = y[u \[ n \]] `}).
    { exists {` λ n s, s = y[u \[ n \]] `}.
      reflexivity. }
    destruct H32 as [yk H32].
    assert (H33 : IsSeq yk).
    { rewrite H32. split.
      - intros x1 y1 z1 I1 I2.
        applyAxiomII' I1; applyAxiomII' I2.
        rewrite I2. assumption.
      - apply AxiomI; intros n;
        split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII.
          exists (y[u \[ n \]]).
          apply AxiomII'. reflexivity. }
    assert (H34 : ∀ n, yk[n] = y[u \[ n \]]).
    { intros n. apply f_x; try apply H33.
      rewrite H32. apply AxiomII'.
      reflexivity. }
    assert (H35 : limit_seq yk x0).
    { split; auto. intros ε I1.
      assert (I2 : ε/2 > 0). lra.
      apply H31 in I2 as I3.
      destruct I3 as [N1 I3].
      apply H25 in I2 as I4.
      destruct I4 as [N2 I4].
      generalize (Max_nat_2 N1 N2).
      intros [N [I5 I6]].
      exists N. intros n I7.
      assert (I8 : (n > N1)%nat).
      { eapply Nat.lt_trans; eauto. }
      assert (I9 : (n > N2)%nat).
      { eapply Nat.lt_trans; eauto. }
      assert (I10 : Abs [yk[n] - xk[n]] < ε / 2).
      { rewrite H30; rewrite H34.
        assert (J1 : (u\[n\] > N2)%nat).
        { assert (K1 : (n <= u\[n\])%nat).
          { apply fn_ge_n; auto. }
          eapply Nat.lt_le_trans; eauto. }
        apply I4 in J1. rewrite H24 in J1.
        rewrite Rminus_0_r in J1.
        assert (J2 : y [u \[ n \]] - x [u \[ n \]]
          = - (x [u \[ n \]] - y [u \[ n \]])).
        field. rewrite J2. rewrite <- Abs_eq_neg.
        assumption. }
      apply I3 in I8.
      assert (I11 : yk[n] - x0 = yk[n] - xk[n] + (xk[n] - x0)).
      field. rewrite I11.
      generalize (Abs_plus_le (yk[n] - xk[n]) (xk[n] - x0)).
      intros I12. lra. }
    assert (H36 : ∀ n, a <= xk[n] <= b).
    { intros n. rewrite H30. generalize (H21 u\[n\]).
      intros [I1 [I2 [I3 I4]]].
      applyAxiomII I1. lra. }
    assert (H37 : a <= x0 <= b).
    { split.
      - apply Theorem2_5_1 with (x := xk); auto.
        exists O. intros n I1. apply H36.
      - apply Theorem2_5_2 with (x := xk); auto.
        exists O. intros n I1. apply H36. }
    assert (H38 : limit_seq {` λ n v, v = f[xk[n]] `} f[x0]
      /\ limit_seq {` λ n v, v = f[yk[n]] `} f[x0]).
    { destruct H37 as [I1 I2].
      assert (I0 : ran[ xk] ⊂ dom[ f]).
      { intros xn K1. applyAxiomII K1.
        destruct K1 as [n K1].
        apply H6. apply f_x in K1; try apply H27.
        rewrite <- K1. apply AxiomII.
        generalize (H36 n). lra. }
      assert (I3 : ran[ yk] ⊂ dom[ f]).
      { intros yn K1. applyAxiomII K1.
        destruct K1 as [n K1].
        apply H6. apply f_x in K1; try apply H33.
        rewrite <- K1. rewrite H34.
        generalize (H21 u\[n\]); intros K2.
        apply K2. }
      destruct I1 as [I1 | I1].
      - destruct I2 as [I2 | I2].
        + assert (J1 : a < x0 < b). lra.
          apply H0 in J1 as [J1 J2].
          generalize J1. intros J3.
          applyAxiomII J1. destruct J1 as [y0 J1].
          apply f_x in J1; try apply J2.
          rewrite J1 in *. split;
          apply Theorem3_8' with (x0 := x0); auto.
        + rewrite I2 in *. generalize H3. intros J1.
          applyAxiomII J1. destruct J1 as [fb J1].
          apply f_x in J1; auto. rewrite J1 in *.
          split; apply Theorem3_8_2' with (x0 := b); auto.
          * intros n. apply H36.
          * intros n. rewrite H34.
            generalize (H21 u\[n\]).
            intros [K1 [K2 K3]].
            applyAxiomII K2. apply K2.
      - rewrite <- I1 in *. generalize H1. intros J1.
        applyAxiomII J1. destruct J1 as [fa J1].
        apply f_x in J1; auto. rewrite J1 in *.
        split; apply Theorem3_8_1' with (x0 := a); auto.
        * intros n. apply H36.
        * intros n. rewrite H34.
          generalize (H21 u\[n\]).
          intros [K1 [K2 K3]].
          applyAxiomII K2. lra. }
    destruct H38 as [H38 H39].
    assert (H40 : ∀ n, {` λ n v,
      v = f[xk[n]] `}[n] = f[xk[n]]).
    { intros n. apply f_x; try apply H38.
      apply AxiomII'. reflexivity. }
    assert (H41 : ∀ n, {` λ n v,
      v = f[yk[n]] `}[n] = f[yk[n]]).
    { intros n. apply f_x; try apply H39.
      apply AxiomII'. reflexivity. }
    assert (H42 : IsSeq {` λ n v,
      v = Abs[f[xk[n]] - f[yk[n]]] `}).
    { split.
      - intros x1 y1 z1 J1 J2.
        applyAxiomII' J1; applyAxiomII' J2.
        rewrite J2; assumption.
      - apply AxiomI; intros n;
        split; intro I1.
        + apply AxiomII. reflexivity.
        + apply AxiomII.
          exists (Abs[f[xk[n]] - f[yk[n]]]).
          apply AxiomII'. reflexivity. }
    assert (H43 : ∀ n, {` λ n v,
      v = Abs[f[xk[n]] - f[yk[n]]] `}[n]
      = Abs[f[xk[n]] - f[yk[n]]]).
    { intros n. apply f_x; try apply H42.
      apply AxiomII'. reflexivity. }
    assert (H44 : limit_seq {` λ n v,
      v = Abs[f[xk[n]] - f[yk[n]]] `} 0).
    { split; auto. intros ε I1.
      assert (I4 : ε/2 > 0). lra.
      apply H38 in I4 as I2.
      destruct I2 as [N1 I2].
      apply H39 in I4 as I3.
      destruct I3 as [N2 I3].
      generalize (Max_nat_2 N1 N2).
      intros [N [I5 I6]].
      exists N. intros n I7.
      assert (I8 : (n > N1)%nat).
      { eapply Nat.lt_trans; eauto. }
      assert (I9 : (n > N2)%nat).
      { eapply Nat.lt_trans; eauto. }
      apply I2 in I8. apply I3 in I9.
      rewrite H40 in I8. rewrite H41 in I9.
      rewrite H43. rewrite Rminus_0_r.
      rewrite Abs_ge; try apply Abs_Rge0.
      assert (I10 : f[xk[n]] - f[yk[n]] =
        (f[xk[n]] - f[x0]) - (f[yk[n]] - f[x0])).
      lra. rewrite I10.
      generalize (Abs_minus_le (f[xk[n]] - f[x0])
        (f[yk[n]] - f[x0])). intros I11.
      lra. }
    assert (H45 : ε0 <= 0).
    { apply Theorem2_5_1 with (x := {` λ n v,
        v = Abs[f[xk[n]] - f[yk[n]]] `}); auto.
      exists O. intros n I1.
      rewrite H43. rewrite H30; rewrite H34.
      apply Rge_le. apply H21. }
    lra.
  - intros ε H8. exists 1.
    split; [lra | intros x1 x2 H9 H10 H11].
    applyAxiomII H9; applyAxiomII H10.
    assert (H12 : x1 = x2). lra.
    rewrite H12 in *.
    apply Abs_R. lra.
  - intros ε H8. exists 1.
    split; [lra | intros x1 x2 H9 H10 H11].
    applyAxiomII H9; applyAxiomII H10.
    lra.
Qed.

End A4_2.

Export A4_2.
