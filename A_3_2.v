Require Export A_3_1.

Module A3_2.

(* 3.2 函数极限的性质 *)

(* 定理3.2 唯一性 *)
Theorem Theorem3_2 : ∀ (f : Fun) (x0 A B : R),
  limit f x0 A -> limit f x0 B -> A = B.
Proof.
  intros f x0 A B H0 H1.
  assert (H2 : ∀ ε : R, ε > 0 -> Abs[A-B] < 2 * ε).
  { intros ε I1. destruct H0 as [H0 [δ1' [I2 [I3 I4]]]].
    destruct H1 as [H1 [δ2' [I5 [I6 I7]]]]. apply I4 in I1 as I8.
    apply I7 in I1 as I9. destruct I8 as [δ1 [I10 I11]].
    destruct I9 as [δ2 [I12 I13]].
    assert (I14 : ∃ x, 0 < Abs [x - x0] < δ1 /\ 0 < Abs [x - x0] < δ2).
    { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
      - exists (x0 + δ1 / 2). assert (J2 : x0 + δ1 / 2 - x0 = δ1 / 2). field.
        rewrite J2. assert (J3 : δ1 / 2 > 0). lra. rewrite Abs_gt; auto.
        repeat split; lra.
      - exists (x0 + δ2 / 2). assert (J2 : x0 + δ2 / 2 - x0 = δ2 / 2). field.
        rewrite J2. assert (J3 : δ2 / 2 > 0). lra. rewrite Abs_gt; auto.
        repeat split; lra. }
    destruct I14 as [x [I14 I15]]. apply I11 in I14.
    apply I13 in I15. generalize (Abs_minus_le (f[x] - A) (f[x] - B)).
    intro I16. assert (I17 : f[x] - A - (f[x] - B) = -(A-B)). field.
    rewrite I17 in I16. rewrite <- Abs_eq_neg in I16. lra. }
  apply NNPP. intro H3. assert (H4 : A-B <> 0). lra. apply Abs_not_eq_0 in H4.
  assert (H5 : Abs[A - B] / 4 > 0). lra. apply H2 in H5. lra.
Qed.

(* 定理3.3 局部有界性 *)
Theorem Theorem3_3 : ∀ (f : Fun) (x0 : R), (∃ A, limit f x0 A) ->
  (∃ δ, δ > 0 /\ IntervalBoundedFun f (Neighbor0 x0 δ)).
Proof.
  intros f x0 H0. destruct H0 as [A H0].
  destruct H0 as [H0 [δ' [I2 [I3 I4]]]].
  generalize (I4 1 Rlt_0_1). intro I5.
  destruct I5 as [δ [I5 I6]]. exists δ.
  split; try lra. repeat split; auto.
  - intros x I7. applyAxiomII I7.
    apply I3. apply AxiomII. lra.
  - exists (Abs[A] + 1).
    intros x I7. applyAxiomII I7. apply I6 in I7.
    generalize (Abs_abs_minus' (f[x]) A).
    intro I8. lra.
Qed.

Theorem Theorem3_3' : ∀ (f : Fun) (x0 : R), (∃ A, limit f x0 A) ->
  (∃ δ, δ > 0 /\ (∃ M, M > 0 /\
    (∀ x, x ∈ (Neighbor0 x0 δ) -> Abs[f[x]] <= M))).
Proof.
  intros f x0 H0. destruct H0 as [A H0].
  destruct H0 as [H0 [δ' [I2 [I3 I4]]]].
  generalize (I4 1 Rlt_0_1). intro I5.
  destruct I5 as [δ [I5 I6]]. exists δ.
  split; try lra.
  exists (Abs[A] + 1). split.
  - generalize (Abs_Rge0 A). intro I7. lra.
  - intros x I7. applyAxiomII I7. apply I6 in I7.
    generalize (Abs_abs_minus' (f[x]) A).
    intro I8. lra.
Qed.

(* 定理3.4 局部保号性 *)
Theorem Theorem3_4_1 : ∀ (f : Fun) (x0 A : R), limit f x0 A -> A > 0 ->
  (∀ r, 0 < r < A -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (Neighbor0 x0 δ) -> 0 < r < f[x]))).
Proof.
  intros f x0 A H0 H1 r H2. destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : A - r > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  apply H8 in H9 as H10. apply Abs_R in H10. lra.
Qed.

Theorem Theorem3_4_2 : ∀ (f : Fun) (x0 A : R), limit f x0 A -> A < 0 ->
  (∀ r, 0 < r < -A -> (∃ δ, δ > 0 /\
    (∀ x, x ∈ (Neighbor0 x0 δ) -> f[x] < -r < 0))).
Proof.
  intros f x0 A H0 H1 r H2. destruct H0 as [H0 [δ' [H3 [H4 H5]]]].
  assert (H6 : -(A + r) > 0). lra. apply H5 in H6 as H7.
  destruct H7 as [δ [H7 H8]]. exists δ. split; try lra.
  intros x H9. applyAxiomII H9.
  apply H8 in H9 as H10. apply Abs_R in H10. lra.
Qed.

(* 定理3.5 保不等式性 *)
Theorem Theorem3_5 : ∀ (f g : Fun) (x0 A B : R), limit f x0 A -> limit g x0 B
  -> (∃ δ', δ' > 0 /\ (∀ x, x ∈ (Neighbor0 x0 δ') -> f[x] <= g[x]))
  -> A <= B.
Proof.
  intros f g x0 A B H0 H1 [δ' [H2 H10]].
  destruct H0 as [H0 [δ1' [H3 [H4 H5]]]].
  destruct H1 as [H1 [δ2' [H6 [H7 H8]]]].
  assert (H9 : ∀ ε, ε > 0 -> A < B + 2 * ε).
  { intros ε I1. apply H5 in I1 as I2. destruct I2 as [δ1 [I2 I3]].
    apply H8 in I1 as I4. destruct I4 as [δ2 [I4 I5]].
    assert (I6 : ∃ δ, δ > 0 /\ δ <= δ' /\ δ <= δ1 /\ δ <= δ2).
    { destruct (Rlt_or_le δ' δ1) as [J1 | J1].
      - destruct (Rlt_or_le δ' δ2) as [J2 | J2];
          [exists δ' | exists δ2]; repeat split; lra.
      - destruct (Rlt_or_le δ1 δ2) as [J2 | J2];
          [exists δ1 | exists δ2]; repeat split; lra. }
    destruct I6 as [δ [I6 [I7 [I8 I9]]]].
    assert (I10 : ∃ x, x ∈ (Neighbor0 x0 δ') /\ 0 < Abs [x - x0] < δ1 /\
      0 < Abs [x - x0] < δ2).
    { exists (x0 + δ/2). assert (J1 : x0 + δ / 2 - x0 > 0). lra.
      rewrite Abs_gt; auto. split; [idtac | split]; try lra.
      apply AxiomII. rewrite Abs_gt; auto. lra. }
    destruct I10 as [x [I10 [I11 I12]]].
    apply H10 in I10. apply I3 in I11. apply I5 in I12.
    apply Abs_R in I11. apply Abs_R in I12. lra. }
  apply Rnot_gt_le. intro H11.
  assert (H12 : (A-B)/4 > 0). lra. apply H9 in H12 as H13. lra.
Qed.

(* 定理3.6 迫敛性 *)
Theorem Theorem3_6 : ∀ (f g h : Fun) (x0 A : R),
  Function h -> limit f x0 A -> limit g x0 A
  -> (∃ δ', δ' > 0 /\ (Neighbor0 x0 δ') ⊂ dom[h] /\
        (∀ x, x ∈ (Neighbor0 x0 δ') -> f[x] <= h[x] <= g[x]))
  -> limit h x0 A.
Proof.
  intros f g h x0 A H0 H1 H2 [δ' [H3 [H4 H5]]]. unfold limit. split; auto.
  exists δ'. repeat split; auto. intros ε H6.
  destruct H1 as [H1 [δ1' [H7 [H8 H9]]]].
  destruct H2 as [H2 [δ2' [H10 [H11 H12]]]].
  apply H12 in H6 as H14. apply H9 in H6 as H13.
  destruct H13 as [δ1 [H15 H16]]. destruct H14 as [δ2 [H17 H18]].
  assert (H19 : ∃ δ, δ > 0 /\ δ < δ' /\ δ < δ1 /\ δ < δ2).
  { destruct (Rlt_or_le δ' δ1) as [J1 | J1].
    - destruct (Rlt_or_le δ' δ2) as [J2 | J2];
        [exists (δ'/2) | exists (δ2/2)]; repeat split; lra.
    - destruct (Rlt_or_le δ1 δ2) as [J2 | J2];
        [exists (δ1/2) | exists (δ2/2)]; repeat split; lra. }
  destruct H19 as [δ [H19 [H20 [H21 H22]]]].
  exists δ. split; try lra. intros x H23.
  assert (H24 : x ∈ (Neighbor0 x0 δ')).
  { apply AxiomII. lra. }
  assert (H25 : 0 < Abs [x - x0] < δ1). lra.
  assert (H26 : 0 < Abs [x - x0] < δ2). lra.
  apply H5 in H24. apply H16 in H25. apply H18 in H26.
  apply Abs_R. apply Abs_R in H25. apply Abs_R in H26. lra.
Qed.

(* 定理3.7 四则运算 *)
Theorem Theorem3_7_1 : ∀ (f g : Fun) (x0 A B : R),
  limit f x0 A -> limit g x0 B
  -> limit (f \+ g) x0 (A+B).
Proof.
  intros f g x0 A B [H0 [δ1' [H1 [H2 H3]]]] [H4 [δ2' [H5 [H6 H7]]]].
  assert (H8 : ∃ h, h = f \+ g).
  { exists {` λ x y, x ∈ dom[f] /\ x ∈ dom[g] /\
    y = f[x] + g[x] `}; auto. }
  destruct H8 as [h H8]. rewrite <- H8.
  assert (H9 : Function h).
  { unfold Function. rewrite H8. intros x y z I1 I2.
    applyAxiomII' I1. applyAxiomII' I2. destruct I2 as [I2 [I3 I4]].
    rewrite I4. apply I1. }
  split; auto.
  assert (H10 : ∃ δ', δ' > 0 /\ δ' <= δ1' /\ δ' <= δ2').
  { destruct (Rlt_or_le δ1' δ2') as [I1 | I1];
      [exists δ1' | exists δ2']; lra. }
  destruct H10 as [δ' [H10 [H11 H12]]]. exists δ'.
  assert (H13 : dom[h] = dom[f] ∩ dom[g]).
  { apply AxiomI. intro x; split; intro I1.
    - applyAxiomII I1. destruct I1 as [y I1]. apply AxiomII.
      rewrite H8 in I1. applyAxiomII' I1. split; apply I1.
    - apply AxiomII. exists (f[x] + g[x]). rewrite H8.
      apply AxiomII'. applyAxiomII I1. destruct I1 as [I1 I2].
      repeat split; auto. }
  split; auto. split.
  - intros z I1. applyAxiomII I1. rewrite H13. destruct I1 as [I1 I2].
    apply AxiomII. split.
    + apply H2. apply AxiomII. split; auto. lra.
    + apply H6. apply AxiomII. split; auto. lra.
  - intros ε H14. assert (H30 : ε / 2 > 0). lra.
    apply H7 in H30 as H16; apply H3 in H30 as H15.
    destruct H15 as [δ1 [H15 H17]].
    destruct H16 as [δ2 [H16 H18]].
    assert (H19 : ∃ δ, δ > 0 /\ δ < δ' /\ δ < δ1 /\ δ < δ2).
    { destruct (Rlt_or_le δ' δ1) as [J1 | J1].
      - destruct (Rlt_or_le δ' δ2) as [J2 | J2];
          [exists (δ'/2) | exists (δ2/2)]; repeat split; lra.
      - destruct (Rlt_or_le δ1 δ2) as [J2 | J2];
          [exists (δ1/2) | exists (δ2/2)]; repeat split; lra. }
    destruct H19 as [δ [H19 [H20 [H21 H22]]]].
    exists δ. split; try lra. intros x H23.
    assert (H24 : 0 < Abs [x - x0] < δ1). lra.
    assert (H25 : 0 < Abs [x - x0] < δ2). lra.
    apply H17 in H24. apply H18 in H25.
    assert (H26 : h[x] = f[x] + g[x]).
    { apply f_x; auto. rewrite H8. apply AxiomII'. repeat split; auto.
      - apply H2. apply AxiomII. lra.
      - apply H6. apply AxiomII. lra. }
    rewrite H26. generalize (Abs_plus_le (f[x]-A) (g[x]-B)). intro H27.
    assert (H28 : f[x] + g[x] - (A + B) = f[x] - A + (g[x] - B)). field.
    rewrite H28. lra.
Qed.

Theorem Theorem3_7_2' : ∀ (f : Fun) (x0 A : R),
  limit f x0 A -> limit (f \* (-1)) x0 (-A).
Proof.
  intros f x0 A H0. destruct H0 as [H0 [δ' [H2 [H3 H4]]]].
  assert (H5 : Function (f \* -1)).
  { unfold Function. intros x y z I1 I2.
    applyAxiomII' I1. applyAxiomII' I2.
    destruct I2 as [I2 I3]. rewrite I3.
    apply I1. }
  unfold limit. split; auto. exists (δ').
  assert (H6 : Neighbor0 x0 δ' ⊂ dom[ f \* -1]).
  { intros x I1. apply AxiomII. exists (-f[x]).
    apply AxiomII'. split; auto. field. }
  repeat split; auto.
  intros ε H7. apply H4 in H7 as H8.
  destruct H8 as [δ [H9 H10]]. exists δ. split; auto.
  intros x H11. apply H10 in H11 as H12.
  apply Abs_R. apply Abs_R in H12.
  assert (H13 : (f \* -1)[x] = -f[x]).
  { apply f_x; auto. apply AxiomII'. split; try field.
    apply H3. apply AxiomII. lra. }
  rewrite H13. lra.
Qed.

Theorem Theorem3_7_2 : ∀ (f g : Fun) (x0 A B : R),
  limit f x0 A -> limit g x0 B
  -> limit (f \- g) x0 (A-B).
Proof.
  intros f g x0 A B H0 H1.
  apply Theorem3_7_2' in H1 as H2.
  assert (H3 : (f \- g) = (f \+ (g \* -1))).
  { apply AxiomI.
    assert (H3 : ∀ x, x ∈ dom[ g] -> (g \* -1) [x] = -g[x]).
    { intros x J1. apply f_x; try apply H2. apply AxiomII'.
      split; [auto | field]. }
    intro z; split; intro I1.
    - applyAxiomII I1. destruct I1 as [x [y [I1 I2]]].
      rewrite I1. apply AxiomII'. destruct I2 as [I2 [I3 I4]].
      split; auto. split.
      + apply AxiomII. exists (-g[x]). apply AxiomII'.
        split; [auto | field].
      + rewrite H3; auto.
    - applyAxiomII I1. destruct I1 as [x [y [I1 I2]]].
      rewrite I1. apply AxiomII'.
      destruct I2 as [I2 [I3 I4]].
      split; auto.
      assert (I5 : x ∈ dom[ g]).
      { applyAxiomII I3. destruct I3 as [y' I3].
        applyAxiomII' I3. apply I3. }
      split; auto. rewrite H3 in I4; auto. }
  rewrite H3. unfold Rminus. apply Theorem3_7_1; auto.
Qed.

Theorem Theorem3_7_3 : ∀ (f g : Fun) (x0 A B : R),
  limit f x0 A -> limit g x0 B
  -> limit (f ** g) x0 (A*B).
Proof.
  intros f g x0 A B [H0 [δ1' [H1 [H2 H3]]]] [H4 [δ2' [H5 [H6 H7]]]].
  assert (H14 : (∃ δ3', δ3' >0 /\ (∃ M, M > 0 /\
    (∀ x, x ∈ (Neighbor0 x0 δ3') -> Abs[g[x]] <= M)))).
  { apply Theorem3_3'. exists B. split; auto. exists δ2'.
    repeat split; auto. }
  destruct H14 as [δ3' [H14 H15]].
  assert (H8 : ∃ δ', δ' > 0 /\ δ' <= δ1' /\ δ' <= δ2' /\ δ' <= δ3').
  { destruct (Rlt_or_le δ1' δ2') as [J1 | J1].
    - destruct (Rlt_or_le δ1' δ3') as [J2 | J2];
        [exists (δ1'/2) | exists (δ3'/2)]; repeat split; lra.
    - destruct (Rlt_or_le δ2' δ3') as [J2 | J2];
        [exists (δ2'/2) | exists (δ3'/2)]; repeat split; lra. }
  destruct H8 as [δ' [H8 [H9 [H10 H11]]]].
  assert (H12 : Function (f ** g)).
  { unfold Function. intros x y z I1 I2.
    applyAxiomII' I1. applyAxiomII' I2.
    destruct I2 as [I2 [I3 I4]].
    rewrite I4. apply I1. }
  split; auto. exists (δ'). split; auto.
  assert (H13 : Neighbor0 x0 δ' ⊂ dom[ f ** g]).
  { intros x I1. apply AxiomII. exists (f[x]*g[x]).
    apply AxiomII'. repeat split; [apply H2 | apply H6];
    apply AxiomII; applyAxiomII I1; lra. }
  split; auto.
  unfold BoundedFun in H15. destruct H15 as [M H15].
  intros ε H16. destruct H15 as [H15 H17].
  generalize (Abs_Rge0 A). intro H18.
  assert (H19 : ε / (M+Abs[A]) > 0).
  { apply  Rmult_gt_0_compat; auto.
    apply Rinv_0_lt_compat. lra. }
  apply H7 in H19 as H21. apply H3 in H19 as H20.
  destruct H20 as [δ1 [H22 H23]].
  destruct H21 as [δ2 [H24 H25]].
  assert (H26 : ∃ δ, δ > 0 /\ δ <= δ1 /\ δ <= δ2 /\ δ < δ').
  { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
    - destruct (Rlt_or_le δ1 δ') as [J2 | J2];
        [exists (δ1/2) | exists (δ'/2)]; repeat split; lra.
    - destruct (Rlt_or_le δ2 δ') as [J2 | J2];
        [exists (δ2/2) | exists (δ'/2)]; repeat split; lra. }
  destruct H26 as [δ [H26 [H27 [H28 H29]]]].
  exists δ. split; [lra | idtac]. intros x H30.
  assert (H31 : 0 < Abs [x - x0] < δ1). lra.
  assert (H32 : 0 < Abs [x - x0] < δ2). lra.
  assert (H33 : (f ** g)[x] = f[x]*g[x]).
  { apply f_x; auto. apply AxiomII'. repeat split;
    [apply H2 | apply H6]; apply AxiomII; lra. }
  rewrite H33. clear H33. apply H23 in H31 as H33.
  apply H25 in H32 as H34.
  assert (H35 : f[x]*g[x] - A*B =
    (f[x]-A)*g[x] + A*(g[x]-B)). field.
  rewrite H35.
  generalize (Abs_plus_le ((f[x]-A)*g[x]) (A*(g[x]-B))).
  intro H36. generalize (Abs_mult (f[x]-A) (g[x])).
  intro H37. generalize (Abs_mult (A) (g[x]-B)).
  intro H38. rewrite H37 in H36. rewrite H38 in H36.
  apply Rle_lt_trans with (r2 := Abs[f[x]-A]*Abs[g[x]] +
    Abs[A]*Abs[g[x]-B]); auto.
  assert (H39 : Abs[g[x]] <= M).
  { apply H17. apply AxiomII. lra. }
  assert (H40 : ε = (ε/(M + Abs[A])) * M + Abs[A]*(ε/(M + Abs[A]))).
  field; lra. rewrite H40. apply Rplus_lt_le_compat.
  - destruct H39 as [H39 | H39].
    + apply Rmult_le_0_lt_compat; auto;
      apply Rge_le; apply Abs_Rge0.
    + rewrite H39. apply Rmult_lt_compat_r; auto.
  - apply Rmult_le_compat_l; lra.
Qed.

Theorem Theorem3_7_4' : ∀ (f : Fun) (x0 A : R),
  limit f x0 A -> A <> 0
  -> limit (1 /// f) x0 (/A).
Proof.
  intros f x0 A H0 H1.
  assert (H2 : ∃ δ1', δ1' > 0 /\ (∀ x, x ∈ (Neighbor0 x0 δ1')
    -> f[x] <> 0)).
  { apply Rdichotomy in H1 as I1.
    destruct I1 as [I1 | I1].
    - generalize (Theorem3_4_2 f x0 A H0 I1).
      intro I2. assert (I3 : 0 < -A/2 < -A). lra.
      apply I2 in I3 as I4.
      destruct I4 as [δ [I4 I5]].
      exists δ. split; auto. intros x I6.
      apply I5 in I6. lra.
    - generalize (Theorem3_4_1 f x0 A H0 I1).
      intro I2. assert (I3 : 0 < A/2 < A). lra.
      apply I2 in I3 as I4.
      destruct I4 as [δ [I4 I5]].
      exists δ. split; auto. intros x I6.
      apply I5 in I6. lra. }
  destruct H2 as [δ1' [H2 H3]].
  assert (H4 : ∃ δ1, δ1 > 0 /\ (∀ x, x ∈ (Neighbor0 x0 δ1)
    -> Abs[f[x]] > Abs[A]/2)).
  { apply Rdichotomy in H1 as I1.
    destruct I1 as [I1 | I1].
    - generalize (Theorem3_4_2 f x0 A H0 I1).
      intro I2. assert (I3 : 0 < -A/2 < -A). lra.
      apply I2 in I3 as I4. destruct I4 as [δ1 [I4 I5]].
      exists δ1. split; auto. intros z I6.
      apply I5 in I6. assert (I7 : f[z] < 0). lra.
      repeat rewrite Abs_lt; auto. lra.
    - generalize (Theorem3_4_1 f x0 A H0 I1).
      intro I2. assert (I3 : 0 < A/2 < A). lra.
      apply I2 in I3 as I4. destruct I4 as [δ1 [I4 I5]].
      exists δ1. split; auto. intros z I6.
      apply I5 in I6. assert (I7 : f[z] > 0). lra.
      repeat rewrite Abs_gt; auto. lra. }
  destruct H4 as [δ1 [H5 H6]].
  assert (H7 : ∀ ε, ε > 0 -> ∃ δ, δ > 0
    /\ Neighbor0 x0 δ ⊂ dom[ f]
    /\ (∀ x, x ∈ (Neighbor0 x0 δ)
    -> Abs[1/f[x]-1/A] < 2*ε/(A*A))).
  { intros ε I1. destruct H0 as [H0 [δ2' [I2 [I3 I4]]]].
    apply I4 in I1 as I5.
    destruct I5 as [δ2 [I6 I7]].
    assert (I8 : ∃ δ, δ > 0 /\ δ < δ1' /\ δ < δ1 /\ δ < δ2).
    { destruct (Rlt_or_le δ1' δ1) as [J1 | J1].
      - destruct (Rlt_or_le δ1' δ2) as [J2 | J2];
          [exists (δ1'/2) | exists (δ2/2)]; repeat split; lra.
      - destruct (Rlt_or_le δ1 δ2) as [J2 | J2];
          [exists (δ1/2) | exists (δ2/2)]; repeat split; lra. }
    destruct I8 as [δ [I8 [I9 [I10 I11]]]].
    exists δ.
    assert (I12 : Neighbor0 x0 δ ⊂ dom[ f]).
    { intros x J1. apply I3. apply AxiomII.
      applyAxiomII J1. lra. }
    repeat split; auto.
    intros x I13. assert (I14 : f[x] <> 0).
    { apply H3. apply AxiomII.
      applyAxiomII I13. lra. }
    assert (I15 : 1/f[x] - 1/A = - ((f[x]-A)/(f[x]*A))).
    { field. split; auto. }
    rewrite I15. rewrite <- Abs_eq_neg.
    assert (I16 : f[x]*A <> 0).
    { apply Rmult_integral_contrapositive_currified; auto. }
    rewrite Abs_div; auto.
    rewrite Abs_mult. clear I15.
    assert (I17 : Abs[f[x]] > Abs[A] / 2).
    { apply H6. apply AxiomII. applyAxiomII I13.
      lra. }
    assert (I18 : Abs[A] > 0).
    { apply Abs_not_eq_0. apply H1. }
    assert (I19 : Abs[f[x]]*Abs[A] > (Abs[A]/2)*Abs[A]).
    { apply Rmult_gt_compat_r; auto. }
    assert (I20 : Abs[A]/2 * Abs[A] = (A*A) / 2).
    { apply Rdichotomy in H1.
      destruct H1 as [H1 | H1].
      - rewrite Abs_lt; auto. field.
      - rewrite Abs_gt; auto. field. }
    assert (I21 : 0 < (Abs[A]/2*Abs[A]) * (Abs[f[x]]*Abs[A])).
    { apply Rmult_gt_0_compat; apply Rmult_gt_0_compat; lra. }
    apply Rinv_lt_contravar in I19; auto.
    clear I21. rewrite I20 in I19.
    assert (I21 : 0 <= Abs[f[x]-A]).
    { apply Rge_le. apply Abs_Rge0. }
    apply Rlt_le in I19 as I22.
    apply Rmult_le_compat_l with
      (r := Abs[f[x]-A]) in I22; auto.
    assert (I23 : A*A/2 > 0).
    { rewrite <- I20. apply Rmult_gt_0_compat; lra. }
    apply Rle_lt_trans with
      (r2 := Abs[f[x]-A] * /(A*A/2)); auto.
    assert (I24 : Abs[f[x]-A] < ε).
    { apply I7. applyAxiomII I13. lra. }
    apply Rinv_0_lt_compat in I23.
    apply Rmult_lt_compat_r with
      (r := / (A*A/2)) in I24; auto.
    assert (I25 : ε * /(A * A / 2) = 2 * ε / (A * A)).
    { field; auto. }
    rewrite <- I25. assumption. }
  unfold limit. assert (H8 : Function (1 /// f)).
  { unfold Function. intros x y z I1 I2.
    applyAxiomII' I1. applyAxiomII' I2.
    destruct I2 as [I2 [I3 I4]].
    rewrite I4. apply I1. }
  destruct H0 as [H0 [δ2' [H9 [H10 H11]]]].
  assert (H12 : ∃ δ', δ' > 0 /\ δ' <= δ1' /\ δ' <= δ2').
  { destruct (Rlt_or_le δ1' δ2') as [I1 | I1];
      [exists δ1' | exists δ2']; lra. }
  destruct H12 as [δ' [H13 [H14 H15]]].
  split; auto. exists δ'. repeat split; auto.
  - intros x I1. apply AxiomII. exists (1/f[x]).
    apply AxiomII'. repeat split;
    [apply H10 | apply H3]; apply AxiomII;
    applyAxiomII I1; lra.
  - intros ε H16. assert (H17 : (A*A) * ε / 2 > 0).
    { assert (I1 : A*A > 0).
      { apply Rdichotomy in H1.
        destruct H1 as [H1 | H1].
        - apply Ropp_gt_lt_0_contravar in H1 as I1.
          assert (I2 : (-A)*(-A) = A*A). field.
          rewrite <- I2. apply Rmult_gt_0_compat; auto.
        - apply Rmult_gt_0_compat; auto. }
      assert (I2 : A * A * ε / 2 = (A * A) * (ε / 2)).
      field. rewrite I2. apply Rmult_gt_0_compat; auto.
      lra. }
    apply H7 in H17 as H18.
    destruct H18 as [δ2 [H18 [H19 H20]]].
    assert (H21 : ∃ δ, δ > 0 /\ δ < δ2 /\ δ < δ').
    { destruct (Rlt_or_le δ2 δ') as [I1 | I1];
        [exists ((δ2)/2) | exists (δ'/2)]; lra. }
    destruct H21 as [δ [H21 [H22 H23]]].
    exists δ. split; try lra.
    intros x H24.
    assert (H25 : (1 /// f)[x] = 1/f[x]).
    { apply f_x; auto. apply AxiomII'.
      repeat split; auto.
      - apply H10. apply AxiomII. lra.
      - apply H3. apply AxiomII. lra. }
    rewrite H25.
    assert (H26 : 2 * (A * A * ε / 2) / (A * A) = ε).
    { field; auto. }
    rewrite H26 in H20.
    assert (H27 : /A = 1/A). field; auto.
    rewrite H27. apply H20.
    apply AxiomII. lra.
Qed.

Theorem Theorem3_7_4 : ∀ (f g : Fun) (x0 A B : R),
  limit f x0 A -> limit g x0 B -> B <> 0
  -> limit (f // g) x0 (A/B).
Proof.
  intros f g x0 A B H0 H1 H2.
  apply Theorem3_7_4' in H1 as H3; auto.
  assert (H4 : f // g = f ** (1 /// g)).
  { apply AxiomI.
    assert (I6 : ∀ x, x ∈ dom[g] -> g[x] <> 0
      -> (1 /// g)[x] = /g[x]).
    { intros x J1 J2. apply f_x; try apply H3. apply AxiomII'.
      repeat split; auto. field. auto. }
    intro z; split; intro I1.
    - applyAxiomII I1.
      destruct I1 as [x [y [I1 [I2 [I3 [I4 I5]]]]]].
      rewrite I1. apply AxiomII'. repeat split; auto.
      + apply AxiomII. exists (1/g[x]).
        apply AxiomII'. repeat split; auto.
      + rewrite I6; auto.
    - applyAxiomII I1.
      destruct I1 as [x [y [I1 [I2 [I3 I4]]]]].
      rewrite I1. apply AxiomII'.
      split; auto. applyAxiomII I3.
      destruct I3 as [y' I3]. applyAxiomII' I3.
      destruct I3 as [I3 [I5 I7]].
      rewrite I6 in I4; auto. }
  rewrite H4. apply Theorem3_7_3; auto.
Qed.

End A3_2.

Export A3_2.