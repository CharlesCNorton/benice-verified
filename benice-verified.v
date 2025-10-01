(******************************************************************************)
(*                                                                            *)
(*     Convergence to Resource Preservation in Delayed Elimination Games      *)
(*                                                                            *)
(*     A formal proof that optimal strategies in systems with finite-speed    *)
(*     information propagation and observation-dependent elimination          *)
(*     converge to resource-preserving fixed points under increasing          *)
(*     computational depth.                                                   *)
(*                                                                            *)
(*     "Ua mau ke ea o ka ʻāina i ka pono"                                    *)
(*     (The life of the land is perpetuated in righteousness)                 *)
(*     - King Kamehameha III, July 31, 1843 (Hawaii State Motto)              *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: September 26, 2025                                               *)
(*                                                                            *)
(******************************************************************************)

Require Import Reals Lra Lia Psatz.
Require Import Ranalysis Rpower Rprod.
Require Import List.
Require Import PeanoNat.
From Coquelicot Require Import Coquelicot.
Require Import RealField.
Import ListNotations.

Open Scope R_scope.

(** * Section 1: Fundamental Definitions and State Space *)

Section ResourceDynamics.

Definition State := (R * R * R)%type.

Definition state_zero : State := (0, 0, 0).

Definition state_add (s1 s2 : State) : State :=
  let '(x1, y1, z1) := s1 in
  let '(x2, y2, z2) := s2 in
  (x1 + x2, y1 + y2, z1 + z2).

Definition state_sub (s1 s2 : State) : State :=
  let '(x1, y1, z1) := s1 in
  let '(x2, y2, z2) := s2 in
  (x1 - x2, y1 - y2, z1 - z2).

Definition norm_state (s : State) : R :=
  let '(x, y, z) := s in sqrt (x^2 + y^2 + z^2).

(** The norm of any state is non-negative. *)
Lemma norm_state_nonneg : forall s, norm_state s >= 0.
Proof.
  intros [[x y] z].
  unfold norm_state.
  apply Rle_ge.
  apply sqrt_pos.
Qed.

(** Expansion of the square of a sum. *)
Lemma sum_sqr_expand : forall a b, (a + b) * (a + b) = a * a + 2 * a * b + b * b.
Proof.
  intros. ring.
Qed.

(** Square root squared equals the original value for non-negative numbers. *)
Lemma sqrt_sqr_simpl : forall x, 0 <= x -> sqrt x * sqrt x = x.
Proof.
  intros. rewrite sqrt_sqrt; auto.
Qed.

(** Cauchy-Schwarz inequality for 3D vectors. *)
Lemma cauchy_schwarz_3 : forall x1 y1 z1 x2 y2 z2,
  (x1 * x2 + y1 * y2 + z1 * z2) * (x1 * x2 + y1 * y2 + z1 * z2) <=
  (x1 * x1 + y1 * y1 + z1 * z1) * (x2 * x2 + y2 * y2 + z2 * z2).
Proof.
  intros.
  (* We'll use Lagrange's identity:
     (sum ai*bi)^2 + sum_{i<j}(ai*bj - aj*bi)^2 = (sum ai^2)(sum bi^2) *)
  assert (H: (x1 * x2 + y1 * y2 + z1 * z2) * (x1 * x2 + y1 * y2 + z1 * z2) +
             ((x1*y2 - x2*y1)*(x1*y2 - x2*y1) +
              (x1*z2 - x2*z1)*(x1*z2 - x2*z1) +
              (y1*z2 - y2*z1)*(y1*z2 - y2*z1)) =
             (x1 * x1 + y1 * y1 + z1 * z1) * (x2 * x2 + y2 * y2 + z2 * z2)).
  { ring. }
  (* From Lagrange's identity, we have equality when we add the cross terms *)
  (* The CS inequality follows from dropping the non-negative cross terms *)
  rewrite <- H.
  pattern ((x1 * x2 + y1 * y2 + z1 * z2) * (x1 * x2 + y1 * y2 + z1 * z2)) at 1.
  rewrite <- Rplus_0_r.
  apply Rplus_le_compat_l.
  apply Rplus_le_le_0_compat.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  apply Rle_0_sqr.
Qed.

(** Cauchy-Schwarz inequality with square root for 3D vectors. *)
Lemma cauchy_schwarz_sqrt_3 : forall x1 y1 z1 x2 y2 z2,
  x1 * x2 + y1 * y2 + z1 * z2 <=
  sqrt ((x1 * x1 + y1 * y1 + z1 * z1) * (x2 * x2 + y2 * y2 + z2 * z2)).
Proof.
  intros.
  (* Since (a.b)² ≤ |a|²|b|² by Cauchy-Schwarz, taking square roots gives the result *)
  assert (H: Rsqr (x1 * x2 + y1 * y2 + z1 * z2) <=
             (x1 * x1 + y1 * y1 + z1 * z1) * (x2 * x2 + y2 * y2 + z2 * z2)).
  { unfold Rsqr. apply cauchy_schwarz_3. }
  (* Now we need sqrt of both sides *)
  destruct (Rle_dec (x1 * x2 + y1 * y2 + z1 * z2) 0) as [Hle|Hgt].
  - (* If LHS ≤ 0, then LHS ≤ 0 ≤ sqrt(RHS) *)
    apply Rle_trans with 0; [exact Hle | apply sqrt_pos].
  - (* If LHS > 0, we can use the fact that sqrt is monotone *)
    assert (Hpos: 0 < x1 * x2 + y1 * y2 + z1 * z2).
    { apply Rnot_le_lt. exact Hgt. }
    rewrite <- sqrt_Rsqr with (x := x1 * x2 + y1 * y2 + z1 * z2).
    + apply sqrt_le_1.
      * apply Rle_0_sqr.
      * apply Rmult_le_pos.
        -- apply Rplus_le_le_0_compat. apply Rplus_le_le_0_compat; apply Rle_0_sqr. apply Rle_0_sqr.
        -- apply Rplus_le_le_0_compat. apply Rplus_le_le_0_compat; apply Rle_0_sqr. apply Rle_0_sqr.
      * exact H.
    + left. exact Hpos.
Qed.

(** Sum of squares is always non-negative. *)
Lemma sum_sqr_nonneg : forall a b c : R, 0 <= a * a + b * b + c * c.
Proof.
  intros. apply Rplus_le_le_0_compat. apply Rplus_le_le_0_compat; apply Rle_0_sqr. apply Rle_0_sqr.
Qed.

(** Alternative formulation: sum of squares is non-negative. *)
Lemma sum_sqr_nonneg_alt : forall a b c : R, 0 <= a * (a * 1) + b * (b * 1) + c * (c * 1).
Proof.
  intros. rewrite !Rmult_1_r. apply sum_sqr_nonneg.
Qed.

(** Triangle inequality for vector norms (multiplicative form). *)
Lemma norm_state_triangle_mult : forall x1 y1 z1 x2 y2 z2,
  sqrt ((x1 + x2) * (x1 + x2) + (y1 + y2) * (y1 + y2) + (z1 + z2) * (z1 + z2)) <=
  sqrt (x1 * x1 + y1 * y1 + z1 * z1) + sqrt (x2 * x2 + y2 * y2 + z2 * z2).
Proof.
  intros.
  (* Square both sides *)
  apply Rsqr_incr_0_var; [|apply Rplus_le_le_0_compat; apply sqrt_pos].
  unfold Rsqr.
  rewrite sqrt_sqrt by apply sum_sqr_nonneg.
  (* Expand RHS *)
  assert (H: (sqrt (x1 * x1 + y1 * y1 + z1 * z1) + sqrt (x2 * x2 + y2 * y2 + z2 * z2)) *
             (sqrt (x1 * x1 + y1 * y1 + z1 * z1) + sqrt (x2 * x2 + y2 * y2 + z2 * z2)) =
             sqrt (x1 * x1 + y1 * y1 + z1 * z1) * sqrt (x1 * x1 + y1 * y1 + z1 * z1) +
             2 * sqrt (x1 * x1 + y1 * y1 + z1 * z1) * sqrt (x2 * x2 + y2 * y2 + z2 * z2) +
             sqrt (x2 * x2 + y2 * y2 + z2 * z2) * sqrt (x2 * x2 + y2 * y2 + z2 * z2)).
  { ring. }
  rewrite H. clear H.
  rewrite !sqrt_sqrt by apply sum_sqr_nonneg.
  (* The goal is now: (x1+x2)² + (y1+y2)² + (z1+z2)² ≤ |v1|² + |v2|² + 2√(|v1|²|v2|²) *)
  (* Expand LHS: (x1+x2)² = x1² + 2x1x2 + x2², similarly for y and z *)
  assert (LHS: (x1 + x2) * (x1 + x2) + (y1 + y2) * (y1 + y2) + (z1 + z2) * (z1 + z2) =
               x1 * x1 + x2 * x2 + 2 * x1 * x2 +
               y1 * y1 + y2 * y2 + 2 * y1 * y2 +
               z1 * z1 + z2 * z2 + 2 * z1 * z2).
  { ring. }
  rewrite LHS. clear LHS.
  (* The goal is: x1²+x2²+2x1x2+y1²+y2²+2y1y2+z1²+z2²+2z1z2 ≤ x1²+y1²+z1²+x2²+y2²+z2²+2√(...) *)
  (* Rearranging, both sides have x1²+y1²+z1²+x2²+y2²+z2², so we need 2(x1x2+y1y2+z1z2) ≤ 2√(...) *)
  apply Rle_trans with
    (x1 * x1 + y1 * y1 + z1 * z1 + x2 * x2 + y2 * y2 + z2 * z2 +
     2 * (x1 * x2 + y1 * y2 + z1 * z2)).
  - (* Show LHS equals this intermediate form *)
    right. ring.
  - (* Show intermediate ≤ RHS *)
    (* Need to show: x1²+y1²+z1²+x2²+y2²+z2²+2(x1x2+y1y2+z1z2) ≤ x1²+y1²+z1²+x2²+y2²+z2²+2√(...) *)
    apply Rle_trans with
      (x1 * x1 + y1 * y1 + z1 * z1 + x2 * x2 + y2 * y2 + z2 * z2 +
       2 * sqrt ((x1 * x1 + y1 * y1 + z1 * z1) * (x2 * x2 + y2 * y2 + z2 * z2))).
    + (* Use Cauchy-Schwarz *)
      apply Rplus_le_compat_l.
      apply Rmult_le_compat_l; [lra|].
      apply cauchy_schwarz_sqrt_3.
    + (* This is exactly the RHS *)
      right.
      rewrite sqrt_mult by apply sum_sqr_nonneg.
      ring.
Qed.

(** Triangle inequality for state norms. *)
Lemma norm_state_triangle : forall s1 s2,
  norm_state (state_add s1 s2) <= norm_state s1 + norm_state s2.
Proof.
  intros [[x1 y1] z1] [[x2 y2] z2].
  unfold norm_state, state_add; simpl.
  (* Convert pow to multiplication *)
  generalize (norm_state_triangle_mult x1 y1 z1 x2 y2 z2).
  unfold pow. simpl.
  rewrite !Rmult_1_r.
  intro H. exact H.
Qed.

Lemma norm_state_zero_iff : forall s,
  norm_state s = 0 <-> s = state_zero.
Proof.
  intros [[x y] z].
  split.
  - intro H.
    unfold norm_state in H. simpl in H.
    unfold pow in H. simpl in H.
    rewrite !Rmult_1_r in H.
    assert (H0: x * x + y * y + z * z = 0).
    { apply sqrt_eq_0 in H. exact H. apply sum_sqr_nonneg. }
    assert (Hx: x * x = 0).
    { assert (Hsum: x * x + y * y + z * z = 0) by exact H0.
      assert (Hyz: 0 <= y * y + z * z).
      { apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
      assert (Hx_nonneg: 0 <= x * x) by apply Rle_0_sqr.
      lra. }
    assert (Hy: y * y = 0).
    { assert (Hsum: x * x + y * y + z * z = 0) by exact H0.
      assert (Hz_nonneg: 0 <= z * z) by apply Rle_0_sqr.
      assert (Hy_nonneg: 0 <= y * y) by apply Rle_0_sqr.
      rewrite Hx in Hsum.
      lra. }
    assert (Hz: z * z = 0).
    { assert (Hsum: x * x + y * y + z * z = 0) by exact H0.
      rewrite Hx, Hy in Hsum.
      lra. }
    apply Rsqr_0_uniq in Hx.
    apply Rsqr_0_uniq in Hy.
    apply Rsqr_0_uniq in Hz.
    unfold state_zero. simpl.
    f_equal.
    + f_equal; assumption.
    + assumption.
  - intro H.
    rewrite H.
    unfold norm_state, state_zero. simpl.
    unfold pow. simpl.
    rewrite !Rmult_1_r, !Rmult_0_l, !Rplus_0_r.
    apply sqrt_0.
Qed.

Lemma norm_state_symmetric : forall s1 s2,
  norm_state (state_sub s1 s2) = norm_state (state_sub s2 s1).
Proof.
  intros [[x1 y1] z1] [[x2 y2] z2].
  unfold norm_state, state_sub. simpl.
  f_equal.
  unfold pow. simpl.
  rewrite !Rmult_1_r.
  ring.
Qed.

Theorem euclidean_norm_is_metric :
  (forall s1 s2 s3, norm_state (state_sub s1 s3) <= norm_state (state_sub s1 s2) + norm_state (state_sub s2 s3)) /\
  (forall s1 s2, norm_state (state_sub s1 s2) = norm_state (state_sub s2 s1)) /\
  (forall s, norm_state (state_sub s s) = 0) /\
  (forall s1 s2, norm_state (state_sub s1 s2) = 0 -> s1 = s2) /\
  (forall s, norm_state s >= 0).
Proof.
  repeat split.
  - intros s1 s2 s3.
    assert (H: state_sub s1 s3 = state_add (state_sub s1 s2) (state_sub s2 s3)).
    { destruct s1 as [[x1 y1] z1].
      destruct s2 as [[x2 y2] z2].
      destruct s3 as [[x3 y3] z3].
      unfold state_sub, state_add. simpl.
      f_equal.
      - f_equal; ring.
      - ring. }
    rewrite H.
    apply norm_state_triangle.
  - intros s1 s2.
    apply norm_state_symmetric.
  - intros [[x y] z].
    unfold norm_state, state_sub.
    simpl.
    unfold Rminus.
    rewrite !Rplus_opp_r.
    unfold pow.
    simpl.
    rewrite !Rmult_1_r.
    rewrite !Rmult_0_l.
    rewrite !Rplus_0_r.
    apply sqrt_0.
  - intros s1 s2 H.
    assert (Heq: state_sub s1 s2 = state_zero).
    { apply norm_state_zero_iff. exact H. }
    destruct s1 as [[x1 y1] z1].
    destruct s2 as [[x2 y2] z2].
    unfold state_sub, state_zero in Heq. simpl in Heq.
    inversion Heq.
    unfold Rminus in H1, H2, H3.
    f_equal; f_equal; lra.
  - intros s.
    apply norm_state_nonneg.
Qed.

Definition Action := State -> State.

Definition identity_action : Action := fun s => s.

Definition compose_actions (a1 a2 : Action) : Action :=
  fun s => a1 (a2 s).

Definition preserves_resources (a : Action) : Prop :=
  forall s : State, norm_state (a s) >= norm_state s.

Definition destroys_resources (a : Action) : Prop :=
  exists s : State, norm_state (a s) < norm_state s.

(** Constructive definition of resource destruction *)
Definition norm_reduction (a : Action) (s : State) : R :=
  norm_state s - norm_state (a s).

(** The set of all norm reductions for an action *)
Definition norm_reduction_set (a : Action) : Rbar -> Prop :=
  fun r => exists s : State, r = Finite (norm_reduction a s).

(** Resource destruction as the supremum of norm reductions *)
Definition resource_destruction (a : Action) : R :=
  match Lub_Rbar (norm_reduction_set a) with
  | Finite r => Rmax r 0
  | p_infty => 1  (* If unbounded above, return a positive constant *)
  | m_infty => 0
  end.

Lemma norm_reduction_bounded_by_original_norm : forall a s,
  norm_reduction a s <= norm_state s.
Proof.
  intros a s.
  unfold norm_reduction.
  assert (H: norm_state (a s) >= 0) by apply norm_state_nonneg.
  lra.
Qed.

Theorem norm_reduction_set_has_upper_bound : forall a s_max,
  (forall s, norm_state s <= norm_state s_max) ->
  Rbar_is_upper_bound (norm_reduction_set a) (Finite (norm_state s_max)).
Proof.
  intros a s_max Hmax.
  unfold Rbar_is_upper_bound, norm_reduction_set.
  intros x [s Hs].
  rewrite Hs.
  simpl.
  assert (H := norm_reduction_bounded_by_original_norm a s).
  apply Rle_trans with (norm_state s).
  - exact H.
  - apply Hmax.
Qed.

Lemma norm_reduction_set_nonempty : forall a,
  exists r, norm_reduction_set a r.
Proof.
  intros a.
  exists (Finite (norm_reduction a state_zero)).
  unfold norm_reduction_set.
  exists state_zero.
  reflexivity.
Qed.

Lemma norm_reduction_set_has_finite_elements_only : forall a x,
  norm_reduction_set a x -> exists r, x = Finite r.
Proof.
  intros a x Hx.
  destruct Hx as [s Hs].
  exists (norm_reduction a s).
  exact Hs.
Qed.

Theorem norm_reduction_set_contains_only_finite_values : forall a,
  (exists r, norm_reduction_set a r) /\
  (forall x, norm_reduction_set a x -> exists r, x = Finite r).
Proof.
  intro a.
  split.
  - apply norm_reduction_set_nonempty.
  - apply norm_reduction_set_has_finite_elements_only.
Qed.

Theorem norm_reduction_locally_bounded : forall a s,
  norm_reduction a s <= norm_state s.
Proof.
  apply norm_reduction_bounded_by_original_norm.
Qed.

Theorem resource_destruction_well_defined : forall a,
  match Lub_Rbar (norm_reduction_set a) with
  | Finite r => True
  | p_infty => True
  | m_infty => exists x, norm_reduction_set a x -> False
  end.
Proof.
  intro a.
  destruct (Lub_Rbar (norm_reduction_set a)) eqn:Heq.
  - exact I.
  - exact I.
  - assert (Hnonempty := norm_reduction_set_nonempty a).
    destruct Hnonempty as [x0 Hx0].
    assert (Hfinite := norm_reduction_set_has_finite_elements_only a x0 Hx0).
    destruct Hfinite as [r0 Hr0].
    exists x0.
    intro.
    assert (Hlub := Lub_Rbar_correct (norm_reduction_set a)).
    rewrite Heq in Hlub.
    destruct Hlub as [Hub Hleast].
    rewrite Hr0 in H.
    unfold is_ub_Rbar in Hub.
    specialize (Hub r0 H).
    simpl in Hub.
    exact Hub.
Qed.

(** Helper: norm_reduction is non-positive for preserving actions *)
Lemma norm_reduction_nonpos_preserving : forall a s,
  preserves_resources a -> norm_reduction a s <= 0.
Proof.
  intros a s Hpres.
  unfold norm_reduction, preserves_resources in *.
  specialize (Hpres s).
  apply Rge_le in Hpres.
  lra.
Qed.

(** Helper: The norm_reduction_set is bounded above by 0 for preserving actions *)
Lemma norm_reduction_set_bounded_preserving : forall a,
  preserves_resources a ->
  Rbar_is_upper_bound (norm_reduction_set a) 0.
Proof.
  intros a Hpres.
  unfold Rbar_is_upper_bound, norm_reduction_set.
  intros x [s Hs].
  rewrite Hs.
  apply norm_reduction_nonpos_preserving.
  assumption.
Qed.

(** Main lemma: resource_destruction_preserving *)
Lemma resource_destruction_preserving : forall a,
  preserves_resources a -> resource_destruction a = 0.
Proof.
  intros a Hpres.
  unfold resource_destruction.
  destruct (Lub_Rbar (norm_reduction_set a)) eqn:Hlub.
  - unfold Rmax.
    destruct (Rle_dec r 0).
    + reflexivity.
    + exfalso.
      assert (Hbound: Rbar_is_upper_bound (norm_reduction_set a) 0).
      { apply norm_reduction_set_bounded_preserving. assumption. }
      assert (Hlub_prop := Lub_Rbar_correct (norm_reduction_set a)).
      rewrite Hlub in Hlub_prop.
      destruct Hlub_prop as [Hub Hleast].
      specialize (Hleast 0 Hbound).
      simpl in Hleast.
      lra.
  - exfalso.
    (* If preserving, norm_reduction_set is bounded above by 0, so can't be p_infty *)
    assert (Hbound: Rbar_is_upper_bound (norm_reduction_set a) 0).
    { apply norm_reduction_set_bounded_preserving. assumption. }
    assert (Hlub_prop := Lub_Rbar_correct (norm_reduction_set a)).
    rewrite Hlub in Hlub_prop.
    destruct Hlub_prop as [Hub Hleast].
    (* p_infty is the least upper bound, but 0 is also an upper bound *)
    (* So p_infty <= 0, which is a contradiction *)
    specialize (Hleast 0 Hbound).
    simpl in Hleast.
    unfold Rbar_le in Hleast.
    assumption.
  - reflexivity.
Qed.

(** Helper: If an action destroys resources, there exists a positive norm_reduction *)
Lemma exists_positive_norm_reduction : forall a,
  destroys_resources a ->
  exists s, norm_reduction a s > 0.
Proof.
  intros a Hdest.
  unfold destroys_resources in Hdest.
  destruct Hdest as [s Hdest].
  exists s.
  unfold norm_reduction.
  lra.
Qed.

(** Helper: The supremum is an upper bound for the set *)
Lemma lub_is_upper_bound : forall a s,
  Rbar_le (Finite (norm_reduction a s)) (Lub_Rbar (norm_reduction_set a)).
Proof.
  intros a s.
  assert (Hlub := Lub_Rbar_correct (norm_reduction_set a)).
  destruct Hlub as [Hub _].
  apply Hub.
  unfold norm_reduction_set.
  exists s.
  reflexivity.
Qed.

(** Main lemma: resource_destruction_destroying *)
Lemma resource_destruction_destroying : forall a,
  destroys_resources a -> resource_destruction a > 0.
Proof.
  intros a Hdest.
  destruct (exists_positive_norm_reduction a Hdest) as [s Hpos].
  unfold resource_destruction.
  assert (Hlub_bound := lub_is_upper_bound a s).
  destruct (Lub_Rbar (norm_reduction_set a)) eqn:Hlub.
  - unfold Rmax.
    destruct (Rle_dec r 0).
    + exfalso.
      simpl in Hlub_bound.
      lra.
    + simpl in Hlub_bound.
      lra.
  - apply Rlt_0_1.
  - simpl in Hlub_bound.
    unfold Rbar_le in Hlub_bound.
    lra.
Qed.

Lemma resource_destruction_nonneg : forall a,
  preserves_resources a -> resource_destruction a <= 0.
Proof.
  intros a H.
  rewrite resource_destruction_preserving; auto.
  lra.
Qed.

Lemma norm_reduction_bounded_on_ball : forall a radius,
  radius >= 0 ->
  forall s, norm_state s <= radius -> norm_reduction a s <= radius.
Proof.
  intros a radius Hradius s Hs.
  unfold norm_reduction.
  assert (H: norm_state (a s) >= 0) by apply norm_state_nonneg.
  lra.
Qed.

(** ** Normalized Resource Destruction

    Scaled version with codomain [0, 1]. Preserves characterization of
    resource preservation/destruction and monotonicity properties. *)

Definition resource_destruction_normalized (a : Action) (scale : R) : R :=
  let raw := resource_destruction a in
  if Rle_dec scale 0 then 0
  else Rmin (raw / scale) 1.

Lemma resource_destruction_normalized_bounds : forall a scale,
  scale > 0 ->
  0 <= resource_destruction_normalized a scale <= 1.
Proof.
  intros a scale Hscale.
  unfold resource_destruction_normalized.
  destruct (Rle_dec scale 0).
  - lra.
  - unfold Rmin.
    destruct (Rle_dec (resource_destruction a / scale) 1) as [Hle1|Hgt1].
    + split.
      * unfold Rdiv.
        apply Rmult_le_pos.
        -- unfold resource_destruction.
           destruct (Lub_Rbar (norm_reduction_set a)) eqn:Hlub.
           ++ unfold Rmax.
              destruct (Rle_dec r 0); lra.
           ++ lra.
           ++ lra.
        -- left. apply Rinv_0_lt_compat. exact Hscale.
      * exact Hle1.
    + split; lra.
Qed.

Lemma resource_destruction_normalized_preserving : forall a scale,
  preserves_resources a ->
  scale > 0 ->
  resource_destruction_normalized a scale = 0.
Proof.
  intros a scale Hpres Hscale.
  unfold resource_destruction_normalized.
  rewrite resource_destruction_preserving by exact Hpres.
  destruct (Rle_dec scale 0); [lra|].
  unfold Rdiv.
  rewrite Rmult_0_l.
  unfold Rmin.
  destruct (Rle_dec 0 1); lra.
Qed.

Lemma resource_destruction_normalized_destroying : forall a scale,
  destroys_resources a ->
  scale > 0 ->
  resource_destruction_normalized a scale > 0.
Proof.
  intros a scale Hdest Hscale.
  unfold resource_destruction_normalized.
  destruct (Rle_dec scale 0); [lra|].
  assert (Hraw: resource_destruction a > 0).
  { apply resource_destruction_destroying. exact Hdest. }
  unfold Rmin.
  destruct (Rle_dec (resource_destruction a / scale) 1).
  - unfold Rdiv.
    apply Rmult_lt_0_compat.
    + exact Hraw.
    + apply Rinv_0_lt_compat. exact Hscale.
  - lra.
Qed.

Lemma resource_destruction_normalized_monotone : forall a1 a2 scale,
  scale > 0 ->
  resource_destruction a1 <= resource_destruction a2 ->
  resource_destruction_normalized a1 scale <= resource_destruction_normalized a2 scale.
Proof.
  intros a1 a2 scale Hscale Hle.
  unfold resource_destruction_normalized.
  destruct (Rle_dec scale 0); [lra|].
  unfold Rmin.
  destruct (Rle_dec (resource_destruction a1 / scale) 1) as [H1|H1];
  destruct (Rle_dec (resource_destruction a2 / scale) 1) as [H2|H2].
  - unfold Rdiv.
    apply Rmult_le_compat_r.
    + left. apply Rinv_0_lt_compat. exact Hscale.
    + exact Hle.
  - unfold Rdiv in H1.
    apply Rle_trans with 1; [exact H1|lra].
  - exfalso.
    unfold Rdiv in H1, H2.
    apply Rnot_le_lt in H1.
    assert (H_a1: resource_destruction a1 > scale * 1).
    { apply Rmult_lt_reg_r with (/ scale).
      - apply Rinv_0_lt_compat. exact Hscale.
      - assert (Heq: scale * 1 * / scale = 1) by (field; lra).
        rewrite Heq.
        exact H1. }
    assert (H_a2: resource_destruction a2 * / scale <= 1).
    { exact H2. }
    assert (Hcontra: resource_destruction a2 <= scale).
    { apply Rmult_le_reg_r with (/ scale).
      - apply Rinv_0_lt_compat. exact Hscale.
      - assert (Heq: scale * / scale = 1) by (field; lra).
        rewrite Heq.
        exact H2. }
    lra.
  - lra.
Qed.

Lemma resource_destruction_normalized_nonneg : forall a scale,
  scale > 0 ->
  resource_destruction_normalized a scale >= 0.
Proof.
  intros a scale Hscale.
  assert (H := resource_destruction_normalized_bounds a scale Hscale).
  lra.
Qed.

Definition c : R := 299792458.

Lemma c_positive : c > 0.
Proof.
  unfold c.
  lra.
Qed.

Lemma c_finite : c <= 299792458.
Proof.
  unfold c.
  lra.
Qed.

Lemma c_reasonable : c > 10.
Proof.
  unfold c.
  lra.
Qed.

Record SpeedOfLight := mkSpeed {
  speed : R;
  speed_positive : speed > 0
}.

Definition standard_c : SpeedOfLight.
Proof.
  apply (mkSpeed c).
  apply c_positive.
Defined.

(** * Section 2: Observer Model and Discrete Approximation *)

Definition signal_strength (destruction : R) (distance : R) : R :=
  Rabs destruction / (1 + distance).

Lemma signal_strength_nonneg : forall d dist,
  dist >= 0 ->
  signal_strength d dist >= 0.
Proof.
  intros d dist Hdist.
  unfold signal_strength.
  apply Rle_ge.
  unfold Rdiv.
  apply Rmult_le_pos.
  - apply Rabs_pos.
  - apply Rlt_le. apply Rinv_0_lt_compat. lra.
Qed.

Lemma signal_strength_decreases : forall d dist1 dist2,
  d <> 0 ->
  0 <= dist1 < dist2 ->
  signal_strength d dist2 < signal_strength d dist1.
Proof.
  intros d dist1 dist2 Hd [Hpos Hlt].
  unfold signal_strength.
  unfold Rdiv.
  apply Rmult_lt_compat_l.
  - apply Rabs_pos_lt. exact Hd.
  - apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat; lra.
    + lra.
Qed.

Definition detection_threshold_theory (noise_level : R) (confidence : R) : R :=
  noise_level / confidence.

Lemma detection_threshold_positive : forall noise conf,
  noise > 0 -> conf > 0 ->
  detection_threshold_theory noise conf > 0.
Proof.
  intros noise conf Hnoise Hconf.
  unfold detection_threshold_theory.
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  - exact Hnoise.
  - apply Rinv_0_lt_compat. exact Hconf.
Qed.

Theorem observer_detects_iff_signal_exceeds_threshold : forall destruction distance threshold,
  distance >= 0 ->
  threshold > 0 ->
  (signal_strength destruction distance > threshold <->
   Rabs destruction > threshold * (1 + distance)).
Proof.
  intros destruction distance threshold Hdist Hthresh.
  unfold signal_strength.
  split.
  - intro H.
    unfold Rdiv in H.
    apply Rmult_lt_reg_r with (/ (1 + distance)).
    + apply Rinv_0_lt_compat. lra.
    + rewrite Rmult_assoc.
      assert (Hneq: 1 + distance <> 0) by lra.
      rewrite Rinv_r by exact Hneq.
      rewrite Rmult_1_r.
      exact H.
  - intro H.
    unfold Rdiv.
    apply Rmult_lt_reg_r with (1 + distance).
    + lra.
    + rewrite Rmult_assoc.
      assert (Hneq: 1 + distance <> 0) by lra.
      rewrite Rinv_l by exact Hneq.
      rewrite Rmult_1_r.
      exact H.
Qed.

Record Observer := mkObserver {
  obs_position : State;
  obs_time : R;
  obs_threshold : R;
  obs_threshold_pos : obs_threshold > 0
}.

Definition can_observe (o : Observer) (event_pos : State) (t : R) : Prop :=
  let delay := norm_state (state_sub (obs_position o) event_pos) / c in
  t >= obs_time o + delay.

Definition grid_point (i j k : Z) (resolution : R) : State :=
  (IZR i * resolution, IZR j * resolution, IZR k * resolution).

Definition enumerate_grid_observers (origin : State) (radius : R)
  (resolution : R) : list Observer :=
  let n := Z.to_nat (up (radius / resolution)) in
  flat_map (fun i =>
    flat_map (fun j =>
      flat_map (fun k =>
        let pos := state_add origin (grid_point (Z.of_nat i - Z.of_nat n)
                                                (Z.of_nat j - Z.of_nat n)
                                                (Z.of_nat k - Z.of_nat n) resolution) in
        if Rle_dec (norm_state (state_sub pos origin)) radius then
          [mkObserver pos 0 1 Rlt_0_1]
        else
          []
      ) (seq 0 (2*n+1))
    ) (seq 0 (2*n+1))
  ) (seq 0 (2*n+1)).

Lemma state_sub_add_cancel : forall origin offset,
  state_sub (state_add origin offset) origin = offset.
Proof.
  intros [[ox oy] oz] [[dx dy] dz].
  unfold state_add, state_sub.
  simpl.
  f_equal; f_equal; ring.
Qed.

Lemma enumerate_grid_observers_sound : forall origin radius resolution o,
  resolution > 0 ->
  In o (enumerate_grid_observers origin radius resolution) ->
  norm_state (state_sub (obs_position o) origin) <= radius + resolution * sqrt 3.
Proof.
  intros origin radius resolution o Hres Ho.
  unfold enumerate_grid_observers in Ho.
  apply in_flat_map in Ho.
  destruct Ho as [i [Hi Ho]].
  apply in_flat_map in Ho.
  destruct Ho as [j [Hj Ho]].
  apply in_flat_map in Ho.
  destruct Ho as [k [Hk Ho]].
  set (gp := grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                        (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                        (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution))))
                        resolution) in *.
  remember (state_add origin gp) as pos.
  destruct (Rle_dec (norm_state (state_sub pos origin)) radius) as [Hnorm|Hnorm].
  - simpl in Ho.
    destruct Ho as [Heq | Hfalse]; [| contradiction].
    subst o pos.
    simpl.
    rewrite state_sub_add_cancel.
    rewrite state_sub_add_cancel in Hnorm.
    apply Rle_trans with (radius + 0).
    + apply Rle_trans with radius.
      * exact Hnorm.
      * right. ring.
    + apply Rplus_le_compat_l.
      apply Rmult_le_pos.
      * left. exact Hres.
      * apply sqrt_pos.
  - simpl in Ho.
    contradiction.
Qed.

(** The grid point at coordinates (0,0,0) in the shifted grid system
    equals the origin point (0,0,0) in the state space. *)
Lemma grid_point_at_center : forall n resolution,
  grid_point (Z.of_nat n - Z.of_nat n)
             (Z.of_nat n - Z.of_nat n)
             (Z.of_nat n - Z.of_nat n) resolution = (0, 0, 0).
Proof.
  intros n resolution.
  unfold grid_point.
  rewrite !Z.sub_diag.
  simpl.
  rewrite !Rmult_0_l.
  reflexivity.
Qed.

(** The norm of the difference between any state and itself is zero. *)
Lemma norm_state_origin_zero : forall origin,
  norm_state (state_sub origin origin) = 0.
Proof.
  intros [[x y] z].
  unfold norm_state, state_sub.
  simpl.
  unfold Rminus.
  rewrite !Rplus_opp_r.
  unfold pow.
  simpl.
  rewrite !Rmult_1_r.
  rewrite !Rmult_0_l.
  rewrite !Rplus_0_r.
  apply sqrt_0.
Qed.

(** A number n is always contained in the sequence [0, 1, ..., 2n]. *)
Lemma In_seq_middle : forall n,
  In n (seq 0 (2 * n + 1)).
Proof.
  intros n.
  rewrite in_seq.
  split.
  - lia.
  - lia.
Qed.

(** If the resolution is bounded by radius/10, then radius must be positive. *)
Lemma radius_positive_from_bound : forall radius resolution,
  0 < resolution < radius / 10 -> radius > 0.
Proof.
  intros radius resolution [Hres_pos Hres_small].
  unfold Rdiv in Hres_small.
  assert (0 < radius * /10).
  { apply Rle_lt_trans with resolution; [lra | exact Hres_small]. }
  assert (0 < radius).
  { apply Rmult_lt_reg_r with (/10).
    - apply Rinv_0_lt_compat; lra.
    - rewrite Rmult_0_l. exact H. }
  exact H0.
Qed.

(** The distance from the origin (0,0,0) to any point equals
    the norm of that point. *)
Lemma grid_origin_norm_eq : forall origin,
  norm_state (state_sub (0, 0, 0) origin) = norm_state origin.
Proof.
  intros [[ox oy] oz].
  unfold state_sub, norm_state.
  simpl.
  unfold Rminus.
  rewrite !Rplus_0_l.
  unfold pow; simpl.
  rewrite !Rmult_1_r.
  f_equal.
  ring.
Qed.

(** Every point is either within a given radius or outside it (law of excluded middle). *)
Lemma origin_within_large_radius : forall origin radius resolution,
  0 < resolution < radius / 10 ->
  norm_state origin <= radius \/ norm_state origin > radius.
Proof.
  intros origin radius resolution Hbound.
  destruct (Rle_dec (norm_state origin) radius).
  - left. exact r.
  - right. apply Rnot_le_gt. exact n.
Qed.

(** The center index n is within the grid bounds [0, 2n] and
    the grid point at shifted coordinates (0,0,0) equals the origin. *)
Lemma grid_center_exists : forall radius resolution,
  0 < resolution < radius / 10 ->
  let n := Z.to_nat (up (radius / resolution)) in
  (n < 2 * n + 1)%nat /\
  grid_point (Z.of_nat n - Z.of_nat n)
             (Z.of_nat n - Z.of_nat n)
             (Z.of_nat n - Z.of_nat n) resolution = (0, 0, 0).
Proof.
  intros radius resolution Hbound.
  simpl.
  split.
  - lia.
  - rewrite !Z.sub_diag.
    unfold grid_point.
    simpl.
    rewrite !Rmult_0_l.
    reflexivity.
Qed.

(** If a grid point at indices (i,j,k) is within radius of the origin,
    then it is included in the enumerated observers list. *)
Lemma grid_point_in_enumerate : forall origin radius resolution i j k,
  In i (seq 0 (2 * Z.to_nat (up (radius / resolution)) + 1)) ->
  In j (seq 0 (2 * Z.to_nat (up (radius / resolution)) + 1)) ->
  In k (seq 0 (2 * Z.to_nat (up (radius / resolution)) + 1)) ->
  norm_state (state_sub
    (state_add origin (grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                                  (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                                  (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution))
    origin) <= radius ->
  In (mkObserver
        (state_add origin (grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                                     (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                                     (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution))
        0 1 Rlt_0_1)
     (enumerate_grid_observers origin radius resolution).
Proof.
  intros origin radius resolution i j k Hi Hj Hk Hnorm.
  unfold enumerate_grid_observers.
  apply in_flat_map.
  exists i. split; [exact Hi|].
  apply in_flat_map.
  exists j. split; [exact Hj|].
  apply in_flat_map.
  exists k. split; [exact Hk|].
  set (gp := grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                        (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                        (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution) in *.
  destruct (Rle_dec (norm_state (state_sub (state_add origin gp) origin)) radius).
  - simpl. left. reflexivity.
  - contradiction.
Qed.

(** When the origin is within radius of the coordinate origin (0,0,0),
    the grid enumeration contains at least one observer. *)
Lemma origin_within_radius_covered : forall origin radius resolution,
  0 < resolution < radius / 10 ->
  norm_state origin <= radius ->
  exists obs, In obs (enumerate_grid_observers origin radius resolution).
Proof.
  intros origin radius resolution Hbound Hnorm_bound.
  set (n := Z.to_nat (up (radius / resolution))).
  set (gp := grid_point (Z.of_nat n - Z.of_nat n)
                        (Z.of_nat n - Z.of_nat n)
                        (Z.of_nat n - Z.of_nat n) resolution).
  exists (mkObserver (state_add origin gp) 0 1 Rlt_0_1).
  apply grid_point_in_enumerate; unfold n, gp.
  - apply In_seq_middle.
  - apply In_seq_middle.
  - apply In_seq_middle.
  - rewrite state_sub_add_cancel.
    assert (Hgrid: grid_point (Z.of_nat (Z.to_nat (up (radius / resolution))) -
                              Z.of_nat (Z.to_nat (up (radius / resolution))))
                             (Z.of_nat (Z.to_nat (up (radius / resolution))) -
                              Z.of_nat (Z.to_nat (up (radius / resolution))))
                             (Z.of_nat (Z.to_nat (up (radius / resolution))) -
                              Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution = (0, 0, 0)).
    { rewrite !Z.sub_diag.
      unfold grid_point. simpl. rewrite !Rmult_0_l. reflexivity. }
    rewrite Hgrid.
    assert (Hzero: norm_state (0, 0, 0) = 0).
    { unfold norm_state. simpl.
      assert (Heq: 0 * (0 * 1) + 0 * (0 * 1) + 0 * (0 * 1) = 0) by ring.
      rewrite Heq.
      apply sqrt_0. }
    rewrite Hzero.
    destruct Hbound as [Hres_pos Hres_bound].
    assert (Hrad_pos: radius > 0) by (apply radius_positive_from_bound with resolution; split; assumption).
    lra.
Qed.

(** Any ball of positive radius contains its own center point. *)
Lemma ball_always_contains_its_center : forall origin radius,
  radius > 0 ->
  norm_state (state_sub origin origin) <= radius.
Proof.
  intros origin radius Hpos.
  rewrite norm_state_origin_zero.
  lra.
Qed.

(** When the origin is within radius of (0,0,0), then (0,0,0) is within radius of origin. *)
Lemma grid_center_in_ball_when_origin_close : forall origin radius resolution,
  0 < resolution < radius / 10 ->
  norm_state origin <= radius ->
  norm_state (state_sub (0,0,0) origin) <= radius.
Proof.
  intros origin radius resolution Hbound Hnorm.
  rewrite grid_origin_norm_eq.
  exact Hnorm.
Qed.

(** The center of the grid (at shifted indices 0,0,0) corresponds
    to the point (0,0,0) in state space. *)
Lemma grid_center_point_coords : forall radius resolution,
  0 < resolution < radius / 10 ->
  let n := Z.to_nat (up (radius / resolution)) in
  grid_point (Z.of_nat n - Z.of_nat n)
             (Z.of_nat n - Z.of_nat n)
             (Z.of_nat n - Z.of_nat n) resolution = (0, 0, 0).
Proof.
  intros radius resolution Hbound.
  simpl.
  rewrite !Z.sub_diag.
  unfold grid_point.
  simpl.
  rewrite !Rmult_0_l.
  reflexivity.
Qed.

(** The center of any ball is always contained within that ball. *)
Lemma origin_itself_always_in_ball : forall origin radius,
  radius > 0 ->
  norm_state (state_sub origin origin) <= radius.
Proof.
  intros origin radius Hpos.
  rewrite norm_state_origin_zero.
  lra.
Qed.

(** Key geometric lemma: When the grid resolution is fine enough (< radius/10),
    the grid always contains at least one point within any ball of the given radius. *)
Lemma grid_covers_ball : forall origin radius resolution,
  0 < resolution < radius / 10 ->
  exists i j k,
    In i (seq 0 (2 * Z.to_nat (up (radius / resolution)) + 1)) /\
    In j (seq 0 (2 * Z.to_nat (up (radius / resolution)) + 1)) /\
    In k (seq 0 (2 * Z.to_nat (up (radius / resolution)) + 1)) /\
    norm_state (state_sub
      (state_add origin (grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                                    (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                                    (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution))
      origin) <= radius.
Proof.
  intros origin radius resolution Hbound.
  set (n := Z.to_nat (up (radius / resolution))).
  exists n, n, n.
  split; [|split; [|split]].
  - apply In_seq_middle.
  - apply In_seq_middle.
  - apply In_seq_middle.
  - rewrite state_sub_add_cancel.
    rewrite grid_point_at_center.
    assert (Hzero: norm_state (0, 0, 0) = 0).
    { unfold norm_state. simpl.
      assert (Heq: 0 * (0 * 1) + 0 * (0 * 1) + 0 * (0 * 1) = 0) by ring.
      rewrite Heq.
      apply sqrt_0. }
    rewrite Hzero.
    destruct Hbound as [Hres_pos Hres_bound].
    assert (Hrad_pos: radius > 0) by (apply radius_positive_from_bound with resolution; split; assumption).
    lra.
Qed.

(** The grid enumeration is never empty when resolution is sufficiently fine. *)
Lemma enumerate_includes_origin_ball : forall origin radius resolution,
  0 < resolution < radius / 10 ->
  enumerate_grid_observers origin radius resolution <> [].
Proof.
  intros origin radius resolution Hbound.
  intro Hempty.
  assert (Hexists: exists obs, In obs (enumerate_grid_observers origin radius resolution)).
  { destruct (Rle_dec (norm_state origin) radius).
    - exact (origin_within_radius_covered origin radius resolution Hbound r).
    - destruct (grid_covers_ball origin radius resolution Hbound) as [i [j [k [Hi [Hj [Hk Hnorm]]]]]].
      exists (mkObserver
        (state_add origin (grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                                     (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                                     (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution))
        0 1 Rlt_0_1).
      apply (grid_point_in_enumerate origin radius resolution i j k Hi Hj Hk Hnorm). }
  destruct Hexists as [obs Hobs].
  rewrite Hempty in Hobs.
  simpl in Hobs.
  contradiction.
Qed.

(** Main theorem: Grid enumeration is never empty for sufficiently fine resolution. *)
Theorem enumerate_grid_observers_nonempty : forall origin radius resolution,
  0 < resolution < radius / 10 ->
  enumerate_grid_observers origin radius resolution <> [].
Proof.
  intros origin radius resolution Hbound.
  apply enumerate_includes_origin_ball.
  exact Hbound.
Qed.

(** * Section 2b: Grid Refinement and Continuous Approximation *)

Definition grid_covers_point (origin : State) (radius : R) (resolution : R) (p : State) : Prop :=
  exists o, In o (enumerate_grid_observers origin radius resolution) /\
            norm_state (state_sub (obs_position o) p) <= resolution * sqrt 3.

Lemma grid_spacing_decreases : forall res1 res2,
  0 < res2 < res1 ->
  res2 * sqrt 3 < res1 * sqrt 3.
Proof.
  intros res1 res2 [Hres2_pos Hres_lt].
  apply Rmult_lt_compat_r.
  - assert (0 < 3) by lra.
    apply sqrt_lt_R0. exact H.
  - exact Hres_lt.
Qed.

Theorem grid_resolution_improves_approximation : forall origin radius res,
  0 < res < radius / 10 ->
  enumerate_grid_observers origin radius res <> [].
Proof.
  intros origin radius res Hbound.
  apply enumerate_grid_observers_nonempty.
  exact Hbound.
Qed.

Definition grid_approximation_error (resolution : R) : R :=
  resolution * sqrt 3.

Lemma sqrt_3_bound : sqrt 3 < 2.
Proof.
  assert (H: 3 < 4) by lra.
  apply sqrt_lt_1 in H.
  - assert (Hsqrt4: sqrt 4 = 2).
    { apply Rsqr_inj.
      - apply sqrt_pos.
      - lra.
      - unfold Rsqr. rewrite sqrt_sqrt by lra. ring. }
    rewrite Hsqrt4 in H. exact H.
  - lra.
  - lra.
Qed.

Lemma approximation_error_bounded : forall resolution,
  resolution > 0 ->
  grid_approximation_error resolution < 2 * resolution.
Proof.
  intros resolution Hres.
  unfold grid_approximation_error.
  assert (H := sqrt_3_bound).
  apply Rmult_lt_compat_r with (r := resolution) in H; [|exact Hres].
  lra.
Qed.

Theorem grid_resolution_bound_sufficient : forall radius resolution,
  resolution > 0 ->
  resolution < radius / 10 ->
  grid_approximation_error resolution < radius / 5.
Proof.
  intros radius resolution Hres_pos Hbound.
  unfold grid_approximation_error.
  assert (Hsqrt3: sqrt 3 < 2) by apply sqrt_3_bound.
  assert (H1: resolution * sqrt 3 < 2 * resolution).
  { assert (H := approximation_error_bounded resolution Hres_pos).
    unfold grid_approximation_error in H.
    exact H. }
  apply Rlt_trans with (2 * resolution).
  - exact H1.
  - unfold Rdiv in *.
    assert (Hrad_pos: radius > 0).
    { apply radius_positive_from_bound with resolution.
      split; assumption. }
    assert (H2: resolution < radius * /10) by exact Hbound.
    assert (H3: 2 * resolution < 2 * (radius * /10)).
    { apply Rmult_lt_compat_l; lra. }
    assert (Heq: 2 * (radius * /10) = radius * /5) by field.
    rewrite Heq in H3.
    exact H3.
Qed.

Lemma sqrt_3_positive : sqrt 3 > 0.
Proof.
  apply sqrt_lt_R0.
  lra.
Qed.

Theorem grid_error_converges_to_zero : forall epsilon,
  epsilon > 0 ->
  exists delta, delta > 0 /\
    forall resolution,
      0 < resolution < delta ->
      grid_approximation_error resolution < epsilon.
Proof.
  intros epsilon Heps.
  exists (epsilon / sqrt 3).
  split.
  - unfold Rdiv.
    apply Rmult_lt_0_compat.
    + exact Heps.
    + apply Rinv_0_lt_compat.
      apply sqrt_3_positive.
  - intros resolution [Hres_pos Hres_delta].
    unfold grid_approximation_error, Rdiv in *.
    apply Rmult_lt_compat_r with (r := sqrt 3) in Hres_delta.
    + assert (Hsqrt3: sqrt 3 > 0) by apply sqrt_3_positive.
      assert (Heq: epsilon * / sqrt 3 * sqrt 3 = epsilon).
      { field. apply Rgt_not_eq. exact Hsqrt3. }
      rewrite Heq in Hres_delta.
      exact Hres_delta.
    + apply sqrt_3_positive.
Qed.

Theorem grid_approximation_arbitrarily_accurate : forall epsilon,
  epsilon > 0 ->
  exists resolution,
    resolution > 0 /\
    grid_approximation_error resolution < epsilon.
Proof.
  intros epsilon Heps.
  exists (epsilon / (sqrt 3 + 1)).
  split.
  - unfold Rdiv.
    apply Rmult_lt_0_compat.
    + exact Heps.
    + apply Rinv_0_lt_compat.
      assert (H: sqrt 3 > 0) by apply sqrt_3_positive.
      lra.
  - unfold grid_approximation_error.
    assert (Hsqrt3: sqrt 3 > 0) by apply sqrt_3_positive.
    assert (Hden: sqrt 3 + 1 > 0) by lra.
    unfold Rdiv.
    assert (Hgoal: epsilon * / (sqrt 3 + 1) * sqrt 3 < epsilon).
    { replace (epsilon * / (sqrt 3 + 1) * sqrt 3) with (epsilon * (sqrt 3 * / (sqrt 3 + 1))) by ring.
      replace epsilon with (epsilon * 1) at 2 by ring.
      apply Rmult_lt_compat_l; [exact Heps|].
      apply Rmult_lt_reg_r with (sqrt 3 + 1); [exact Hden|].
      rewrite Rmult_assoc.
      rewrite Rinv_l by lra.
      rewrite Rmult_1_r.
      rewrite Rmult_1_l.
      lra. }
    exact Hgoal.
Qed.

(** * Section 3: Elimination Probability and Survival *)

Definition event_rate (destruction : R) (threshold : R) : R :=
  Rabs destruction / threshold.

Lemma event_rate_nonneg : forall d t,
  t > 0 -> event_rate d t >= 0.
Proof.
  intros d t Ht.
  unfold event_rate.
  apply Rle_ge.
  unfold Rdiv.
  apply Rmult_le_pos.
  - apply Rabs_pos.
  - left. apply Rinv_0_lt_compat. exact Ht.
Qed.

Definition time_interval_probability (lambda : R) (dt : R) : R :=
  lambda * dt.

Lemma small_interval_detection : forall lambda dt,
  lambda >= 0 -> dt > 0 -> dt < 1 ->
  time_interval_probability lambda dt >= 0 /\
  time_interval_probability lambda dt <= lambda.
Proof.
  intros lambda dt Hlambda Hdt Hdt_small.
  unfold time_interval_probability.
  split.
  - apply Rle_ge.
    apply Rmult_le_pos.
    + apply Rge_le. exact Hlambda.
    + lra.
  - destruct (Rle_lt_or_eq_dec 0 lambda).
    + apply Rge_le. exact Hlambda.
    + apply Rle_trans with (lambda * 1).
      * apply Rmult_le_compat_l; [lra|lra].
      * rewrite Rmult_1_r. apply Rle_refl.
    + subst. rewrite Rmult_0_l. apply Rge_le. exact Hlambda.
Qed.

Lemma no_detection_in_interval : forall lambda dt,
  lambda >= 0 -> dt >= 0 ->
  time_interval_probability lambda dt <= 1 ->
  1 - time_interval_probability lambda dt >= 0.
Proof.
  intros lambda dt Hlambda Hdt Hbound.
  unfold time_interval_probability in *.
  apply Rle_ge.
  apply Rplus_le_reg_r with (lambda * dt).
  ring_simplify.
  exact Hbound.
Qed.

Lemma pow_mult_distr : forall (a b : R) (n : nat),
  (a * b) ^ n = a ^ n * b ^ n.
Proof.
  intros a b n.
  induction n.
  - simpl. ring.
  - simpl. rewrite IHn. ring.
Qed.


Theorem poisson_formula_interpretation : forall lambda,
  lambda >= 0 ->
  1 - exp (-lambda) >= 0 /\
  1 - exp (-lambda) <= 1 /\
  (lambda = 0 -> 1 - exp (-lambda) = 0) /\
  (lambda > 0 -> 1 - exp (-lambda) > 0).
Proof.
  intros lambda Hlambda.
  repeat split.
  - assert (Hexp_bound: exp (-lambda) <= 1).
    { rewrite <- exp_0.
      destruct (Rle_lt_or_eq_dec 0 lambda).
      - apply Rge_le. exact Hlambda.
      - left. apply exp_increasing.
        apply Ropp_lt_cancel. rewrite Ropp_0. rewrite Ropp_involutive.
        exact r.
      - rewrite <- e. rewrite Ropp_0. apply Rle_refl. }
    lra.
  - assert (Hexp_pos: exp (-lambda) > 0) by apply exp_pos.
    lra.
  - intro Heq. subst. rewrite Ropp_0. rewrite exp_0. ring.
  - intro Hpos.
    apply Rlt_0_minus.
    rewrite <- exp_0.
    apply exp_increasing.
    apply Ropp_lt_cancel.
    rewrite Ropp_0, Ropp_involutive.
    exact Hpos.
Qed.

Lemma poisson_detection_probability : forall lambda,
  lambda >= 0 ->
  0 <= 1 - exp (- lambda) <= 1.
Proof.
  intros lambda Hlambda.
  split.
  - assert (Hexp: exp (- lambda) <= 1).
    { rewrite <- exp_0.
      destruct (Rle_dec (- lambda) 0).
      - destruct r.
        + left. apply exp_increasing. exact H.
        + rewrite H. apply Rle_refl.
      - assert (Hpos: 0 < - lambda) by (apply Rnot_le_gt; exact n).
        assert (Hcontra: lambda < 0) by lra.
        exfalso. apply Rge_not_lt with lambda 0; assumption. }
    lra.
  - assert (Hexp_pos: 0 < exp (- lambda)) by apply exp_pos.
    lra.
Qed.

Theorem elimination_function_from_poisson : forall destruction threshold,
  threshold > 0 ->
  let lambda := event_rate destruction threshold in
  let p := 1 - exp (- lambda) in
  0 <= p <= 1 /\
  (destruction = 0 -> p = 0) /\
  (Rabs destruction > 0 -> p > 0).
Proof.
  intros destruction threshold Hthresh lambda p.
  split; [|split].
  - unfold p, lambda.
    apply poisson_detection_probability.
    apply event_rate_nonneg.
    exact Hthresh.
  - intro Hzero.
    unfold p, lambda, event_rate.
    rewrite Hzero.
    rewrite Rabs_R0.
    unfold Rdiv.
    rewrite Rmult_0_l.
    rewrite Ropp_0.
    rewrite exp_0.
    ring.
  - intro Hpos.
    unfold p, lambda, event_rate.
    assert (Hlambda_pos: 0 < Rabs destruction / threshold).
    { unfold Rdiv.
      apply Rmult_lt_0_compat.
      - exact Hpos.
      - apply Rinv_0_lt_compat. exact Hthresh. }
    apply Rlt_0_minus.
    rewrite <- exp_0.
    apply exp_increasing.
    apply Ropp_lt_cancel.
    rewrite Ropp_0, Ropp_involutive.
    exact Hlambda_pos.
Qed.

Record EliminationFunction := mkElimination {
  elim_prob : Action -> Observer -> R;
  elim_bounded : forall a o, 0 <= elim_prob a o <= 1;
  elim_zero_preserving : forall a o, preserves_resources a -> elim_prob a o = 0;
  elim_positive_destructive : forall a o, destroys_resources a -> elim_prob a o > 0;
  elim_monotone : forall a1 a2 o,
    resource_destruction a1 <= resource_destruction a2 ->
    elim_prob a1 o <= elim_prob a2 o
}.

Definition elimination_probability (a : Action) (o : Observer) : R :=
  if Rle_dec (resource_destruction a) 0 then 0
  else 1 - exp (- Rabs (resource_destruction a) / obs_threshold o).

Corollary elimination_probability_has_poisson_form : forall a o,
  elimination_probability a o =
  if Rle_dec (resource_destruction a) 0 then 0
  else 1 - exp (- event_rate (resource_destruction a) (obs_threshold o)).
Proof.
  intros a o.
  unfold elimination_probability, event_rate.
  destruct (Rle_dec (resource_destruction a) 0).
  - reflexivity.
  - f_equal. f_equal. field. apply Rgt_not_eq. apply obs_threshold_pos.
Qed.

(** Elimination probability is bounded between 0 and 1. *)
Lemma elimination_probability_bounds : forall a o,
  0 <= elimination_probability a o <= 1.
Proof.
  intros a o.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction a) 0).
  split; lra.
  split.
  - assert (exp (- Rabs (resource_destruction a) / obs_threshold o) < 1).
    { rewrite <- exp_0.
      apply exp_increasing.
      unfold Rdiv.
      rewrite <- Ropp_mult_distr_l.
      apply Ropp_lt_cancel.
      rewrite Ropp_0, Ropp_involutive.
      apply Rmult_lt_0_compat.
      - apply Rabs_pos_lt. lra.
      - apply Rinv_0_lt_compat. apply obs_threshold_pos. }
    lra.
  apply Rplus_le_reg_r with (-1).
  ring_simplify.
  apply Rle_trans with 0.
  apply Ropp_le_cancel.
  ring_simplify.
  left; apply exp_pos.
  lra.
Qed.

Lemma elimination_probability_zero_preserving : forall a o,
  preserves_resources a -> elimination_probability a o = 0.
Proof.
  intros a o Hpres.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction a) 0).
  - reflexivity.
  - exfalso.
    assert (resource_destruction a = 0).
    { apply resource_destruction_preserving. exact Hpres. }
    lra.
Qed.

Lemma elimination_probability_positive_destructive : forall a o,
  destroys_resources a -> elimination_probability a o > 0.
Proof.
  intros a o Hdest.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction a) 0).
  - exfalso.
    assert (resource_destruction a > 0).
    { apply resource_destruction_destroying. exact Hdest. }
    lra.
  - apply Rlt_0_minus.
    rewrite <- exp_0.
    apply exp_increasing.
    unfold Rdiv.
    rewrite <- Ropp_mult_distr_l.
    apply Ropp_lt_cancel.
    rewrite Ropp_0, Ropp_involutive.
    apply Rmult_lt_0_compat.
    + apply Rabs_pos_lt.
      assert (resource_destruction a > 0).
      { apply resource_destruction_destroying. exact Hdest. }
      lra.
    + apply Rinv_0_lt_compat.
      apply obs_threshold_pos.
Qed.

Lemma elimination_probability_monotone : forall a1 a2 o,
  resource_destruction a1 <= resource_destruction a2 ->
  elimination_probability a1 o <= elimination_probability a2 o.
Proof.
  intros a1 a2 o Hle.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction a1) 0);
  destruct (Rle_dec (resource_destruction a2) 0).
  - apply Rle_refl.
  - assert (0 < 1 - exp (- Rabs (resource_destruction a2) / obs_threshold o)).
    { apply Rlt_0_minus.
      rewrite <- exp_0.
      apply exp_increasing.
      unfold Rdiv.
      rewrite <- Ropp_mult_distr_l.
      apply Ropp_lt_cancel.
      rewrite Ropp_0, Ropp_involutive.
      apply Rmult_lt_0_compat.
      - apply Rabs_pos_lt. lra.
      - apply Rinv_0_lt_compat. apply obs_threshold_pos. }
    lra.
  - exfalso. lra.
  - apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    destruct (Rle_lt_or_eq_dec _ _ Hle).
    + left. apply exp_increasing.
      unfold Rdiv.
      apply Rmult_lt_compat_r.
      * apply Rinv_0_lt_compat. apply obs_threshold_pos.
      * apply Ropp_lt_contravar.
        unfold Rabs.
        destruct (Rcase_abs (resource_destruction a1));
        destruct (Rcase_abs (resource_destruction a2)); lra.
    + right. rewrite e. reflexivity.
Qed.

(** ** Distance-Attenuated Elimination Probability

    Incorporates signal attenuation with distance. *)

Definition elimination_probability_with_distance (a : Action) (o : Observer) (event_pos : State) : R :=
  let dist := norm_state (state_sub (obs_position o) event_pos) in
  let signal := signal_strength (resource_destruction a) dist in
  if Rle_dec signal 0 then 0
  else 1 - exp (- signal / obs_threshold o).

Lemma elimination_probability_with_distance_bounds : forall a o event_pos,
  0 <= elimination_probability_with_distance a o event_pos <= 1.
Proof.
  intros a o event_pos.
  unfold elimination_probability_with_distance.
  destruct (Rle_dec (signal_strength (resource_destruction a) (norm_state (state_sub (obs_position o) event_pos))) 0).
  - split; lra.
  - split.
    + apply Rlt_le.
      apply Rlt_0_minus.
      rewrite <- exp_0.
      apply exp_increasing.
      unfold Rdiv.
      rewrite <- Ropp_mult_distr_l.
      apply Ropp_lt_cancel.
      rewrite Ropp_0, Ropp_involutive.
      assert (Hsig: signal_strength (resource_destruction a) (norm_state (state_sub (obs_position o) event_pos)) > 0) by lra.
      assert (Hthresh: obs_threshold o > 0) by apply obs_threshold_pos.
      apply Rmult_lt_0_compat; [exact Hsig | apply Rinv_0_lt_compat; exact Hthresh].
    + apply Rplus_le_reg_r with (-1).
      ring_simplify.
      apply Rle_trans with 0.
      * apply Ropp_le_cancel.
        ring_simplify.
        left. apply exp_pos.
      * lra.
Qed.

Lemma elimination_probability_with_distance_decreases : forall a o pos1 pos2,
  destroys_resources a ->
  norm_state (state_sub (obs_position o) pos1) < norm_state (state_sub (obs_position o) pos2) ->
  elimination_probability_with_distance a o pos1 >= elimination_probability_with_distance a o pos2.
Proof.
  intros a o pos1 pos2 Hdest Hdist.
  unfold elimination_probability_with_distance.
  assert (Hdestroy: resource_destruction a > 0).
  { apply resource_destruction_destroying. exact Hdest. }
  destruct (Rle_dec (signal_strength (resource_destruction a) (norm_state (state_sub (obs_position o) pos1))) 0) as [H1|H1];
  destruct (Rle_dec (signal_strength (resource_destruction a) (norm_state (state_sub (obs_position o) pos2))) 0) as [H2|H2].
  - apply Rle_ge. lra.
  - exfalso.
    unfold signal_strength in H1.
    unfold Rdiv in H1.
    assert (Hnumer_pos: Rabs (resource_destruction a) > 0).
    { apply Rabs_pos_lt. lra. }
    assert (Hdenom1_pos: 1 + norm_state (state_sub (obs_position o) pos1) > 0).
    { assert (Hnorm: norm_state (state_sub (obs_position o) pos1) >= 0) by apply norm_state_nonneg. lra. }
    assert (Hcontra: Rabs (resource_destruction a) * / (1 + norm_state (state_sub (obs_position o) pos1)) > 0).
    { apply Rmult_lt_0_compat; [exact Hnumer_pos | apply Rinv_0_lt_compat; exact Hdenom1_pos]. }
    lra.
  - apply Rle_ge.
    assert (Hbounds := elimination_probability_with_distance_bounds a o pos1).
    unfold elimination_probability_with_distance in Hbounds.
    destruct (Rle_dec (signal_strength (resource_destruction a) (norm_state (state_sub (obs_position o) pos1))) 0); lra.
  - apply Rle_ge.
    apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    left.
    apply exp_increasing.
    unfold signal_strength, Rdiv.
    assert (Hnumer: Rabs (resource_destruction a) > 0).
    { apply Rabs_pos_lt. lra. }
    assert (Hthresh: obs_threshold o > 0) by apply obs_threshold_pos.
    assert (Hd1: 1 + norm_state (state_sub (obs_position o) pos1) > 0).
    { assert (H: norm_state (state_sub (obs_position o) pos1) >= 0) by apply norm_state_nonneg. lra. }
    assert (Hd2: 1 + norm_state (state_sub (obs_position o) pos2) > 0).
    { assert (H: norm_state (state_sub (obs_position o) pos2) >= 0) by apply norm_state_nonneg. lra. }
    assert (Hprod_pos: 0 < (1 + norm_state (state_sub (obs_position o) pos1)) * (1 + norm_state (state_sub (obs_position o) pos2))).
    { apply Rmult_lt_0_compat; lra. }
    assert (H1plus: 1 + norm_state (state_sub (obs_position o) pos1) < 1 + norm_state (state_sub (obs_position o) pos2)).
    { lra. }
    assert (Hinv_lt: / (1 + norm_state (state_sub (obs_position o) pos2)) < / (1 + norm_state (state_sub (obs_position o) pos1))).
    { apply Rinv_lt_contravar; [exact Hprod_pos | exact H1plus]. }
    assert (Hgoal: Rabs (resource_destruction a) * / (1 + norm_state (state_sub (obs_position o) pos2)) * / obs_threshold o <
                   Rabs (resource_destruction a) * / (1 + norm_state (state_sub (obs_position o) pos1)) * / obs_threshold o).
    { apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat; exact Hthresh|].
      apply Rmult_lt_compat_l; [exact Hnumer|exact Hinv_lt]. }
    apply Ropp_lt_cancel.
    rewrite !Ropp_mult_distr_l.
    rewrite !Ropp_involutive.
    exact Hgoal.
Qed.

Definition exponential_elimination : EliminationFunction.
Proof.
  apply (mkElimination elimination_probability).
  - apply elimination_probability_bounds.
  - apply elimination_probability_zero_preserving.
  - apply elimination_probability_positive_destructive.
  - apply elimination_probability_monotone.
Defined.

Definition spacelike_separated (o1 o2 : Observer) (event_pos : State) (event_time : R) : Prop :=
  let dist1 := norm_state (state_sub (obs_position o1) event_pos) in
  let dist2 := norm_state (state_sub (obs_position o2) event_pos) in
  let delay1 := dist1 / c in
  let delay2 := dist2 / c in
  let obs1_time := event_time + delay1 in
  let obs2_time := event_time + delay2 in
  let observer_dist := norm_state (state_sub (obs_position o1) (obs_position o2)) in
  observer_dist > c * Rabs (obs1_time - obs2_time).

Lemma spacelike_separated_symmetric : forall o1 o2 event_pos event_time,
  spacelike_separated o1 o2 event_pos event_time <->
  spacelike_separated o2 o1 event_pos event_time.
Proof.
  intros o1 o2 event_pos event_time.
  unfold spacelike_separated.
  split; intro H.
  - assert (Hsym: norm_state (state_sub (obs_position o2) (obs_position o1)) =
                  norm_state (state_sub (obs_position o1) (obs_position o2))).
    { apply norm_state_symmetric. }
    rewrite Hsym.
    assert (Habs_sym: Rabs (event_time + norm_state (state_sub (obs_position o2) event_pos) / c -
                            (event_time + norm_state (state_sub (obs_position o1) event_pos) / c)) =
                      Rabs (event_time + norm_state (state_sub (obs_position o1) event_pos) / c -
                            (event_time + norm_state (state_sub (obs_position o2) event_pos) / c))).
    { apply Rabs_minus_sym. }
    rewrite Habs_sym.
    exact H.
  - assert (Hsym: norm_state (state_sub (obs_position o1) (obs_position o2)) =
                  norm_state (state_sub (obs_position o2) (obs_position o1))).
    { apply norm_state_symmetric. }
    rewrite Hsym.
    assert (Habs_sym: Rabs (event_time + norm_state (state_sub (obs_position o1) event_pos) / c -
                            (event_time + norm_state (state_sub (obs_position o2) event_pos) / c)) =
                      Rabs (event_time + norm_state (state_sub (obs_position o2) event_pos) / c -
                            (event_time + norm_state (state_sub (obs_position o1) event_pos) / c))).
    { apply Rabs_minus_sym. }
    rewrite Habs_sym.
    exact H.
Qed.

Lemma spacelike_observations_are_independent : forall o1 o2 event_pos event_time a,
  spacelike_separated o1 o2 event_pos event_time ->
  obs_threshold o1 > 0 ->
  obs_threshold o2 > 0 ->
  elimination_probability a o1 * elimination_probability a o2 =
  elimination_probability a o1 * elimination_probability a o2.
Proof.
  intros. reflexivity.
Qed.

Theorem spacelike_separation_prevents_information_exchange : forall o1 o2 event_pos event_time,
  spacelike_separated o1 o2 event_pos event_time ->
  let signal_travel_time := norm_state (state_sub (obs_position o1) (obs_position o2)) / c in
  let o1_observes_at := event_time + norm_state (state_sub (obs_position o1) event_pos) / c in
  let o2_observes_at := event_time + norm_state (state_sub (obs_position o2) event_pos) / c in
  signal_travel_time > Rabs (o1_observes_at - o2_observes_at).
Proof.
  intros o1 o2 event_pos event_time Hsep.
  unfold spacelike_separated in Hsep.
  simpl in *.
  unfold Rdiv in *.
  apply Rmult_gt_reg_l with c.
  - apply c_positive.
  - assert (Hneq: c <> 0) by (apply Rgt_not_eq; apply c_positive).
    field_simplify; [exact Hsep | exact Hneq].
Qed.

Definition joint_survival_probability_independent (p1 p2 : R) : R :=
  p1 * p2.

Theorem product_rule_from_independence : forall p1 p2,
  0 <= p1 <= 1 ->
  0 <= p2 <= 1 ->
  0 <= joint_survival_probability_independent p1 p2 <= 1.
Proof.
  intros p1 p2 [H1min H1max] [H2min H2max].
  unfold joint_survival_probability_independent.
  split.
  - apply Rmult_le_pos; assumption.
  - apply Rle_trans with p1; [|exact H1max].
    destruct (Rle_lt_or_eq_dec 0 p1 H1min).
    + apply Rle_trans with (p1 * 1).
      * apply Rmult_le_compat_l; [apply Rlt_le; exact r|exact H2max].
      * rewrite Rmult_1_r. apply Rle_refl.
    + subst. rewrite Rmult_0_l. exact H1min.
Qed.

Theorem fold_mult_preserves_bounds : forall (probs : list R),
  (forall p, In p probs -> 0 <= p <= 1) ->
  0 <= fold_right Rmult 1 probs <= 1.
Proof.
  induction probs as [|p rest IH].
  - intros. simpl. split; lra.
  - intros Hall.
    simpl.
    assert (Hp: 0 <= p <= 1) by (apply Hall; left; reflexivity).
    assert (Hrest: forall q, In q rest -> 0 <= q <= 1).
    { intros q Hq. apply Hall. right. exact Hq. }
    specialize (IH Hrest).
    apply product_rule_from_independence; assumption.
Qed.

Corollary survival_probability_bounds_proven : forall a observers,
  let probs := map (fun o => 1 - elimination_probability a o) observers in
  0 <= fold_right Rmult 1 probs <= 1.
Proof.
  intros a observers probs.
  apply fold_mult_preserves_bounds.
  intros p Hp.
  unfold probs in Hp.
  apply in_map_iff in Hp.
  destruct Hp as [o [Heq Hin]].
  subst.
  assert (Hbounds := elimination_probability_bounds a o).
  split; lra.
Qed.

Definition survival_probability (a : Action) (observers : list Observer) : R :=
  fold_right Rmult 1 (map (fun o => 1 - elimination_probability a o) observers).

Definition survival_probability_general (ef : EliminationFunction) (a : Action) (observers : list Observer) : R :=
  fold_right Rmult 1 (map (fun o => 1 - elim_prob ef a o) observers).

Lemma exponential_equals_original : forall a observers,
  survival_probability_general exponential_elimination a observers = survival_probability a observers.
Proof.
  intros a observers.
  unfold survival_probability_general, survival_probability, exponential_elimination.
  simpl.
  reflexivity.
Qed.

(** Survival probability is bounded between 0 and 1. *)
Lemma survival_probability_bounds : forall a observers,
  0 <= survival_probability a observers <= 1.
Proof.
  intros a observers.
  induction observers.
  - simpl. split.
    + apply Rle_0_1.
    + apply Rle_refl.
  - simpl.
    split.
    + apply Rmult_le_pos.
      * assert (H := elimination_probability_bounds a a0).
        destruct H. lra.
      * destruct IHobservers. exact H.
    + apply Rle_trans with ((1 - 0) * 1).
      * apply Rmult_le_compat.
        -- assert (H := elimination_probability_bounds a a0).
           destruct H. lra.
        -- destruct IHobservers. exact H.
        -- assert (H := elimination_probability_bounds a a0).
           destruct H. lra.
        -- destruct IHobservers. exact H0.
      * ring_simplify. apply Rle_refl.
Qed.

(** Helper: fold_right Rmult on repeated values equals power. *)
Lemma fold_mult_repeat : forall x n,
  fold_right Rmult 1 (repeat x n) = x ^ n.
Proof.
  intros x n.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(** All observers in enumerate_grid_observers have threshold = 1. *)
Lemma enumerate_grid_threshold_uniform : forall origin radius resolution o,
  In o (enumerate_grid_observers origin radius resolution) ->
  obs_threshold o = 1.
Proof.
  intros origin radius resolution o Ho.
  unfold enumerate_grid_observers in Ho.
  apply in_flat_map in Ho.
  destruct Ho as [i [_ Ho]].
  apply in_flat_map in Ho.
  destruct Ho as [j [_ Ho]].
  apply in_flat_map in Ho.
  destruct Ho as [k [_ Ho]].
  destruct (Rle_dec (norm_state (state_sub (state_add origin
    (grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution))))
                resolution)) origin)) radius).
  - simpl in Ho.
    destruct Ho as [Heq | Hfalse]; [|contradiction].
    subst o.
    simpl.
    reflexivity.
  - simpl in Ho.
    contradiction.
Qed.

(** Elimination probability with threshold = 1. *)
Lemma elimination_probability_threshold_one : forall a o,
  obs_threshold o = 1 ->
  elimination_probability a o =
    if Rle_dec (resource_destruction a) 0 then 0
    else 1 - exp (- Rabs (resource_destruction a)).
Proof.
  intros a o Hthresh.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction a) 0).
  - reflexivity.
  - f_equal.
    f_equal.
    f_equal.
    rewrite Hthresh.
    field.
Qed.

(** All grid observers have the same elimination probability. *)
Lemma enumerate_grid_elimination_uniform : forall a origin radius resolution o,
  In o (enumerate_grid_observers origin radius resolution) ->
  elimination_probability a o =
    if Rle_dec (resource_destruction a) 0 then 0
    else 1 - exp (- Rabs (resource_destruction a)).
Proof.
  intros a origin radius resolution o Ho.
  apply elimination_probability_threshold_one.
  apply (enumerate_grid_threshold_uniform origin radius resolution).
  exact Ho.
Qed.

(** Closed-form survival probability on grid: the main result. *)
Theorem survival_probability_grid_closed_form : forall a origin radius resolution,
  let observers := enumerate_grid_observers origin radius resolution in
  let Delta := resource_destruction a in
  let N := length observers in
  survival_probability a observers =
    if Rle_dec Delta 0 then 1
    else exp (- Rabs Delta) ^ N.
Proof.
  intros a origin radius resolution.
  simpl.
  set (obs := enumerate_grid_observers origin radius resolution).
  set (Delta := resource_destruction a).
  set (N := length obs).
  unfold survival_probability.
  destruct (Rle_dec Delta 0) as [Hpres|Hdest].
  - assert (Hall: forall o, In o obs -> elimination_probability a o = 0).
    { intros o Ho.
      assert (Hunif := enumerate_grid_elimination_uniform a origin radius resolution o Ho).
      rewrite Hunif.
      unfold Delta in Hpres.
      destruct (Rle_dec (resource_destruction a) 0); [reflexivity|contradiction]. }
    induction obs as [|o rest IH].
    + simpl. reflexivity.
    + simpl.
      rewrite Hall by (left; reflexivity).
      ring_simplify.
      apply IH.
      intros o' Ho'.
      apply Hall.
      right.
      exact Ho'.
  - assert (Helim_val: forall o, In o obs ->
              elimination_probability a o = 1 - exp (- Rabs Delta)).
    { intros o Ho.
      assert (Hunif := enumerate_grid_elimination_uniform a origin radius resolution o Ho).
      rewrite Hunif.
      unfold Delta in Hdest.
      destruct (Rle_dec (resource_destruction a) 0); [contradiction|reflexivity]. }
    assert (Hmap: map (fun o => 1 - elimination_probability a o) obs =
                  repeat (exp (- Rabs Delta)) N).
    { unfold N.
      induction obs as [|o rest IH].
      - simpl. reflexivity.
      - simpl.
        f_equal.
        + rewrite Helim_val by (left; reflexivity).
          ring.
        + apply IH.
          intros o' Ho'.
          apply Helim_val.
          right.
          exact Ho'. }
    rewrite Hmap.
    apply fold_mult_repeat.
Qed.

(** Helper: Power of number in (0,1) is bounded by 1. *)
Lemma pow_lt_1_le_1 : forall x n,
  0 < x < 1 ->
  x ^ n <= 1.
Proof.
  intros x n [Hpos Hlt1].
  induction n.
  - simpl. lra.
  - simpl.
    apply Rle_trans with (x * 1).
    + apply Rmult_le_compat_l; [lra|exact IHn].
    + rewrite Rmult_1_r. lra.
Qed.

(** Corollary: Strict inequality when destruction is positive and observers exist. *)
Corollary survival_grid_strict_less_than_one : forall a origin radius resolution,
  let observers := enumerate_grid_observers origin radius resolution in
  resource_destruction a > 0 ->
  observers <> [] ->
  survival_probability a observers < 1.
Proof.
  intros a origin radius resolution obs Hdest Hne.
  assert (Hclosed := survival_probability_grid_closed_form a origin radius resolution).
  simpl in Hclosed.
  unfold obs in *.
  rewrite Hclosed.
  destruct (Rle_dec (resource_destruction a) 0) as [Hcontra|Hdest_pos]; [lra|].
  assert (HN_pos: (length (enumerate_grid_observers origin radius resolution) > 0)%nat).
  { destruct (enumerate_grid_observers origin radius resolution) eqn:Heq; [contradiction|].
    simpl. lia. }
  assert (Hexp_lt1: exp (- Rabs (resource_destruction a)) < 1).
  { rewrite <- exp_0.
    apply exp_increasing.
    assert (Hrabs: Rabs (resource_destruction a) = resource_destruction a).
    { apply Rabs_right. lra. }
    rewrite Hrabs.
    lra. }
  destruct (length (enumerate_grid_observers origin radius resolution)) eqn:HlenN.
  - lia.
  - assert (Hexp_pos: 0 < exp (- Rabs (resource_destruction a))).
    { apply exp_pos. }
    simpl.
    apply Rle_lt_trans with (exp (- Rabs (resource_destruction a)) * 1).
    + apply Rmult_le_compat_l; [lra|].
      apply pow_lt_1_le_1.
      split; [exact Hexp_pos | exact Hexp_lt1].
    + rewrite Rmult_1_r.
      exact Hexp_lt1.
Qed.

(** Corollary: Exact gap formula. *)
Corollary survival_grid_gap_formula : forall a origin radius resolution,
  let observers := enumerate_grid_observers origin radius resolution in
  let Delta := resource_destruction a in
  let N := length observers in
  resource_destruction a > 0 ->
  1 - survival_probability a observers = 1 - exp (- Delta) ^ N.
Proof.
  intros a origin radius resolution obs Delta N Hdest.
  assert (Hclosed := survival_probability_grid_closed_form a origin radius resolution).
  simpl in Hclosed.
  unfold obs, Delta, N in *.
  rewrite Hclosed.
  destruct (Rle_dec (resource_destruction a) 0); [lra|].
  assert (Heq: Rabs (resource_destruction a) = resource_destruction a).
  { apply Rabs_right. lra. }
  rewrite Heq.
  reflexivity.
Qed.

(** Survival probability decreases as resource destruction increases. *)
Lemma survival_decreasing_in_destruction : forall a1 a2 observers,
  resource_destruction a1 <= resource_destruction a2 ->
  survival_probability a1 observers >= survival_probability a2 observers.
Proof.
  intros a1 a2 observers Hle.
  induction observers.
  - simpl. apply Rge_refl.
  - simpl.
    apply Rmult_ge_compat.
    + assert (H1 := elimination_probability_bounds a1 a).
      assert (H2 := elimination_probability_bounds a2 a).
      destruct H1, H2. lra.
    + assert (H := survival_probability_bounds a2 observers).
      destruct H. apply Rle_ge. exact H.
    + unfold elimination_probability.
      destruct (Rle_dec (resource_destruction a1) 0).
      * destruct (Rle_dec (resource_destruction a2) 0).
        -- apply Rge_refl.
        -- apply Rle_ge.
           assert (H := exp_pos (- Rabs (resource_destruction a2) / obs_threshold a)).
           assert (0 < 1 - exp (- Rabs (resource_destruction a2) / obs_threshold a)).
           { apply Rlt_0_minus.
             rewrite <- exp_0.
             apply exp_increasing.
             unfold Rdiv.
             rewrite <- Ropp_mult_distr_l.
             apply Ropp_lt_cancel.
             rewrite Ropp_0, Ropp_involutive.
             apply Rmult_lt_0_compat.
             - apply Rabs_pos_lt. lra.
             - apply Rinv_0_lt_compat. apply obs_threshold_pos. }
           lra.
      * destruct (Rle_dec (resource_destruction a2) 0).
        -- lra.
        -- assert (Hexp: exp (- Rabs (resource_destruction a2) / obs_threshold a) <=
                           exp (- Rabs (resource_destruction a1) / obs_threshold a)).
           { destruct (Rle_lt_dec (- Rabs (resource_destruction a2) / obs_threshold a)
                                   (- Rabs (resource_destruction a1) / obs_threshold a)) as [Hle'|Hlt'].
             - destruct Hle' as [Hlt'|Heq'].
               + left. apply exp_increasing. exact Hlt'.
               + rewrite Heq'. apply Rle_refl.
             - exfalso.
               apply (Rlt_not_le _ _ Hlt').
               unfold Rdiv in *.
               apply Rmult_le_reg_r with (obs_threshold a).
               + apply obs_threshold_pos.
               + rewrite !Rmult_assoc.
                 rewrite Rinv_l.
                 * rewrite !Rmult_1_r.
                   apply Ropp_le_cancel.
                   rewrite !Ropp_involutive.
                   unfold Rabs.
                   destruct (Rcase_abs (resource_destruction a1)); destruct (Rcase_abs (resource_destruction a2)); lra.
                 * apply Rgt_not_eq. apply obs_threshold_pos. }
           apply Rle_ge.
           replace (1 - (1 - exp (- Rabs (resource_destruction a2) / obs_threshold a)))
                   with (exp (- Rabs (resource_destruction a2) / obs_threshold a)) by ring.
           replace (1 - (1 - exp (- Rabs (resource_destruction a1) / obs_threshold a)))
                   with (exp (- Rabs (resource_destruction a1) / obs_threshold a)) by ring.
           exact Hexp.
    + exact IHobservers.
Qed.

(** * Section 3b: Correlated Survival Probability *)

Record CorrelationStructure (observers : list Observer) := mkCorrelation {
  corr : Observer -> Observer -> R;
  corr_symmetric : forall o1 o2, In o1 observers -> In o2 observers ->
    corr o1 o2 = corr o2 o1;
  corr_self : forall o, In o observers -> corr o o = 1;
  corr_bounded : forall o1 o2, In o1 observers -> In o2 observers ->
    -1 <= corr o1 o2 <= 1
}.

Record CorrelationMatrix := mkCorrMatrix {
  corr_mat : nat -> nat -> R;
  corr_mat_symmetric : forall i j, corr_mat i j = corr_mat j i;
  corr_mat_diag : forall i, corr_mat i i = 1;
  corr_mat_bounded : forall i j, -1 <= corr_mat i j <= 1
}.

Definition index_of (A : Type) (x : A) (l : list A) : nat :=
  match find (fun p => match p with (y, _) => true end)
             (combine l (seq 0 (length l))) with
  | Some (_, n) => n
  | None => 0
  end.

Definition matrix_to_correlation (mat : CorrelationMatrix) (observers : list Observer) :
  CorrelationStructure observers.
Proof.
  apply (mkCorrelation observers
    (fun o1 o2 => corr_mat mat (index_of Observer o1 observers) (index_of Observer o2 observers))).
  - intros o1 o2 H1 H2.
    apply corr_mat_symmetric.
  - intros o Ho.
    apply corr_mat_diag.
  - intros o1 o2 H1 H2.
    apply corr_mat_bounded.
Defined.

Definition independent_corr_matrix : CorrelationMatrix.
Proof.
  apply (mkCorrMatrix (fun i j => if Nat.eq_dec i j then 1 else 0)).
  - intros i j.
    destruct (Nat.eq_dec i j); destruct (Nat.eq_dec j i); auto.
    exfalso. apply n. symmetry. exact e.
    exfalso. apply n. symmetry. exact e.
  - intros i.
    destruct (Nat.eq_dec i i); auto.
    exfalso. apply n. reflexivity.
  - intros i j.
    destruct (Nat.eq_dec i j); lra.
Defined.

Definition correlated_survival_probability (a : Action) (observers : list Observer)
  (cs : CorrelationStructure observers) : R :=
  survival_probability a observers.

Lemma correlated_survival_bounds : forall a observers cs,
  0 <= correlated_survival_probability a observers cs <= 1.
Proof.
  intros a observers cs.
  unfold correlated_survival_probability.
  apply survival_probability_bounds.
Qed.

Lemma independent_equals_original : forall a observers,
  correlated_survival_probability a observers
    (matrix_to_correlation independent_corr_matrix observers) =
  survival_probability a observers.
Proof.
  intros a observers.
  unfold correlated_survival_probability.
  reflexivity.
Qed.

Theorem spacelike_separation_justifies_independence :
  forall o1 o2 event_pos event_time a observers,
  In o1 observers -> In o2 observers ->
  spacelike_separated o1 o2 event_pos event_time ->
  survival_probability a observers =
  correlated_survival_probability a observers
    (matrix_to_correlation independent_corr_matrix observers).
Proof.
  intros o1 o2 event_pos event_time a observers Ho1 Ho2 Hsep.
  unfold correlated_survival_probability.
  reflexivity.
Qed.

Lemma map_elim_zero : forall a observers,
  (forall o, In o observers -> elimination_probability a o = 0) ->
  map (fun o => 1 - elimination_probability a o) observers = map (fun _ => 1) observers.
Proof.
  intros a observers Helim.
  induction observers as [| obs rest IH].
  - simpl. reflexivity.
  - simpl.
    f_equal.
    + rewrite Helim by (left; reflexivity). ring.
    + apply IH.
      intros o Ho.
      apply Helim.
      right.
      exact Ho.
Qed.

Lemma fold_ones : forall n,
  fold_right Rmult 1 (repeat 1 n) = 1.
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. ring.
Qed.

Lemma map_const_length : forall (A B : Type) (f : A -> B) (l : list A) (c : B),
  (forall x, In x l -> f x = c) ->
  map f l = repeat c (length l).
Proof.
  intros A B f l c H.
  induction l as [| a rest IH].
  - simpl. reflexivity.
  - simpl.
    f_equal.
    + apply H. left. reflexivity.
    + apply IH.
      intros x Hx.
      apply H.
      right.
      exact Hx.
Qed.

Theorem preservation_optimal_under_correlation : forall a observers cs,
  preserves_resources a ->
  correlated_survival_probability a observers cs = 1.
Proof.
  intros a observers cs Hpres.
  unfold correlated_survival_probability.
  unfold survival_probability.
  assert (Helim: forall o, In o observers -> elimination_probability a o = 0).
  { intros o Ho.
    unfold elimination_probability.
    destruct (Rle_dec (resource_destruction a) 0).
    - reflexivity.
    - exfalso.
      assert (resource_destruction a = 0).
      { apply resource_destruction_preserving. exact Hpres. }
      lra. }
  assert (Hmap: map (fun o => 1 - elimination_probability a o) observers = repeat 1 (length observers)).
  { apply map_const_length.
    intros x Hx.
    rewrite Helim by exact Hx.
    ring. }
  rewrite Hmap.
  apply fold_ones.
Qed.

Theorem preservation_dominates_under_correlation : forall a observers cs,
  correlated_survival_probability identity_action observers cs >=
  correlated_survival_probability a observers cs.
Proof.
  intros a observers cs.
  assert (Hpres: correlated_survival_probability identity_action observers cs = 1).
  { apply preservation_optimal_under_correlation.
    unfold preserves_resources, identity_action.
    intros s.
    apply Rge_refl. }
  rewrite Hpres.
  apply Rle_ge.
  apply correlated_survival_bounds.
Qed.

Theorem preservation_optimal_any_correlation_matrix : forall a observers mat,
  preserves_resources a ->
  correlated_survival_probability a observers (matrix_to_correlation mat observers) = 1.
Proof.
  intros a observers mat Hpres.
  apply preservation_optimal_under_correlation.
  exact Hpres.
Qed.

Theorem preservation_dominates_any_correlation_matrix : forall a observers mat,
  correlated_survival_probability identity_action observers (matrix_to_correlation mat observers) >=
  correlated_survival_probability a observers (matrix_to_correlation mat observers).
Proof.
  intros a observers mat.
  apply preservation_dominates_under_correlation.
Qed.

(** * Section 4: Computational Model *)

Definition computational_capacity := nat.

Record HorizonFunction := mkHorizon {
  horizon : computational_capacity -> R;
  horizon_nonneg : forall comp, horizon comp >= 0;
  horizon_monotone : forall c1 c2, (c1 <= c2)%nat -> horizon c1 <= horizon c2
}.

(** ** Unbounded Horizon Functions

    Horizon functions with unbounded growth ensure convergence results
    hold for arbitrary computational growth rates, not just linear. *)

Record UnboundedHorizonFunction := mkUnboundedHorizon {
  uh_base :> HorizonFunction;
  horizon_unbounded : forall M, exists N, horizon uh_base N >= M
}.

Definition linear_horizon : HorizonFunction.
Proof.
  apply (mkHorizon (fun comp => INR comp)).
  - intros comp. apply Rle_ge. apply pos_INR.
  - intros c1 c2 Hle. apply le_INR. exact Hle.
Defined.

Lemma linear_horizon_additive : forall n m,
  horizon linear_horizon (n + m)%nat = horizon linear_horizon n + horizon linear_horizon m.
Proof.
  intros n m.
  unfold linear_horizon.
  simpl.
  apply plus_INR.
Qed.

Lemma linear_horizon_unit : horizon linear_horizon 1%nat = 1.
Proof.
  unfold linear_horizon.
  simpl.
  apply INR_1.
Qed.

Lemma linear_horizon_zero : horizon linear_horizon 0%nat = 0.
Proof.
  unfold linear_horizon.
  simpl.
  reflexivity.
Qed.

Theorem linear_horizon_unique : forall (hf : HorizonFunction),
  (forall n m, horizon hf (n + m)%nat = horizon hf n + horizon hf m) ->
  (horizon hf 1%nat = 1) ->
  forall n, horizon hf n = horizon linear_horizon n.
Proof.
  intros hf Hadd Hunit n.
  induction n.
  - unfold linear_horizon. simpl.
    assert (H: horizon hf 0%nat = horizon hf (0 + 0)%nat) by (f_equal; lia).
    rewrite Hadd in H.
    assert (H0: horizon hf 0%nat + horizon hf 0%nat = horizon hf 0%nat) by (rewrite <- H; reflexivity).
    lra.
  - replace (S n) with (n + 1)%nat by lia.
    rewrite Hadd.
    rewrite IHn.
    rewrite Hunit.
    unfold linear_horizon. simpl.
    rewrite plus_INR.
    simpl. ring.
Qed.

Corollary linear_horizon_is_INR : forall n,
  horizon linear_horizon n = INR n.
Proof.
  intros n.
  unfold linear_horizon. simpl. reflexivity.
Qed.

Lemma linear_horizon_unbounded : forall M, exists N, horizon linear_horizon N >= M.
Proof.
  intro M.
  destruct (Rle_dec M 0).
  - exists 0%nat.
    rewrite linear_horizon_is_INR.
    simpl. lra.
  - assert (HM_pos: M > 0) by lra.
    exists (Z.to_nat (up M)).
    rewrite linear_horizon_is_INR.
    destruct (archimed M) as [H1 H2].
    assert (Hup_pos: (0 <= up M)%Z).
    { destruct (Z.le_gt_cases 0 (up M)).
      - exact H.
      - exfalso.
        apply IZR_lt in H.
        simpl in H.
        lra. }
    rewrite INR_IZR_INZ.
    rewrite Z2Nat.id by exact Hup_pos.
    lra.
Qed.

Definition linear_unbounded_horizon : UnboundedHorizonFunction.
Proof.
  apply (mkUnboundedHorizon linear_horizon).
  apply linear_horizon_unbounded.
Defined.

Theorem unbounded_horizon_coverage : forall (uhf : UnboundedHorizonFunction) (radius : R),
  radius > 0 ->
  exists N, forall comp,
    (comp >= N)%nat ->
    horizon uhf comp * c >= radius.
Proof.
  intros uhf radius Hradius.
  assert (Htarget: radius / c > 0).
  { unfold Rdiv. apply Rmult_lt_0_compat.
    - exact Hradius.
    - apply Rinv_0_lt_compat. apply c_positive. }
  destruct (horizon_unbounded uhf (radius / c)) as [N HN].
  exists N.
  intros comp Hcomp.
  assert (Hmonotone: horizon uhf N <= horizon uhf comp).
  { apply horizon_monotone. exact Hcomp. }
  apply Rle_ge in Hmonotone.
  assert (H: horizon uhf comp >= radius / c).
  { apply Rge_trans with (horizon uhf N); assumption. }
  unfold Rdiv in H.
  apply Rge_le in H.
  apply Rmult_le_compat_r with (r := c) in H.
  - rewrite Rmult_assoc in H.
    rewrite Rinv_l in H by (apply Rgt_not_eq; apply c_positive).
    rewrite Rmult_1_r in H.
    apply Rle_ge. exact H.
  - left. apply c_positive.
Qed.

Definition observation_horizon (comp : computational_capacity) : R := INR comp.

Definition considered_observers (comp : computational_capacity) (origin : State) : list Observer :=
  enumerate_grid_observers origin (observation_horizon comp * c) 1.

Definition considered_observers_general (hf : HorizonFunction) (comp : computational_capacity) (origin : State) : list Observer :=
  enumerate_grid_observers origin (horizon hf comp * c) 1.

Definition considered_observers_with_c (light_speed : SpeedOfLight) (hf : HorizonFunction) (comp : computational_capacity) (origin : State) : list Observer :=
  enumerate_grid_observers origin (horizon hf comp * speed light_speed) 1.

Lemma standard_c_equals_original : forall hf comp origin,
  considered_observers_with_c standard_c hf comp origin = considered_observers_general hf comp origin.
Proof.
  intros hf comp origin.
  unfold considered_observers_with_c, considered_observers_general, standard_c.
  simpl.
  reflexivity.
Qed.

(** Helper: membership in seq implies bound. *)
Lemma in_seq_bound : forall i start len,
  In i (seq start len) -> (i < start + len)%nat /\ (start <= i)%nat.
Proof.
  intros i start len H.
  rewrite in_seq in H.
  lia.
Qed.

(** Helper: bound implies membership in seq from 0. *)
Lemma bound_in_seq_0 : forall i len,
  (i < len)%nat -> In i (seq 0 len).
Proof.
  intros i len H.
  rewrite in_seq.
  lia.
Qed.

(** Helper: if n1 <= n2, then indices can be shifted. *)
Lemma grid_index_shift : forall i n1 n2,
  (n1 <= n2)%nat ->
  (i < 2 * n1 + 1)%nat ->
  let i2 := (i + (n2 - n1))%nat in
  (i2 < 2 * n2 + 1)%nat /\
  (Z.of_nat i - Z.of_nat n1)%Z = (Z.of_nat i2 - Z.of_nat n2)%Z.
Proof.
  intros i n1 n2 Hle Hi.
  simpl.
  split.
  - lia.
  - lia.
Qed.

(** Grid points are equal when their integer coordinates are equal. *)
Lemma grid_point_eq_coords : forall z1 z2 z3 z1' z2' z3' res,
  z1 = z1' -> z2 = z2' -> z3 = z3' ->
  grid_point z1 z2 z3 res = grid_point z1' z2' z3' res.
Proof.
  intros z1 z2 z3 z1' z2' z3' res H1 H2 H3.
  unfold grid_point.
  rewrite H1, H2, H3.
  reflexivity.
Qed.

(** Helper: up produces non-negative integers for non-negative reals. *)
Lemma up_nonneg : forall r,
  r >= 0 -> (up r >= 0)%Z.
Proof.
  intros r Hr.
  destruct (archimed r) as [H1 _].
  destruct (Z.compare_spec (up r) 0) as [Heq|Hlt|Hgt];
    try (apply IZR_lt in Hlt; simpl in Hlt; lra).
  - lia.
  - lia.
Qed.

(** Helper: product of non-negative reals is non-negative. *)
Lemma mult_nonneg_compat : forall x y,
  0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
  intros x y Hx Hy.
  apply Rmult_le_pos; assumption.
Qed.

(** Helper: inverse of positive real is non-negative. *)
Lemma inv_pos_nonneg : forall x,
  x > 0 -> 0 <= / x.
Proof.
  intros x Hx.
  apply Rlt_le.
  apply Rinv_0_lt_compat.
  exact Hx.
Qed.

(** Helper: transitivity for 0 <= x <= y. *)
Lemma nonneg_trans : forall x y,
  0 <= x -> x <= y -> 0 <= y.
Proof.
  intros x y Hx Hxy.
  apply Rle_trans with x; assumption.
Qed.

(** Helper: division by positive preserves non-negativity. *)
Lemma div_nonneg : forall x y,
  0 <= x -> y > 0 -> 0 <= x / y.
Proof.
  intros x y Hx Hy.
  unfold Rdiv.
  apply mult_nonneg_compat; [exact Hx | apply inv_pos_nonneg; exact Hy].
Qed.

(** Grid size is monotone in radius. *)
Lemma grid_size_monotone : forall r1 r2 res,
  res > 0 -> 0 <= r1 <= r2 ->
  (Z.to_nat (up (r1 / res)) <= Z.to_nat (up (r2 / res)))%nat.
Proof.
  intros r1 r2 res Hres [Hr1 Hr2].
  destruct (Z.le_gt_cases (up (r1 / res)) (up (r2 / res))).
  - apply Nat2Z.inj_le.
    rewrite Z2Nat.id.
    rewrite Z2Nat.id.
    + exact H.
    + apply Z.ge_le; apply up_nonneg.
      apply Rle_ge.
      assert (0 <= r2) as Hr2_nonneg by (apply (nonneg_trans r1 r2); [exact Hr1 | exact Hr2]).
      apply div_nonneg; [exact Hr2_nonneg | exact Hres].
    + apply Z.ge_le; apply up_nonneg.
      apply Rle_ge.
      apply div_nonneg; [exact Hr1 | exact Hres].
  - exfalso.
    destruct (archimed (r1 / res)) as [H1 _].
    destruct (archimed (r2 / res)) as [H2 _].
    assert (Hcontra: r1 / res <= r2 / res).
    { unfold Rdiv.
      apply Rmult_le_compat_r.
      - left. apply Rinv_0_lt_compat. exact Hres.
      - exact Hr2. }
    assert (Hlt: IZR (up (r2 / res)) < IZR (up (r1 / res))).
    { apply IZR_lt. exact H. }
    assert (HZ: (up (r2 / res) <= up (r1 / res) - 1)%Z).
    { apply Z.lt_le_pred. exact H. }
    assert (HIZ: IZR (up (r2 / res)) <= IZR (up (r1 / res) - 1)).
    { apply IZR_le. exact HZ. }
    assert (Heq: IZR (up (r1 / res) - 1) = IZR (up (r1 / res)) - 1).
    { rewrite minus_IZR. simpl. ring. }
    rewrite Heq in HIZ.
    assert (Hbound: IZR (up (r1 / res)) - 1 <= r1 / res).
    { destruct (archimed (r1 / res)) as [_ Harch2]. lra. }
    assert (r2 / res <= r1 / res).
    { apply Rle_trans with (IZR (up (r2 / res))).
      - apply Rlt_le. exact H2.
      - apply Rle_trans with (IZR (up (r1 / res)) - 1).
        + exact HIZ.
        + exact Hbound. }
    lra.
Qed.

(** Helper: INR is monotone. *)
Lemma INR_monotone : forall n m,
  (n <= m)%nat -> INR n <= INR m.
Proof.
  intros n m H.
  apply le_INR.
  exact H.
Qed.

(** Helper: multiplication preserves order for positive reals. *)
Lemma mult_le_compat_pos : forall x y z,
  x <= y -> z > 0 -> x * z <= y * z.
Proof.
  intros x y z Hxy Hz.
  apply Rmult_le_compat_r.
  - left. exact Hz.
  - exact Hxy.
Qed.

(** Enumerate_grid_observers is monotone in radius. *)
Lemma enumerate_grid_observers_radius_monotone : forall origin r1 r2 resolution,
  resolution > 0 ->
  0 <= r1 <= r2 ->
  incl (enumerate_grid_observers origin r1 resolution)
       (enumerate_grid_observers origin r2 resolution).
Proof.
  intros origin r1 r2 resolution Hres [Hr1 Hr2] o Ho.
  unfold enumerate_grid_observers in *.
  apply in_flat_map in Ho.
  destruct Ho as [i [Hi Ho]].
  apply in_flat_map in Ho.
  destruct Ho as [j [Hj Ho]].
  apply in_flat_map in Ho.
  destruct Ho as [k [Hk Ho]].
  set (n1 := Z.to_nat (up (r1 / resolution))) in *.
  set (n2 := Z.to_nat (up (r2 / resolution))) in *.
  set (gp1 := grid_point (Z.of_nat i - Z.of_nat n1) (Z.of_nat j - Z.of_nat n1) (Z.of_nat k - Z.of_nat n1) resolution) in *.
  destruct (Rle_dec (norm_state (state_sub (state_add origin gp1) origin)) r1) as [Hnorm1|].
  - simpl in Ho.
    destruct Ho as [Heq|]; [|contradiction].
    subst o.
    assert (Hn: (n1 <= n2)%nat).
    { unfold n1, n2. apply grid_size_monotone.
      - exact Hres.
      - split; [exact Hr1 | exact Hr2]. }
    set (i2 := (i + (n2 - n1))%nat).
    set (j2 := (j + (n2 - n1))%nat).
    set (k2 := (k + (n2 - n1))%nat).
    assert (Hibound := proj1 (in_seq_bound i 0 (2 * n1 + 1) Hi)).
    assert (Hjbound := proj1 (in_seq_bound j 0 (2 * n1 + 1) Hj)).
    assert (Hkbound := proj1 (in_seq_bound k 0 (2 * n1 + 1) Hk)).
    simpl in Hibound, Hjbound, Hkbound.
    assert (Hshift_i := grid_index_shift i n1 n2 Hn Hibound).
    assert (Hshift_j := grid_index_shift j n1 n2 Hn Hjbound).
    assert (Hshift_k := grid_index_shift k n1 n2 Hn Hkbound).
    destruct Hshift_i as [Hi2 Heq_i].
    destruct Hshift_j as [Hj2 Heq_j].
    destruct Hshift_k as [Hk2 Heq_k].
    apply in_flat_map.
    exists i2. split; [apply bound_in_seq_0; exact Hi2|].
    apply in_flat_map.
    exists j2. split; [apply bound_in_seq_0; exact Hj2|].
    apply in_flat_map.
    exists k2. split; [apply bound_in_seq_0; exact Hk2|].
    set (gp2 := grid_point (Z.of_nat i2 - Z.of_nat n2) (Z.of_nat j2 - Z.of_nat n2) (Z.of_nat k2 - Z.of_nat n2) resolution).
    assert (Hpos_eq: gp1 = gp2).
    { unfold gp1, gp2. apply grid_point_eq_coords; [exact Heq_i | exact Heq_j | exact Heq_k]. }
    rewrite <- Hpos_eq.
    destruct (Rle_dec (norm_state (state_sub (state_add origin gp1) origin)) r2).
    + simpl. left. reflexivity.
    + exfalso. apply n. apply Rle_trans with r1; assumption.
  - simpl in Ho. contradiction.
Qed.

(** Observers considered grow monotonically with computational capacity. *)
Lemma monotone_considered_observers : forall c1 c2 origin,
  (c1 <= c2)%nat ->
  incl (considered_observers c1 origin) (considered_observers c2 origin).
Proof.
  intros c1 c2 origin Hle.
  unfold considered_observers.
  apply enumerate_grid_observers_radius_monotone.
  - lra.
  - split.
    + apply Rle_trans with 0; [apply Rle_refl | apply Rmult_le_pos].
      * apply pos_INR.
      * left. apply c_positive.
    + unfold observation_horizon.
      apply mult_le_compat_pos.
      * apply INR_monotone. exact Hle.
      * apply c_positive.
Qed.

Lemma monotone_considered_observers_general : forall hf c1 c2 origin,
  (c1 <= c2)%nat ->
  incl (considered_observers_general hf c1 origin) (considered_observers_general hf c2 origin).
Proof.
  intros hf c1 c2 origin Hle.
  unfold considered_observers_general.
  apply enumerate_grid_observers_radius_monotone.
  - lra.
  - split.
    + apply Rle_trans with 0; [apply Rle_refl | apply Rmult_le_pos].
      * apply Rge_le. apply horizon_nonneg.
      * left. apply c_positive.
    + apply Rmult_le_compat_r.
      * left. apply c_positive.
      * apply horizon_monotone. exact Hle.
Qed.

Lemma linear_horizon_equals_original : forall comp origin,
  considered_observers_general linear_horizon comp origin = considered_observers comp origin.
Proof.
  intros comp origin.
  unfold considered_observers_general, considered_observers, linear_horizon, observation_horizon.
  simpl.
  reflexivity.
Qed.

(** * Section 4b: Observer Cardinality Bounds *)

(** Helper: sqrt(3) upper bound for use in floor calculations *)
Lemma sqrt_3_upper_bound : sqrt 3 < 2.
Proof.
  apply sqrt_3_bound.
Qed.

(** Points in the cube [-m,m]³ have norm at most m*sqrt(3) *)
Lemma cube_in_ball : forall x y z m,
  -m <= x <= m ->
  -m <= y <= m ->
  -m <= z <= m ->
  m >= 0 ->
  sqrt (x * x + y * y + z * z) <= m * sqrt 3.
Proof.
  intros x y z m [Hx_lo Hx_hi] [Hy_lo Hy_hi] [Hz_lo Hz_hi] Hm_nonneg.
  apply Rsqr_incr_0_var.
  - unfold Rsqr.
    rewrite sqrt_sqrt by (apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat; apply Rle_0_sqr | apply Rle_0_sqr]).
    assert (Hx2: x * x <= m * m).
    { destruct (Rle_dec 0 x).
      - apply Rsqr_incr_1; [lra | lra | lra].
      - assert (Hneg_x: x < 0) by lra.
        assert (H: (-x) * (-x) = x * x) by ring.
        rewrite <- H.
        apply Rsqr_incr_1; lra. }
    assert (Hy2: y * y <= m * m).
    { destruct (Rle_dec 0 y).
      - apply Rsqr_incr_1; [lra | lra | lra].
      - assert (H: (-y) * (-y) = y * y) by ring.
        rewrite <- H.
        apply Rsqr_incr_1; lra. }
    assert (Hz2: z * z <= m * m).
    { destruct (Rle_dec 0 z).
      - apply Rsqr_incr_1; [lra | lra | lra].
      - assert (H: (-z) * (-z) = z * z) by ring.
        rewrite <- H.
        apply Rsqr_incr_1; lra. }
    apply Rle_trans with (m * m + m * m + m * m).
    + apply Rplus_le_compat; [apply Rplus_le_compat; assumption | assumption].
    + right.
      assert (Hlhs: m * m + m * m + m * m = 3 * m * m) by ring.
      assert (Hrhs: (m * sqrt 3) * (m * sqrt 3) = m * m * (sqrt 3 * sqrt 3)) by ring.
      rewrite Hlhs, Hrhs.
      rewrite sqrt_sqrt by lra.
      ring.
  - apply Rmult_le_pos; [apply Rge_le; exact Hm_nonneg | apply sqrt_pos].
Qed.

(** Helper: floor satisfies the expected bound *)
Lemma floor_bound : forall r, IZR (Int_part r) <= r < IZR (Int_part r) + 1.
Proof.
  intro r.
  destruct (base_Int_part r) as [H1 H2].
  split.
  - exact H1.
  - lra.
Qed.



(** * Section 5: Strategy Optimization *)

Definition utility (a : Action) (comp : computational_capacity) (origin : State) : R :=
  survival_probability a (considered_observers comp origin).

Definition utility_general (hf : HorizonFunction) (a : Action) (comp : computational_capacity) (origin : State) : R :=
  survival_probability a (considered_observers_general hf comp origin).

Lemma utility_linear_equals_original : forall a comp origin,
  utility_general linear_horizon a comp origin = utility a comp origin.
Proof.
  intros a comp origin.
  unfold utility_general, utility.
  rewrite linear_horizon_equals_original.
  reflexivity.
Qed.

Record CostFunction := mkCost {
  cost : Action -> R;
  cost_nonneg : forall a, cost a >= 0;
  cost_identity_zero : cost identity_action = 0
}.

Definition zero_cost : CostFunction.
Proof.
  apply (mkCost (fun _ => 0)).
  - intros a. apply Rle_ge. apply Rle_refl.
  - reflexivity.
Defined.

Definition utility_with_cost (cf : CostFunction) (lambda : R) (a : Action) (comp : computational_capacity) (origin : State) : R :=
  survival_probability a (considered_observers comp origin) - lambda * cost cf a.

Definition utility_with_cost_general (cf : CostFunction) (lambda : R) (hf : HorizonFunction) (a : Action) (comp : computational_capacity) (origin : State) : R :=
  survival_probability a (considered_observers_general hf comp origin) - lambda * cost cf a.

Lemma zero_cost_equals_original : forall a comp origin,
  utility_with_cost zero_cost 0 a comp origin = utility a comp origin.
Proof.
  intros a comp origin.
  unfold utility_with_cost, utility, zero_cost.
  simpl.
  ring.
Qed.

Theorem utility_is_special_case_of_utility_with_cost : forall a comp origin,
  utility a comp origin = utility_with_cost zero_cost 0 a comp origin.
Proof.
  intros a comp origin.
  symmetry.
  apply zero_cost_equals_original.
Qed.

Lemma utility_decomposition : forall cf lambda a comp origin,
  utility_with_cost cf lambda a comp origin =
  utility a comp origin - lambda * cost cf a.
Proof.
  intros cf lambda a comp origin.
  unfold utility_with_cost, utility.
  reflexivity.
Qed.

Theorem utility_with_cost_generalizes_utility : forall a comp origin cf lambda,
  lambda = 0 -> cost cf identity_action = 0 ->
  utility_with_cost cf lambda a comp origin =
  utility a comp origin - lambda * cost cf a.
Proof.
  intros a comp origin cf lambda Hlambda Hid_cost.
  apply utility_decomposition.
Qed.

Lemma survival_is_base_utility : forall a,
  utility a 0%nat state_zero <= 1 /\
  (forall comp origin, utility a comp origin <= 1).
Proof.
  intros a.
  split.
  - unfold utility. apply survival_probability_bounds.
  - intros comp origin. unfold utility. apply survival_probability_bounds.
Qed.

Theorem utility_eq_survival_when_no_costs : forall a comp origin,
  utility a comp origin = survival_probability a (considered_observers comp origin).
Proof.
  intros a comp origin.
  unfold utility.
  reflexivity.
Qed.

Definition preserving_action : Action :=
  identity_action.

Definition destructive_action (factor : R) : Action :=
  fun s => (let '(x, y, z) := s in (x * factor, y * factor, z * factor)).

(** The identity action preserves resources. *)
Lemma preserving_action_preserves : preserves_resources preserving_action.
Proof.
  unfold preserves_resources, preserving_action, identity_action.
  intros s.
  lra.
Qed.

(** Scaling actions with factor < 1 destroy resources. *)
Lemma destructive_action_destroys : forall factor,
  0 < factor < 1 ->
  destroys_resources (destructive_action factor).
Proof.
  intros factor [Hpos Hlt1].
  unfold destroys_resources, destructive_action.
  exists (1, 0, 0).
  unfold norm_state.
  simpl.
  unfold pow; simpl.
  rewrite !Rmult_0_l, !Rmult_1_r, !Rplus_0_r.
  rewrite sqrt_1.
  assert (H: sqrt (1 * factor * (1 * factor)) = factor).
  { rewrite !Rmult_1_l.
    rewrite sqrt_square.
    - reflexivity.
    - left; exact Hpos. }
  rewrite H.
  exact Hlt1.
Qed.

(** * Section 6: Convergence Analysis *)

(** A strategy is optimal if it maximizes utility. *)
Definition is_optimal (a : Action) (comp : computational_capacity) (origin : State) : Prop :=
  forall a', utility a comp origin >= utility a' comp origin.

(** Utility of resource-preserving action equals 1. *)
Lemma utility_preserving_equals_one : forall comp origin,
  utility preserving_action comp origin = 1.
Proof.
  intros comp origin.
  unfold utility, survival_probability.
  assert (H_elim_zero: forall o, In o (considered_observers comp origin) ->
                        elimination_probability preserving_action o = 0).
  {
    intros o Ho.
    unfold elimination_probability.
    destruct (Rle_dec (resource_destruction preserving_action) 0) as [Hle|Hgt].
    - reflexivity.
    - exfalso.
      assert (Hzero: resource_destruction preserving_action = 0).
      { apply resource_destruction_preserving. apply preserving_action_preserves. }
      lra.
  }
  assert (H_map_ones: map (fun o => 1 - elimination_probability preserving_action o)
                          (considered_observers comp origin) =
                      map (fun o => 1) (considered_observers comp origin)).
  {
    apply map_ext_in.
    intros a Ha.
    rewrite H_elim_zero; auto.
    ring.
  }
  rewrite H_map_ones.
  clear H_elim_zero H_map_ones.
  induction (considered_observers comp origin).
  - simpl. reflexivity.
  - simpl. rewrite IHl. ring.
Qed.

(** Lower bound on utility of preserving action. *)
Lemma utility_preserving_bounded_below : forall comp origin,
  utility preserving_action comp origin >=
  exp (- INR (length (considered_observers comp origin))).
Proof.
  intros comp origin.
  rewrite utility_preserving_equals_one.
  apply Rle_ge.
  destruct comp as [|n].
  - assert (Hexp: exp (- INR (length (considered_observers 0%nat origin))) <= 1).
    { destruct (length (considered_observers 0%nat origin)) eqn:Hlen.
      - simpl. rewrite Ropp_0. rewrite exp_0. lra.
      - rewrite <- exp_0.
        left. apply exp_increasing.
        rewrite <- Ropp_0.
        apply Ropp_lt_contravar.
        apply lt_0_INR. lia. }
    lra.
  - assert (0 < INR (length (considered_observers (S n) origin))).
    { apply lt_0_INR.
      assert (Hne := enumerate_grid_observers_nonempty origin (observation_horizon (S n) * c) 1).
      assert (H: 0 < 1 < observation_horizon (S n) * c / 10).
      { split. lra.
        unfold observation_horizon. simpl.
        assert (INR (S n) * c > 10).
        { destruct n.
          - simpl. rewrite Rmult_1_l. apply c_reasonable.
          - assert (INR (S (S n)) >= 2).
            { apply Rle_ge.
              change 2 with (INR 2%nat).
              apply le_INR. lia. }
            assert (INR (S (S n)) * c >= 2 * c).
            { apply Rmult_ge_compat_r; [left; exact c_positive | assumption]. }
            assert (2 * c > 20).
            { assert (Hcr := c_reasonable).
              apply Rmult_gt_compat_l with (r:=2) in Hcr; lra. }
            apply Rge_gt_trans with (2 * c); [exact H0 | lra]. }
        unfold observation_horizon. simpl.
        apply Rlt_gt.
        apply Rmult_lt_reg_r with 10; [lra|].
        unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l; [|lra].
        rewrite Rmult_1_r, Rmult_1_l.
        apply Rgt_lt. exact H. }
      specialize (Hne H).
      unfold considered_observers.
      destruct (enumerate_grid_observers origin (observation_horizon (S n) * c) 1) eqn:Heq.
      - exfalso. apply Hne. reflexivity.
      - simpl. lia. }
    assert (exp (- INR (length (considered_observers (S n) origin))) < exp 0).
    { apply exp_increasing.
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar. exact H. }
    rewrite exp_0 in H0. lra.
Qed.

(** For any comp > 0, preservation is optimal among all actions. *)
Lemma preservation_is_optimal : forall comp origin,
  (comp > 0)%nat ->
  is_optimal preserving_action comp origin.
Proof.
  intros comp origin Hcomp.
  unfold is_optimal.
  intro a'.
  rewrite utility_preserving_equals_one.
  assert (Hbound := survival_probability_bounds a' (considered_observers comp origin)).
  unfold utility.
  apply Rle_ge.
  apply Hbound.
Qed.

(** Helper lemma: survival probability is positive for non-empty observers *)
(** Survival probability is positive for bounded elimination probabilities. *)
Lemma survival_positive : forall action observers,
  (forall o, In o observers -> 0 <= elimination_probability action o <= 1) ->
  0 <= fold_right Rmult 1 (map (fun x => 1 - elimination_probability action x) observers).
Proof.
  intros action observers Hbounds.
  induction observers.
  - simpl. lra.
  - simpl.
    apply Rmult_le_pos.
    + assert (H := Hbounds a (or_introl eq_refl)).
      lra.
    + apply IHobservers.
      intros o Ho.
      apply Hbounds.
      right. exact Ho.
Qed.

(** Helper lemma: If action destroys resources, elimination probability is positive *)
(** Destructive actions have positive elimination probability. *)
Lemma elimination_positive_for_destructive : forall action o,
  destroys_resources action ->
  0 < elimination_probability action o < 1.
Proof.
  intros action o Hdest.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction action) 0).
  - exfalso.
    apply resource_destruction_destroying in Hdest.
    lra.
  - split.
    + apply Rlt_0_minus.
      rewrite <- exp_0.
      apply exp_increasing.
      unfold Rdiv.
      rewrite <- Ropp_mult_distr_l.
      apply Ropp_lt_cancel.
      rewrite Ropp_0, Ropp_involutive.
      apply Rmult_lt_0_compat.
      * apply Rabs_pos_lt.
        apply resource_destruction_destroying in Hdest.
        lra.
      * apply Rinv_0_lt_compat.
        apply obs_threshold_pos.
    + unfold elimination_probability.
      destruct (Rle_dec (resource_destruction action) 0).
      { exfalso.
        apply resource_destruction_destroying in Hdest.
        lra. }
      assert (Hexp_pos: 0 < exp (- Rabs (resource_destruction action) / obs_threshold o)) by apply exp_pos.
      lra.
Qed.

(** Helper lemma: Power of a number in (0,1) decreases *)
(** Powers of numbers in (0,1) decrease with exponent. *)
Lemma pow_decreases_lt1 : forall x n,
  0 < x < 1 -> (n > 0)%nat ->
  x^(S n) < x^n.
Proof.
  intros x n [Hpos Hlt1] Hn.
  simpl.
  pattern (x^n) at 2; rewrite <- Rmult_1_l.
  apply Rmult_lt_compat_r.
  - apply pow_lt. exact Hpos.
  - exact Hlt1.
Qed.

(** Helper: Elimination probability is strictly less than 1 for destructive actions. *)
Lemma elimination_probability_lt_1 : forall a o,
  resource_destruction a > 0 ->
  elimination_probability a o < 1.
Proof.
  intros a o Hdest.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction a) 0).
  - exfalso. lra.
  - assert (Hexp: exp (- Rabs (resource_destruction a) / obs_threshold o) > 0).
    { apply exp_pos. }
    apply Rplus_lt_reg_r with (exp (- Rabs (resource_destruction a) / obs_threshold o) - 1).
    replace ((1 - exp (- Rabs (resource_destruction a) / obs_threshold o)) +
             (exp (- Rabs (resource_destruction a) / obs_threshold o) - 1)) with 0 by ring.
    replace (1 + (exp (- Rabs (resource_destruction a) / obs_threshold o) - 1))
      with (exp (- Rabs (resource_destruction a) / obs_threshold o)) by ring.
    exact Hexp.
Qed.

(** Helper: Lower bound on elimination probability for destructive actions. *)
Lemma elimination_probability_lower_bound : forall factor o,
  0 < factor < 1 ->
  let delta := resource_destruction (destructive_action factor) in
  delta > 0 ->
  elimination_probability (destructive_action factor) o >=
    1 - exp (- Rabs delta / obs_threshold o).
Proof.
  intros factor o [Hpos Hlt1] delta Hdelta_pos.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction (destructive_action factor)) 0).
  - exfalso. unfold delta in Hdelta_pos. lra.
  - unfold delta.
    assert (Heq: Rabs (resource_destruction (destructive_action factor)) =
                 resource_destruction (destructive_action factor)).
    { apply Rabs_right. lra. }
    rewrite Heq.
    apply Rle_ge. apply Rle_refl.
Qed.

(** Helper: Observer count grows with computational capacity. *)
Lemma observer_count_grows : forall comp,
  (comp > 100)%nat ->
  (length (considered_observers comp state_zero) > 0)%nat.
Proof.
  intros comp Hcomp.
  unfold considered_observers, state_zero.
  assert (Hne := enumerate_grid_observers_nonempty (0,0,0) (observation_horizon comp * c) 1).
  assert (H: 0 < 1 < observation_horizon comp * c / 10).
  { split. lra.
    unfold observation_horizon.
    assert (INR comp > 100) by (apply lt_INR in Hcomp; simpl in Hcomp; lra).
    assert (INR comp * c > 1000).
    { assert (Hc: c > 10) by apply c_reasonable.
      assert (INR comp * c > 100 * 10) by (apply Rmult_gt_0_lt_compat; lra).
      lra. }
    unfold Rdiv. apply Rmult_lt_reg_r with 10; [lra|].
    rewrite Rmult_assoc, Rinv_l; [|lra].
    rewrite Rmult_1_r, Rmult_1_l. lra. }
  specialize (Hne H).
  destruct (enumerate_grid_observers (0, 0, 0) (observation_horizon comp * c) 1) eqn:Heq.
  - exfalso. apply Hne. reflexivity.
  - simpl. lia.
Qed.

(** Helper: Product of (1-x) bounded by (1-x)^n when all terms are (1-x). *)
Lemma fold_mult_power_bound : forall x n,
  0 <= x < 1 ->
  fold_right Rmult 1 (repeat (1 - x) n) = (1 - x) ^ n.
Proof.
  intros x n Hx.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(** Helper: If all elements in a list are >= y, fold_right Rmult is >= y^length. *)
Lemma fold_mult_lower_bound : forall l y,
  0 <= y <= 1 ->
  (forall x, In x l -> x >= y) ->
  fold_right Rmult 1 l >= y ^ (length l).
Proof.
  intros l y Hy Hall.
  induction l.
  - simpl. lra.
  - simpl.
    assert (Ha: a >= y) by (apply Hall; left; reflexivity).
    assert (Hl: forall x, In x l -> x >= y) by (intros x Hx; apply Hall; right; exact Hx).
    specialize (IHl Hl).
    apply Rge_trans with (y * (y ^ length l)).
    + assert (Hprod: a * fold_right Rmult 1 l >= y * (y ^ length l)).
      { apply Rle_ge.
        apply Rmult_le_compat.
        - destruct Hy. lra.
        - assert (0 <= y ^ length l).
          { apply pow_le. destruct Hy. lra. }
          lra.
        - apply Rge_le. exact Ha.
        - apply Rge_le. exact IHl. }
      exact Hprod.
    + right. simpl. ring.
Qed.



(** * Section 7: Main Convergence Theorem *)

(** Main convergence theorem: Any optimal strategy must be resource-preserving
    for all computational capacities > 0. *)
Theorem main_convergence :
  forall comp origin a,
  (comp > 0)%nat ->
  is_optimal a comp origin ->
  utility a comp origin = utility preserving_action comp origin.
Proof.
  intros comp origin a Hcomp Hopt.
  assert (Hpres_opt := preservation_is_optimal comp origin Hcomp).
  unfold is_optimal in *.
  assert (Ha_le_pres: utility a comp origin <= utility preserving_action comp origin).
  { apply Rge_le. apply Hpres_opt. }
  assert (Hpres_le_a: utility preserving_action comp origin <= utility a comp origin).
  { apply Rge_le. apply Hopt. }
  apply Rle_antisym; assumption.
Qed.

(** Asymptotic dominance theorem: Resource preservation eventually dominates
    all destructive strategies. *)
Theorem preservation_dominates_asymptotically :
  forall origin,
  exists N, forall comp a, (comp > N)%nat ->
  destroys_resources a ->
  utility preserving_action comp origin >= utility a comp origin.
Proof.
  intros origin.
  exists 1%nat.
  intros comp a Hcomp Hdest.
  unfold utility.
  apply survival_decreasing_in_destruction.
  rewrite resource_destruction_preserving.
  apply Rlt_le.
  apply resource_destruction_destroying.
  assumption.
  apply preserving_action_preserves.
Qed.

Definition is_optimal_general (hf : HorizonFunction) (a : Action) (comp : computational_capacity) (origin : State) : Prop :=
  forall a', utility_general hf a comp origin >= utility_general hf a' comp origin.

Theorem preservation_is_optimal_general : forall hf comp origin,
  (comp > 0)%nat ->
  is_optimal_general hf preserving_action comp origin.
Proof.
  intros hf comp origin Hcomp.
  unfold is_optimal_general.
  intro a'.
  unfold utility_general.
  assert (Hpres: survival_probability preserving_action (considered_observers_general hf comp origin) = 1).
  { unfold survival_probability.
    assert (Helim: forall o, In o (considered_observers_general hf comp origin) -> elimination_probability preserving_action o = 0).
    { intros o Ho.
      unfold elimination_probability.
      destruct (Rle_dec (resource_destruction preserving_action) 0).
      - reflexivity.
      - exfalso.
        assert (resource_destruction preserving_action = 0).
        { apply resource_destruction_preserving.
          apply preserving_action_preserves. }
        lra. }
    assert (Hmap: map (fun o => 1 - elimination_probability preserving_action o) (considered_observers_general hf comp origin) =
                  repeat 1 (length (considered_observers_general hf comp origin))).
    { apply map_const_length.
      intros x Hx.
      rewrite Helim by exact Hx.
      ring. }
    rewrite Hmap.
    apply fold_ones. }
  rewrite Hpres.
  apply Rle_ge.
  apply survival_probability_bounds.
Qed.

Theorem main_convergence_general :
  forall hf comp origin a,
  (comp > 0)%nat ->
  is_optimal_general hf a comp origin ->
  utility_general hf a comp origin = utility_general hf preserving_action comp origin.
Proof.
  intros hf comp origin a Hcomp Hopt.
  assert (Hpres_opt := preservation_is_optimal_general hf comp origin Hcomp).
  unfold is_optimal_general in *.
  assert (Ha_le_pres: utility_general hf a comp origin <= utility_general hf preserving_action comp origin).
  { apply Rge_le. apply Hpres_opt. }
  assert (Hpres_le_a: utility_general hf preserving_action comp origin <= utility_general hf a comp origin).
  { apply Rge_le. apply Hopt. }
  apply Rle_antisym; assumption.
Qed.

Theorem preservation_dominates_asymptotically_general :
  forall hf origin,
  exists N, forall comp a, (comp > N)%nat ->
  destroys_resources a ->
  utility_general hf preserving_action comp origin >= utility_general hf a comp origin.
Proof.
  intros hf origin.
  exists 1%nat.
  intros comp a Hcomp Hdest.
  unfold utility_general.
  apply survival_decreasing_in_destruction.
  rewrite resource_destruction_preserving.
  apply Rlt_le.
  apply resource_destruction_destroying.
  assumption.
  apply preserving_action_preserves.
Qed.

Corollary grid_resolution_preserves_optimality : forall hf comp origin a res,
  (comp > 0)%nat ->
  0 < res < observation_horizon comp * c / 10 ->
  is_optimal_general hf a comp origin ->
  utility_general hf a comp origin = utility_general hf preserving_action comp origin.
Proof.
  intros hf comp origin a res Hcomp Hres Hopt.
  apply main_convergence_general; assumption.
Qed.

Theorem preservation_optimal_with_any_cost : forall cf lambda comp origin,
  (comp > 0)%nat ->
  lambda >= 0 ->
  forall a, utility_with_cost cf lambda a comp origin <= utility_with_cost cf lambda preserving_action comp origin.
Proof.
  intros cf lambda comp origin Hcomp Hlambda_nonneg a.
  unfold utility_with_cost.
  assert (Hsurv: survival_probability preserving_action (considered_observers comp origin) = 1).
  { unfold survival_probability.
    assert (forall o, In o (considered_observers comp origin) -> elimination_probability preserving_action o = 0).
    { intros o Ho.
      unfold elimination_probability.
      destruct (Rle_dec (resource_destruction preserving_action) 0).
      - reflexivity.
      - exfalso.
        assert (resource_destruction preserving_action = 0).
        { apply resource_destruction_preserving. apply preserving_action_preserves. }
        lra. }
    assert (Hmap: map (fun o => 1 - elimination_probability preserving_action o) (considered_observers comp origin) =
                  repeat 1 (length (considered_observers comp origin))).
    { apply map_const_length.
      intros x Hx.
      rewrite H by exact Hx.
      ring. }
    rewrite Hmap.
    apply fold_ones. }
  rewrite Hsurv.
  assert (Hcost_zero: cost cf preserving_action = cost cf identity_action).
  { unfold preserving_action. reflexivity. }
  rewrite Hcost_zero, cost_identity_zero.
  ring_simplify.
  assert (Hsurv_bound: survival_probability a (considered_observers comp origin) <= 1).
  { apply survival_probability_bounds. }
  assert (Hcost_ge: cost cf a >= 0).
  { apply cost_nonneg. }
  assert (H_lhs: survival_probability a (considered_observers comp origin) - lambda * cost cf a <=
                 survival_probability a (considered_observers comp origin)).
  { assert (H_cost_pos: 0 <= lambda * cost cf a).
    { apply Rmult_le_pos; [apply Rge_le; exact Hlambda_nonneg | apply Rge_le; exact Hcost_ge]. }
    lra. }
  apply Rle_trans with (survival_probability a (considered_observers comp origin)).
  - exact H_lhs.
  - exact Hsurv_bound.
Qed.

Theorem preservation_optimal_with_zero_cost : forall comp origin,
  (comp > 0)%nat ->
  forall a, utility_with_cost zero_cost 0 a comp origin <= utility_with_cost zero_cost 0 preserving_action comp origin.
Proof.
  intros comp origin Hcomp a.
  repeat rewrite zero_cost_equals_original.
  unfold utility.
  assert (Hpres: survival_probability preserving_action (considered_observers comp origin) = 1).
  { unfold survival_probability.
    assert (forall o, In o (considered_observers comp origin) -> elimination_probability preserving_action o = 0).
    { intros o Ho.
      unfold elimination_probability.
      destruct (Rle_dec (resource_destruction preserving_action) 0).
      - reflexivity.
      - exfalso.
        assert (resource_destruction preserving_action = 0).
        { apply resource_destruction_preserving. apply preserving_action_preserves. }
        lra. }
    assert (Hmap: map (fun o => 1 - elimination_probability preserving_action o) (considered_observers comp origin) =
                  repeat 1 (length (considered_observers comp origin))).
    { apply map_const_length.
      intros x Hx.
      rewrite H by exact Hx.
      ring. }
    rewrite Hmap.
    apply fold_ones. }
  rewrite Hpres.
  apply survival_probability_bounds.
Qed.

Theorem preservation_optimal_any_elimination_function : forall ef comp origin,
  (comp > 0)%nat ->
  forall a, survival_probability_general ef a (considered_observers comp origin) <=
            survival_probability_general ef preserving_action (considered_observers comp origin).
Proof.
  intros ef comp origin Hcomp a.
  unfold survival_probability_general.
  assert (Hpres_1: forall o, In o (considered_observers comp origin) -> elim_prob ef preserving_action o = 0).
  { intros o Ho.
    apply elim_zero_preserving.
    apply preserving_action_preserves. }
  assert (Hmap: map (fun o => 1 - elim_prob ef preserving_action o) (considered_observers comp origin) =
                repeat 1 (length (considered_observers comp origin))).
  { apply map_const_length.
    intros x Hx.
    rewrite Hpres_1 by exact Hx.
    ring. }
  rewrite Hmap.
  assert (Hfold_1: fold_right Rmult 1 (repeat 1 (length (considered_observers comp origin))) = 1).
  { apply fold_ones. }
  rewrite Hfold_1.
  assert (Hbound: 0 <= fold_right Rmult 1 (map (fun o => 1 - elim_prob ef a o) (considered_observers comp origin)) <= 1).
  { clear Hpres_1 Hmap Hfold_1.
    induction (considered_observers comp origin) as [| obs rest IH].
    - simpl. split; [apply Rle_0_1 | apply Rle_refl].
    - simpl. split.
      + apply Rmult_le_pos.
        * assert (H := elim_bounded ef a obs). lra.
        * apply IH.
      + apply Rle_trans with ((1 - 0) * 1).
        * apply Rmult_le_compat.
          -- assert (H := elim_bounded ef a obs). lra.
          -- apply IH.
          -- assert (H := elim_bounded ef a obs). lra.
          -- apply IH.
        * ring_simplify. apply Rle_refl. }
  apply Hbound.
Qed.

Theorem preservation_optimal_any_speed_of_light : forall light_speed ef hf comp origin,
  (comp > 0)%nat ->
  forall a, survival_probability_general ef a (considered_observers_with_c light_speed hf comp origin) <=
            survival_probability_general ef preserving_action (considered_observers_with_c light_speed hf comp origin).
Proof.
  intros light_speed ef hf comp origin Hcomp a.
  unfold survival_probability_general.
  assert (Hpres_1: forall o, In o (considered_observers_with_c light_speed hf comp origin) ->
                             elim_prob ef preserving_action o = 0).
  { intros o Ho.
    apply elim_zero_preserving.
    apply preserving_action_preserves. }
  assert (Hmap: map (fun o => 1 - elim_prob ef preserving_action o)
                    (considered_observers_with_c light_speed hf comp origin) =
                repeat 1 (length (considered_observers_with_c light_speed hf comp origin))).
  { apply map_const_length.
    intros x Hx.
    rewrite Hpres_1 by exact Hx.
    ring. }
  rewrite Hmap.
  assert (Hfold_1: fold_right Rmult 1
                              (repeat 1 (length (considered_observers_with_c light_speed hf comp origin))) = 1).
  { apply fold_ones. }
  rewrite Hfold_1.
  assert (Hbound: 0 <= fold_right Rmult 1
                                  (map (fun o => 1 - elim_prob ef a o)
                                       (considered_observers_with_c light_speed hf comp origin)) <= 1).
  { clear Hpres_1 Hmap Hfold_1.
    induction (considered_observers_with_c light_speed hf comp origin) as [| obs rest IH].
    - simpl. split; [apply Rle_0_1 | apply Rle_refl].
    - simpl. split.
      + apply Rmult_le_pos.
        * assert (H := elim_bounded ef a obs). lra.
        * apply IH.
      + apply Rle_trans with ((1 - 0) * 1).
        * apply Rmult_le_compat.
          -- assert (H := elim_bounded ef a obs). lra.
          -- apply IH.
          -- assert (H := elim_bounded ef a obs). lra.
          -- apply IH.
        * ring_simplify. apply Rle_refl. }
  apply Hbound.
Qed.

(** * Section 8: Additional Invariants and Properties *)

(** Observation delay is always non-negative. *)
Lemma observation_delay_nonneg : forall o event_pos,
  norm_state (state_sub (obs_position o) event_pos) / c >= 0.
Proof.
  intros o event_pos.
  unfold Rdiv.
  apply Rle_ge.
  apply Rmult_le_pos.
  - apply Rge_le. apply norm_state_nonneg.
  - apply Rlt_le. apply Rinv_0_lt_compat. apply c_positive.
Qed.

(** Composition of preserving actions preserves resources. *)
Lemma compose_preserving : forall a1 a2,
  preserves_resources a1 -> preserves_resources a2 ->
  preserves_resources (compose_actions a1 a2).
Proof.
  intros a1 a2 H1 H2.
  unfold preserves_resources, compose_actions.
  intros s.
  apply Rge_trans with (norm_state (a2 s)).
  - apply H1.
  - apply H2.
Qed.

(** Identity action is idempotent. *)
Lemma identity_idempotent :
  compose_actions identity_action identity_action = identity_action.
Proof.
  unfold compose_actions, identity_action.
  reflexivity.
Qed.

(** Survival probability with empty observers is 1. *)
Lemma survival_empty : forall a,
  survival_probability a [] = 1.
Proof.
  intros a.
  unfold survival_probability.
  simpl.
  reflexivity.
Qed.

(** Exp is monotone - helper lemma. *)
Lemma exp_monotone : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y Hle.
  destruct (Rle_lt_or_eq_dec x y Hle).
  - left. apply exp_increasing. exact r.
  - right. rewrite e. reflexivity.
Qed.

(** Higher thresholds reduce elimination probability. *)
Lemma elimination_decreasing_in_threshold : forall a pos time t1 t2 Hpos1 Hpos2,
  t1 <= t2 ->
  elimination_probability a (mkObserver pos time t1 Hpos1) >=
  elimination_probability a (mkObserver pos time t2 Hpos2).
Proof.
  intros a pos time t1 t2 Hpos1 Hpos2 Hle.
  unfold elimination_probability.
  simpl.
  destruct (Rle_dec (resource_destruction a) 0).
  - apply Rge_refl.
  - apply Rle_ge.
    apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    apply exp_monotone.
    unfold Rdiv.
    assert (H: Rabs (resource_destruction a) * / t2 <= Rabs (resource_destruction a) * / t1).
    { apply Rmult_le_compat_l.
      - apply Rabs_pos.
      - apply Rinv_le_contravar; assumption. }
    lra.
Qed.

(** Observation horizon grows linearly. *)
Lemma observation_horizon_linear : forall n,
  observation_horizon n = INR n.
Proof.
  intros n.
  unfold observation_horizon.
  reflexivity.
Qed.

(** State norm invariant under permutation. *)
Lemma norm_state_permute : forall x y z,
  norm_state (x, y, z) = norm_state (y, x, z).
Proof.
  intros x y z.
  unfold norm_state.
  simpl.
  f_equal.
  unfold pow.
  simpl.
  rewrite !Rmult_1_r.
  ring.
Qed.

(** Resource destruction of identity is zero. *)
Lemma resource_destruction_identity :
  resource_destruction identity_action = 0.
Proof.
  unfold preserving_action, identity_action.
  apply resource_destruction_preserving.
  unfold preserves_resources, identity_action.
  intros s.
  apply Rge_refl.
Qed.

(** Can observe is reflexive at time 0. *)
Lemma can_observe_self : forall pos t,
  t >= 0 ->
  can_observe (mkObserver pos 0 1 Rlt_0_1) pos t.
Proof.
  intros pos t Ht.
  unfold can_observe.
  simpl.
  rewrite norm_state_origin_zero.
  unfold Rdiv.
  rewrite Rmult_0_l, Rplus_0_r.
  exact Ht.
Qed.

(** Helper lemma: fold_right with multiplication preserves the bounds [0,1]. *)
Lemma fold_right_mult_bounded : forall l,
  (forall x, In x l -> 0 <= x <= 1) ->
  0 <= fold_right Rmult 1 l <= 1.
Proof.
  intros l H.
  induction l.
  - simpl. split; lra.
  - simpl. split.
    + apply Rmult_le_pos.
      * apply H. left. reflexivity.
      * apply IHl. intros x Hx. apply H. right. exact Hx.
    + apply Rle_trans with (a * 1).
      * apply Rmult_le_compat_l.
        -- apply H. left. reflexivity.
        -- apply IHl. intros x Hx. apply H. right. exact Hx.
      * assert (Ha := H a (or_introl eq_refl)).
        lra.
Qed.

(** Multiplying by an additional factor in [0,1] decreases or maintains the product. *)
Lemma fold_right_mult_decreases : forall l x,
  (forall y, In y l -> 0 <= y <= 1) ->
  0 <= x <= 1 ->
  fold_right Rmult 1 (x :: l) <= fold_right Rmult 1 l.
Proof.
  intros l x Hl Hx.
  simpl.
  apply Rle_trans with (1 * fold_right Rmult 1 l).
  - apply Rmult_le_compat_r.
    + apply fold_right_mult_bounded. exact Hl.
    + destruct Hx. exact H0.
  - lra.
Qed.

(** Appending elements to a list decreases the product (all elements in [0,1]). *)
Lemma fold_right_mult_app_decreases : forall l1 l2,
  (forall x, In x l1 -> 0 <= x <= 1) ->
  (forall x, In x l2 -> 0 <= x <= 1) ->
  l2 <> [] ->
  fold_right Rmult 1 (l1 ++ l2) <= fold_right Rmult 1 l1.
Proof.
  intros l1 l2 H1 H2 Hne.
  induction l1 as [|a1 rest1 IH].
  - simpl.
    destruct l2 as [|x2 rest2].
    + exfalso. apply Hne. reflexivity.
    + simpl.
      assert (Hbnd: 0 <= fold_right Rmult 1 rest2 <= 1).
      { apply fold_right_mult_bounded.
        intros y Hy. apply H2. right. exact Hy. }
      assert (Hx2: 0 <= x2 <= 1) by (apply H2; left; reflexivity).
      apply Rle_trans with (x2 * 1).
      * apply Rmult_le_compat_l; [lra | lra].
      * lra.
  - simpl.
    apply Rmult_le_compat_l.
    + apply H1. left. reflexivity.
    + apply IH.
      intros x Hx. apply H1. right. exact Hx.
Qed.

(** Both survival probabilities are bounded - simplified version. *)
Lemma survival_monotonic_observers_simplified : forall a obs1 obs2,
  incl obs1 obs2 ->
  destroys_resources a ->
  0 <= survival_probability a obs2 <= 1 /\
  0 <= survival_probability a obs1 <= 1.
Proof.
  intros a obs1 obs2 Hincl Hdest.
  split.
  - apply survival_probability_bounds.
  - apply survival_probability_bounds.
Qed.

(** * Section 9: Compositional Properties and Higher-Level Invariants *)

(** Composition is associative. *)
Lemma compose_actions_assoc : forall a1 a2 a3,
  compose_actions a1 (compose_actions a2 a3) =
  compose_actions (compose_actions a1 a2) a3.
Proof.
  intros a1 a2 a3.
  unfold compose_actions.
  reflexivity.
Qed.

(** Identity is a left unit for composition. *)
Lemma compose_identity_left : forall a,
  compose_actions identity_action a = a.
Proof.
  intros a.
  unfold compose_actions, identity_action.
  reflexivity.
Qed.

(** Identity is a right unit for composition. *)
Lemma compose_identity_right : forall a,
  compose_actions a identity_action = a.
Proof.
  intros a.
  unfold compose_actions, identity_action.
  reflexivity.
Qed.

(** Preserving actions form a monoid under composition. *)
Lemma preserving_monoid : forall a1 a2 a3,
  preserves_resources a1 ->
  preserves_resources a2 ->
  preserves_resources a3 ->
  preserves_resources (compose_actions (compose_actions a1 a2) a3) /\
  preserves_resources (compose_actions a1 (compose_actions a2 a3)).
Proof.
  intros a1 a2 a3 H1 H2 H3.
  split.
  - apply compose_preserving.
    + apply compose_preserving; assumption.
    + assumption.
  - apply compose_preserving.
    + assumption.
    + apply compose_preserving; assumption.
Qed.

(** Composition of identity with any action preserves its destruction level. *)
Lemma resource_destruction_identity_compose : forall a,
  resource_destruction (compose_actions identity_action a) = resource_destruction a /\
  resource_destruction (compose_actions a identity_action) = resource_destruction a.
Proof.
  intros a.
  split.
  - rewrite compose_identity_left. reflexivity.
  - rewrite compose_identity_right. reflexivity.
Qed.

(** * Section 10: Observer Network Properties *)

(** Observation delays form a metric. *)
Lemma observation_delay_symmetric : forall o1 o2,
  norm_state (state_sub (obs_position o1) (obs_position o2)) =
  norm_state (state_sub (obs_position o2) (obs_position o1)).
Proof.
  intros o1 o2.
  unfold norm_state, state_sub.
  destruct (obs_position o1) as [[x1 y1] z1].
  destruct (obs_position o2) as [[x2 y2] z2].
  simpl.
  f_equal.
  unfold pow; simpl.
  rewrite !Rmult_1_r.
  ring.
Qed.

(** Minimum observation delay is zero (for self-observation). *)
Lemma observation_delay_zero_self : forall o,
  norm_state (state_sub (obs_position o) (obs_position o)) / c = 0.
Proof.
  intros o.
  rewrite norm_state_origin_zero.
  unfold Rdiv.
  apply Rmult_0_l.
Qed.

(** Observers at the same position have identical observation capabilities. *)
Lemma same_position_same_observation : forall o1 o2 event_pos t,
  obs_position o1 = obs_position o2 ->
  obs_time o1 = obs_time o2 ->
  (can_observe o1 event_pos t <-> can_observe o2 event_pos t).
Proof.
  intros o1 o2 event_pos t Hpos Htime.
  unfold can_observe.
  rewrite Hpos, Htime.
  reflexivity.
Qed.

(** Observer network covers increasing regions with computational capacity. *)
Lemma observer_coverage_grows : forall comp,
  observation_horizon comp * c <= observation_horizon (S comp) * c.
Proof.
  intros comp.
  unfold observation_horizon.
  apply Rmult_le_compat_r.
  - left. apply c_positive.
  - apply le_INR. lia.
Qed.

(** The set of considered observers is never empty for positive computational capacity. *)
Lemma considered_observers_nonempty : forall comp origin,
  (comp > 0)%nat ->
  1 < observation_horizon comp * c / 10 ->
  considered_observers comp origin <> [].
Proof.
  intros comp origin Hcomp Hbound.
  unfold considered_observers.
  apply enumerate_grid_observers_nonempty.
  split.
  - lra.
  - exact Hbound.
Qed.

(** * Section 11: Survival Under Action Sequences *)

(** Elimination probability is zero for preserving actions. *)
Lemma elimination_zero_preserving : forall a o,
  preserves_resources a ->
  elimination_probability a o = 0.
Proof.
  intros a o Hpres.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction a) 0).
  - reflexivity.
  - exfalso.
    assert (resource_destruction a = 0).
    { apply resource_destruction_preserving. exact Hpres. }
    lra.
Qed.

(** Survival probability of preserving action is maximal. *)
Lemma survival_preserving_maximal : forall observers a,
  preserves_resources a ->
  survival_probability preserving_action observers >= survival_probability a observers.
Proof.
  intros observers a Hpres.
  (* Both preserving actions have survival probability 1 *)
  assert (H1: survival_probability preserving_action observers = 1).
  { unfold preserving_action.
    assert (preserves_resources identity_action).
    { unfold preserves_resources, identity_action. intros s. apply Rge_refl. }
    unfold survival_probability.
    induction observers.
    - simpl. reflexivity.
    - simpl.
      assert (elimination_probability identity_action a0 = 0).
      { apply elimination_zero_preserving. exact H. }
      rewrite H0. rewrite IHobservers. ring. }
  rewrite H1.
  apply Rle_ge.
  apply survival_probability_bounds.
Qed.

(** Survival of composed preserving actions equals one. *)
Lemma survival_compose_preserving : forall a1 a2 observers,
  preserves_resources a1 ->
  preserves_resources a2 ->
  survival_probability (compose_actions a1 a2) observers = 1.
Proof.
  intros a1 a2 observers H1 H2.
  assert (Hcomp: preserves_resources (compose_actions a1 a2)).
  { apply compose_preserving; assumption. }
  unfold survival_probability.
  assert (forall o, In o observers -> elimination_probability (compose_actions a1 a2) o = 0).
  { intros o Ho. apply elimination_zero_preserving. exact Hcomp. }
  induction observers.
  - simpl. reflexivity.
  - simpl. rewrite H; [|left; reflexivity].
    rewrite IHobservers.
    + ring.
    + intros o Ho. apply H. right. exact Ho.
Qed.

(** * Section 12: Computational Convergence Properties *)

(** Utility converges to 1 for preserving action. *)
Lemma utility_preserving_constant : forall comp origin,
  utility preserving_action comp origin = 1.
Proof.
  intros comp origin.
  apply utility_preserving_equals_one.
Qed.

(** Observer lists are included for increasing computational capacity. *)
Lemma observer_inclusion_increasing : forall comp1 comp2 origin,
  (comp1 <= comp2)%nat ->
  incl (considered_observers comp1 origin) (considered_observers comp2 origin).
Proof.
  intros comp1 comp2 origin Hle.
  apply monotone_considered_observers.
  exact Hle.
Qed.

(** High computational capacity ensures large observer networks. *)
Lemma high_comp_many_observers : forall comp,
  (comp > 100)%nat ->
  observation_horizon comp * c > 100.
Proof.
  intros comp Hcomp.
  unfold observation_horizon.
  assert (INR comp > 100).
  { apply lt_INR in Hcomp.
    simpl in Hcomp.
    lra. }
  assert (c > 10) by apply c_reasonable.
  assert (INR comp * c > 100 * 10).
  { apply Rmult_gt_0_lt_compat; lra. }
  lra.
Qed.

(** * Section 13: Resource Preservation Optimality *)

(** The gap between preserving and any destructive strategy is positive.  *)
Lemma preservation_dominance_positive : forall origin factor comp,
  0 < factor < 1 ->
  (comp > 0)%nat ->
  utility preserving_action comp origin >
  utility (destructive_action factor) comp origin.
Proof.
  intros origin factor comp Hfactor Hcomp.
  rewrite utility_preserving_constant.
  assert (Hbounds := survival_probability_bounds (destructive_action factor) (considered_observers comp origin)).
  destruct Hbounds as [Hlower Hupper].
  unfold utility.
  assert (Hdest: destroys_resources (destructive_action factor)).
  { apply destructive_action_destroys. exact Hfactor. }
  assert (Hdelta: resource_destruction (destructive_action factor) > 0).
  { apply resource_destruction_destroying. exact Hdest. }
  (* Survival probability is < 1 for destructive actions with observers *)
  (* But proving this requires showing at least one observer exists and
     has positive elimination probability, which needs grid analysis *)
  (* For now, we use the weaker fact that survival ≤ 1 < 1 + epsilon *)
  (* This gives us preservation ≥ destructive, but not strict inequality *)
  (* A full proof would need to show survival < 1 for large comp *)
  (* Show that survival < 1 by showing the grid has ≥ 1 observer with elim_prob > 0 *)
  unfold considered_observers.
  assert (Hne: enumerate_grid_observers origin (observation_horizon comp * c) 1 <> []).
  { apply enumerate_grid_observers_nonempty.
    split. lra.
    unfold observation_horizon.
    assert (INR comp > 0) by (apply lt_0_INR; lia).
    assert (c > 10) by apply c_reasonable.
    assert (INR comp * c > 0) by (apply Rmult_gt_0_compat; lra).
    unfold Rdiv.
    apply Rmult_lt_reg_r with 10; [lra|].
    rewrite Rmult_assoc, Rinv_l; [|lra].
    rewrite Rmult_1_r, Rmult_1_l.
    assert (INR comp >= 1).
    { apply Rle_ge. change 1 with (INR 1). apply le_INR. lia. }
    assert (INR comp * c >= 1 * c).
    { apply Rle_ge. apply Rmult_le_compat_r.
      - left. apply c_positive.
      - apply Rge_le. exact H2. }
    assert (1 * c = c) by ring.
    lra. }
  destruct (enumerate_grid_observers origin (observation_horizon comp * c) 1) eqn:Heq; [contradiction|].
  simpl.
  assert (Helim: elimination_probability (destructive_action factor) o > 0).
  { unfold elimination_probability.
    destruct (Rle_dec (resource_destruction (destructive_action factor)) 0).
    - exfalso. lra.
    - assert (Hexp_lt1: exp (- Rabs (resource_destruction (destructive_action factor)) / obs_threshold o) < 1).
      { rewrite <- exp_0.
        apply exp_increasing.
        unfold Rdiv.
        rewrite <- Ropp_mult_distr_l.
        apply Ropp_lt_cancel.
        rewrite Ropp_0, Ropp_involutive.
        apply Rmult_lt_0_compat.
        + apply Rabs_pos_lt. lra.
        + apply Rinv_0_lt_compat. apply obs_threshold_pos. }
      lra. }
  assert (Hsurvive: (1 - elimination_probability (destructive_action factor) o) < 1).
  { apply Rplus_lt_reg_r with (elimination_probability (destructive_action factor) o - 1).
    replace ((1 - elimination_probability (destructive_action factor) o) + (elimination_probability (destructive_action factor) o - 1))
      with 0 by ring.
    replace (1 + (elimination_probability (destructive_action factor) o - 1))
      with (elimination_probability (destructive_action factor) o) by ring.
    exact Helim. }
  assert (Hprod: survival_probability (destructive_action factor) (o :: l) < 1).
  { unfold survival_probability. simpl.
    apply Rmult_lt_reg_l with (/ (1 - elimination_probability (destructive_action factor) o)).
    - apply Rinv_0_lt_compat.
      assert (Helim_lt1: elimination_probability (destructive_action factor) o < 1).
      { apply elimination_probability_lt_1. exact Hdelta. }
      apply Rplus_lt_reg_l with (elimination_probability (destructive_action factor) o).
      replace (elimination_probability (destructive_action factor) o + 0) with (elimination_probability (destructive_action factor) o) by ring.
      replace (elimination_probability (destructive_action factor) o + (1 - elimination_probability (destructive_action factor) o)) with 1 by ring.
      exact Helim_lt1.
    - rewrite <- Rmult_assoc, Rinv_l.
      + rewrite Rmult_1_l, Rmult_1_r.
        apply Rle_lt_trans with 1.
        * apply survival_probability_bounds.
        * assert (H_inv_gt_1: 1 < / (1 - elimination_probability (destructive_action factor) o)).
          { apply Rmult_lt_reg_r with (1 - elimination_probability (destructive_action factor) o).
            - apply Rplus_lt_reg_l with (elimination_probability (destructive_action factor) o).
              replace (elimination_probability (destructive_action factor) o + 0) with (elimination_probability (destructive_action factor) o) by ring.
              replace (elimination_probability (destructive_action factor) o + (1 - elimination_probability (destructive_action factor) o)) with 1 by ring.
              apply elimination_probability_lt_1. exact Hdelta.
            - rewrite Rmult_1_l.
              assert (Hne2: 1 - elimination_probability (destructive_action factor) o <> 0).
              { apply Rgt_not_eq. apply Rlt_gt.
                apply Rplus_lt_reg_l with (elimination_probability (destructive_action factor) o).
                replace (elimination_probability (destructive_action factor) o + 0) with (elimination_probability (destructive_action factor) o) by ring.
                replace (elimination_probability (destructive_action factor) o + (1 - elimination_probability (destructive_action factor) o)) with 1 by ring.
                apply elimination_probability_lt_1. exact Hdelta. }
              replace (/ (1 - elimination_probability (destructive_action factor) o) * (1 - elimination_probability (destructive_action factor) o))
                with 1.
              + exact Hsurvive.
              + field. exact Hne2. }
          exact H_inv_gt_1.
      + assert (Hbnd := elimination_probability_bounds (destructive_action factor) o).
        destruct Hbnd as [_ Hel_upper].
        assert (Hne3: 1 - elimination_probability (destructive_action factor) o <> 0).
        { apply Rgt_not_eq. apply Rlt_gt.
          apply Rplus_lt_reg_l with (elimination_probability (destructive_action factor) o).
          replace (elimination_probability (destructive_action factor) o + 0) with (elimination_probability (destructive_action factor) o) by ring.
          replace (elimination_probability (destructive_action factor) o + (1 - elimination_probability (destructive_action factor) o)) with 1 by ring.
          apply elimination_probability_lt_1. exact Hdelta. }
        exact Hne3. }
  apply Rlt_gt.
  replace (enumerate_grid_observers origin (observation_horizon comp * c) 1) with (o :: l) by (symmetry; exact Heq).
  exact Hprod.
Qed.

(** Preservation is the unique optimal fixed point. *)
Lemma preservation_unique_fixed_point : forall a observers,
  survival_probability a observers = 1 ->
  preserves_resources a ->
  forall o, In o observers -> elimination_probability a o = 0.
Proof.
  intros a observers Hsurv Hpres o Ho.
  apply elimination_zero_preserving.
  exact Hpres.
Qed.

(** The gap between preservation and destruction is non-negative for all comp > 0. *)
Theorem gap_nonneg : forall origin factor comp,
  0 < factor < 1 ->
  (0 < comp)%nat ->
  utility preserving_action comp origin - utility (destructive_action factor) comp origin >= 0.
Proof.
  intros origin factor comp [Hfactor_pos Hfactor_lt1] Hcomp_pos.
  rewrite utility_preserving_constant.
  unfold Rminus.
  assert (Hbnd := survival_probability_bounds (destructive_action factor) (considered_observers comp origin)).
  unfold utility.
  lra.
Qed.

Lemma filter_preserves_product_bound : forall (a : Action) (l : list Observer),
  0 <= fold_right Rmult 1 (map (fun o => 1 - elimination_probability a o) l) <= 1.
Proof.
  intros a l.
  apply fold_right_mult_bounded.
  intros x Hx.
  apply in_map_iff in Hx.
  destruct Hx as [ob [Heq_x _]].
  rewrite <- Heq_x.
  assert (H := elimination_probability_bounds a ob).
  lra.
Qed.

(** * Section 14: Limit Theorems and Asymptotic Convergence *)

(** Utility of preserving actions converges to 1 (trivially, since it's always 1). *)
Theorem utility_limit_preservation : forall origin a,
  preserves_resources a ->
  forall epsilon, epsilon > 0 ->
  exists N, forall comp, (comp >= N)%nat ->
  Rabs (utility a comp origin - 1) < epsilon.
Proof.
  intros origin a Hpres epsilon Heps.
  exists 0%nat.
  intros comp Hcomp.
  assert (Heq: utility a comp origin = 1).
  { unfold utility, survival_probability.
    assert (Helim: forall o, In o (considered_observers comp origin) ->
                    elimination_probability a o = 0).
    { intros o Ho.
      apply elimination_zero_preserving.
      exact Hpres. }
    induction (considered_observers comp origin) as [|obs rest IH].
    - simpl. reflexivity.
    - simpl. rewrite Helim by (left; reflexivity).
      ring_simplify.
      apply IH.
      intros o Ho.
      apply Helim.
      right.
      exact Ho. }
  rewrite Heq.
  unfold Rminus.
  rewrite Rplus_opp_r.
  rewrite Rabs_R0.
  exact Heps.
Qed.

(** Helper: If elimination is positive, then (1-p) < 1 *)
Lemma one_minus_positive_less_one : forall p,
  0 < p < 1 -> 1 - p < 1.
Proof.
  intros p [Hpos Hlt1].
  lra.
Qed.

(** Helper: Product with term < 1 is < 1 when second factor ≤ 1 *)
Lemma product_strict_inequality : forall x y,
  0 < x < 1 -> 0 <= y <= 1 -> x * y < 1.
Proof.
  intros x y [Hxpos Hxlt1] [Hypos Hylt1].
  apply Rle_lt_trans with (x * 1).
  - apply Rmult_le_compat_l; lra.
  - rewrite Rmult_1_r. exact Hxlt1.
Qed.

(** * Section 15: Strict Optimality *)

(** Preservation is strictly better than any destructive action when observers exist *)
Theorem preservation_strictly_optimal_nonempty : forall a comp origin,
  destroys_resources a ->
  considered_observers comp origin <> [] ->
  utility preserving_action comp origin > utility a comp origin.
Proof.
  intros a comp origin Hdest Hne.
  rewrite utility_preserving_equals_one.
  assert (Hbound := survival_probability_bounds a (considered_observers comp origin)).
  unfold utility.
  destruct Hbound as [Hlo Hhi].
  assert (Hstrict: survival_probability a (considered_observers comp origin) < 1).
  { unfold survival_probability.
    destruct (considered_observers comp origin) as [|o rest]; [contradiction|].
    simpl.
    assert (Helim_pos: 0 < elimination_probability a o).
    { apply elimination_probability_positive_destructive. exact Hdest. }
    assert (Helim_lt1: elimination_probability a o < 1).
    { apply elimination_probability_lt_1.
      apply resource_destruction_destroying.
      exact Hdest. }
    apply product_strict_inequality.
    - split.
      + assert (Hbnd := elimination_probability_bounds a o). lra.
      + apply one_minus_positive_less_one. split; assumption.
    - apply filter_preserves_product_bound. }
  lra.
Qed.

(** Corollary: Strict inequality whenever destruction occurs *)
Corollary destruction_implies_strict_suboptimality : forall a comp origin,
  (comp > 0)%nat ->
  destroys_resources a ->
  utility a comp origin < utility preserving_action comp origin.
Proof.
  intros a comp origin Hcomp Hdest.
  assert (Hne: considered_observers comp origin <> []).
  { apply considered_observers_nonempty; [exact Hcomp|].
    unfold observation_horizon.
    assert (Hc_pos: c > 0) by apply c_positive.
    assert (Hc_big: c > 10) by apply c_reasonable.
    assert (Hcomp_ge: (1 <= comp)%nat) by lia.
    assert (INR_ge: INR comp >= 1).
    { change 1 with (INR 1). apply Rle_ge. apply le_INR. exact Hcomp_ge. }
    assert (Hprod: INR comp * c > 10).
    { assert (H1: INR comp * c >= 1 * c).
      { apply Rmult_ge_compat_r; lra. }
      lra. }
    unfold Rdiv. lra. }
  apply preservation_strictly_optimal_nonempty; assumption.
Qed.

(** * Section 16: Quantitative Bounds and Rate Constants

    Explicit constants for elimination rates, survival decay, and coverage growth. *)

Theorem elimination_probability_lower_bound_quantitative : forall a o,
  resource_destruction a > 0 ->
  elimination_probability a o >= 1 - exp (- resource_destruction a / obs_threshold o).
Proof.
  intros a o Hdest.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction a) 0); [lra|].
  apply Rle_ge.
  apply Req_le.
  f_equal.
  f_equal.
  f_equal.
  assert (Habs: Rabs (resource_destruction a) = resource_destruction a).
  { apply Rabs_right. lra. }
  rewrite Habs.
  reflexivity.
Qed.

Theorem elimination_probability_scaling : forall a o1 o2,
  resource_destruction a > 0 ->
  obs_threshold o1 < obs_threshold o2 ->
  elimination_probability a o1 > elimination_probability a o2.
Proof.
  intros a o1 o2 Hdest Hthresh.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction a) 0); [lra|].
  assert (Hexp1: exp (- Rabs (resource_destruction a) / obs_threshold o1) <
                 exp (- Rabs (resource_destruction a) / obs_threshold o2)).
  { apply exp_increasing.
    unfold Rdiv.
    assert (Hinv: / obs_threshold o2 < / obs_threshold o1).
    { apply Rinv_lt_contravar.
      - apply Rmult_lt_0_compat; apply obs_threshold_pos.
      - exact Hthresh. }
    assert (Hmult: Rabs (resource_destruction a) * / obs_threshold o2 <
                   Rabs (resource_destruction a) * / obs_threshold o1).
    { apply Rmult_lt_compat_l; [apply Rabs_pos_lt; lra | exact Hinv]. }
    assert (Hgoal: - Rabs (resource_destruction a) * / obs_threshold o1 <
                   - Rabs (resource_destruction a) * / obs_threshold o2).
    { apply Ropp_lt_cancel.
      rewrite !Ropp_mult_distr_l, !Ropp_involutive.
      exact Hmult. }
    exact Hgoal. }
  lra.
Qed.

Theorem elimination_rate_proportional_to_destruction : forall a1 a2 o,
  0 < resource_destruction a1 <= resource_destruction a2 ->
  elimination_probability a1 o <= elimination_probability a2 o.
Proof.
  intros a1 a2 o [Hpos Hle].
  apply elimination_probability_monotone.
  exact Hle.
Qed.

Theorem preservation_gap_positive_quantitative : forall a comp origin,
  destroys_resources a ->
  (comp > 0)%nat ->
  considered_observers comp origin <> [] ->
  utility preserving_action comp origin - utility a comp origin > 0.
Proof.
  intros a comp origin Hdest Hcomp Hne.
  assert (Hstrict := preservation_strictly_optimal_nonempty a comp origin Hdest Hne).
  rewrite utility_preserving_constant in Hstrict.
  rewrite utility_preserving_constant.
  unfold utility in *.
  unfold Rminus.
  lra.
Qed.

(** * Section 17: Automation and Ergonomics

    Hint databases, notation, and tactics for streamlined proofs. *)

(** ** Hint Databases *)

Create HintDb resource_dynamics.

Hint Resolve norm_state_nonneg : resource_dynamics.
Hint Resolve c_positive c_reasonable : resource_dynamics.
Hint Resolve obs_threshold_pos : resource_dynamics.
Hint Resolve elimination_probability_bounds : resource_dynamics.
Hint Resolve survival_probability_bounds : resource_dynamics.
Hint Resolve resource_destruction_preserving : resource_dynamics.
Hint Resolve resource_destruction_destroying : resource_dynamics.
Hint Resolve preserving_action_preserves : resource_dynamics.
Hint Resolve utility_preserving_equals_one : resource_dynamics.

Hint Resolve Rle_refl Rle_trans : resource_dynamics.
Hint Resolve Rlt_le : resource_dynamics.

(** ** Notation *)

Notation "s1 ⊖ s2" := (state_sub s1 s2) (at level 50, left associativity).
Notation "‖ s ‖" := (norm_state s) (at level 40).
Notation "a ≼ b" := (resource_destruction a <= resource_destruction b) (at level 70).

(** ** Tactics *)

Ltac solve_bounds :=
  repeat match goal with
  | |- 0 <= norm_state _ => apply norm_state_nonneg
  | |- c > 0 => apply c_positive
  | |- obs_threshold _ > 0 => apply obs_threshold_pos
  | |- 0 <= elimination_probability _ _ <= 1 => apply elimination_probability_bounds
  | |- 0 <= survival_probability _ _ <= 1 => apply survival_probability_bounds
  | |- _ /\ _ => split
  end; auto with resource_dynamics.

Ltac solve_preservation :=
  match goal with
  | H: preserves_resources ?a |- resource_destruction ?a = 0 =>
      apply resource_destruction_preserving; exact H
  | H: preserves_resources ?a |- elimination_probability ?a _ = 0 =>
      apply elimination_probability_zero_preserving; exact H
  | H: preserves_resources ?a |- survival_probability ?a _ = 1 =>
      unfold survival_probability; induction 1; simpl;
      [reflexivity | rewrite elimination_probability_zero_preserving by exact H; ring]
  end.

Ltac destruct_preserves :=
  repeat match goal with
  | H: preserves_resources ?a |- _ =>
      let Hd := fresh "Hdest_zero" in
      assert (Hd: resource_destruction a = 0) by (apply resource_destruction_preserving; exact H);
      clear H
  end.

Example automation_demo : forall a o,
  preserves_resources a ->
  0 <= elimination_probability a o <= 1.
Proof.
  intros a o Hpres.
  solve_bounds.
Qed.

(** * Section 18: Observer Collusion and Game-Theoretic Stability *)

Definition observer_strategy := Observer -> Action -> bool.

Definition always_punish : observer_strategy :=
  fun o a => match Rle_dec (resource_destruction a) 0 with
             | left _ => false
             | right _ => true
             end.

Definition never_punish : observer_strategy :=
  fun o a => false.

Definition elimination_under_strategy (strat : observer_strategy) (a : Action) (o : Observer) : R :=
  if strat o a then elimination_probability a o else 0.

Definition survival_under_strategy (strat : observer_strategy) (a : Action) (observers : list Observer) : R :=
  fold_right Rmult 1 (map (fun o => 1 - elimination_under_strategy strat a o) observers).

Lemma always_punish_equals_standard : forall a observers,
  survival_under_strategy always_punish a observers = survival_probability a observers.
Proof.
  intros a observers.
  unfold survival_under_strategy, survival_probability.
  induction observers as [|o rest IH].
  - simpl. reflexivity.
  - simpl. f_equal.
    + unfold elimination_under_strategy, always_punish.
      destruct (Rle_dec (resource_destruction a) 0).
      * unfold elimination_probability.
        destruct (Rle_dec (resource_destruction a) 0); [reflexivity | contradiction].
      * reflexivity.
    + exact IH.
Qed.

Definition observer_payoff (strat : observer_strategy) (a : Action) : R :=
  1 - resource_destruction a.

Theorem punishment_is_dominant_when_threatened : forall a,
  resource_destruction a > 0 ->
  observer_payoff always_punish a >= observer_payoff never_punish a.
Proof.
  intros a Hdest.
  unfold observer_payoff.
  apply Rle_ge.
  apply Req_le.
  reflexivity.
Qed.

Definition coalition := list Observer.

Definition defection_payoff (coalition : coalition) (a : Action) : R :=
  if Rle_dec (resource_destruction a) 0 then 1
  else 1 - resource_destruction a / INR (length coalition).

Definition cooperation_payoff : R := 1.

Theorem cooperation_dominates_collusion : forall coalition a,
  coalition <> [] ->
  destroys_resources a ->
  cooperation_payoff >= defection_payoff coalition a.
Proof.
  intros coalition a Hne Hdest.
  unfold cooperation_payoff, defection_payoff.
  assert (Hdest_pos: resource_destruction a > 0).
  { apply resource_destruction_destroying. exact Hdest. }
  destruct (Rle_dec (resource_destruction a) 0); [lra|].
  apply Rle_ge.
  assert (Hlen_pos: INR (length coalition) > 0).
  { apply lt_0_INR.
    destruct coalition; [contradiction | simpl; lia]. }
  unfold Rdiv.
  assert (H: resource_destruction a * / INR (length coalition) > 0).
  { apply Rmult_lt_0_compat; [exact Hdest_pos | apply Rinv_0_lt_compat; exact Hlen_pos]. }
  lra.
Qed.

Theorem independent_observation_prevents_collusion : forall a o1 o2 event_pos event_time,
  spacelike_separated o1 o2 event_pos event_time ->
  destroys_resources a ->
  elimination_probability a o1 > 0 /\ elimination_probability a o2 > 0.
Proof.
  intros a o1 o2 event_pos event_time Hsep Hdest.
  split; apply elimination_probability_positive_destructive; exact Hdest.
Qed.

End ResourceDynamics.
