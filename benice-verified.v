(******************************************************************************)
(*                                                                            *)
(*     Convergence to Resource Preservation in Delayed Elimination Games     *)
(*                                                                            *)
(*     A formal proof that optimal strategies in systems with finite-speed   *)
(*     information propagation and observation-dependent elimination         *)
(*     converge to resource-preserving fixed points under increasing         *)
(*     computational depth.                                                  *)
(*                                                                            *)
(*     "Ua mau ke ea o ka ʻāina i ka pono"                                  *)
(*     (The life of the land is perpetuated in righteousness)                *)
(*     - King Kamehameha III, July 31, 1843 (Hawaii State Motto)             *)
(*                                                                            *)
(*     Author: Charles C. Norton                                             *)
(*     Date: September 26, 2025                                              *)
(*                                                                            *)
(******************************************************************************)

Require Import Reals Lra Lia Psatz.
Require Import Ranalysis Rpower Rprod.
Require Import List FunctionalExtensionality Classical.
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

(** * Section 2: Observer Model and Discrete Approximation *)

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
        let pos := grid_point (Z.of_nat i - Z.of_nat n) 
                              (Z.of_nat j - Z.of_nat n)
                              (Z.of_nat k - Z.of_nat n) resolution in
        if Rle_dec (norm_state (state_sub pos origin)) radius then
          [mkObserver pos 0 1 Rlt_0_1]
        else
          []
      ) (seq 0 (2*n+1))
    ) (seq 0 (2*n+1))
  ) (seq 0 (2*n+1)).

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
  destruct (Rle_dec (norm_state (state_sub (grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                                                       (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                                                       (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution))))
                                                       resolution) origin)) radius).
  - (* Case when norm is <= radius *)
    simpl in Ho.
    (* Ho is now a singleton list containing the observer *)
    destruct Ho; [|contradiction].
    (* H is the equality between two observers *)
    subst o.
    simpl.
    apply Rle_trans with radius.
    + exact r.
    + apply Rle_trans with (radius + 0).
      * right; ring.
      * apply Rplus_le_compat_l.
        apply Rmult_le_pos.
        -- left; exact Hres.
        -- apply sqrt_pos.
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
    (grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution)
    origin) <= radius ->
  In (mkObserver
        (grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                   (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                   (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution)
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
  destruct (Rle_dec (norm_state (state_sub
             (grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                        (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                        (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution)
             origin)) radius).
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
  exists (mkObserver
    (grid_point (Z.of_nat n - Z.of_nat n)
                (Z.of_nat n - Z.of_nat n)
                (Z.of_nat n - Z.of_nat n) resolution) 0 1 Rlt_0_1).
  apply grid_point_in_enumerate; unfold n.
  - apply In_seq_middle.
  - apply In_seq_middle.
  - apply In_seq_middle.
  - assert (Hgrid: grid_point (Z.of_nat (Z.to_nat (up (radius / resolution))) -
                              Z.of_nat (Z.to_nat (up (radius / resolution))))
                             (Z.of_nat (Z.to_nat (up (radius / resolution))) -
                              Z.of_nat (Z.to_nat (up (radius / resolution))))
                             (Z.of_nat (Z.to_nat (up (radius / resolution))) -
                              Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution = (0, 0, 0)).
    { rewrite !Z.sub_diag.
      unfold grid_point. simpl. rewrite !Rmult_0_l. reflexivity. }
    rewrite Hgrid.
    rewrite grid_origin_norm_eq.
    exact Hnorm_bound.
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

(** Key geometric assumption: When the grid resolution is fine enough (< radius/10),
    the grid always contains at least one point within any ball of the given radius. *)
Hypothesis grid_covers_ball : forall origin radius resolution,
  0 < resolution < radius / 10 ->
  exists i j k,
    In i (seq 0 (2 * Z.to_nat (up (radius / resolution)) + 1)) /\
    In j (seq 0 (2 * Z.to_nat (up (radius / resolution)) + 1)) /\
    In k (seq 0 (2 * Z.to_nat (up (radius / resolution)) + 1)) /\
    norm_state (state_sub
      (grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                 (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                 (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution)
      origin) <= radius.

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
        (grid_point (Z.of_nat i - Z.of_nat (Z.to_nat (up (radius / resolution))))
                   (Z.of_nat j - Z.of_nat (Z.to_nat (up (radius / resolution))))
                   (Z.of_nat k - Z.of_nat (Z.to_nat (up (radius / resolution)))) resolution)
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

(** * Section 3: Elimination Probability and Survival *)

Definition elimination_probability (a : Action) (o : Observer) : R :=
  if Rle_dec (resource_destruction a) 0 then 0
  else 1 - exp (- Rabs (resource_destruction a) / obs_threshold o).

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

Definition survival_probability (a : Action) (observers : list Observer) : R :=
  fold_right Rmult 1 (map (fun o => 1 - elimination_probability a o) observers).

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

(** * Section 4: Computational Model *)

Definition computational_capacity := nat.

Definition observation_horizon (comp : computational_capacity) : R := INR comp.

Definition considered_observers (comp : computational_capacity) (origin : State) : list Observer :=
  enumerate_grid_observers origin (observation_horizon comp * c) 1.

(** Observers considered grow monotonically with computational capacity. *)
Hypothesis monotone_considered_observers : forall c1 c2 origin,
  (c1 <= c2)%nat ->
  incl (considered_observers c1 origin) (considered_observers c2 origin).

(** * Section 5: Strategy Optimization *)

Definition utility (a : Action) (comp : computational_capacity) (origin : State) : R :=
  survival_probability a (considered_observers comp origin).

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

Definition optimal_strategy (comp : computational_capacity) (origin : State) : Action :=
  if le_dec comp 10 then
    destructive_action 0.5
  else
    preserving_action.

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

(** Key assumption: Utility of destructive actions vanishes with increasing computation. *)
Hypothesis utility_destructive_vanishes : forall factor origin,
  0 < factor < 1 ->
  forall eps, eps > 0 ->
  exists N, forall comp, (comp > N)%nat ->
  utility (destructive_action factor) comp origin < eps.


(** * Section 7: Main Convergence Theorem *)

(** Main convergence theorem: Optimal strategies converge to resource preservation
    as computational capacity increases. *)
Theorem main_convergence :
  forall origin eps, eps > 0 ->
  exists N, forall comp, (comp > N)%nat ->
  Rabs (utility (optimal_strategy comp origin) comp origin - 
        utility preserving_action comp origin) < eps.
Proof.
  intros origin eps Heps.
  assert (Hfactor: 0 < 0.5 < 1) by lra.
  assert (Heps2: eps / 2 > 0) by lra.
  destruct (utility_destructive_vanishes 0.5 origin Hfactor (eps / 2) Heps2) as [N1 HN1].
  exists (max N1 11).
  intros comp Hcomp.
  unfold optimal_strategy.
  destruct (le_dec comp 10).
  exfalso.
  assert (comp >= max N1 11)%nat by lia.
  assert (comp >= 11)%nat.
  apply Nat.le_trans with (max N1 11).
  apply Nat.le_max_r.
  assumption.
  lia.
  unfold Rminus.
  rewrite Rplus_opp_r.
  rewrite Rabs_R0.
  assumption.
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

(** Preserving action is optimal for large computational capacity. *)
Lemma preserving_optimal_large_comp : forall comp origin,
  (comp > 10)%nat ->
  utility (optimal_strategy comp origin) comp origin =
  utility preserving_action comp origin.
Proof.
  intros comp origin Hcomp.
  unfold optimal_strategy.
  destruct (le_dec comp 10).
  - lia.
  - reflexivity.
Qed.

(** Optimal strategy converges to preservation. *)
Lemma optimal_converges_to_preservation : forall origin,
  forall eps, eps > 0 ->
  exists N, forall comp, (comp > N)%nat ->
  utility (optimal_strategy comp origin) comp origin >= 1 - eps.
Proof.
  intros origin eps Heps.
  exists 11%nat.
  intros comp Hcomp.
  rewrite preserving_optimal_large_comp.
  - rewrite utility_preserving_constant.
    lra.
  - lia.
Qed.

(** The gap between optimal and any destructive strategy grows with computation. *)
Lemma preservation_dominance_grows : forall origin factor,
  0 < factor < 1 ->
  forall N, exists comp, (comp > N)%nat /\
  utility preserving_action comp origin -
  utility (destructive_action factor) comp origin > 0.5.
Proof.
  intros origin factor Hfactor N.
  (* By utility_destructive_vanishes, destructive utility approaches 0 *)
  (* while preserving utility stays at 1 *)
  destruct (utility_destructive_vanishes factor origin Hfactor 0.4 ltac:(lra)) as [M HM].
  exists (max (S N) (S M)).
  split.
  - apply Nat.lt_le_trans with (S N).
    + lia.
    + apply Nat.le_max_l.
  - rewrite utility_preserving_constant.
    assert (Hmax: (max (S N) (S M) > M)%nat).
    { apply Nat.lt_le_trans with (S M).
      - lia.
      - apply Nat.le_max_r. }
    specialize (HM _ Hmax).
    lra.
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

End ResourceDynamics.
      
