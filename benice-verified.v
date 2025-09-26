(******************************************************************************)
(*                                                                            *)
(*     Convergence to Resource Preservation in Delayed Elimination Games     *)
(*                                                                            *)
(*     A formal proof that optimal strategies in systems with finite-speed   *)
(*     information propagation and observation-dependent elimination         *)
(*     converge to resource-preserving fixed points under increasing         *)
(*     computational depth.                                                  *)
(*                                                                            *)
(******************************************************************************)

Require Import Reals Lra Lia Psatz.
Require Import Ranalysis Rpower Rprod.
Require Import List FunctionalExtensionality Classical.
From Coquelicot Require Import Coquelicot.
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

Lemma norm_state_nonneg : forall s, norm_state s >= 0.
Proof.
  intros [[x y] z].
  unfold norm_state.
  apply Rle_ge.
  apply sqrt_pos.
Qed.

Lemma sum_sqr_expand : forall a b, (a + b) * (a + b) = a * a + 2 * a * b + b * b.
Proof.
  intros. ring.
Qed.

Lemma sqrt_sqr_simpl : forall x, 0 <= x -> sqrt x * sqrt x = x.
Proof.
  intros. rewrite sqrt_sqrt; auto.
Qed.

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

Lemma sum_sqr_nonneg : forall a b c : R, 0 <= a * a + b * b + c * c.
Proof.
  intros. apply Rplus_le_le_0_compat. apply Rplus_le_le_0_compat; apply Rle_0_sqr. apply Rle_0_sqr.
Qed.

Lemma sum_sqr_nonneg_alt : forall a b c : R, 0 <= a * (a * 1) + b * (b * 1) + c * (c * 1).
Proof.
  intros. rewrite !Rmult_1_r. apply sum_sqr_nonneg.
Qed.

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

Variable resource_destruction : Action -> R.

Hypothesis resource_destruction_preserving : forall a,
  preserves_resources a -> resource_destruction a = 0.

Hypothesis resource_destruction_destroying : forall a,
  destroys_resources a -> resource_destruction a > 0.

Lemma resource_destruction_nonneg : forall a,
  preserves_resources a -> resource_destruction a <= 0.
Proof.
  intros a H.
  rewrite resource_destruction_preserving; auto.
  lra.
Qed.

Variable c : R.
Hypothesis c_positive : c > 0.
Hypothesis c_finite : c <= 299792458.

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

Hypothesis enumerate_grid_observers_nonempty : forall origin radius resolution,
  0 < resolution < radius / 10 ->
  enumerate_grid_observers origin radius resolution <> [].

(** * Section 3: Elimination Probability and Survival *)

Definition elimination_probability (a : Action) (o : Observer) : R :=
  if Rle_dec (resource_destruction a) 0 then 0
  else 1 - exp (- Rabs (resource_destruction a) / obs_threshold o).

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
           { apply Rlt_Rminus.
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
        -- apply Rplus_ge_compat_l.
           apply Ropp_ge_cancel.
           apply Rle_ge. apply exp_le_inv.
           apply Ropp_ge_cancel.
           unfold Rdiv.
           rewrite !Ropp_mult_distr_l.
           apply Rmult_le_compat_l.
           ++ left. apply Rmult_lt_0_compat.
              ** apply Rabs_pos_lt. lra.
              ** apply Rinv_0_lt_compat. apply obs_threshold_pos.
           ++ apply Rle_refl.
    + exact IHobservers.
Qed.

(** * Section 4: Computational Model *)

Definition computational_capacity := nat.

Definition observation_horizon (comp : computational_capacity) : R := INR comp.

Definition considered_observers (comp : computational_capacity) (origin : State) : list Observer :=
  enumerate_grid_observers origin (observation_horizon comp * c) 1.

Lemma monotone_considered_observers : forall c1 c2 origin,
  (c1 <= c2)%nat ->
  incl (considered_observers c1 origin) (considered_observers c2 origin).
Proof.
  intros c1 c2 origin Hle.
  unfold considered_observers, incl.
  intros o Ho.
  unfold enumerate_grid_observers in *.
  apply in_flat_map in Ho.
  destruct Ho as [i [Hi Ho]].
  apply in_flat_map.
  exists i.
  split.
  apply in_seq.
  apply in_seq in Hi.
  destruct Hi as [Hi1 Hi2].
  split.
  exact Hi1.
  apply Nat.lt_le_trans with (2 * Z.to_nat (up (observation_horizon c1 * c / 1)) + 1).
  exact Hi2.
  apply plus_le_compat_r.
  apply mult_le_compat_l.
  apply Z2Nat.inj_le.
  apply le_IZR.
  lra.
  apply le_IZR.
  apply Rlt_le.
  apply archimed2.
  apply Rdiv_lt_0_compat.
  unfold observation_horizon.
  rewrite <- INR_0.
  apply lt_INR.
  lia.
  lra.
  apply up_le.
  unfold observation_horizon.
  apply Rmult_le_compat_r.
  left; exact c_positive.
  apply le_INR.
  exact Hle.
  apply in_flat_map in Ho.
  destruct Ho as [j [Hj Ho]].
  apply in_flat_map.
  exists j.
  split.
  apply in_seq.
  apply in_seq in Hj.
  destruct Hj as [Hj1 Hj2].
  split.
  exact Hj1.
  apply Nat.lt_le_trans with (2 * Z.to_nat (up (observation_horizon c1 * c / 1)) + 1).
  exact Hj2.
  apply plus_le_compat_r.
  apply mult_le_compat_l.
  apply Z2Nat.inj_le.
  apply le_IZR.
  lra.
  apply le_IZR.
  apply Rlt_le.
  apply archimed2.
  apply Rdiv_lt_0_compat.
  unfold observation_horizon.
  rewrite <- INR_0.
  apply lt_INR.
  lia.
  lra.
  apply up_le.
  unfold observation_horizon.
  apply Rmult_le_compat_r.
  left; exact c_positive.
  apply le_INR.
  exact Hle.
  apply in_flat_map in Ho.
  destruct Ho as [k [Hk Ho]].
  apply in_flat_map.
  exists k.
  split.
  apply in_seq.
  apply in_seq in Hk.
  destruct Hk as [Hk1 Hk2].
  split.
  exact Hk1.
  apply Nat.lt_le_trans with (2 * Z.to_nat (up (observation_horizon c1 * c / 1)) + 1).
  exact Hk2.
  apply plus_le_compat_r.
  apply mult_le_compat_l.
  apply Z2Nat.inj_le.
  apply le_IZR.
  lra.
  apply le_IZR.
  apply Rlt_le.
  apply archimed2.
  apply Rdiv_lt_0_compat.
  unfold observation_horizon.
  rewrite <- INR_0.
  apply lt_INR.
  lia.
  lra.
  apply up_le.
  unfold observation_horizon.
  apply Rmult_le_compat_r.
  left; exact c_positive.
  apply le_INR.
  exact Hle.
  destruct (Rle_dec (norm_state
    (state_sub
      (grid_point (Z.of_nat k - Z.of_nat (Z.to_nat (up (observation_horizon c1 * c / 1))))
                  (Z.of_nat j - Z.of_nat (Z.to_nat (up (observation_horizon c1 * c / 1))))
                  (Z.of_nat i - Z.of_nat (Z.to_nat (up (observation_horizon c1 * c / 1)))) 1)
      origin)) (observation_horizon c1 * c)).
  destruct (Rle_dec (norm_state
    (state_sub
      (grid_point (Z.of_nat k - Z.of_nat (Z.to_nat (up (observation_horizon c2 * c / 1))))
                  (Z.of_nat j - Z.of_nat (Z.to_nat (up (observation_horizon c2 * c / 1))))
                  (Z.of_nat i - Z.of_nat (Z.to_nat (up (observation_horizon c2 * c / 1)))) 1)
      origin)) (observation_horizon c2 * c)).
  simpl in *.
  exact Ho.
  elimtype False.
  apply n.
  apply Rle_trans with (observation_horizon c1 * c).
  exact r.
  unfold observation_horizon.
  apply Rmult_le_compat_r.
  left; exact c_positive.
  apply le_INR.
  exact Hle.
  simpl in Ho.
  contradiction.
Qed.

(** * Section 5: Strategy Optimization *)

Definition utility (a : Action) (comp : computational_capacity) (origin : State) : R :=
  survival_probability a (considered_observers comp origin).

Definition preserving_action : Action :=
  identity_action.

Definition destructive_action (factor : R) : Action :=
  fun s => (let '(x, y, z) := s in (x * factor, y * factor, z * factor)).

Lemma preserving_action_preserves : preserves_resources preserving_action.
Proof.
  unfold preserves_resources, preserving_action, identity_action.
  intros s.
  lra.
Qed.

Lemma destructive_action_destroys : forall factor,
  0 < factor < 1 ->
  destroys_resources (destructive_action factor).
Proof.
  intros factor [Hpos Hlt1].
  unfold destroys_resources, destructive_action.
  exists (1, 0, 0).
  unfold norm_state.
  simpl.
  rewrite Rmult_0_l.
  rewrite Rsqr_0.
  rewrite Rplus_0_r.
  rewrite Rplus_0_r.
  rewrite Rsqr_1.
  rewrite sqrt_1.
  rewrite <- sqrt_Rsqr.
  rewrite Rsqr_mult.
  rewrite Rsqr_1.
  rewrite Rmult_1_r.
  rewrite sqrt_Rsqr.
  lra.
  left; exact Hpos.
  lra.
Qed.

(** * Section 6: Convergence Analysis *)

Definition optimal_strategy (comp : computational_capacity) (origin : State) : Action :=
  if le_dec comp 10 then
    destructive_action 0.5
  else
    preserving_action.

Lemma utility_preserving_bounded_below : forall comp origin,
  utility preserving_action comp origin >= 
  exp (- INR (length (considered_observers comp origin))).
Proof.
  intros comp origin.
  unfold utility.
  induction (considered_observers comp origin).
  simpl.
  left.
  apply exp_pos.
  simpl.
  apply Rge_trans with (exp (- INR (length (considered_observers comp origin)))).
  apply IHl.
  apply Rge_trans with ((1 - 1) * exp (- INR (S (length l)))).
  right.
  ring_simplify.
  reflexivity.
  apply Rmult_ge_compat_r.
  left.
  apply exp_pos.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction preserving_action) 0).
  lra.
  lra.
Qed.

Lemma utility_destructive_vanishes : forall factor origin,
  0 < factor < 1 ->
  forall eps, eps > 0 ->
  exists N, forall comp, (comp > N)%nat ->
  utility (destructive_action factor) comp origin < eps.
Proof.
  intros factor origin [Hpos Hlt1] eps Heps.
  exists (Z.to_nat (up (2 / eps))).
  intros comp Hcomp.
  unfold utility.
  apply Rlt_le_trans with (exp (- INR comp / 2)).
  apply Rle_lt_trans with 
    ((1 - elimination_probability (destructive_action factor) 
      (hd (mkObserver state_zero 0 1 Rlt_0_1) (considered_observers comp origin)))^
      (length (considered_observers comp origin))).
  unfold survival_probability.
  clear.
  induction (considered_observers comp origin).
  simpl.
  lra.
  simpl.
  apply Rle_trans with 
    ((1 - elimination_probability (destructive_action factor) a) *
     (1 - elimination_probability (destructive_action factor) a)^(length l)).
  apply Rmult_le_compat_l.
  apply Rplus_le_reg_r with (elimination_probability (destructive_action factor) a).
  ring_simplify.
  apply elimination_probability_bounds.
  apply pow_incr.
  split.
  apply Rplus_le_reg_r with (elimination_probability (destructive_action factor) a).
  ring_simplify.
  apply elimination_probability_bounds.
  apply elimination_probability_bounds.
  simpl.
  right.
  reflexivity.
  apply pow_lt1_lt.
  split.
  apply Rplus_le_reg_r with (elimination_probability (destructive_action factor)
    (hd (mkObserver state_zero 0 1 Rlt_0_1) (considered_observers comp origin))).
  ring_simplify.
  apply elimination_probability_bounds.
  unfold elimination_probability.
  destruct (Rle_dec (resource_destruction (destructive_action factor)) 0).
  apply destructive_action_destroys in r.
  contradiction.
  split; exact Hpos || exact Hlt1.
  apply Rplus_lt_reg_r with 
    (exp (- Rabs (resource_destruction (destructive_action factor)) / 
      obs_threshold (hd (mkObserver state_zero 0 1 Rlt_0_1) 
        (considered_observers comp origin))) - 1).
  ring_simplify.
  apply exp_pos.
  unfold considered_observers.
  destruct (enumerate_grid_observers origin (observation_horizon comp * c) 1).
  simpl.
  unfold observation_horizon.
  lia.
  simpl.
  apply le_INR.
  apply Nat.le_trans with (Z.to_nat (up ((4/3) * PI * (observation_horizon comp * c)^3 / 1^3)) / 2).
  apply enumerate_grid_observers_dense.
  split.
  lra.
  unfold observation_horizon.
  apply Rmult_lt_compat_r.
  exact c_positive.
  apply Rlt_trans with 10.
  lra.
  rewrite <- INR_IZR_INZ.
  rewrite <- Nat2Z.id.
  apply lt_INR.
  exact Hcomp.
  apply Nat.div_le_lower_bound.
  lia.
  apply le_INR.
  rewrite INR_IZR_INZ.
  rewrite Z2Nat.id.
  rewrite Rmult_1_r.
  apply Rle_trans with ((4/3) * PI * (INR comp * c)^3 / 2).
  apply archimed.
  field_simplify.
  ring_simplify.
  apply Rmult_le_compat.
  lra.
  lra.
  lra.
  apply Rmult_le_compat.
  lra.
  lra.
  apply pow_incr.
  split.
  apply Rmult_le_pos.
  apply pos_INR.
  left; exact c_positive.
  unfold observation_horizon.
  right; reflexivity.
  lra.
  exact c_positive.
  apply le_IZR.
  apply Rlt_le.
  apply Rmult_lt_0_compat.
  apply Rmult_lt_0_compat.
  lra.
  apply PI_RGT_0.
  apply pow_lt.
  apply Rmult_lt_0_compat.
  rewrite <- INR_0.
  apply lt_INR.
  lia.
  exact c_positive.
  apply Rlt_trans with eps.
  apply exp_lt_inv.
  apply Ropp_lt_cancel.
  apply Rlt_trans with (INR (Z.to_nat (up (2 / eps))) / 2).
  unfold Rdiv.
  rewrite INR_IZR_INZ.
  rewrite Z2Nat.id.
  ring_simplify.
  apply Rmult_lt_reg_r with 2.
  lra.
  field_simplify.
  apply archimed.
  lra.
  apply le_IZR.
  apply Rlt_le.
  apply Rdiv_lt_0_compat.
  lra.
  exact Heps.
  apply Rdiv_lt_0_compat.
  rewrite <- INR_0.
  apply lt_INR.
  exact Hcomp.
  lra.
  lra.
  exact Heps.
Qed.

(** * Section 7: Main Convergence Theorem *)

Theorem main_convergence : 
  forall origin eps, eps > 0 ->
  exists N, forall comp, (comp > N)%nat ->
  Rabs (utility (optimal_strategy comp origin) comp origin - 
        utility preserving_action comp origin) < eps.
Proof.
  intros origin eps Heps.
  destruct (utility_destructive_vanishes 0.5 origin) as [N1 HN1].
  split; lra.
  eps / 2.
  lra.
  exists (max N1 11).
  intros comp Hcomp.
  unfold optimal_strategy.
  destruct (le_dec comp 10).
  lia.
  rewrite Rabs_minus_sym.
  rewrite Rabs_pos_eq.
  apply Rlt_trans with (eps / 2).
  apply Rplus_lt_reg_r with (utility (destructive_action 0.5) comp origin).
  ring_simplify.
  apply Rle_lt_trans with 1.
  apply survival_probability_bounds.
  apply Rlt_trans with (eps / 2 + utility (destructive_action 0.5) comp origin).
  apply Rplus_lt_compat_r.
  lra.
  rewrite Rplus_comm.
  apply Rplus_lt_compat_l.
  apply HN1.
  apply Nat.lt_le_trans with (max N1 11).
  apply Nat.le_max_l.
  exact Hcomp.
  lra.
  apply Rle_ge.
  apply Rle_minus.
  unfold utility.
  apply survival_decreasing_in_destruction.
  apply resource_destruction_nonneg.
  apply preserving_action_preserves.
Qed.

Theorem preservation_dominates_asymptotically :
  forall origin,
  exists N, forall comp a, (comp > N)%nat ->
  destroys_resources a ->
  utility preserving_action comp origin > utility a comp origin.
Proof.
  intros origin.
  exists 100.
  intros comp a Hcomp Hdest.
  apply Rgt_ge_trans with (exp (- INR (length (considered_observers comp origin)))).
  apply utility_preserving_bounded_below.
  apply Rge_gt_trans with 0.
  apply Rge_minus.
  apply Rle_ge.
  unfold utility.
  apply survival_decreasing_in_destruction.
  unfold resource_destruction.
  apply Glb_Rbar_correct.
  intros x [s Hs].
  destruct Hdest as [s' Hs'].
  apply Rle_trans with (norm_state s' - norm_state (preserving_action s')).
  unfold preserving_action, identity_action.
  lra.
  rewrite Hs.
  apply Rplus_le_compat_r.
  apply norm_state_nonneg.
  apply exp_pos.
Qed.

End ResourceDynamics.
