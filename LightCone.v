(** Signals, judges and the light cone; the lattice of potential judges; the hazard sum; the discounted lattice sum. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.
From BeNice Require Import Vectors Actions Sums.

(** * Section 4: A judge at distance d receives the signal at t0 + d / c and its response arrives no earlier than t0 + 2 d / c, so a horizon T exposes the agent to the judges within c T / 2; the parameters are the speed c, the lattice spacing res and the tolerance tol. *)

Record Attenuation := mkAttenuation {
  att : R -> R;
  att_kappa : R;
  att_kappa_pos : 0 < att_kappa;
  att_pos : forall d, 0 <= d -> 0 < att d;
  att_le_1 : forall d, 0 <= d -> att d <= 1;
  att_inverse_square : forall d, 0 <= d -> att_kappa / (1 + d * d) <= att d
}.

Section Geometry.

Variable c : R.
Hypothesis c_pos : 0 < c.

Variable res : R.
Hypothesis res_pos : 0 < res.

Variable tol : R.
Hypothesis tol_pos : 0 < tol.

Record Observer := mkObserver {
  obs_pos : Vec3;
  obs_tol : R;
  obs_tol_pos : 0 < obs_tol
}.

Definition dist (o : Observer) (x0 : Vec3) : R := norm (vsub (obs_pos o) x0).

Lemma dist_nonneg : forall o x0, 0 <= dist o x0.
Proof. intros; apply norm_nonneg. Qed.

Definition reception_time (o : Observer) (x0 : Vec3) (t0 : R) : R :=
  t0 + dist o x0 / c.

Definition earliest_response (o : Observer) (x0 : Vec3) (t0 : R) : R :=
  t0 + 2 * dist o x0 / c.

(** Nothing from a judge reaches the agent before the round trip 2 d / c. *)
Theorem round_trip : forall o x0 t0 t_decide t_arrive,
  reception_time o x0 t0 <= t_decide ->
  t_decide + dist o x0 / c <= t_arrive ->
  earliest_response o x0 t0 <= t_arrive.
Proof.
  intros o x0 t0 td ta H1 H2; unfold reception_time, earliest_response in *.
  unfold Rdiv in *; lra.
Qed.

Definition horizon_radius (T : R) : R := c * T / 2.

Theorem within_horizon_iff : forall o x0 t0 T,
  earliest_response o x0 t0 <= t0 + T <-> dist o x0 <= horizon_radius T.
Proof.
  intros o x0 t0 T; unfold earliest_response, horizon_radius.
  split; intro H.
  - apply Rmult_le_reg_l with (2 / c); [apply Rdiv_lt_0_compat; lra |].
    replace (2 / c * (c * T / 2)) with T by (field; lra).
    unfold Rdiv in *; lra.
  - apply Rmult_le_compat_l with (r := 2 / c) in H; [| left; apply Rdiv_lt_0_compat; lra].
    replace (2 / c * (c * T / 2)) with T in H by (field; lra).
    unfold Rdiv in *; lra.
Qed.

Lemma vsub_vsub_cancel : forall p q x0, vsub (vsub p x0) (vsub q x0) = vsub p q.
Proof. intros [[a b] d] [[e f] g] [[h i] j]; unfold vsub; f_equal; [f_equal|]; ring. Qed.

(** No judge's reception lies in the timelike past of another's: c times their reception-time gap is at most their distance. *)
Theorem receptions_not_timelike : forall o1 o2 x0 t0,
  c * Rabs (reception_time o1 x0 t0 - reception_time o2 x0 t0) <=
  norm (vsub (obs_pos o1) (obs_pos o2)).
Proof.
  intros o1 o2 x0 t0; unfold reception_time, dist.
  replace (t0 + norm (vsub (obs_pos o1) x0) / c - (t0 + norm (vsub (obs_pos o2) x0) / c))
    with ((norm (vsub (obs_pos o1) x0) - norm (vsub (obs_pos o2) x0)) / c) by (field; lra).
  unfold Rdiv; rewrite Rabs_mult, (Rabs_right (/ c)) by (left; apply Rinv_0_lt_compat; exact c_pos).
  replace (c * (Rabs (norm (vsub (obs_pos o1) x0) - norm (vsub (obs_pos o2) x0)) * / c))
    with (Rabs (norm (vsub (obs_pos o1) x0) - norm (vsub (obs_pos o2) x0))) by (field; lra).
  rewrite <- (vsub_vsub_cancel (obs_pos o1) (obs_pos o2) x0).
  apply norm_reverse_triangle_abs.
Qed.

(** ** The potential judges within radius rad of x0 are the points of the cubic lattice of spacing res in that ball, each of tolerance tol. *)

Definition lattice_point (x0 : Vec3) (n i j k : nat) : Vec3 :=
  vadd x0 (vscale res (IZR (Z.of_nat i - Z.of_nat n),
                       IZR (Z.of_nat j - Z.of_nat n),
                       IZR (Z.of_nat k - Z.of_nat n))).

Lemma lattice_point_sub : forall x0 n i j k,
  vsub (lattice_point x0 n i j k) x0 =
  vscale res (IZR (Z.of_nat i - Z.of_nat n),
              IZR (Z.of_nat j - Z.of_nat n),
              IZR (Z.of_nat k - Z.of_nat n)).
Proof. intros [[a b] d] n i j k; unfold lattice_point, vadd, vsub, vscale; f_equal; [f_equal|]; ring. Qed.

Lemma lattice_point_dist : forall x0 n i j k,
  norm (vsub (lattice_point x0 n i j k) x0) =
  res * norm (IZR (Z.of_nat i - Z.of_nat n),
              IZR (Z.of_nat j - Z.of_nat n),
              IZR (Z.of_nat k - Z.of_nat n)).
Proof. intros; rewrite lattice_point_sub, norm_scale_nonneg by lra; reflexivity. Qed.

Definition grid_size (rad : R) : nat := Z.to_nat (up (rad / res)).

Definition cube_size (rad : R) : nat := Z.to_nat (Int_part (rad / (2 * res))).

Definition in_ball (x0 : Vec3) (rad : R) (p : Vec3) : bool :=
  if Rle_dec (norm (vsub p x0)) rad then true else false.

Lemma in_ball_true : forall x0 rad p, in_ball x0 rad p = true <-> norm (vsub p x0) <= rad.
Proof.
  intros x0 rad p; unfold in_ball; destruct (Rle_dec (norm (vsub p x0)) rad); split; intro H;
    try reflexivity; try tauto; discriminate.
Qed.

Definition cell (x0 : Vec3) (rad : R) (n i j k : nat) : list Observer :=
  if in_ball x0 rad (lattice_point x0 n i j k)
  then [mkObserver (lattice_point x0 n i j k) tol tol_pos]
  else [].

Definition judges (x0 : Vec3) (rad : R) : list Observer :=
  let n := grid_size rad in
  let L := seq 0 (2 * n + 1) in
  flat_map (fun i => flat_map (fun j => flat_map (fun k => cell x0 rad n i j k) L) L) L.

Lemma judges_spec : forall x0 rad o,
  In o (judges x0 rad) ->
  exists i j k,
    In i (seq 0 (2 * grid_size rad + 1)) /\
    In j (seq 0 (2 * grid_size rad + 1)) /\
    In k (seq 0 (2 * grid_size rad + 1)) /\
    o = mkObserver (lattice_point x0 (grid_size rad) i j k) tol tol_pos /\
    norm (vsub (lattice_point x0 (grid_size rad) i j k) x0) <= rad.
Proof.
  intros x0 rad o Ho; unfold judges in Ho.
  apply in_flat_map in Ho; destruct Ho as [i [Hi Ho]].
  apply in_flat_map in Ho; destruct Ho as [j [Hj Ho]].
  apply in_flat_map in Ho; destruct Ho as [k [Hk Ho]].
  unfold cell in Ho.
  destruct (in_ball x0 rad (lattice_point x0 (grid_size rad) i j k)) eqn:E.
  - destruct Ho as [Ho | []]; subst o.
    exists i, j, k; repeat split; try assumption.
    apply in_ball_true; exact E.
  - destruct Ho.
Qed.

Lemma judges_dist : forall x0 rad o, In o (judges x0 rad) -> dist o x0 <= rad.
Proof.
  intros x0 rad o Ho; destruct (judges_spec x0 rad o Ho) as [i [j [k [_ [_ [_ [Heq Hn]]]]]]].
  subst o; unfold dist; simpl; exact Hn.
Qed.

Lemma judges_tol : forall x0 rad o, In o (judges x0 rad) -> obs_tol o = tol.
Proof.
  intros x0 rad o Ho; destruct (judges_spec x0 rad o Ho) as [i [j [k [_ [_ [_ [Heq _]]]]]]].
  subst o; reflexivity.
Qed.

(** Sums over the judges unfold to triple sums over the lattice indices. *)
Lemma Rsum_judges : forall (F : Observer -> R) x0 rad,
  Rsum F (judges x0 rad) =
  Rsum (fun i => Rsum (fun j => Rsum (fun k =>
    if in_ball x0 rad (lattice_point x0 (grid_size rad) i j k)
    then F (mkObserver (lattice_point x0 (grid_size rad) i j k) tol tol_pos) else 0)
    (seq 0 (2 * grid_size rad + 1))) (seq 0 (2 * grid_size rad + 1))) (seq 0 (2 * grid_size rad + 1)).
Proof.
  intros F x0 rad; unfold judges.
  rewrite Rsum_flat_map; apply Rsum_ext; intros i _.
  rewrite Rsum_flat_map; apply Rsum_ext; intros j _.
  rewrite Rsum_flat_map; apply Rsum_ext; intros k _.
  unfold cell; apply Rsum_if.
Qed.

(** ** Counting the judges: the inscribed cube from below and the enclosing cube from above. *)

Lemma cube_size_INR : forall rad, 0 <= rad ->
  INR (cube_size rad) = IZR (Int_part (rad / (2 * res))).
Proof.
  intros rad Hrad; unfold cube_size; apply INR_Z_to_nat.
  apply Int_part_nonneg; apply Rdiv_nonneg; lra.
Qed.

Lemma grid_size_INR : forall rad, 0 <= rad ->
  INR (grid_size rad) = IZR (up (rad / res)).
Proof.
  intros rad Hrad; unfold grid_size; apply INR_Z_to_nat.
  apply up_nonneg; apply Rdiv_nonneg; lra.
Qed.

Lemma cube_size_bounds : forall rad, 0 <= rad ->
  rad / (2 * res) - 1 < INR (cube_size rad) /\ INR (cube_size rad) <= rad / (2 * res).
Proof.
  intros rad Hrad; rewrite cube_size_INR by exact Hrad.
  destruct (base_Int_part (rad / (2 * res))) as [H1 H2]; lra.
Qed.

Lemma grid_size_bounds : forall rad, 0 <= rad ->
  rad / res < INR (grid_size rad) /\ INR (grid_size rad) <= rad / res + 1.
Proof.
  intros rad Hrad; rewrite grid_size_INR by exact Hrad.
  destruct (archimed (rad / res)) as [H1 H2]; lra.
Qed.

Lemma cube_le_grid : forall rad, 0 <= rad -> (cube_size rad <= grid_size rad)%nat.
Proof.
  intros rad Hrad.
  destruct (cube_size_bounds rad Hrad) as [_ Hm].
  destruct (grid_size_bounds rad Hrad) as [Hn _].
  assert (Hhalf : rad / (2 * res) <= rad / res).
  { unfold Rdiv; rewrite Rinv_mult.
    assert (0 < / res) by (apply Rinv_0_lt_compat; exact res_pos).
    nra. }
  apply INR_le; lra.
Qed.

(** A lattice point whose indices lie within cube_size of the centre is in the ball. *)
Lemma cube_point_in_ball : forall x0 rad i j k,
  0 <= rad ->
  (grid_size rad - cube_size rad <= i <= grid_size rad + cube_size rad)%nat ->
  (grid_size rad - cube_size rad <= j <= grid_size rad + cube_size rad)%nat ->
  (grid_size rad - cube_size rad <= k <= grid_size rad + cube_size rad)%nat ->
  norm (vsub (lattice_point x0 (grid_size rad) i j k) x0) <= rad.
Proof.
  intros x0 rad i j k Hrad Hi Hj Hk.
  rewrite lattice_point_dist.
  set (n := grid_size rad) in *. set (m := cube_size rad) in *.
  assert (Hmn := cube_le_grid rad Hrad). fold n m in Hmn.
  assert (Hbound : forall u, (n - m <= u <= n + m)%nat ->
                   Rabs (IZR (Z.of_nat u - Z.of_nat n)) <= INR m).
  { intros u Hu.
    rewrite INR_IZR_INZ.
    apply Rabs_le; split.
    - rewrite <- opp_IZR; apply IZR_le; lia.
    - apply IZR_le; lia. }
  assert (H := cube_in_ball _ _ _ (INR m) (Hbound i Hi) (Hbound j Hj) (Hbound k Hk)).
  destruct (cube_size_bounds rad Hrad) as [_ Hm]. fold m in Hm.
  assert (Hm0 : 0 <= INR m) by apply pos_INR.
  assert (Hs3 := sqrt3_lt_2).
  assert (H2 : INR m * sqrt 3 <= INR m * 2) by nra.
  assert (H3 : res * (INR m * 2) <= rad).
  { unfold Rdiv in Hm; rewrite Rinv_mult in Hm.
    assert (0 < / res) by (apply Rinv_0_lt_compat; exact res_pos).
    apply Rmult_le_reg_r with (/ res); [assumption |].
    replace (res * (INR m * 2) * / res) with (INR m * 2) by (field; lra).
    nra. }
  assert (Hnn := norm_nonneg (IZR (Z.of_nat i - Z.of_nat n), IZR (Z.of_nat j - Z.of_nat n),
                              IZR (Z.of_nat k - Z.of_nat n))).
  nra.
Qed.

(** Lower bound for a sum over the judges by the inscribed cube. *)
Lemma Rsum_judges_lower : forall (F : Observer -> R) x0 rad C,
  0 <= rad -> 0 <= C ->
  (forall p, norm (vsub p x0) <= rad -> C <= F (mkObserver p tol tol_pos)) ->
  INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1) * C
  <= Rsum F (judges x0 rad).
Proof.
  intros F x0 rad C Hrad HC HF.
  rewrite Rsum_judges.
  set (n := grid_size rad). set (m := cube_size rad).
  set (L := seq 0 (2 * n + 1)). set (mid := seq (n - m) (2 * m + 1)).
  set (term := fun i j k =>
    if in_ball x0 rad (lattice_point x0 n i j k)
    then F (mkObserver (lattice_point x0 n i j k) tol tol_pos) else 0).
  assert (Hmn : (m <= n)%nat) by apply cube_le_grid, Hrad.
  assert (Hterm_nonneg : forall i j k, 0 <= term i j k).
  { intros i j k; unfold term.
    destruct (in_ball x0 rad (lattice_point x0 n i j k)) eqn:E; [| lra].
    apply Rle_trans with C; [exact HC |]. apply HF. apply in_ball_true; exact E. }
  assert (Hterm_mid : forall i j k, In i mid -> In j mid -> In k mid -> C <= term i j k).
  { intros i j k Hi Hj Hk; unfold term.
    apply in_seq in Hi; apply in_seq in Hj; apply in_seq in Hk.
    assert (Hin : in_ball x0 rad (lattice_point x0 n i j k) = true).
    { apply in_ball_true. apply cube_point_in_ball; [exact Hrad | lia | lia | lia]. }
    rewrite Hin. apply HF. apply in_ball_true; exact Hin. }
  assert (Hlen : (n - m + (2 * m + 1) <= 2 * n + 1)%nat) by lia.
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k => term i j k) L) L) mid).
  2:{ apply Rsum_seq_sub; [exact Hlen |].
      intros i _; apply Rsum_nonneg; intros j _; apply Rsum_nonneg; intros k _; apply Hterm_nonneg. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k => term i j k) L) mid) mid).
  2:{ apply Rsum_le; intros i _; apply Rsum_seq_sub; [exact Hlen |].
      intros j _; apply Rsum_nonneg; intros k _; apply Hterm_nonneg. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k => term i j k) mid) mid) mid).
  2:{ apply Rsum_le; intros i _; apply Rsum_le; intros j _; apply Rsum_seq_sub; [exact Hlen |].
      intros k _; apply Hterm_nonneg. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k => C) mid) mid) mid).
  2:{ apply Rsum_le; intros i Hi; apply Rsum_le; intros j Hj; apply Rsum_le; intros k Hk.
      apply Hterm_mid; assumption. }
  rewrite !Rsum_const. unfold mid; rewrite length_seq.
  apply Req_le; ring.
Qed.

Theorem judges_count_lower : forall x0 rad, 0 <= rad ->
  INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1)
  <= INR (length (judges x0 rad)).
Proof.
  intros x0 rad Hrad.
  assert (H := Rsum_judges_lower (fun _ => 1) x0 rad 1 Hrad Rle_0_1 (fun _ _ => Rle_refl 1)).
  rewrite Rsum_const in H. lra.
Qed.

Theorem judges_count_upper : forall x0 rad,
  INR (length (judges x0 rad)) <=
  INR (2 * grid_size rad + 1) * INR (2 * grid_size rad + 1) * INR (2 * grid_size rad + 1).
Proof.
  intros x0 rad.
  assert (E : INR (length (judges x0 rad)) = Rsum (fun _ => 1) (judges x0 rad)).
  { rewrite Rsum_const; ring. }
  rewrite E, Rsum_judges.
  set (L := seq 0 (2 * grid_size rad + 1)).
  assert (HL : INR (length L) = INR (2 * grid_size rad + 1)) by (unfold L; rewrite length_seq; reflexivity).
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k => 1) L) L) L).
  - apply Rsum_le; intros i _; apply Rsum_le; intros j _; apply Rsum_le; intros k _.
    destruct (in_ball x0 rad (lattice_point x0 (grid_size rad) i j k)); lra.
  - rewrite !Rsum_const, HL. apply Req_le; ring.
Qed.

(** The judges always include the agent's own cell: the list is never empty. *)
Lemma judges_nonempty : forall x0 rad, 0 <= rad -> (1 <= length (judges x0 rad))%nat.
Proof.
  intros x0 rad Hrad.
  assert (H := judges_count_lower x0 rad Hrad).
  assert (H1 : 1 <= INR (2 * cube_size rad + 1)).
  { replace 1 with (INR 1) by reflexivity. apply le_INR. lia. }
  assert (H2 : 1 <= INR (length (judges x0 rad))) by nra.
  replace 1 with (INR 1) in H2 by reflexivity.
  apply INR_le; exact H2.
Qed.

(** ** The hazard sum: the attenuation at each judge's distance, per unit tolerance, summed over the judges. *)

Definition hazard (A : Attenuation) (x0 : Vec3) (rad : R) : R :=
  Rsum (fun o => att A (dist o x0) / obs_tol o) (judges x0 rad).

Lemma hazard_nonneg : forall A x0 rad, 0 <= hazard A x0 rad.
Proof.
  intros A x0 rad; unfold hazard; apply Rsum_nonneg; intros o Ho.
  apply Rdiv_nonneg; [left; apply att_pos, dist_nonneg | apply obs_tol_pos].
Qed.

Lemma hazard_lower_cube : forall A x0 rad, 0 <= rad ->
  INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1)
    * (att_kappa A / ((1 + rad * rad) * tol)) <= hazard A x0 rad.
Proof.
  intros A x0 rad Hrad; unfold hazard.
  apply Rsum_judges_lower; [exact Hrad | |].
  - apply Rdiv_nonneg; [left; apply att_kappa_pos | nra].
  - intros p Hp.
    cbv beta; unfold dist; cbn [obs_pos obs_tol].
    set (d := norm (vsub p x0)) in *.
    assert (Hd : 0 <= d) by apply norm_nonneg.
    assert (Hk := att_kappa_pos A).
    assert (Hinv : att_kappa A / (1 + rad * rad) <= att_kappa A / (1 + d * d)).
    { unfold Rdiv; apply Rmult_le_compat_l; [lra |].
      apply Rinv_le_contravar; nra. }
    assert (Hatt := att_inverse_square A d Hd).
    unfold Rdiv in *; rewrite Rinv_mult.
    assert (0 < / tol) by (apply Rinv_0_lt_compat; exact tol_pos).
    rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r; [lra |].
    lra.
Qed.

(** For rad >= max 1 (2 res) the hazard is at least kappa * rad / (16 res^3 tol): the cubic count against inverse-square attenuation. *)
Theorem hazard_lower_bound : forall A x0 rad,
  1 <= rad -> 2 * res <= rad ->
  att_kappa A * rad / (16 * (res * res * res) * tol) <= hazard A x0 rad.
Proof.
  intros A x0 rad Hrad1 Hrad2.
  assert (Hrad : 0 <= rad) by lra.
  assert (H := hazard_lower_cube A x0 rad Hrad).
  set (M := INR (2 * cube_size rad + 1)) in *.
  assert (Hk := att_kappa_pos A).
  destruct (cube_size_bounds rad Hrad) as [Hm _].
  assert (HM : rad / (2 * res) <= M).
  { unfold M. rewrite plus_INR, mult_INR. simpl INR.
    assert (E : rad / res = 2 * (rad / (2 * res))) by (field; lra).
    assert (Hge1 : 1 <= rad / (2 * res)).
    { apply Rmult_le_reg_r with (2 * res); [lra |].
      unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra. }
    lra. }
  set (rho := rad / (2 * res)) in *.
  assert (Hrho : 0 < rho) by (unfold rho; apply Rdiv_lt_0_compat; lra).
  assert (HMpos : 0 <= M) by lra.
  assert (HM3 : rho * rho * rho <= M * M * M).
  { apply Rle_trans with (rho * rho * M).
    - apply Rmult_le_compat_l; [nra | exact HM].
    - apply Rle_trans with (rho * M * M).
      + replace (rho * rho * M) with (rho * M * rho) by ring.
        apply Rmult_le_compat_l; [nra | exact HM].
      + replace (rho * M * M) with (M * M * rho) by ring.
        apply Rmult_le_compat_l; [nra | exact HM]. }
  assert (Hrr : 0 < 2 * rad * rad * tol).
  { apply Rmult_lt_0_compat; [nra | exact tol_pos]. }
  assert (Hden : att_kappa A / (2 * rad * rad * tol) <= att_kappa A / ((1 + rad * rad) * tol)).
  { unfold Rdiv; apply Rmult_le_compat_l; [lra |].
    apply Rinv_le_contravar; [nra |].
    apply Rmult_le_compat_r; [lra | nra]. }
  assert (Hpos : 0 <= att_kappa A / (2 * rad * rad * tol)).
  { apply Rdiv_nonneg; [lra | exact Hrr]. }
  assert (Hfin : att_kappa A * rad / (16 * (res * res * res) * tol)
                 = rho * rho * rho * (att_kappa A / (2 * rad * rad * tol))).
  { unfold rho; field; repeat split; lra. }
  rewrite Hfin.
  apply Rle_trans with (M * M * M * (att_kappa A / (2 * rad * rad * tol))).
  { apply Rmult_le_compat_r; [exact Hpos | exact HM3]. }
  apply Rle_trans with (M * M * M * (att_kappa A / ((1 + rad * rad) * tol))); [| exact H].
  apply Rmult_le_compat_l; [| exact Hden].
  apply Rmult_le_pos; [apply Rmult_le_pos; exact HMpos || exact HMpos | exact HMpos].
Qed.


Lemma horizon_radius_nonneg : forall T, 0 <= T -> 0 <= horizon_radius T.
Proof. intros T HT; unfold horizon_radius; apply Rdiv_nonneg; nra. Qed.

Definition discount (r : R) (o : Observer) (x0 : Vec3) : R :=
  exp (- r * (2 * dist o x0 / c)).

Lemma discount_bounds : forall r o x0, 0 <= r -> 0 < discount r o x0 <= 1.
Proof.
  intros r o x0 Hr; unfold discount; split; [apply exp_pos | apply exp_le_1].
  assert (Hd := dist_nonneg o x0).
  assert (0 <= 2 * dist o x0 / c) by (apply Rdiv_nonneg; lra).
  nra.
Qed.

Lemma discount_zero : forall o x0, discount 0 o x0 = 1.
Proof. intros; unfold discount; replace (- 0 * (2 * dist o x0 / c)) with 0 by ring; apply exp_0. Qed.

(** The per-axis decay factor of the discount across one lattice step. *)
Definition decay (r : R) : R := exp (- (2 * r * res / (c * sqrt 3))).

Lemma decay_bounds : forall r, 0 < r -> 0 < decay r < 1.
Proof.
  intros r Hr; unfold decay; split; [apply exp_pos | apply exp_lt_1].
  assert (0 < 2 * r * res / (c * sqrt 3)).
  { apply Rdiv_lt_0_compat; [nra | apply Rmult_lt_0_compat; [exact c_pos | apply sqrt3_pos]]. }
  lra.
Qed.

Lemma exp_neg_INR : forall mu k, exp (- mu * INR k) = exp (- mu) ^ k.
Proof.
  intros mu k; induction k as [| k IH].
  - simpl; rewrite Rmult_0_r, exp_0; reflexivity.
  - rewrite S_INR; replace (- mu * (INR k + 1)) with (- mu * INR k + - mu) by ring.
    rewrite exp_plus, IH; simpl; ring.
Qed.

Lemma Rabs_IZR_ndist : forall i n, Rabs (IZR (Z.of_nat i - Z.of_nat n)) = INR (ndist i n).
Proof.
  intros i n; rewrite minus_IZR, <- !INR_IZR_INZ.
  destruct (le_lt_dec n i) as [H | H].
  - rewrite Rabs_right by (assert (Hle := le_INR _ _ H); lra).
    rewrite ndist_ge by exact H. rewrite minus_INR by exact H; reflexivity.
  - rewrite Rabs_left by (assert (Hlt := lt_INR _ _ H); lra).
    rewrite ndist_le by lia. rewrite minus_INR by lia; ring.
Qed.

Lemma discount_lattice_le : forall r x0 n i j k, 0 < r ->
  discount r (mkObserver (lattice_point x0 n i j k) tol tol_pos) x0 <=
  decay r ^ ndist i n * decay r ^ ndist j n * decay r ^ ndist k n.
Proof.
  intros r x0 n i j k Hr.
  unfold discount, dist, decay; cbn [obs_pos].
  rewrite lattice_point_dist.
  set (a := IZR (Z.of_nat i - Z.of_nat n)).
  set (b := IZR (Z.of_nat j - Z.of_nat n)).
  set (d := IZR (Z.of_nat k - Z.of_nat n)).
  set (mu := 2 * r * res / (c * sqrt 3)).
  rewrite <- !exp_neg_INR, <- !exp_plus.
  apply exp_le_compat.
  rewrite <- !Rabs_IZR_ndist. fold a b d.
  assert (HL := l1_le_sqrt3_norm a b d).
  assert (Hs3 := sqrt3_pos).
  assert (Hmu : 0 <= mu).
  { unfold mu; apply Rdiv_nonneg; [nra | apply Rmult_lt_0_compat; [exact c_pos | exact Hs3]]. }
  assert (Hstep : mu * (Rabs a + Rabs b + Rabs d) <= mu * (sqrt 3 * norm (a, b, d)))
    by (apply Rmult_le_compat_l; assumption).
  assert (Heq : mu * (sqrt 3 * norm (a, b, d)) = r * (2 * (res * norm (a, b, d)) / c))
    by (unfold mu; field; lra).
  lra.
Qed.

Lemma discount_sum_le : forall r x0 rad, 0 < r ->
  Rsum (fun o => discount r o x0) (judges x0 rad) <=
  8 / ((1 - decay r) * (1 - decay r) * (1 - decay r)).
Proof.
  intros r x0 rad Hr.
  rewrite Rsum_judges.
  set (n := grid_size rad). set (L := seq 0 (2 * n + 1)). set (q := decay r).
  destruct (decay_bounds r Hr) as [Hq0 Hq1]. fold q in Hq0, Hq1.
  set (G := Rsum (fun i => q ^ ndist i n) L).
  assert (HG : G <= 2 / (1 - q)) by (unfold G, L; apply two_sided_geometric_bound; split; lra).
  assert (HG0 : 0 <= G) by (unfold G; apply Rsum_nonneg; intros i _; apply pow_le; lra).
  apply Rle_trans with
    (Rsum (fun i => Rsum (fun j => Rsum (fun k => q ^ ndist i n * q ^ ndist j n * q ^ ndist k n) L) L) L).
  - apply Rsum_le; intros i _; apply Rsum_le; intros j _; apply Rsum_le; intros k _.
    destruct (in_ball x0 rad (lattice_point x0 n i j k)).
    + apply discount_lattice_le; exact Hr.
    + repeat apply Rmult_le_pos; apply pow_le; lra.
  - assert (E : Rsum (fun i => Rsum (fun j => Rsum (fun k =>
                  q ^ ndist i n * q ^ ndist j n * q ^ ndist k n) L) L) L = G * G * G).
    { transitivity (Rsum (fun i => Rsum (fun j => q ^ ndist i n * q ^ ndist j n * G) L) L).
      { apply Rsum_ext; intros i _; apply Rsum_ext; intros j _.
        unfold G; rewrite <- Rsum_scal_l; reflexivity. }
      transitivity (Rsum (fun i => q ^ ndist i n * G * G) L).
      { apply Rsum_ext; intros i _.
        rewrite (Rsum_ext _ (fun j => (q ^ ndist i n * G) * q ^ ndist j n)) by (intros j _; ring).
        rewrite Rsum_scal_l; fold G; reflexivity. }
      rewrite (Rsum_ext _ (fun i => (G * G) * q ^ ndist i n)) by (intros i _; ring).
      rewrite Rsum_scal_l; fold G; ring. }
    rewrite E.
    assert (H1q : 0 < 1 - q) by lra.
    replace (8 / ((1 - q) * (1 - q) * (1 - q)))
      with ((2 / (1 - q)) * (2 / (1 - q)) * (2 / (1 - q))) by (field; lra).
    apply cube_le; split; assumption.
Qed.

(** * Section 9: A larger radius admits every judge of a smaller one, so the count and the hazard are monotone in the radius. *)

Lemma grid_size_monotone : forall rad1 rad2,
  0 <= rad1 <= rad2 -> (grid_size rad1 <= grid_size rad2)%nat.
Proof.
  intros rad1 rad2 [H0 H]; unfold grid_size.
  apply Z2Nat.inj_le; [apply up_nonneg; apply Rdiv_nonneg; lra | apply up_nonneg; apply Rdiv_nonneg; lra |].
  apply up_monotone.
  unfold Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact res_pos | exact H].
Qed.

Lemma lattice_point_shift : forall x0 n1 n2 i j k, (n1 <= n2)%nat ->
  lattice_point x0 n2 (i + (n2 - n1)) (j + (n2 - n1)) (k + (n2 - n1)) = lattice_point x0 n1 i j k.
Proof.
  intros x0 n1 n2 i j k Hn; unfold lattice_point.
  assert (E1 : (Z.of_nat (i + (n2 - n1)) - Z.of_nat n2)%Z = (Z.of_nat i - Z.of_nat n1)%Z) by lia.
  assert (E2 : (Z.of_nat (j + (n2 - n1)) - Z.of_nat n2)%Z = (Z.of_nat j - Z.of_nat n1)%Z) by lia.
  assert (E3 : (Z.of_nat (k + (n2 - n1)) - Z.of_nat n2)%Z = (Z.of_nat k - Z.of_nat n1)%Z) by lia.
  rewrite E1, E2, E3; reflexivity.
Qed.

Lemma Rsum_judges_monotone : forall (F : Observer -> R) x0 rad1 rad2,
  0 <= rad1 <= rad2 -> (forall o, 0 <= F o) ->
  Rsum F (judges x0 rad1) <= Rsum F (judges x0 rad2).
Proof.
  intros F x0 rad1 rad2 [H0 H12] HF.
  rewrite !Rsum_judges.
  set (n1 := grid_size rad1). set (n2 := grid_size rad2).
  assert (Hn : (n1 <= n2)%nat) by (apply grid_size_monotone; split; assumption).
  set (term2 := fun i j k =>
    if in_ball x0 rad2 (lattice_point x0 n2 i j k)
    then F (mkObserver (lattice_point x0 n2 i j k) tol tol_pos) else 0).
  assert (Hnn : forall i j k, 0 <= term2 i j k).
  { intros i j k; unfold term2; destruct (in_ball x0 rad2 (lattice_point x0 n2 i j k)); [apply HF | lra]. }
  assert (Hlen : (n2 - n1 + (2 * n1 + 1) <= 2 * n2 + 1)%nat) by lia.
  assert (Hpt : forall i j k,
    (if in_ball x0 rad1 (lattice_point x0 n1 i j k)
     then F (mkObserver (lattice_point x0 n1 i j k) tol tol_pos) else 0)
    <= term2 (i + (n2 - n1))%nat (j + (n2 - n1))%nat (k + (n2 - n1))%nat).
  { intros i j k; unfold term2; rewrite (lattice_point_shift x0 n1 n2 i j k Hn).
    destruct (in_ball x0 rad1 (lattice_point x0 n1 i j k)) eqn:E1.
    - assert (E2 : in_ball x0 rad2 (lattice_point x0 n1 i j k) = true).
      { apply in_ball_true; apply Rle_trans with rad1; [apply in_ball_true; exact E1 | exact H12]. }
      rewrite E2; apply Rle_refl.
    - destruct (in_ball x0 rad2 (lattice_point x0 n1 i j k)); [apply HF | lra]. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k =>
    term2 (i + (n2 - n1))%nat (j + (n2 - n1))%nat (k + (n2 - n1))%nat)
    (seq 0 (2 * n1 + 1))) (seq 0 (2 * n1 + 1))) (seq 0 (2 * n1 + 1))).
  { apply Rsum_le; intros i _; apply Rsum_le; intros j _; apply Rsum_le; intros k _; apply Hpt. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k =>
    term2 (i + (n2 - n1))%nat (j + (n2 - n1))%nat k)
    (seq 0 (2 * n2 + 1))) (seq 0 (2 * n1 + 1))) (seq 0 (2 * n1 + 1))).
  { apply Rsum_le; intros i _; apply Rsum_le; intros j _.
    apply (Rsum_seq_shift_sub (fun k => term2 (i + (n2 - n1))%nat (j + (n2 - n1))%nat k)
             (n2 - n1)%nat (2 * n1 + 1)%nat (2 * n2 + 1)%nat Hlen).
    intros k _; apply Hnn. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k =>
    term2 (i + (n2 - n1))%nat j k)
    (seq 0 (2 * n2 + 1))) (seq 0 (2 * n2 + 1))) (seq 0 (2 * n1 + 1))).
  { apply Rsum_le; intros i _.
    apply (Rsum_seq_shift_sub (fun j => Rsum (fun k => term2 (i + (n2 - n1))%nat j k) (seq 0 (2 * n2 + 1)))
             (n2 - n1)%nat (2 * n1 + 1)%nat (2 * n2 + 1)%nat Hlen).
    intros j _; apply Rsum_nonneg; intros k _; apply Hnn. }
  apply (Rsum_seq_shift_sub (fun i => Rsum (fun j => Rsum (fun k => term2 i j k) (seq 0 (2 * n2 + 1)))
                                       (seq 0 (2 * n2 + 1)))
           (n2 - n1)%nat (2 * n1 + 1)%nat (2 * n2 + 1)%nat Hlen).
  intros i _; apply Rsum_nonneg; intros j _; apply Rsum_nonneg; intros k _; apply Hnn.
Qed.

Theorem judges_count_monotone : forall x0 rad1 rad2,
  0 <= rad1 <= rad2 -> (length (judges x0 rad1) <= length (judges x0 rad2))%nat.
Proof.
  intros x0 rad1 rad2 H.
  assert (Hs := Rsum_judges_monotone (fun _ => 1) x0 rad1 rad2 H (fun _ => Rle_0_1)).
  rewrite !Rsum_const in Hs.
  apply INR_le; lra.
Qed.

Theorem hazard_monotone : forall (A : Attenuation) x0 rad1 rad2,
  0 <= rad1 <= rad2 -> hazard A x0 rad1 <= hazard A x0 rad2.
Proof.
  intros A x0 rad1 rad2 H; unfold hazard; apply Rsum_judges_monotone; [exact H |].
  intros o; apply Rdiv_nonneg; [left; apply att_pos, dist_nonneg | apply obs_tol_pos].
Qed.

End Geometry.

(** Three attenuation laws: flat, inverse square, and inverse linear with constant 1 / 2. *)

Definition flat_attenuation : Attenuation.
Proof.
  refine (mkAttenuation (fun _ => 1) 1 Rlt_0_1 _ _ _).
  - intros d _; lra.
  - intros d _; lra.
  - intros d Hd; unfold Rdiv; rewrite Rmult_1_l.
    apply Rle_trans with (/ 1); [apply Rinv_le_contravar; nra | rewrite Rinv_1; lra].
Defined.

Definition inverse_square_attenuation : Attenuation.
Proof.
  refine (mkAttenuation (fun d => 1 / (1 + d * d)) 1 Rlt_0_1 _ _ _).
  - intros d Hd; apply Rdiv_lt_0_compat; nra.
  - intros d Hd; unfold Rdiv; rewrite Rmult_1_l.
    apply Rle_trans with (/ 1); [apply Rinv_le_contravar; nra | rewrite Rinv_1; lra].
  - intros d Hd; apply Rle_refl.
Defined.

Definition inverse_linear_attenuation : Attenuation.
Proof.
  refine (mkAttenuation (fun d => 1 / (1 + d)) (/ 2) _ _ _ _).
  - apply Rinv_0_lt_compat; lra.
  - intros d Hd; apply Rdiv_lt_0_compat; lra.
  - intros d Hd; unfold Rdiv; rewrite Rmult_1_l.
    apply Rle_trans with (/ 1); [apply Rinv_le_contravar; lra | rewrite Rinv_1; lra].
  - intros d Hd.
    assert (H1 : 0 < 1 + d * d) by nra.
    assert (H2 : 0 < 1 + d) by lra.
    unfold Rdiv.
    apply Rmult_le_reg_r with ((1 + d * d) * (1 + d)); [nra |].
    replace (/ 2 * / (1 + d * d) * ((1 + d * d) * (1 + d))) with ((1 + d) * / 2) by (field; lra).
    replace (1 * / (1 + d) * ((1 + d * d) * (1 + d))) with (1 + d * d) by (field; lra).
    assert (S := Rle_0_sqr (d - / 4)); unfold Rsqr in S.
    lra.
Defined.
