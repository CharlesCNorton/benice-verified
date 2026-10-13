(** Physical instantiation: the SI speed of light, judges at the stellar density of the solar neighbourhood or at the density of bright galaxies, inverse-square attenuation on the scale of the judge spacing, destruction in units of tolerance; the depths come out in years. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.
From BeNice Require Import Vectors Actions Sums LightCone Survival Resources.

(** Metres per second, exact by the definition of the metre. *)
Definition c_SI : R := 299792458.

(** Metres per parsec: 648000 / pi astronomical units of 149597870700 m, to the metre. *)
Definition parsec : R := 30856775814913673.

(** Seconds per Julian year. *)
Definition year : R := 31557600.

(** Metres between neighbouring judges at one judge per ten cubic parsecs, the stellar density within ten parsecs of the Sun: the cube root of ten parsecs, to the metre. *)
Definition stellar_spacing : R := 66477837815650017.

(** Metres between neighbouring judges at one judge per hundred cubic megaparsecs, the density of bright galaxies: the cube root of a hundred megaparsecs, to the metre. *)
Definition galactic_spacing : R := 143224466063796132118528.

Lemma a_le_div : forall a b n, 0 < n -> a * n <= b -> a <= b / n.
Proof.
  intros a b n Hn H; apply Rmult_le_reg_r with n; [exact Hn |].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra; exact H.
Qed.

Lemma div_le_a : forall a b n, 0 < n -> b <= a * n -> b / n <= a.
Proof.
  intros a b n Hn H; apply Rmult_le_reg_r with n; [exact Hn |].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra; exact H.
Qed.

Lemma div_lt_a : forall a b n, 0 < n -> b < a * n -> b / n < a.
Proof.
  intros a b n Hn H; apply Rmult_lt_reg_r with n; [exact Hn |].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra; exact H.
Qed.

Section Scale.

(** The judge spacing in metres is the unit of length and the attenuation scale. *)
Variable spacing : R.
Hypothesis spacing_pos : 0 < spacing.

(** The speed of light in spacings per second. *)
Definition c_u : R := c_SI / spacing.

Lemma c_u_pos : 0 < c_u.
Proof. unfold c_u, c_SI; apply Rdiv_lt_0_compat; lra. Qed.

Definition res_u : R := 1.
Definition tol_u : R := 1.

Lemma res_u_pos : 0 < res_u.
Proof. unfold res_u; lra. Qed.

Lemma tol_u_pos : 0 < tol_u.
Proof. unfold tol_u; lra. Qed.

Definition depth_min : R := T_min c_u res_u.
Definition hazard_rate : R := rate c_u res_u tol_u inverse_square_attenuation.

(** The minimal depth is four light-crossings of the spacing. *)
Lemma depth_min_eq : depth_min = 4 * spacing / c_SI.
Proof.
  unfold depth_min, T_min, res_u.
  rewrite Rmax_right.
  - unfold c_u; field; repeat split; unfold c_SI; lra.
  - unfold Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; apply c_u_pos | lra].
Qed.

(** The hazard rate per unit destruction is c / (32 spacing) per second. *)
Lemma hazard_rate_eq : hazard_rate = c_SI / (32 * spacing).
Proof.
  unfold hazard_rate, rate, res_u, tol_u, c_u; simpl (att_kappa inverse_square_attenuation).
  field; repeat split; unfold c_SI; lra.
Qed.

Lemma hazard_rate_pos : 0 < hazard_rate.
Proof. apply (rate_pos c_u c_u_pos res_u res_u_pos tol_u tol_u_pos inverse_square_attenuation). Qed.

Theorem physical_survival_bound : forall s0 x0 a T,
  depth_min <= T ->
  survival c_u res_u tol_u tol_u_pos inverse_square_attenuation Action (destr s0) a x0 T <=
  exp (- destruction a s0 * hazard_rate * T).
Proof.
  intros s0 x0 a T HT.
  apply (destruction_survival_rate c_u c_u_pos res_u res_u_pos tol_u tol_u_pos inverse_square_attenuation s0 a x0 T HT).
Qed.

(** An act destroying at least one tolerance unit survives with probability at most one half once the horizon exceeds the minimal depth and the reciprocal hazard rate. *)
Theorem physical_half : forall s0 x0 a T,
  1 <= destruction a s0 -> depth_min <= T -> 1 <= hazard_rate * T ->
  survival c_u res_u tol_u tol_u_pos inverse_square_attenuation Action (destr s0) a x0 T <= 1 / 2.
Proof.
  intros s0 x0 a T Hd HT Hr.
  apply Rle_trans with (exp (- destruction a s0 * hazard_rate * T)); [apply physical_survival_bound; exact HT |].
  apply Rle_trans with (exp (- 1)).
  - apply exp_le_compat.
    assert (Hr0 := hazard_rate_pos).
    assert (Hm : 1 * (hazard_rate * T) <= destruction a s0 * (hazard_rate * T)) by (apply Rmult_le_compat_r; lra).
    lra.
  - assert (He := exp_ineq1_le 1).
    assert (Hprod : exp (- 1) * exp 1 = 1).
    { rewrite <- exp_plus; replace (- 1 + 1) with 0 by ring; apply exp_0. }
    assert (Hpos := exp_pos (- 1)).
    apply Rmult_le_reg_r with 2; [lra |].
    replace (1 / 2 * 2) with 1 by field.
    nra.
Qed.

(** Preservation overtakes any act destroying at least one tolerance unit for at most an e-fold benefit once the horizon exceeds the minimal depth and the reciprocal hazard rate. *)
Theorem physical_crossover : forall s0 x0 (benefit : Action -> R) p a T,
  preserving_at p s0 -> 0 < benefit p -> 1 <= destruction a s0 -> benefit a <= exp 1 * benefit p ->
  depth_min < T -> 1 < hazard_rate * T ->
  utility c_u res_u tol_u tol_u_pos inverse_square_attenuation Action (destr s0) benefit a x0 T <
  utility c_u res_u tol_u tol_u_pos inverse_square_attenuation Action (destr s0) benefit p x0 T.
Proof.
  intros s0 x0 benefit p a T Hp Hbp Hd HB HT Hr.
  apply (uniform_crossover c_u c_u_pos res_u res_u_pos tol_u tol_u_pos inverse_square_attenuation Action (destr s0)
           (destr_nonneg s0) benefit x0 p 1 (exp 1 * benefit p));
    [apply destr_zero_iff; exact Hp | exact Hbp | lra | | exact Hd | exact HB].
  unfold crossover_depth; apply Rmax_lub_lt; [exact HT |].
  replace (exp 1 * benefit p / benefit p) with (exp 1) by (field; lra).
  rewrite Rmax_left by (assert (He := exp_ineq1_le 1); lra).
  rewrite ln_exp, Rmult_1_l.
  fold hazard_rate.
  apply div_lt_a; [apply hazard_rate_pos | lra].
Qed.

(** With presence credence q per site, the crossover depth is the larger of the minimal depth and (1 + delta) ln(B / bp) / (q delta hazard_rate). *)
Theorem physical_presence_depth : forall q delta B bp,
  crossover_depth_w c_u res_u tol_u inverse_square_attenuation q delta B bp =
  Rmax depth_min ((1 + delta) * ln (Rmax (B / bp) 1) / (q * delta * hazard_rate)).
Proof.
  intros q delta B bp; unfold crossover_depth_w, depth_min, hazard_rate, tol_u.
  replace (delta / 1) with delta by field.
  reflexivity.
Qed.

End Scale.

(** ** The stellar neighbourhood: one judge per ten cubic parsecs. *)

Lemma stellar_spacing_pos : 0 < stellar_spacing.
Proof. unfold stellar_spacing; lra. Qed.

Definition stellar_depth_min : R := depth_min stellar_spacing.
Definition stellar_rate : R := hazard_rate stellar_spacing.

(** The minimal depth lies between 28 and 29 years. *)
Theorem stellar_depth_min_bounds : 28 * year <= stellar_depth_min <= 29 * year.
Proof.
  unfold stellar_depth_min; rewrite (depth_min_eq stellar_spacing stellar_spacing_pos).
  unfold stellar_spacing, c_SI, year.
  split; [apply a_le_div | apply div_le_a]; lra.
Qed.

(** The hazard rate per unit destruction lies between 1.409e-10 and 1.41e-10 per second. *)
Theorem stellar_rate_bounds : 1409 / 10000000000000 <= stellar_rate <= 141 / 1000000000000.
Proof.
  unfold stellar_rate; rewrite (hazard_rate_eq stellar_spacing stellar_spacing_pos).
  unfold stellar_spacing, c_SI.
  split; [apply a_le_div | apply div_le_a]; lra.
Qed.

(** Beyond 230 years of horizon, an act destroying one tolerance unit survives with probability at most one half. *)
Theorem stellar_half_life : forall s0 x0 a T,
  1 <= destruction a s0 -> 230 * year <= T ->
  survival (c_u stellar_spacing) res_u tol_u tol_u_pos inverse_square_attenuation Action (destr s0) a x0 T <= 1 / 2.
Proof.
  intros s0 x0 a T Hd HT.
  assert (Hb := stellar_depth_min_bounds); unfold stellar_depth_min in Hb.
  assert (Hr := stellar_rate_bounds); unfold stellar_rate in Hr.
  apply (physical_half stellar_spacing stellar_spacing_pos s0 x0 a T Hd).
  - unfold year in *; lra.
  - apply Rle_trans with (1409 / 10000000000000 * (230 * year)); [unfold year; lra |].
    apply Rmult_le_compat; [lra | unfold year; lra | lra | exact HT].
Qed.

(** Beyond 230 years of horizon, preservation overtakes any act destroying one tolerance unit for at most an e-fold benefit. *)
Theorem stellar_crossover : forall s0 x0 (benefit : Action -> R) p a T,
  preserving_at p s0 -> 0 < benefit p -> 1 <= destruction a s0 -> benefit a <= exp 1 * benefit p ->
  230 * year < T ->
  utility (c_u stellar_spacing) res_u tol_u tol_u_pos inverse_square_attenuation Action (destr s0) benefit a x0 T <
  utility (c_u stellar_spacing) res_u tol_u tol_u_pos inverse_square_attenuation Action (destr s0) benefit p x0 T.
Proof.
  intros s0 x0 benefit p a T Hp Hbp Hd HB HT.
  assert (Hb := stellar_depth_min_bounds); unfold stellar_depth_min in Hb.
  assert (Hr := stellar_rate_bounds); unfold stellar_rate in Hr.
  apply (physical_crossover stellar_spacing stellar_spacing_pos s0 x0 benefit p a T Hp Hbp Hd HB).
  - unfold year in *; lra.
  - apply Rle_lt_trans with (1409 / 10000000000000 * (230 * year)); [unfold year; lra |].
    apply Rle_lt_trans with (hazard_rate stellar_spacing * (230 * year)).
    + apply Rmult_le_compat_r; [unfold year; lra | lra].
    + apply Rmult_lt_compat_l; [apply (hazard_rate_pos stellar_spacing stellar_spacing_pos) | exact HT].
Qed.

(** At one judge in a million stars, the crossover for a unit destruction and an e-fold benefit lies within 450 million years. *)
Theorem stellar_presence_example : forall bp, 0 < bp ->
  crossover_depth_w (c_u stellar_spacing) res_u tol_u inverse_square_attenuation (1 / 1000000) 1 (exp 1 * bp) bp
  <= 450000000 * year.
Proof.
  intros bp Hbp.
  rewrite (physical_presence_depth stellar_spacing).
  assert (Hb := stellar_depth_min_bounds); unfold stellar_depth_min in Hb.
  assert (Hr := stellar_rate_bounds); unfold stellar_rate in Hr.
  apply Rmax_lub; [unfold year in *; lra |].
  replace (exp 1 * bp / bp) with (exp 1) by (field; lra).
  rewrite Rmax_left by (assert (He := exp_ineq1_le 1); lra).
  rewrite ln_exp.
  apply div_le_a; [lra |].
  unfold year in *; lra.
Qed.

(** ** Bright galaxies: one judge per hundred cubic megaparsecs. *)

Lemma galactic_spacing_pos : 0 < galactic_spacing.
Proof. unfold galactic_spacing; lra. Qed.

Definition galactic_depth_min : R := depth_min galactic_spacing.
Definition galactic_rate : R := hazard_rate galactic_spacing.

(** The minimal depth lies between 60 and 62 million years. *)
Theorem galactic_depth_min_bounds : 60000000 * year <= galactic_depth_min <= 62000000 * year.
Proof.
  unfold galactic_depth_min; rewrite (depth_min_eq galactic_spacing galactic_spacing_pos).
  unfold galactic_spacing, c_SI, year.
  split; [apply a_le_div | apply div_le_a]; lra.
Qed.

(** The hazard rate per unit destruction lies between 6.5e-17 and 6.6e-17 per second. *)
Theorem galactic_rate_bounds : 65 / 1000000000000000000 <= galactic_rate <= 66 / 1000000000000000000.
Proof.
  unfold galactic_rate; rewrite (hazard_rate_eq galactic_spacing galactic_spacing_pos).
  unfold galactic_spacing, c_SI.
  split; [apply a_le_div | apply div_le_a]; lra.
Qed.

(** Beyond 500 million years of horizon, preservation overtakes any act destroying one tolerance unit for at most an e-fold benefit. *)
Theorem galactic_crossover : forall s0 x0 (benefit : Action -> R) p a T,
  preserving_at p s0 -> 0 < benefit p -> 1 <= destruction a s0 -> benefit a <= exp 1 * benefit p ->
  500000000 * year < T ->
  utility (c_u galactic_spacing) res_u tol_u tol_u_pos inverse_square_attenuation Action (destr s0) benefit a x0 T <
  utility (c_u galactic_spacing) res_u tol_u tol_u_pos inverse_square_attenuation Action (destr s0) benefit p x0 T.
Proof.
  intros s0 x0 benefit p a T Hp Hbp Hd HB HT.
  assert (Hb := galactic_depth_min_bounds); unfold galactic_depth_min in Hb.
  assert (Hr := galactic_rate_bounds); unfold galactic_rate in Hr.
  apply (physical_crossover galactic_spacing galactic_spacing_pos s0 x0 benefit p a T Hp Hbp Hd HB).
  - unfold year in *; lra.
  - apply Rle_lt_trans with (65 / 1000000000000000000 * (500000000 * year)); [unfold year; lra |].
    apply Rle_lt_trans with (hazard_rate galactic_spacing * (500000000 * year)).
    + apply Rmult_le_compat_r; [unfold year; lra | lra].
    + apply Rmult_lt_compat_l; [apply (hazard_rate_pos galactic_spacing galactic_spacing_pos) | exact HT].
Qed.
