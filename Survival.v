(** Elimination and survival, the closed form, the rate of convergence, utility and the crossover depth, time preference and weighted survival. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.
From BeNice Require Import Vectors Actions Sums LightCone.

(** * Section 5: Elimination has the Poisson form 1 - exp(- signal / tolerance) with the signal the attenuated offense, a non-negative functional of the option, and survival is the product over the judges within the horizon. *)


Section Model.

Variable c : R.
Hypothesis c_pos : 0 < c.
Variable res : R.
Hypothesis res_pos : 0 < res.
Variable tol : R.
Hypothesis tol_pos : 0 < tol.

Variable A : Attenuation.

(** The options form an arbitrary type, instantiated with actions in Resources and with verdicts in Judges. *)
Variable Act : Type.

Variable offense : Act -> R.
Hypothesis offense_nonneg : forall a, 0 <= offense a.

(** Local abbreviations supplying the geometric parameters. *)
Notation judges := (LightCone.judges res tol tol_pos).
Notation hazard := (LightCone.hazard res tol tol_pos).
Notation horizon_radius := (LightCone.horizon_radius c).
Notation horizon_radius_nonneg := (LightCone.horizon_radius_nonneg c c_pos).
Notation judges_nonempty := (LightCone.judges_nonempty res res_pos tol tol_pos).
Notation judges_tol := (LightCone.judges_tol res tol tol_pos).
Notation hazard_nonneg := (LightCone.hazard_nonneg res tol tol_pos).
Notation hazard_lower_bound := (LightCone.hazard_lower_bound res res_pos tol tol_pos).
Notation hazard_monotone := (LightCone.hazard_monotone res res_pos tol tol_pos).
Notation Rsum_judges := (LightCone.Rsum_judges res tol tol_pos).
Notation discount := (LightCone.discount c).
Notation discount_bounds := (LightCone.discount_bounds c c_pos).
Notation discount_zero := (LightCone.discount_zero c).
Notation decay := (LightCone.decay c res).
Notation decay_bounds := (LightCone.decay_bounds c c_pos res res_pos).
Notation discount_sum_le := (LightCone.discount_sum_le c c_pos res res_pos tol tol_pos).

Definition signal (a : Act) (o : Observer) (x0 : Vec3) : R :=
  offense a * att A (dist o x0) / obs_tol o.

Lemma signal_nonneg : forall a o x0, 0 <= signal a o x0.
Proof.
  intros; unfold signal; apply Rdiv_nonneg; [| apply obs_tol_pos].
  apply Rmult_le_pos; [apply offense_nonneg | left; apply att_pos, dist_nonneg].
Qed.

Lemma signal_zero : forall a o x0, offense a = 0 -> signal a o x0 = 0.
Proof. intros a o x0 H; unfold signal; rewrite H; unfold Rdiv; ring. Qed.

Lemma signal_pos : forall a o x0, 0 < offense a -> 0 < signal a o x0.
Proof.
  intros a o x0 H; unfold signal; apply Rdiv_lt_0_compat; [| apply obs_tol_pos].
  apply Rmult_lt_0_compat; [exact H | apply att_pos, dist_nonneg].
Qed.

Lemma signal_monotone : forall a1 a2 o x0,
  offense a1 <= offense a2 -> signal a1 o x0 <= signal a2 o x0.
Proof.
  intros a1 a2 o x0 H; unfold signal, Rdiv.
  assert (0 < att A (dist o x0)) by (apply att_pos, dist_nonneg).
  assert (0 < / obs_tol o) by (apply Rinv_0_lt_compat, obs_tol_pos).
  apply Rmult_le_compat_r; [lra |].
  apply Rmult_le_compat_r; lra.
Qed.

Definition elim_prob (a : Act) (o : Observer) (x0 : Vec3) : R :=
  1 - exp (- signal a o x0).

Lemma elim_prob_bounds : forall a o x0, 0 <= elim_prob a o x0 < 1.
Proof.
  intros a o x0; unfold elim_prob.
  assert (H := signal_nonneg a o x0).
  assert (He := exp_pos (- signal a o x0)).
  assert (He1 : exp (- signal a o x0) <= 1) by (apply exp_le_1; lra).
  lra.
Qed.

Lemma elim_prob_zero : forall a o x0, offense a = 0 -> elim_prob a o x0 = 0.
Proof. intros a o x0 H; unfold elim_prob; rewrite signal_zero by exact H; rewrite Ropp_0, exp_0; ring. Qed.

Lemma elim_prob_pos : forall a o x0, 0 < offense a -> 0 < elim_prob a o x0.
Proof.
  intros a o x0 H; unfold elim_prob.
  assert (Hs := signal_pos a o x0 H).
  assert (He : exp (- signal a o x0) < 1) by (apply exp_lt_1; lra).
  lra.
Qed.

Lemma elim_prob_monotone : forall a1 a2 o x0,
  offense a1 <= offense a2 -> elim_prob a1 o x0 <= elim_prob a2 o x0.
Proof.
  intros a1 a2 o x0 H; unfold elim_prob.
  assert (Hs := signal_monotone a1 a2 o x0 H).
  assert (He : exp (- signal a2 o x0) <= exp (- signal a1 o x0)) by (apply exp_le_compat; lra).
  lra.
Qed.

(** Survival: the judges within the horizon decide independently, so the agent survives with the product of their survival probabilities. *)
Definition survival (a : Act) (x0 : Vec3) (T : R) : R :=
  Rprod (fun o => 1 - elim_prob a o x0) (judges x0 (horizon_radius T)).

Theorem survival_closed_form : forall a x0 T,
  survival a x0 T = exp (- offense a * hazard A x0 (horizon_radius T)).
Proof.
  intros a x0 T; unfold survival, hazard.
  rewrite (Rprod_ext _ (fun o => exp ((- offense a) * (att A (dist o x0) / obs_tol o)))).
  - rewrite Rprod_exp, Rsum_scal_l; reflexivity.
  - intros o _; unfold elim_prob, signal.
    replace (1 - (1 - exp (- (offense a * att A (dist o x0) / obs_tol o))))
      with (exp (- (offense a * att A (dist o x0) / obs_tol o))) by ring.
    f_equal; unfold Rdiv; ring.
Qed.

Lemma survival_pos : forall a x0 T, 0 < survival a x0 T.
Proof. intros; rewrite survival_closed_form; apply exp_pos. Qed.

Lemma survival_le_1 : forall a x0 T, survival a x0 T <= 1.
Proof.
  intros a x0 T; rewrite survival_closed_form; apply exp_le_1.
  assert (H1 := offense_nonneg a). assert (H2 := hazard_nonneg A x0 (horizon_radius T)). nra.
Qed.

Lemma survival_of_inoffensive : forall a x0 T, offense a = 0 -> survival a x0 T = 1.
Proof.
  intros a x0 T H; rewrite survival_closed_form, H.
  replace (- 0 * hazard A x0 (horizon_radius T)) with 0 by ring.
  apply exp_0.
Qed.

Lemma survival_antitone_offense : forall a1 a2 x0 T,
  offense a1 <= offense a2 -> survival a2 x0 T <= survival a1 x0 T.
Proof.
  intros a1 a2 x0 T H; rewrite !survival_closed_form; apply exp_le_compat.
  assert (Hh := hazard_nonneg A x0 (horizon_radius T)). nra.
Qed.

Lemma survival_lt_1 : forall a x0 T, 0 < offense a -> 0 <= T -> survival a x0 T < 1.
Proof.
  intros a x0 T Ha HT; rewrite survival_closed_form; apply exp_lt_1.
  assert (Hrad : 0 <= horizon_radius T) by (unfold horizon_radius; apply Rdiv_nonneg; nra).
  assert (Hh : 0 < hazard A x0 (horizon_radius T)).
  { unfold hazard.
    destruct (judges x0 (horizon_radius T)) as [| o rest] eqn:E.
    - exfalso. assert (H1 := judges_nonempty x0 (horizon_radius T) Hrad). rewrite E in H1; simpl in H1; lia.
    - rewrite Rsum_cons.
      assert (0 < att A (dist o x0) / obs_tol o).
      { apply Rdiv_lt_0_compat; [apply att_pos, dist_nonneg | apply obs_tol_pos]. }
      assert (0 <= Rsum (fun o0 => att A (dist o0 x0) / obs_tol o0) rest).
      { apply Rsum_nonneg; intros o' _; apply Rdiv_nonneg; [left; apply att_pos, dist_nonneg | apply obs_tol_pos]. }
      lra. }
  nra.
Qed.

(** * Section 6: With horizon radius c T / 2 the hazard is at least rate * T, with rate explicit in c, res, tol and the attenuation constant. *)

Definition rate : R := att_kappa A * c / (32 * (res * res * res) * tol).

Lemma rate_pos : 0 < rate.
Proof.
  unfold rate; apply Rdiv_lt_0_compat.
  - apply Rmult_lt_0_compat; [apply att_kappa_pos | exact c_pos].
  - repeat apply Rmult_lt_0_compat; lra.
Qed.

Definition T_min : R := Rmax (2 / c) (4 * res / c).

Lemma T_min_pos : 0 < T_min.
Proof.
  unfold T_min; apply Rlt_le_trans with (2 / c); [apply Rdiv_lt_0_compat; lra | apply Rmax_l].
Qed.

Theorem hazard_horizon_lower : forall x0 T,
  T_min <= T -> rate * T <= hazard A x0 (horizon_radius T).
Proof.
  intros x0 T HT.
  assert (H1 : 2 / c <= T) by (apply Rle_trans with T_min; [apply Rmax_l | exact HT]).
  assert (H2 : 4 * res / c <= T) by (apply Rle_trans with T_min; [apply Rmax_r | exact HT]).
  assert (Hr1 : 1 <= horizon_radius T).
  { unfold horizon_radius. apply Rmult_le_reg_l with (2 / c); [apply Rdiv_lt_0_compat; lra |].
    replace (2 / c * (c * T / 2)) with T by (field; lra). rewrite Rmult_1_r. exact H1. }
  assert (Hr2 : 2 * res <= horizon_radius T).
  { unfold horizon_radius. apply Rmult_le_reg_l with (2 / c); [apply Rdiv_lt_0_compat; lra |].
    replace (2 / c * (c * T / 2)) with T by (field; lra).
    replace (2 / c * (2 * res)) with (4 * res / c) by (field; lra). exact H2. }
  assert (H := hazard_lower_bound A x0 (horizon_radius T) Hr1 Hr2).
  replace (rate * T) with (att_kappa A * horizon_radius T / (16 * (res * res * res) * tol)); [exact H |].
  unfold rate, horizon_radius; field; repeat split; lra.
Qed.

Theorem survival_upper_bound : forall a x0 T,
  T_min <= T -> survival a x0 T <= exp (- offense a * rate * T).
Proof.
  intros a x0 T HT; rewrite survival_closed_form; apply exp_le_compat.
  assert (H := hazard_horizon_lower x0 T HT).
  assert (Ho := offense_nonneg a).
  nra.
Qed.

(** ** Convergence: the survival of any offensive action vanishes with depth. *)

Theorem survival_vanishes : forall a x0,
  0 < offense a ->
  forall eps, 0 < eps ->
  exists T0, forall T, T0 <= T -> survival a x0 T < eps.
Proof.
  intros a x0 Ha eps Heps.
  set (P := offense a * rate).
  assert (HP : 0 < P) by (unfold P; apply Rmult_lt_0_compat; [exact Ha | apply rate_pos]).
  exists (Rmax T_min ((- ln eps) / P + 1)).
  intros T HT.
  assert (HT1 : T_min <= T) by (apply Rle_trans with (Rmax T_min ((- ln eps) / P + 1)); [apply Rmax_l | exact HT]).
  assert (HT2 : (- ln eps) / P + 1 <= T) by (apply Rle_trans with (Rmax T_min ((- ln eps) / P + 1)); [apply Rmax_r | exact HT]).
  apply Rle_lt_trans with (exp (- offense a * rate * T)); [apply survival_upper_bound; exact HT1 |].
  rewrite <- (exp_ln eps Heps).
  apply exp_increasing.
  assert (HPT : P * ((- ln eps) / P + 1) <= P * T) by (apply Rmult_le_compat_l; lra).
  replace (P * ((- ln eps) / P + 1)) with (- ln eps + P) in HPT by (field; lra).
  unfold P in HPT, HP; lra.
Qed.

Theorem survival_Un_cv : forall a x0 (Tn : nat -> R),
  0 < offense a -> cv_infty Tn ->
  Un_cv (fun n => survival a x0 (Tn n)) 0.
Proof.
  intros a x0 Tn Ha Hinf eps Heps.
  destruct (survival_vanishes a x0 Ha eps Heps) as [T0 HT0].
  destruct (Hinf T0) as [N HN].
  exists N; intros n Hn.
  unfold Rdist; rewrite Rminus_0_r, Rabs_right by (left; apply survival_pos).
  apply HT0; left; apply HN; exact Hn.
Qed.

(** * Section 7: Elimination forfeits the benefit, so utility is benefit times survival; a lucrative offensive action wins at shallow depth and loses beyond an explicit crossover depth. *)

Variable benefit : Act -> R.

Definition utility (a : Act) (x0 : Vec3) (T : R) : R := benefit a * survival a x0 T.

Lemma utility_of_inoffensive : forall a x0 T, offense a = 0 -> utility a x0 T = benefit a.
Proof. intros a x0 T H; unfold utility; rewrite survival_of_inoffensive by exact H; ring. Qed.

Definition crossover_depth (delta B bp : R) : R :=
  Rmax T_min (ln (Rmax (B / bp) 1) / (delta * rate)).

Theorem uniform_crossover : forall x0 p delta B,
  offense p = 0 -> 0 < benefit p -> 0 < delta ->
  forall T, crossover_depth delta B (benefit p) < T ->
  forall a, delta <= offense a -> benefit a <= B ->
  utility a x0 T < utility p x0 T.
Proof.
  intros x0 p delta B Hp Hbp Hdelta T HT a Ha HB.
  rewrite (utility_of_inoffensive p x0 T Hp).
  unfold utility.
  assert (HS := survival_pos a x0 T).
  assert (HS1 := survival_le_1 a x0 T).
  assert (HT1 : T_min < T) by (apply Rle_lt_trans with (crossover_depth delta B (benefit p)); [apply Rmax_l | exact HT]).
  assert (HT2 : ln (Rmax (B / benefit p) 1) / (delta * rate) < T)
    by (apply Rle_lt_trans with (crossover_depth delta B (benefit p)); [apply Rmax_r | exact HT]).
  destruct (Rle_dec (benefit a) 0) as [Hneg | Hposb].
  - nra.
  - apply Rnot_le_lt in Hposb.
    assert (HBpos : 0 < B) by lra.
    assert (Hdr : 0 < delta * rate) by (apply Rmult_lt_0_compat; [exact Hdelta | apply rate_pos]).
    assert (Hup : survival a x0 T <= exp (- delta * rate * T)).
    { apply Rle_trans with (exp (- offense a * rate * T)); [apply survival_upper_bound; lra |].
      apply exp_le_compat.
      assert (HrT : 0 < rate * T).
      { apply Rmult_lt_0_compat; [apply rate_pos | assert (H := T_min_pos); lra]. }
      assert (Hm : delta * (rate * T) <= offense a * (rate * T)) by (apply Rmult_le_compat_r; lra).
      lra. }
    assert (Hkey : exp (- delta * rate * T) < benefit p / B).
    { assert (Hbb : 0 < benefit p / B).
      { unfold Rdiv; apply Rmult_lt_0_compat; [exact Hbp | apply Rinv_0_lt_compat; exact HBpos]. }
      rewrite <- (exp_ln (benefit p / B) Hbb).
      apply exp_increasing.
      rewrite ln_div by lra.
      assert (Hln : ln (B / benefit p) <= ln (Rmax (B / benefit p) 1)).
      { apply ln_le_compat; [apply Rdiv_lt_0_compat; lra | apply Rmax_l]. }
      rewrite ln_div in Hln by lra.
      assert (Hmul : ln (Rmax (B / benefit p) 1) < delta * rate * T).
      { apply Rmult_lt_compat_r with (r := delta * rate) in HT2; [| exact Hdr].
        unfold Rdiv in HT2.
        rewrite Rmult_assoc, Rinv_l, Rmult_1_r in HT2 by lra.
        lra. }
      lra. }
    apply Rle_lt_trans with (B * survival a x0 T); [nra |].
    apply Rle_lt_trans with (B * exp (- delta * rate * T)); [nra |].
    apply Rmult_lt_reg_r with (/ B); [apply Rinv_0_lt_compat; exact HBpos |].
    replace (B * exp (- delta * rate * T) * / B) with (exp (- delta * rate * T)) by (field; lra).
    replace (benefit p * / B) with (benefit p / B) by reflexivity.
    exact Hkey.
Qed.

Definition pointwise_depth (p a : Act) : R :=
  crossover_depth (offense a) (benefit a) (benefit p).

Corollary pointwise_crossover : forall x0 p a,
  offense p = 0 -> 0 < benefit p -> 0 < offense a ->
  forall T, pointwise_depth p a < T -> utility a x0 T < utility p x0 T.
Proof.
  intros x0 p a Hp Hbp Ha T HT.
  apply (uniform_crossover x0 p (offense a) (benefit a) Hp Hbp Ha T HT a); lra.
Qed.

(** Beyond the crossover depth preservation is optimal on the class, strictly against every offensive member. *)
Theorem preservation_optimal_beyond_crossover : forall x0 p delta B,
  offense p = 0 -> 0 < benefit p -> 0 < delta ->
  forall T, crossover_depth delta B (benefit p) < T ->
  forall a, (offense a = 0 \/ delta <= offense a) -> benefit a <= benefit p \/ benefit a <= B ->
  (delta <= offense a -> benefit a <= B -> utility a x0 T < utility p x0 T) /\
  (offense a = 0 -> benefit a <= benefit p -> utility a x0 T <= utility p x0 T).
Proof.
  intros x0 p delta B Hp Hbp Hdelta T HT a _ _; split.
  - intros Ha HB; apply (uniform_crossover x0 p delta B Hp Hbp Hdelta T HT a Ha HB).
  - intros Ha HB; rewrite !utility_of_inoffensive by assumption; exact HB.
Qed.

(** ** Optimal actions converge to the inoffensive ones at rate 1 / T. *)

Theorem optimal_offense_bound : forall x0 p a B T,
  offense p = 0 -> 0 < benefit p -> benefit a <= B ->
  T_min <= T ->
  utility p x0 T <= utility a x0 T ->
  offense a * (rate * T) <= ln (B / benefit p).
Proof.
  intros x0 p a B T Hp Hbp HB HT Hopt.
  rewrite utility_of_inoffensive in Hopt by exact Hp.
  unfold utility in Hopt.
  assert (HS := survival_pos a x0 T).
  assert (HS1 := survival_le_1 a x0 T).
  assert (Hba : 0 < benefit a) by nra.
  assert (HBpos : 0 < B) by lra.
  assert (Hratio : benefit p / B <= survival a x0 T).
  { apply Rmult_le_reg_r with B; [exact HBpos |].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    nra. }
  rewrite survival_closed_form in Hratio.
  rewrite <- (exp_ln (benefit p / B)) in Hratio by (apply Rdiv_lt_0_compat; lra).
  apply exp_le_inv in Hratio.
  rewrite ln_div in Hratio by lra.
  rewrite ln_div by lra.
  assert (Hh := hazard_horizon_lower x0 T HT).
  assert (Ho := offense_nonneg a).
  assert (Hprod : offense a * (rate * T) <= offense a * hazard A x0 (horizon_radius T))
    by (apply Rmult_le_compat_l; assumption).
  lra.
Qed.

Corollary optimal_offense_le : forall x0 p a B T,
  offense p = 0 -> 0 < benefit p -> benefit a <= B ->
  T_min <= T ->
  utility p x0 T <= utility a x0 T ->
  offense a <= ln (B / benefit p) / (rate * T).
Proof.
  intros x0 p a B T Hp Hbp HB HT Hopt.
  assert (H := optimal_offense_bound x0 p a B T Hp Hbp HB HT Hopt).
  assert (HrT : 0 < rate * T).
  { apply Rmult_lt_0_compat; [apply rate_pos | assert (Hm := T_min_pos); lra]. }
  apply Rmult_le_reg_r with (rate * T); [exact HrT |].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  exact H.
Qed.

Theorem optimal_offense_vanishes : forall x0 p B,
  offense p = 0 -> 0 < benefit p ->
  forall eps, 0 < eps ->
  exists T0, forall T, T0 <= T ->
  forall a, benefit a <= B -> utility p x0 T <= utility a x0 T -> offense a < eps.
Proof.
  intros x0 p B Hp Hbp eps Heps.
  set (L := Rmax (ln (B / benefit p)) 0).
  assert (HL : 0 <= L) by apply Rmax_r.
  assert (Hr := rate_pos).
  exists (Rmax T_min (L / (rate * eps) + 1)).
  intros T HT a HB Hopt.
  assert (HT1 : T_min <= T) by (apply Rle_trans with (Rmax T_min (L / (rate * eps) + 1)); [apply Rmax_l | exact HT]).
  assert (HT2 : L / (rate * eps) + 1 <= T) by (apply Rle_trans with (Rmax T_min (L / (rate * eps) + 1)); [apply Rmax_r | exact HT]).
  assert (H := optimal_offense_bound x0 p a B T Hp Hbp HB HT1 Hopt).
  assert (Hln : ln (B / benefit p) <= L) by apply Rmax_l.
  assert (Hre : 0 < rate * eps) by (apply Rmult_lt_0_compat; assumption).
  assert (HLT : L < rate * eps * T).
  { assert (Hm : rate * eps * (L / (rate * eps) + 1) <= rate * eps * T) by (apply Rmult_le_compat_l; lra).
    replace (rate * eps * (L / (rate * eps) + 1)) with (L + rate * eps) in Hm by (field; lra).
    lra. }
  assert (Ho := offense_nonneg a).
  assert (HT0 : 0 < T) by (assert (Hm := T_min_pos); lra).
  apply Rnot_le_lt; intro Hge.
  assert (eps * (rate * T) <= offense a * (rate * T)) by (apply Rmult_le_compat_r; nra).
  nra.
Qed.

(** ** The crossover is a phase change: at any fixed depth an offensive action whose benefit exceeds the preserving benefit over its own survival wins. *)
Theorem shallow_offense_wins : forall x0 p a T,
  offense p = 0 ->
  benefit p / survival a x0 T < benefit a ->
  utility p x0 T < utility a x0 T.
Proof.
  intros x0 p a T Hp H.
  rewrite utility_of_inoffensive by exact Hp; unfold utility.
  assert (HS := survival_pos a x0 T).
  apply Rmult_lt_reg_r with (/ survival a x0 T); [apply Rinv_0_lt_compat; exact HS |].
  replace (benefit a * survival a x0 T * / survival a x0 T) with (benefit a) by (field; lra).
  exact H.
Qed.

(** ** Fixed point: on any finite menu, every optimal action is eventually inoffensive. *)

Lemma fold_Rmax_ge : forall {X : Type} (g : X -> R) base (l : list X) x,
  In x l -> g x <= fold_right Rmax base (map g l).
Proof.
  intros X g base l; induction l as [| y l IH]; intros x Hx; [destruct Hx |].
  destruct Hx as [Heq | Hin]; simpl.
  - subst; apply Rmax_l.
  - apply Rle_trans with (fold_right Rmax base (map g l)); [apply IH; exact Hin | apply Rmax_r].
Qed.

Theorem optimal_actions_are_inoffensive : forall x0 (menu : list Act) p,
  In p menu -> offense p = 0 -> 0 < benefit p ->
  exists Tstar, forall T, Tstar < T ->
    forall a, In a menu ->
    (forall a', In a' menu -> utility a' x0 T <= utility a x0 T) ->
    offense a = 0.
Proof.
  intros x0 menu p Hin Hp Hbp.
  exists (fold_right Rmax T_min (map (pointwise_depth p) menu)).
  intros T HT a Ha Hopt.
  destruct (Rle_lt_or_eq_dec 0 (offense a) (offense_nonneg a)) as [Hpos | Hzero]; [| symmetry; exact Hzero].
  exfalso.
  assert (Hd : pointwise_depth p a < T).
  { apply Rle_lt_trans with (fold_right Rmax T_min (map (pointwise_depth p) menu)); [| exact HT].
    apply (fold_Rmax_ge (pointwise_depth p) T_min menu a Ha). }
  assert (Hlt := pointwise_crossover x0 p a Hp Hbp Hpos T Hd).
  assert (Hle := Hopt p Hin).
  lra.
Qed.

(** * Section 8: A response arriving after the round trip is weighted by exp(- r 2 d / c); the discounted lattice hazard is bounded, so for a fixed rate r > 0 every discounted survival has a positive floor at every depth and a lucrative offensive action is preferred forever. *)

Definition survival_disc (r : R) (a : Act) (x0 : Vec3) (T : R) : R :=
  Rprod (fun o => 1 - discount r o x0 * elim_prob a o x0) (judges x0 (horizon_radius T)).

Lemma survival_disc_zero_rate : forall a x0 T, survival_disc 0 a x0 T = survival a x0 T.
Proof. intros; unfold survival_disc, survival; apply Rprod_ext; intros o _; rewrite discount_zero; ring. Qed.

Lemma survival_disc_of_inoffensive : forall r a x0 T, offense a = 0 -> survival_disc r a x0 T = 1.
Proof.
  intros r a x0 T H; unfold survival_disc.
  rewrite (Rprod_ext _ (fun _ => 1)); [apply Rprod_one |].
  intros o _; rewrite elim_prob_zero by exact H; ring.
Qed.

Lemma survival_le_survival_disc : forall r a x0 T, 0 <= r -> survival a x0 T <= survival_disc r a x0 T.
Proof.
  intros r a x0 T Hr; unfold survival, survival_disc; apply Rprod_le; intros o _.
  assert (He := elim_prob_bounds a o x0). assert (Hw := discount_bounds r o x0 Hr).
  split; [lra | nra].
Qed.

Lemma ratio_monotone : forall s t, 0 <= s <= t -> t < 1 -> s / (1 - s) <= t / (1 - t).
Proof.
  intros s t [Hs Hst] Ht.
  assert (H1 : 0 < 1 - t) by lra. assert (H2 : 0 < 1 - s) by lra.
  unfold Rdiv.
  apply Rmult_le_reg_r with ((1 - s) * (1 - t)); [nra |].
  replace (s * / (1 - s) * ((1 - s) * (1 - t))) with (s * (1 - t)) by (field; lra).
  replace (t * / (1 - t) * ((1 - s) * (1 - t))) with (t * (1 - s)) by (field; lra).
  nra.
Qed.

Lemma one_minus_ge_exp : forall x, 0 <= x < 1 -> exp (- (x / (1 - x))) <= 1 - x.
Proof.
  intros x [Hx0 Hx1].
  set (y := x / (1 - x)).
  assert (Hy : 0 <= y) by (unfold y; apply Rdiv_nonneg; lra).
  rewrite exp_Ropp.
  assert (H1 : 1 + y <= exp y) by apply exp_ineq1_le.
  assert (H2 : / exp y <= / (1 + y)) by (apply Rinv_le_contravar; lra).
  assert (H3 : 1 + y = / (1 - x)) by (unfold y; field; lra).
  rewrite H3, Rinv_inv in H2.
  exact H2.
Qed.

Lemma per_judge_floor : forall w e pb,
  0 <= w <= 1 -> 0 <= e <= pb -> pb < 1 ->
  exp (- (pb / (1 - pb)) * w) <= 1 - w * e.
Proof.
  intros w e pb [Hw0 Hw1] [He0 Hepb] Hpb.
  set (x := w * e).
  assert (Hx0 : 0 <= x) by (unfold x; nra).
  assert (Hxpb : x <= w * pb) by (unfold x; nra).
  assert (Hwpb : w * pb <= pb) by nra.
  assert (Hx1 : x < 1) by lra.
  apply Rle_trans with (exp (- (x / (1 - x)))); [| apply one_minus_ge_exp; split; assumption].
  apply exp_le_compat.
  assert (Hr1 : x / (1 - x) <= (w * pb) / (1 - w * pb)) by (apply ratio_monotone; [split; assumption | lra]).
  assert (Hr2 : (w * pb) / (1 - w * pb) <= (w * pb) / (1 - pb)).
  { unfold Rdiv; apply Rmult_le_compat_l; [nra |]. apply Rinv_le_contravar; lra. }
  assert (Heq : (w * pb) / (1 - pb) = (pb / (1 - pb)) * w) by (unfold Rdiv; ring).
  lra.
Qed.

Definition hazard_cap (r : R) : R := 8 / ((1 - decay r) * (1 - decay r) * (1 - decay r)).

Definition survival_floor (r : R) (a : Act) : R :=
  exp (- (exp (offense a / tol) - 1) * hazard_cap r).

Lemma survival_floor_pos : forall r a, 0 < survival_floor r a.
Proof. intros; apply exp_pos. Qed.

Theorem discounted_survival_floor : forall r a x0 T,
  0 < r -> survival_floor r a <= survival_disc r a x0 T.
Proof.
  intros r a x0 T Hr.
  set (u := offense a / tol).
  assert (Hu : 0 <= u) by (unfold u; apply Rdiv_nonneg; [apply offense_nonneg | exact tol_pos]).
  set (pb := 1 - exp (- u)).
  assert (Hpb0 : 0 <= pb) by (unfold pb; assert (exp (- u) <= 1) by (apply exp_le_1; lra); lra).
  assert (Hpb1 : pb < 1) by (unfold pb; assert (H := exp_pos (- u)); lra).
  assert (HK : pb / (1 - pb) = exp u - 1).
  { unfold pb. replace (1 - (1 - exp (- u))) with (exp (- u)) by ring.
    rewrite exp_Ropp. field. assert (H := exp_pos u); lra. }
  assert (HK0 : 0 <= exp u - 1) by (assert (H := exp_ineq1_le u); lra).
  unfold survival_disc, survival_floor; fold u.
  apply Rle_trans with
    (Rprod (fun o => exp (- (pb / (1 - pb)) * discount r o x0)) (judges x0 (horizon_radius T))).
  - rewrite Rprod_exp, Rsum_scal_l, HK.
    apply exp_le_compat.
    assert (Hsum := discount_sum_le r x0 (horizon_radius T) Hr).
    fold (hazard_cap r) in Hsum.
    nra.
  - apply Rprod_le; intros o Ho; split; [left; apply exp_pos |].
    apply per_judge_floor; [| | exact Hpb1].
    + assert (H := discount_bounds r o x0 (Rlt_le _ _ Hr)); lra.
    + split; [apply elim_prob_bounds |].
      unfold elim_prob, pb.
      assert (Hsig : signal a o x0 <= u).
      { unfold signal, u; rewrite (judges_tol _ _ _ Ho).
        assert (Hatt := att_le_1 A (dist o x0) (dist_nonneg o x0)).
        assert (Ho0 := offense_nonneg a).
        assert (0 < / tol) by (apply Rinv_0_lt_compat; exact tol_pos).
        unfold Rdiv; apply Rmult_le_compat_r; [lra | nra]. }
      assert (exp (- u) <= exp (- signal a o x0)) by (apply exp_le_compat; lra).
      lra.
Qed.

Corollary discounted_survival_bounded_below : forall r a x0,
  0 < r -> exists m, 0 < m /\ forall T, m <= survival_disc r a x0 T.
Proof.
  intros r a x0 Hr; exists (survival_floor r a); split; [apply survival_floor_pos |].
  intros T; apply discounted_survival_floor; exact Hr.
Qed.

Definition utility_disc (r : R) (a : Act) (x0 : Vec3) (T : R) : R :=
  benefit a * survival_disc r a x0 T.

Theorem discounting_blocks_convergence : forall r x0 p a,
  0 < r -> offense p = 0 -> 0 < benefit p ->
  benefit p < benefit a * survival_floor r a ->
  forall T, utility_disc r p x0 T < utility_disc r a x0 T.
Proof.
  intros r x0 p a Hr Hp Hbp H T; unfold utility_disc.
  rewrite survival_disc_of_inoffensive by exact Hp; rewrite Rmult_1_r.
  assert (Hfl := survival_floor_pos r a).
  assert (Hf := discounted_survival_floor r a x0 T Hr).
  assert (Hba : 0 < benefit a) by nra.
  assert (benefit a * survival_floor r a <= benefit a * survival_disc r a x0 T)
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

Theorem survival_antitone_horizon : forall a x0 T1 T2,
  0 <= T1 <= T2 -> survival a x0 T2 <= survival a x0 T1.
Proof.
  intros a x0 T1 T2 [H0 H]; rewrite !survival_closed_form; apply exp_le_compat.
  assert (Hm : hazard A x0 (horizon_radius T1) <= hazard A x0 (horizon_radius T2)).
  { apply hazard_monotone; split; [apply horizon_radius_nonneg; exact H0 |].
    unfold horizon_radius, Rdiv; apply Rmult_le_compat_r; [lra | apply Rmult_le_compat_l; lra]. }
  assert (Ho := offense_nonneg a). nra.
Qed.

(** * Section 9b: Weighted survival: any per-judge weight in [0, 1] bounded below by wmin > 0 on the judges within the horizon preserves convergence with the rate scaled by wmin / (1 + offense / tol). *)

Definition survival_w (w : Observer -> R) (a : Act) (x0 : Vec3) (T : R) : R :=
  Rprod (fun o => 1 - w o * elim_prob a o x0) (judges x0 (horizon_radius T)).

Lemma survival_w_of_inoffensive : forall w a x0 T, offense a = 0 -> survival_w w a x0 T = 1.
Proof.
  intros w a x0 T H; unfold survival_w.
  rewrite (Rprod_ext _ (fun _ => 1)); [apply Rprod_one |].
  intros o _; rewrite elim_prob_zero by exact H; ring.
Qed.

Lemma survival_w_nonneg : forall w a x0 T,
  (forall o, In o (judges x0 (horizon_radius T)) -> 0 <= w o <= 1) ->
  0 <= survival_w w a x0 T.
Proof.
  intros w a x0 T Hw; unfold survival_w; apply Rprod_nonneg; intros o Ho.
  assert (He := elim_prob_bounds a o x0). destruct (Hw o Ho). nra.
Qed.

Lemma one_minus_le_exp : forall x, 1 - x <= exp (- x).
Proof. intro x; assert (H := exp_ineq1_le (- x)); lra. Qed.

(** The elimination probability is at least the signal in units of 1 + offense / tol. *)
Lemma elim_prob_lower : forall a o x0, obs_tol o = tol ->
  signal a o x0 / (1 + offense a / tol) <= elim_prob a o x0.
Proof.
  intros a o x0 Htol; unfold elim_prob.
  set (s := signal a o x0).
  assert (Hs : 0 <= s) by apply signal_nonneg.
  set (S := offense a / tol).
  assert (HS : 0 <= S) by (unfold S; apply Rdiv_nonneg; [apply offense_nonneg | exact tol_pos]).
  assert (HsS : s <= S).
  { unfold s, S, signal; rewrite Htol.
    assert (Hatt := att_le_1 A (dist o x0) (dist_nonneg o x0)).
    assert (Ho := offense_nonneg a).
    assert (0 < / tol) by (apply Rinv_0_lt_compat; exact tol_pos).
    unfold Rdiv; apply Rmult_le_compat_r; [lra | nra]. }
  assert (H1 : exp (- s) <= / (1 + s)).
  { rewrite exp_Ropp. apply Rinv_le_contravar; [lra | apply exp_ineq1_le]. }
  assert (H2 : s / (1 + s) = 1 - / (1 + s)) by (field; lra).
  assert (H3 : s / (1 + S) <= s / (1 + s)).
  { unfold Rdiv; apply Rmult_le_compat_l; [exact Hs |]. apply Rinv_le_contravar; lra. }
  lra.
Qed.

Lemma signal_sum : forall a x0 rad,
  Rsum (fun o => signal a o x0) (judges x0 rad) = offense a * hazard A x0 rad.
Proof.
  intros a x0 rad; unfold LightCone.hazard, signal.
  rewrite <- Rsum_scal_l; apply Rsum_ext; intros o _; unfold Rdiv; ring.
Qed.

Theorem survival_w_upper : forall (w : Observer -> R) (wmin : R) a x0 T,
  0 <= wmin ->
  (forall o, In o (judges x0 (horizon_radius T)) -> wmin <= w o <= 1) ->
  T_min <= T ->
  survival_w w a x0 T <= exp (- (wmin * offense a * rate * T / (1 + offense a / tol))).
Proof.
  intros w wmin a x0 T Hwmin Hw HT; unfold survival_w.
  set (S := offense a / tol).
  assert (HS : 0 <= S) by (unfold S; apply Rdiv_nonneg; [apply offense_nonneg | exact tol_pos]).
  apply Rle_trans with
    (Rprod (fun o => exp (- (wmin * elim_prob a o x0))) (judges x0 (horizon_radius T))).
  - apply Rprod_le; intros o Ho.
    assert (He := elim_prob_bounds a o x0).
    destruct (Hw o Ho) as [Hw1 Hw2].
    split; [nra |].
    apply Rle_trans with (exp (- (w o * elim_prob a o x0))); [apply one_minus_le_exp |].
    apply exp_le_compat. nra.
  - rewrite Rprod_exp.
    apply exp_le_compat.
    rewrite (Rsum_ext _ (fun o => (- wmin) * elim_prob a o x0)) by (intros; ring).
    rewrite Rsum_scal_l.
    assert (Hlow : Rsum (fun o => signal a o x0 / (1 + S)) (judges x0 (horizon_radius T))
                   <= Rsum (fun o => elim_prob a o x0) (judges x0 (horizon_radius T))).
    { apply Rsum_le; intros o Ho; apply elim_prob_lower; apply (judges_tol _ _ _ Ho). }
    rewrite (Rsum_ext _ (fun o => / (1 + S) * signal a o x0)) in Hlow by (intros; unfold Rdiv; ring).
    rewrite Rsum_scal_l, signal_sum in Hlow.
    set (E := Rsum (fun o => elim_prob a o x0) (judges x0 (horizon_radius T))) in *.
    set (Hz := hazard A x0 (horizon_radius T)) in *.
    assert (Hh := hazard_horizon_lower x0 T HT). fold Hz in Hh.
    assert (Ho := offense_nonneg a).
    assert (Hinv : 0 < / (1 + S)) by (apply Rinv_0_lt_compat; lra).
    assert (H1 : offense a * (rate * T) <= offense a * Hz) by (apply Rmult_le_compat_l; assumption).
    assert (H2 : / (1 + S) * (offense a * (rate * T)) <= / (1 + S) * (offense a * Hz))
      by (apply Rmult_le_compat_l; lra).
    assert (H3 : wmin * (/ (1 + S) * (offense a * (rate * T))) <= wmin * E)
      by (apply Rmult_le_compat_l; lra).
    replace (wmin * offense a * rate * T / (1 + S))
      with (wmin * (/ (1 + S) * (offense a * (rate * T)))) by (unfold Rdiv; ring).
    lra.
Qed.

(** ** Time preference with r T bounded by K behaves like the undiscounted model with the rate scaled by exp(- K). *)

Lemma discount_ge_on_ball : forall r x0 T o,
  0 <= r -> In o (judges x0 (horizon_radius T)) ->
  exp (- (r * T)) <= discount r o x0.
Proof.
  intros r x0 T o Hr Ho; unfold LightCone.discount.
  apply exp_le_compat.
  assert (Hdist := LightCone.judges_dist res tol tol_pos x0 (horizon_radius T) o Ho).
  unfold LightCone.horizon_radius in Hdist.
  assert (Hq : 2 * dist o x0 / c <= T).
  { apply Rmult_le_reg_l with (c / 2); [apply Rdiv_lt_0_compat; lra |].
    replace (c / 2 * (2 * dist o x0 / c)) with (dist o x0) by (field; lra).
    replace (c / 2 * T) with (c * T / 2) by (field; lra).
    exact Hdist. }
  assert (Hm : r * (2 * dist o x0 / c) <= r * T) by (apply Rmult_le_compat_l; assumption).
  lra.
Qed.

Theorem discounted_survival_upper : forall r a x0 T,
  0 <= r -> T_min <= T ->
  survival_disc r a x0 T <=
  exp (- (exp (- (r * T)) * offense a * rate * T / (1 + offense a / tol))).
Proof.
  intros r a x0 T Hr HT.
  change (survival_disc r a x0 T) with (survival_w (fun o => discount r o x0) a x0 T).
  apply survival_w_upper; [left; apply exp_pos | | exact HT].
  intros o Ho; split.
  - apply discount_ge_on_ball; assumption.
  - apply (discount_bounds r o x0 Hr).
Qed.

Theorem patient_survival_upper : forall K r a x0 T,
  0 <= r -> r * T <= K -> T_min <= T ->
  survival_disc r a x0 T <= exp (- (exp (- K) * offense a * rate * T / (1 + offense a / tol))).
Proof.
  intros K r a x0 T Hr HK HT.
  apply Rle_trans with (exp (- (exp (- (r * T)) * offense a * rate * T / (1 + offense a / tol)))).
  { apply discounted_survival_upper; assumption. }
  apply exp_le_compat.
  assert (He : exp (- K) <= exp (- (r * T))) by (apply exp_le_compat; lra).
  assert (Ho := offense_nonneg a). assert (Hrt := rate_pos).
  assert (HT0 : 0 <= T) by (assert (Hm := T_min_pos); lra).
  assert (HS : 0 < 1 + offense a / tol).
  { assert (Hs : 0 <= offense a / tol) by (apply Rdiv_nonneg; [exact Ho | exact tol_pos]). lra. }
  assert (Hprod : 0 <= offense a * rate * T / (1 + offense a / tol)).
  { apply Rdiv_nonneg; [apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra] | exact HS]. }
  assert (Hm : exp (- K) * (offense a * rate * T / (1 + offense a / tol)) <=
               exp (- (r * T)) * (offense a * rate * T / (1 + offense a / tol)))
    by (apply Rmult_le_compat_r; assumption).
  replace (exp (- K) * offense a * rate * T / (1 + offense a / tol))
    with (exp (- K) * (offense a * rate * T / (1 + offense a / tol))) by (unfold Rdiv; ring).
  replace (exp (- (r * T)) * offense a * rate * T / (1 + offense a / tol))
    with (exp (- (r * T)) * (offense a * rate * T / (1 + offense a / tol))) by (unfold Rdiv; ring).
  lra.
Qed.

Theorem patient_survival_vanishes : forall K a x0,
  0 < offense a ->
  forall eps, 0 < eps ->
  exists T0, forall T r, T0 <= T -> 0 <= r -> r * T <= K -> survival_disc r a x0 T < eps.
Proof.
  intros K a x0 Ha eps Heps.
  assert (HS : 0 < 1 + offense a / tol).
  { assert (Hs : 0 <= offense a / tol) by (apply Rdiv_nonneg; [lra | exact tol_pos]). lra. }
  set (P := exp (- K) * offense a * rate / (1 + offense a / tol)).
  assert (HP : 0 < P).
  { unfold P; apply Rdiv_lt_0_compat; [| exact HS].
    apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; [apply exp_pos | exact Ha] | apply rate_pos]. }
  exists (Rmax T_min ((- ln eps) / P + 1)).
  intros T r HT Hr HK.
  assert (HT1 : T_min <= T) by (eapply Rle_trans; [apply Rmax_l | exact HT]).
  assert (HT2 : (- ln eps) / P + 1 <= T) by (eapply Rle_trans; [apply Rmax_r | exact HT]).
  apply Rle_lt_trans with (exp (- (exp (- K) * offense a * rate * T / (1 + offense a / tol)))).
  { apply patient_survival_upper; assumption. }
  rewrite <- (exp_ln eps Heps); apply exp_increasing.
  assert (HPT : P * ((- ln eps) / P + 1) <= P * T) by (apply Rmult_le_compat_l; lra).
  replace (P * ((- ln eps) / P + 1)) with (- ln eps + P) in HPT by (field; lra).
  assert (E : exp (- K) * offense a * rate * T / (1 + offense a / tol) = P * T)
    by (unfold P, Rdiv; ring).
  rewrite E. lra.
Qed.

(** ** Presence credence: any positive credence per site suffices. *)

Definition survival_presence (q : R) (a : Act) (x0 : Vec3) (T : R) : R :=
  survival_w (fun _ => q) a x0 T.

Theorem presence_survival_upper : forall q a x0 T,
  0 <= q <= 1 -> T_min <= T ->
  survival_presence q a x0 T <= exp (- (q * offense a * rate * T / (1 + offense a / tol))).
Proof.
  intros q a x0 T [Hq0 Hq1] HT; unfold survival_presence.
  apply survival_w_upper; [exact Hq0 | intros o _; split; [apply Rle_refl | exact Hq1] | exact HT].
Qed.

(** ** The weighted crossover depth. *)

Definition utility_w (w : Observer -> R) (a : Act) (x0 : Vec3) (T : R) : R :=
  benefit a * survival_w w a x0 T.

Definition crossover_depth_w (wmin delta B bp : R) : R :=
  Rmax T_min ((1 + delta / tol) * ln (Rmax (B / bp) 1) / (wmin * delta * rate)).

Lemma ratio_tol_monotone : forall x y, 0 <= x <= y -> x / (1 + x / tol) <= y / (1 + y / tol).
Proof.
  intros x y [Hx Hxy].
  assert (Ht : 0 < / tol) by (apply Rinv_0_lt_compat; exact tol_pos).
  assert (H1 : 0 < 1 + x / tol) by (unfold Rdiv; nra).
  assert (H2 : 0 < 1 + y / tol) by (unfold Rdiv; nra).
  unfold Rdiv in *.
  apply Rmult_le_reg_r with ((1 + x * / tol) * (1 + y * / tol)); [nra |].
  replace (x * / (1 + x * / tol) * ((1 + x * / tol) * (1 + y * / tol)))
    with (x * (1 + y * / tol)) by (field; lra).
  replace (y * / (1 + y * / tol) * ((1 + x * / tol) * (1 + y * / tol)))
    with (y * (1 + x * / tol)) by (field; lra).
  nra.
Qed.

Theorem weighted_crossover : forall (w : Observer -> R) wmin x0 p delta B,
  offense p = 0 -> 0 < benefit p -> 0 < delta -> 0 < wmin ->
  forall T, crossover_depth_w wmin delta B (benefit p) < T ->
  (forall o, In o (judges x0 (horizon_radius T)) -> wmin <= w o <= 1) ->
  forall a, delta <= offense a -> benefit a <= B ->
  utility_w w a x0 T < utility_w w p x0 T.
Proof.
  intros w wmin x0 p delta B Hp Hbp Hdelta Hwmin T HT Hw a Ha HB.
  unfold utility_w.
  rewrite (survival_w_of_inoffensive w p x0 T Hp), Rmult_1_r.
  assert (Hw01 : forall o, In o (judges x0 (horizon_radius T)) -> 0 <= w o <= 1).
  { intros o Ho; destruct (Hw o Ho); lra. }
  assert (HS0 := survival_w_nonneg w a x0 T Hw01).
  assert (HT1 : T_min < T)
    by (apply Rle_lt_trans with (crossover_depth_w wmin delta B (benefit p)); [apply Rmax_l | exact HT]).
  assert (HT2 : (1 + delta / tol) * ln (Rmax (B / benefit p) 1) / (wmin * delta * rate) < T)
    by (apply Rle_lt_trans with (crossover_depth_w wmin delta B (benefit p)); [apply Rmax_r | exact HT]).
  destruct (Rle_dec (benefit a) 0) as [Hneg | Hposb].
  - nra.
  - apply Rnot_le_lt in Hposb.
    assert (HBpos : 0 < B) by lra.
    assert (Hr := rate_pos).
    assert (Hdt : 0 < 1 + delta / tol).
    { assert (0 <= delta / tol) by (apply Rdiv_nonneg; lra). lra. }
    assert (Hwdr : 0 < wmin * delta * rate)
      by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; assumption | exact Hr]).
    assert (Hup : survival_w w a x0 T <= exp (- (wmin * delta * rate * T / (1 + delta / tol)))).
    { apply Rle_trans with (exp (- (wmin * offense a * rate * T / (1 + offense a / tol)))).
      { apply survival_w_upper; [lra | exact Hw | lra]. }
      apply exp_le_compat.
      assert (Hmono := ratio_tol_monotone delta (offense a) (conj (Rlt_le _ _ Hdelta) Ha)).
      assert (HrT : 0 <= wmin * rate * T).
      { apply Rmult_le_pos; [apply Rmult_le_pos; lra | assert (Hm := T_min_pos); lra]. }
      assert (Hm : wmin * rate * T * (delta / (1 + delta / tol)) <=
                   wmin * rate * T * (offense a / (1 + offense a / tol)))
        by (apply Rmult_le_compat_l; assumption).
      replace (wmin * delta * rate * T / (1 + delta / tol))
        with (wmin * rate * T * (delta / (1 + delta / tol))) by (unfold Rdiv; ring).
      replace (wmin * offense a * rate * T / (1 + offense a / tol))
        with (wmin * rate * T * (offense a / (1 + offense a / tol))) by (unfold Rdiv; ring).
      lra. }
    assert (Hkey : exp (- (wmin * delta * rate * T / (1 + delta / tol))) < benefit p / B).
    { assert (Hbb : 0 < benefit p / B) by (apply Rdiv_lt_0_compat; lra).
      rewrite <- (exp_ln (benefit p / B) Hbb).
      apply exp_increasing.
      rewrite ln_div by lra.
      assert (Hln : ln (B / benefit p) <= ln (Rmax (B / benefit p) 1)).
      { apply ln_le_compat; [apply Rdiv_lt_0_compat; lra | apply Rmax_l]. }
      rewrite ln_div in Hln by lra.
      set (L := ln (Rmax (B / benefit p) 1)) in *.
      assert (Hmul : (1 + delta / tol) * L < wmin * delta * rate * T).
      { apply Rmult_lt_compat_r with (r := wmin * delta * rate) in HT2; [| exact Hwdr].
        replace ((1 + delta / tol) * L / (wmin * delta * rate) * (wmin * delta * rate))
          with ((1 + delta / tol) * L) in HT2 by (field; lra).
        lra. }
      assert (Hdiv : L < wmin * delta * rate * T / (1 + delta / tol)).
      { apply Rmult_lt_reg_r with (1 + delta / tol); [exact Hdt |].
        replace (wmin * delta * rate * T / (1 + delta / tol) * (1 + delta / tol))
          with (wmin * delta * rate * T) by (field; lra).
        lra. }
      lra. }
    apply Rle_lt_trans with (B * survival_w w a x0 T); [nra |].
    apply Rle_lt_trans with (B * exp (- (wmin * delta * rate * T / (1 + delta / tol)))); [nra |].
    apply Rmult_lt_reg_r with (/ B); [apply Rinv_0_lt_compat; exact HBpos |].
    replace (B * exp (- (wmin * delta * rate * T / (1 + delta / tol))) * / B)
      with (exp (- (wmin * delta * rate * T / (1 + delta / tol)))) by (field; lra).
    exact Hkey.
Qed.

Corollary presence_crossover : forall q x0 p delta B,
  offense p = 0 -> 0 < benefit p -> 0 < delta -> 0 < q <= 1 ->
  forall T, crossover_depth_w q delta B (benefit p) < T ->
  forall a, delta <= offense a -> benefit a <= B ->
  benefit a * survival_presence q a x0 T < benefit p * survival_presence q p x0 T.
Proof.
  intros q x0 p delta B Hp Hbp Hdelta [Hq0 Hq1] T HT a Ha HB.
  apply (weighted_crossover (fun _ => q) q x0 p delta B Hp Hbp Hdelta Hq0 T HT); [| exact Ha | exact HB].
  intros o _; split; [apply Rle_refl | exact Hq1].
Qed.

Corollary patient_crossover : forall K r x0 p delta B,
  offense p = 0 -> 0 < benefit p -> 0 < delta -> 0 <= r ->
  forall T, crossover_depth_w (exp (- K)) delta B (benefit p) < T -> r * T <= K ->
  forall a, delta <= offense a -> benefit a <= B ->
  utility_disc r a x0 T < utility_disc r p x0 T.
Proof.
  intros K r x0 p delta B Hp Hbp Hdelta Hr T HT HK a Ha HB.
  change (utility_disc r a x0 T) with (utility_w (fun o => discount r o x0) a x0 T).
  change (utility_disc r p x0 T) with (utility_w (fun o => discount r o x0) p x0 T).
  apply (weighted_crossover (fun o => discount r o x0) (exp (- K)) x0 p delta B Hp Hbp Hdelta (exp_pos _) T HT);
    [| exact Ha | exact HB].
  intros o Ho; split.
  - apply Rle_trans with (exp (- (r * T))); [apply exp_le_compat; lra | apply discount_ge_on_ball; assumption].
  - apply (discount_bounds r o x0 Hr).
Qed.

End Model.
