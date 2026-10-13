(** Judges as players: best responses, the tolerance credence, and the derived asymmetry. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.
From BeNice Require Import Vectors Actions Sums LightCone Survival.

(** * Section 11: A judge is an agent facing judges: its verdict is a best response, the Poisson elimination probability is the credence that its tolerance lies below the perceived offense, punishing a preserver destroys the preserver's value, and punishing a persistent destroyer is net-preserving. *)

Inductive Verdict : Type := Punish | Ignore.

Definition judge_payoff (tau omega : R) (v : Verdict) : R :=
  match v with Punish => - tau | Ignore => - omega end.

Definition judge_best (tau omega : R) : Verdict :=
  if Rlt_dec tau omega then Punish else Ignore.

Lemma judge_best_optimal : forall tau omega v,
  judge_payoff tau omega v <= judge_payoff tau omega (judge_best tau omega).
Proof.
  intros tau omega v; unfold judge_payoff, judge_best.
  destruct (Rlt_dec tau omega); destruct v; lra.
Qed.

Lemma judge_best_punish_iff : forall tau omega, judge_best tau omega = Punish <-> tau < omega.
Proof.
  intros tau omega; unfold judge_best.
  destruct (Rlt_dec tau omega) as [Hlt | Hge]; split; intro H;
    [exact Hlt | reflexivity | discriminate | exfalso; exact (Hge H)].
Qed.

Lemma judge_best_ignores_harmless : forall tau, 0 < tau -> judge_best tau 0 = Ignore.
Proof. intros tau Ht; unfold judge_best; destruct (Rlt_dec tau 0); [lra | reflexivity]. Qed.

Lemma judge_best_monotone : forall tau w1 w2,
  w1 <= w2 -> judge_best tau w1 = Punish -> judge_best tau w2 = Punish.
Proof. intros tau w1 w2 Hw H; apply judge_best_punish_iff in H; apply judge_best_punish_iff; lra. Qed.

(** The agent's credence that a judge of mean tolerance theta has tolerance below omega. *)
Definition tolerance_credence (theta omega : R) : R := 1 - exp (- omega / theta).

Lemma tolerance_credence_zero : forall theta, tolerance_credence theta 0 = 0.
Proof.
  intros theta; unfold tolerance_credence.
  replace (- 0 / theta) with 0 by (unfold Rdiv; ring). rewrite exp_0; ring.
Qed.

Lemma tolerance_credence_bounds : forall theta omega,
  0 < theta -> 0 <= omega -> 0 <= tolerance_credence theta omega < 1.
Proof.
  intros theta omega Ht Hw; unfold tolerance_credence.
  assert (H1 : - omega / theta <= 0).
  { unfold Rdiv; assert (0 < / theta) by (apply Rinv_0_lt_compat; exact Ht); nra. }
  assert (H2 := exp_le_1 _ H1). assert (H3 := exp_pos (- omega / theta)). lra.
Qed.

Lemma tolerance_credence_monotone : forall theta w1 w2,
  0 < theta -> w1 <= w2 -> tolerance_credence theta w1 <= tolerance_credence theta w2.
Proof.
  intros theta w1 w2 Ht Hw; unfold tolerance_credence.
  assert (exp (- w2 / theta) <= exp (- w1 / theta)).
  { apply exp_le_compat; unfold Rdiv.
    assert (0 < / theta) by (apply Rinv_0_lt_compat; exact Ht). nra. }
  lra.
Qed.

Lemma tolerance_credence_limit : forall theta eps,
  0 < theta -> 0 < eps ->
  exists W, forall omega, W <= omega -> 1 - eps < tolerance_credence theta omega.
Proof.
  intros theta eps Ht He.
  exists (theta * (- ln eps) + theta).
  intros omega Hw; unfold tolerance_credence.
  assert (exp (- omega / theta) < eps).
  { rewrite <- (exp_ln eps He). apply exp_increasing.
    unfold Rdiv. apply Rmult_lt_reg_r with theta; [exact Ht |].
    replace (- omega * / theta * theta) with (- omega) by (field; lra).
    lra. }
  lra.
Qed.

(** Under the exponential credence, the Poisson elimination probability is the credence that the judge's tolerance lies below the perceived offense. *)
Theorem elim_prob_is_tolerance_credence : forall (A : Attenuation) (Act : Type) (offense : Act -> R) a o x0,
  elim_prob A Act offense a o x0 = tolerance_credence (obs_tol o) (offense a * att A (dist o x0)).
Proof. intros; unfold elim_prob, signal, tolerance_credence; f_equal; f_equal; unfold Rdiv; ring. Qed.

(** The judge's own offense as seen by its judges: punishing destroys the offender's value phi and prevents the destruction psi it would have caused. *)
Definition judge_offense (phi psi : R) (v : Verdict) : R :=
  match v with Punish => Rmax 0 (phi - psi) | Ignore => 0 end.

Lemma judge_offense_nonneg : forall phi psi v, 0 <= judge_offense phi psi v.
Proof. intros phi psi [|]; simpl; [apply Rmax_l | lra]. Qed.

Lemma punishing_a_preserver_destroys : forall phi, 0 <= phi -> judge_offense phi 0 Punish = phi.
Proof. intros phi H; simpl; rewrite Rminus_0_r; apply Rmax_right; exact H. Qed.

Lemma punishing_a_destroyer_preserves : forall phi psi, phi <= psi -> judge_offense phi psi Punish = 0.
Proof. intros phi psi H; simpl; apply Rmax_left; lra. Qed.

Lemma persistent_destroyer : forall phi delta TJ,
  0 < delta -> phi / delta <= TJ -> judge_offense phi (delta * TJ) Punish = 0.
Proof.
  intros phi delta TJ Hd H; apply punishing_a_destroyer_preserves.
  assert (E : phi = delta * (phi / delta)) by (field; lra).
  rewrite E; apply Rmult_le_compat_l; lra.
Qed.

(** The judge's benefit: its continued existence b0, plus the prevented destruction, minus the cost of punishing. *)
Definition judge_benefit (b0 gain cost : R) (v : Verdict) : R :=
  match v with Punish => b0 + gain - cost | Ignore => b0 end.

(** Prevented destruction valued at w per unit over a horizon T exceeds a fixed cost once T exceeds cost / (w * delta). *)
Lemma gain_exceeds_cost : forall w delta cost T,
  0 < w -> 0 < delta -> cost / (w * delta) < T -> cost < w * (delta * T).
Proof.
  intros w delta cost T Hw Hd H.
  assert (Hwd : 0 < w * delta) by (apply Rmult_lt_0_compat; assumption).
  apply Rmult_lt_compat_l with (r := w * delta) in H; [| exact Hwd].
  replace (w * delta * (cost / (w * delta))) with cost in H by (field; lra).
  lra.
Qed.

Section JudgesAsPlayers.

Variable c : R.
Hypothesis c_pos : 0 < c.
Variable res : R.
Hypothesis res_pos : 0 < res.
Variable tol : R.
Hypothesis tol_pos : 0 < tol.
Variable A : Attenuation.

(** A judge that punishes preservers is a destroyer: its survival vanishes. *)
Theorem harsh_judge_survival_vanishes : forall phi xJ,
  0 < phi ->
  forall eps, 0 < eps ->
  exists T0, forall TJ, T0 <= TJ ->
    survival c res tol tol_pos A Verdict (judge_offense phi 0) Punish xJ TJ < eps.
Proof.
  intros phi xJ Hphi eps Heps.
  apply (survival_vanishes c c_pos res res_pos tol tol_pos A Verdict (judge_offense phi 0)
           (judge_offense_nonneg phi 0) Punish xJ); [| exact Heps].
  rewrite punishing_a_preserver_destroys; lra.
Qed.

(** Beyond its own crossover depth a judge spares preservers whatever the gain from punishing them. *)
Theorem deep_judges_spare_preservers : forall phi b0 gain cost xJ,
  0 < phi -> 0 < b0 ->
  exists TJstar, forall TJ, TJstar < TJ ->
    utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 gain cost) Punish xJ TJ <
    utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 gain cost) Ignore xJ TJ.
Proof.
  intros phi b0 gain cost xJ Hphi Hb0.
  exists (pointwise_depth c res tol A Verdict (judge_offense phi 0) (judge_benefit b0 gain cost) Ignore Punish).
  intros TJ HT.
  apply (pointwise_crossover c c_pos res res_pos tol tol_pos A Verdict (judge_offense phi 0)
           (judge_offense_nonneg phi 0) (judge_benefit b0 gain cost) xJ Ignore Punish);
    [reflexivity | exact Hb0 | rewrite punishing_a_preserver_destroys; lra | exact HT].
Qed.

(** Once the horizon exceeds phi / delta, punishing a persistent destroyer is inoffensive and a judge whose gain exceeds its cost punishes. *)
Theorem deep_judges_punish_persistent_destroyers : forall phi delta b0 gain cost xJ TJ,
  0 < delta -> phi / delta <= TJ -> cost < gain ->
  utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 gain cost) Ignore xJ TJ <
  utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 gain cost) Punish xJ TJ.
Proof.
  intros phi delta b0 gain cost xJ TJ Hd H Hgc.
  rewrite (utility_of_inoffensive c res tol tol_pos A Verdict (judge_offense phi (delta * TJ))
             (judge_benefit b0 gain cost) Ignore xJ TJ eq_refl).
  rewrite (utility_of_inoffensive c res tol tol_pos A Verdict (judge_offense phi (delta * TJ))
             (judge_benefit b0 gain cost) Punish xJ TJ (persistent_destroyer phi delta TJ Hd H)).
  simpl; lra.
Qed.

(** The asymmetry assumed at the agent level is the behaviour of deep judges. *)
Theorem derived_asymmetry : forall phi delta b0 w cost xJ,
  0 < phi -> 0 < delta -> 0 < b0 -> 0 < w ->
  exists TJstar, forall TJ, TJstar < TJ ->
    utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 0 cost) Punish xJ TJ <
    utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 0 cost) Ignore xJ TJ /\
    utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 (w * (delta * TJ)) cost) Ignore xJ TJ <
    utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 (w * (delta * TJ)) cost) Punish xJ TJ.
Proof.
  intros phi delta b0 w cost xJ Hphi Hd Hb0 Hw.
  destruct (deep_judges_spare_preservers phi b0 0 cost xJ Hphi Hb0) as [TJ1 H1].
  exists (Rmax TJ1 (Rmax (phi / delta) (cost / (w * delta)))).
  intros TJ HT.
  assert (HT1 : TJ1 < TJ) by (eapply Rle_lt_trans; [apply Rmax_l | exact HT]).
  assert (HTd : phi / delta <= TJ).
  { left; eapply Rle_lt_trans; [| exact HT]. eapply Rle_trans; [apply Rmax_l | apply Rmax_r]. }
  assert (HTc : cost / (w * delta) < TJ).
  { eapply Rle_lt_trans; [| exact HT]. eapply Rle_trans; [apply Rmax_r | apply Rmax_r]. }
  split.
  - apply H1; exact HT1.
  - apply deep_judges_punish_persistent_destroyers; [exact Hd | exact HTd | apply gain_exceeds_cost; assumption].
Qed.

End JudgesAsPlayers.
