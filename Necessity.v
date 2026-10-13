(** Necessity of the remaining premises: without a stake in survival, without value at risk, or without valuation of prevented destruction the conclusions fail at every depth, and partial forfeiture of the benefit is enough when the unforfeited part is smaller than the preserving benefit. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.
From BeNice Require Import Vectors Actions Sums LightCone Survival Resources Judges.

Section Necessity.

Variable c : R.
Hypothesis c_pos : 0 < c.
Variable res : R.
Hypothesis res_pos : 0 < res.
Variable tol : R.
Hypothesis tol_pos : 0 < tol.
Variable A : Attenuation.
Variable Act : Type.
Variable offense : Act -> R.
Hypothesis offense_nonneg : forall a, 0 <= offense a.
Variable benefit : Act -> R.

(** An agent with no stake in preservation is unconstrained: any action of positive benefit beats it at every depth. *)
Theorem self_preservation_necessary : forall x0 p a T,
  offense p = 0 -> benefit p <= 0 -> 0 < benefit a ->
  utility c res tol tol_pos A Act offense benefit p x0 T < utility c res tol tol_pos A Act offense benefit a x0 T.
Proof.
  intros x0 p a T Hp Hbp Hba.
  rewrite (utility_of_inoffensive c res tol tol_pos A Act offense benefit p x0 T Hp); unfold utility.
  assert (HS := survival_pos c res tol tol_pos A Act offense a x0 T). nra.
Qed.

(** Elimination forfeits the fraction theta of the benefit and the rest is collected regardless. *)
Definition utility_partial (theta : R) (a : Act) (x0 : Vec3) (T : R) : R :=
  benefit a * ((1 - theta) + theta * survival c res tol tol_pos A Act offense a x0 T).

(** Partial forfeiture suffices when the unforfeited part of the offender's benefit is below the preserving benefit. *)
Theorem partial_forfeiture_crossover : forall x0 p a theta,
  offense p = 0 -> 0 < benefit p -> 0 < offense a -> 0 < theta <= 1 ->
  (1 - theta) * benefit a < benefit p ->
  exists Tstar, forall T, Tstar < T -> utility_partial theta a x0 T < utility_partial theta p x0 T.
Proof.
  intros x0 p a theta Hp Hbp Ha [Ht0 Ht1] Hgap.
  destruct (Rle_dec (benefit a) 0) as [Hneg | Hpos].
  - exists 0; intros T _; unfold utility_partial.
    rewrite (survival_of_inoffensive c res tol tol_pos A Act offense p x0 T Hp).
    assert (HS := survival_pos c res tol tol_pos A Act offense a x0 T).
    assert (HS1 := survival_le_1 c res tol tol_pos A Act offense offense_nonneg a x0 T).
    nra.
  - apply Rnot_le_lt in Hpos.
    set (gap := benefit p - (1 - theta) * benefit a).
    assert (Hg : 0 < gap) by (unfold gap; lra).
    assert (Htb : 0 < theta * benefit a) by nra.
    assert (Heps : 0 < gap / (theta * benefit a)) by (apply Rdiv_lt_0_compat; assumption).
    destruct (survival_vanishes c c_pos res res_pos tol tol_pos A Act offense offense_nonneg a x0 Ha _ Heps) as [T0 HT0].
    exists T0; intros T HT; unfold utility_partial.
    rewrite (survival_of_inoffensive c res tol tol_pos A Act offense p x0 T Hp).
    assert (HS := HT0 T (Rlt_le _ _ HT)).
    assert (Hm : theta * benefit a * survival c res tol tol_pos A Act offense a x0 T <
                 theta * benefit a * (gap / (theta * benefit a)))
      by (apply Rmult_lt_compat_l; assumption).
    replace (theta * benefit a * (gap / (theta * benefit a))) with gap in Hm by (field; repeat split; lra).
    unfold gap in Hm. lra.
Qed.

End Necessity.

Section JudgeNecessity.

Variable c : R.
Hypothesis c_pos : 0 < c.
Variable res : R.
Hypothesis res_pos : 0 < res.
Variable tol : R.
Hypothesis tol_pos : 0 < tol.
Variable A : Attenuation.

(** A judge with no stake in its own survival is not deterred: when punishing a preserver pays, Punish beats Ignore at every depth. *)
Theorem judge_stake_necessary : forall phi b0 gainP cost xJ TJ,
  b0 <= 0 -> 0 < b0 + gainP - cost ->
  utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 gainP cost) Ignore xJ TJ <
  utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 gainP cost) Punish xJ TJ.
Proof.
  intros phi b0 gainP cost xJ TJ Hb0 Hpay.
  rewrite (utility_of_inoffensive c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 gainP cost)
             Ignore xJ TJ eq_refl).
  unfold utility.
  assert (HS := survival_pos c res tol tol_pos A Verdict (judge_offense phi 0) Punish xJ TJ).
  cbn [judge_benefit]. nra.
Qed.

(** Without value at risk there is no deterrent: a worthless preserver is punished whenever the gain exceeds the cost. *)
Theorem victim_value_necessary : forall b0 gainP cost xJ TJ,
  cost < gainP ->
  utility c res tol tol_pos A Verdict (judge_offense 0 0) (judge_benefit b0 gainP cost) Ignore xJ TJ <
  utility c res tol tol_pos A Verdict (judge_offense 0 0) (judge_benefit b0 gainP cost) Punish xJ TJ.
Proof.
  intros b0 gainP cost xJ TJ Hgc.
  assert (H0 : judge_offense 0 0 Punish = 0) by (simpl; rewrite Rminus_0_r; apply Rmax_left; lra).
  rewrite (utility_of_inoffensive c res tol tol_pos A Verdict (judge_offense 0 0) (judge_benefit b0 gainP cost)
             Ignore xJ TJ eq_refl).
  rewrite (utility_of_inoffensive c res tol tol_pos A Verdict (judge_offense 0 0) (judge_benefit b0 gainP cost)
             Punish xJ TJ H0).
  cbn [judge_benefit]. lra.
Qed.

(** Without valuation of prevented destruction, judges never punish: with w = 0 and positive cost, Ignore beats Punish on every persistent destroyer. *)
Theorem valuation_necessary : forall phi delta b0 cost xJ TJ,
  0 < delta -> phi / delta <= TJ -> 0 < cost ->
  utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 (0 * (delta * TJ)) cost) Punish xJ TJ <
  utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 (0 * (delta * TJ)) cost) Ignore xJ TJ.
Proof.
  intros phi delta b0 cost xJ TJ Hd HTJ Hcost.
  rewrite (utility_of_inoffensive c res tol tol_pos A Verdict (judge_offense phi (delta * TJ))
             (judge_benefit b0 (0 * (delta * TJ)) cost) Ignore xJ TJ eq_refl).
  rewrite (utility_of_inoffensive c res tol tol_pos A Verdict (judge_offense phi (delta * TJ))
             (judge_benefit b0 (0 * (delta * TJ)) cost) Punish xJ TJ (persistent_destroyer phi delta TJ Hd HTJ)).
  cbn [judge_benefit]. lra.
Qed.

End JudgeNecessity.
