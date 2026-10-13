(** Resource preservation: the thesis instantiated with the destruction of the event. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.
From BeNice Require Import Vectors Actions Sums LightCone Survival.

(** * Section 10: The thesis: the offense is the destruction of the event on the state s0; preserving actions do not reduce the norm and destructive ones do. *)

Section Resources.

Variable c : R.
Hypothesis c_pos : 0 < c.
Variable res : R.
Hypothesis res_pos : 0 < res.
Variable tol : R.
Hypothesis tol_pos : 0 < tol.
Variable A : Attenuation.
Variable s0 : Vec3.
Variable benefit : Action -> R.

Definition destr (a : Action) : R := destruction a s0.

Lemma destr_nonneg : forall a, 0 <= destr a.
Proof. intro; apply destruction_nonneg. Qed.

Lemma destr_zero_iff : forall a, destr a = 0 <-> preserving_at a s0.
Proof. intro; apply destruction_zero_iff. Qed.

Lemma destr_pos_iff : forall a, 0 < destr a <-> destructive_at a s0.
Proof. intro; apply destruction_pos_iff. Qed.

Theorem preservation_survives : forall p x0 T,
  preserving_at p s0 -> survival c res tol tol_pos A Action destr p x0 T = 1.
Proof. intros p x0 T Hp; apply survival_of_inoffensive; apply destr_zero_iff; exact Hp. Qed.

Theorem preservation_dominates : forall p a x0 T,
  preserving_at p s0 ->
  survival c res tol tol_pos A Action destr a x0 T <= survival c res tol tol_pos A Action destr p x0 T.
Proof.
  intros p a x0 T Hp; rewrite (preservation_survives p x0 T Hp).
  apply survival_le_1; exact destr_nonneg.
Qed.

Theorem destruction_survival_lt_1 : forall a x0 T,
  destructive_at a s0 -> 0 <= T -> survival c res tol tol_pos A Action destr a x0 T < 1.
Proof.
  intros a x0 T Ha HT.
  apply (survival_lt_1 c c_pos res res_pos tol tol_pos A Action destr a x0 T); [| exact HT].
  apply destr_pos_iff; exact Ha.
Qed.

Theorem destruction_survival_rate : forall a x0 T,
  T_min c res <= T ->
  survival c res tol tol_pos A Action destr a x0 T <= exp (- destruction a s0 * rate c res tol A * T).
Proof.
  intros a x0 T HT.
  apply (survival_upper_bound c c_pos res res_pos tol tol_pos A Action destr destr_nonneg a x0 T HT).
Qed.

Theorem destruction_survival_vanishes : forall a x0,
  destructive_at a s0 ->
  forall eps, 0 < eps ->
  exists T0, forall T, T0 <= T -> survival c res tol tol_pos A Action destr a x0 T < eps.
Proof.
  intros a x0 Ha eps Heps.
  apply (survival_vanishes c c_pos res res_pos tol tol_pos A Action destr destr_nonneg a x0);
    [apply destr_pos_iff; exact Ha | exact Heps].
Qed.

Theorem destruction_survival_Un_cv : forall a x0 (Tn : nat -> R),
  destructive_at a s0 -> cv_infty Tn ->
  Un_cv (fun n => survival c res tol tol_pos A Action destr a x0 (Tn n)) 0.
Proof.
  intros a x0 Tn Ha HTn.
  apply (survival_Un_cv c c_pos res res_pos tol tol_pos A Action destr destr_nonneg a x0 Tn);
    [apply destr_pos_iff; exact Ha | exact HTn].
Qed.

Theorem preservation_crossover : forall x0 p a,
  preserving_at p s0 -> 0 < benefit p -> destructive_at a s0 ->
  exists Tstar, forall T, Tstar < T ->
    utility c res tol tol_pos A Action destr benefit a x0 T <
    utility c res tol tol_pos A Action destr benefit p x0 T.
Proof.
  intros x0 p a Hp Hbp Ha.
  exists (pointwise_depth c res tol A Action destr benefit p a).
  intros T HT.
  apply (pointwise_crossover c c_pos res res_pos tol tol_pos A Action destr destr_nonneg benefit x0 p a);
    [apply destr_zero_iff; exact Hp | exact Hbp | apply destr_pos_iff; exact Ha | exact HT].
Qed.

Theorem optimal_destruction_bound : forall x0 p a B T,
  preserving_at p s0 -> 0 < benefit p -> benefit a <= B ->
  T_min c res <= T ->
  utility c res tol tol_pos A Action destr benefit p x0 T <=
  utility c res tol tol_pos A Action destr benefit a x0 T ->
  destruction a s0 <= ln (B / benefit p) / (rate c res tol A * T).
Proof.
  intros x0 p a B T Hp Hbp HB HT Hopt.
  apply (optimal_offense_le c c_pos res res_pos tol tol_pos A Action destr destr_nonneg benefit x0 p a B T);
    [apply destr_zero_iff; exact Hp | exact Hbp | exact HB | exact HT | exact Hopt].
Qed.

Theorem optimal_destruction_vanishes : forall x0 p B,
  preserving_at p s0 -> 0 < benefit p ->
  forall eps, 0 < eps ->
  exists T0, forall T, T0 <= T ->
    forall a, benefit a <= B ->
    utility c res tol tol_pos A Action destr benefit p x0 T <=
    utility c res tol tol_pos A Action destr benefit a x0 T ->
    destruction a s0 < eps.
Proof.
  intros x0 p B Hp Hbp eps Heps.
  apply (optimal_offense_vanishes c c_pos res res_pos tol tol_pos A Action destr destr_nonneg benefit x0 p B);
    [apply destr_zero_iff; exact Hp | exact Hbp | exact Heps].
Qed.

Theorem optimal_actions_preserve : forall x0 (menu : list Action) p,
  In p menu -> preserving_at p s0 -> 0 < benefit p ->
  exists Tstar, forall T, Tstar < T ->
    forall a, In a menu ->
    (forall a', In a' menu ->
      utility c res tol tol_pos A Action destr benefit a' x0 T <=
      utility c res tol tol_pos A Action destr benefit a x0 T) ->
    preserving_at a s0.
Proof.
  intros x0 menu p Hin Hp Hbp.
  destruct (optimal_actions_are_inoffensive c c_pos res res_pos tol tol_pos A Action destr destr_nonneg
              benefit x0 menu p Hin (proj2 (destr_zero_iff p) Hp) Hbp) as [Tstar H].
  exists Tstar; intros T HT a Ha Hopt.
  apply destr_zero_iff; apply (H T HT a Ha Hopt).
Qed.

Theorem shallow_destruction_wins : forall x0 p a T,
  preserving_at p s0 ->
  benefit p / survival c res tol tol_pos A Action destr a x0 T < benefit a ->
  utility c res tol tol_pos A Action destr benefit p x0 T <
  utility c res tol tol_pos A Action destr benefit a x0 T.
Proof.
  intros x0 p a T Hp H; apply shallow_offense_wins; [apply destr_zero_iff; exact Hp | exact H].
Qed.

Theorem deeper_never_safer : forall a x0 T1 T2,
  0 <= T1 <= T2 ->
  survival c res tol tol_pos A Action destr a x0 T2 <= survival c res tol tol_pos A Action destr a x0 T1.
Proof.
  intros a x0 T1 T2 H.
  apply (survival_antitone_horizon c c_pos res res_pos tol tol_pos A Action destr destr_nonneg a x0 T1 T2 H).
Qed.

Theorem time_preference_blocks_convergence : forall r x0 p a,
  0 < r -> preserving_at p s0 -> 0 < benefit p ->
  benefit p < benefit a * survival_floor c res tol Action destr r a ->
  forall T,
    utility_disc c res tol tol_pos A Action destr benefit r p x0 T <
    utility_disc c res tol tol_pos A Action destr benefit r a x0 T.
Proof.
  intros r x0 p a Hr Hp Hbp H T.
  apply (discounting_blocks_convergence c c_pos res res_pos tol tol_pos A Action destr destr_nonneg benefit r x0 p a);
    [exact Hr | apply destr_zero_iff; exact Hp | exact Hbp | exact H].
Qed.

Lemma identity_preserving_at : preserving_at identity_action s0.
Proof. apply identity_preserving. Qed.

Lemma scaling_is_destructive : forall f, 0 <= f < 1 -> 0 < norm s0 -> destructive_at (scale_action f) s0.
Proof.
  intros f [Hf0 Hf1] Hs; unfold destructive_at, scale_action.
  rewrite norm_scale_nonneg by exact Hf0. nra.
Qed.

Lemma scaling_destruction : forall f, 0 <= f <= 1 -> destr (scale_action f) = (1 - f) * norm s0.
Proof. intros f Hf; apply destruction_scale; exact Hf. Qed.

(** ** Policies: a sequence of acts is judged act by act. *)

Definition policy_survival (acts : list Action) (x0 : Vec3) (T : R) : R :=
  Rprod (fun a => survival c res tol tol_pos A Action destr a x0 T) acts.

Theorem preserving_policy_survives : forall acts x0 T,
  (forall a, In a acts -> preserving_at a s0) -> policy_survival acts x0 T = 1.
Proof.
  intros acts x0 T H; unfold policy_survival.
  rewrite (Rprod_ext _ (fun _ => 1)); [apply Rprod_one |].
  intros a Ha; apply preservation_survives; apply H; exact Ha.
Qed.

Theorem policy_survival_le_act : forall acts a x0 T,
  In a acts -> policy_survival acts x0 T <= survival c res tol tol_pos A Action destr a x0 T.
Proof.
  intros acts a x0 T Hin; unfold policy_survival.
  induction acts as [| b rest IH]; [destruct Hin |].
  rewrite Rprod_cons.
  assert (Hb0 := survival_pos c res tol tol_pos A Action destr b x0 T).
  assert (Hb1 : survival c res tol tol_pos A Action destr b x0 T <= 1)
    by (apply survival_le_1; exact destr_nonneg).
  assert (Hr0 : 0 <= Rprod (fun a' => survival c res tol tol_pos A Action destr a' x0 T) rest).
  { apply Rprod_nonneg; intros a' _; left; apply survival_pos. }
  assert (Hr1 : Rprod (fun a' => survival c res tol tol_pos A Action destr a' x0 T) rest <= 1).
  { apply Rprod_le_1; intros a' _; split; [left; apply survival_pos | apply survival_le_1; exact destr_nonneg]. }
  destruct Hin as [<- | Hin].
  - nra.
  - apply Rle_trans with (Rprod (fun a' => survival c res tol tol_pos A Action destr a' x0 T) rest);
      [nra | apply IH; exact Hin].
Qed.

Corollary destructive_policy_vanishes : forall acts a x0,
  In a acts -> destructive_at a s0 ->
  forall eps, 0 < eps -> exists T0, forall T, T0 <= T -> policy_survival acts x0 T < eps.
Proof.
  intros acts a x0 Hin Ha eps Heps.
  destruct (destruction_survival_vanishes a x0 Ha eps Heps) as [T0 HT0].
  exists T0; intros T HT.
  eapply Rle_lt_trans; [apply policy_survival_le_act; exact Hin | apply HT0; exact HT].
Qed.

(** ** Concealment: a judge sees the fraction v of the destruction; any positive fraction suffices. *)

Definition visible (v : R) (a : Action) : R := v * destruction a s0.

Lemma visible_nonneg : forall v, 0 <= v -> forall a, 0 <= visible v a.
Proof. intros v Hv a; unfold visible; apply Rmult_le_pos; [exact Hv | apply destruction_nonneg]. Qed.

Theorem concealment_must_be_perfect : forall v a x0,
  0 < v -> destructive_at a s0 ->
  forall eps, 0 < eps ->
  exists T0, forall T, T0 <= T -> survival c res tol tol_pos A Action (visible v) a x0 T < eps.
Proof.
  intros v a x0 Hv Ha eps Heps.
  apply (survival_vanishes c c_pos res res_pos tol tol_pos A Action (visible v) (visible_nonneg v (Rlt_le _ _ Hv)) a x0);
    [| exact Heps].
  unfold visible; apply Rmult_lt_0_compat; [exact Hv | apply destr_pos_iff; exact Ha].
Qed.

(** ** Presence credence and time preference, restated for destruction. *)

Theorem presence_destruction_decays : forall q a x0 T,
  0 <= q <= 1 -> T_min c res <= T ->
  survival_presence c res tol tol_pos A Action destr q a x0 T <=
  exp (- (q * destruction a s0 * rate c res tol A * T / (1 + destruction a s0 / tol))).
Proof.
  intros q a x0 T Hq HT.
  apply (presence_survival_upper c c_pos res res_pos tol tol_pos A Action destr destr_nonneg q a x0 T Hq HT).
Qed.

Theorem patient_destruction_vanishes : forall K a x0,
  destructive_at a s0 ->
  forall eps, 0 < eps ->
  exists T0, forall T r, T0 <= T -> 0 <= r -> r * T <= K ->
    survival_disc c res tol tol_pos A Action destr r a x0 T < eps.
Proof.
  intros K a x0 Ha eps Heps.
  apply (patient_survival_vanishes c c_pos res res_pos tol tol_pos A Action destr destr_nonneg K a x0);
    [apply destr_pos_iff; exact Ha | exact Heps].
Qed.

Theorem patient_preservation_crossover : forall K r x0 p delta B,
  preserving_at p s0 -> 0 < benefit p -> 0 < delta -> 0 <= r ->
  forall T, crossover_depth_w c res tol A (exp (- K)) delta B (benefit p) < T -> r * T <= K ->
  forall a, delta <= destruction a s0 -> benefit a <= B ->
  utility_disc c res tol tol_pos A Action destr benefit r a x0 T <
  utility_disc c res tol tol_pos A Action destr benefit r p x0 T.
Proof.
  intros K r x0 p delta B Hp Hbp Hdelta Hr T HT HK a Ha HB.
  apply (patient_crossover c c_pos res res_pos tol tol_pos A Action destr destr_nonneg benefit K r x0 p delta B);
    [apply destr_zero_iff; exact Hp | exact Hbp | exact Hdelta | exact Hr | exact HT | exact HK | exact Ha | exact HB].
Qed.

Theorem presence_preservation_crossover : forall q x0 p delta B,
  preserving_at p s0 -> 0 < benefit p -> 0 < delta -> 0 < q <= 1 ->
  forall T, crossover_depth_w c res tol A q delta B (benefit p) < T ->
  forall a, delta <= destruction a s0 -> benefit a <= B ->
  benefit a * survival_presence c res tol tol_pos A Action destr q a x0 T <
  benefit p * survival_presence c res tol tol_pos A Action destr q p x0 T.
Proof.
  intros q x0 p delta B Hp Hbp Hdelta Hq T HT a Ha HB.
  apply (presence_crossover c c_pos res res_pos tol tol_pos A Action destr destr_nonneg benefit q x0 p delta B);
    [apply destr_zero_iff; exact Hp | exact Hbp | exact Hdelta | exact Hq | exact HT | exact Ha | exact HB].
Qed.

End Resources.
