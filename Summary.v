(** The thesis, its extensions and the two-level game as single theorems, with their axioms printed. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.
From BeNice Require Import Vectors Actions Sums LightCone Survival Resources Judges Independence Population Physical Rational Necessity.

(** * Section 13: The thesis in one theorem, for any speed of light, lattice spacing, tolerance, attenuation no steeper than inverse square, event position, resource state and benefit function. *)

Theorem convergence_to_resource_preservation :
  forall (c res tol : R) (tol_pos : 0 < tol) (A : Attenuation) (s0 x0 : Vec3) (benefit : Action -> R),
  0 < c -> 0 < res ->
  (forall p T, preserving_at p s0 ->
     survival c res tol tol_pos A Action (destr s0) p x0 T = 1) /\
  (forall a T, T_min c res <= T ->
     survival c res tol tol_pos A Action (destr s0) a x0 T <=
     exp (- destruction a s0 * rate c res tol A * T)) /\
  (forall a (Tn : nat -> R), destructive_at a s0 -> cv_infty Tn ->
     Un_cv (fun n => survival c res tol tol_pos A Action (destr s0) a x0 (Tn n)) 0) /\
  (forall p a, preserving_at p s0 -> 0 < benefit p -> destructive_at a s0 ->
     exists Tstar, forall T, Tstar < T ->
       utility c res tol tol_pos A Action (destr s0) benefit a x0 T <
       utility c res tol tol_pos A Action (destr s0) benefit p x0 T) /\
  (forall p a B T, preserving_at p s0 -> 0 < benefit p -> benefit a <= B -> T_min c res <= T ->
     utility c res tol tol_pos A Action (destr s0) benefit p x0 T <=
     utility c res tol tol_pos A Action (destr s0) benefit a x0 T ->
     destruction a s0 <= ln (B / benefit p) / (rate c res tol A * T)) /\
  (forall (menu : list Action) p, In p menu -> preserving_at p s0 -> 0 < benefit p ->
     exists Tstar, forall T, Tstar < T ->
       forall a, In a menu ->
       (forall a', In a' menu ->
          utility c res tol tol_pos A Action (destr s0) benefit a' x0 T <=
          utility c res tol tol_pos A Action (destr s0) benefit a x0 T) ->
       preserving_at a s0).
Proof.
  intros c res tol tol_pos A s0 x0 benefit Hc Hres.
  repeat split.
  - intros p T Hp; apply preservation_survives; exact Hp.
  - intros a T HT; apply destruction_survival_rate; assumption.
  - intros a Tn Ha HTn; apply destruction_survival_Un_cv; assumption.
  - intros p a Hp Hbp Ha; apply preservation_crossover; assumption.
  - intros p a B T Hp Hbp HB HT Hopt; apply (optimal_destruction_bound c Hc res Hres tol tol_pos A s0 benefit x0 p a B T); assumption.
  - intros menu p Hin Hp Hbp.
    apply (optimal_actions_preserve c Hc res Hres tol tol_pos A s0 benefit x0 menu p); assumption.
Qed.

(** The two-level game: deep judges spare preservers and punish persistent destroyers, and against such judges every optimal action of a deep agent is preserving. *)
Theorem two_level_equilibrium :
  forall (c res tol : R) (tol_pos : 0 < tol) (A : Attenuation) (s0 x0 xJ : Vec3) (benefit : Action -> R)
         (menu : list Action) (p : Action) (phi delta b0 w cost : R),
  0 < c -> 0 < res ->
  In p menu -> preserving_at p s0 -> 0 < benefit p ->
  0 < phi -> 0 < delta -> 0 < b0 -> 0 < w ->
  exists Tstar TJstar,
    (forall T, Tstar < T ->
       forall a, In a menu ->
       (forall a', In a' menu ->
          utility c res tol tol_pos A Action (destr s0) benefit a' x0 T <=
          utility c res tol tol_pos A Action (destr s0) benefit a x0 T) ->
       preserving_at a s0) /\
    (forall TJ, TJstar < TJ ->
       utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 0 cost) Punish xJ TJ <
       utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 0 cost) Ignore xJ TJ /\
       utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 (w * (delta * TJ)) cost) Ignore xJ TJ <
       utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 (w * (delta * TJ)) cost) Punish xJ TJ).
Proof.
  intros c res tol tol_pos A s0 x0 xJ benefit menu p phi delta b0 w cost Hc Hres Hin Hp Hbp Hphi Hd Hb0 Hw.
  destruct (optimal_actions_preserve c Hc res Hres tol tol_pos A s0 benefit x0 menu p Hin Hp Hbp) as [Tstar HT].
  destruct (derived_asymmetry c Hc res Hres tol tol_pos A phi delta b0 w cost xJ Hphi Hd Hb0 Hw) as [TJstar HTJ].
  exists Tstar, TJstar; split; [exact HT | exact HTJ].
Qed.

(** Beyond the thesis: any positive presence credence, any positive visibility and any time preference with r T bounded preserve the convergence, a fixed positive rate does not, and a policy with a destructive act vanishes with it. *)
Theorem beyond_the_thesis :
  forall (c res tol : R) (tol_pos : 0 < tol) (A : Attenuation) (s0 x0 : Vec3) (benefit : Action -> R),
  0 < c -> 0 < res ->
  (forall q a T, 0 <= q <= 1 -> T_min c res <= T ->
     survival_presence c res tol tol_pos A Action (destr s0) q a x0 T <=
     exp (- (q * destruction a s0 * rate c res tol A * T / (1 + destruction a s0 / tol)))) /\
  (forall v a, 0 < v -> destructive_at a s0 -> forall eps, 0 < eps ->
     exists T0, forall T, T0 <= T ->
       survival c res tol tol_pos A Action (visible s0 v) a x0 T < eps) /\
  (forall K a, destructive_at a s0 -> forall eps, 0 < eps ->
     exists T0, forall T r, T0 <= T -> 0 <= r -> r * T <= K ->
       survival_disc c res tol tol_pos A Action (destr s0) r a x0 T < eps) /\
  (forall r p a, 0 < r -> preserving_at p s0 -> 0 < benefit p ->
     benefit p < benefit a * survival_floor c res tol Action (destr s0) r a ->
     forall T, utility_disc c res tol tol_pos A Action (destr s0) benefit r p x0 T <
               utility_disc c res tol tol_pos A Action (destr s0) benefit r a x0 T) /\
  (forall acts a, In a acts -> destructive_at a s0 -> forall eps, 0 < eps ->
     exists T0, forall T, T0 <= T -> policy_survival c res tol tol_pos A s0 acts x0 T < eps).
Proof.
  intros c res tol tol_pos A s0 x0 benefit Hc Hres.
  repeat split.
  - intros q a T Hq HT; apply (presence_destruction_decays c Hc res Hres tol tol_pos A s0 q a x0 T Hq HT).
  - intros v a Hv Ha eps Heps; apply (concealment_must_be_perfect c Hc res Hres tol tol_pos A s0 v a x0 Hv Ha eps Heps).
  - intros K a Ha eps Heps; apply (patient_destruction_vanishes c Hc res Hres tol tol_pos A s0 K a x0 Ha eps Heps).
  - intros r p a Hr Hp Hbp H T;
      apply (time_preference_blocks_convergence c Hc res Hres tol tol_pos A s0 benefit r x0 p a Hr Hp Hbp H T).
  - intros acts a Hin Ha eps Heps;
      apply (destructive_policy_vanishes c Hc res Hres tol tol_pos A s0 acts a x0 Hin Ha eps Heps).
Qed.

Print Assumptions convergence_to_resource_preservation.
Print Assumptions beyond_the_thesis.
Print Assumptions two_level_equilibrium.
Print Assumptions nash_exists.
Print Assumptions frechet_bound.
Print Assumptions stellar_crossover.
Print Assumptions galactic_crossover.
Print Assumptions convergence_rational.
Print Assumptions stellar_crossover_rational.
Print Assumptions partial_forfeiture_crossover.
Print Assumptions self_preservation_necessary.
