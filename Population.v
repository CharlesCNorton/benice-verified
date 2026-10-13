(** The population game: every player is both agent and judge, and the strategy that preserves, spares preservers and punishes persistent destroyers is a Nash equilibrium at depth. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.
From BeNice Require Import Vectors Actions Sums LightCone Survival Resources Judges.

Section Population.

Variable c : R.
Hypothesis c_pos : 0 < c.
Variable res : R.
Hypothesis res_pos : 0 < res.
Variable tol : R.
Hypothesis tol_pos : 0 < tol.
Variable A : Attenuation.
Variable s0 x0 : Vec3.
Variable benefit : Action -> R.
Variables phi delta b0 gainP gain cost : R.

(** A strategy fixes a player's act, its verdict on a preserver and its verdict on a persistent destroyer. *)
Record Strategy := mkStrategy { act : Action; on_preserver : Verdict; on_destroyer : Verdict }.

Definition nice (p : Action) : Strategy := mkStrategy p Ignore Punish.

(** A player's benefit sums the three decisions; its one life survives all three judgments. *)
Definition total_benefit (s : Strategy) : R :=
  benefit (act s) + judge_benefit b0 gainP cost (on_preserver s) + judge_benefit b0 gain cost (on_destroyer s).

Definition total_survival (s : Strategy) (T : R) : R :=
  survival c res tol tol_pos A Action (destr s0) (act s) x0 T *
  survival c res tol tol_pos A Verdict (judge_offense phi 0) (on_preserver s) x0 T *
  survival c res tol tol_pos A Verdict (judge_offense phi (delta * T)) (on_destroyer s) x0 T.

Definition payoff (s : Strategy) (T : R) : R := total_benefit s * total_survival s T.

Lemma payoff_bound : forall ba bP bD Sa SP bp cP cD,
  0 <= ba -> 0 <= bP -> 0 <= bD -> 0 <= Sa <= 1 -> 0 <= SP <= 1 ->
  ba * Sa <= bp -> bP * SP <= cP -> bD <= cD ->
  (ba + bP + bD) * Sa * SP <= bp + cP + cD.
Proof.
  intros ba bP bD Sa SP bp cP cD Hba HbP HbD [HSa0 HSa1] [HSP0 HSP1] H1 H2 H3.
  assert (E1 : ba * Sa * SP <= ba * Sa).
  { apply Rle_trans with (ba * Sa * 1); [apply Rmult_le_compat_l; nra | lra]. }
  assert (E2 : bP * Sa * SP <= bP * SP).
  { replace (bP * Sa * SP) with (bP * SP * Sa) by ring.
    apply Rle_trans with (bP * SP * 1); [apply Rmult_le_compat_l; nra | lra]. }
  assert (E3 : bD * Sa * SP <= bD).
  { apply Rle_trans with (bD * Sa).
    - apply Rle_trans with (bD * Sa * 1); [apply Rmult_le_compat_l; nra | lra].
    - apply Rle_trans with (bD * 1); [apply Rmult_le_compat_l; lra | lra]. }
  lra.
Qed.

Lemma payoff_bound_strict : forall ba bP bD Sa SP bp cP cD,
  0 <= ba -> 0 <= bP -> 0 <= bD -> 0 <= Sa <= 1 -> 0 <= SP <= 1 ->
  ba * Sa <= bp -> bP * SP <= cP -> bD <= cD ->
  (ba * Sa < bp \/ bP * SP < cP) ->
  (ba + bP + bD) * Sa * SP < bp + cP + cD.
Proof.
  intros ba bP bD Sa SP bp cP cD Hba HbP HbD [HSa0 HSa1] [HSP0 HSP1] H1 H2 H3 Hstrict.
  assert (E1 : ba * Sa * SP <= ba * Sa).
  { apply Rle_trans with (ba * Sa * 1); [apply Rmult_le_compat_l; nra | lra]. }
  assert (E2 : bP * Sa * SP <= bP * SP).
  { replace (bP * Sa * SP) with (bP * SP * Sa) by ring.
    apply Rle_trans with (bP * SP * 1); [apply Rmult_le_compat_l; nra | lra]. }
  assert (E3 : bD * Sa * SP <= bD).
  { apply Rle_trans with (bD * Sa).
    - apply Rle_trans with (bD * Sa * 1); [apply Rmult_le_compat_l; nra | lra].
    - apply Rle_trans with (bD * 1); [apply Rmult_le_compat_l; lra | lra]. }
  destruct Hstrict; lra.
Qed.

(** When every other player is nice, being nice is a best response for a deep player, and any deviation to a destructive act or to punishing preservers is strictly worse. *)
Theorem nice_is_nash : forall (menu : list Action) (p : Action),
  In p menu -> preserving_at p s0 -> 0 < benefit p ->
  (forall a, In a menu -> 0 <= benefit a) ->
  (forall a, In a menu -> preserving_at a s0 -> benefit a <= benefit p) ->
  0 < phi -> 0 < delta -> 0 < b0 -> cost < gain -> 0 <= b0 + gainP - cost ->
  exists Tstar, forall T, Tstar < T ->
    forall s, In (act s) menu ->
    payoff s T <= payoff (nice p) T /\
    ((destructive_at (act s) s0 \/ on_preserver s = Punish) -> payoff s T < payoff (nice p) T).
Proof.
  intros menu p Hin Hp Hbp Hben Hbest Hphi Hd Hb0 Hgc HgP.
  destruct (deep_judges_spare_preservers c c_pos res res_pos tol tol_pos A phi b0 gainP cost x0 Hphi Hb0)
    as [TJ HTJ].
  set (Tmenu := fold_right Rmax (T_min c res)
                  (map (pointwise_depth c res tol A Action (destr s0) benefit p) menu)).
  exists (Rmax (Rmax Tmenu TJ) (phi / delta)).
  intros T HT [a vP vD] Hs; cbn [act on_preserver on_destroyer] in *.
  assert (HTm : Tmenu < T).
  { eapply Rle_lt_trans; [| exact HT]. eapply Rle_trans; [apply Rmax_l | apply Rmax_l]. }
  assert (HTJ' : TJ < T).
  { eapply Rle_lt_trans; [| exact HT]. eapply Rle_trans; [apply Rmax_r | apply Rmax_l]. }
  assert (HTd : phi / delta <= T) by (left; eapply Rle_lt_trans; [apply Rmax_r | exact HT]).
  unfold payoff, total_benefit, total_survival, nice; cbn [act on_preserver on_destroyer].
  (* the nice player survives with certainty *)
  rewrite (preservation_survives c res tol tol_pos A s0 p x0 T Hp).
  rewrite (survival_of_inoffensive c res tol tol_pos A Verdict (judge_offense phi 0) Ignore x0 T eq_refl).
  rewrite (survival_of_inoffensive c res tol tol_pos A Verdict (judge_offense phi (delta * T)) Punish x0 T
             (persistent_destroyer phi delta T Hd HTd)).
  (* the verdict on the destroyer is inoffensive either way *)
  assert (HSD : survival c res tol tol_pos A Verdict (judge_offense phi (delta * T)) vD x0 T = 1).
  { apply survival_of_inoffensive; destruct vD; [apply persistent_destroyer; assumption | reflexivity]. }
  rewrite HSD, !Rmult_1_r.
  set (Sa := survival c res tol tol_pos A Action (destr s0) a x0 T).
  set (SP := survival c res tol tol_pos A Verdict (judge_offense phi 0) vP x0 T).
  assert (HSa : 0 <= Sa <= 1).
  { split; [left; apply survival_pos | apply survival_le_1; exact (destr_nonneg s0)]. }
  assert (HSP : 0 <= SP <= 1).
  { split; [left; apply survival_pos | apply survival_le_1; exact (judge_offense_nonneg phi 0)]. }
  (* the agent component *)
  assert (Hagent : benefit a * Sa <= benefit p /\ (destructive_at a s0 -> benefit a * Sa < benefit p)).
  { destruct (Rlt_dec (norm (a s0)) (norm s0)) as [Hdes | Hndes].
    - assert (Hlt : utility c res tol tol_pos A Action (destr s0) benefit a x0 T <
                    utility c res tol tol_pos A Action (destr s0) benefit p x0 T).
      { apply (pointwise_crossover c c_pos res res_pos tol tol_pos A Action (destr s0) (destr_nonneg s0)
                 benefit x0 p a).
        - apply destr_zero_iff; exact Hp.
        - exact Hbp.
        - apply destr_pos_iff; exact Hdes.
        - eapply Rle_lt_trans; [| exact HTm].
          apply (fold_Rmax_ge (pointwise_depth c res tol A Action (destr s0) benefit p) (T_min c res) menu a Hs). }
      rewrite (utility_of_inoffensive c res tol tol_pos A Action (destr s0) benefit p x0 T
                 (proj2 (destr_zero_iff s0 p) Hp)) in Hlt.
      unfold utility in Hlt; fold Sa in Hlt.
      split; [left; exact Hlt | intros _; exact Hlt].
    - assert (Hpres : preserving_at a s0) by (unfold preserving_at; apply Rnot_lt_le; exact Hndes).
      assert (HSa1 : Sa = 1) by (unfold Sa; apply preservation_survives; exact Hpres).
      rewrite HSa1, Rmult_1_r.
      split; [apply Hbest; assumption | intros Hdes; exfalso; exact (Hndes Hdes)]. }
  destruct Hagent as [Hag Hag_strict].
  assert (Hba : 0 <= benefit a) by (apply Hben; exact Hs).
  (* the verdict on preservers *)
  assert (HP : 0 <= judge_benefit b0 gainP cost vP /\
               judge_benefit b0 gainP cost vP * SP <= b0 /\
               (vP = Punish -> judge_benefit b0 gainP cost vP * SP < b0)).
  { destruct vP.
    - assert (Hlt := HTJ T HTJ').
      rewrite (utility_of_inoffensive c res tol tol_pos A Verdict (judge_offense phi 0)
                 (judge_benefit b0 gainP cost) Ignore x0 T eq_refl) in Hlt.
      unfold utility in Hlt; fold SP in Hlt; cbn [judge_benefit] in *.
      split; [exact HgP | split; [left; exact Hlt | intros _; exact Hlt]].
    - cbn [judge_benefit].
      assert (HSP1 : SP = 1) by (unfold SP; apply survival_of_inoffensive; reflexivity).
      rewrite HSP1, Rmult_1_r.
      split; [lra | split; [lra | intros H; discriminate H]]. }
  destruct HP as [HbP [HPle HPstrict]].
  (* the verdict on destroyers *)
  assert (HD : 0 <= judge_benefit b0 gain cost vD /\ judge_benefit b0 gain cost vD <= b0 + gain - cost).
  { destruct vD; cbn [judge_benefit]; split; lra. }
  destruct HD as [HbD HDle].
  cbn [judge_benefit].
  rewrite <- Rmult_assoc.
  split.
  - apply payoff_bound; assumption.
  - intros Hdev.
    apply payoff_bound_strict; try assumption.
    destruct Hdev as [Hdes | HPun]; [left; apply Hag_strict; exact Hdes | right; apply HPstrict; exact HPun].
Qed.

End Population.
