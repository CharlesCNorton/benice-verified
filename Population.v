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
Variables phi delta b0 w cost : R.

(** A strategy fixes a player's act, its verdict on a preserver and its verdict on a persistent destroyer. *)
Record Strategy := mkStrategy { act : Action; on_preserver : Verdict; on_destroyer : Verdict }.

Definition nice (p : Action) : Strategy := mkStrategy p Ignore Punish.

(** A player's benefit sums the three decisions, punishing a preserver prevents nothing and punishing a destroyer prevents delta * T valued at w per unit; its one life survives all three judgments. *)
Definition total_benefit (s : Strategy) (T : R) : R :=
  benefit (act s) + judge_benefit b0 0 cost (on_preserver s) + judge_benefit b0 (w * (delta * T)) cost (on_destroyer s).

Definition total_survival (s : Strategy) (T : R) : R :=
  survival c res tol tol_pos A Action (destr s0) (act s) x0 T *
  survival c res tol tol_pos A Verdict (judge_offense phi 0) (on_preserver s) x0 T *
  survival c res tol tol_pos A Verdict (judge_offense phi (delta * T)) (on_destroyer s) x0 T.

Definition payoff (s : Strategy) (T : R) : R := total_benefit s T * total_survival s T.

(** Each decision's contribution is bounded by its best value, whatever the signs of the benefits. *)
Lemma payoff_bound : forall ba bP bD Sa SP bp cP cD,
  0 <= Sa <= 1 -> 0 <= SP <= 1 ->
  ba * Sa <= bp -> 0 <= bp -> bP * SP <= cP -> 0 <= cP -> bD <= cD -> 0 <= cD ->
  (ba + bP + bD) * Sa * SP <= bp + cP + cD.
Proof.
  intros ba bP bD Sa SP bp cP cD [HSa0 HSa1] [HSP0 HSP1] H1 Hbp H2 HcP H3 HcD.
  assert (HSS : 0 <= Sa * SP) by nra.
  assert (E1 : ba * Sa * SP <= bp).
  { destruct (Rle_dec (ba * Sa) 0) as [Hneg | Hpos].
    - assert (ba * Sa * SP <= 0) by nra. lra.
    - apply Rle_trans with (ba * Sa); [| exact H1].
      apply Rle_trans with (ba * Sa * 1); [apply Rmult_le_compat_l; lra | lra]. }
  assert (E2 : bP * Sa * SP <= cP).
  { destruct (Rle_dec bP 0) as [Hneg | Hpos].
    - assert (bP * Sa * SP <= 0) by nra. lra.
    - apply Rle_trans with (bP * SP); [| exact H2].
      replace (bP * Sa * SP) with (bP * SP * Sa) by ring.
      apply Rle_trans with (bP * SP * 1); [apply Rmult_le_compat_l; nra | lra]. }
  assert (E3 : bD * Sa * SP <= cD).
  { destruct (Rle_dec bD 0) as [Hneg | Hpos].
    - assert (bD * Sa * SP <= 0) by nra. lra.
    - apply Rle_trans with bD; [| exact H3].
      apply Rle_trans with (bD * 1); [| lra].
      replace (bD * Sa * SP) with (bD * (Sa * SP)) by ring.
      apply Rmult_le_compat_l; nra. }
  lra.
Qed.

Lemma payoff_bound_strict : forall ba bP bD Sa SP bp cP cD,
  0 <= Sa <= 1 -> 0 <= SP <= 1 ->
  ba * Sa <= bp -> 0 < bp -> bP * SP <= cP -> 0 < cP -> bD <= cD -> 0 <= cD ->
  (ba * Sa < bp \/ bP * SP < cP) ->
  (ba + bP + bD) * Sa * SP < bp + cP + cD.
Proof.
  intros ba bP bD Sa SP bp cP cD [HSa0 HSa1] [HSP0 HSP1] H1 Hbp H2 HcP H3 HcD Hstrict.
  assert (HSS : 0 <= Sa * SP) by nra.
  assert (E1 : ba * Sa * SP <= bp).
  { destruct (Rle_dec (ba * Sa) 0) as [Hneg | Hpos].
    - assert (ba * Sa * SP <= 0) by nra. lra.
    - apply Rle_trans with (ba * Sa); [| exact H1].
      apply Rle_trans with (ba * Sa * 1); [apply Rmult_le_compat_l; lra | lra]. }
  assert (E2 : bP * Sa * SP <= cP).
  { destruct (Rle_dec bP 0) as [Hneg | Hpos].
    - assert (bP * Sa * SP <= 0) by nra. lra.
    - apply Rle_trans with (bP * SP); [| exact H2].
      replace (bP * Sa * SP) with (bP * SP * Sa) by ring.
      apply Rle_trans with (bP * SP * 1); [apply Rmult_le_compat_l; nra | lra]. }
  assert (E3 : bD * Sa * SP <= cD).
  { destruct (Rle_dec bD 0) as [Hneg | Hpos].
    - assert (bD * Sa * SP <= 0) by nra. lra.
    - apply Rle_trans with bD; [| exact H3].
      apply Rle_trans with (bD * 1); [| lra].
      replace (bD * Sa * SP) with (bD * (Sa * SP)) by ring.
      apply Rmult_le_compat_l; nra. }
  assert (E1s : ba * Sa < bp -> ba * Sa * SP < bp).
  { intro H. destruct (Rle_dec (ba * Sa) 0) as [Hneg | Hpos].
    - assert (ba * Sa * SP <= 0) by nra. lra.
    - apply Rle_lt_trans with (ba * Sa); [| exact H].
      apply Rle_trans with (ba * Sa * 1); [apply Rmult_le_compat_l; lra | lra]. }
  assert (E2s : bP * SP < cP -> bP * Sa * SP < cP).
  { intro H. destruct (Rle_dec bP 0) as [Hneg | Hpos].
    - assert (bP * Sa * SP <= 0) by nra. lra.
    - apply Rle_lt_trans with (bP * SP); [| exact H].
      replace (bP * Sa * SP) with (bP * SP * Sa) by ring.
      apply Rle_trans with (bP * SP * 1); [apply Rmult_le_compat_l; nra | lra]. }
  destruct Hstrict as [H | H]; [specialize (E1s H) | specialize (E2s H)]; lra.
Qed.

(** When every other player is nice, being nice is a best response for a deep player, and deviating to a destructive act or to punishing preservers is strictly worse. *)
Theorem nice_is_nash : forall (menu : list Action) (p : Action),
  In p menu -> preserving_at p s0 -> 0 < benefit p ->
  (forall a, In a menu -> preserving_at a s0 -> benefit a <= benefit p) ->
  0 < phi -> 0 < delta -> 0 < b0 -> 0 < w ->
  exists Tstar, forall T, Tstar < T ->
    forall s, In (act s) menu ->
    payoff s T <= payoff (nice p) T /\
    ((destructive_at (act s) s0 \/ on_preserver s = Punish) -> payoff s T < payoff (nice p) T).
Proof.
  intros menu p Hin Hp Hbp Hbest Hphi Hd Hb0 Hw.
  destruct (deep_judges_spare_preservers c c_pos res res_pos tol tol_pos A phi b0 0 cost x0 Hphi Hb0)
    as [TJ HTJ].
  set (Tmenu := fold_right Rmax (T_min c res)
                  (map (pointwise_depth c res tol A Action (destr s0) benefit p) menu)).
  exists (Rmax (Rmax Tmenu TJ) (Rmax (phi / delta) (cost / (w * delta)))).
  intros T HT [a vP vD] Hs; cbn [act on_preserver on_destroyer] in *.
  assert (HTm : Tmenu < T).
  { eapply Rle_lt_trans; [| exact HT]. eapply Rle_trans; [apply Rmax_l | apply Rmax_l]. }
  assert (HTJ' : TJ < T).
  { eapply Rle_lt_trans; [| exact HT]. eapply Rle_trans; [apply Rmax_r | apply Rmax_l]. }
  assert (HTd : phi / delta <= T).
  { left; eapply Rle_lt_trans; [| exact HT]. eapply Rle_trans; [apply Rmax_l | apply Rmax_r]. }
  assert (HTc : cost / (w * delta) < T).
  { eapply Rle_lt_trans; [| exact HT]. eapply Rle_trans; [apply Rmax_r | apply Rmax_r]. }
  assert (Hgain : cost < w * (delta * T)) by (apply gain_exceeds_cost; assumption).
  unfold payoff, total_benefit, total_survival, nice; cbn [act on_preserver on_destroyer].
  rewrite (preservation_survives c res tol tol_pos A s0 p x0 T Hp).
  rewrite (survival_of_inoffensive c res tol tol_pos A Verdict (judge_offense phi 0) Ignore x0 T eq_refl).
  rewrite (survival_of_inoffensive c res tol tol_pos A Verdict (judge_offense phi (delta * T)) Punish x0 T
             (persistent_destroyer phi delta T Hd HTd)).
  assert (HSD : survival c res tol tol_pos A Verdict (judge_offense phi (delta * T)) vD x0 T = 1).
  { apply survival_of_inoffensive; destruct vD; [apply persistent_destroyer; assumption | reflexivity]. }
  rewrite HSD, !Rmult_1_r.
  set (Sa := survival c res tol tol_pos A Action (destr s0) a x0 T).
  set (SP := survival c res tol tol_pos A Verdict (judge_offense phi 0) vP x0 T).
  assert (HSa : 0 <= Sa <= 1).
  { split; [left; apply survival_pos | apply survival_le_1; exact (destr_nonneg s0)]. }
  assert (HSP : 0 <= SP <= 1).
  { split; [left; apply survival_pos | apply survival_le_1; exact (judge_offense_nonneg phi 0)]. }
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
  assert (HP : judge_benefit b0 0 cost vP * SP <= b0 /\
               (vP = Punish -> judge_benefit b0 0 cost vP * SP < b0)).
  { destruct vP.
    - assert (Hlt := HTJ T HTJ').
      rewrite (utility_of_inoffensive c res tol tol_pos A Verdict (judge_offense phi 0)
                 (judge_benefit b0 0 cost) Ignore x0 T eq_refl) in Hlt.
      unfold utility in Hlt; fold SP in Hlt; cbn [judge_benefit] in *.
      split; [left; exact Hlt | intros _; exact Hlt].
    - cbn [judge_benefit].
      assert (HSP1 : SP = 1) by (unfold SP; apply survival_of_inoffensive; reflexivity).
      rewrite HSP1, Rmult_1_r.
      split; [lra | intros H; discriminate H]. }
  destruct HP as [HPle HPstrict].
  assert (HD : judge_benefit b0 (w * (delta * T)) cost vD <= b0 + w * (delta * T) - cost).
  { destruct vD; cbn [judge_benefit]; lra. }
  assert (HcD : 0 <= b0 + w * (delta * T) - cost) by lra.
  cbn [judge_benefit].
  rewrite <- Rmult_assoc.
  split.
  - apply payoff_bound; try assumption; lra.
  - intros Hdev.
    apply payoff_bound_strict; try assumption; try lra.
    destruct Hdev as [Hdes | HPun]; [left; apply Hag_strict; exact Hdes | right; apply HPstrict; exact HPun].
Qed.

(** Every finite menu either holds a preserving action of maximal benefit among its preserving actions or holds none. *)
Lemma best_preserving : forall (menu : list Action),
  (exists best, In best menu /\ preserving_at best s0 /\
     forall a, In a menu -> preserving_at a s0 -> benefit a <= benefit best) \/
  (forall a, In a menu -> ~ preserving_at a s0).
Proof.
  induction menu as [| b rest IH].
  - right; intros a [].
  - destruct (Rle_dec (norm s0) (norm (b s0))) as [Hb | Hb].
    + destruct IH as [[best [Hin [Hpres Hmax]]] | Hnone].
      * destruct (Rle_dec (benefit b) (benefit best)) as [Hle | Hgt].
        -- left; exists best; split; [right; exact Hin | split; [exact Hpres |]].
           intros a [<- | Ha] Hpa; [exact Hle | apply Hmax; assumption].
        -- left; exists b; split; [left; reflexivity | split; [exact Hb |]].
           intros a [<- | Ha] Hpa; [apply Rle_refl |].
           apply Rle_trans with (benefit best); [apply Hmax; assumption | lra].
      * left; exists b; split; [left; reflexivity | split; [exact Hb |]].
        intros a [<- | Ha] Hpa; [apply Rle_refl | exfalso; exact (Hnone a Ha Hpa)].
    + destruct IH as [[best [Hin [Hpres Hmax]]] | Hnone].
      * left; exists best; split; [right; exact Hin | split; [exact Hpres |]].
        intros a [<- | Ha] Hpa; [exfalso; exact (Hb Hpa) | apply Hmax; assumption].
      * right; intros a [<- | Ha]; [exact Hb | exact (Hnone a Ha)].
Qed.

(** Any finite menu holding a preserving action of positive benefit holds one whose nice strategy is a Nash equilibrium at depth. *)
Theorem nash_exists : forall (menu : list Action),
  (exists p0, In p0 menu /\ preserving_at p0 s0 /\ 0 < benefit p0) ->
  0 < phi -> 0 < delta -> 0 < b0 -> 0 < w ->
  exists p, In p menu /\ preserving_at p s0 /\
  exists Tstar, forall T, Tstar < T ->
    forall s, In (act s) menu ->
    payoff s T <= payoff (nice p) T /\
    ((destructive_at (act s) s0 \/ on_preserver s = Punish) -> payoff s T < payoff (nice p) T).
Proof.
  intros menu [p0 [Hin0 [Hp0 Hb0']]] Hphi Hd Hb0 Hw.
  destruct (best_preserving menu) as [[p [Hin [Hp Hmax]]] | Hnone].
  - assert (Hbp : 0 < benefit p) by (apply Rlt_le_trans with (benefit p0); [exact Hb0' | apply Hmax; assumption]).
    exists p; split; [exact Hin | split; [exact Hp |]].
    apply nice_is_nash; assumption.
  - exfalso; exact (Hnone p0 Hin0 Hp0).
Qed.

End Population.
