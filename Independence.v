(** Independence: couplings of the judges, the Frechet bound, the independent and the perfectly dependent coupling. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.
From BeNice Require Import Vectors Actions Sums LightCone Survival.

(** * Section 12: The model's survival is the joint survival of the independent coupling; any coupling has joint survival at most one minus the largest marginal, and the perfectly dependent coupling attains it independently of the number of judges. *)

Record Coupling := mkCoupling {
  scen : list (R * list bool);
  scen_nonneg : forall ws, In ws scen -> 0 <= fst ws;
  scen_total : Rsum fst scen = 1
}.

Definition marginal (C : Coupling) (i : nat) : R :=
  Rsum (fun ws => if nth i (snd ws) false then fst ws else 0) (scen C).

Definition joint_survival (C : Coupling) : R :=
  Rsum (fun ws => if forallb negb (snd ws) then fst ws else 0) (scen C).

Lemma forallb_negb_nth : forall (s : list bool) i, forallb negb s = true -> nth i s false = false.
Proof.
  intros s i H.
  destruct (lt_dec i (length s)) as [Hlt | Hge].
  - rewrite forallb_forall in H.
    specialize (H (nth i s false) (nth_In s false Hlt)).
    destruct (nth i s false); [discriminate | reflexivity].
  - apply nth_overflow; lia.
Qed.

Theorem frechet_bound : forall C i, joint_survival C <= 1 - marginal C i.
Proof.
  intros C i; unfold joint_survival, marginal.
  rewrite <- (scen_total C), Rsum_minus.
  apply Rsum_le; intros ws Hws.
  assert (Hw := scen_nonneg C ws Hws).
  destruct (nth i (snd ws) false) eqn:E.
  - destruct (forallb negb (snd ws)) eqn:F; [| lra].
    rewrite forallb_negb_nth in E by exact F; discriminate.
  - destruct (forallb negb (snd ws)); lra.
Qed.

Fixpoint product_scen (e : list R) : list (R * list bool) :=
  match e with
  | [] => [(1, [])]
  | p :: rest =>
      flat_map (fun ws => [(p * fst ws, true :: snd ws); ((1 - p) * fst ws, false :: snd ws)])
               (product_scen rest)
  end.

Lemma product_scen_nonneg : forall e,
  (forall p, In p e -> 0 <= p <= 1) ->
  forall ws, In ws (product_scen e) -> 0 <= fst ws.
Proof.
  induction e as [| p rest IH]; intros He ws Hws.
  - simpl in Hws; destruct Hws as [<- | []]; simpl; lra.
  - change (product_scen (p :: rest)) with
      (flat_map (fun ws => [(p * fst ws, true :: snd ws); ((1 - p) * fst ws, false :: snd ws)])
                (product_scen rest)) in Hws.
    apply in_flat_map in Hws; destruct Hws as [ws' [Hws' Hin]].
    assert (Hp : 0 <= p <= 1) by (apply He; left; reflexivity).
    assert (Hw' : 0 <= fst ws') by (apply IH; [intros q Hq; apply He; right; exact Hq | exact Hws']).
    simpl in Hin; destruct Hin as [<- | [<- | []]]; simpl; nra.
Qed.

Lemma product_scen_total : forall e, Rsum fst (product_scen e) = 1.
Proof.
  induction e as [| p rest IH]; [simpl; ring |].
  change (product_scen (p :: rest)) with
    (flat_map (fun ws => [(p * fst ws, true :: snd ws); ((1 - p) * fst ws, false :: snd ws)])
              (product_scen rest)).
  rewrite Rsum_flat_map.
  rewrite (Rsum_ext _ fst); [exact IH |].
  intros ws _; unfold Rsum; simpl; ring.
Qed.

Lemma product_scen_survival : forall e,
  Rsum (fun ws => if forallb negb (snd ws) then fst ws else 0) (product_scen e) =
  Rprod (fun p => 1 - p) e.
Proof.
  induction e as [| p rest IH]; [simpl; ring |].
  change (product_scen (p :: rest)) with
    (flat_map (fun ws => [(p * fst ws, true :: snd ws); ((1 - p) * fst ws, false :: snd ws)])
              (product_scen rest)).
  rewrite Rsum_flat_map.
  rewrite (Rsum_ext _ (fun ws => (1 - p) * (if forallb negb (snd ws) then fst ws else 0))).
  - rewrite Rsum_scal_l, IH, Rprod_cons; reflexivity.
  - intros ws _; unfold Rsum; simpl.
    destruct (forallb negb (snd ws)); ring.
Qed.

Lemma product_scen_marginal : forall e i, (i < length e)%nat ->
  Rsum (fun ws => if nth i (snd ws) false then fst ws else 0) (product_scen e) = nth i e 0.
Proof.
  induction e as [| p rest IH]; intros i Hi; [simpl in Hi; lia |].
  change (product_scen (p :: rest)) with
    (flat_map (fun ws => [(p * fst ws, true :: snd ws); ((1 - p) * fst ws, false :: snd ws)])
              (product_scen rest)).
  rewrite Rsum_flat_map.
  destruct i as [| i'].
  - rewrite (Rsum_ext _ (fun ws => p * fst ws)).
    + rewrite Rsum_scal_l, product_scen_total; simpl; ring.
    + intros ws _; unfold Rsum; simpl; ring.
  - rewrite (Rsum_ext _ (fun ws => if nth i' (snd ws) false then fst ws else 0)).
    + apply IH; simpl in Hi; lia.
    + intros ws _; unfold Rsum; simpl. destruct (nth i' (snd ws) false); ring.
Qed.

Definition independent_coupling (e : list R) (He : forall p, In p e -> 0 <= p <= 1) : Coupling :=
  mkCoupling (product_scen e) (product_scen_nonneg e He) (product_scen_total e).

Theorem independent_marginals : forall e He i, (i < length e)%nat ->
  marginal (independent_coupling e He) i = nth i e 0.
Proof. intros e He i Hi; unfold marginal; simpl; apply product_scen_marginal; exact Hi. Qed.

Theorem independent_survival : forall e He,
  joint_survival (independent_coupling e He) = Rprod (fun p => 1 - p) e.
Proof. intros e He; unfold joint_survival; simpl; apply product_scen_survival. Qed.

(** The model's survival is the joint survival of the independent coupling. *)
Theorem survival_is_independent_coupling :
  forall c res tol tol_pos (A : Attenuation) (Act : Type) (offense : Act -> R) a x0 T He,
  survival c res tol tol_pos A Act offense a x0 T =
  joint_survival (independent_coupling
    (map (fun o => elim_prob A Act offense a o x0) (judges res tol tol_pos x0 (horizon_radius c T))) He).
Proof.
  intros; rewrite independent_survival, Rprod_map; reflexivity.
Qed.

(** The perfectly dependent coupling: with probability q every judge eliminates and otherwise none, so the marginals are q and the joint survival is 1 - q for any number of judges. *)
Lemma nth_repeat_lt : forall (b : bool) N i, (i < N)%nat -> nth i (repeat b N) false = b.
Proof.
  intros b N; induction N as [| N IH]; intros i Hi; [lia |].
  destruct i as [| i]; simpl; [reflexivity | apply IH; lia].
Qed.

Lemma forallb_negb_repeat_false : forall N, forallb negb (repeat false N) = true.
Proof. induction N as [| N IH]; [reflexivity | simpl; exact IH]. Qed.

Lemma forallb_negb_repeat_true : forall N, (1 <= N)%nat -> forallb negb (repeat true N) = false.
Proof. intros [| N] H; [lia | reflexivity]. Qed.

Definition all_or_nothing (q : R) (N : nat) (Hq : 0 <= q <= 1) : Coupling.
Proof.
  refine (mkCoupling [(q, repeat true N); (1 - q, repeat false N)] _ _).
  - intros ws Hws; simpl in Hws; destruct Hws as [<- | [<- | []]]; simpl; lra.
  - unfold Rsum; simpl; ring.
Defined.

Theorem all_or_nothing_marginals : forall q N Hq i, (i < N)%nat ->
  marginal (all_or_nothing q N Hq) i = q.
Proof.
  intros q N Hq i Hi; unfold marginal; simpl.
  rewrite !nth_repeat_lt by exact Hi. ring.
Qed.

Theorem all_or_nothing_survival : forall q N Hq, (1 <= N)%nat ->
  joint_survival (all_or_nothing q N Hq) = 1 - q.
Proof.
  intros q N Hq HN; unfold joint_survival; simpl.
  rewrite forallb_negb_repeat_true by exact HN.
  rewrite forallb_negb_repeat_false. ring.
Qed.

