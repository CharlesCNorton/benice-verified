(** Actions on the resource state and the destruction of an event. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.
From BeNice Require Import Vectors.

(** * Section 2: An action maps the resource state to a new state; the destruction of the event is the drop in norm clamped at zero, so scaling by f destroys the fraction 1 - f. *)

Definition Action : Type := Vec3 -> Vec3.

Definition identity_action : Action := fun s => s.

Definition compose (a1 a2 : Action) : Action := fun s => a1 (a2 s).

Definition scale_action (f : R) : Action := fun s => vscale f s.

Definition annihilate : Action := fun _ => vzero.

Definition destruction (a : Action) (s : Vec3) : R := Rmax 0 (norm s - norm (a s)).

Definition preserving_at (a : Action) (s : Vec3) : Prop := norm s <= norm (a s).

Definition destructive_at (a : Action) (s : Vec3) : Prop := norm (a s) < norm s.

Definition preserving (a : Action) : Prop := forall s, preserving_at a s.

Lemma destruction_nonneg : forall a s, 0 <= destruction a s.
Proof. intros; apply Rmax_l. Qed.

Lemma destruction_le_norm : forall a s, destruction a s <= norm s.
Proof.
  intros a s; unfold destruction.
  assert (H := norm_nonneg (a s)); assert (H' := norm_nonneg s).
  apply Rmax_lub; lra.
Qed.

Lemma destruction_zero_iff : forall a s, destruction a s = 0 <-> preserving_at a s.
Proof.
  intros a s; unfold destruction, preserving_at; split; intro H.
  - destruct (Rle_dec (norm s - norm (a s)) 0) as [Hle | Hgt]; [lra |].
    rewrite Rmax_right in H by lra. lra.
  - apply Rmax_left; lra.
Qed.

Lemma destruction_pos_iff : forall a s, 0 < destruction a s <-> destructive_at a s.
Proof.
  intros a s; unfold destruction, destructive_at; split; intro H.
  - destruct (Rle_dec (norm s - norm (a s)) 0) as [Hle | Hgt].
    + rewrite Rmax_left in H by lra. lra.
    + lra.
  - rewrite Rmax_right by lra. lra.
Qed.

Lemma destruction_of_preserving : forall a s, preserving a -> destruction a s = 0.
Proof. intros a s H; apply destruction_zero_iff; apply H. Qed.

Lemma identity_preserving : preserving identity_action.
Proof. intros s; unfold preserving_at, identity_action; lra. Qed.

Lemma compose_preserving : forall a1 a2,
  preserving a1 -> preserving a2 -> preserving (compose a1 a2).
Proof.
  intros a1 a2 H1 H2 s; unfold preserving_at, compose.
  apply Rle_trans with (norm (a2 s)); [apply H2 | apply H1].
Qed.

Lemma destruction_identity : forall s, destruction identity_action s = 0.
Proof. intros s; apply destruction_of_preserving, identity_preserving. Qed.

Lemma destruction_scale : forall f s, 0 <= f <= 1 ->
  destruction (scale_action f) s = (1 - f) * norm s.
Proof.
  intros f s [Hf0 Hf1]; unfold destruction, scale_action.
  rewrite norm_scale_nonneg by exact Hf0.
  assert (H := norm_nonneg s).
  rewrite Rmax_right by nra. ring.
Qed.

Lemma destruction_annihilate : forall s, destruction annihilate s = norm s.
Proof.
  intros s; unfold destruction, annihilate.
  rewrite norm_vzero.
  assert (H := norm_nonneg s).
  rewrite Rmax_right by lra. ring.
Qed.

Lemma destruction_monotone : forall a1 a2 s,
  norm (a1 s) <= norm (a2 s) -> destruction a2 s <= destruction a1 s.
Proof.
  intros a1 a2 s H; unfold destruction.
  apply Rmax_lub; [apply Rmax_l |].
  apply Rle_trans with (norm s - norm (a1 s)); [lra | apply Rmax_r].
Qed.

