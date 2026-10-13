(******************************************************************************)
(*                                                                            *)
(*     Convergence to Resource Preservation in Delayed Elimination Games      *)
(*                                                                            *)
(*     "Ua mau ke ea o ka ʻāina i ka pono"                                    *)
(*     (The life of the land is perpetuated in righteousness)                 *)
(*     - King Kamehameha III, July 31, 1843 (Hawaii State Motto)              *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: October 13, 2026                                                 *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.

(** * Section 1: Vectors, Norm, Metric *)

Definition Vec3 : Type := (R * R * R)%type.

Definition vzero : Vec3 := (0, 0, 0).

Definition vadd (u v : Vec3) : Vec3 :=
  let '(x1, y1, z1) := u in
  let '(x2, y2, z2) := v in
  (x1 + x2, y1 + y2, z1 + z2).

Definition vsub (u v : Vec3) : Vec3 :=
  let '(x1, y1, z1) := u in
  let '(x2, y2, z2) := v in
  (x1 - x2, y1 - y2, z1 - z2).

Definition vscale (k : R) (v : Vec3) : Vec3 :=
  let '(x, y, z) := v in (k * x, k * y, k * z).

Definition dot (u v : Vec3) : R :=
  let '(x1, y1, z1) := u in
  let '(x2, y2, z2) := v in
  x1 * x2 + y1 * y2 + z1 * z2.

Definition sqnorm (v : Vec3) : R :=
  let '(x, y, z) := v in x * x + y * y + z * z.

Definition norm (v : Vec3) : R := sqrt (sqnorm v).

Lemma sqnorm_nonneg : forall v, 0 <= sqnorm v.
Proof. intros [[x y] z]; simpl; nra. Qed.

Lemma norm_nonneg : forall v, 0 <= norm v.
Proof. intros v; apply sqrt_pos. Qed.

Lemma norm_sq : forall v, norm v * norm v = sqnorm v.
Proof. intros v; apply sqrt_sqrt, sqnorm_nonneg. Qed.

Lemma norm_vzero : norm vzero = 0.
Proof.
  unfold norm, vzero; simpl.
  replace (0 * 0 + 0 * 0 + 0 * 0) with 0 by ring.
  apply sqrt_0.
Qed.

Lemma vsub_self : forall v, vsub v v = vzero.
Proof. intros [[x y] z]; unfold vsub, vzero; f_equal; [f_equal|]; ring. Qed.

Lemma norm_sub_sym : forall u v, norm (vsub u v) = norm (vsub v u).
Proof.
  intros [[x1 y1] z1] [[x2 y2] z2]; unfold norm, vsub; simpl; f_equal; ring.
Qed.

Lemma norm_scale : forall k v, norm (vscale k v) = Rabs k * norm v.
Proof.
  intros k [[x y] z]; unfold norm, vscale; simpl.
  replace (k * x * (k * x) + k * y * (k * y) + k * z * (k * z))
    with ((k * k) * (x * x + y * y + z * z)) by ring.
  rewrite sqrt_mult_alt by nra.
  f_equal.
  rewrite <- Rsqr_def, sqrt_Rsqr_abs.
  reflexivity.
Qed.

Lemma norm_scale_nonneg : forall k v, 0 <= k -> norm (vscale k v) = k * norm v.
Proof. intros k v Hk; rewrite norm_scale, Rabs_right; lra. Qed.

(** Cauchy-Schwarz through Lagrange's identity. *)
Lemma cauchy_schwarz : forall u v, dot u v <= norm u * norm v.
Proof.
  intros [[x1 y1] z1] [[x2 y2] z2].
  unfold dot, norm; simpl.
  set (A := x1 * x1 + y1 * y1 + z1 * z1).
  set (B := x2 * x2 + y2 * y2 + z2 * z2).
  set (D := x1 * x2 + y1 * y2 + z1 * z2).
  assert (HA : 0 <= A) by (unfold A; nra).
  assert (HB : 0 <= B) by (unfold B; nra).
  assert (Hlag : D * D <= A * B).
  { assert (E : D * D + ((x1 * y2 - x2 * y1) * (x1 * y2 - x2 * y1)
                        + (x1 * z2 - x2 * z1) * (x1 * z2 - x2 * z1)
                        + (y1 * z2 - y2 * z1) * (y1 * z2 - y2 * z1)) = A * B)
      by (unfold A, B, D; ring).
    assert (H1 := Rle_0_sqr (x1 * y2 - x2 * y1)).
    assert (H2 := Rle_0_sqr (x1 * z2 - x2 * z1)).
    assert (H3 := Rle_0_sqr (y1 * z2 - y2 * z1)).
    unfold Rsqr in H1, H2, H3.
    lra. }
  rewrite <- sqrt_mult_alt by exact HA.
  destruct (Rle_dec D 0) as [HD | HD].
  - apply Rle_trans with 0; [exact HD | apply sqrt_pos].
  - apply Rnot_le_lt in HD.
    rewrite <- (sqrt_Rsqr D) by lra.
    apply sqrt_le_1; [apply Rle_0_sqr | nra | unfold Rsqr; exact Hlag].
Qed.

Lemma sqnorm_vadd : forall u v, sqnorm (vadd u v) = sqnorm u + 2 * dot u v + sqnorm v.
Proof. intros [[x1 y1] z1] [[x2 y2] z2]; unfold sqnorm, vadd, dot; simpl; ring. Qed.

Lemma norm_triangle : forall u v, norm (vadd u v) <= norm u + norm v.
Proof.
  intros u v.
  apply Rsqr_incr_0_var.
  - unfold Rsqr.
    rewrite norm_sq, sqnorm_vadd.
    assert (H := cauchy_schwarz u v).
    assert (Hu := norm_sq u). assert (Hv := norm_sq v).
    nra.
  - apply Rplus_le_le_0_compat; apply norm_nonneg.
Qed.

Lemma vsub_vadd_cancel : forall u v, vadd (vsub u v) v = u.
Proof. intros [[x1 y1] z1] [[x2 y2] z2]; unfold vadd, vsub; f_equal; [f_equal|]; ring. Qed.

Lemma vsub_vsub : forall u v w, vsub u w = vadd (vsub u v) (vsub v w).
Proof. intros [[a b] c] [[d e] f] [[g h] i]; unfold vadd, vsub; f_equal; [f_equal|]; ring. Qed.

(** The metric axioms for the Euclidean norm. *)
Theorem norm_metric :
  (forall u v w, norm (vsub u w) <= norm (vsub u v) + norm (vsub v w)) /\
  (forall u v, norm (vsub u v) = norm (vsub v u)) /\
  (forall u, norm (vsub u u) = 0) /\
  (forall u, 0 <= norm u).
Proof.
  repeat split.
  - intros u v w; rewrite (vsub_vsub u v w); apply norm_triangle.
  - apply norm_sub_sym.
  - intros u; rewrite vsub_self; apply norm_vzero.
  - apply norm_nonneg.
Qed.

(** Reverse triangle inequality. *)
Lemma norm_reverse_triangle : forall u v, norm u - norm v <= norm (vsub u v).
Proof.
  intros u v.
  assert (H := norm_triangle (vsub u v) v).
  rewrite vsub_vadd_cancel in H.
  lra.
Qed.

Lemma norm_reverse_triangle_abs : forall u v, Rabs (norm u - norm v) <= norm (vsub u v).
Proof.
  intros u v.
  apply Rabs_le; split.
  - rewrite norm_sub_sym.
    assert (H := norm_reverse_triangle v u). lra.
  - apply norm_reverse_triangle.
Qed.

Lemma sqrt3_pos : 0 < sqrt 3.
Proof. apply sqrt_lt_R0; lra. Qed.

Lemma sqrt3_lt_2 : sqrt 3 < 2.
Proof.
  rewrite <- (sqrt_Rsqr 2) by lra.
  apply sqrt_lt_1; [lra | unfold Rsqr; lra | unfold Rsqr; lra].
Qed.

Lemma sqrt3_sq : sqrt 3 * sqrt 3 = 3.
Proof. apply sqrt_sqrt; lra. Qed.

(** A point of the cube of half-side M lies in the ball of radius M * sqrt 3. *)
Lemma cube_in_ball : forall x y z M,
  Rabs x <= M -> Rabs y <= M -> Rabs z <= M ->
  norm (x, y, z) <= M * sqrt 3.
Proof.
  intros x y z M Hx Hy Hz.
  assert (HM : M >= 0)
    by (apply Rle_ge; apply Rle_trans with (Rabs x); [apply Rabs_pos | exact Hx]).
  assert (HabsM : Rabs M = M) by (apply Rabs_right; exact HM).
  apply Rsqr_incr_0_var.
  - unfold Rsqr.
    rewrite norm_sq; simpl.
    assert (Hx2 : Rsqr x <= Rsqr M) by (apply Rsqr_le_abs_1; rewrite HabsM; exact Hx).
    assert (Hy2 : Rsqr y <= Rsqr M) by (apply Rsqr_le_abs_1; rewrite HabsM; exact Hy).
    assert (Hz2 : Rsqr z <= Rsqr M) by (apply Rsqr_le_abs_1; rewrite HabsM; exact Hz).
    unfold Rsqr in Hx2, Hy2, Hz2.
    replace (M * sqrt 3 * (M * sqrt 3)) with (M * M * (sqrt 3 * sqrt 3)) by ring.
    rewrite sqrt3_sq. lra.
  - apply Rmult_le_pos; [apply Rge_le; exact HM | apply sqrt_pos].
Qed.

(** The l1 norm is at most sqrt 3 times the Euclidean norm. *)
Lemma l1_le_sqrt3_norm : forall x y z,
  Rabs x + Rabs y + Rabs z <= sqrt 3 * norm (x, y, z).
Proof.
  intros x y z.
  set (a := Rabs x). set (b := Rabs y). set (d := Rabs z).
  assert (Ha : 0 <= a) by apply Rabs_pos.
  assert (Hb : 0 <= b) by apply Rabs_pos.
  assert (Hd : 0 <= d) by apply Rabs_pos.
  assert (Hsq : (a + b + d) * (a + b + d) <= 3 * (x * x + y * y + z * z)).
  { assert (Ea : a * a = x * x) by (unfold a; change (Rsqr (Rabs x) = Rsqr x); symmetry; apply Rsqr_abs).
    assert (Eb : b * b = y * y) by (unfold b; change (Rsqr (Rabs y) = Rsqr y); symmetry; apply Rsqr_abs).
    assert (Ed : d * d = z * z) by (unfold d; change (Rsqr (Rabs z) = Rsqr z); symmetry; apply Rsqr_abs).
    assert (S1 := Rle_0_sqr (a - b)).
    assert (S2 := Rle_0_sqr (b - d)).
    assert (S3 := Rle_0_sqr (a - d)).
    unfold Rsqr in S1, S2, S3.
    rewrite <- Ea, <- Eb, <- Ed.
    lra. }
  apply Rsqr_incr_0_var.
  - unfold Rsqr.
    replace (sqrt 3 * norm (x, y, z) * (sqrt 3 * norm (x, y, z)))
      with ((sqrt 3 * sqrt 3) * (norm (x, y, z) * norm (x, y, z))) by ring.
    rewrite sqrt3_sq, norm_sq. simpl. exact Hsq.
  - apply Rmult_le_pos; [apply sqrt_pos | apply norm_nonneg].
Qed.

(** * Section 2: Actions and the Destruction of an Event

    An action maps the resource state of the world to a new resource state.
    The event is the pair (state before, state after); its destruction is the
    drop in resources it causes, clamped at zero. This is the quantity judges
    perceive, and it is finite and informative: scaling the resources by a
    factor f destroys the fraction (1 - f) of them. *)

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

(** * Section 3: Finite Sums and Products *)

Definition Rsum {A : Type} (f : A -> R) (l : list A) : R :=
  fold_right (fun x acc => f x + acc) 0 l.

Definition Rprod {A : Type} (f : A -> R) (l : list A) : R :=
  fold_right (fun x acc => f x * acc) 1 l.

Section Sums.
Context {A : Type}.

Lemma Rsum_nil : forall (f : A -> R), Rsum f [] = 0.
Proof. reflexivity. Qed.

Lemma Rsum_cons : forall (f : A -> R) x l, Rsum f (x :: l) = f x + Rsum f l.
Proof. reflexivity. Qed.

Lemma Rsum_app : forall (f : A -> R) l1 l2, Rsum f (l1 ++ l2) = Rsum f l1 + Rsum f l2.
Proof.
  intros f l1 l2; induction l1 as [| x l1 IH]; simpl; [ring |].
  unfold Rsum in *; simpl; rewrite IH; ring.
Qed.

Lemma Rsum_ext : forall (f g : A -> R) l,
  (forall x, In x l -> f x = g x) -> Rsum f l = Rsum g l.
Proof.
  intros f g l H; induction l as [| x l IH]; [reflexivity |].
  rewrite !Rsum_cons, (H x (or_introl eq_refl)), IH; [reflexivity |].
  intros y Hy; apply H; right; exact Hy.
Qed.

Lemma Rsum_le : forall (f g : A -> R) l,
  (forall x, In x l -> f x <= g x) -> Rsum f l <= Rsum g l.
Proof.
  intros f g l H; induction l as [| x l IH]; [simpl; lra |].
  rewrite !Rsum_cons.
  assert (Hx := H x (or_introl eq_refl)).
  assert (IH' : Rsum f l <= Rsum g l) by (apply IH; intros y Hy; apply H; right; exact Hy).
  lra.
Qed.

Lemma Rsum_nonneg : forall (f : A -> R) l,
  (forall x, In x l -> 0 <= f x) -> 0 <= Rsum f l.
Proof.
  intros f l H; induction l as [| x l IH]; [simpl; lra |].
  rewrite Rsum_cons.
  assert (Hx := H x (or_introl eq_refl)).
  assert (IH' : 0 <= Rsum f l) by (apply IH; intros y Hy; apply H; right; exact Hy).
  lra.
Qed.

Lemma Rsum_scal_l : forall (f : A -> R) (k : R) l,
  Rsum (fun x => k * f x) l = k * Rsum f l.
Proof.
  intros f k l; induction l as [| x l IH]; [simpl; ring |].
  rewrite !Rsum_cons, IH; ring.
Qed.

Lemma Rsum_const : forall (k : R) l, Rsum (fun _ : A => k) l = INR (length l) * k.
Proof.
  intros k l; induction l as [| x l IH]; [simpl; ring |].
  rewrite Rsum_cons, IH; simpl length; rewrite S_INR; ring.
Qed.

Lemma Rsum_ge_const : forall (f : A -> R) (k : R) l,
  (forall x, In x l -> k <= f x) -> INR (length l) * k <= Rsum f l.
Proof.
  intros f k l H; rewrite <- (Rsum_const k l); apply Rsum_le; exact H.
Qed.

Lemma Rsum_le_const : forall (f : A -> R) (k : R) l,
  (forall x, In x l -> f x <= k) -> Rsum f l <= INR (length l) * k.
Proof.
  intros f k l H; rewrite <- (Rsum_const k l); apply Rsum_le; exact H.
Qed.

Lemma Rsum_if : forall (f : A -> R) (b : bool) (x : A),
  Rsum f (if b then [x] else []) = if b then f x else 0.
Proof. intros f [|] x; simpl; ring. Qed.

Lemma Rprod_nil : forall (f : A -> R), Rprod f [] = 1.
Proof. reflexivity. Qed.

Lemma Rprod_cons : forall (f : A -> R) x l, Rprod f (x :: l) = f x * Rprod f l.
Proof. reflexivity. Qed.

Lemma Rprod_ext : forall (f g : A -> R) l,
  (forall x, In x l -> f x = g x) -> Rprod f l = Rprod g l.
Proof.
  intros f g l H; induction l as [| x l IH]; [reflexivity |].
  rewrite !Rprod_cons, (H x (or_introl eq_refl)), IH; [reflexivity |].
  intros y Hy; apply H; right; exact Hy.
Qed.

Lemma Rprod_exp : forall (g : A -> R) l, Rprod (fun x => exp (g x)) l = exp (Rsum g l).
Proof.
  intros g l; induction l as [| x l IH]; [simpl; rewrite exp_0; reflexivity |].
  rewrite Rprod_cons, Rsum_cons, IH, exp_plus; reflexivity.
Qed.

Lemma Rprod_nonneg : forall (f : A -> R) l,
  (forall x, In x l -> 0 <= f x) -> 0 <= Rprod f l.
Proof.
  intros f l H; induction l as [| x l IH]; [simpl; lra |].
  rewrite Rprod_cons.
  apply Rmult_le_pos; [apply H; left; reflexivity |].
  apply IH; intros y Hy; apply H; right; exact Hy.
Qed.

Lemma Rprod_le_1 : forall (f : A -> R) l,
  (forall x, In x l -> 0 <= f x <= 1) -> Rprod f l <= 1.
Proof.
  intros f l H; induction l as [| x l IH]; [simpl; lra |].
  rewrite Rprod_cons.
  assert (Hx := H x (or_introl eq_refl)).
  assert (Hrest : forall y, In y l -> 0 <= f y <= 1) by (intros y Hy; apply H; right; exact Hy).
  assert (H0 := Rprod_nonneg f l (fun y Hy => proj1 (Hrest y Hy))).
  assert (H1 := IH Hrest).
  nra.
Qed.

Lemma Rprod_le : forall (f g : A -> R) l,
  (forall x, In x l -> 0 <= f x <= g x) -> Rprod f l <= Rprod g l.
Proof.
  intros f g l H; induction l as [| x l IH]; [simpl; lra |].
  rewrite !Rprod_cons.
  assert (Hx := H x (or_introl eq_refl)).
  assert (Hrest : forall y, In y l -> 0 <= f y <= g y) by (intros y Hy; apply H; right; exact Hy).
  assert (H0 := Rprod_nonneg f l (fun y Hy => proj1 (Hrest y Hy))).
  assert (H1 := IH Hrest).
  apply Rmult_le_compat; lra.
Qed.

Lemma Rprod_bounded : forall (f : A -> R) l,
  (forall x, In x l -> 0 <= f x <= 1) -> 0 <= Rprod f l <= 1.
Proof.
  intros f l H; split.
  - apply Rprod_nonneg; intros x Hx; apply (H x Hx).
  - apply Rprod_le_1; exact H.
Qed.

End Sums.

Lemma Rprod_one : forall {A : Type} (l : list A), Rprod (fun _ => 1) l = 1.
Proof. intros A l; induction l as [| x l IH]; [reflexivity |]. rewrite Rprod_cons, IH; ring. Qed.

Lemma cube_le : forall x y, 0 <= x <= y -> x * x * x <= y * y * y.
Proof.
  intros x y [Hx Hxy].
  assert (Hy : 0 <= y) by lra.
  apply Rle_trans with (x * x * y); [apply Rmult_le_compat_l; [nra | exact Hxy] |].
  apply Rle_trans with (x * y * y).
  - replace (x * x * y) with (x * y * x) by ring. apply Rmult_le_compat_l; [nra | exact Hxy].
  - replace (x * y * y) with (y * y * x) by ring. apply Rmult_le_compat_l; [nra | exact Hxy].
Qed.

Lemma Rsum_minus : forall {A : Type} (f g : A -> R) l,
  Rsum f l - Rsum g l = Rsum (fun x => f x - g x) l.
Proof.
  intros A f g l; induction l as [| x l IH]; [simpl; ring |].
  rewrite !Rsum_cons, <- IH; ring.
Qed.

Lemma Rprod_map : forall {A B : Type} (f : B -> R) (g : A -> B) l,
  Rprod f (map g l) = Rprod (fun x => f (g x)) l.
Proof.
  intros A B f g l; induction l as [| y l IH]; [reflexivity |].
  change (map g (y :: l)) with (g y :: map g l).
  rewrite !Rprod_cons, IH; reflexivity.
Qed.

Lemma Rsum_map : forall {A B : Type} (f : B -> R) (g : A -> B) l,
  Rsum f (map g l) = Rsum (fun x => f (g x)) l.
Proof.
  intros A B f g l; induction l as [| y l IH]; [reflexivity |].
  change (map g (y :: l)) with (g y :: map g l).
  rewrite !Rsum_cons, IH; reflexivity.
Qed.

Lemma Rsum_flat_map : forall {A B : Type} (f : B -> R) (g : A -> list B) l,
  Rsum f (flat_map g l) = Rsum (fun x => Rsum f (g x)) l.
Proof.
  intros A B f g l; induction l as [| x l IH]; [reflexivity |].
  change (flat_map g (x :: l)) with (g x ++ flat_map g l).
  rewrite Rsum_app, Rsum_cons, IH; reflexivity.
Qed.

(** Sums over integer ranges. *)

Lemma Rsum_seq_shift : forall (f : nat -> R) (d len : nat),
  Rsum (fun i => f (i + d)%nat) (seq 0 len) = Rsum f (seq d len).
Proof.
  intros f d len; revert d; induction len as [| len IH]; intros d; [reflexivity |].
  change (seq 0 (S len)) with (0%nat :: seq 1 len).
  change (seq d (S len)) with (d :: seq (S d) len).
  rewrite !Rsum_cons.
  rewrite <- (seq_shift len 0), Rsum_map.
  rewrite <- (IH (S d)).
  cbv beta.
  apply Rplus_eq_compat_l.
  apply Rsum_ext; intros i _; f_equal; lia.
Qed.

(** A sum of non-negative terms over a sub-range is bounded by the sum over the range. *)
Lemma Rsum_seq_sub : forall (f : nat -> R) (a b len : nat),
  (a + b <= len)%nat ->
  (forall i, (i < len)%nat -> 0 <= f i) ->
  Rsum f (seq a b) <= Rsum f (seq 0 len).
Proof.
  intros f a b len Hab Hpos.
  replace len with (a + b + (len - a - b))%nat by lia.
  rewrite seq_app, Rsum_app, seq_app, Rsum_app.
  rewrite !Nat.add_0_l.
  assert (H1 : 0 <= Rsum f (seq 0 a)).
  { apply Rsum_nonneg; intros i Hi; apply in_seq in Hi; apply Hpos; lia. }
  assert (H2 : 0 <= Rsum f (seq (a + b) (len - a - b))).
  { apply Rsum_nonneg; intros i Hi; apply in_seq in Hi; apply Hpos; lia. }
  lra.
Qed.

Lemma Rsum_seq_shift_sub : forall (f : nat -> R) (d len len2 : nat),
  (d + len <= len2)%nat ->
  (forall i, (i < len2)%nat -> 0 <= f i) ->
  Rsum (fun i => f (i + d)%nat) (seq 0 len) <= Rsum f (seq 0 len2).
Proof. intros f d len len2 H Hf; rewrite Rsum_seq_shift; apply Rsum_seq_sub; assumption. Qed.

Lemma up_monotone : forall x y, x <= y -> (up x <= up y)%Z.
Proof.
  intros x y H.
  destruct (archimed x) as [H1 H2]. destruct (archimed y) as [H3 H4].
  assert (Hlt : (up x < up y + 1)%Z) by (apply lt_IZR; rewrite plus_IZR; lra).
  lia.
Qed.

(** Finite geometric sums. *)
Lemma geometric_sum_closed : forall q len,
  (1 - q) * Rsum (fun i => q ^ i) (seq 0 len) = 1 - q ^ len.
Proof.
  intros q len; induction len as [| len IH]; [simpl; ring |].
  rewrite seq_S, Rsum_app, Rsum_cons, Rsum_nil, Nat.add_0_l.
  cbv beta.
  rewrite Rmult_plus_distr_l, IH.
  simpl; ring.
Qed.

Lemma geometric_sum_bound : forall q len,
  0 <= q < 1 -> Rsum (fun i => q ^ i) (seq 0 len) <= / (1 - q).
Proof.
  intros q len [Hq0 Hq1].
  assert (Hc := geometric_sum_closed q len).
  assert (Hpow : 0 <= q ^ len) by (apply pow_le; exact Hq0).
  assert (H1q : 0 < 1 - q) by lra.
  apply Rmult_le_reg_l with (1 - q); [exact H1q |].
  rewrite Hc, Rinv_r by lra. lra.
Qed.

(** The two-sided sum of q^|i - n| over i in [0, 2n]. *)
Definition ndist (i n : nat) : nat := (i - n) + (n - i).

Lemma ndist_ge : forall i n, (n <= i)%nat -> ndist i n = (i - n)%nat.
Proof. intros; unfold ndist; lia. Qed.

Lemma ndist_le : forall i n, (i <= n)%nat -> ndist i n = (n - i)%nat.
Proof. intros; unfold ndist; lia. Qed.

Lemma reflected_geometric_sum : forall q n,
  Rsum (fun i => q ^ (n - i)) (seq 0 n) = Rsum (fun u => q ^ (S u)) (seq 0 n).
Proof.
  intros q n; induction n as [| n IH]; [reflexivity |].
  transitivity (q ^ (S n) + Rsum (fun i => q ^ (n - i)) (seq 0 n)).
  - change (seq 0 (S n)) with (0%nat :: seq 1 n).
    rewrite Rsum_cons, <- (seq_shift n 0), Rsum_map.
    cbv beta.
    apply Rplus_eq_compat_l.
    apply Rsum_ext; intros i _; f_equal; lia.
  - rewrite IH, (seq_S n 0), Rsum_app, Rsum_cons, Rsum_nil, Nat.add_0_l.
    cbv beta. ring.
Qed.

Lemma two_sided_geometric_bound : forall q n,
  0 <= q < 1 ->
  Rsum (fun i => q ^ (ndist i n)) (seq 0 (2 * n + 1)) <= 2 / (1 - q).
Proof.
  intros q n Hq.
  replace (2 * n + 1)%nat with (n + (n + 1))%nat by lia.
  rewrite seq_app, Rsum_app, Nat.add_0_l.
  assert (HA : Rsum (fun i => q ^ ndist i n) (seq 0 n) <= / (1 - q)).
  { rewrite (Rsum_ext (fun i => q ^ ndist i n) (fun i => q ^ (n - i)) (seq 0 n)).
    - rewrite reflected_geometric_sum.
      apply Rle_trans with (Rsum (fun u => q ^ u) (seq 0 n)).
      + apply Rsum_le; intros u _; simpl.
        assert (0 <= q ^ u) by (apply pow_le; lra). nra.
      + apply geometric_sum_bound; exact Hq.
    - intros i Hi; apply in_seq in Hi; rewrite ndist_le by lia; reflexivity. }
  assert (HB : Rsum (fun i => q ^ ndist i n) (seq n (n + 1)) <= / (1 - q)).
  { rewrite <- (Rsum_seq_shift (fun i => q ^ ndist i n) n (n + 1)).
    apply Rle_trans with (Rsum (fun i => q ^ i) (seq 0 (n + 1))).
    - apply Rsum_le; intros i _; cbv beta.
      rewrite ndist_ge by lia.
      replace (i + n - n)%nat with i by lia.
      apply Rle_refl.
    - apply geometric_sum_bound; exact Hq. }
  unfold Rdiv; lra.
Qed.

(** Integer parts. *)

Lemma Int_part_nonneg : forall x, 0 <= x -> (0 <= Int_part x)%Z.
Proof.
  intros x Hx.
  destruct (base_Int_part x) as [_ H].
  assert (Hlt : (-1 < Int_part x)%Z) by (apply lt_IZR; lra).
  lia.
Qed.

Lemma up_nonneg : forall x, 0 <= x -> (0 <= up x)%Z.
Proof.
  intros x Hx.
  destruct (archimed x) as [H _].
  assert (Hlt : (0 < up x)%Z) by (apply lt_IZR; lra).
  lia.
Qed.

Lemma INR_Z_to_nat : forall z, (0 <= z)%Z -> INR (Z.to_nat z) = IZR z.
Proof. intros z Hz; rewrite INR_IZR_INZ, Z2Nat.id by exact Hz; reflexivity. Qed.

Lemma Rdiv_nonneg : forall a b, 0 <= a -> 0 < b -> 0 <= a / b.
Proof.
  intros a b Ha Hb; unfold Rdiv; apply Rmult_le_pos; [exact Ha | left; apply Rinv_0_lt_compat; exact Hb].
Qed.

(** * Section 4: Signals, Judges and the Light Cone

    The agent acts at position x0 at time t0. A judge at distance d receives the
    signal at t0 + d / c and its response, travelling at most at c, reaches the
    agent no earlier than t0 + 2 d / c. An agent planning over a horizon T is
    therefore exposed to exactly the judges within distance c T / 2: the horizon
    radius. The model is parametric in c, in the lattice spacing res, which fixes
    the density of potential judges, and in their tolerance tol. *)

Record Attenuation := mkAttenuation {
  att : R -> R;
  att_kappa : R;
  att_kappa_pos : 0 < att_kappa;
  att_kappa_le_1 : att_kappa <= 1;
  att_pos : forall d, 0 <= d -> 0 < att d;
  att_le_1 : forall d, 0 <= d -> att d <= 1;
  att_inverse_square : forall d, 0 <= d -> att_kappa / (1 + d * d) <= att d
}.

Section Model.

Variable c : R.
Hypothesis c_pos : 0 < c.

Variable res : R.
Hypothesis res_pos : 0 < res.

Variable tol : R.
Hypothesis tol_pos : 0 < tol.

Record Observer := mkObserver {
  obs_pos : Vec3;
  obs_tol : R;
  obs_tol_pos : 0 < obs_tol
}.

Definition dist (o : Observer) (x0 : Vec3) : R := norm (vsub (obs_pos o) x0).

Lemma dist_nonneg : forall o x0, 0 <= dist o x0.
Proof. intros; apply norm_nonneg. Qed.

Definition reception_time (o : Observer) (x0 : Vec3) (t0 : R) : R :=
  t0 + dist o x0 / c.

Definition earliest_response (o : Observer) (x0 : Vec3) (t0 : R) : R :=
  t0 + 2 * dist o x0 / c.

(** A judge decides no earlier than reception, and its response travels at most
    at c, so nothing from the judge reaches the agent before the round trip. *)
Theorem round_trip : forall o x0 t0 t_decide t_arrive,
  reception_time o x0 t0 <= t_decide ->
  t_decide + dist o x0 / c <= t_arrive ->
  earliest_response o x0 t0 <= t_arrive.
Proof.
  intros o x0 t0 td ta H1 H2; unfold reception_time, earliest_response in *.
  unfold Rdiv in *; lra.
Qed.

Definition horizon_radius (T : R) : R := c * T / 2.

Theorem within_horizon_iff : forall o x0 t0 T,
  earliest_response o x0 t0 <= t0 + T <-> dist o x0 <= horizon_radius T.
Proof.
  intros o x0 t0 T; unfold earliest_response, horizon_radius.
  split; intro H.
  - apply Rmult_le_reg_l with (2 / c); [apply Rdiv_lt_0_compat; lra |].
    replace (2 / c * (c * T / 2)) with T by (field; lra).
    unfold Rdiv in *; lra.
  - apply Rmult_le_compat_l with (r := 2 / c) in H; [| left; apply Rdiv_lt_0_compat; lra].
    replace (2 / c * (c * T / 2)) with T in H by (field; lra).
    unfold Rdiv in *; lra.
Qed.

Lemma vsub_vsub_cancel : forall p q x0, vsub (vsub p x0) (vsub q x0) = vsub p q.
Proof. intros [[a b] d] [[e f] g] [[h i] j]; unfold vsub; f_equal; [f_equal|]; ring. Qed.

(** Two judges receive the signal at times whose separation, multiplied by c, is
    at most their distance: neither reception lies in the other's causal past, so
    the decisions taken at reception cannot influence one another. *)
Theorem receptions_not_timelike : forall o1 o2 x0 t0,
  c * Rabs (reception_time o1 x0 t0 - reception_time o2 x0 t0) <=
  norm (vsub (obs_pos o1) (obs_pos o2)).
Proof.
  intros o1 o2 x0 t0; unfold reception_time, dist.
  replace (t0 + norm (vsub (obs_pos o1) x0) / c - (t0 + norm (vsub (obs_pos o2) x0) / c))
    with ((norm (vsub (obs_pos o1) x0) - norm (vsub (obs_pos o2) x0)) / c) by (field; lra).
  unfold Rdiv; rewrite Rabs_mult, (Rabs_right (/ c)) by (left; apply Rinv_0_lt_compat; exact c_pos).
  replace (c * (Rabs (norm (vsub (obs_pos o1) x0) - norm (vsub (obs_pos o2) x0)) * / c))
    with (Rabs (norm (vsub (obs_pos o1) x0) - norm (vsub (obs_pos o2) x0))) by (field; lra).
  rewrite <- (vsub_vsub_cancel (obs_pos o1) (obs_pos o2) x0).
  apply norm_reverse_triangle_abs.
Qed.

(** ** The lattice of potential judges

    The potential judges within radius rad of x0 are the points of the cubic
    lattice of spacing res that lie in that ball, each with tolerance tol. *)

Definition lattice_point (x0 : Vec3) (n i j k : nat) : Vec3 :=
  vadd x0 (vscale res (IZR (Z.of_nat i - Z.of_nat n),
                       IZR (Z.of_nat j - Z.of_nat n),
                       IZR (Z.of_nat k - Z.of_nat n))).

Lemma lattice_point_sub : forall x0 n i j k,
  vsub (lattice_point x0 n i j k) x0 =
  vscale res (IZR (Z.of_nat i - Z.of_nat n),
              IZR (Z.of_nat j - Z.of_nat n),
              IZR (Z.of_nat k - Z.of_nat n)).
Proof. intros [[a b] d] n i j k; unfold lattice_point, vadd, vsub, vscale; f_equal; [f_equal|]; ring. Qed.

Lemma lattice_point_dist : forall x0 n i j k,
  norm (vsub (lattice_point x0 n i j k) x0) =
  res * norm (IZR (Z.of_nat i - Z.of_nat n),
              IZR (Z.of_nat j - Z.of_nat n),
              IZR (Z.of_nat k - Z.of_nat n)).
Proof. intros; rewrite lattice_point_sub, norm_scale_nonneg by lra; reflexivity. Qed.

Definition grid_size (rad : R) : nat := Z.to_nat (up (rad / res)).

Definition cube_size (rad : R) : nat := Z.to_nat (Int_part (rad / (2 * res))).

Definition in_ball (x0 : Vec3) (rad : R) (p : Vec3) : bool :=
  if Rle_dec (norm (vsub p x0)) rad then true else false.

Lemma in_ball_true : forall x0 rad p, in_ball x0 rad p = true <-> norm (vsub p x0) <= rad.
Proof.
  intros x0 rad p; unfold in_ball; destruct (Rle_dec (norm (vsub p x0)) rad); split; intro H;
    try reflexivity; try tauto; discriminate.
Qed.

Definition cell (x0 : Vec3) (rad : R) (n i j k : nat) : list Observer :=
  if in_ball x0 rad (lattice_point x0 n i j k)
  then [mkObserver (lattice_point x0 n i j k) tol tol_pos]
  else [].

Definition judges (x0 : Vec3) (rad : R) : list Observer :=
  let n := grid_size rad in
  let L := seq 0 (2 * n + 1) in
  flat_map (fun i => flat_map (fun j => flat_map (fun k => cell x0 rad n i j k) L) L) L.

Lemma judges_spec : forall x0 rad o,
  In o (judges x0 rad) ->
  exists i j k,
    In i (seq 0 (2 * grid_size rad + 1)) /\
    In j (seq 0 (2 * grid_size rad + 1)) /\
    In k (seq 0 (2 * grid_size rad + 1)) /\
    o = mkObserver (lattice_point x0 (grid_size rad) i j k) tol tol_pos /\
    norm (vsub (lattice_point x0 (grid_size rad) i j k) x0) <= rad.
Proof.
  intros x0 rad o Ho; unfold judges in Ho.
  apply in_flat_map in Ho; destruct Ho as [i [Hi Ho]].
  apply in_flat_map in Ho; destruct Ho as [j [Hj Ho]].
  apply in_flat_map in Ho; destruct Ho as [k [Hk Ho]].
  unfold cell in Ho.
  destruct (in_ball x0 rad (lattice_point x0 (grid_size rad) i j k)) eqn:E.
  - destruct Ho as [Ho | []]; subst o.
    exists i, j, k; repeat split; try assumption.
    apply in_ball_true; exact E.
  - destruct Ho.
Qed.

Lemma judges_dist : forall x0 rad o, In o (judges x0 rad) -> dist o x0 <= rad.
Proof.
  intros x0 rad o Ho; destruct (judges_spec x0 rad o Ho) as [i [j [k [_ [_ [_ [Heq Hn]]]]]]].
  subst o; unfold dist; simpl; exact Hn.
Qed.

Lemma judges_tol : forall x0 rad o, In o (judges x0 rad) -> obs_tol o = tol.
Proof.
  intros x0 rad o Ho; destruct (judges_spec x0 rad o Ho) as [i [j [k [_ [_ [_ [Heq _]]]]]]].
  subst o; reflexivity.
Qed.

(** Sums over the judges unfold to triple sums over the lattice indices. *)
Lemma Rsum_judges : forall (F : Observer -> R) x0 rad,
  Rsum F (judges x0 rad) =
  Rsum (fun i => Rsum (fun j => Rsum (fun k =>
    if in_ball x0 rad (lattice_point x0 (grid_size rad) i j k)
    then F (mkObserver (lattice_point x0 (grid_size rad) i j k) tol tol_pos) else 0)
    (seq 0 (2 * grid_size rad + 1))) (seq 0 (2 * grid_size rad + 1))) (seq 0 (2 * grid_size rad + 1)).
Proof.
  intros F x0 rad; unfold judges.
  rewrite Rsum_flat_map; apply Rsum_ext; intros i _.
  rewrite Rsum_flat_map; apply Rsum_ext; intros j _.
  rewrite Rsum_flat_map; apply Rsum_ext; intros k _.
  unfold cell; apply Rsum_if.
Qed.

(** ** Counting the judges *)

Lemma cube_size_INR : forall rad, 0 <= rad ->
  INR (cube_size rad) = IZR (Int_part (rad / (2 * res))).
Proof.
  intros rad Hrad; unfold cube_size; apply INR_Z_to_nat.
  apply Int_part_nonneg; apply Rdiv_nonneg; lra.
Qed.

Lemma grid_size_INR : forall rad, 0 <= rad ->
  INR (grid_size rad) = IZR (up (rad / res)).
Proof.
  intros rad Hrad; unfold grid_size; apply INR_Z_to_nat.
  apply up_nonneg; apply Rdiv_nonneg; lra.
Qed.

Lemma cube_size_bounds : forall rad, 0 <= rad ->
  rad / (2 * res) - 1 < INR (cube_size rad) /\ INR (cube_size rad) <= rad / (2 * res).
Proof.
  intros rad Hrad; rewrite cube_size_INR by exact Hrad.
  destruct (base_Int_part (rad / (2 * res))) as [H1 H2]; lra.
Qed.

Lemma grid_size_bounds : forall rad, 0 <= rad ->
  rad / res < INR (grid_size rad) /\ INR (grid_size rad) <= rad / res + 1.
Proof.
  intros rad Hrad; rewrite grid_size_INR by exact Hrad.
  destruct (archimed (rad / res)) as [H1 H2]; lra.
Qed.

Lemma cube_le_grid : forall rad, 0 <= rad -> (cube_size rad <= grid_size rad)%nat.
Proof.
  intros rad Hrad.
  destruct (cube_size_bounds rad Hrad) as [_ Hm].
  destruct (grid_size_bounds rad Hrad) as [Hn _].
  assert (Hhalf : rad / (2 * res) <= rad / res).
  { unfold Rdiv; rewrite Rinv_mult.
    assert (0 < / res) by (apply Rinv_0_lt_compat; exact res_pos).
    nra. }
  apply INR_le; lra.
Qed.

(** A lattice point whose indices lie within cube_size of the centre is in the ball. *)
Lemma cube_point_in_ball : forall x0 rad i j k,
  0 <= rad ->
  (grid_size rad - cube_size rad <= i <= grid_size rad + cube_size rad)%nat ->
  (grid_size rad - cube_size rad <= j <= grid_size rad + cube_size rad)%nat ->
  (grid_size rad - cube_size rad <= k <= grid_size rad + cube_size rad)%nat ->
  norm (vsub (lattice_point x0 (grid_size rad) i j k) x0) <= rad.
Proof.
  intros x0 rad i j k Hrad Hi Hj Hk.
  rewrite lattice_point_dist.
  set (n := grid_size rad) in *. set (m := cube_size rad) in *.
  assert (Hmn := cube_le_grid rad Hrad). fold n m in Hmn.
  assert (Hbound : forall u, (n - m <= u <= n + m)%nat ->
                   Rabs (IZR (Z.of_nat u - Z.of_nat n)) <= INR m).
  { intros u Hu.
    rewrite INR_IZR_INZ.
    apply Rabs_le; split.
    - rewrite <- opp_IZR; apply IZR_le; lia.
    - apply IZR_le; lia. }
  assert (H := cube_in_ball _ _ _ (INR m) (Hbound i Hi) (Hbound j Hj) (Hbound k Hk)).
  destruct (cube_size_bounds rad Hrad) as [_ Hm]. fold m in Hm.
  assert (Hm0 : 0 <= INR m) by apply pos_INR.
  assert (Hs3 := sqrt3_lt_2).
  assert (H2 : INR m * sqrt 3 <= INR m * 2) by nra.
  assert (H3 : res * (INR m * 2) <= rad).
  { unfold Rdiv in Hm; rewrite Rinv_mult in Hm.
    assert (0 < / res) by (apply Rinv_0_lt_compat; exact res_pos).
    apply Rmult_le_reg_r with (/ res); [assumption |].
    replace (res * (INR m * 2) * / res) with (INR m * 2) by (field; lra).
    nra. }
  assert (Hnn := norm_nonneg (IZR (Z.of_nat i - Z.of_nat n), IZR (Z.of_nat j - Z.of_nat n),
                              IZR (Z.of_nat k - Z.of_nat n))).
  nra.
Qed.

(** Lower bound for a sum over the judges by the inscribed cube. *)
Lemma Rsum_judges_lower : forall (F : Observer -> R) x0 rad C,
  0 <= rad -> 0 <= C ->
  (forall p, norm (vsub p x0) <= rad -> C <= F (mkObserver p tol tol_pos)) ->
  INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1) * C
  <= Rsum F (judges x0 rad).
Proof.
  intros F x0 rad C Hrad HC HF.
  rewrite Rsum_judges.
  set (n := grid_size rad). set (m := cube_size rad).
  set (L := seq 0 (2 * n + 1)). set (mid := seq (n - m) (2 * m + 1)).
  set (term := fun i j k =>
    if in_ball x0 rad (lattice_point x0 n i j k)
    then F (mkObserver (lattice_point x0 n i j k) tol tol_pos) else 0).
  assert (Hmn : (m <= n)%nat) by apply cube_le_grid, Hrad.
  assert (Hterm_nonneg : forall i j k, 0 <= term i j k).
  { intros i j k; unfold term.
    destruct (in_ball x0 rad (lattice_point x0 n i j k)) eqn:E; [| lra].
    apply Rle_trans with C; [exact HC |]. apply HF. apply in_ball_true; exact E. }
  assert (Hterm_mid : forall i j k, In i mid -> In j mid -> In k mid -> C <= term i j k).
  { intros i j k Hi Hj Hk; unfold term.
    apply in_seq in Hi; apply in_seq in Hj; apply in_seq in Hk.
    assert (Hin : in_ball x0 rad (lattice_point x0 n i j k) = true).
    { apply in_ball_true. apply cube_point_in_ball; [exact Hrad | lia | lia | lia]. }
    rewrite Hin. apply HF. apply in_ball_true; exact Hin. }
  assert (Hlen : (n - m + (2 * m + 1) <= 2 * n + 1)%nat) by lia.
  change (Rsum (fun i => Rsum (fun j => Rsum (fun k => term i j k) L) L) L) with
         (Rsum (fun i => Rsum (fun j => Rsum (fun k => term i j k) L) L) L).
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k => term i j k) L) L) mid).
  2:{ apply Rsum_seq_sub; [exact Hlen |].
      intros i _; apply Rsum_nonneg; intros j _; apply Rsum_nonneg; intros k _; apply Hterm_nonneg. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k => term i j k) L) mid) mid).
  2:{ apply Rsum_le; intros i _; apply Rsum_seq_sub; [exact Hlen |].
      intros j _; apply Rsum_nonneg; intros k _; apply Hterm_nonneg. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k => term i j k) mid) mid) mid).
  2:{ apply Rsum_le; intros i _; apply Rsum_le; intros j _; apply Rsum_seq_sub; [exact Hlen |].
      intros k _; apply Hterm_nonneg. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k => C) mid) mid) mid).
  2:{ apply Rsum_le; intros i Hi; apply Rsum_le; intros j Hj; apply Rsum_le; intros k Hk.
      apply Hterm_mid; assumption. }
  rewrite !Rsum_const. unfold mid; rewrite length_seq.
  apply Req_le; ring.
Qed.

Theorem judges_count_lower : forall x0 rad, 0 <= rad ->
  INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1)
  <= INR (length (judges x0 rad)).
Proof.
  intros x0 rad Hrad.
  assert (H := Rsum_judges_lower (fun _ => 1) x0 rad 1 Hrad Rle_0_1 (fun _ _ => Rle_refl 1)).
  rewrite Rsum_const in H. lra.
Qed.

Theorem judges_count_upper : forall x0 rad,
  INR (length (judges x0 rad)) <=
  INR (2 * grid_size rad + 1) * INR (2 * grid_size rad + 1) * INR (2 * grid_size rad + 1).
Proof.
  intros x0 rad.
  assert (E : INR (length (judges x0 rad)) = Rsum (fun _ => 1) (judges x0 rad)).
  { rewrite Rsum_const; ring. }
  rewrite E, Rsum_judges.
  set (L := seq 0 (2 * grid_size rad + 1)).
  assert (HL : INR (length L) = INR (2 * grid_size rad + 1)) by (unfold L; rewrite length_seq; reflexivity).
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k => 1) L) L) L).
  - apply Rsum_le; intros i _; apply Rsum_le; intros j _; apply Rsum_le; intros k _.
    destruct (in_ball x0 rad (lattice_point x0 (grid_size rad) i j k)); lra.
  - rewrite !Rsum_const, HL. apply Req_le; ring.
Qed.

(** The judges always include the agent's own cell: the list is never empty. *)
Lemma judges_nonempty : forall x0 rad, 0 <= rad -> (1 <= length (judges x0 rad))%nat.
Proof.
  intros x0 rad Hrad.
  assert (H := judges_count_lower x0 rad Hrad).
  assert (H1 : 1 <= INR (2 * cube_size rad + 1)).
  { replace 1 with (INR 1) by reflexivity. apply le_INR. lia. }
  assert (H2 : 1 <= INR (length (judges x0 rad))) by nra.
  replace 1 with (INR 1) in H2 by reflexivity.
  apply INR_le; exact H2.
Qed.

(** ** The hazard sum

    For each judge, the perceived signal is the destruction attenuated by its
    distance, in units of its tolerance. The hazard is the sum over judges. *)

Definition hazard (A : Attenuation) (x0 : Vec3) (rad : R) : R :=
  Rsum (fun o => att A (dist o x0) / obs_tol o) (judges x0 rad).

Lemma hazard_nonneg : forall A x0 rad, 0 <= hazard A x0 rad.
Proof.
  intros A x0 rad; unfold hazard; apply Rsum_nonneg; intros o Ho.
  apply Rdiv_nonneg; [left; apply att_pos, dist_nonneg | apply obs_tol_pos].
Qed.

Lemma hazard_lower_cube : forall A x0 rad, 0 <= rad ->
  INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1) * INR (2 * cube_size rad + 1)
    * (att_kappa A / ((1 + rad * rad) * tol)) <= hazard A x0 rad.
Proof.
  intros A x0 rad Hrad; unfold hazard.
  apply Rsum_judges_lower; [exact Hrad | |].
  - apply Rdiv_nonneg; [left; apply att_kappa_pos | nra].
  - intros p Hp.
    cbv beta; unfold dist; cbn [obs_pos obs_tol].
    set (d := norm (vsub p x0)) in *.
    assert (Hd : 0 <= d) by apply norm_nonneg.
    assert (Hk := att_kappa_pos A).
    assert (Hinv : att_kappa A / (1 + rad * rad) <= att_kappa A / (1 + d * d)).
    { unfold Rdiv; apply Rmult_le_compat_l; [lra |].
      apply Rinv_le_contravar; nra. }
    assert (Hatt := att_inverse_square A d Hd).
    unfold Rdiv in *; rewrite Rinv_mult.
    assert (0 < / tol) by (apply Rinv_0_lt_compat; exact tol_pos).
    rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r; [lra |].
    lra.
Qed.

(** The explicit lower bound: once the radius exceeds 1 and twice the lattice
    spacing, the hazard grows at least linearly in the radius. The cube of
    judges grows as the cube of the radius while inverse-square attenuation
    divides by its square. *)
Theorem hazard_lower_bound : forall A x0 rad,
  1 <= rad -> 2 * res <= rad ->
  att_kappa A * rad / (16 * (res * res * res) * tol) <= hazard A x0 rad.
Proof.
  intros A x0 rad Hrad1 Hrad2.
  assert (Hrad : 0 <= rad) by lra.
  assert (H := hazard_lower_cube A x0 rad Hrad).
  set (M := INR (2 * cube_size rad + 1)) in *.
  assert (Hk := att_kappa_pos A).
  destruct (cube_size_bounds rad Hrad) as [Hm _].
  assert (HM : rad / (2 * res) <= M).
  { unfold M. rewrite plus_INR, mult_INR. simpl INR.
    assert (E : rad / res = 2 * (rad / (2 * res))) by (field; lra).
    assert (Hge1 : 1 <= rad / (2 * res)).
    { apply Rmult_le_reg_r with (2 * res); [lra |].
      unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra. }
    lra. }
  set (rho := rad / (2 * res)) in *.
  assert (Hrho : 0 < rho) by (unfold rho; apply Rdiv_lt_0_compat; lra).
  assert (HMpos : 0 <= M) by lra.
  assert (HM3 : rho * rho * rho <= M * M * M).
  { apply Rle_trans with (rho * rho * M).
    - apply Rmult_le_compat_l; [nra | exact HM].
    - apply Rle_trans with (rho * M * M).
      + replace (rho * rho * M) with (rho * M * rho) by ring.
        apply Rmult_le_compat_l; [nra | exact HM].
      + replace (rho * M * M) with (M * M * rho) by ring.
        apply Rmult_le_compat_l; [nra | exact HM]. }
  assert (Hrr : 0 < 2 * rad * rad * tol).
  { apply Rmult_lt_0_compat; [nra | exact tol_pos]. }
  assert (Hden : att_kappa A / (2 * rad * rad * tol) <= att_kappa A / ((1 + rad * rad) * tol)).
  { unfold Rdiv; apply Rmult_le_compat_l; [lra |].
    apply Rinv_le_contravar; [nra |].
    apply Rmult_le_compat_r; [lra | nra]. }
  assert (Hpos : 0 <= att_kappa A / (2 * rad * rad * tol)).
  { apply Rdiv_nonneg; [lra | exact Hrr]. }
  assert (Hfin : att_kappa A * rad / (16 * (res * res * res) * tol)
                 = rho * rho * rho * (att_kappa A / (2 * rad * rad * tol))).
  { unfold rho; field; repeat split; lra. }
  rewrite Hfin.
  apply Rle_trans with (M * M * M * (att_kappa A / (2 * rad * rad * tol))).
  { apply Rmult_le_compat_r; [exact Hpos | exact HM3]. }
  apply Rle_trans with (M * M * M * (att_kappa A / ((1 + rad * rad) * tol))); [| exact H].
  apply Rmult_le_compat_l; [| exact Hden].
  apply Rmult_le_pos; [apply Rmult_le_pos; exact HMpos || exact HMpos | exact HMpos].
Qed.

(** * Section 5: Elimination, Survival, and the Closed Form

    A judge's elimination probability has the Poisson form 1 - exp(- signal /
    tolerance), where the signal is the offense the judge perceives, attenuated
    by distance. The offense is a non-negative functional of the action; the
    thesis instantiates it with the destruction of the event, and Section 10
    shows that the comparative conclusions need only a gap between the offense
    of the preserving action and that of its competitor. *)

Variable A : Attenuation.

(** The agent's options form an arbitrary type; the thesis instantiates it with
    actions on the resource state, and Section 11 with the verdicts of a judge. *)
Variable Act : Type.

Variable offense : Act -> R.
Hypothesis offense_nonneg : forall a, 0 <= offense a.

Lemma exp_le_compat : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H; destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq].
  - left; apply exp_increasing; exact Hlt.
  - rewrite Heq; apply Rle_refl.
Qed.

Lemma exp_le_inv : forall x y, exp x <= exp y -> x <= y.
Proof.
  intros x y H; apply Rnot_lt_le; intro Hlt.
  apply exp_increasing in Hlt; lra.
Qed.

Lemma exp_le_1 : forall x, x <= 0 -> exp x <= 1.
Proof. intros x H; rewrite <- exp_0; apply exp_le_compat; exact H. Qed.

Lemma exp_lt_1 : forall x, x < 0 -> exp x < 1.
Proof. intros x H; rewrite <- exp_0; apply exp_increasing; exact H. Qed.

Lemma ln_le_compat : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx H; destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq].
  - left; apply ln_increasing; assumption.
  - rewrite Heq; apply Rle_refl.
Qed.

Lemma ln_div : forall x y, 0 < x -> 0 < y -> ln (x / y) = ln x - ln y.
Proof.
  intros x y Hx Hy; unfold Rdiv.
  rewrite ln_mult; [| exact Hx | apply Rinv_0_lt_compat; exact Hy].
  rewrite ln_Rinv by exact Hy; reflexivity.
Qed.

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

(** Survival: the judges within the horizon decide independently, so the
    agent survives with the product of the per-judge survival probabilities. *)
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

(** * Section 6: The Rate of Convergence

    With the horizon radius c T / 2, the hazard grows at least like rate * T. *)

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

Lemma horizon_radius_nonneg : forall T, 0 <= T -> 0 <= horizon_radius T.
Proof. intros T HT; unfold horizon_radius; apply Rdiv_nonneg; nra. Qed.

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

(** * Section 7: Benefits, Utility, and the Crossover Depth

    Elimination forfeits the action's benefit, so expected utility is the
    benefit times survival. A destructive action with a large enough benefit
    wins at shallow depth and loses beyond an explicit depth. *)

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

(** Beyond the crossover depth, preservation is optimal against every action of
    the class, and the inequality is strict against every offensive one. *)
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

(** ** The crossover is a genuine phase change.

    At any fixed depth, an offensive action whose benefit exceeds the
    preserving benefit divided by its own survival is the better choice, so
    the preference for preservation emerges with depth rather than holding
    from the start. *)
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

(** * Section 8: Time Preference and the Sharp Converse

    A judge at distance d responds after the round trip 2 d / c. An agent with
    time preference rate r weighs a response arriving at that time by
    exp(- r * 2 d / c). The discounted hazard over the whole lattice is bounded,
    because the three-dimensional lattice sum of exp(- lambda |x|) factors into
    three geometric sums, so the discounted survival of every action stays above
    a positive floor at every depth. Convergence therefore requires patience:
    with any positive rate, an offensive action whose benefit exceeds the
    preserving benefit divided by its floor is preferred at every depth. *)

Definition discount (r : R) (o : Observer) (x0 : Vec3) : R :=
  exp (- r * (2 * dist o x0 / c)).

Lemma discount_bounds : forall r o x0, 0 <= r -> 0 < discount r o x0 <= 1.
Proof.
  intros r o x0 Hr; unfold discount; split; [apply exp_pos | apply exp_le_1].
  assert (Hd := dist_nonneg o x0).
  assert (0 <= 2 * dist o x0 / c) by (apply Rdiv_nonneg; lra).
  nra.
Qed.

Lemma discount_zero : forall o x0, discount 0 o x0 = 1.
Proof. intros; unfold discount; replace (- 0 * (2 * dist o x0 / c)) with 0 by ring; apply exp_0. Qed.

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

(** The per-axis decay factor of the discount across one lattice step. *)
Definition decay (r : R) : R := exp (- (2 * r * res / (c * sqrt 3))).

Lemma decay_bounds : forall r, 0 < r -> 0 < decay r < 1.
Proof.
  intros r Hr; unfold decay; split; [apply exp_pos | apply exp_lt_1].
  assert (0 < 2 * r * res / (c * sqrt 3)).
  { apply Rdiv_lt_0_compat; [nra | apply Rmult_lt_0_compat; [exact c_pos | apply sqrt3_pos]]. }
  lra.
Qed.

Lemma exp_neg_INR : forall mu k, exp (- mu * INR k) = exp (- mu) ^ k.
Proof.
  intros mu k; induction k as [| k IH].
  - simpl; rewrite Rmult_0_r, exp_0; reflexivity.
  - rewrite S_INR; replace (- mu * (INR k + 1)) with (- mu * INR k + - mu) by ring.
    rewrite exp_plus, IH; simpl; ring.
Qed.

Lemma Rabs_IZR_ndist : forall i n, Rabs (IZR (Z.of_nat i - Z.of_nat n)) = INR (ndist i n).
Proof.
  intros i n; rewrite minus_IZR, <- !INR_IZR_INZ.
  destruct (le_lt_dec n i) as [H | H].
  - rewrite Rabs_right by (assert (Hle := le_INR _ _ H); lra).
    rewrite ndist_ge by exact H. rewrite minus_INR by exact H; reflexivity.
  - rewrite Rabs_left by (assert (Hlt := lt_INR _ _ H); lra).
    rewrite ndist_le by lia. rewrite minus_INR by lia; ring.
Qed.

Lemma discount_lattice_le : forall r x0 n i j k, 0 < r ->
  discount r (mkObserver (lattice_point x0 n i j k) tol tol_pos) x0 <=
  decay r ^ ndist i n * decay r ^ ndist j n * decay r ^ ndist k n.
Proof.
  intros r x0 n i j k Hr.
  unfold discount, dist, decay; cbn [obs_pos].
  rewrite lattice_point_dist.
  set (a := IZR (Z.of_nat i - Z.of_nat n)).
  set (b := IZR (Z.of_nat j - Z.of_nat n)).
  set (d := IZR (Z.of_nat k - Z.of_nat n)).
  set (mu := 2 * r * res / (c * sqrt 3)).
  rewrite <- !exp_neg_INR, <- !exp_plus.
  apply exp_le_compat.
  rewrite <- !Rabs_IZR_ndist. fold a b d.
  assert (HL := l1_le_sqrt3_norm a b d).
  assert (Hs3 := sqrt3_pos).
  assert (Hmu : 0 <= mu).
  { unfold mu; apply Rdiv_nonneg; [nra | apply Rmult_lt_0_compat; [exact c_pos | exact Hs3]]. }
  assert (Hstep : mu * (Rabs a + Rabs b + Rabs d) <= mu * (sqrt 3 * norm (a, b, d)))
    by (apply Rmult_le_compat_l; assumption).
  assert (Heq : mu * (sqrt 3 * norm (a, b, d)) = r * (2 * (res * norm (a, b, d)) / c))
    by (unfold mu; field; lra).
  lra.
Qed.

Lemma discount_sum_le : forall r x0 rad, 0 < r ->
  Rsum (fun o => discount r o x0) (judges x0 rad) <=
  8 / ((1 - decay r) * (1 - decay r) * (1 - decay r)).
Proof.
  intros r x0 rad Hr.
  rewrite Rsum_judges.
  set (n := grid_size rad). set (L := seq 0 (2 * n + 1)). set (q := decay r).
  destruct (decay_bounds r Hr) as [Hq0 Hq1]. fold q in Hq0, Hq1.
  set (G := Rsum (fun i => q ^ ndist i n) L).
  assert (HG : G <= 2 / (1 - q)) by (unfold G, L; apply two_sided_geometric_bound; split; lra).
  assert (HG0 : 0 <= G) by (unfold G; apply Rsum_nonneg; intros i _; apply pow_le; lra).
  apply Rle_trans with
    (Rsum (fun i => Rsum (fun j => Rsum (fun k => q ^ ndist i n * q ^ ndist j n * q ^ ndist k n) L) L) L).
  - apply Rsum_le; intros i _; apply Rsum_le; intros j _; apply Rsum_le; intros k _.
    destruct (in_ball x0 rad (lattice_point x0 n i j k)).
    + apply discount_lattice_le; exact Hr.
    + repeat apply Rmult_le_pos; apply pow_le; lra.
  - assert (E : Rsum (fun i => Rsum (fun j => Rsum (fun k =>
                  q ^ ndist i n * q ^ ndist j n * q ^ ndist k n) L) L) L = G * G * G).
    { transitivity (Rsum (fun i => Rsum (fun j => q ^ ndist i n * q ^ ndist j n * G) L) L).
      { apply Rsum_ext; intros i _; apply Rsum_ext; intros j _.
        unfold G; rewrite <- Rsum_scal_l; reflexivity. }
      transitivity (Rsum (fun i => q ^ ndist i n * G * G) L).
      { apply Rsum_ext; intros i _.
        rewrite (Rsum_ext _ (fun j => (q ^ ndist i n * G) * q ^ ndist j n)) by (intros j _; ring).
        rewrite Rsum_scal_l; fold G; reflexivity. }
      rewrite (Rsum_ext _ (fun i => (G * G) * q ^ ndist i n)) by (intros i _; ring).
      rewrite Rsum_scal_l; fold G; ring. }
    rewrite E.
    assert (H1q : 0 < 1 - q) by lra.
    replace (8 / ((1 - q) * (1 - q) * (1 - q)))
      with ((2 / (1 - q)) * (2 / (1 - q)) * (2 / (1 - q))) by (field; lra).
    apply cube_le; split; assumption.
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

(** * Section 9: Depth Is Never Safer for an Offender

    A larger horizon radius admits every judge of a smaller one: the hazard is
    monotone in the horizon and the survival of an offensive action is
    antitone in it. *)

Lemma grid_size_monotone : forall rad1 rad2,
  0 <= rad1 <= rad2 -> (grid_size rad1 <= grid_size rad2)%nat.
Proof.
  intros rad1 rad2 [H0 H]; unfold grid_size.
  apply Z2Nat.inj_le; [apply up_nonneg; apply Rdiv_nonneg; lra | apply up_nonneg; apply Rdiv_nonneg; lra |].
  apply up_monotone.
  unfold Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact res_pos | exact H].
Qed.

Lemma lattice_point_shift : forall x0 n1 n2 i j k, (n1 <= n2)%nat ->
  lattice_point x0 n2 (i + (n2 - n1)) (j + (n2 - n1)) (k + (n2 - n1)) = lattice_point x0 n1 i j k.
Proof.
  intros x0 n1 n2 i j k Hn; unfold lattice_point.
  assert (E1 : (Z.of_nat (i + (n2 - n1)) - Z.of_nat n2)%Z = (Z.of_nat i - Z.of_nat n1)%Z) by lia.
  assert (E2 : (Z.of_nat (j + (n2 - n1)) - Z.of_nat n2)%Z = (Z.of_nat j - Z.of_nat n1)%Z) by lia.
  assert (E3 : (Z.of_nat (k + (n2 - n1)) - Z.of_nat n2)%Z = (Z.of_nat k - Z.of_nat n1)%Z) by lia.
  rewrite E1, E2, E3; reflexivity.
Qed.

Lemma Rsum_judges_monotone : forall (F : Observer -> R) x0 rad1 rad2,
  0 <= rad1 <= rad2 -> (forall o, 0 <= F o) ->
  Rsum F (judges x0 rad1) <= Rsum F (judges x0 rad2).
Proof.
  intros F x0 rad1 rad2 [H0 H12] HF.
  rewrite !Rsum_judges.
  set (n1 := grid_size rad1). set (n2 := grid_size rad2).
  assert (Hn : (n1 <= n2)%nat) by (apply grid_size_monotone; split; assumption).
  set (term2 := fun i j k =>
    if in_ball x0 rad2 (lattice_point x0 n2 i j k)
    then F (mkObserver (lattice_point x0 n2 i j k) tol tol_pos) else 0).
  assert (Hnn : forall i j k, 0 <= term2 i j k).
  { intros i j k; unfold term2; destruct (in_ball x0 rad2 (lattice_point x0 n2 i j k)); [apply HF | lra]. }
  assert (Hlen : (n2 - n1 + (2 * n1 + 1) <= 2 * n2 + 1)%nat) by lia.
  assert (Hpt : forall i j k,
    (if in_ball x0 rad1 (lattice_point x0 n1 i j k)
     then F (mkObserver (lattice_point x0 n1 i j k) tol tol_pos) else 0)
    <= term2 (i + (n2 - n1))%nat (j + (n2 - n1))%nat (k + (n2 - n1))%nat).
  { intros i j k; unfold term2; rewrite (lattice_point_shift x0 n1 n2 i j k Hn).
    destruct (in_ball x0 rad1 (lattice_point x0 n1 i j k)) eqn:E1.
    - assert (E2 : in_ball x0 rad2 (lattice_point x0 n1 i j k) = true).
      { apply in_ball_true; apply Rle_trans with rad1; [apply in_ball_true; exact E1 | exact H12]. }
      rewrite E2; apply Rle_refl.
    - destruct (in_ball x0 rad2 (lattice_point x0 n1 i j k)); [apply HF | lra]. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k =>
    term2 (i + (n2 - n1))%nat (j + (n2 - n1))%nat (k + (n2 - n1))%nat)
    (seq 0 (2 * n1 + 1))) (seq 0 (2 * n1 + 1))) (seq 0 (2 * n1 + 1))).
  { apply Rsum_le; intros i _; apply Rsum_le; intros j _; apply Rsum_le; intros k _; apply Hpt. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k =>
    term2 (i + (n2 - n1))%nat (j + (n2 - n1))%nat k)
    (seq 0 (2 * n2 + 1))) (seq 0 (2 * n1 + 1))) (seq 0 (2 * n1 + 1))).
  { apply Rsum_le; intros i _; apply Rsum_le; intros j _.
    apply (Rsum_seq_shift_sub (fun k => term2 (i + (n2 - n1))%nat (j + (n2 - n1))%nat k)
             (n2 - n1)%nat (2 * n1 + 1)%nat (2 * n2 + 1)%nat Hlen).
    intros k _; apply Hnn. }
  apply Rle_trans with (Rsum (fun i => Rsum (fun j => Rsum (fun k =>
    term2 (i + (n2 - n1))%nat j k)
    (seq 0 (2 * n2 + 1))) (seq 0 (2 * n2 + 1))) (seq 0 (2 * n1 + 1))).
  { apply Rsum_le; intros i _.
    apply (Rsum_seq_shift_sub (fun j => Rsum (fun k => term2 (i + (n2 - n1))%nat j k) (seq 0 (2 * n2 + 1)))
             (n2 - n1)%nat (2 * n1 + 1)%nat (2 * n2 + 1)%nat Hlen).
    intros j _; apply Rsum_nonneg; intros k _; apply Hnn. }
  apply (Rsum_seq_shift_sub (fun i => Rsum (fun j => Rsum (fun k => term2 i j k) (seq 0 (2 * n2 + 1)))
                                       (seq 0 (2 * n2 + 1)))
           (n2 - n1)%nat (2 * n1 + 1)%nat (2 * n2 + 1)%nat Hlen).
  intros i _; apply Rsum_nonneg; intros j _; apply Rsum_nonneg; intros k _; apply Hnn.
Qed.

Theorem judges_count_monotone : forall x0 rad1 rad2,
  0 <= rad1 <= rad2 -> (length (judges x0 rad1) <= length (judges x0 rad2))%nat.
Proof.
  intros x0 rad1 rad2 H.
  assert (Hs := Rsum_judges_monotone (fun _ => 1) x0 rad1 rad2 H (fun _ => Rle_0_1)).
  rewrite !Rsum_const in Hs.
  apply INR_le; lra.
Qed.

Theorem hazard_monotone : forall x0 rad1 rad2,
  0 <= rad1 <= rad2 -> hazard A x0 rad1 <= hazard A x0 rad2.
Proof.
  intros x0 rad1 rad2 H; unfold hazard; apply Rsum_judges_monotone; [exact H |].
  intros o; apply Rdiv_nonneg; [left; apply att_pos, dist_nonneg | apply obs_tol_pos].
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

End Model.

(** * Section 10: Resource Preservation

    The thesis: the offense a judge perceives is the destruction of the event.
    The agent acts on the resource state s0 at position x0; its options are
    actions on the state; the preserving ones are those that do not reduce the
    resources, and the destructive ones are those that do. *)

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

End Resources.

(** * Section 11: Judges as Players

    A judge is itself an agent facing judges of its own. Its verdict on an
    offender is a best response to its payoffs, and the elimination probability
    the agent faces is the agent's credence that the judge's tolerance lies below
    the perceived offense. Punishing a preserver destroys the preserver's
    resources, so under the same measure the judge is a destroyer, and the core
    theorems apply to it: its survival vanishes with its own depth and deep
    judges spare preservers. Punishing a destroyer that would destroy more than
    it is worth over the judge's horizon is net-preserving. The asymmetry the
    agent-level theorems assume is therefore the behaviour of deep judges. *)

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

(** The Poisson elimination probability is the credence that the judge's
    tolerance lies below the perceived offense, under the exponential credence. *)
Theorem elim_prob_is_tolerance_credence : forall (A : Attenuation) (Act : Type) (offense : Act -> R) a o x0,
  elim_prob A Act offense a o x0 = tolerance_credence (obs_tol o) (offense a * att A (dist o x0)).
Proof. intros; unfold elim_prob, signal, tolerance_credence; f_equal; f_equal; unfold Rdiv; ring. Qed.

(** The judge's own offense, as seen by its judges: punishing destroys the
    offender's resources phi and prevents the destruction psi the offender would
    have caused over the judge's horizon. *)
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

(** The judge's benefit: its own continued existence b0, plus the value of the
    destruction it prevents, minus the cost of punishing. *)
Definition judge_benefit (b0 gain cost : R) (v : Verdict) : R :=
  match v with Punish => b0 + gain - cost | Ignore => b0 end.

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

(** Beyond its own crossover depth, a judge spares preservers whatever the
    gain from punishing them. *)
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

(** Once its horizon exceeds the offender's value divided by the destruction
    rate, punishing a persistent destroyer is inoffensive, and a judge whose
    gain exceeds its cost punishes. *)
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
Theorem derived_asymmetry : forall phi delta b0 gain cost xJ,
  0 < phi -> 0 < delta -> 0 < b0 -> cost < gain ->
  exists TJstar, forall TJ, TJstar < TJ -> phi / delta <= TJ ->
    utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 gain cost) Punish xJ TJ <
    utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 gain cost) Ignore xJ TJ /\
    utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 gain cost) Ignore xJ TJ <
    utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 gain cost) Punish xJ TJ.
Proof.
  intros phi delta b0 gain cost xJ Hphi Hd Hb0 Hgc.
  destruct (deep_judges_spare_preservers phi b0 gain cost xJ Hphi Hb0) as [TJstar H].
  exists TJstar; intros TJ HT Hpers; split.
  - apply H; exact HT.
  - apply deep_judges_punish_persistent_destroyers; assumption.
Qed.

End JudgesAsPlayers.

(** * Section 12: Independence

    The survival of Section 5 multiplies the judges' survival probabilities,
    which is the joint survival under the independent coupling of their
    marginals. Section 4 justifies independence: no judge's reception lies in
    another's causal past. The results here show what independence buys. Under
    any coupling the joint survival is at most one minus the largest marginal,
    and the perfectly dependent coupling attains that bound with a survival that
    does not decay with the number of judges. *)

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

(** The perfectly dependent coupling: with probability q every judge
    eliminates, otherwise none does. Its marginals are q and its joint survival
    is 1 - q however many judges there are. *)
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

(** * Section 13: Summary

    The statement of the thesis in one theorem, for any speed of light, any
    lattice spacing, any tolerance, any attenuation no steeper than inverse
    square, any event position, any resource state and any benefit function. *)

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

(** The two-level game: deep judges spare preservers and punish persistent
    destroyers, and against such judges every optimal action of a deep agent is
    preserving. *)
Theorem two_level_equilibrium :
  forall (c res tol : R) (tol_pos : 0 < tol) (A : Attenuation) (s0 x0 xJ : Vec3) (benefit : Action -> R)
         (menu : list Action) (p : Action) (phi delta b0 gain cost : R),
  0 < c -> 0 < res ->
  In p menu -> preserving_at p s0 -> 0 < benefit p ->
  0 < phi -> 0 < delta -> 0 < b0 -> cost < gain ->
  exists Tstar TJstar,
    (forall T, Tstar < T ->
       forall a, In a menu ->
       (forall a', In a' menu ->
          utility c res tol tol_pos A Action (destr s0) benefit a' x0 T <=
          utility c res tol tol_pos A Action (destr s0) benefit a x0 T) ->
       preserving_at a s0) /\
    (forall TJ, TJstar < TJ -> phi / delta <= TJ ->
       utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 gain cost) Punish xJ TJ <
       utility c res tol tol_pos A Verdict (judge_offense phi 0) (judge_benefit b0 gain cost) Ignore xJ TJ /\
       utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 gain cost) Ignore xJ TJ <
       utility c res tol tol_pos A Verdict (judge_offense phi (delta * TJ)) (judge_benefit b0 gain cost) Punish xJ TJ).
Proof.
  intros c res tol tol_pos A s0 x0 xJ benefit menu p phi delta b0 gain cost Hc Hres Hin Hp Hbp Hphi Hd Hb0 Hgc.
  destruct (optimal_actions_preserve c Hc res Hres tol tol_pos A s0 benefit x0 menu p Hin Hp Hbp) as [Tstar HT].
  destruct (derived_asymmetry c Hc res Hres tol tol_pos A phi delta b0 gain cost xJ Hphi Hd Hb0 Hgc) as [TJstar HTJ].
  exists Tstar, TJstar; split; [exact HT | exact HTJ].
Qed.

Print Assumptions convergence_to_resource_preservation.
Print Assumptions two_level_equilibrium.
Print Assumptions time_preference_blocks_convergence.
Print Assumptions frechet_bound.
