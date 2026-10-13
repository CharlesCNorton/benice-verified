(** Vectors in R^3 with the Euclidean norm: metric axioms, Cauchy-Schwarz, both triangle inequalities, the cube-in-ball and l1 bounds. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.

(** * Section 1: Vectors, the Euclidean norm and its metric. *)

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

(** Cauchy-Schwarz, dot u v <= norm u * norm v, from Lagrange's identity. *)
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

(** The Euclidean distance is a metric: triangle inequality, symmetry, vanishing on the diagonal, non-negativity. *)
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

(** Reverse triangle inequality: norm u - norm v <= norm (u - v). *)
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

