(** Finite sums and products, geometric sums, integer parts, bounds on exp and ln. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.

(** * Section 3: Finite sums and products over lists, with their order, scaling and reindexing laws. *)

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

(** Finite geometric sums: the closed form and the bound 1 / (1 - q). *)
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

(** The two-sided geometric sum of q^|i - n| over i in [0, 2n] is at most 2 / (1 - q). *)
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

(** Integer parts: Int_part and up of a non-negative real are non-negative, and up is monotone. *)

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
