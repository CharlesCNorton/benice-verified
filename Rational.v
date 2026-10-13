(** The axiom-light variant: resources measured additively, the lattice filtered by squared distance, judges responding by any law that vanishes at zero offense with positive slope, so that the convergence theorem rests on the two axioms beneath every real-number comparison and on nothing from exp, ln or sqrt. *)

From Stdlib Require Import Reals Lra Lia List ZArith Psatz.
Import ListNotations.
Open Scope R_scope.
From BeNice Require Import Vectors Actions Sums LightCone Survival Resources Physical.

(** * Additive resources *)

Definition l1 (v : Vec3) : R := let '(x, y, z) := v in Rabs x + Rabs y + Rabs z.

Lemma l1_nonneg : forall v, 0 <= l1 v.
Proof. intros [[x y] z]; simpl; assert (Hx := Rabs_pos x); assert (Hy := Rabs_pos y); assert (Hz := Rabs_pos z); lra. Qed.

Lemma l1_scale : forall k v, l1 (vscale k v) = Rabs k * l1 v.
Proof. intros k [[x y] z]; unfold vscale, l1; rewrite !Rabs_mult; ring. Qed.

Definition destruction1 (a : Action) (s : Vec3) : R := Rmax 0 (l1 s - l1 (a s)).

Definition preserving1_at (a : Action) (s : Vec3) : Prop := l1 s <= l1 (a s).

Definition destructive1_at (a : Action) (s : Vec3) : Prop := l1 (a s) < l1 s.

Lemma destruction1_nonneg : forall a s, 0 <= destruction1 a s.
Proof. intros; apply Rmax_l. Qed.

Lemma destruction1_zero_iff : forall a s, destruction1 a s = 0 <-> preserving1_at a s.
Proof.
  intros a s; unfold destruction1, preserving1_at; split; intro H.
  - destruct (Rle_dec (l1 s - l1 (a s)) 0) as [Hle | Hgt]; [lra |].
    rewrite Rmax_right in H by lra. lra.
  - apply Rmax_left; lra.
Qed.

Lemma destruction1_pos_iff : forall a s, 0 < destruction1 a s <-> destructive1_at a s.
Proof.
  intros a s; unfold destruction1, destructive1_at; split; intro H.
  - destruct (Rle_dec (l1 s - l1 (a s)) 0) as [Hle | Hgt]; [rewrite Rmax_left in H by lra; lra | lra].
  - rewrite Rmax_right by lra. lra.
Qed.

Lemma identity_preserving1 : forall s, preserving1_at identity_action s.
Proof. intros s; unfold preserving1_at, identity_action; lra. Qed.

Lemma destruction1_scale : forall f s, 0 <= f <= 1 -> destruction1 (scale_action f) s = (1 - f) * l1 s.
Proof.
  intros f s [Hf0 Hf1]; unfold destruction1, scale_action.
  rewrite l1_scale, Rabs_right by lra.
  assert (H := l1_nonneg s).
  rewrite Rmax_right by nra. ring.
Qed.

(** * Attenuation over the squared distance *)

Record Attenuation2 := mkAttenuation2 {
  att2 : R -> R;
  kappa2 : R;
  kappa2_pos : 0 < kappa2;
  att2_pos : forall q, 0 <= q -> 0 < att2 q;
  att2_le_1 : forall q, 0 <= q -> att2 q <= 1;
  att2_inverse_square : forall q, 0 <= q -> kappa2 / (1 + q) <= att2 q
}.

Definition inverse_square2 : Attenuation2.
Proof.
  refine (mkAttenuation2 (fun q => 1 / (1 + q)) 1 Rlt_0_1 _ _ _).
  - intros q Hq; apply Rdiv_lt_0_compat; lra.
  - intros q Hq; unfold Rdiv; rewrite Rmult_1_l.
    apply Rle_trans with (/ 1); [apply Rinv_le_contravar; lra | rewrite Rinv_1; lra].
  - intros q Hq; apply Rle_refl.
Defined.

(** * Response laws: zero at zero offense, bounded by one, at least a positive multiple of x / (1 + x). *)

Record ResponseLaw := mkLaw {
  law : R -> R;
  law_zero : law 0 = 0;
  law_nonneg : forall x, 0 <= x -> 0 <= law x;
  law_le_1 : forall x, 0 <= x -> law x <= 1;
  slope : R;
  slope_pos : 0 < slope;
  law_lower : forall x, 0 <= x -> slope * (x / (1 + x)) <= law x
}.

Definition rational_law : ResponseLaw.
Proof.
  refine (mkLaw (fun x => x / (1 + x)) _ _ _ 1 Rlt_0_1 _).
  - unfold Rdiv; ring.
  - intros x Hx; apply Rdiv_nonneg; lra.
  - intros x Hx; apply div_le_a; lra.
  - intros x Hx; rewrite Rmult_1_l; apply Rle_refl.
Defined.

Definition poisson_law : ResponseLaw.
Proof.
  refine (mkLaw (fun x => 1 - exp (- x)) _ _ _ 1 Rlt_0_1 _).
  - rewrite Ropp_0, exp_0; ring.
  - intros x Hx. assert (Hn : - x <= 0) by lra. assert (H := exp_le_1 (- x) Hn). lra.
  - intros x Hx; assert (H := exp_pos (- x)); lra.
  - intros x Hx; rewrite Rmult_1_l.
    assert (H1 : exp (- x) <= / (1 + x)).
    { rewrite exp_Ropp; apply Rinv_le_contravar; [lra | apply exp_ineq1_le]. }
    assert (H2 : x / (1 + x) = 1 - / (1 + x)) by (field; repeat split; lra).
    lra.
Defined.

(** * The lattice filtered by squared distance *)

Section Geometry2.

Variable c : R.
Hypothesis c_pos : 0 < c.
Variable res : R.
Hypothesis res_pos : 0 < res.
Variable tol : R.
Hypothesis tol_pos : 0 < tol.

Definition dist2 (o : Observer) (x0 : Vec3) : R := sqnorm (vsub (obs_pos o) x0).

Lemma dist2_nonneg : forall o x0, 0 <= dist2 o x0.
Proof. intros; apply sqnorm_nonneg. Qed.

Definition in_ball2 (x0 : Vec3) (rad : R) (p : Vec3) : bool :=
  if Rle_dec (sqnorm (vsub p x0)) (rad * rad) then true else false.

Lemma in_ball2_true : forall x0 rad p, in_ball2 x0 rad p = true <-> sqnorm (vsub p x0) <= rad * rad.
Proof.
  intros x0 rad p; unfold in_ball2; destruct (Rle_dec (sqnorm (vsub p x0)) (rad * rad)); split; intro H;
    try reflexivity; try tauto; discriminate.
Qed.

Definition cell2 (x0 : Vec3) (rad : R) (n i j k : nat) : list Observer :=
  if in_ball2 x0 rad (lattice_point res x0 n i j k)
  then [mkObserver (lattice_point res x0 n i j k) tol tol_pos]
  else [].

Definition judges2 (x0 : Vec3) (rad : R) : list Observer :=
  let n := grid_size res rad in
  let L := seq 0 (2 * n + 1) in
  flat_map (fun i => flat_map (fun j => flat_map (fun k => cell2 x0 rad n i j k) L) L) L.

Lemma judges2_spec : forall x0 rad o,
  In o (judges2 x0 rad) ->
  exists i j k,
    o = mkObserver (lattice_point res x0 (grid_size res rad) i j k) tol tol_pos /\
    sqnorm (vsub (lattice_point res x0 (grid_size res rad) i j k) x0) <= rad * rad.
Proof.
  intros x0 rad o Ho; unfold judges2 in Ho.
  apply in_flat_map in Ho; destruct Ho as [i [Hi Ho]].
  apply in_flat_map in Ho; destruct Ho as [j [Hj Ho]].
  apply in_flat_map in Ho; destruct Ho as [k [Hk Ho]].
  unfold cell2 in Ho.
  destruct (in_ball2 x0 rad (lattice_point res x0 (grid_size res rad) i j k)) eqn:E.
  - destruct Ho as [Ho | []]; subst o.
    exists i, j, k; split; [reflexivity | apply in_ball2_true; exact E].
  - destruct Ho.
Qed.

Lemma judges2_dist2 : forall x0 rad o, In o (judges2 x0 rad) -> dist2 o x0 <= rad * rad.
Proof.
  intros x0 rad o Ho; destruct (judges2_spec x0 rad o Ho) as [i [j [k [Heq Hn]]]].
  subst o; unfold dist2; simpl; exact Hn.
Qed.

Lemma judges2_tol : forall x0 rad o, In o (judges2 x0 rad) -> obs_tol o = tol.
Proof.
  intros x0 rad o Ho; destruct (judges2_spec x0 rad o Ho) as [i [j [k [Heq _]]]].
  subst o; reflexivity.
Qed.

Lemma Rsum_judges2 : forall (F : Observer -> R) x0 rad,
  Rsum F (judges2 x0 rad) =
  Rsum (fun i => Rsum (fun j => Rsum (fun k =>
    if in_ball2 x0 rad (lattice_point res x0 (grid_size res rad) i j k)
    then F (mkObserver (lattice_point res x0 (grid_size res rad) i j k) tol tol_pos) else 0)
    (seq 0 (2 * grid_size res rad + 1))) (seq 0 (2 * grid_size res rad + 1))) (seq 0 (2 * grid_size res rad + 1)).
Proof.
  intros F x0 rad; unfold judges2.
  rewrite Rsum_flat_map; apply Rsum_ext; intros i _.
  rewrite Rsum_flat_map; apply Rsum_ext; intros j _.
  rewrite Rsum_flat_map; apply Rsum_ext; intros k _.
  unfold cell2; apply Rsum_if.
Qed.

Lemma sqnorm_vscale : forall k v, sqnorm (vscale k v) = k * k * sqnorm v.
Proof. intros k [[x y] z]; unfold vscale, sqnorm; ring. Qed.

Lemma cube_in_ball2 : forall x y z M,
  Rabs x <= M -> Rabs y <= M -> Rabs z <= M -> sqnorm (x, y, z) <= 3 * M * M.
Proof.
  intros x y z M Hx Hy Hz.
  assert (HM : M >= 0) by (apply Rle_ge; apply Rle_trans with (Rabs x); [apply Rabs_pos | exact Hx]).
  assert (HabsM : Rabs M = M) by (apply Rabs_right; exact HM).
  assert (Hx2 : Rsqr x <= Rsqr M) by (apply Rsqr_le_abs_1; rewrite HabsM; exact Hx).
  assert (Hy2 : Rsqr y <= Rsqr M) by (apply Rsqr_le_abs_1; rewrite HabsM; exact Hy).
  assert (Hz2 : Rsqr z <= Rsqr M) by (apply Rsqr_le_abs_1; rewrite HabsM; exact Hz).
  unfold Rsqr in *; simpl; lra.
Qed.

Lemma cube_point_in_ball2 : forall x0 rad i j k,
  0 <= rad ->
  (grid_size res rad - cube_size res rad <= i <= grid_size res rad + cube_size res rad)%nat ->
  (grid_size res rad - cube_size res rad <= j <= grid_size res rad + cube_size res rad)%nat ->
  (grid_size res rad - cube_size res rad <= k <= grid_size res rad + cube_size res rad)%nat ->
  sqnorm (vsub (lattice_point res x0 (grid_size res rad) i j k) x0) <= rad * rad.
Proof.
  intros x0 rad i j k Hrad Hi Hj Hk.
  rewrite lattice_point_sub, sqnorm_vscale.
  set (n := grid_size res rad) in *. set (m := cube_size res rad) in *.
  assert (Hbound : forall u, (n - m <= u <= n + m)%nat ->
                   Rabs (IZR (Z.of_nat u - Z.of_nat n)) <= INR m).
  { intros u Hu; rewrite INR_IZR_INZ; apply Rabs_le; split.
    - rewrite <- opp_IZR; apply IZR_le; lia.
    - apply IZR_le; lia. }
  assert (H := cube_in_ball2 _ _ _ (INR m) (Hbound i Hi) (Hbound j Hj) (Hbound k Hk)).
  destruct (cube_size_bounds res res_pos rad Hrad) as [_ Hm]. fold m in Hm.
  assert (Hm0 : 0 <= INR m) by apply pos_INR.
  assert (H3 : 2 * res * INR m <= rad).
  { unfold Rdiv in Hm; rewrite Rinv_mult in Hm.
    assert (0 < / res) by (apply Rinv_0_lt_compat; exact res_pos).
    apply Rmult_le_reg_r with (/ res); [assumption |].
    replace (2 * res * INR m * / res) with (2 * INR m) by (field; repeat split; lra).
    nra. }
  assert (Hx0 : 0 <= 2 * res * INR m) by (apply Rmult_le_pos; lra).
  assert (Hsq : (2 * res * INR m) * (2 * res * INR m) <= rad * rad) by (apply Rmult_le_compat; lra).
  assert (H4 : forall q, q <= 3 * INR m * INR m -> res * res * q <= res * res * (3 * INR m * INR m))
    by (intros q Hq; apply Rmult_le_compat_l; [nra | exact Hq]).
  specialize (H4 _ H).
  assert (Hnn : 0 <= res * res * INR m * INR m) by (repeat apply Rmult_le_pos; lra).
  lra.
Qed.

Lemma Rsum_judges2_lower : forall (F : Observer -> R) x0 rad C,
  0 <= rad -> 0 <= C ->
  (forall p, sqnorm (vsub p x0) <= rad * rad -> C <= F (mkObserver p tol tol_pos)) ->
  INR (2 * cube_size res rad + 1) * INR (2 * cube_size res rad + 1) * INR (2 * cube_size res rad + 1) * C
  <= Rsum F (judges2 x0 rad).
Proof.
  intros F x0 rad C Hrad HC HF.
  rewrite Rsum_judges2.
  set (n := grid_size res rad). set (m := cube_size res rad).
  set (L := seq 0 (2 * n + 1)). set (mid := seq (n - m) (2 * m + 1)).
  set (term := fun i j k =>
    if in_ball2 x0 rad (lattice_point res x0 n i j k)
    then F (mkObserver (lattice_point res x0 n i j k) tol tol_pos) else 0).
  assert (Hmn : (m <= n)%nat) by (apply cube_le_grid; assumption).
  assert (Hterm_nonneg : forall i j k, 0 <= term i j k).
  { intros i j k; unfold term.
    destruct (in_ball2 x0 rad (lattice_point res x0 n i j k)) eqn:E; [| lra].
    apply Rle_trans with C; [exact HC |]. apply HF. apply in_ball2_true; exact E. }
  assert (Hterm_mid : forall i j k, In i mid -> In j mid -> In k mid -> C <= term i j k).
  { intros i j k Hi Hj Hk; unfold term.
    apply in_seq in Hi; apply in_seq in Hj; apply in_seq in Hk.
    assert (Hin : in_ball2 x0 rad (lattice_point res x0 n i j k) = true).
    { apply in_ball2_true. apply cube_point_in_ball2; [exact Hrad | lia | lia | lia]. }
    rewrite Hin. apply HF. apply in_ball2_true; exact Hin. }
  assert (Hlen : (n - m + (2 * m + 1) <= 2 * n + 1)%nat) by lia.
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

Theorem judges2_count_lower : forall x0 rad, 0 <= rad ->
  INR (2 * cube_size res rad + 1) * INR (2 * cube_size res rad + 1) * INR (2 * cube_size res rad + 1)
  <= INR (length (judges2 x0 rad)).
Proof.
  intros x0 rad Hrad.
  assert (H := Rsum_judges2_lower (fun _ => 1) x0 rad 1 Hrad Rle_0_1 (fun _ _ => Rle_refl 1)).
  rewrite Rsum_const in H. lra.
Qed.

(** The hazard over the squared distance. *)
Definition hazard2 (A : Attenuation2) (x0 : Vec3) (rad : R) : R :=
  Rsum (fun o => att2 A (dist2 o x0) / obs_tol o) (judges2 x0 rad).

Lemma hazard2_nonneg : forall A x0 rad, 0 <= hazard2 A x0 rad.
Proof.
  intros A x0 rad; unfold hazard2; apply Rsum_nonneg; intros o Ho.
  apply Rdiv_nonneg; [left; apply att2_pos, dist2_nonneg | apply obs_tol_pos].
Qed.

Lemma hazard2_lower_cube : forall A x0 rad, 0 <= rad ->
  INR (2 * cube_size res rad + 1) * INR (2 * cube_size res rad + 1) * INR (2 * cube_size res rad + 1)
    * (kappa2 A / ((1 + rad * rad) * tol)) <= hazard2 A x0 rad.
Proof.
  intros A x0 rad Hrad; unfold hazard2.
  apply Rsum_judges2_lower; [exact Hrad | |].
  - apply Rdiv_nonneg; [left; apply kappa2_pos | nra].
  - intros p Hp.
    cbv beta; unfold dist2; cbn [obs_pos obs_tol].
    set (q := sqnorm (vsub p x0)) in *.
    assert (Hq : 0 <= q) by apply sqnorm_nonneg.
    assert (Hk := kappa2_pos A).
    assert (Hinv : kappa2 A / (1 + rad * rad) <= kappa2 A / (1 + q)).
    { unfold Rdiv; apply Rmult_le_compat_l; [lra |]. apply Rinv_le_contravar; lra. }
    assert (Hatt := att2_inverse_square A q Hq).
    unfold Rdiv in *; rewrite Rinv_mult.
    assert (0 < / tol) by (apply Rinv_0_lt_compat; exact tol_pos).
    rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r; [lra |].
    lra.
Qed.

Theorem hazard2_lower_bound : forall A x0 rad,
  1 <= rad -> 2 * res <= rad ->
  kappa2 A * rad / (16 * (res * res * res) * tol) <= hazard2 A x0 rad.
Proof.
  intros A x0 rad Hrad1 Hrad2.
  assert (Hrad : 0 <= rad) by lra.
  assert (H := hazard2_lower_cube A x0 rad Hrad).
  set (M := INR (2 * cube_size res rad + 1)) in *.
  assert (Hk := kappa2_pos A).
  destruct (cube_size_bounds res res_pos rad Hrad) as [Hm _].
  assert (HM : rad / (2 * res) <= M).
  { unfold M. rewrite plus_INR, mult_INR. simpl INR.
    assert (Hge1 : 1 <= rad / (2 * res)).
    { apply Rmult_le_reg_r with (2 * res); [lra |].
      unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra. }
    lra. }
  set (rho := rad / (2 * res)) in *.
  assert (Hrho : 0 < rho) by (unfold rho; apply Rdiv_lt_0_compat; lra).
  assert (HMpos : 0 <= M) by lra.
  assert (HM3 : rho * rho * rho <= M * M * M) by (apply cube_le; split; lra).
  assert (Hrr : 0 < 2 * rad * rad * tol) by (apply Rmult_lt_0_compat; [nra | exact tol_pos]).
  assert (Hden : kappa2 A / (2 * rad * rad * tol) <= kappa2 A / ((1 + rad * rad) * tol)).
  { unfold Rdiv; apply Rmult_le_compat_l; [lra |].
    apply Rinv_le_contravar; [nra |].
    apply Rmult_le_compat_r; [lra | nra]. }
  assert (Hpos : 0 <= kappa2 A / (2 * rad * rad * tol)) by (apply Rdiv_nonneg; [lra | exact Hrr]).
  assert (Hfin : kappa2 A * rad / (16 * (res * res * res) * tol)
                 = rho * rho * rho * (kappa2 A / (2 * rad * rad * tol))).
  { unfold rho; field; repeat split; lra. }
  rewrite Hfin.
  apply Rle_trans with (M * M * M * (kappa2 A / (2 * rad * rad * tol))).
  { apply Rmult_le_compat_r; [exact Hpos | exact HM3]. }
  apply Rle_trans with (M * M * M * (kappa2 A / ((1 + rad * rad) * tol))); [| exact H].
  apply Rmult_le_compat_l; [| exact Hden].
  apply Rmult_le_pos; [apply Rmult_le_pos; exact HMpos || exact HMpos | exact HMpos].
Qed.

Definition rate2 (A : Attenuation2) : R := kappa2 A * c / (32 * (res * res * res) * tol).

Lemma rate2_pos : forall A, 0 < rate2 A.
Proof.
  intros A; unfold rate2; apply Rdiv_lt_0_compat.
  - apply Rmult_lt_0_compat; [apply kappa2_pos | exact c_pos].
  - repeat apply Rmult_lt_0_compat; lra.
Qed.

Theorem hazard2_horizon_lower : forall A x0 T,
  T_min c res <= T -> rate2 A * T <= hazard2 A x0 (horizon_radius c T).
Proof.
  intros A x0 T HT.
  assert (H1 : 2 / c <= T) by (apply Rle_trans with (T_min c res); [apply Rmax_l | exact HT]).
  assert (H2 : 4 * res / c <= T) by (apply Rle_trans with (T_min c res); [apply Rmax_r | exact HT]).
  assert (Hr1 : 1 <= horizon_radius c T).
  { unfold horizon_radius. apply Rmult_le_reg_l with (2 / c); [apply Rdiv_lt_0_compat; lra |].
    replace (2 / c * (c * T / 2)) with T by (field; repeat split; lra). rewrite Rmult_1_r. exact H1. }
  assert (Hr2 : 2 * res <= horizon_radius c T).
  { unfold horizon_radius. apply Rmult_le_reg_l with (2 / c); [apply Rdiv_lt_0_compat; lra |].
    replace (2 / c * (c * T / 2)) with T by (field; repeat split; lra).
    replace (2 / c * (2 * res)) with (4 * res / c) by (field; repeat split; lra). exact H2. }
  assert (H := hazard2_lower_bound A x0 (horizon_radius c T) Hr1 Hr2).
  replace (rate2 A * T) with (kappa2 A * horizon_radius c T / (16 * (res * res * res) * tol)); [exact H |].
  unfold rate2, horizon_radius; field; repeat split; lra.
Qed.

End Geometry2.

(** * Survival under a response law, with weights *)

Lemma prod_one_minus_le_inv_sum : forall {X : Type} (f : X -> R) (l : list X),
  (forall x, In x l -> 0 <= f x <= 1) ->
  Rprod (fun x => 1 - f x) l <= / (1 + Rsum f l).
Proof.
  intros X f l; induction l as [| x l IH]; intros H.
  - simpl; rewrite Rplus_0_r, Rinv_1; lra.
  - rewrite Rprod_cons, Rsum_cons.
    assert (Hx := H x (or_introl eq_refl)).
    assert (Hrest : forall y, In y l -> 0 <= f y <= 1) by (intros y Hy; apply H; right; exact Hy).
    assert (Hs : 0 <= Rsum f l) by (apply Rsum_nonneg; intros y Hy; apply (Hrest y Hy)).
    assert (IH' := IH Hrest).
    set (y := f x) in *. set (s := Rsum f l) in *.
    assert (HP0 : 0 <= Rprod (fun z => 1 - f z) l) by (apply Rprod_nonneg; intros z Hz; assert (Hz' := Hrest z Hz); lra).
    apply Rle_trans with ((1 - y) * / (1 + s)).
    { apply Rmult_le_compat_l; [lra | exact IH']. }
    assert (H1 : 0 < 1 + s) by lra.
    assert (H2 : 0 < 1 + (y + s)) by lra.
    apply Rmult_le_reg_r with ((1 + s) * (1 + (y + s))); [nra |].
    replace ((1 - y) * / (1 + s) * ((1 + s) * (1 + (y + s)))) with ((1 - y) * (1 + (y + s))) by (field; repeat split; lra).
    replace (/ (1 + (y + s)) * ((1 + s) * (1 + (y + s)))) with (1 + s) by (field; repeat split; lra).
    nra.
Qed.

Section Core2.

Variable c : R.
Hypothesis c_pos : 0 < c.
Variable res : R.
Hypothesis res_pos : 0 < res.
Variable tol : R.
Hypothesis tol_pos : 0 < tol.
Variable A : Attenuation2.
Variable L : ResponseLaw.
Variable Act : Type.
Variable offense : Act -> R.
Hypothesis offense_nonneg : forall a, 0 <= offense a.

Notation judges2 := (judges2 res tol tol_pos).
Notation hazard2 := (hazard2 res tol tol_pos A).
Notation horizon_radius := (horizon_radius c).

Definition signal2 (a : Act) (o : Observer) (x0 : Vec3) : R :=
  offense a * att2 A (dist2 o x0) / obs_tol o.

Lemma signal2_nonneg : forall a o x0, 0 <= signal2 a o x0.
Proof.
  intros; unfold signal2; apply Rdiv_nonneg; [| apply obs_tol_pos].
  apply Rmult_le_pos; [apply offense_nonneg | left; apply att2_pos, dist2_nonneg].
Qed.

Definition elim2 (a : Act) (o : Observer) (x0 : Vec3) : R := law L (signal2 a o x0).

Lemma elim2_bounds : forall a o x0, 0 <= elim2 a o x0 <= 1.
Proof.
  intros; unfold elim2; split; [apply law_nonneg | apply law_le_1]; apply signal2_nonneg.
Qed.

Lemma elim2_zero : forall a o x0, offense a = 0 -> elim2 a o x0 = 0.
Proof.
  intros a o x0 H; unfold elim2, signal2; rewrite H.
  replace (0 * att2 A (dist2 o x0) / obs_tol o) with 0 by (unfold Rdiv; ring).
  apply law_zero.
Qed.

Definition survival2 (w : Observer -> R) (a : Act) (x0 : Vec3) (T : R) : R :=
  Rprod (fun o => 1 - w o * elim2 a o x0) (judges2 x0 (horizon_radius T)).

Lemma survival2_of_inoffensive : forall w a x0 T, offense a = 0 -> survival2 w a x0 T = 1.
Proof.
  intros w a x0 T H; unfold survival2.
  rewrite (Rprod_ext _ (fun _ => 1)); [apply Rprod_one |].
  intros o _; rewrite elim2_zero by exact H; ring.
Qed.

Lemma survival2_nonneg : forall w a x0 T,
  (forall o, In o (judges2 x0 (horizon_radius T)) -> 0 <= w o <= 1) -> 0 <= survival2 w a x0 T.
Proof.
  intros w a x0 T Hw; unfold survival2; apply Rprod_nonneg; intros o Ho.
  assert (He := elim2_bounds a o x0). destruct (Hw o Ho). nra.
Qed.

Lemma survival2_le_1 : forall w a x0 T,
  (forall o, In o (judges2 x0 (horizon_radius T)) -> 0 <= w o <= 1) -> survival2 w a x0 T <= 1.
Proof.
  intros w a x0 T Hw; unfold survival2; apply Rprod_le_1; intros o Ho.
  assert (He := elim2_bounds a o x0). destruct (Hw o Ho). split; nra.
Qed.

(** The response to a judge's signal is at least slope times the signal in units of 1 + offense / tol. *)
Lemma elim2_lower : forall a o x0, obs_tol o = tol ->
  slope L * (signal2 a o x0 / (1 + offense a / tol)) <= elim2 a o x0.
Proof.
  intros a o x0 Htol; unfold elim2.
  set (s := signal2 a o x0).
  assert (Hs : 0 <= s) by apply signal2_nonneg.
  set (S := offense a / tol).
  assert (HS : 0 <= S) by (unfold S; apply Rdiv_nonneg; [apply offense_nonneg | exact tol_pos]).
  assert (HsS : s <= S).
  { unfold s, S, signal2; rewrite Htol.
    assert (Hatt := att2_le_1 A (dist2 o x0) (dist2_nonneg o x0)).
    assert (Ho := offense_nonneg a).
    assert (0 < / tol) by (apply Rinv_0_lt_compat; exact tol_pos).
    unfold Rdiv; apply Rmult_le_compat_r; [lra | nra]. }
  assert (Hlaw := law_lower L s Hs).
  assert (H3 : s / (1 + S) <= s / (1 + s)).
  { unfold Rdiv; apply Rmult_le_compat_l; [exact Hs |]. apply Rinv_le_contravar; lra. }
  assert (Hsl := slope_pos L).
  apply Rle_trans with (slope L * (s / (1 + s))); [apply Rmult_le_compat_l; lra | exact Hlaw].
Qed.

Lemma signal2_sum : forall a x0 rad,
  Rsum (fun o => signal2 a o x0) (judges2 x0 rad) = offense a * hazard2 x0 rad.
Proof.
  intros a x0 rad; unfold Rational.hazard2, signal2.
  rewrite <- Rsum_scal_l; apply Rsum_ext; intros o _; unfold Rdiv; ring.
Qed.

(** The rational bound: any weights above wmin on the horizon ball give survival at most 1 / (1 + wmin slope offense rate2 T / (1 + offense / tol)). *)
Theorem survival2_upper : forall (w : Observer -> R) (wmin : R) a x0 T,
  0 <= wmin ->
  (forall o, In o (judges2 x0 (horizon_radius T)) -> wmin <= w o <= 1) ->
  T_min c res <= T ->
  survival2 w a x0 T <=
  / (1 + wmin * slope L * offense a * rate2 c res tol A * T / (1 + offense a / tol)).
Proof.
  intros w wmin a x0 T Hwmin Hw HT; unfold survival2.
  set (S := offense a / tol).
  assert (HS : 0 <= S) by (unfold S; apply Rdiv_nonneg; [apply offense_nonneg | exact tol_pos]).
  set (J := judges2 x0 (horizon_radius T)).
  assert (Hwe : forall o, In o J -> 0 <= w o * elim2 a o x0 <= 1).
  { intros o Ho; assert (He := elim2_bounds a o x0); destruct (Hw o Ho); split; nra. }
  apply Rle_trans with (/ (1 + Rsum (fun o => w o * elim2 a o x0) J)).
  { apply (prod_one_minus_le_inv_sum (fun o => w o * elim2 a o x0) J Hwe). }
  assert (Hsum0 : 0 <= Rsum (fun o => w o * elim2 a o x0) J) by (apply Rsum_nonneg; intros o Ho; apply (Hwe o Ho)).
  assert (Hlow : Rsum (fun o => wmin * (slope L * (signal2 a o x0 / (1 + S)))) J <=
                 Rsum (fun o => w o * elim2 a o x0) J).
  { apply Rsum_le; intros o Ho.
    assert (He := elim2_lower a o x0 (judges2_tol res tol tol_pos _ _ _ Ho)).
    assert (He0 := elim2_bounds a o x0).
    destruct (Hw o Ho) as [Hw1 Hw2].
    assert (Hsl := slope_pos L).
    assert (Hsg := signal2_nonneg a o x0).
    assert (Hsg2 : 0 <= signal2 a o x0 / (1 + S)) by (apply Rdiv_nonneg; lra).
    apply Rle_trans with (wmin * elim2 a o x0); [apply Rmult_le_compat_l; [exact Hwmin | exact He] |].
    apply Rmult_le_compat_r; lra. }
  rewrite (Rsum_ext _ (fun o => (wmin * slope L * / (1 + S)) * signal2 a o x0)) in Hlow
    by (intros o _; unfold Rdiv; ring).
  rewrite Rsum_scal_l in Hlow.
  unfold J in Hlow; rewrite signal2_sum in Hlow; fold J in Hlow.
  assert (Hh := hazard2_horizon_lower c c_pos res res_pos tol tol_pos A x0 T HT).
  assert (Ho := offense_nonneg a).
  assert (Hsl := slope_pos L).
  assert (Hinv : 0 < / (1 + S)) by (apply Rinv_0_lt_compat; lra).
  assert (Hk : 0 <= wmin * slope L * / (1 + S)) by (apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra]).
  assert (H1 : offense a * (rate2 c res tol A * T) <= offense a * hazard2 x0 (horizon_radius T))
    by (apply Rmult_le_compat_l; assumption).
  assert (H2 : wmin * slope L * / (1 + S) * (offense a * (rate2 c res tol A * T)) <=
               wmin * slope L * / (1 + S) * (offense a * hazard2 x0 (horizon_radius T)))
    by (apply Rmult_le_compat_l; assumption).
  apply Rinv_le_contravar.
  - assert (Hp : 0 <= wmin * slope L * / (1 + S) * (offense a * (rate2 c res tol A * T))).
    { apply Rmult_le_pos; [exact Hk |]. apply Rmult_le_pos; [exact Ho |].
      apply Rmult_le_pos; [left; apply rate2_pos; assumption | assert (Hm := T_min_pos c c_pos res); lra]. }
    replace (wmin * slope L * offense a * rate2 c res tol A * T / (1 + S))
      with (wmin * slope L * / (1 + S) * (offense a * (rate2 c res tol A * T))) by (unfold Rdiv; ring).
    lra.
  - replace (wmin * slope L * offense a * rate2 c res tol A * T / (1 + S))
      with (wmin * slope L * / (1 + S) * (offense a * (rate2 c res tol A * T))) by (unfold Rdiv; ring).
    lra.
Qed.

(** Convergence with an explicit rational depth. *)
Theorem survival2_vanishes : forall (w : Observer -> R) (wmin : R) a x0,
  0 < wmin -> 0 < offense a ->
  (forall T, forall o, In o (judges2 x0 (horizon_radius T)) -> wmin <= w o <= 1) ->
  forall eps, 0 < eps ->
  exists T0, forall T, T0 <= T -> survival2 w a x0 T < eps.
Proof.
  intros w wmin a x0 Hwmin Ha Hw eps Heps.
  set (S := offense a / tol).
  assert (HS : 0 <= S) by (unfold S; apply Rdiv_nonneg; [lra | exact tol_pos]).
  set (P := wmin * slope L * offense a * rate2 c res tol A / (1 + S)).
  assert (HP : 0 < P).
  { unfold P; apply Rdiv_lt_0_compat; [| lra].
    apply Rmult_lt_0_compat; [| apply rate2_pos; assumption].
    apply Rmult_lt_0_compat; [| exact Ha].
    apply Rmult_lt_0_compat; [exact Hwmin | apply slope_pos]. }
  exists (Rmax (T_min c res) ((/ eps) / P + 1)).
  intros T HT.
  assert (HT1 : T_min c res <= T) by (eapply Rle_trans; [apply Rmax_l | exact HT]).
  assert (HT2 : (/ eps) / P + 1 <= T) by (eapply Rle_trans; [apply Rmax_r | exact HT]).
  apply Rle_lt_trans with (/ (1 + wmin * slope L * offense a * rate2 c res tol A * T / (1 + S))).
  { apply survival2_upper; [lra | apply Hw | exact HT1]. }
  assert (HPT : P * ((/ eps) / P + 1) <= P * T) by (apply Rmult_le_compat_l; lra).
  replace (P * ((/ eps) / P + 1)) with (/ eps + P) in HPT by (field; repeat split; lra).
  assert (E : wmin * slope L * offense a * rate2 c res tol A * T / (1 + S) = P * T) by (unfold P, Rdiv; ring).
  rewrite E.
  assert (Hie : 0 < / eps) by (apply Rinv_0_lt_compat; exact Heps).
  rewrite <- (Rinv_inv eps).
  apply Rinv_lt_contravar; [nra | lra].
Qed.

Variable benefit : Act -> R.

Definition utility2 (w : Observer -> R) (a : Act) (x0 : Vec3) (T : R) : R := benefit a * survival2 w a x0 T.

Definition crossover_depth2 (wmin delta B bp : R) : R :=
  Rmax (T_min c res) ((1 + delta / tol) * (B / bp - 1) / (wmin * slope L * delta * rate2 c res tol A)).

(** The rational crossover: beyond crossover_depth2, preservation beats every action of the class. *)
Theorem crossover2 : forall (w : Observer -> R) wmin x0 p delta B,
  offense p = 0 -> 0 < benefit p -> 0 < delta -> 0 < wmin ->
  forall T, crossover_depth2 wmin delta B (benefit p) < T ->
  (forall o, In o (judges2 x0 (horizon_radius T)) -> wmin <= w o <= 1) ->
  forall a, delta <= offense a -> benefit a <= B ->
  utility2 w a x0 T < utility2 w p x0 T.
Proof.
  intros w wmin x0 p delta B Hp Hbp Hdelta Hwmin T HT Hw a Ha HB.
  unfold utility2.
  rewrite (survival2_of_inoffensive w p x0 T Hp), Rmult_1_r.
  assert (Hw01 : forall o, In o (judges2 x0 (horizon_radius T)) -> 0 <= w o <= 1).
  { intros o Ho; destruct (Hw o Ho); lra. }
  assert (HS0 := survival2_nonneg w a x0 T Hw01).
  assert (HT1 : T_min c res < T)
    by (apply Rle_lt_trans with (crossover_depth2 wmin delta B (benefit p)); [apply Rmax_l | exact HT]).
  assert (HT2 : (1 + delta / tol) * (B / benefit p - 1) / (wmin * slope L * delta * rate2 c res tol A) < T)
    by (apply Rle_lt_trans with (crossover_depth2 wmin delta B (benefit p)); [apply Rmax_r | exact HT]).
  destruct (Rle_dec (benefit a) 0) as [Hneg | Hposb].
  - nra.
  - apply Rnot_le_lt in Hposb.
    assert (HBpos : 0 < B) by lra.
    assert (Hr := rate2_pos c c_pos res res_pos tol tol_pos A).
    assert (Hsl := slope_pos L).
    assert (Hdt : 0 < 1 + delta / tol) by (assert (0 <= delta / tol) by (apply Rdiv_nonneg; lra); lra).
    assert (Hwdr : 0 < wmin * slope L * delta * rate2 c res tol A).
    { apply Rmult_lt_0_compat; [| exact Hr].
      apply Rmult_lt_0_compat; [| exact Hdelta].
      apply Rmult_lt_0_compat; [exact Hwmin | exact Hsl]. }
    assert (Hmono := ratio_tol_monotone tol tol_pos delta (offense a) (conj (Rlt_le _ _ Hdelta) Ha)).
    set (X := wmin * slope L * offense a * rate2 c res tol A * T / (1 + offense a / tol)).
    set (Y := wmin * slope L * delta * rate2 c res tol A * T / (1 + delta / tol)).
    assert (HYX : Y <= X).
    { unfold X, Y.
      assert (HrT : 0 <= wmin * slope L * rate2 c res tol A * T).
      { assert (Hm := T_min_pos c c_pos res).
        apply Rmult_le_pos; [| lra].
        apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra]. }
      assert (Hm : wmin * slope L * rate2 c res tol A * T * (delta / (1 + delta / tol)) <=
                   wmin * slope L * rate2 c res tol A * T * (offense a / (1 + offense a / tol)))
        by (apply Rmult_le_compat_l; assumption).
      replace (wmin * slope L * delta * rate2 c res tol A * T / (1 + delta / tol))
        with (wmin * slope L * rate2 c res tol A * T * (delta / (1 + delta / tol))) by (unfold Rdiv; ring).
      replace (wmin * slope L * offense a * rate2 c res tol A * T / (1 + offense a / tol))
        with (wmin * slope L * rate2 c res tol A * T * (offense a / (1 + offense a / tol))) by (unfold Rdiv; ring).
      exact Hm. }
    assert (HY : B / benefit p - 1 < Y).
    { unfold Y.
      apply Rmult_lt_compat_r with (r := wmin * slope L * delta * rate2 c res tol A) in HT2; [| exact Hwdr].
      replace ((1 + delta / tol) * (B / benefit p - 1) / (wmin * slope L * delta * rate2 c res tol A) *
               (wmin * slope L * delta * rate2 c res tol A))
        with ((1 + delta / tol) * (B / benefit p - 1)) in HT2 by (field; repeat split; lra).
      apply Rmult_lt_reg_r with (1 + delta / tol); [exact Hdt |].
      replace (wmin * slope L * delta * rate2 c res tol A * T / (1 + delta / tol) * (1 + delta / tol))
        with (wmin * slope L * delta * rate2 c res tol A * T) by (field; repeat split; lra).
      lra. }
    assert (Hup : survival2 w a x0 T <= / (1 + X)) by (apply survival2_upper; [lra | exact Hw | lra]).
    assert (HY0 : 0 <= Y).
    { unfold Y; apply Rdiv_nonneg; [| lra].
      assert (Hm := T_min_pos c c_pos res).
      apply Rmult_le_pos; [| lra].
      apply Rmult_le_pos; [| lra].
      apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra]. }
    assert (Hkey : B * / (1 + X) < benefit p).
    { apply Rmult_lt_reg_r with (1 + X); [lra |].
      replace (B * / (1 + X) * (1 + X)) with B by (field; repeat split; lra).
      assert (B / benefit p - 1 < X) by lra.
      assert (B < benefit p * (1 + X)).
      { apply Rmult_lt_reg_r with (/ benefit p); [apply Rinv_0_lt_compat; exact Hbp |].
        replace (benefit p * (1 + X) * / benefit p) with (1 + X) by (field; repeat split; lra).
        unfold Rdiv in *; lra. }
      lra. }
    apply Rle_lt_trans with (B * survival2 w a x0 T); [nra |].
    apply Rle_lt_trans with (B * / (1 + X)); [apply Rmult_le_compat_l; lra | exact Hkey].
Qed.

(** Any action at least as good as preservation has offense bounded by a quantity falling like 1 / T. *)
Theorem optimal_offense2_le : forall x0 p a B T,
  offense p = 0 -> 0 < benefit p -> benefit a <= B -> T_min c res <= T ->
  utility2 (fun _ => 1) p x0 T <= utility2 (fun _ => 1) a x0 T ->
  slope L * offense a * (rate2 c res tol A * T) <= (B / benefit p - 1) * (1 + offense a / tol).
Proof.
  intros x0 p a B T Hp Hbp HB HT Hopt.
  unfold utility2 in Hopt.
  rewrite (survival2_of_inoffensive _ p x0 T Hp), Rmult_1_r in Hopt.
  assert (Hw : forall o, In o (judges2 x0 (horizon_radius T)) -> 1 <= (fun _ : Observer => 1) o <= 1)
    by (intros; split; apply Rle_refl).
  assert (Hw01 : forall o, In o (judges2 x0 (horizon_radius T)) -> 0 <= (fun _ : Observer => 1) o <= 1)
    by (intros; split; lra).
  assert (HS0 := survival2_nonneg (fun _ => 1) a x0 T Hw01).
  assert (HS1 := survival2_le_1 (fun _ => 1) a x0 T Hw01).
  assert (Hba : 0 < benefit a) by nra.
  assert (HBpos : 0 < B) by lra.
  assert (Hup := survival2_upper (fun _ => 1) 1 a x0 T Rle_0_1 Hw HT).
  set (X := 1 * slope L * offense a * rate2 c res tol A * T / (1 + offense a / tol)) in *.
  assert (HX0 : 0 <= X).
  { unfold X; apply Rdiv_nonneg.
    - assert (Hm := T_min_pos c c_pos res).
      assert (Hsl := slope_pos L). assert (Ho := offense_nonneg a).
      assert (Hr := rate2_pos c c_pos res res_pos tol tol_pos A).
      apply Rmult_le_pos; [| lra].
      apply Rmult_le_pos; [| lra].
      apply Rmult_le_pos; [| exact Ho].
      apply Rmult_le_pos; lra.
    - assert (0 <= offense a / tol) by (apply Rdiv_nonneg; [apply offense_nonneg | exact tol_pos]); lra. }
  assert (Hratio : benefit p <= B * / (1 + X)).
  { apply Rle_trans with (benefit a * survival2 (fun _ => 1) a x0 T); [exact Hopt |].
    apply Rle_trans with (B * survival2 (fun _ => 1) a x0 T); [nra |].
    apply Rmult_le_compat_l; lra. }
  assert (HX : 1 + X <= B / benefit p).
  { apply Rmult_le_reg_l with (benefit p); [exact Hbp |].
    replace (benefit p * (B / benefit p)) with B by (field; repeat split; lra).
    apply Rmult_le_reg_r with (/ (1 + X)); [apply Rinv_0_lt_compat; lra |].
    replace (benefit p * (1 + X) * / (1 + X)) with (benefit p) by (field; repeat split; lra).
    exact Hratio. }
  assert (Hdt : 0 < 1 + offense a / tol).
  { assert (0 <= offense a / tol) by (apply Rdiv_nonneg; [apply offense_nonneg | exact tol_pos]); lra. }
  assert (HXe : X * (1 + offense a / tol) = slope L * offense a * (rate2 c res tol A * T)).
  { assert (Ho := offense_nonneg a). unfold X. field. repeat split; lra. }
  rewrite <- HXe.
  apply Rmult_le_compat_r; lra.
Qed.

(** Presence credence q per site. *)
Theorem presence2_upper : forall q a x0 T,
  0 <= q <= 1 -> T_min c res <= T ->
  survival2 (fun _ => q) a x0 T <= / (1 + q * slope L * offense a * rate2 c res tol A * T / (1 + offense a / tol)).
Proof.
  intros q a x0 T [Hq0 Hq1] HT.
  apply survival2_upper; [exact Hq0 | intros o _; split; [apply Rle_refl | exact Hq1] | exact HT].
Qed.

(** Hyperbolic time preference, which weights a response after the round trip by 1 / (1 + r t), caps the survival of an offender at every depth beyond 1 / r. *)
Theorem hyperbolic_cap : forall (w : Observer -> R) r a x0 T,
  0 < r ->
  (forall o, In o (judges2 x0 (horizon_radius T)) -> / (1 + r * T) <= w o <= 1) ->
  T_min c res <= T -> / r <= T ->
  survival2 w a x0 T <= / (1 + slope L * offense a * rate2 c res tol A / (2 * r * (1 + offense a / tol))).
Proof.
  intros w r a x0 T Hr Hw HT HrT.
  assert (Hw0 : 0 <= / (1 + r * T)).
  { left; apply Rinv_0_lt_compat. assert (Hm := T_min_pos c c_pos res). nra. }
  apply Rle_trans with (/ (1 + / (1 + r * T) * slope L * offense a * rate2 c res tol A * T / (1 + offense a / tol))).
  { apply survival2_upper; assumption. }
  assert (Hsl := slope_pos L). assert (Ho := offense_nonneg a).
  assert (Hrate := rate2_pos c c_pos res res_pos tol tol_pos A).
  assert (Hdt : 0 < 1 + offense a / tol).
  { assert (0 <= offense a / tol) by (apply Rdiv_nonneg; [exact Ho | exact tol_pos]); lra. }
  assert (HT0 : 0 < T) by (assert (Hm := T_min_pos c c_pos res); lra).
  assert (Hfrac : / (2 * r) <= / (1 + r * T) * T).
  { assert (H1 : 1 + r * T <= 2 * r * T).
    { assert (r * T >= 1).
      { apply Rmult_le_compat_l with (r := r) in HrT; [| lra].
        replace (r * / r) with 1 in HrT by (field; repeat split; lra). lra. }
      lra. }
    apply Rmult_le_reg_l with (2 * r * (1 + r * T)); [nra |].
    replace (2 * r * (1 + r * T) * / (2 * r)) with (1 + r * T) by (field; repeat split; lra).
    replace (2 * r * (1 + r * T) * (/ (1 + r * T) * T)) with (2 * r * T) by (field; repeat split; nra).
    exact H1. }
  assert (Hnum : 0 <= slope L * offense a * rate2 c res tol A)
    by (apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra]).
  apply Rinv_le_contravar.
  - assert (0 <= slope L * offense a * rate2 c res tol A / (2 * r * (1 + offense a / tol))).
    { apply Rdiv_nonneg; [exact Hnum | nra]. }
    lra.
  - assert (HK : 0 <= slope L * offense a * rate2 c res tol A / (1 + offense a / tol)).
    { apply Rdiv_nonneg; [exact Hnum | lra]. }
    replace (slope L * offense a * rate2 c res tol A / (2 * r * (1 + offense a / tol)))
      with (slope L * offense a * rate2 c res tol A / (1 + offense a / tol) * / (2 * r)) by (field; repeat split; lra).
    replace (/ (1 + r * T) * slope L * offense a * rate2 c res tol A * T / (1 + offense a / tol))
      with (slope L * offense a * rate2 c res tol A / (1 + offense a / tol) * (/ (1 + r * T) * T)) by (field; repeat split; nra).
    assert (Hm : slope L * offense a * rate2 c res tol A / (1 + offense a / tol) * / (2 * r) <=
                 slope L * offense a * rate2 c res tol A / (1 + offense a / tol) * (/ (1 + r * T) * T))
      by (apply Rmult_le_compat_l; assumption).
    lra.
Qed.

End Core2.

(** * The thesis in the rational fragment *)

Section Resources2.

Variable c : R.
Hypothesis c_pos : 0 < c.
Variable res : R.
Hypothesis res_pos : 0 < res.
Variable tol : R.
Hypothesis tol_pos : 0 < tol.
Variable s0 : Vec3.
Variable benefit : Action -> R.

Definition destr1 (a : Action) : R := destruction1 a s0.

Lemma destr1_nonneg : forall a, 0 <= destr1 a.
Proof. intro; apply destruction1_nonneg. Qed.

Notation Surv := (survival2 c res tol tol_pos inverse_square2 rational_law Action destr1 (fun _ => 1)).
Notation Util := (utility2 c res tol tol_pos inverse_square2 rational_law Action destr1 benefit (fun _ => 1)).

Theorem preservation1_survives : forall p x0 T, preserving1_at p s0 -> Surv p x0 T = 1.
Proof. intros p x0 T Hp; apply survival2_of_inoffensive; apply destruction1_zero_iff; exact Hp. Qed.

Theorem destruction1_survival_bound : forall a x0 T,
  T_min c res <= T ->
  Surv a x0 T <= / (1 + destruction1 a s0 * (c / (32 * (res * res * res) * tol)) * T / (1 + destruction1 a s0 / tol)).
Proof.
  intros a x0 T HT.
  assert (H := survival2_upper c c_pos res res_pos tol tol_pos inverse_square2 rational_law Action destr1 destr1_nonneg
                 (fun _ => 1) 1 a x0 T Rle_0_1 (fun o _ => conj (Rle_refl 1) (Rle_refl 1)) HT).
  unfold rate2 in H; simpl (kappa2 inverse_square2) in H; simpl (slope rational_law) in H.
  replace (destruction1 a s0 * (c / (32 * (res * res * res) * tol)) * T / (1 + destruction1 a s0 / tol))
    with (1 * 1 * destr1 a * (1 * c / (32 * (res * res * res) * tol)) * T / (1 + destr1 a / tol))
    by (unfold destr1, Rdiv; ring).
  exact H.
Qed.

Theorem destruction1_survival_vanishes : forall a x0,
  destructive1_at a s0 ->
  forall eps, 0 < eps -> exists T0, forall T, T0 <= T -> Surv a x0 T < eps.
Proof.
  intros a x0 Ha eps Heps.
  apply (survival2_vanishes c c_pos res res_pos tol tol_pos inverse_square2 rational_law Action destr1 destr1_nonneg
           (fun _ => 1) 1 a x0 Rlt_0_1); [apply destruction1_pos_iff; exact Ha | | exact Heps].
  intros T o _; split; apply Rle_refl.
Qed.

Theorem preservation1_crossover : forall x0 p delta B,
  preserving1_at p s0 -> 0 < benefit p -> 0 < delta ->
  forall T, crossover_depth2 c res tol inverse_square2 rational_law 1 delta B (benefit p) < T ->
  forall a, delta <= destruction1 a s0 -> benefit a <= B ->
  Util a x0 T < Util p x0 T.
Proof.
  intros x0 p delta B Hp Hbp Hdelta T HT a Ha HB.
  apply (crossover2 c c_pos res res_pos tol tol_pos inverse_square2 rational_law Action destr1 destr1_nonneg benefit
           (fun _ => 1) 1 x0 p delta B);
    [apply destruction1_zero_iff; exact Hp | exact Hbp | exact Hdelta | lra | exact HT
    | intros o _; split; apply Rle_refl | exact Ha | exact HB].
Qed.

Theorem optimal_destruction1_bound : forall x0 p a B T,
  preserving1_at p s0 -> 0 < benefit p -> benefit a <= B -> T_min c res <= T ->
  Util p x0 T <= Util a x0 T ->
  destruction1 a s0 * (c / (32 * (res * res * res) * tol) * T) <= (B / benefit p - 1) * (1 + destruction1 a s0 / tol).
Proof.
  intros x0 p a B T Hp Hbp HB HT Hopt.
  assert (H := optimal_offense2_le c c_pos res res_pos tol tol_pos inverse_square2 rational_law Action destr1 destr1_nonneg
                 benefit x0 p a B T (proj2 (destruction1_zero_iff p s0) Hp) Hbp HB HT Hopt).
  unfold rate2 in H; simpl (kappa2 inverse_square2) in H; simpl (slope rational_law) in H.
  unfold destr1 in H.
  replace (destruction1 a s0 * (c / (32 * (res * res * res) * tol) * T))
    with (1 * destruction1 a s0 * (1 * c / (32 * (res * res * res) * tol) * T)) by (unfold Rdiv; ring).
  exact H.
Qed.

End Resources2.

(** The thesis with resources measured additively, the lattice filtered by squared distance and the rational response law: it rests on the two axioms beneath every comparison of real numbers. *)
Theorem convergence_rational :
  forall (c res tol : R) (tol_pos : 0 < tol) (s0 x0 : Vec3) (benefit : Action -> R),
  0 < c -> 0 < res ->
  (forall p T, preserving1_at p s0 ->
     survival2 c res tol tol_pos inverse_square2 rational_law Action (destr1 s0) (fun _ => 1) p x0 T = 1) /\
  (forall a, destructive1_at a s0 -> forall eps, 0 < eps ->
     exists T0, forall T, T0 <= T ->
       survival2 c res tol tol_pos inverse_square2 rational_law Action (destr1 s0) (fun _ => 1) a x0 T < eps) /\
  (forall p delta B, preserving1_at p s0 -> 0 < benefit p -> 0 < delta ->
     forall T, crossover_depth2 c res tol inverse_square2 rational_law 1 delta B (benefit p) < T ->
     forall a, delta <= destruction1 a s0 -> benefit a <= B ->
       utility2 c res tol tol_pos inverse_square2 rational_law Action (destr1 s0) benefit (fun _ => 1) a x0 T <
       utility2 c res tol tol_pos inverse_square2 rational_law Action (destr1 s0) benefit (fun _ => 1) p x0 T).
Proof.
  intros c res tol tol_pos s0 x0 benefit Hc Hres.
  repeat split.
  - intros p T Hp; apply (preservation1_survives c res tol tol_pos s0 p x0 T Hp).
  - intros a Ha eps Heps; apply (destruction1_survival_vanishes c Hc res Hres tol tol_pos s0 a x0 Ha eps Heps).
  - intros p delta B Hp Hbp Hd T HT a Ha HB.
    apply (preservation1_crossover c Hc res Hres tol tol_pos s0 benefit x0 p delta B Hp Hbp Hd T HT a Ha HB).
Qed.

(** At the stellar density with the rational law, preservation overtakes any act destroying one tolerance unit for at most a two-fold benefit beyond 450 years. *)
Theorem stellar_crossover_rational : forall s0 x0 (benefit : Action -> R) p a T,
  preserving1_at p s0 -> 0 < benefit p -> 1 <= destruction1 a s0 -> benefit a <= 2 * benefit p ->
  450 * year < T ->
  utility2 (c_u stellar_spacing) res_u tol_u tol_u_pos inverse_square2 rational_law Action (destr1 s0) benefit (fun _ => 1) a x0 T <
  utility2 (c_u stellar_spacing) res_u tol_u tol_u_pos inverse_square2 rational_law Action (destr1 s0) benefit (fun _ => 1) p x0 T.
Proof.
  intros s0 x0 benefit p a T Hp Hbp Hd HB HT.
  assert (Hcu : 0 < c_u stellar_spacing) by (apply c_u_pos, stellar_spacing_pos).
  apply (preservation1_crossover (c_u stellar_spacing) Hcu res_u res_u_pos tol_u tol_u_pos s0 benefit x0 p 1
           (2 * benefit p) Hp Hbp Rlt_0_1 T); [| exact Hd | exact HB].
  unfold crossover_depth2; apply Rmax_lub_lt.
  - assert (Hb := stellar_depth_min_bounds); unfold stellar_depth_min, depth_min in Hb; unfold year in *; lra.
  - unfold rate2, tol_u, res_u; simpl (kappa2 inverse_square2); simpl (slope rational_law).
    replace (2 * benefit p / benefit p - 1) with 1 by (field; repeat split; lra).
    assert (Hr := stellar_rate_bounds); unfold stellar_rate in Hr.
    rewrite (hazard_rate_eq stellar_spacing stellar_spacing_pos) in Hr.
    replace ((1 + 1 / 1) * 1 / (1 * 1 * 1 * (1 * c_u stellar_spacing / (32 * (1 * 1 * 1) * 1))))
      with (2 / (c_SI / (32 * stellar_spacing))) by (unfold c_u; field; repeat split; unfold c_SI, stellar_spacing; lra).
    apply div_lt_a; [unfold c_SI, stellar_spacing; apply Rdiv_lt_0_compat; lra |].
    assert (Hprod : 1409 / 10000000000000 * (450 * year) <= c_SI / (32 * stellar_spacing) * (450 * year))
      by (apply Rmult_le_compat_r; [unfold year; lra | lra]).
    assert (Hlt : c_SI / (32 * stellar_spacing) * (450 * year) < c_SI / (32 * stellar_spacing) * T).
    { apply Rmult_lt_compat_l; [unfold c_SI, stellar_spacing; apply Rdiv_lt_0_compat; lra | exact HT]. }
    unfold year in *; lra.
Qed.

Print Assumptions convergence_rational.
Print Assumptions stellar_crossover_rational.
Print Assumptions hyperbolic_cap.
