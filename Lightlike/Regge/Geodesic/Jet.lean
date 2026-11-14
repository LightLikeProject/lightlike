import Lightlike.Regge.Geodesic.Exp

/-!
# Jets of a metric at a point

Step 4 of RC6a, first part: the first and second derivatives of a coordinate metric at a point,
written as matrices; the Christoffel contraction; uniform bounds on compact sets; and Taylor's
theorem with remainder along a segment. For a point `x` and vectors `u, u'`:

* `dmat g x u` is the matrix `Σ_k u_k ∂_k g_{ij}(x)`, the derivative of `g` in the direction `u`;
* `ddmat g x u u'` is the matrix `Σ_{k,l} u_k u'_l ∂_l ∂_k g_{ij}(x)`;
* `chr g x u v` is the vector `Σ_{j,k} Γ^i_{jk}(x) u_j v_k`.

All three are linear in each vector argument; `dmat` and `ddmat` are symmetric matrices on `U`.

## Main results

* `IsCoordMetric.dot_mulVec_chr`: `g(q, Γ(u, v)) = ½ (∂_u g(q, v) + ∂_v g(q, u) - ∂_q g(u, v))`,
  the lowered Christoffel symbols in terms of directional derivatives.
* `IsCoordMetric.exists_jet_bound`: one bound for the entries of `g`, `g⁻¹`, the first three
  derivatives of `g`, `Γ` and the first derivatives of `Γ` on a compact subset of `U`.
* `taylor_one`, `taylor_two`, `taylor_three`: Taylor's theorem with remainder of order `1, 2, 3`
  along a segment in `U`, for a smooth function, in terms of the partial derivatives `pd`.
-/

open Set Filter Topology Metric
open scoped ContDiff Matrix

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-! ## Derivatives of the metric as matrices -/

/-- The derivative of the metric at `x` in the direction `u`: the matrix
`Σ_k u_k ∂_k g_{ij}(x)`. -/
noncomputable def dmat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k, u k * Lightlike.pd k (fun y => g y i j) x

/-- The second derivative of the metric at `x` in the directions `u, u'`: the matrix
`Σ_{k,l} u_k u'_l ∂_l ∂_k g_{ij}(x)`. -/
noncomputable def ddmat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u u' : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k, ∑ l, u k * u' l * Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) x

/-- The Christoffel contraction `Γ_x(u, v)^i = Σ_{j,k} Γ^i_{jk}(x) u_j v_k`. -/
noncomputable def chr (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u v : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j, ∑ k, Lightlike.christoffel g i j k x * u j * v k

/-- The geodesic acceleration is minus the Christoffel contraction: `accel g x v = -Γ_x(v, v)`. -/
theorem accel_eq_neg_chr (x v : Fin n → ℝ) : accel g x v = -chr g x v v := by
  ext i
  simp [accel, chr]

/-! ### Linearity -/

theorem dmat_add (x u u' : Fin n → ℝ) : dmat g x (u + u') = dmat g x u + dmat g x u' := by
  ext i j; simp [dmat, add_mul, Finset.sum_add_distrib]

theorem dmat_smul (x u : Fin n → ℝ) (c : ℝ) : dmat g x (c • u) = c • dmat g x u := by
  ext i j; simp [dmat, Finset.mul_sum, mul_assoc]

theorem dmat_zero (x : Fin n → ℝ) : dmat g x 0 = 0 := by
  ext i j; simp [dmat]

theorem ddmat_add_left (x u u' v : Fin n → ℝ) :
    ddmat g x (u + u') v = ddmat g x u v + ddmat g x u' v := by
  ext i j; simp [ddmat, add_mul, Finset.sum_add_distrib]

theorem ddmat_add_right (x u v v' : Fin n → ℝ) :
    ddmat g x u (v + v') = ddmat g x u v + ddmat g x u v' := by
  ext i j; simp [ddmat, mul_add, add_mul, Finset.sum_add_distrib]

theorem ddmat_smul_left (x u v : Fin n → ℝ) (c : ℝ) :
    ddmat g x (c • u) v = c • ddmat g x u v := by
  ext i j; simp [ddmat, Finset.mul_sum, mul_assoc]

theorem ddmat_smul_right (x u v : Fin n → ℝ) (c : ℝ) :
    ddmat g x u (c • v) = c • ddmat g x u v := by
  ext i j; simp only [ddmat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem ddmat_zero_left (x v : Fin n → ℝ) : ddmat g x 0 v = 0 := by
  ext i j; simp [ddmat]

theorem chr_add_left (x u u' v : Fin n → ℝ) :
    chr g x (u + u') v = chr g x u v + chr g x u' v := by
  ext i; simp [chr, mul_add, add_mul, Finset.sum_add_distrib]

theorem chr_add_right (x u v v' : Fin n → ℝ) :
    chr g x u (v + v') = chr g x u v + chr g x u v' := by
  ext i; simp [chr, mul_add, Finset.sum_add_distrib]

theorem chr_smul_left (x u v : Fin n → ℝ) (c : ℝ) : chr g x (c • u) v = c • chr g x u v := by
  ext i; simp only [chr, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem chr_smul_right (x u v : Fin n → ℝ) (c : ℝ) : chr g x u (c • v) = c • chr g x u v := by
  ext i; simp only [chr, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem chr_zero_left (x v : Fin n → ℝ) : chr g x 0 v = 0 := by
  ext i; simp [chr]

/-! ### Symmetry -/

/-- For a symmetric matrix, `p ⬝ (M q) = q ⬝ (M p)`. -/
theorem dot_mulVec_comm {M : Matrix (Fin n) (Fin n) ℝ} (hM : Mᵀ = M) (p q : Fin n → ℝ) :
    p ⬝ᵥ (M *ᵥ q) = q ⬝ᵥ (M *ᵥ p) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, dotProduct_comm]

/-- The derivative of the metric is a symmetric matrix on `U`. -/
theorem _root_.Lightlike.IsCoordMetric.dmat_transpose (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (u : Fin n → ℝ) : (dmat g x u)ᵀ = dmat g x u := by
  ext i j
  simp only [dmat, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [hg.pd_symm hx k j i]

/-- The second derivative of the metric is a symmetric matrix on `U`. -/
theorem _root_.Lightlike.IsCoordMetric.ddmat_transpose (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (u u' : Fin n → ℝ) : (ddmat g x u u')ᵀ = ddmat g x u u' := by
  ext i j
  simp only [ddmat, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    rw [Lightlike.pd_congr (hg.eventuallyEq_pd_symm hx k j i) l]

/-! ### The lowered Christoffel symbols -/

/-- **Lowered Christoffel symbols through directional derivatives**: on `U`,
`g(q, Γ(u, v)) = ½ (∂_u g(q, v) + ∂_v g(q, u) - ∂_q g(u, v))`. -/
theorem _root_.Lightlike.IsCoordMetric.dot_mulVec_chr (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (q u v : Fin n → ℝ) :
    q ⬝ᵥ (g x *ᵥ chr g x u v) = (1 / 2) * (q ⬝ᵥ (dmat g x u *ᵥ v) + q ⬝ᵥ (dmat g x v *ᵥ u)
      - u ⬝ᵥ (dmat g x q *ᵥ v)) := by
  have hlow : g x *ᵥ chr g x u v =
      fun ρ => ∑ j, ∑ k, Lightlike.christoffelFirst g ρ j k x * u j * v k := by
    ext ρ
    simp only [Matrix.mulVec, dotProduct, chr, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hg.lower_christoffel hx ρ j k, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hlow]
  simp only [dotProduct, Matrix.mulVec, dmat, Matrix.of_apply, Lightlike.christoffelFirst,
    Finset.mul_sum, Finset.sum_mul]
  -- bring every term to the order of summation `ρ, j, k`
  have e1 : ∀ ρ : Fin n, ∑ k, ∑ j, q ρ * (u j * Lightlike.pd j (fun y => g y ρ k) x * v k) =
      ∑ j, ∑ k, q ρ * (u j * Lightlike.pd j (fun y => g y ρ k) x * v k) := fun ρ => Finset.sum_comm
  have e3 : ∑ j, ∑ k, ∑ ρ, u j * (q ρ * Lightlike.pd ρ (fun y => g y j k) x * v k) =
      ∑ ρ, ∑ j, ∑ k, u j * (q ρ * Lightlike.pd ρ (fun y => g y j k) x * v k) :=
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
  rw [Finset.sum_congr rfl fun ρ _ => e1 ρ, e3, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## Bounds (sup norms) -/

theorem abs_le_norm_apply (p : Fin n → ℝ) (i : Fin n) : |p i| ≤ ‖p‖ := by
  simpa [Real.norm_eq_abs] using norm_le_pi_norm p i

/-- `|Σ_k a_k b_k| ≤ n A B` if `|a_k| ≤ A` and `|b_k| ≤ B`. -/
theorem abs_sum_mul_le {a b : Fin n → ℝ} {A B : ℝ} (hA : 0 ≤ A) (ha : ∀ k, |a k| ≤ A)
    (hb : ∀ k, |b k| ≤ B) : |∑ k, a k * b k| ≤ n * A * B := by
  calc |∑ k, a k * b k| ≤ ∑ k, |a k * b k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, A * B := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]; exact mul_le_mul (ha k) (hb k) (abs_nonneg _) hA
    _ = n * A * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- A bound on the entries bounds the bilinear form: `|p ⬝ (M q)| ≤ n² m ‖p‖ ‖q‖`. -/
theorem abs_dot_mulVec_le {M : Matrix (Fin n) (Fin n) ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hM : ∀ i j, |M i j| ≤ m) (p q : Fin n → ℝ) :
    |p ⬝ᵥ (M *ᵥ q)| ≤ n ^ 2 * m * ‖p‖ * ‖q‖ := by
  have h : |p ⬝ᵥ (M *ᵥ q)| ≤ n * ‖p‖ * (n * m * ‖q‖) :=
    abs_sum_mul_le (norm_nonneg p) (abs_le_norm_apply p) fun i =>
      abs_sum_mul_le hm (hM i) (abs_le_norm_apply q)
  calc _ ≤ _ := h
    _ = n ^ 2 * m * ‖p‖ * ‖q‖ := by ring

/-- `‖M q‖ ≤ n m ‖q‖` if the entries of `M` are bounded by `m`. -/
theorem norm_mulVec_le {M : Matrix (Fin n) (Fin n) ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hM : ∀ i j, |M i j| ≤ m) (q : Fin n → ℝ) : ‖M *ᵥ q‖ ≤ n * m * ‖q‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hm)
    (norm_nonneg q))).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_sum_mul_le hm (hM i) (abs_le_norm_apply q)

/-- Entries of `∂_u g` are bounded by `n m ‖u‖` if the first derivatives are bounded by `m`. -/
theorem abs_dmat_le {x u : Fin n → ℝ} {m : ℝ}
    (hd : ∀ i j k, |Lightlike.pd k (fun y => g y i j) x| ≤ m) (i j : Fin n) :
    |dmat g x u i j| ≤ n * m * ‖u‖ := by
  have h := abs_sum_mul_le (norm_nonneg u) (abs_le_norm_apply u) (hd i j)
  simp only [dmat, Matrix.of_apply]
  calc _ ≤ _ := h
    _ = n * m * ‖u‖ := by ring

/-- Entries of `∂_u ∂_{u'} g` are bounded by `n² m ‖u‖ ‖u'‖` if the second derivatives are bounded
by `m`. -/
theorem abs_ddmat_le {x u u' : Fin n → ℝ} {m : ℝ}
    (hd : ∀ i j k l, |Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) x| ≤ m) (i j : Fin n) :
    |ddmat g x u u' i j| ≤ n ^ 2 * m * ‖u‖ * ‖u'‖ := by
  have h : |∑ k, u k * ∑ l, u' l * Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) x| ≤
      n * ‖u‖ * (n * ‖u'‖ * m) :=
    abs_sum_mul_le (norm_nonneg u) (abs_le_norm_apply u) fun k =>
      abs_sum_mul_le (norm_nonneg u') (abs_le_norm_apply u') (hd i j k)
  have e : ddmat g x u u' i j = ∑ k, u k * ∑ l, u' l * Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) x := by
    simp only [ddmat, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  calc _ ≤ _ := h
    _ = n ^ 2 * m * ‖u‖ * ‖u'‖ := by ring

/-- `‖Γ(u, v)‖ ≤ n² m ‖u‖ ‖v‖` if the Christoffel symbols are bounded by `m`. -/
theorem norm_chr_le {x u v : Fin n → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hc : ∀ i j k, |Lightlike.christoffel g i j k x| ≤ m) :
    ‖chr g x u v‖ ≤ n ^ 2 * m * ‖u‖ * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by have := norm_nonneg u; have := norm_nonneg v; positivity)).2
    fun i => ?_
  rw [Real.norm_eq_abs]
  have h : |∑ j, u j * ∑ k, v k * Lightlike.christoffel g i j k x| ≤ n * ‖u‖ * (n * ‖v‖ * m) :=
    abs_sum_mul_le (norm_nonneg u) (abs_le_norm_apply u) fun j =>
      abs_sum_mul_le (norm_nonneg v) (abs_le_norm_apply v) (hc i j)
  have e : chr g x u v i = ∑ j, u j * ∑ k, v k * Lightlike.christoffel g i j k x := by
    simp only [chr, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  calc _ ≤ _ := h
    _ = n ^ 2 * m * ‖u‖ * ‖v‖ := by ring

/-- A finite family of functions continuous on a compact set has a common bound. -/
theorem exists_bound_fintype {ι : Type*} [Fintype ι] {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (f : ι → (Fin n → ℝ) → ℝ) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ m, 0 ≤ m ∧ ∀ i, ∀ z ∈ K, |f i z| ≤ m := by
  choose M hM using fun i => hK.exists_bound_of_continuousOn (hf i)
  refine ⟨∑ i, |M i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i z hz => ?_⟩
  calc |f i z| = ‖f i z‖ := (Real.norm_eq_abs _).symm
    _ ≤ M i := hM i z hz
    _ ≤ |M i| := le_abs_self _
    _ ≤ ∑ i, |M i| := Finset.single_le_sum (fun j _ => abs_nonneg (M j)) (Finset.mem_univ i)

/-- **Uniform bounds for the jets of the metric** on a compact subset `K` of `U`: one `m ≥ 0`
bounds the entries of `g` and `g⁻¹`, the first three partial derivatives of `g`, the Christoffel
symbols and their first partial derivatives. -/
theorem _root_.Lightlike.IsCoordMetric.exists_jet_bound (hg : Lightlike.IsCoordMetric g U)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ m, 0 ≤ m ∧ ∀ z ∈ K, ∀ i j k l p : Fin n,
      |g z i j| ≤ m ∧ |(g z)⁻¹ i j| ≤ m ∧ |Lightlike.pd k (fun y => g y i j) z| ≤ m ∧
      |Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) z| ≤ m ∧
      |Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) z| ≤ m ∧
      |Lightlike.christoffel g i j k z| ≤ m ∧ |Lightlike.pd l (Lightlike.christoffel g i j k) z| ≤ m := by
  have d1 : ∀ k i j, ContDiffOn ℝ ∞ (Lightlike.pd k (fun y => g y i j)) U :=
    fun k i j => hg.contDiffOn_pdg k i j
  have d2 : ∀ k l i j, ContDiffOn ℝ ∞ (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) U :=
    fun k l i j => Lightlike.contDiffOn_pd (d1 k i j) hg.isOpen l
  have d3 : ∀ k l p i j, ContDiffOn ℝ ∞ (Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => g y i j)))) U :=
    fun k l p i j => Lightlike.contDiffOn_pd (d2 k l i j) hg.isOpen p
  have e1 : ∀ i j k l, ContDiffOn ℝ ∞ (Lightlike.pd l (Lightlike.christoffel g i j k)) U :=
    fun i j k l => Lightlike.contDiffOn_pd (hg.contDiffOn_christoffel i j k) hg.isOpen l
  obtain ⟨m1, h1, hm1⟩ := exists_bound_fintype hK (fun (t : Fin n × Fin n) y => g y t.1 t.2)
    fun t => (hg.smooth t.1 t.2).continuousOn.mono hKU
  obtain ⟨m2, h2, hm2⟩ := exists_bound_fintype hK (fun (t : Fin n × Fin n) y => (g y)⁻¹ t.1 t.2)
    fun t => (hg.contDiffOn_inv t.1 t.2).continuousOn.mono hKU
  obtain ⟨m3, h3, hm3⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n) => Lightlike.pd t.1 (fun y => g y t.2.1 t.2.2))
    fun t => (d1 t.1 t.2.1 t.2.2).continuousOn.mono hKU
  obtain ⟨m4, h4, hm4⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n × Fin n) =>
      Lightlike.pd t.2.1 (Lightlike.pd t.1 (fun y => g y t.2.2.1 t.2.2.2)))
    fun t => (d2 t.1 t.2.1 t.2.2.1 t.2.2.2).continuousOn.mono hKU
  obtain ⟨m5, h5, hm5⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n × Fin n × Fin n) =>
      Lightlike.pd t.2.2.1 (Lightlike.pd t.2.1 (Lightlike.pd t.1 (fun y => g y t.2.2.2.1 t.2.2.2.2))))
    fun t => (d3 t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2).continuousOn.mono hKU
  obtain ⟨m6, h6, hm6⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n) => Lightlike.christoffel g t.1 t.2.1 t.2.2)
    fun t => (hg.contDiffOn_christoffel t.1 t.2.1 t.2.2).continuousOn.mono hKU
  obtain ⟨m7, h7, hm7⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n × Fin n) => Lightlike.pd t.2.2.2 (Lightlike.christoffel g t.1 t.2.1 t.2.2.1))
    fun t => (e1 t.1 t.2.1 t.2.2.1 t.2.2.2).continuousOn.mono hKU
  refine ⟨m1 + m2 + m3 + m4 + m5 + m6 + m7, by linarith, fun z hz i j k l p =>
    ⟨(hm1 (i, j) z hz).trans (by linarith), (hm2 (i, j) z hz).trans (by linarith),
      (hm3 (k, i, j) z hz).trans (by linarith), (hm4 (k, l, i, j) z hz).trans (by linarith),
      (hm5 (k, l, p, i, j) z hz).trans (by linarith), (hm6 (i, j, k) z hz).trans (by linarith),
      (hm7 (i, j, k, l) z hz).trans (by linarith)⟩⟩

/-! ## Taylor's theorem along a segment -/

/-- A function vanishing at `0` whose derivative is bounded by `K s^k` on `[0, 1]` is bounded by
`K s^(k+1) / (k+1)` there. -/
theorem abs_le_of_hasDerivAt_le_pow {ψ ψ' : ℝ → ℝ} {K : ℝ} {k : ℕ} (h0 : ψ 0 = 0)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt ψ (ψ' s) s)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, |ψ' s| ≤ K * s ^ k) :
    ∀ s ∈ Icc (0 : ℝ) 1, |ψ s| ≤ K * s ^ (k + 1) / (k + 1) := by
  intro s hs
  have hB : ∀ t, HasDerivAt (fun s : ℝ => K * s ^ (k + 1) / (k + 1)) (K * t ^ k) t := by
    intro t
    have h := ((hasDerivAt_pow (k + 1) t).const_mul K).div_const ((k : ℝ) + 1)
    convert h using 1
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ) (f' := ψ') (a := 0)
    (b := 1) (B := fun s => K * s ^ (k + 1) / (k + 1)) (B' := fun s => K * s ^ k)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (by simp [h0]) hB
    (fun t ht => by simpa [Real.norm_eq_abs] using hb t (Ico_subset_Icc_self ht)) hs
  simpa [Real.norm_eq_abs] using this

/-- One-dimensional Taylor estimate of order `1`. -/
theorem taylor_aux_one {φ0 φ1 : ℝ → ℝ} {K : ℝ}
    (d0 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ0 (φ1 s) s) (hb : ∀ s ∈ Icc (0 : ℝ) 1, |φ1 s| ≤ K) :
    |φ0 1 - φ0 0| ≤ K := by
  have := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ0 s - φ0 0) (ψ' := φ1) (K := K) (k := 0)
    (by simp) (fun s hs => (d0 s hs).sub_const _) (fun s hs => by simpa using hb s hs) 1
    ⟨zero_le_one, le_rfl⟩
  simpa using this

/-- One-dimensional Taylor estimate of order `2`. -/
theorem taylor_aux_two {φ0 φ1 φ2 : ℝ → ℝ} {K : ℝ}
    (d0 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ0 (φ1 s) s)
    (d1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s) (hb : ∀ s ∈ Icc (0 : ℝ) 1, |φ2 s| ≤ K) :
    |φ0 1 - φ0 0 - φ1 0| ≤ K := by
  have h1 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ1 s - φ1 0) (ψ' := φ2) (K := K) (k := 0)
    (by simp) (fun s hs => (d1 s hs).sub_const _) (fun s hs => by simpa using hb s hs)
  have h0 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ0 s - φ0 0 - s * φ1 0)
    (ψ' := fun s => φ1 s - φ1 0) (K := K) (k := 1) (by simp)
    (fun s hs => (((d0 s hs).sub_const _).sub ((hasDerivAt_id' s).mul_const (φ1 0))).congr_deriv
      (by ring))
    (fun s hs => by simpa using h1 s hs) 1 ⟨zero_le_one, le_rfl⟩
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  norm_num at h0
  linarith [h0]

/-- One-dimensional Taylor estimate of order `3`. -/
theorem taylor_aux_three {φ0 φ1 φ2 φ3 : ℝ → ℝ} {K : ℝ}
    (d0 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ0 (φ1 s) s)
    (d1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s)
    (d2 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ2 (φ3 s) s) (hb : ∀ s ∈ Icc (0 : ℝ) 1, |φ3 s| ≤ K) :
    |φ0 1 - φ0 0 - φ1 0 - (1 / 2) * φ2 0| ≤ K := by
  have h2 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ2 s - φ2 0) (ψ' := φ3) (K := K) (k := 0)
    (by simp) (fun s hs => (d2 s hs).sub_const _) (fun s hs => by simpa using hb s hs)
  have h1 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ1 s - φ1 0 - s * φ2 0)
    (ψ' := fun s => φ2 s - φ2 0) (K := K) (k := 1) (by simp)
    (fun s hs => (((d1 s hs).sub_const _).sub ((hasDerivAt_id' s).mul_const (φ2 0))).congr_deriv
      (by ring))
    (fun s hs => by simpa using h2 s hs)
  have h0 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ0 s - φ0 0 - s * φ1 0 - s ^ 2 / 2 * φ2 0)
    (ψ' := fun s => φ1 s - φ1 0 - s * φ2 0) (K := K / 2) (k := 2) (by simp)
    (fun s hs => ((((d0 s hs).sub_const _).sub ((hasDerivAt_id' s).mul_const (φ1 0))).sub
      (((hasDerivAt_pow 2 s).div_const 2).mul_const (φ2 0))).congr_deriv (by simp))
    (fun s hs => (h1 s hs).trans_eq (by push_cast; ring))
    1 ⟨zero_le_one, le_rfl⟩
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  norm_num at h0
  rw [show φ0 1 - φ0 0 - φ1 0 - 1 / 2 * φ2 0 = φ0 1 - φ0 0 - φ1 0 - 2⁻¹ * φ2 0 by ring]
  linarith [h0]

/-- The derivative of `f` along the line `s ↦ x + s w`. -/
theorem hasDerivAt_line {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {x w : Fin n → ℝ} {s : ℝ} (hs : x + s • w ∈ U) :
    HasDerivAt (fun s => f (x + s • w)) (∑ k, w k * Lightlike.pd k f (x + s • w)) s := by
  have hγ : HasDerivAt (fun s : ℝ => x + s • w) w s := by
    simpa using ((hasDerivAt_id' s).smul_const w).const_add x
  exact hasDerivAt_comp_pd (Lightlike.differentiableAt_of_contDiffOn hf hU hs) hγ

/-- **Taylor's theorem of order `1`** along a segment in `U`:
`|f(x + w) - f(x)| ≤ n m ‖w‖` if the first partial derivatives are bounded by `m` on the
segment. -/
theorem taylor_one {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {x w : Fin n → ℝ} (hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • w ∈ U) {m : ℝ}
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k, |Lightlike.pd k f (x + s • w)| ≤ m) :
    |f (x + w) - f x| ≤ n * m * ‖w‖ := by
  have := taylor_aux_one (φ0 := fun s => f (x + s • w))
    (φ1 := fun s => ∑ k, w k * Lightlike.pd k f (x + s • w)) (K := n * ‖w‖ * m)
    (fun s hs => hasDerivAt_line hf hU (hseg s hs))
    (fun s hs => abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) (hm s hs))
  simp only [one_smul, zero_smul, add_zero] at this
  linarith

/-- **Taylor's theorem of order `2`** along a segment in `U`, with the second partial derivatives
bounded by `m` on the segment. -/
theorem taylor_two {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {x w : Fin n → ℝ} (hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • w ∈ U) {m : ℝ}
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k l, |Lightlike.pd l (Lightlike.pd k f) (x + s • w)| ≤ m) :
    |f (x + w) - f x - ∑ k, w k * Lightlike.pd k f x| ≤ n ^ 2 * m * ‖w‖ ^ 2 := by
  have f1 : ∀ k, ContDiffOn ℝ ∞ (Lightlike.pd k f) U := fun k => Lightlike.contDiffOn_pd hf hU k
  have := taylor_aux_two (φ0 := fun s => f (x + s • w))
    (φ1 := fun s => ∑ k, w k * Lightlike.pd k f (x + s • w))
    (φ2 := fun s => ∑ k, w k * ∑ l, w l * Lightlike.pd l (Lightlike.pd k f) (x + s • w))
    (K := n * ‖w‖ * (n * ‖w‖ * m))
    (fun s hs => hasDerivAt_line hf hU (hseg s hs))
    (fun s hs => HasDerivAt.fun_sum fun k _ =>
      (hasDerivAt_line (f1 k) hU (hseg s hs)).const_mul (w k))
    (fun s hs => abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun k =>
      abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun l => hm s hs k l)
  simp only [one_smul, zero_smul, add_zero] at this
  calc _ ≤ _ := this
    _ = n ^ 2 * m * ‖w‖ ^ 2 := by ring

/-- **Taylor's theorem of order `3`** along a segment in `U`, with the third partial derivatives
bounded by `m` on the segment:
`|f(x + w) - f(x) - ∂_w f(x) - ½ ∂_w ∂_w f(x)| ≤ n³ m ‖w‖³`. -/
theorem taylor_three {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {x w : Fin n → ℝ} (hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • w ∈ U) {m : ℝ}
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k l p, |Lightlike.pd p (Lightlike.pd l (Lightlike.pd k f)) (x + s • w)| ≤ m) :
    |f (x + w) - f x - ∑ k, w k * Lightlike.pd k f x
      - (1 / 2) * ∑ k, ∑ l, w k * w l * Lightlike.pd l (Lightlike.pd k f) x| ≤ n ^ 3 * m * ‖w‖ ^ 3 := by
  have f1 : ∀ k, ContDiffOn ℝ ∞ (Lightlike.pd k f) U := fun k => Lightlike.contDiffOn_pd hf hU k
  have f2 : ∀ k l, ContDiffOn ℝ ∞ (Lightlike.pd l (Lightlike.pd k f)) U :=
    fun k l => Lightlike.contDiffOn_pd (f1 k) hU l
  have := taylor_aux_three (φ0 := fun s => f (x + s • w))
    (φ1 := fun s => ∑ k, w k * Lightlike.pd k f (x + s • w))
    (φ2 := fun s => ∑ k, w k * ∑ l, w l * Lightlike.pd l (Lightlike.pd k f) (x + s • w))
    (φ3 := fun s => ∑ k, w k * ∑ l, w l * ∑ p, w p * Lightlike.pd p (Lightlike.pd l (Lightlike.pd k f)) (x + s • w))
    (K := n * ‖w‖ * (n * ‖w‖ * (n * ‖w‖ * m)))
    (fun s hs => hasDerivAt_line hf hU (hseg s hs))
    (fun s hs => HasDerivAt.fun_sum fun k _ =>
      (hasDerivAt_line (f1 k) hU (hseg s hs)).const_mul (w k))
    (fun s hs => HasDerivAt.fun_sum fun k _ => (HasDerivAt.fun_sum fun l _ =>
      (hasDerivAt_line (f2 k l) hU (hseg s hs)).const_mul (w l)).const_mul (w k))
    (fun s hs => abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun k =>
      abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun l =>
        abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun p => hm s hs k l p)
  simp only [one_smul, zero_smul, add_zero] at this
  have e : ∑ k, w k * ∑ l, w l * Lightlike.pd l (Lightlike.pd k f) x =
      ∑ k, ∑ l, w k * w l * Lightlike.pd l (Lightlike.pd k f) x := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← e]
  calc _ ≤ _ := this
    _ = n ^ 3 * m * ‖w‖ ^ 3 := by ring

end Lightlike.Geodesic
