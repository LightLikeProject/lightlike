import Lightlike.Upstream.GeodesicExpansion.Metric
import Mathlib

/-!
# Jets of a metric at a point

The first and second derivatives of a coordinate metric at a point, written as matrices; the
Christoffel contraction; and uniform bounds on compact sets. For a point `x` and vectors `u, u'`:

* `dmat g x u` is the matrix `Σ_k u_k ∂_k g_{ij}(x)`, the derivative of `g` in the direction `u`;
* `ddmat g x u u'` is the matrix `Σ_{k,l} u_k u'_l ∂_l ∂_k g_{ij}(x)`;
* `chr g x u v` is the vector `Σ_{j,k} Γ^i_{jk}(x) u_j v_k`.

All three are linear in each vector argument; `dmat` and `ddmat` are symmetric matrices on `U`.

## Main results

* `IsCoordMetric.dot_mulVec_chr`: `g(q, Γ(u, v)) = ½ (∂_u g(q, v) + ∂_v g(q, u) - ∂_q g(u, v))`,
  the lowered Christoffel symbols in terms of directional derivatives.
* `abs_dot_mulVec_le`, `norm_mulVec_le`, `abs_dmat_le`, `abs_ddmat_le`, `norm_chr_le`:
  sup-norm bounds on these objects from bounds on the entries.
-/

open Matrix Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-! ## Derivatives of the metric as matrices -/

/-- The derivative of the metric at `x` in the direction `u`: the matrix
`Σ_k u_k ∂_k g_{ij}(x)`. -/
def dmat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k, u k * pd k (fun y => g y i j) x

/-- The second derivative of the metric at `x` in the directions `u, u'`: the matrix
`Σ_{k,l} u_k u'_l ∂_l ∂_k g_{ij}(x)`. -/
def ddmat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u u' : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k, ∑ l, u k * u' l * pd l (pd k (fun y => g y i j)) x

/-- The Christoffel contraction `Γ_x(u, v)^i = Σ_{j,k} Γ^i_{jk}(x) u_j v_k`. -/
def chr (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u v : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j, ∑ k, christoffel g i j k x * u j * v k

/-- The acceleration of a geodesic through `x` with velocity `v`: `-Γ(x)(v, v)`. -/
def accel (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x v : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => -∑ j, ∑ k, christoffel g i j k x * v j * v k

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
theorem IsCoordMetric.dmat_transpose (hg : IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (u : Fin n → ℝ) : (dmat g x u)ᵀ = dmat g x u := by
  ext i j
  simp only [dmat, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [hg.pd_symm hx k j i]

/-- The second derivative of the metric is a symmetric matrix on `U`. -/
theorem IsCoordMetric.ddmat_transpose (hg : IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (u u' : Fin n → ℝ) : (ddmat g x u u')ᵀ = ddmat g x u u' := by
  ext i j
  simp only [ddmat, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    rw [pd_congr (hg.eventuallyEq_pd_symm hx k j i) l]

/-! ### The lowered Christoffel symbols -/

/-- **Lowered Christoffel symbols through directional derivatives**: on `U`,
`g(q, Γ(u, v)) = ½ (∂_u g(q, v) + ∂_v g(q, u) - ∂_q g(u, v))`. -/
theorem IsCoordMetric.dot_mulVec_chr (hg : IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (q u v : Fin n → ℝ) :
    q ⬝ᵥ (g x *ᵥ chr g x u v) = (1 / 2) * (q ⬝ᵥ (dmat g x u *ᵥ v) + q ⬝ᵥ (dmat g x v *ᵥ u)
      - u ⬝ᵥ (dmat g x q *ᵥ v)) := by
  have hlow : g x *ᵥ chr g x u v =
      fun ρ => ∑ j, ∑ k, christoffelFirst g ρ j k x * u j * v k := by
    ext ρ
    simp only [Matrix.mulVec, dotProduct, chr, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hg.lower_christoffel hx ρ j k, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hlow]
  simp only [dotProduct, Matrix.mulVec, dmat, Matrix.of_apply, christoffelFirst,
    Finset.mul_sum, Finset.sum_mul]
  -- bring every term to the order of summation `ρ, j, k`
  have e1 : ∀ ρ : Fin n, ∑ k, ∑ j, q ρ * (u j * pd j (fun y => g y ρ k) x * v k) =
      ∑ j, ∑ k, q ρ * (u j * pd j (fun y => g y ρ k) x * v k) := fun ρ => Finset.sum_comm
  have e3 : ∑ j, ∑ k, ∑ ρ, u j * (q ρ * pd ρ (fun y => g y j k) x * v k) =
      ∑ ρ, ∑ j, ∑ k, u j * (q ρ * pd ρ (fun y => g y j k) x * v k) :=
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
    (hd : ∀ i j k, |pd k (fun y => g y i j) x| ≤ m) (i j : Fin n) :
    |dmat g x u i j| ≤ n * m * ‖u‖ := by
  have h := abs_sum_mul_le (norm_nonneg u) (abs_le_norm_apply u) (hd i j)
  simp only [dmat, Matrix.of_apply]
  calc _ ≤ _ := h
    _ = n * m * ‖u‖ := by ring

/-- Entries of `∂_u ∂_{u'} g` are bounded by `n² m ‖u‖ ‖u'‖` if the second derivatives are bounded
by `m`. -/
theorem abs_ddmat_le {x u u' : Fin n → ℝ} {m : ℝ}
    (hd : ∀ i j k l, |pd l (pd k (fun y => g y i j)) x| ≤ m) (i j : Fin n) :
    |ddmat g x u u' i j| ≤ n ^ 2 * m * ‖u‖ * ‖u'‖ := by
  have h : |∑ k, u k * ∑ l, u' l * pd l (pd k (fun y => g y i j)) x| ≤
      n * ‖u‖ * (n * ‖u'‖ * m) :=
    abs_sum_mul_le (norm_nonneg u) (abs_le_norm_apply u) fun k =>
      abs_sum_mul_le (norm_nonneg u') (abs_le_norm_apply u') (hd i j k)
  have e : ddmat g x u u' i j =
      ∑ k, u k * ∑ l, u' l * pd l (pd k (fun y => g y i j)) x := by
    simp only [ddmat, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  calc _ ≤ _ := h
    _ = n ^ 2 * m * ‖u‖ * ‖u'‖ := by ring

/-- `‖Γ(u, v)‖ ≤ n² m ‖u‖ ‖v‖` if the Christoffel symbols are bounded by `m`. -/
theorem norm_chr_le {x u v : Fin n → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hc : ∀ i j k, |christoffel g i j k x| ≤ m) :
    ‖chr g x u v‖ ≤ n ^ 2 * m * ‖u‖ * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by have := norm_nonneg u; have := norm_nonneg v; positivity)).2
    fun i => ?_
  rw [Real.norm_eq_abs]
  have h : |∑ j, u j * ∑ k, v k * christoffel g i j k x| ≤ n * ‖u‖ * (n * ‖v‖ * m) :=
    abs_sum_mul_le (norm_nonneg u) (abs_le_norm_apply u) fun j =>
      abs_sum_mul_le (norm_nonneg v) (abs_le_norm_apply v) (hc i j)
  have e : chr g x u v i = ∑ j, u j * ∑ k, v k * christoffel g i j k x := by
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
theorem IsCoordMetric.exists_jet_bound (hg : IsCoordMetric g U)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ m, 0 ≤ m ∧ ∀ z ∈ K, ∀ i j k l p : Fin n,
      |g z i j| ≤ m ∧ |(g z)⁻¹ i j| ≤ m ∧ |pd k (fun y => g y i j) z| ≤ m ∧
      |pd l (pd k (fun y => g y i j)) z| ≤ m ∧
      |pd p (pd l (pd k (fun y => g y i j))) z| ≤ m ∧
      |christoffel g i j k z| ≤ m ∧ |pd l (christoffel g i j k) z| ≤ m := by
  have d1 : ∀ k i j, ContDiffOn ℝ ∞ (pd k (fun y => g y i j)) U :=
    fun k i j => hg.contDiffOn_pdg k i j
  have d2 : ∀ k l i j, ContDiffOn ℝ ∞ (pd l (pd k (fun y => g y i j))) U :=
    fun k l i j => contDiffOn_pd (d1 k i j) hg.isOpen l
  have d3 : ∀ k l p i j, ContDiffOn ℝ ∞ (pd p (pd l (pd k (fun y => g y i j)))) U :=
    fun k l p i j => contDiffOn_pd (d2 k l i j) hg.isOpen p
  have e1 : ∀ i j k l, ContDiffOn ℝ ∞ (pd l (christoffel g i j k)) U :=
    fun i j k l => contDiffOn_pd (hg.contDiffOn_christoffel i j k) hg.isOpen l
  obtain ⟨m1, h1, hm1⟩ := exists_bound_fintype hK (fun (t : Fin n × Fin n) y => g y t.1 t.2)
    fun t => (hg.smooth t.1 t.2).continuousOn.mono hKU
  obtain ⟨m2, h2, hm2⟩ := exists_bound_fintype hK (fun (t : Fin n × Fin n) y => (g y)⁻¹ t.1 t.2)
    fun t => (hg.contDiffOn_inv t.1 t.2).continuousOn.mono hKU
  obtain ⟨m3, h3, hm3⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n) => pd t.1 (fun y => g y t.2.1 t.2.2))
    fun t => (d1 t.1 t.2.1 t.2.2).continuousOn.mono hKU
  obtain ⟨m4, h4, hm4⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n × Fin n) =>
      pd t.2.1 (pd t.1 (fun y => g y t.2.2.1 t.2.2.2)))
    fun t => (d2 t.1 t.2.1 t.2.2.1 t.2.2.2).continuousOn.mono hKU
  obtain ⟨m5, h5, hm5⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n × Fin n × Fin n) =>
      pd t.2.2.1 (pd t.2.1 (pd t.1 (fun y => g y t.2.2.2.1 t.2.2.2.2))))
    fun t => (d3 t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2).continuousOn.mono hKU
  obtain ⟨m6, h6, hm6⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n) => christoffel g t.1 t.2.1 t.2.2)
    fun t => (hg.contDiffOn_christoffel t.1 t.2.1 t.2.2).continuousOn.mono hKU
  obtain ⟨m7, h7, hm7⟩ := exists_bound_fintype hK
    (fun (t : Fin n × Fin n × Fin n × Fin n) => pd t.2.2.2 (christoffel g t.1 t.2.1 t.2.2.1))
    fun t => (e1 t.1 t.2.1 t.2.2.1 t.2.2.2).continuousOn.mono hKU
  refine ⟨m1 + m2 + m3 + m4 + m5 + m6 + m7, by linarith, fun z hz i j k l p =>
    ⟨(hm1 (i, j) z hz).trans (by linarith), (hm2 (i, j) z hz).trans (by linarith),
      (hm3 (k, i, j) z hz).trans (by linarith), (hm4 (k, l, i, j) z hz).trans (by linarith),
      (hm5 (k, l, p, i, j) z hz).trans (by linarith), (hm6 (i, j, k) z hz).trans (by linarith),
      (hm7 (i, j, k, l) z hz).trans (by linarith)⟩⟩

end Lightlike.Upstream.GeodesicExpansion
