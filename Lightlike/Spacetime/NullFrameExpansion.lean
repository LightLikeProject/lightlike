import Lightlike.Spacetime.RaychaudhuriNullManifold

/-!
# The expansion of a null geodesic field in a null frame (G1-012, closed trapped surfaces)

For a nondegenerate symmetric bilinear form `B` on a space `E` of dimension `m + 2`, a **null frame** is `m` orthonormal
vectors `e` orthogonal to a null pair `V`, `N` with `B(V, N) = -1`. In it the trace of a linear map `A` is
`tr A = Σᵢ B(A eᵢ, eᵢ) - B(A V, N) - B(A N, V)` (`NullFrame.trace_eq`).

On a manifold, for the Levi-Civita connection and a smooth null field `V` (`g(V, V) = 0` near `x`) with `∇_V V = 0` at `x`,
`g(∇_u V, V) = 0` (`trappedExp_cov_null`), so the two correction terms vanish and the expansion
`Θ = tr ∇V` (`expansionM`) is the frame expansion `Σᵢ g(∇_{eᵢ} V, eᵢ)` (`trappedExp_expansionM_eq`). This is the link
between the expansion of a null normal field along a surface (`eᵢ` an orthonormal frame of its tangent space, `V`, `N` its
two null normals) and the `Θ` of `raychaudhuri_null_focusing_manifold` (`RaychaudhuriNullManifold.lean`).
-/

open Module Finset

namespace Lightlike.Penrose

/-- A **null frame** for a bilinear form `B`: `m` orthonormal vectors `e`, orthogonal to a null pair `V`, `N`
with `B(V, N) = -1`. -/
structure NullFrame {E : Type*} [AddCommGroup E] [Module ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (m : ℕ) where
  /-- the orthonormal vectors -/
  e : Fin m → E
  /-- the first null vector -/
  V : E
  /-- the second null vector -/
  N : E
  /-- the `e i` are orthonormal -/
  he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0
  /-- `V` is null -/
  hV : B V V = 0
  /-- `N` is null -/
  hN : B N N = 0
  /-- `B(V, N) = -1` -/
  hVN : B V N = -1
  /-- the `e i` are orthogonal to `V` -/
  heV : ∀ i, B (e i) V = 0
  /-- the `e i` are orthogonal to `N` -/
  heN : ∀ i, B (e i) N = 0

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} {m : ℕ}

namespace NullFrame

/-- The vectors of a null frame, indexed by `Fin m ⊕ Fin 2`: `e`, then `V`, then `N`. -/
def vec (F : NullFrame B m) : Fin m ⊕ Fin 2 → E
  | Sum.inl i => F.e i
  | Sum.inr 0 => F.V
  | Sum.inr 1 => F.N

variable (hB : ∀ u v, B u v = B v u) (F : NullFrame B m)
include hB

/-- `B(vec k, e j)` is the Kronecker delta. -/
lemma B_vec_e (k : Fin m ⊕ Fin 2) (j : Fin m) :
    B (F.vec k) (F.e j) = if k = Sum.inl j then 1 else 0 := by
  rcases k with i | k
  · simp [vec, F.he, Sum.inl.injEq]
  · fin_cases k <;> simp [vec, hB F.V, hB F.N, F.heV, F.heN]

/-- `B(vec k, V)` is `-1` exactly for `k = N`. -/
lemma B_vec_V (k : Fin m ⊕ Fin 2) :
    B (F.vec k) F.V = if k = Sum.inr 1 then -1 else 0 := by
  rcases k with i | k
  · simp [vec, F.heV]
  · fin_cases k
    · simp [vec, F.hV]
    · simp [vec, hB F.N, F.hVN]

/-- `B(vec k, N)` is `-1` exactly for `k = V`. -/
lemma B_vec_N (k : Fin m ⊕ Fin 2) :
    B (F.vec k) F.N = if k = Sum.inr 0 then -1 else 0 := by
  rcases k with i | k
  · simp [vec, F.heN]
  · fin_cases k
    · simp [vec, F.hVN]
    · simp [vec, F.hN]

/-- The coordinates of `w` along the null frame. -/
def coord (w : E) : Fin m ⊕ Fin 2 → ℝ
  | Sum.inl i => B w (F.e i)
  | Sum.inr 0 => - B w F.N
  | Sum.inr 1 => - B w F.V

/-- `B(Σ gₖ vecₖ, eⱼ) = gⱼ`. -/
lemma B_sum_e (g : Fin m ⊕ Fin 2 → ℝ) (j : Fin m) :
    B (∑ k, g k • F.vec k) (F.e j) = g (Sum.inl j) := by
  simp [map_sum, B_vec_e hB F]

/-- `B(Σ gₖ vecₖ, V) = -g_N`. -/
lemma B_sum_V (g : Fin m ⊕ Fin 2 → ℝ) :
    B (∑ k, g k • F.vec k) F.V = - g (Sum.inr 1) := by
  simp [map_sum, B_vec_V hB F]

/-- `B(Σ gₖ vecₖ, N) = -g_V`. -/
lemma B_sum_N (g : Fin m ⊕ Fin 2 → ℝ) :
    B (∑ k, g k • F.vec k) F.N = - g (Sum.inr 0) := by
  simp [map_sum, B_vec_N hB F]

/-- The vectors of a null frame are linearly independent. -/
lemma linearIndependent_vec : LinearIndependent ℝ F.vec := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h1 := B_sum_e hB F g
  have h2 := B_sum_V hB F g
  have h3 := B_sum_N hB F g
  rw [hg] at h1 h2 h3
  simp only [map_zero, LinearMap.zero_apply] at h1 h2 h3
  rcases k with i | k
  · linarith [h1 i]
  · fin_cases k
    · show g (Sum.inr 0) = 0
      linarith
    · show g (Sum.inr 1) = 0
      linarith

end NullFrame

/-- The null frame is a basis. -/
noncomputable def NullFrame.basis [FiniteDimensional ℝ E] (hB : ∀ u v, B u v = B v u) (hdim : finrank ℝ E = m + 2) (F : NullFrame B m) :
    Basis (Fin m ⊕ Fin 2) ℝ E :=
  basisOfLinearIndependentOfCardEqFinrank (NullFrame.linearIndependent_vec hB F) (by simp [hdim])

/-- The basis vectors are the frame vectors. -/
lemma NullFrame.basis_apply [FiniteDimensional ℝ E] (hB : ∀ u v, B u v = B v u) (hdim : finrank ℝ E = m + 2) (F : NullFrame B m)
    (k : Fin m ⊕ Fin 2) : F.basis hB hdim k = F.vec k := by
  simp [NullFrame.basis]

/-- Every vector is the sum of its coordinates along the null frame. -/
lemma NullFrame.expand [FiniteDimensional ℝ E] (hnd : ∀ u : E, (∀ v, B u v = 0) → u = 0) (hB : ∀ u v, B u v = B v u)
    (hdim : finrank ℝ E = m + 2) (F : NullFrame B m) (w : E) : w = ∑ k, F.coord w k • F.vec k := by
  set r := w - ∑ k, F.coord w k • F.vec k with hr
  have hBr : ∀ k, B r (F.vec k) = 0 := by
    intro k
    rcases k with i | k
    · have h := NullFrame.B_sum_e hB F (F.coord w) i
      show B (w - ∑ k, F.coord w k • F.vec k) (F.e i) = 0
      rw [map_sub, LinearMap.sub_apply, h]
      simp [NullFrame.coord]
    · fin_cases k
      · have h := NullFrame.B_sum_V hB F (F.coord w)
        show B (w - ∑ k, F.coord w k • F.vec k) F.V = 0
        rw [map_sub, LinearMap.sub_apply, h]
        simp [NullFrame.coord]
      · have h := NullFrame.B_sum_N hB F (F.coord w)
        show B (w - ∑ k, F.coord w k • F.vec k) F.N = 0
        rw [map_sub, LinearMap.sub_apply, h]
        simp [NullFrame.coord]
  have hall : ∀ u, B r u = 0 := by
    intro u
    have hu := (F.basis hB hdim).sum_repr u
    rw [← hu, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [map_smul, NullFrame.basis_apply, hBr, smul_zero]
  exact sub_eq_zero.mp (hnd r hall)

/-- **The trace in a null frame**: for a nondegenerate symmetric form `B` on a space of dimension `m + 2`, an
orthonormal `m`-frame `e` orthogonal to a null pair `V`, `N` with `B(V, N) = -1`, and any linear map `A`,
`tr A = Σᵢ B(A eᵢ, eᵢ) - B(A V, N) - B(A N, V)`. -/
theorem NullFrame.trace_eq [FiniteDimensional ℝ E] (hnd : ∀ u : E, (∀ v, B u v = 0) → u = 0) (hB : ∀ u v, B u v = B v u)
    (hdim : finrank ℝ E = m + 2) (F : NullFrame B m) (A : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E A = ∑ i, B (A (F.e i)) (F.e i) - B (A F.V) F.N - B (A F.N) F.V := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (F.basis hB hdim)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, NullFrame.basis_apply]
  have hrepr : ∀ w k, (F.basis hB hdim).repr w k = F.coord w k := by
    intro w k
    have h := (F.basis hB hdim).repr_sum_self (F.coord w)
    have hw : (∑ k, F.coord w k • (F.basis hB hdim) k) = w := by
      simp only [NullFrame.basis_apply]; exact (F.expand hnd hB hdim w).symm
    rw [hw] at h
    exact congrFun h k
  simp only [hrepr, Fintype.sum_sum_type, Fin.sum_univ_two, NullFrame.vec, NullFrame.coord]
  ring

end Lightlike.Penrose

/-! ## The expansion of a null field in a null frame, on a manifold -/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Matrix Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

/-- The metric at `x` as a bilinear form (a linear map into linear maps) on the tangent space. -/
def metricForm (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x : M) :
    TangentSpace 𝓘(ℝ, Fin n → ℝ) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => g.g x u v) (fun u u' v => by simp) (fun c u v => by simp)
    (fun u v v' => by simp) (fun c u v => by simp)

/-- `metricForm` is the metric. -/
@[simp] lemma metricForm_apply (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x : M)
    (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) : metricForm g x u v = g.g x u v := rfl

variable (cov : Connection 𝓘(ℝ, Fin n → ℝ) M)

/-- A contraction identity: if `∑ₐ gk a * C a b = 0` for every `b`, then `∑ᵢ (∑ⱼ C i j * u j) * gk i = 0`. -/
lemma trappedExp_dot_aux {n : ℕ} (C : Fin n → Fin n → ℝ) (u gk : Fin n → ℝ) (key : ∀ b, ∑ a, gk a * C a b = 0) :
    ∑ i, (∑ j, C i j * u j) * gk i = 0 := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h2 : ∑ i, C i j * u j * gk i = u j * ∑ i, gk i * C i j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2, key j, mul_zero]

/-- **A null field has `g(∇_u V, V) = 0`**: if `g(V, V) = 0` near `x` for a smooth field `V` and the Levi-Civita
connection, then `g(∇_u V, V) = 0` at `x` for every `u`. -/
theorem trappedExp_cov_null (gL : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))) {x : M}
    (hnull : ∀ᶠ q in 𝓝 x, gL.g q (V q) (V q) = 0) (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    gL.g x (cov V x u) (V x) = 0 := by
  set g := gL.toNondegMetric
  have hxs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hx0 : (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) = x :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).left_inv hxs
  have hy0 : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hxs
  have hmd : ∀ q, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) q :=
    fun q => (hV q).mdifferentiableAt (by simp)
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.1
    (hnull.and ((isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_nhds hxs))
  set U := (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target ∩ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm ⁻¹' W with hU
  have hUo : IsOpen U :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hWo
  have hy0U : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ U := ⟨hy0, by simp only [Set.mem_preimage, hx0]; exact hxW⟩
  have hgU : IsCoordMetric (g.coordMetric x) U :=
    (g.isCoordMetric_coordMetric x).of_subset hUo Set.inter_subset_left
  have hvU : ∀ a, ContDiffOn ℝ ∞ (fun y => chartComp x V y a) U := fun a =>
    (contDiffOn_chartComp hV x a).mono Set.inter_subset_left
  have hnormU : ∀ y ∈ U, chartComp x V y ⬝ᵥ (g.coordMetric x y *ᵥ chartComp x V y) = 0 := by
    intro y hy
    have hq := hWsub hy.2
    have e := g_hv x g hy.1 (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)) (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y))
    have hc : chartComp x V y = hv x _ (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)) := rfl
    rw [hc, ← e]
    exact hq.1
  have key := covD_orthogonal_of_const (c := 0) hgU hvU hnormU hy0U
  have hvx : hv x x (V x) = chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
    simp only [chartComp, hx0]; rfl
  rw [g_hv' x g hxs, hv_cov_eq' x cov g h hxs (hmd x) u, hvx]
  simp only [Matrix.mulVec, dotProduct, covDMat, Matrix.of_apply] at key ⊢
  exact trappedExp_dot_aux _ _ _ key

/-- **The expansion of a null geodesic field is the frame expansion** `Σᵢ g(∇_{eᵢ} V, eᵢ)`: for a smooth null field
`V` (`g(V, V) = 0` near `x`) of the Levi-Civita connection with `∇_V V = 0` at `x`, and a null frame `(e, V, N)` of the
tangent space at `x` (`m = n - 2` orthonormal vectors orthogonal to the null pair `V`, `N`, `g(V, N) = -1`), the
expansion `Θ = tr ∇V` is `Σᵢ g(∇_{eᵢ} V, eᵢ)`. -/
theorem trappedExp_expansionM_eq (gL : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))) {x : M}
    (hnull : ∀ᶠ q in 𝓝 x, gL.g q (V q) (V q) = 0) (hgeo : cov V x (V x) = 0) (hn : 2 ≤ n)
    (F : Penrose.NullFrame (metricForm gL.toNondegMetric x) (n - 2)) (hFV : F.V = V x) :
    expansionM cov V x = ∑ i, gL.g x (cov V x (F.e i)) (F.e i) := by
  have hB : ∀ u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      metricForm gL.toNondegMetric x u v = metricForm gL.toNondegMetric x v u := fun u v => gL.symm x u v
  have hnd : ∀ u : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, (∀ v, metricForm gL.toNondegMetric x u v = 0) → u = 0 :=
    fun u hu => gL.nondegenerate x u hu
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) x) = (n - 2) + 2 := by
    show Module.finrank ℝ (Fin n → ℝ) = (n - 2) + 2
    simp [Module.finrank_fin_fun]; omega
  have hT := Penrose.NullFrame.trace_eq hnd hB hdim F
    (cov V x : TangentSpace 𝓘(ℝ, Fin n → ℝ) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
  have h1 : gL.g x (cov V x F.V) F.N = 0 := by rw [hFV, hgeo]; simp
  have h2 : gL.g x (cov V x F.N) F.V = 0 := by rw [hFV]; exact trappedExp_cov_null cov gL h hV hnull F.N
  unfold expansionM
  rw [hT]
  simp only [ContinuousLinearMap.coe_coe, metricForm_apply, h1, h2]
  ring

end Lightlike

end
