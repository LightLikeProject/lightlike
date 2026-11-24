import Lightlike.Geodesic.UniformNormalChart
import Lightlike.Geodesic.LocalCausalityManifold

/-!
# Time balls of uniform radius over a compact set

For a coordinate metric `g` on `U`, a compact `K ⊆ U` and a continuous field `e` of timelike
vectors on `K`, there are `ρ, r > 0` such that for every `p ∈ K` there are a normal chart `φ` and a
field `N` with `IsTimeBall g U p ρ φ (e p) r N` (`Lightlike.Geodesic.exists_uniform_isTimeBall`).
-/

open Set Metric Filter Topology Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ}

/-- **A uniform radius from compactness.** If `F` is continuous on `K × closedBall 0 ρ` and negative
on `K × {0}`, `K` compact, then `F < 0` on `K × ball 0 r` for some `0 < r ≤ ρ`. -/
theorem exists_uniform_radius {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {K : Set E}
    (hK : IsCompact K) {ρ : ℝ} (hρ : 0 < ρ) {F : E × E → ℝ}
    (hF : ContinuousOn F (K ×ˢ closedBall 0 ρ)) (h0 : ∀ p ∈ K, F (p, 0) < 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ p ∈ K, ∀ v ∈ ball (0 : E) r, F (p, v) < 0 := by
  set S : Set (E × E) := K ×ˢ closedBall 0 ρ with hS
  have hSc : IsCompact S := hK.prod (isCompact_closedBall 0 ρ)
  set C : Set (E × E) := S ∩ F ⁻¹' Ici 0 with hC
  have hCc : IsCompact C :=
    hSc.of_isClosed_subset (hF.preimage_isClosed_of_isClosed hSc.isClosed isClosed_Ici)
      inter_subset_left
  have hmemS : ∀ p ∈ K, ∀ v ∈ closedBall (0 : E) ρ, (p, v) ∈ S := fun p hp v hv => ⟨hp, hv⟩
  by_cases hne : C.Nonempty
  · obtain ⟨q, hqC, hmin⟩ := hCc.exists_isMinOn hne
      (f := fun q : E × E => ‖q.2‖) (continuous_snd.norm.continuousOn)
    have hqpos : 0 < ‖q.2‖ := by
      refine norm_pos_iff.2 fun h => ?_
      have h1 := h0 q.1 hqC.1.1
      have h2 : F q ≥ 0 := hqC.2
      have : q = (q.1, 0) := Prod.ext rfl h
      rw [this] at h2
      linarith
    refine ⟨min ρ ‖q.2‖, lt_min hρ hqpos, min_le_left _ _, fun p hp v hv => ?_⟩
    by_contra hcon
    have hv' : ‖v‖ < min ρ ‖q.2‖ := by simpa using hv
    have hvS : (p, v) ∈ S := hmemS p hp v (by
      rw [mem_closedBall_zero_iff]; exact (hv'.trans_le (min_le_left _ _)).le)
    have hvC : (p, v) ∈ C := ⟨hvS, not_lt.1 hcon⟩
    have := hmin hvC
    exact absurd (this.trans_lt (hv'.trans_le (min_le_right _ _))) (lt_irrefl _)
  · refine ⟨ρ, hρ, le_rfl, fun p hp v hv => ?_⟩
    have hvS : (p, v) ∈ S := hmemS p hp v (ball_subset_closedBall hv)
    by_contra hcon
    exact hne ⟨(p, v), hvS, not_lt.1 hcon⟩


/-- Continuity of the matrix inverse on a set where the determinant does not vanish. -/
lemma continuousOn_matrix_inv {X : Type*} [TopologicalSpace X] {S : Set X}
    {M : X → Matrix (Fin n) (Fin n) ℝ} (hM : ContinuousOn M S) (hdet : ∀ x ∈ S, (M x).det ≠ 0) :
    ContinuousOn (fun x => (M x)⁻¹) S := by
  have hM' := (continuousOn_iff_continuous_domRestrict).1 hM
  rw [continuousOn_iff_continuous_domRestrict]
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hM'.matrix_det.inv₀ fun x => hdet x x.2).smul hM'.matrix_adjugate

/-- The field `N` of a time ball: `N v = g(φ v)⁻¹ (Dφ⁻¹)ᵀ g_p e`, the gradient of `-x⁰`. -/
def timeField (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (p e : Fin n → ℝ)
    (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)) (v : Fin n → ℝ) : Fin n → ℝ :=
  (g (φ v))⁻¹ *ᵥ ((LinearMap.toMatrix' ((fderiv ℝ φ.symm (φ v) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))ᵀ *ᵥ (g p *ᵥ e))

/-- The matrix of the derivative of the inverse of a normal chart is the inverse of the matrix of the
derivative of the chart, and the latter is invertible. -/
lemma toMatrix_fderiv_symm {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    {p : Fin n → ℝ} {ρ : ℝ} {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)}
    (h : IsNormalChart g U p ρ φ) {v : Fin n → ℝ} (hv : v ∈ ball (0 : Fin n → ℝ) ρ) :
    LinearMap.toMatrix' ((fderiv ℝ φ.symm (φ v) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
      (LinearMap.toMatrix' ((fderiv ℝ φ v : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))⁻¹ ∧
    (LinearMap.toMatrix' ((fderiv ℝ φ v : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).det ≠ 0 := by
  set B := LinearMap.toMatrix' ((fderiv ℝ φ.symm (φ v) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) with hB
  set A := LinearMap.toMatrix' ((fderiv ℝ φ v : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) with hA
  have hBA : B * A = 1 := by
    rw [hB, hA, ← LinearMap.toMatrix'_comp]
    have : ((fderiv ℝ φ.symm (φ v) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ ((fderiv ℝ φ v : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = LinearMap.id := by
      exact LinearMap.ext fun w => h.fderiv_symm_apply hv w
    rw [this]
    exact LinearMap.toMatrix'_id
  exact ⟨(Matrix.inv_eq_left_inv hBA).symm,
    (Matrix.isUnit_det_of_left_inverse hBA).ne_zero⟩


/-- The properties of the field `N` at one centre: the duality identity, `N 0 = e`, continuity. -/
lemma timeField_props {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : IsCoordMetric g U) {p e : Fin n → ℝ} {ρ : ℝ}
    {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)} (hφ : IsNormalChart g U p ρ φ)
    (hp : p ∈ U) :
    (∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∀ w,
      pairing g (φ v) (timeField g p e φ v) (fderiv ℝ φ v w) = pairing g p e w) ∧
    timeField g p e φ 0 = e ∧ ContinuousOn (timeField g p e φ) (ball 0 ρ) := by
  have hρ := hφ.pos
  have hsrc : ∀ v ∈ ball (0 : Fin n → ℝ) ρ, v ∈ φ.source := fun v hv => by
    rw [hφ.source_eq]; exact hv
  have hmapU : ∀ v ∈ ball (0 : Fin n → ℝ) ρ, φ v ∈ U := fun v hv =>
    hφ.target_subset (φ.map_source (hsrc v hv))
  set L : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun v =>
    LinearMap.toMatrix' ((fderiv ℝ φ.symm (φ v) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) with hLdef
  set N : (Fin n → ℝ) → Fin n → ℝ := fun v => (g (φ v))⁻¹ *ᵥ ((L v)ᵀ *ᵥ (g p *ᵥ e)) with hNdef
  -- `N v` represents `w ↦ g_p (e, w)` through the chart
  have hdual : ∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∀ w,
      pairing g (φ v) (N v) (fderiv ℝ φ v w) = pairing g p e w := by
    intro v hv w
    have hy := hmapU v hv
    have hLw : L v *ᵥ (fderiv ℝ φ v w) = w := by
      simp only [hLdef]
      rw [LinearMap.toMatrix'_mulVec]
      exact hφ.fderiv_symm_apply hv w
    rw [pairing_eq_dotProduct, pairing_eq_dotProduct]
    calc ((g (φ v))⁻¹ *ᵥ ((L v)ᵀ *ᵥ (g p *ᵥ e))) ⬝ᵥ (g (φ v) *ᵥ fderiv ℝ φ v w)
        = (((g (φ v))⁻¹ *ᵥ ((L v)ᵀ *ᵥ (g p *ᵥ e))) ᵥ* g (φ v)) ⬝ᵥ fderiv ℝ φ v w :=
          dotProduct_mulVec _ _ _
      _ = (g (φ v) *ᵥ ((g (φ v))⁻¹ *ᵥ ((L v)ᵀ *ᵥ (g p *ᵥ e)))) ⬝ᵥ fderiv ℝ φ v w := by
          rw [← mulVec_transpose, hg.symm _ hy]
      _ = ((L v)ᵀ *ᵥ (g p *ᵥ e)) ⬝ᵥ fderiv ℝ φ v w := by
          rw [mulVec_mulVec, mul_nonsing_inv _ (hg.isUnit_det _ hy), one_mulVec]
      _ = ((g p *ᵥ e) ᵥ* L v) ⬝ᵥ fderiv ℝ φ v w := by rw [mulVec_transpose]
      _ = (g p *ᵥ e) ⬝ᵥ (L v *ᵥ fderiv ℝ φ v w) := (dotProduct_mulVec _ _ _).symm
      _ = (g p *ᵥ e) ⬝ᵥ w := by rw [hLw]
      _ = (e ᵥ* g p) ⬝ᵥ w := by rw [← mulVec_transpose, hg.symm _ hp]
      _ = e ⬝ᵥ (g p *ᵥ w) := (dotProduct_mulVec _ _ _).symm
  -- `N 0 = e`
  have hD0 : fderiv ℝ φ.symm (φ 0) = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    ext1 w
    have := hφ.fderiv_symm_apply (mem_ball_self hρ) w
    rwa [hφ.hasFDerivAt_zero.fderiv, ContinuousLinearMap.id_apply] at this
  have hN0 : N 0 = e := by
    have hL0 : L 0 = 1 := by
      simp only [hLdef, hD0, ContinuousLinearMap.coe_id]
      exact LinearMap.toMatrix'_id
    simp only [hNdef]
    rw [hL0, transpose_one, one_mulVec, hφ.map_zero, mulVec_mulVec,
      nonsing_inv_mul _ (hg.isUnit_det _ hp), one_mulVec]
  -- continuity of `N`
  have hφc : ContinuousOn φ (ball 0 ρ) := hφ.source_eq ▸ hφ.contDiffOn.continuousOn
  have hDc : ContinuousOn (fun v => fderiv ℝ φ.symm (φ v)) (ball 0 ρ) :=
    (hφ.contDiffOn_symm.continuousOn_fderiv_of_isOpen φ.open_target (by simp)).comp hφc
      (fun v hv => φ.map_source (hsrc v hv))
  have hLc : ContinuousOn L (ball 0 ρ) := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have h1 : ContinuousOn (fun v => fderiv ℝ φ.symm (φ v) (Pi.single j 1) i)
        (ball 0 ρ) := (continuous_apply i).comp_continuousOn (hDc.clm_apply continuousOn_const)
    refine h1.congr fun v _ => ?_
    simp only [hLdef]
    rw [LinearMap.toMatrix'_apply]
    rfl
  have hGc : ContinuousOn (fun v => g (φ v)) (ball 0 ρ) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j =>
      (hg.smooth i j).continuousOn.comp hφc fun v hv => hmapU v hv
  have hNc : ContinuousOn N (ball 0 ρ) := by
    have hG' := (continuousOn_iff_continuous_domRestrict).1 hGc
    have hL' := (continuousOn_iff_continuous_domRestrict).1 hLc
    rw [continuousOn_iff_continuous_domRestrict]
    have hdet : ∀ v : ball (0 : Fin n → ℝ) ρ, (g (φ v)).det ≠ 0 := fun v =>
      (hg.isUnit_det _ (hmapU v v.2)).ne_zero
    have hinv : Continuous fun v : ball (0 : Fin n → ℝ) ρ => (g (φ v))⁻¹ := by
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
      exact (hG'.matrix_det.inv₀ hdet).smul hG'.matrix_adjugate
    exact hinv.matrix_mulVec (hL'.matrix_transpose.matrix_mulVec continuous_const)
  exact ⟨hdual, hN0, hNc⟩


/-- **Time balls of uniform radius over a compact set.** Let `g` be a coordinate metric on `U`,
`K ⊆ U` compact, and `e` a continuous field of timelike vectors on `K`. Then there are `0 < r ≤ ρ`
such that for every `p ∈ K` there are a normal chart `φ` and a field `N` with
`IsTimeBall g U p ρ φ (e p) r N`. -/
theorem exists_uniform_isTimeBall {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : IsCoordMetric g U) {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {e : (Fin n → ℝ) → Fin n → ℝ} (he : ContinuousOn e K)
    (hlt : ∀ p ∈ K, pairing g p (e p) (e p) < 0) :
    ∃ ρ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ p ∈ K, ∃ (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ))
      (N : (Fin n → ℝ) → Fin n → ℝ), IsTimeBall g U p ρ φ (e p) r N := by
  obtain ⟨ρ, hρ, hdom, hch, -⟩ := exists_uniform_normalChart hg hK hKU
  have hch' : ∀ p : Fin n → ℝ, ∃ φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ), p ∈ K →
      IsNormalChart g U p ρ φ ∧ ∀ v ∈ ball (0 : Fin n → ℝ) ρ, φ v = expMap g U (p, v) := by
    intro p
    by_cases hp : p ∈ K
    · obtain ⟨φ, h⟩ := hch p hp
      exact ⟨φ, fun _ => h⟩
    · exact ⟨OpenPartialHomeomorph.refl _, fun h => absurd h hp⟩
  choose φ hφφ using hch'
  have hφ : ∀ p ∈ K, IsNormalChart g U p ρ (φ p) := fun p hp => (hφφ p hp).1
  have hφeq : ∀ p ∈ K, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, φ p v = expMap g U (p, v) :=
    fun p hp => (hφφ p hp).2
  set S : Set ((Fin n → ℝ) × (Fin n → ℝ)) := K ×ˢ ball 0 ρ with hS
  have hSdom : S ⊆ expDomain g U := fun q hq => hdom q.1 hq.1 q.2 hq.2
  have hopen := isOpen_expDomain hg
  have hEcd := contDiffOn_expMap hg
  have hEU : ∀ p ∈ K, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, expMap g U (p, v) ∈ U := by
    intro p hp v hv
    rw [← hφeq p hp v hv]
    exact (hφ p hp).target_subset ((φ p).map_source (by rw [(hφ p hp).source_eq]; exact hv))
  -- the matrix of `D_v exp`
  set Am : (Fin n → ℝ) × (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun q =>
    LinearMap.toMatrix' (((fderiv ℝ (expMap g U) q).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) with hAm
  have hfd : ∀ q ∈ expDomain g U, HasFDerivAt (fun u => expMap g U (q.1, u))
      ((fderiv ℝ (expMap g U) q).comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) q.2 := by
    intro q hq
    have h1 : HasFDerivAt (expMap g U) (fderiv ℝ (expMap g U) q) (q.1, q.2) :=
      ((hEcd.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
    have h2 : HasFDerivAt (fun f : Fin n → ℝ => ((q.1, f) : (Fin n → ℝ) × (Fin n → ℝ)))
        (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)) q.2 := hasFDerivAt_prodMk_right q.1 q.2
    exact HasFDerivAt.comp (g := expMap g U) q.2 h1 h2
  have hAφ : ∀ p ∈ K, ∀ v ∈ ball (0 : Fin n → ℝ) ρ,
      LinearMap.toMatrix' ((fderiv ℝ (φ p) v : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = Am (p, v) := by
    intro p hp v hv
    have hev : φ p =ᶠ[𝓝 v] fun u => expMap g U (p, u) := by
      filter_upwards [isOpen_ball.mem_nhds hv] with u hu using hφeq p hp u hu
    rw [hAm, hev.fderiv_eq]
    exact congrArg _ (congrArg _ (hfd (p, v) (hdom p hp v hv)).fderiv)
  have hAc : ContinuousOn Am S := by
    have hfc : ContinuousOn (fderiv ℝ (expMap g U)) (expDomain g U) :=
      hEcd.continuousOn_fderiv_of_isOpen hopen (by simp)
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have h1 : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
        fderiv ℝ (expMap g U) q (0, Pi.single j 1) i) S :=
      (continuous_apply i).comp_continuousOn ((hfc.mono hSdom).clm_apply continuousOn_const)
    refine h1.congr fun q _ => ?_
    simp only [hAm, LinearMap.toMatrix'_apply]
    rfl
  have hdet : ∀ q ∈ S, (Am q).det ≠ 0 := by
    rintro ⟨p, v⟩ ⟨hp, hv⟩
    rw [← hAφ p hp v hv]
    exact (toMatrix_fderiv_symm (hφ p hp) hv).2
  have hinv : ContinuousOn (fun q => (Am q)⁻¹) S := continuousOn_matrix_inv hAc hdet
  -- the field `N` jointly
  set Nq : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ := fun q =>
    (g (expMap g U q))⁻¹ *ᵥ ((Am q)⁻¹ᵀ *ᵥ (g q.1 *ᵥ e q.1)) with hNq
  have hNeq : ∀ p ∈ K, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, timeField g p (e p) (φ p) v = Nq (p, v) := by
    intro p hp v hv
    have h1 := (toMatrix_fderiv_symm (hφ p hp) hv).1
    rw [hAφ p hp v hv] at h1
    simp only [timeField, hNq]
    rw [h1, hφeq p hp v hv]
  have hEc : ContinuousOn (expMap g U) S := (hEcd.mono hSdom).continuousOn
  have hGc : ∀ i j, ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => g (expMap g U q) i j) S :=
    fun i j => (hg.smooth i j).continuousOn.comp hEc fun q hq => hEU q.1 hq.1 q.2 hq.2
  have hGmat : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => g (expMap g U q)) S :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hGc i j
  have hg1 : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => g q.1) S :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j =>
      ((hg.smooth i j).continuousOn.comp continuousOn_fst fun q hq => hKU hq.1)
  have hec : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => e q.1) S :=
    he.comp continuousOn_fst fun q hq => hq.1
  have hGinv : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (g (expMap g U q))⁻¹) S :=
    continuousOn_matrix_inv hGmat fun q hq => (hg.isUnit_det _ (hEU q.1 hq.1 q.2 hq.2)).ne_zero
  have hNc : ContinuousOn Nq S := by
    have h1 : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => g q.1 *ᵥ e q.1) S :=
      continuousOn_pi.2 fun i => by
        simp only [Matrix.mulVec, dotProduct]
        exact continuousOn_finsetSum _ fun j _ => ((continuous_apply j).comp_continuousOn
          ((continuous_apply i).comp_continuousOn hg1)).mul ((continuous_apply j).comp_continuousOn hec)
    have h1' := (continuousOn_iff_continuous_domRestrict).1 h1
    have hinv' := (continuousOn_iff_continuous_domRestrict).1 hinv
    have hGinv' := (continuousOn_iff_continuous_domRestrict).1 hGinv
    rw [continuousOn_iff_continuous_domRestrict]
    exact hGinv'.matrix_mulVec (hinv'.matrix_transpose.matrix_mulVec h1')
  have hFc : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      pairing g (expMap g U q) (Nq q) (Nq q)) S := by
    simp only [pairing]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact ((continuous_apply i).comp_continuousOn hNc).mul
      ((hGc i j).mul ((continuous_apply j).comp_continuousOn hNc))
  have hF0 : ∀ p ∈ K, pairing g (expMap g U (p, 0)) (Nq (p, 0)) (Nq (p, 0)) < 0 := by
    intro p hp
    have h0 : (0 : Fin n → ℝ) ∈ ball (0 : Fin n → ℝ) ρ := mem_ball_self hρ
    have hN0 := (timeField_props (e := e p) hg (hφ p hp) (hKU hp)).2.1
    rw [hNeq p hp 0 h0] at hN0
    rw [hN0, expMap_zero hg (hKU hp)]
    exact hlt p hp
  have hSub : K ×ˢ closedBall (0 : Fin n → ℝ) (ρ / 2) ⊆ S := fun q hq =>
    ⟨hq.1, closedBall_subset_ball (half_lt_self hρ) hq.2⟩
  obtain ⟨r, hr, hrρ, hrF⟩ := exists_uniform_radius hK (half_pos hρ)
    (F := fun q : (Fin n → ℝ) × (Fin n → ℝ) => pairing g (expMap g U q) (Nq q) (Nq q))
    (hFc.mono hSub) hF0
  refine ⟨ρ, r, hr, hrρ.trans (half_le_self hρ.le), fun p hp => ?_⟩
  have hrb : ball (0 : Fin n → ℝ) r ⊆ ball (0 : Fin n → ℝ) ρ :=
    ball_subset_ball (hrρ.trans (half_le_self hρ.le))
  obtain ⟨hdual, -, hNcont⟩ := timeField_props (e := e p) hg (hφ p hp) (hKU hp)
  refine ⟨φ p, timeField g p (e p) (φ p), ⟨hφ p hp, hr, hrρ.trans (half_le_self hρ.le), hlt p hp,
    fun v hv w => hdual v (hrb hv) w, fun v hv => ?_, hNcont.mono hrb⟩⟩
  rw [hNeq p hp v (hrb hv), hφeq p hp v (hrb hv)]
  exact hrF p hp v hv

/-- **Future time balls of uniform radius over a compact set.** Let `g` be a coordinate metric on `U`,
`K ⊆ U` compact, and `X` a continuous timelike field on `U`. Then there are `0 < r ≤ ρ` and `η > 0`
such that for every `p ∈ K` there are a normal chart `φ` and a field `N` with
`IsTimeBall g U p ρ φ (X p) r N`, `g(N, X) < 0` on the ball, and every `y` within `η` of `p` lies in
`φ (B(0, r))`. -/
theorem exists_uniform_future_timeBall {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : IsCoordMetric g U) {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {e : (Fin n → ℝ) → Fin n → ℝ} (he' : ContinuousOn e U)
    (hlt' : ∀ y ∈ U, pairing g y (e y) (e y) < 0) :
    ∃ ρ r η : ℝ, 0 < r ∧ r ≤ ρ ∧ 0 < η ∧ ∀ p ∈ K, ∃ (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ))
      (N : (Fin n → ℝ) → Fin n → ℝ), IsTimeBall g U p ρ φ (e p) r N ∧
      (∀ v ∈ ball (0 : Fin n → ℝ) r, pairing g (φ v) (N v) (e (φ v)) < 0) ∧
      ∀ y : Fin n → ℝ, Dist.dist y p < η → ∃ v ∈ ball (0 : Fin n → ℝ) r, φ v = y := by
  have he : ContinuousOn e K := he'.mono hKU
  have hlt : ∀ p ∈ K, pairing g p (e p) (e p) < 0 := fun p hp => hlt' p (hKU hp)
  obtain ⟨ρ, hρ, hdom, hch, hη⟩ := exists_uniform_normalChart hg hK hKU
  have hch' : ∀ p : Fin n → ℝ, ∃ φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ), p ∈ K →
      IsNormalChart g U p ρ φ ∧ ∀ v ∈ ball (0 : Fin n → ℝ) ρ, φ v = expMap g U (p, v) := by
    intro p
    by_cases hp : p ∈ K
    · obtain ⟨φ, h⟩ := hch p hp
      exact ⟨φ, fun _ => h⟩
    · exact ⟨OpenPartialHomeomorph.refl _, fun h => absurd h hp⟩
  choose φ hφφ using hch'
  have hφ : ∀ p ∈ K, IsNormalChart g U p ρ (φ p) := fun p hp => (hφφ p hp).1
  have hφeq : ∀ p ∈ K, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, φ p v = expMap g U (p, v) :=
    fun p hp => (hφφ p hp).2
  set S : Set ((Fin n → ℝ) × (Fin n → ℝ)) := K ×ˢ ball 0 ρ with hS
  have hSdom : S ⊆ expDomain g U := fun q hq => hdom q.1 hq.1 q.2 hq.2
  have hopen := isOpen_expDomain hg
  have hEcd := contDiffOn_expMap hg
  have hEU : ∀ p ∈ K, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, expMap g U (p, v) ∈ U := by
    intro p hp v hv
    rw [← hφeq p hp v hv]
    exact (hφ p hp).target_subset ((φ p).map_source (by rw [(hφ p hp).source_eq]; exact hv))
  -- the matrix of `D_v exp`
  set Am : (Fin n → ℝ) × (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun q =>
    LinearMap.toMatrix' (((fderiv ℝ (expMap g U) q).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) with hAm
  have hfd : ∀ q ∈ expDomain g U, HasFDerivAt (fun u => expMap g U (q.1, u))
      ((fderiv ℝ (expMap g U) q).comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) q.2 := by
    intro q hq
    have h1 : HasFDerivAt (expMap g U) (fderiv ℝ (expMap g U) q) (q.1, q.2) :=
      ((hEcd.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
    have h2 : HasFDerivAt (fun f : Fin n → ℝ => ((q.1, f) : (Fin n → ℝ) × (Fin n → ℝ)))
        (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)) q.2 := hasFDerivAt_prodMk_right q.1 q.2
    exact HasFDerivAt.comp (g := expMap g U) q.2 h1 h2
  have hAφ : ∀ p ∈ K, ∀ v ∈ ball (0 : Fin n → ℝ) ρ,
      LinearMap.toMatrix' ((fderiv ℝ (φ p) v : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = Am (p, v) := by
    intro p hp v hv
    have hev : φ p =ᶠ[𝓝 v] fun u => expMap g U (p, u) := by
      filter_upwards [isOpen_ball.mem_nhds hv] with u hu using hφeq p hp u hu
    rw [hAm, hev.fderiv_eq]
    exact congrArg _ (congrArg _ (hfd (p, v) (hdom p hp v hv)).fderiv)
  have hAc : ContinuousOn Am S := by
    have hfc : ContinuousOn (fderiv ℝ (expMap g U)) (expDomain g U) :=
      hEcd.continuousOn_fderiv_of_isOpen hopen (by simp)
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have h1 : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
        fderiv ℝ (expMap g U) q (0, Pi.single j 1) i) S :=
      (continuous_apply i).comp_continuousOn ((hfc.mono hSdom).clm_apply continuousOn_const)
    refine h1.congr fun q _ => ?_
    simp only [hAm, LinearMap.toMatrix'_apply]
    rfl
  have hdet : ∀ q ∈ S, (Am q).det ≠ 0 := by
    rintro ⟨p, v⟩ ⟨hp, hv⟩
    rw [← hAφ p hp v hv]
    exact (toMatrix_fderiv_symm (hφ p hp) hv).2
  have hinv : ContinuousOn (fun q => (Am q)⁻¹) S := continuousOn_matrix_inv hAc hdet
  -- the field `N` jointly
  set Nq : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ := fun q =>
    (g (expMap g U q))⁻¹ *ᵥ ((Am q)⁻¹ᵀ *ᵥ (g q.1 *ᵥ e q.1)) with hNq
  have hNeq : ∀ p ∈ K, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, timeField g p (e p) (φ p) v = Nq (p, v) := by
    intro p hp v hv
    have h1 := (toMatrix_fderiv_symm (hφ p hp) hv).1
    rw [hAφ p hp v hv] at h1
    simp only [timeField, hNq]
    rw [h1, hφeq p hp v hv]
  have hEc : ContinuousOn (expMap g U) S := (hEcd.mono hSdom).continuousOn
  have hGc : ∀ i j, ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => g (expMap g U q) i j) S :=
    fun i j => (hg.smooth i j).continuousOn.comp hEc fun q hq => hEU q.1 hq.1 q.2 hq.2
  have hGmat : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => g (expMap g U q)) S :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hGc i j
  have hg1 : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => g q.1) S :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j =>
      ((hg.smooth i j).continuousOn.comp continuousOn_fst fun q hq => hKU hq.1)
  have hec : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => e q.1) S :=
    he.comp continuousOn_fst fun q hq => hq.1
  have hGinv : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (g (expMap g U q))⁻¹) S :=
    continuousOn_matrix_inv hGmat fun q hq => (hg.isUnit_det _ (hEU q.1 hq.1 q.2 hq.2)).ne_zero
  have hNc : ContinuousOn Nq S := by
    have h1 : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => g q.1 *ᵥ e q.1) S :=
      continuousOn_pi.2 fun i => by
        simp only [Matrix.mulVec, dotProduct]
        exact continuousOn_finsetSum _ fun j _ => ((continuous_apply j).comp_continuousOn
          ((continuous_apply i).comp_continuousOn hg1)).mul ((continuous_apply j).comp_continuousOn hec)
    have h1' := (continuousOn_iff_continuous_domRestrict).1 h1
    have hinv' := (continuousOn_iff_continuous_domRestrict).1 hinv
    have hGinv' := (continuousOn_iff_continuous_domRestrict).1 hGinv
    rw [continuousOn_iff_continuous_domRestrict]
    exact hGinv'.matrix_mulVec (hinv'.matrix_transpose.matrix_mulVec h1')
  have hFc : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      pairing g (expMap g U q) (Nq q) (Nq q)) S := by
    simp only [pairing]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact ((continuous_apply i).comp_continuousOn hNc).mul
      ((hGc i j).mul ((continuous_apply j).comp_continuousOn hNc))
  have hF0 : ∀ p ∈ K, pairing g (expMap g U (p, 0)) (Nq (p, 0)) (Nq (p, 0)) < 0 := by
    intro p hp
    have h0 : (0 : Fin n → ℝ) ∈ ball (0 : Fin n → ℝ) ρ := mem_ball_self hρ
    have hN0 := (timeField_props (e := e p) hg (hφ p hp) (hKU hp)).2.1
    rw [hNeq p hp 0 h0] at hN0
    rw [hN0, expMap_zero hg (hKU hp)]
    exact hlt p hp
  have hecE : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => e (expMap g U q)) S :=
    he'.comp hEc fun q hq => hEU q.1 hq.1 q.2 hq.2
  have hF2c : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      pairing g (expMap g U q) (Nq q) (e (expMap g U q))) S := by
    simp only [pairing]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact ((continuous_apply i).comp_continuousOn hNc).mul
      ((hGc i j).mul ((continuous_apply j).comp_continuousOn hecE))
  have hF20 : ∀ p ∈ K, pairing g (expMap g U (p, 0)) (Nq (p, 0)) (e (expMap g U (p, 0))) < 0 := by
    intro p hp
    have h0 : (0 : Fin n → ℝ) ∈ ball (0 : Fin n → ℝ) ρ := mem_ball_self hρ
    have hN0 := (timeField_props (e := e p) hg (hφ p hp) (hKU hp)).2.1
    rw [hNeq p hp 0 h0] at hN0
    rw [hN0, expMap_zero hg (hKU hp)]
    exact hlt p hp
  have hSub : K ×ˢ closedBall (0 : Fin n → ℝ) (ρ / 2) ⊆ S := fun q hq =>
    ⟨hq.1, closedBall_subset_ball (half_lt_self hρ) hq.2⟩
  obtain ⟨r, hr, hrρ, hrF⟩ := exists_uniform_radius hK (half_pos hρ)
    (F := fun q : (Fin n → ℝ) × (Fin n → ℝ) => pairing g (expMap g U q) (Nq q) (Nq q))
    (hFc.mono hSub) hF0
  obtain ⟨r₂, hr₂, hr₂ρ, hrF₂⟩ := exists_uniform_radius hK (half_pos hρ)
    (F := fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      pairing g (expMap g U q) (Nq q) (e (expMap g U q)))
    (hF2c.mono hSub) hF20
  have hrle : min r r₂ ≤ ρ / 2 := (min_le_left _ _).trans hrρ
  obtain ⟨η, hη0, hηy⟩ := hη (min r r₂) (lt_min hr hr₂) (hrle.trans (half_le_self hρ.le))
  refine ⟨ρ, min r r₂, η, lt_min hr hr₂, hrle.trans (half_le_self hρ.le), hη0, fun p hp => ?_⟩
  have hrb : ball (0 : Fin n → ℝ) (min r r₂) ⊆ ball (0 : Fin n → ℝ) ρ :=
    ball_subset_ball (hrle.trans (half_le_self hρ.le))
  have hrb1 : ball (0 : Fin n → ℝ) (min r r₂) ⊆ ball (0 : Fin n → ℝ) r :=
    ball_subset_ball (min_le_left _ _)
  have hrb2 : ball (0 : Fin n → ℝ) (min r r₂) ⊆ ball (0 : Fin n → ℝ) r₂ :=
    ball_subset_ball (min_le_right _ _)
  obtain ⟨hdual, -, hNcont⟩ := timeField_props (e := e p) hg (hφ p hp) (hKU hp)
  refine ⟨φ p, timeField g p (e p) (φ p), ⟨⟨hφ p hp, lt_min hr hr₂,
    hrle.trans (half_le_self hρ.le), hlt p hp, fun v hv w => hdual v (hrb hv) w, fun v hv => ?_,
    hNcont.mono hrb⟩, fun v hv => ?_, fun y hy => ?_⟩⟩
  · rw [hNeq p hp v (hrb hv), hφeq p hp v (hrb hv)]
    exact hrF p hp v (hrb1 hv)
  · rw [hNeq p hp v (hrb hv), hφeq p hp v (hrb hv)]
    exact hrF₂ p hp v (hrb2 hv)
  · obtain ⟨v, hv, hvy⟩ := hηy p hp y hy
    exact ⟨v, hv, by rw [hφeq p hp v (hrb hv)]; exact hvy⟩


end Lightlike.Geodesic
