import Mathlib

/-!
# Complex projective space as a complex manifold

`ℙ ℂ (Fin (n + 1) → ℂ)` (Mathlib's `Projectivization`, algebraic only) gets the quotient topology of
`{v ≠ 0} ⊂ ℂⁿ⁺¹` (`instTopologicalSpace`). The projection is continuous and open
(`continuous_proj`, `isOpenMap_proj`). The standard charts
`U_i = {[v] | v_i ≠ 0} → ℂⁿ`, `[v] ↦ (v_{i.succAbove j} / v_i)_j`, with inverse
`w ↦ [insertNth i 1 w]` (`chart`), are homeomorphisms of the open sets `U_i` onto `ℂⁿ`, every
point lies in one of them (`ChartedSpace`), and the transition maps are analytic, so `ℙⁿ(ℂ)` is a
complex (analytic) manifold modelled on `ℂⁿ` (`isManifold`): `CP 1` and `CP 3` in particular.

## Main results

* `isOpenMap_proj`: the projection `{v ≠ 0} → ℙ` is open (`π⁻¹(π O) = ⋃_c c • O`).
* `isOpen_chartSet`, `continuousOn_chartFun`, `continuous_chartInv`, `chart`: the charts.
* `instChartedSpace`, `isManifold`: the complex manifold `ℙⁿ(ℂ)`.

## References

* T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196, §1.4, p. 9: `CP³` "the space of all complex
  lines through the origin in ℂ⁴" with homogeneous coordinates (1.21); "we can chart CP³ by covering
  it with the coordinate patches U_i = {Z^A ∈ ℂ⁴ | Z^i ≠ 0}; in U_i there are manifestly three
  well-defined complex coordinates given by taking (Z^i)⁻¹ Z^A". Here for every `n`, the coordinate
  `Z^i / Z^i = 1` omitted.
-/

open Set Topology Filter
open scoped LinearAlgebra.Projectivization Manifold ContDiff

noncomputable section

namespace Lightlike.Projective

variable {n : ℕ}

/-- **The quotient topology** on `ℙ ℂ (Fin (n + 1) → ℂ)`, from the nonzero vectors. -/
instance instTopologicalSpace : TopologicalSpace (ℙ ℂ (Fin (n + 1) → ℂ)) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ (Fin (n + 1) → ℂ))))

/-- Complex projective space `ℙⁿ(ℂ)`. -/
abbrev CP (n : ℕ) := ℙ ℂ (Fin (n + 1) → ℂ)

/-- The projection from the nonzero vectors. -/
def proj (v : {v : Fin (n + 1) → ℂ // v ≠ 0}) : CP n := Projectivization.mk ℂ v.1 v.2

lemma isQuotientMap_proj : IsQuotientMap (proj (n := n)) := isQuotientMap_quotient_mk'

lemma continuous_proj : Continuous (proj (n := n)) := isQuotientMap_proj.continuous

lemma isOpen_iff {s : Set (CP n)} : IsOpen s ↔ IsOpen (proj ⁻¹' s) :=
  isQuotientMap_proj.isOpen_preimage.symm

/-- Scaling of nonzero vectors by a unit. -/
def scale (c : ℂˣ) (v : {v : Fin (n + 1) → ℂ // v ≠ 0}) : {v : Fin (n + 1) → ℂ // v ≠ 0} :=
  ⟨(c : ℂ) • v.1, smul_ne_zero c.ne_zero v.2⟩

lemma continuous_scale (c : ℂˣ) : Continuous (scale (n := n) c) :=
  ((continuous_const_smul (c : ℂ)).comp continuous_subtype_val).subtype_mk _

lemma proj_eq_proj_iff (v w : {v : Fin (n + 1) → ℂ // v ≠ 0}) :
    proj v = proj w ↔ ∃ c : ℂˣ, scale c w = v := by
  rw [proj, proj, Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, Subtype.ext (by rw [← hc, Units.smul_def]; rfl)⟩
  · rintro ⟨c, hc⟩; exact ⟨c, by rw [Units.smul_def]; exact congrArg Subtype.val hc⟩

/-- **The projection is an open map**: `π⁻¹(π O) = ⋃_c c • O`. -/
theorem isOpenMap_proj : IsOpenMap (proj (n := n)) := by
  intro O hO
  rw [isOpen_iff]
  have : proj ⁻¹' (proj '' O) = ⋃ c : ℂˣ, scale c ⁻¹' O := by
    ext w
    simp only [mem_preimage, mem_image, mem_iUnion]
    constructor
    · rintro ⟨v, hv, hvw⟩
      obtain ⟨c, hc⟩ := (proj_eq_proj_iff v w).1 hvw
      exact ⟨c, hc ▸ hv⟩
    · rintro ⟨c, hc⟩
      exact ⟨scale c w, hc, (proj_eq_proj_iff _ _).2 ⟨c, rfl⟩⟩
  rw [this]
  exact isOpen_iUnion fun c => hO.preimage (continuous_scale c)

/-- The representative of `proj v` is a nonzero multiple of `v`. -/
lemma rep_proj (v : {v : Fin (n + 1) → ℂ // v ≠ 0}) : ∃ c : ℂˣ, (proj v).rep = (c : ℂ) • v.1 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v.1 v.2
  exact ⟨a, by rw [proj, ← ha, Units.smul_def]⟩

/-! ## The standard charts -/

/-- The chart domain `U_i = {[v] | v_i ≠ 0}`. -/
def chartSet (i : Fin (n + 1)) : Set (CP n) := {p | p.rep i ≠ 0}

lemma proj_mem_chartSet (v : {v : Fin (n + 1) → ℂ // v ≠ 0}) (i : Fin (n + 1)) :
    proj v ∈ chartSet i ↔ v.1 i ≠ 0 := by
  obtain ⟨c, hc⟩ := rep_proj v
  show (proj v).rep i ≠ 0 ↔ _
  rw [hc]
  simp [c.ne_zero]

lemma isOpen_chartSet (i : Fin (n + 1)) : IsOpen (chartSet (n := n) i) := by
  rw [isOpen_iff]
  have : proj ⁻¹' chartSet i = {v : {v : Fin (n + 1) → ℂ // v ≠ 0} | v.1 i ≠ 0} := by
    ext v; exact proj_mem_chartSet v i
  rw [this]
  exact isOpen_ne_fun ((continuous_apply i).comp continuous_subtype_val) continuous_const

/-- The affine coordinates `(v_{i.succAbove j} / v_i)_j`. -/
def affCoord (i : Fin (n + 1)) (v : Fin (n + 1) → ℂ) : Fin n → ℂ := fun j => v (i.succAbove j) / v i

lemma affCoord_smul (i : Fin (n + 1)) {c : ℂ} (hc : c ≠ 0) (v : Fin (n + 1) → ℂ) :
    affCoord i (c • v) = affCoord i v := by
  funext j
  simp only [affCoord, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc

/-- The chart map `[v] ↦ (v_{i.succAbove j} / v_i)_j`. -/
def chartFun (i : Fin (n + 1)) (p : CP n) : Fin n → ℂ := affCoord i p.rep

lemma chartFun_proj (i : Fin (n + 1)) (v : {v : Fin (n + 1) → ℂ // v ≠ 0}) :
    chartFun i (proj v) = affCoord i v.1 := by
  obtain ⟨c, hc⟩ := rep_proj v
  rw [chartFun, hc, affCoord_smul i c.ne_zero]

/-- The vector `insertNth i 1 w`. -/
def chartInvVec (i : Fin (n + 1)) (w : Fin n → ℂ) : Fin (n + 1) → ℂ := Fin.insertNth i 1 w

lemma chartInvVec_apply_self (i : Fin (n + 1)) (w : Fin n → ℂ) : chartInvVec i w i = 1 :=
  Fin.insertNth_apply_same _ _ _

lemma chartInvVec_ne (i : Fin (n + 1)) (w : Fin n → ℂ) : chartInvVec i w ≠ 0 := fun h => by
  have := congrFun h i
  rw [chartInvVec_apply_self] at this
  exact one_ne_zero this

/-- The inverse chart `w ↦ [insertNth i 1 w]`. -/
def chartInv (i : Fin (n + 1)) (w : Fin n → ℂ) : CP n := proj ⟨chartInvVec i w, chartInvVec_ne i w⟩

lemma chartInv_mem (i : Fin (n + 1)) (w : Fin n → ℂ) : chartInv i w ∈ chartSet i :=
  (proj_mem_chartSet _ i).2 (by
    show chartInvVec i w i ≠ 0
    rw [chartInvVec_apply_self]; exact one_ne_zero)

lemma chartFun_chartInv (i : Fin (n + 1)) (w : Fin n → ℂ) : chartFun i (chartInv i w) = w := by
  rw [chartInv, chartFun_proj]
  funext j
  simp [affCoord, chartInvVec, Fin.insertNth_apply_succAbove]

lemma chartInv_chartFun (i : Fin (n + 1)) {p : CP n} (hp : p ∈ chartSet i) :
    chartInv i (chartFun i p) = p := by
  have hp' : p.rep i ≠ 0 := hp
  have h : chartInvVec i (affCoord i p.rep) = (p.rep i)⁻¹ • p.rep := by
    funext k
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
    · rw [chartInvVec_apply_self, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hp']
    · simp [chartInvVec, Fin.insertNth_apply_succAbove, affCoord, div_eq_inv_mul]
  conv_rhs => rw [← Projectivization.mk_rep p]
  rw [chartInv, chartFun, proj, Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 (p.rep i)⁻¹ (inv_ne_zero hp'), by rw [Units.smul_def, Units.val_mk0, ← h]⟩

lemma continuous_chartInvVec (i : Fin (n + 1)) : Continuous (chartInvVec (n := n) i) :=
  Continuous.finInsertNth i continuous_const continuous_id

lemma continuous_chartInv (i : Fin (n + 1)) : Continuous (chartInv (n := n) i) :=
  continuous_proj.comp ((continuous_chartInvVec i).subtype_mk _)

/-- **The chart map is continuous on `U_i`**: the projection is open. -/
lemma continuousOn_chartFun (i : Fin (n + 1)) : ContinuousOn (chartFun (n := n) i) (chartSet i) := by
  rw [continuousOn_open_iff (isOpen_chartSet i)]
  intro t ht
  have hset : chartSet i ∩ chartFun i ⁻¹' t =
      proj '' ({v : {v : Fin (n + 1) → ℂ // v ≠ 0} | v.1 i ≠ 0} ∩ (fun v => affCoord i v.1) ⁻¹' t) := by
    ext p
    constructor
    · rintro ⟨hp, hpt⟩
      exact ⟨⟨p.rep, p.rep_nonzero⟩, ⟨hp, hpt⟩, Projectivization.mk_rep p⟩
    · rintro ⟨v, ⟨hv, hvt⟩, rfl⟩
      exact ⟨(proj_mem_chartSet v i).2 hv, by rw [mem_preimage, chartFun_proj]; exact hvt⟩
  rw [hset]
  refine isOpenMap_proj _ ?_
  have hc : ContinuousOn (fun v : {v : Fin (n + 1) → ℂ // v ≠ 0} => affCoord i v.1)
      {v : {v : Fin (n + 1) → ℂ // v ≠ 0} | v.1 i ≠ 0} := by
    refine continuousOn_pi.2 fun j => ?_
    exact ((continuous_apply _).comp continuous_subtype_val).continuousOn.div
      ((continuous_apply i).comp continuous_subtype_val).continuousOn fun v hv => hv
  exact hc.isOpen_inter_preimage
    (isOpen_ne_fun ((continuous_apply i).comp continuous_subtype_val) continuous_const) ht

/-- **The standard chart `U_i ≅ ℂⁿ`**, a homeomorphism of the open set `U_i` onto `ℂⁿ`. -/
def chart (i : Fin (n + 1)) : OpenPartialHomeomorph (CP n) (Fin n → ℂ) where
  toFun := chartFun i
  invFun := chartInv i
  source := chartSet i
  target := univ
  map_source' _ _ := mem_univ _
  map_target' w _ := chartInv_mem i w
  left_inv' _ hp := chartInv_chartFun i hp
  right_inv' w _ := chartFun_chartInv i w
  open_source := isOpen_chartSet i
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_chartFun i
  continuousOn_invFun := (continuous_chartInv i).continuousOn

lemma exists_rep_ne (p : CP n) : ∃ i, p.rep i ≠ 0 := by
  by_contra h
  exact p.rep_nonzero (funext fun i => Classical.not_not.1 fun hi => h ⟨i, hi⟩)

/-- A chart index at `p`. -/
def chartIndex (p : CP n) : Fin (n + 1) := (exists_rep_ne p).choose

/-- **`ℙⁿ(ℂ)` is a charted space modelled on `ℂⁿ`**, with the standard charts. -/
instance instChartedSpace : ChartedSpace (Fin n → ℂ) (CP n) where
  atlas := range chart
  chartAt p := chart (chartIndex p)
  mem_chart_source p := (exists_rep_ne p).choose_spec
  chart_mem_atlas _ := mem_range_self _

/-! ## Analytic transition maps -/

lemma contDiff_chartInvVec_apply (j m : Fin (n + 1)) :
    ContDiff ℂ ω (fun w : Fin n → ℂ => chartInvVec j w m) := by
  rcases Fin.eq_self_or_eq_succAbove j m with rfl | ⟨k, rfl⟩
  · simp only [chartInvVec_apply_self]; exact contDiff_const
  · simp only [chartInvVec, Fin.insertNth_apply_succAbove]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).contDiff

/-- The transition map from the chart at `j` to the chart at `i` is analytic on its domain. -/
lemma contDiffOn_transition (i j : Fin (n + 1)) :
    ContDiffOn ℂ ω (chartFun i ∘ chartInv j) {w | chartInvVec j w i ≠ 0} := by
  have h1 : ContDiffOn ℂ ω (fun w => affCoord i (chartInvVec j w)) {w | chartInvVec j w i ≠ 0} := by
    refine contDiffOn_pi.2 fun k => ?_
    exact (contDiff_chartInvVec_apply j _).contDiffOn.div (contDiff_chartInvVec_apply j i).contDiffOn
      fun w hw => hw
  refine h1.congr fun w _ => ?_
  show chartFun i (chartInv j w) = _
  rw [chartInv, chartFun_proj]

/-- **`ℙⁿ(ℂ)` is a complex analytic manifold modelled on `ℂⁿ`.** -/
instance isManifold : IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CP n) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨j, rfl⟩ ⟨i, rfl⟩
  have hsrc : 𝓘(ℂ, Fin n → ℂ).symm ⁻¹' ((chart j).symm ≫ₕ chart i).source ∩
      range 𝓘(ℂ, Fin n → ℂ) = {w | chartInvVec j w i ≠ 0} := by
    ext w
    simp only [modelWithCornersSelf_coe_symm, preimage_id_eq, id_eq, modelWithCornersSelf_coe,
      range_id, inter_univ, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    show w ∈ univ ∧ chartInv j w ∈ chartSet i ↔ _
    rw [chartInv, proj_mem_chartSet]
    simp
  rw [hsrc]
  exact contDiffOn_transition i j

/-! ### `CP¹` and `CP³` -/

example : IsManifold 𝓘(ℂ, Fin 1 → ℂ) ω (CP 1) := inferInstance

example : IsManifold 𝓘(ℂ, Fin 3 → ℂ) ω (CP 3) := inferInstance

end Lightlike.Projective
