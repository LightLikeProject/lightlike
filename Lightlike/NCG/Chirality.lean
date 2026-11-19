import Lightlike.NCG.Uniqueness
import Lightlike.NCG.RealSummands
import Mathlib.LinearAlgebra.Trace

/-!
# The chirality of an orientable finite spectral triple

T. Krajewski, arXiv:hep-th/9701081, Section 3.3, p. 13 (read): "The chirality `χ` commutes with `π(A)` and `J π(A) J⁻¹`,
and is hermitian, so that it can be written as a block diagonal matrix, `χ = ⊕ᵢⱼ I_{nᵢ} ⊗ χᵢⱼ ⊗ I_{nⱼ}`. Since
`χ = ∑_p π(x^p) J π(y^p) J⁻¹`, with `x^p, y^p ∈ A`, `χᵢⱼ` is scalar matrix. Furthermore `χᵢⱼ = ±1` as follows from
`χ² = 1`. We also have `[χ, J] = 0` so that `χᵢⱼ = χⱼᵢ`."

For a complex-linear triple over `⊕ Mₙᵢ(ℂ)` and an orientable grading `γ = ∑_p π(x_p) J π(y_p) J`, `γ` acts on the
multiplicity space `Vᵢⱼ` as the scalar `cᵢⱼ = ∑_p (x_p)ᵢ₀₀ conj((y_p)ⱼ₀₀)`: `E₀₀ x E₀₀ = xᵢ₀₀ E₀₀`, and `J π(E₀₀ y E₀₀) J`
is `conj(yⱼ₀₀)` times `J π(E₀₀) J`.

* `unit_mul_mul_unit`, `lU_pi_lU`, `rU_rightOp_rU`: the corner of `π(a)` and of `J π(b) J` on `Vᵢⱼ`;
* `IsOrientable`, `chiScalar`, `grading_smul_of_mem_Vsub`: the chirality is the scalar `cᵢⱼ` on `Vᵢⱼ`;
* `lU_pi_lU'`, `rU_rightOp_rU'`, `chiScalarAt`, `grading_smul_of_corner`, `chiScalarAt_eq`: the same scalar at every diagonal
  corner;
* `chiScalar_mul_self`, `conj_chiScalar`, `chiScalar_eq_one_or`, `chiScalar_symm`: `cᵢⱼ = ±1` and `cⱼᵢ = cᵢⱼ` on nonzero
  vertices;
* `projC`, `corner`, `corner_comp`, `projC_idem`, `trace_grading_projC`: `Tr(γ π(E^i_αα) J π(E^j_ββ) J) = cᵢⱼ rᵢⱼ`, the
  intersection form in the complex case;
* `trace_grading_sum`: the trace over sums of diagonal corners.
-/

open scoped InnerProductSpace

namespace Lightlike.NCG

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} [∀ i, NeZero (n i)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {T : FiniteSpectralTriple (MatSum n) H} (R : RealStructure T)

/-- `E^i_{00} a E^i_{00} = aᵢ₀₀ E^i_{00}`. -/
lemma unit_mul_mul_unit (a : MatSum n) (i : ι) : unit n i 0 0 * a * unit n i 0 0 = a i 0 0 • unit n i 0 0 :=
  unitC_mul_mul_unitC a i 0 0

/-- `π(E₀₀) π(a) π(E₀₀) = aᵢ₀₀ π(E₀₀)`. -/
lemma lU_pi_lU (hℂ : IsComplexLinear T) (a : MatSum n) (i : ι) (w : H) :
    lU T i 0 0 (T.π a (lU T i 0 0 w)) = a i 0 0 • lU T i 0 0 w := by
  simp only [lU, ContinuousLinearMap.coe_coe]
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, unit_mul_mul_unit,
    hℂ, ContinuousLinearMap.smul_apply]

/-- `J π(E₀₀) J · J π(b) J · J π(E₀₀) J = conj(bⱼ₀₀) J π(E₀₀) J`. -/
lemma rU_rightOp_rU (hℂ : IsComplexLinear T) (b : MatSum n) (j : ι) (w : H) :
    rU R j 0 0 (rightOp R b (rU R j 0 0 w)) = starRingEnd ℂ (b j 0 0) • rU R j 0 0 w := by
  simp only [rU]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← rightOp_mul, ← rightOp_mul, unit_mul_mul_unit,
    rightOp_smul R hℂ, LinearMap.smul_apply]

/-- **An orientable grading** (Krajewski, Section 3.3, p. 13: `χ = ∑_p π(x^p) J π(y^p) J⁻¹`). -/
def IsOrientable (G : Grading T R) {m : ℕ} (x y : Fin m → MatSum n) : Prop :=
  ∀ v, G.γ v = ∑ p, T.π (x p) (rightOp R (y p) v)

/-- The scalar `cᵢⱼ = ∑_p (x_p)ᵢ₀₀ conj((y_p)ⱼ₀₀)` of an orientable grading on the vertex `(i, j)`. -/
def chiScalar {m : ℕ} (x y : Fin m → MatSum n) (i j : ι) : ℂ := ∑ p, x p i 0 0 * starRingEnd ℂ (y p j 0 0)

/-- `γ` commutes with `π(E)`. -/
lemma grading_lU (G : Grading T R) (i : ι) (α β : Fin (n i)) (w : H) :
    G.γ (lU T i α β w) = lU T i α β (G.γ w) := by
  simp only [lU, ContinuousLinearMap.coe_coe]
  rw [← ContinuousLinearMap.mul_apply, G.γ_π, ContinuousLinearMap.mul_apply]

/-- `γ` commutes with `J π(E) J`. -/
lemma grading_rU (G : Grading T R) (j : ι) (α β : Fin (n j)) (w : H) :
    G.γ (rU R j α β w) = rU R j α β (G.γ w) := by
  simp only [rU, rightOp_apply]
  rw [G.γ_J, ← ContinuousLinearMap.mul_apply G.γ, G.γ_π, ContinuousLinearMap.mul_apply, G.γ_J]

/-- **The chirality is a scalar on each multiplicity space** (Krajewski, Section 3.3, p. 13): for an orientable grading,
`γ v = cᵢⱼ v` for `v ∈ Vᵢⱼ`. -/
theorem grading_smul_of_mem_Vsub (hℂ : IsComplexLinear T) (G : Grading T R) {m : ℕ} {x y : Fin m → MatSum n}
    (hG : IsOrientable R G x y) {i j : ι} {v : H} (hv : v ∈ Vsub R i j) :
    G.γ v = chiScalar x y i j • v := by
  have hv' : lU T i 0 0 (rU R j 0 0 v) = v := lU_rU_of_mem_Vsub R hv
  have hrl : ∀ w, rU R j 0 0 (lU T i 0 0 w) = lU T i 0 0 (rU R j 0 0 w) := fun w => (lU_rU R i j 0 0 0 0 w).symm
  have hγ : G.γ v = lU T i 0 0 (rU R j 0 0 (G.γ v)) := by
    conv_lhs => rw [← hv']
    rw [grading_lU, grading_rU]
  have hterm : ∀ p, lU T i 0 0 (rU R j 0 0 (T.π (x p) (rightOp R (y p) v))) =
      (x p i 0 0 * starRingEnd ℂ (y p j 0 0)) • v := fun p => by
    have h1 : rU R j 0 0 (T.π (x p) (rightOp R (y p) v)) = T.π (x p) (rU R j 0 0 (rightOp R (y p) v)) :=
      (R.order_zero (x p) _ _).symm
    have h2 : rightOp R (y p) v = lU T i 0 0 (rightOp R (y p) (rU R j 0 0 v)) := by
      conv_lhs => rw [← hv']
      exact (R.order_zero _ (y p) _).symm
    rw [h1, h2, hrl, rU_rightOp_rU R hℂ]
    simp only [map_smul, ContinuousLinearMap.map_smul, lU_pi_lU hℂ]
    simp only [hv', smul_smul]
    congr 1
    ring
  rw [hγ, hG, map_sum, map_sum]
  simp only [hterm, chiScalar, Finset.sum_smul]

/-- `π(E_αα) π(a) π(E_αα) = aᵢαα π(E_αα)`. -/
lemma lU_pi_lU' (hℂ : IsComplexLinear T) (a : MatSum n) (i : ι) (α : Fin (n i)) (w : H) :
    lU T i α α (T.π a (lU T i α α w)) = a i α α • lU T i α α w := by
  simp only [lU, ContinuousLinearMap.coe_coe]
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul,
    show unit n i α α * a * unit n i α α = a i α α • unit n i α α from unitC_mul_mul_unitC a i α α,
    hℂ, ContinuousLinearMap.smul_apply]

/-- `J π(E_ββ) J · J π(b) J · J π(E_ββ) J = conj(bⱼββ) J π(E_ββ) J`. -/
lemma rU_rightOp_rU' (hℂ : IsComplexLinear T) (b : MatSum n) (j : ι) (β : Fin (n j)) (w : H) :
    rU R j β β (rightOp R b (rU R j β β w)) = starRingEnd ℂ (b j β β) • rU R j β β w := by
  simp only [rU]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← rightOp_mul, ← rightOp_mul,
    show unit n j β β * b * unit n j β β = b j β β • unit n j β β from unitC_mul_mul_unitC b j β β,
    rightOp_smul R hℂ, LinearMap.smul_apply]

/-- The scalar of an orientable grading computed at the corner `(α, β)`. -/
def chiScalarAt {m : ℕ} (x y : Fin m → MatSum n) (i j : ι) (α : Fin (n i)) (β : Fin (n j)) : ℂ :=
  ∑ p, x p i α α * starRingEnd ℂ (y p j β β)

/-- **The chirality at any diagonal corner**: if `π(E^i_αα) J π(E^j_ββ) J v = v`, then `γ v = (∑_p (x_p)ᵢαα
conj((y_p)ⱼββ)) v`. -/
theorem grading_smul_of_corner (hℂ : IsComplexLinear T) (G : Grading T R) {m : ℕ} {x y : Fin m → MatSum n}
    (hG : IsOrientable R G x y) {i j : ι} (α : Fin (n i)) (β : Fin (n j)) {v : H}
    (hv' : lU T i α α (rU R j β β v) = v) : G.γ v = chiScalarAt x y i j α β • v := by
  have hrl : ∀ w, rU R j β β (lU T i α α w) = lU T i α α (rU R j β β w) := fun w => (lU_rU R i j α α β β w).symm
  have hγ : G.γ v = lU T i α α (rU R j β β (G.γ v)) := by
    conv_lhs => rw [← hv']
    rw [grading_lU, grading_rU]
  have hterm : ∀ p, lU T i α α (rU R j β β (T.π (x p) (rightOp R (y p) v))) =
      (x p i α α * starRingEnd ℂ (y p j β β)) • v := fun p => by
    have h1 : rU R j β β (T.π (x p) (rightOp R (y p) v)) = T.π (x p) (rU R j β β (rightOp R (y p) v)) :=
      (R.order_zero (x p) _ _).symm
    have h2 : rightOp R (y p) v = lU T i α α (rightOp R (y p) (rU R j β β v)) := by
      conv_lhs => rw [← hv']
      exact (R.order_zero _ (y p) _).symm
    rw [h1, h2, hrl, rU_rightOp_rU' R hℂ]
    simp only [map_smul, ContinuousLinearMap.map_smul, lU_pi_lU' hℂ]
    simp only [hv', smul_smul]
    congr 1
    ring
  rw [hγ, hG, map_sum, map_sum]
  simp only [hterm, chiScalarAt, Finset.sum_smul]

/-- **The chirality does not depend on the corner**: on a nonzero vertex the scalars at all diagonal corners agree. -/
theorem chiScalarAt_eq (hℂ : IsComplexLinear T) (G : Grading T R) {m : ℕ} {x y : Fin m → MatSum n}
    (hG : IsOrientable R G x y) {i j : ι} {v : H} (hv : v ∈ Vsub R i j) (hv0 : v ≠ 0)
    (α : Fin (n i)) (β : Fin (n j)) : chiScalarAt x y i j α β = chiScalar x y i j := by
  have hv' : lU T i 0 0 (rU R j 0 0 v) = v := lU_rU_of_mem_Vsub R hv
  set w := lU T i α 0 (rU R j β 0 v) with hw
  have hw' : lU T i α α (rU R j β β w) = w := by
    rw [hw, ← lU_rU R i j α 0 β β, rU_rU, if_pos rfl, lU_lU, if_pos rfl]
  have hγw : G.γ w = chiScalar x y i j • w := by
    rw [hw, grading_lU, grading_rU, grading_smul_of_mem_Vsub R hℂ G hG hv, map_smul, map_smul]
  have hw0 : w ≠ 0 := by
    intro h
    apply hv0
    have : lU T i 0 α (rU R j 0 β w) = v := by
      rw [hw, ← lU_rU R i j α 0 0 β, rU_rU, if_pos rfl, lU_lU, if_pos rfl, hv']
    rw [← this, h, map_zero, map_zero]
  have h := (grading_smul_of_corner R hℂ G hG α β hw').symm.trans hγw
  exact smul_left_injective ℂ hw0 h

/-- **`cᵢⱼ² = 1`** on a nonzero vertex (`γ² = 1`). -/
theorem chiScalar_mul_self (hℂ : IsComplexLinear T) (G : Grading T R) {m : ℕ} {x y : Fin m → MatSum n}
    (hG : IsOrientable R G x y) {i j : ι} {v : H} (hv : v ∈ Vsub R i j) (hv0 : v ≠ 0) :
    chiScalar x y i j * chiScalar x y i j = 1 := by
  have h1 : G.γ (G.γ v) = v := by rw [← ContinuousLinearMap.mul_apply, G.γ_γ, ContinuousLinearMap.one_apply]
  rw [grading_smul_of_mem_Vsub R hℂ G hG hv, map_smul, grading_smul_of_mem_Vsub R hℂ G hG hv, smul_smul] at h1
  exact smul_left_injective ℂ hv0 (h1.trans (one_smul ℂ v).symm)

/-- **`cᵢⱼ` is real** on a nonzero vertex (`γ` is self-adjoint). -/
theorem conj_chiScalar (hℂ : IsComplexLinear T) (G : Grading T R) {m : ℕ} {x y : Fin m → MatSum n}
    (hG : IsOrientable R G x y) {i j : ι} {v : H} (hv : v ∈ Vsub R i j) (hv0 : v ≠ 0) :
    starRingEnd ℂ (chiScalar x y i j) = chiScalar x y i j := by
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp G.isSelfAdjoint_γ) v v
  simp only [ContinuousLinearMap.coe_coe, grading_smul_of_mem_Vsub R hℂ G hG hv, inner_smul_left,
    inner_smul_right] at hs
  have hn : (⟪v, v⟫_ℂ) ≠ 0 := inner_self_ne_zero.mpr hv0
  exact mul_right_cancel₀ hn hs

/-- **`cᵢⱼ = ±1`** on a nonzero vertex (Krajewski, Section 3.3, p. 13: "`χᵢⱼ = ±1` as follows from `χ² = 1`"). -/
theorem chiScalar_eq_one_or (hℂ : IsComplexLinear T) (G : Grading T R) {m : ℕ} {x y : Fin m → MatSum n}
    (hG : IsOrientable R G x y) {i j : ι} {v : H} (hv : v ∈ Vsub R i j) (hv0 : v ≠ 0) :
    chiScalar x y i j = 1 ∨ chiScalar x y i j = -1 := by
  have h := chiScalar_mul_self R hℂ G hG hv hv0
  have : (chiScalar x y i j - 1) * (chiScalar x y i j + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h1)

/-- **`cⱼᵢ = cᵢⱼ`** (Krajewski, Section 3.3, p. 13: "`[χ, J] = 0` so that `χᵢⱼ = χⱼᵢ`"): `J` maps `Vᵢⱼ` onto `Vⱼᵢ`
antilinearly and commutes with `γ`. -/
theorem chiScalar_symm (hℂ : IsComplexLinear T) (G : Grading T R) {m : ℕ} {x y : Fin m → MatSum n}
    (hG : IsOrientable R G x y) {i j : ι} {v : H} (hv : v ∈ Vsub R i j) (hv0 : v ≠ 0) :
    chiScalar x y j i = chiScalar x y i j := by
  have hJv := J_mem_Vsub R hv
  have hJ0 : R.J v ≠ 0 := fun h => hv0 (by rw [← R.J_J v, h, map_zero])
  have h := G.γ_J v
  rw [grading_smul_of_mem_Vsub R hℂ G hG hv, LinearMap.map_smulₛₗ, grading_smul_of_mem_Vsub R hℂ G hG hJv,
    conj_chiScalar R hℂ G hG hv hv0] at h
  exact smul_left_injective ℂ hJ0 h

/-- The corner projection `π(E^i_αα) J π(E^j_ββ) J`. -/
def projC (i j : ι) (α : Fin (n i)) (β : Fin (n j)) : H →ₗ[ℂ] H := lU T i α α ∘ₗ rU R j β β

/-- `π(E^i_{αγ}) J π(E^j_{βδ}) J`. -/
def corner (i j : ι) (α γ : Fin (n i)) (β δ : Fin (n j)) : H →ₗ[ℂ] H := lU T i α γ ∘ₗ rU R j β δ

/-- `corner(α γ, β δ) ∘ corner(γ' ε, δ' ζ) = δ_{γγ'} δ_{δδ'} corner(α ε, β ζ)`. -/
lemma corner_comp (i j : ι) (α γ ε : Fin (n i)) (β δ ζ : Fin (n j)) :
    corner R i j α γ β δ ∘ₗ corner R i j γ ε δ ζ = corner R i j α ε β ζ := by
  ext v
  simp only [corner, LinearMap.comp_apply]
  rw [← lU_rU R i j γ ε β δ, lU_lU, if_pos rfl, rU_rU, if_pos rfl]

/-- The corner projection is idempotent. -/
lemma projC_idem (i j : ι) (α : Fin (n i)) (β : Fin (n j)) : IsIdempotentElem (projC R i j α β) := by
  show projC R i j α β ∘ₗ projC R i j α β = projC R i j α β
  exact corner_comp R i j α α α β β β

/-- **The trace of a corner of the chirality is `c r`** (Krajewski, Section 3.3, p. 14, in the complex case:
"`∩ᵢⱼ = Tr[χ π(pᵢ) J π(pⱼ) J⁻¹] = sign(μᵢⱼ) Tr[pᵢ ⊗ I_{|μᵢⱼ|} ⊗ pⱼ] = μᵢⱼ`"): at the corner `(0, 0)` the projection has
range `Vᵢⱼ` and `γ` is `cᵢⱼ` there; another corner is conjugate to it by `corner(α 0, β 0)` and `corner(0 α, 0 β)`. -/
theorem trace_grading_projC (hℂ : IsComplexLinear T) (G : Grading T R) {m : ℕ} {x y : Fin m → MatSum n}
    (hG : IsOrientable R G x y) (i j : ι) (α : Fin (n i)) (β : Fin (n j)) :
    LinearMap.trace ℂ H ((G.γ : H →ₗ[ℂ] H) ∘ₗ projC R i j α β) = chiScalar x y i j * multiplicity R i j := by
  have h0 : (G.γ : H →ₗ[ℂ] H) ∘ₗ projC R i j 0 0 = chiScalar x y i j • projC R i j 0 0 := by
    ext v
    exact grading_smul_of_mem_Vsub R hℂ G hG ⟨v, rfl⟩
  have htr0 : LinearMap.trace ℂ H ((G.γ : H →ₗ[ℂ] H) ∘ₗ projC R i j 0 0) = chiScalar x y i j * multiplicity R i j := by
    rw [h0, map_smul, (LinearMap.IsIdempotentElem.isProj_range _ (projC_idem R i j 0 0)).trace, smul_eq_mul]
    rfl
  have hγA : (G.γ : H →ₗ[ℂ] H) ∘ₗ corner R i j α 0 β 0 = corner R i j α 0 β 0 ∘ₗ (G.γ : H →ₗ[ℂ] H) := by
    ext v
    simp only [corner, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, grading_lU, grading_rU]
  have hP : projC R i j α β = corner R i j α 0 β 0 ∘ₗ projC R i j 0 0 ∘ₗ corner R i j 0 α 0 β := by
    show corner R i j α α β β = corner R i j α 0 β 0 ∘ₗ (corner R i j 0 0 0 0 ∘ₗ corner R i j 0 α 0 β)
    rw [corner_comp, corner_comp]
  have hBA : corner R i j 0 α 0 β ∘ₗ corner R i j α 0 β 0 = projC R i j 0 0 := corner_comp R i j 0 α 0 0 β 0
  rw [hP, ← LinearMap.comp_assoc, hγA, LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc,
    LinearMap.comp_assoc, hBA, show projC R i j 0 0 ∘ₗ projC R i j 0 0 = projC R i j 0 0 from projC_idem R i j 0 0]
  exact htr0

/-- **The trace over sums of corners**: `Tr(γ (∑_t π(E^{k_t}_{α_t α_t})) (∑_u J π(E^{l_u}_{β_u β_u}) J)) =
∑_t ∑_u c_{k_t l_u} r_{k_t l_u}`. -/
theorem trace_grading_sum (hℂ : IsComplexLinear T) (G : Grading T R) {m : ℕ} {x y : Fin m → MatSum n}
    (hG : IsOrientable R G x y) {s s' : Type*} [Fintype s] [Fintype s'] (k : s → ι) (α : ∀ t, Fin (n (k t)))
    (l : s' → ι) (β : ∀ u, Fin (n (l u))) :
    LinearMap.trace ℂ H ((G.γ : H →ₗ[ℂ] H) * (∑ t, lU T (k t) (α t) (α t)) * (∑ u, rU R (l u) (β u) (β u))) =
      ∑ t, ∑ u, chiScalar x y (k t) (l u) * multiplicity R (k t) (l u) := by
  have hexp : (G.γ : H →ₗ[ℂ] H) * (∑ t, lU T (k t) (α t) (α t)) * (∑ u, rU R (l u) (β u) (β u)) =
      ∑ t, ∑ u, (G.γ : H →ₗ[ℂ] H) * (lU T (k t) (α t) (α t) * rU R (l u) (β u) (β u)) := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [hexp, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun u _ => trace_grading_projC R hℂ G hG (k t) (l u) (α t) (β u)

end

end Lightlike.NCG
