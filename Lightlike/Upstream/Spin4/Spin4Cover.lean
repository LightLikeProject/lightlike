import Mathlib
import Lightlike.Upstream.Spin4.QuaternionSU2

/-!
# `Spin(4)` as a double cover of `SO(4)`, via unit quaternions

`x ↦ p x q⁻¹` for unit quaternions `p, q` is a rotation of `ℍ[ℝ] ≅ ℝ⁴`; every rotation is of this
form, and `(p, q)` and `(p', q')` give the same rotation iff `(p', q') = ±(p, q)`.
Together with `Quaternion.unitaryEquivSU2` this says `SU(2) × SU(2) → SO(4)` is a double cover.

## Main declarations
* `Quaternion.rotIso p q`: the linear isometry `x ↦ p * x * star q`.
* `Quaternion.SO4`: the linear isometries of `ℍ[ℝ]` of determinant `1`.
* `Quaternion.rotHom : unitary ℍ[ℝ] × unitary ℍ[ℝ] →* SO4`.
* `Quaternion.rotHom_surjective`, `Quaternion.rotHom_eq_one_iff`.
-/

open Module Submodule
open scoped Quaternion

namespace Quaternion

/-- The basis `1, i, j, k` of `ℍ[ℝ]`. -/
noncomputable abbrev basisH : Module.Basis (Fin 4) ℝ ℍ[ℝ] :=
  QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1)

lemma basisH_apply (i : Fin 4) :
    basisH i = ![(1 : ℍ[ℝ]), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] i := by
  apply basisH.repr.injective
  ext j
  fin_cases i <;> fin_cases j <;> simp [basisH, Module.Basis.repr_self]

/-- Cofactor expansion of a `4 × 4` determinant. -/
lemma det_fin_four (a b c d e f g h i j k l m n o p : ℝ) :
    (!![a, b, c, d; e, f, g, h; i, j, k, l; m, n, o, p] : Matrix (Fin 4) (Fin 4) ℝ).det =
      a * (f * (k * p - l * o) - g * (j * p - l * n) + h * (j * o - k * n))
      - b * (e * (k * p - l * o) - g * (i * p - l * m) + h * (i * o - k * m))
      + c * (e * (j * p - l * n) - f * (i * p - l * m) + h * (i * n - j * m))
      - d * (e * (j * o - k * n) - f * (i * o - k * m) + g * (i * n - j * m)) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Left multiplication by `q` has determinant `normSq q ^ 2`. -/
lemma det_mulLeft (q : ℍ[ℝ]) : LinearMap.det (LinearMap.mulLeft ℝ q) = normSq q ^ 2 := by
  have hM : LinearMap.toMatrix basisH basisH (LinearMap.mulLeft ℝ q) =
      !![q.re, -q.imI, -q.imJ, -q.imK; q.imI, q.re, -q.imK, q.imJ;
        q.imJ, q.imK, q.re, -q.imI; q.imK, -q.imJ, q.imI, q.re] := by
    ext i j
    rw [LinearMap.toMatrix_apply, basisH_apply]
    fin_cases i <;> fin_cases j <;> simp [basisH]
  rw [← LinearMap.det_toMatrix basisH, hM, det_fin_four, normSq_def']
  ring

/-- Right multiplication by `q` has determinant `normSq q ^ 2`. -/
lemma det_mulRight (q : ℍ[ℝ]) : LinearMap.det (LinearMap.mulRight ℝ q) = normSq q ^ 2 := by
  have hM : LinearMap.toMatrix basisH basisH (LinearMap.mulRight ℝ q) =
      !![q.re, -q.imI, -q.imJ, -q.imK; q.imI, q.re, q.imK, -q.imJ;
        q.imJ, -q.imK, q.re, q.imI; q.imK, q.imJ, -q.imI, q.re] := by
    ext i j
    rw [LinearMap.toMatrix_apply, basisH_apply]
    fin_cases i <;> fin_cases j <;> simp [basisH]
  rw [← LinearMap.det_toMatrix basisH, hM, det_fin_four, normSq_def']
  ring

/-- Quaternion conjugation as a real-linear map. -/
def conjₗ : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] where
  toFun := star
  map_add' := star_add
  map_smul' r x := by ext <;> simp

/-- Conjugation reverses orientation: determinant `-1`. -/
lemma det_conjₗ : LinearMap.det conjₗ = -1 := by
  have hM : LinearMap.toMatrix basisH basisH conjₗ =
      !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
    ext i j
    rw [LinearMap.toMatrix_apply, basisH_apply]
    fin_cases i <;> fin_cases j <;> simp [basisH, conjₗ]
  rw [← LinearMap.det_toMatrix basisH, hM, det_fin_four]
  norm_num

/-- The determinant of `x ↦ p x q` is `normSq p ^ 2 * normSq q ^ 2`. -/
lemma det_mulLeft_comp_mulRight (p q : ℍ[ℝ]) :
    LinearMap.det ((LinearMap.mulLeft ℝ p).comp (LinearMap.mulRight ℝ q)) =
      normSq p ^ 2 * normSq q ^ 2 := by
  rw [LinearMap.det_comp, det_mulLeft, det_mulRight]

/-- `v x̄ v = 2⟪v, x⟫ v - |v|² x`. -/
lemma mul_star_mul_self (v x : ℍ[ℝ]) :
    v * star x * v = (2 * (v * star x).re) • v - normSq v • x := by
  ext <;> simp [normSq_def'] <;> ring

/-- The reflection of `ℍ[ℝ]` in the hyperplane `v^⊥` is `x ↦ -v x̄ v / |v|²`. -/
lemma reflection_eq {v : ℍ[ℝ]} (hv : v ≠ 0) (x : ℍ[ℝ]) :
    reflection (ℝ ∙ v)ᗮ x = (-(normSq v)⁻¹) • (v * star x * v) := by
  have hN : normSq v ≠ 0 := normSq_ne_zero.mpr hv
  have hn : ‖v‖ ^ 2 = normSq v := by rw [normSq_eq_norm_mul_self, sq]
  rw [reflection_orthogonal_apply, reflection_singleton_apply, inner_def]
  simp only [RCLike.ofReal_real_eq_id, id, hn, mul_star_mul_self, two_smul]
  ext <;> simp <;> field_simp <;> ring

/-- The rotation group `SO(4)` of `ℍ[ℝ] ≅ ℝ⁴`: linear isometries of determinant `1`. -/
def SO4 : Subgroup (ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]) where
  carrier := {f | LinearMap.det (f.toLinearEquiv : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]) = 1}
  mul_mem' {f g} hf hg := by
    change LinearMap.det _ = 1
    have : ((f * g).toLinearEquiv : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]) =
        (f.toLinearEquiv : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]) ∘ₗ (g.toLinearEquiv : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]) :=
      LinearMap.ext fun x => rfl
    rw [this, LinearMap.det_comp, hf, hg, one_mul]
  one_mem' := by
    change LinearMap.det _ = 1
    have : ((1 : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]).toLinearEquiv : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]) = LinearMap.id :=
      LinearMap.ext fun x => rfl
    rw [this, LinearMap.det_id]
  inv_mem' {f} hf := by
    change LinearMap.det _ = 1
    have h : (f⁻¹.toLinearEquiv : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]) ∘ₗ (f.toLinearEquiv : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]) =
        LinearMap.id :=
      LinearMap.ext fun x => f.symm_apply_apply x
    have := congrArg LinearMap.det h
    rwa [LinearMap.det_comp, LinearMap.det_id, hf, mul_one] at this

lemma mem_SO4 {f : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]} :
    f ∈ SO4 ↔ LinearMap.det (f.toLinearEquiv : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]) = 1 :=
  Iff.rfl

/-- `x ↦ p x q̄` for unit quaternions `p`, `q`: a linear isometry of `ℍ[ℝ]`. -/
noncomputable def rotIso (p q : unitary ℍ[ℝ]) : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ] where
  toFun x := p * x * star (q : ℍ[ℝ])
  invFun y := star (p : ℍ[ℝ]) * y * q
  map_add' x y := by rw [mul_add, add_mul]
  map_smul' r x := by simp
  left_inv x := by
    simp only [← mul_assoc, Unitary.star_mul_self_of_mem p.2, one_mul]
    rw [mul_assoc, Unitary.star_mul_self_of_mem q.2, mul_one]
  right_inv y := by
    simp only [← mul_assoc, Unitary.mul_star_self_of_mem p.2, one_mul]
    rw [mul_assoc, Unitary.mul_star_self_of_mem q.2, mul_one]
  norm_map' x := by
    change ‖(p : ℍ[ℝ]) * x * star (q : ℍ[ℝ])‖ = ‖x‖
    rw [norm_mul, norm_mul, norm_star, CStarRing.norm_of_mem_unitary p.2,
      CStarRing.norm_of_mem_unitary q.2, one_mul, mul_one]

lemma rotIso_apply (p q : unitary ℍ[ℝ]) (x : ℍ[ℝ]) :
    rotIso p q x = p * x * star (q : ℍ[ℝ]) := rfl

lemma rotIso_mem_SO4 (p q : unitary ℍ[ℝ]) : rotIso p q ∈ SO4 := by
  rw [mem_SO4]
  have : ((rotIso p q).toLinearEquiv : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]) =
      (LinearMap.mulLeft ℝ (p : ℍ[ℝ])).comp (LinearMap.mulRight ℝ (star (q : ℍ[ℝ]))) :=
    LinearMap.ext fun x => (mul_assoc _ _ _)
  rw [this, det_mulLeft_comp_mulRight, normSq_eq_one_of_mem_unitary, normSq_star,
    normSq_eq_one_of_mem_unitary]
  norm_num

/-- The double-cover homomorphism `(p, q) ↦ (x ↦ p x q⁻¹)` from pairs of unit quaternions
(that is, `SU(2) × SU(2)`) to `SO(4)`. -/
noncomputable def rotHom : unitary ℍ[ℝ] × unitary ℍ[ℝ] →* SO4 where
  toFun g := ⟨rotIso g.1 g.2, rotIso_mem_SO4 _ _⟩
  map_one' := by
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    intro x
    simp [rotIso_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    intro x
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, LinearIsometryEquiv.coe_mul,
      Function.comp_apply, rotIso_apply, Submonoid.coe_mul, star_mul, mul_assoc]

lemma rotHom_apply (g : unitary ℍ[ℝ] × unitary ℍ[ℝ]) (x : ℍ[ℝ]) :
    (rotHom g : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]) x = (g.1 : ℍ[ℝ]) * x * star (g.2 : ℍ[ℝ]) := rfl

/-- A product of reflections of `ℍ[ℝ]` is `x ↦ P x Q` or `x ↦ P x̄ Q`. -/
lemma prod_reflections (l : List ℍ[ℝ]) :
    (∃ P Q : ℍ[ℝ], ∀ x, (l.map fun v => reflection (ℝ ∙ v)ᗮ).prod x = P * x * Q) ∨
      (∃ P Q : ℍ[ℝ], ∀ x, (l.map fun v => reflection (ℝ ∙ v)ᗮ).prod x = P * star x * Q) := by
  induction l with
  | nil => exact Or.inl ⟨1, 1, fun x => by simp⟩
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, LinearIsometryEquiv.coe_mul, Function.comp_apply]
    by_cases ha : a = 0
    · have hR : ∀ y, reflection (ℝ ∙ a)ᗮ y = y := fun y => by
        subst ha
        exact reflection_mem_subspace_eq_self
          (by rw [Submodule.mem_orthogonal_singleton_iff_inner_right]; simp)
      simp only [hR]
      exact ih
    · rcases ih with ⟨P, Q, h⟩ | ⟨P, Q, h⟩
      · refine Or.inr ⟨(-(normSq a)⁻¹) • (a * star Q), star P * a, fun x => ?_⟩
        rw [h, reflection_eq ha, star_mul, star_mul, smul_mul_assoc, smul_mul_assoc]
        simp only [mul_assoc]
      · refine Or.inl ⟨(-(normSq a)⁻¹) • (a * star Q), star P * a, fun x => ?_⟩
        rw [h, reflection_eq ha, star_mul, star_mul, star_star, smul_mul_assoc, smul_mul_assoc]
        simp only [mul_assoc]

/-- **Every rotation of `ℝ⁴ ≅ ℍ[ℝ]` is `x ↦ p x q⁻¹`** for unit quaternions `p`, `q`. -/
theorem rotHom_surjective : Function.Surjective rotHom := by
  rintro ⟨f, hf⟩
  obtain ⟨l, -, hl⟩ := f.reflections_generate_dim
  have hnorm : ∀ P Q : ℍ[ℝ], f 1 = P * Q → normSq P * normSq Q = 1 := by
    intro P Q h
    have h1 : ‖f 1‖ = 1 := by rw [LinearIsometryEquiv.norm_map, norm_one]
    rw [h, norm_mul] at h1
    rw [normSq_eq_norm_mul_self, normSq_eq_norm_mul_self]
    nlinarith [h1]
  rcases prod_reflections l with ⟨P, Q, h⟩ | ⟨P, Q, h⟩
  · rw [← hl] at h
    have hPQ := hnorm P Q (by rw [h, mul_one])
    have hP : ‖P‖ ≠ 0 := by
      intro h0
      rw [normSq_eq_norm_mul_self, h0] at hPQ
      simp at hPQ
    set s := ‖P‖
    have hs2 : s * s = normSq P := (normSq_eq_norm_mul_self P).symm
    have hpu : normSq (s⁻¹ • P) = 1 := by
      rw [normSq_smul, ← hs2]; field_simp
    have hqu : normSq (s • Q) = 1 := by
      rw [normSq_smul, sq, hs2, hPQ]
    have hqu' : normSq (star (s • Q)) = 1 := by rw [normSq_star, hqu]
    let p : unitary ℍ[ℝ] := ⟨s⁻¹ • P, mem_unitary_of_normSq_eq_one hpu⟩
    let q : unitary ℍ[ℝ] := ⟨star (s • Q), mem_unitary_of_normSq_eq_one hqu'⟩
    refine ⟨(p, q), Subtype.ext (LinearIsometryEquiv.ext fun x => ?_)⟩
    rw [rotHom_apply, h]
    simp only [p, q, star_star, smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hP,
      one_smul]
  · exfalso
    rw [← hl] at h
    have hPQ := hnorm P Q (by rw [h, star_one, mul_one])
    have hlin : (f.toLinearEquiv : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]) =
        (LinearMap.mulLeft ℝ P).comp ((LinearMap.mulRight ℝ Q).comp conjₗ) :=
      LinearMap.ext fun x => by
        change f x = P * (star x * Q)
        rw [h, mul_assoc]
    rw [mem_SO4, hlin, LinearMap.det_comp, LinearMap.det_comp, det_mulLeft, det_mulRight,
      det_conjₗ] at hf
    have : normSq P ^ 2 * (normSq Q ^ 2 * -1) = -1 := by
      rw [← mul_assoc, ← mul_pow, hPQ]; norm_num
    rw [this] at hf
    norm_num at hf

/-- A quaternion commuting with `i` and `j` is real. -/
lemma eq_coe_of_commute {p : ℍ[ℝ]} (hi : p * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * p)
    (hj : p * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * p) : p = (p.re : ℍ[ℝ]) := by
  have h1 := congrArg (fun x : ℍ[ℝ] => x.imJ) hi
  have h2 := congrArg (fun x : ℍ[ℝ] => x.imK) hi
  have h3 := congrArg (fun x : ℍ[ℝ] => x.imK) hj
  simp at h1 h2 h3
  ext <;> simp <;> linarith

/-- **The kernel of `SU(2) × SU(2) → SO(4)` is `{(1, 1), (-1, -1)}`**, as unit quaternions. -/
theorem rotHom_eq_one_iff (g : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    rotHom g = 1 ↔ (g.1 : ℍ[ℝ]) = 1 ∧ (g.2 : ℍ[ℝ]) = 1 ∨
      (g.1 : ℍ[ℝ]) = -1 ∧ (g.2 : ℍ[ℝ]) = -1 := by
  rcases g with ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  constructor
  · intro hg
    have hx : ∀ x : ℍ[ℝ], p * x * star q = x :=
      fun x => by
        have := rotHom_apply (⟨p, hp⟩, ⟨q, hq⟩) x
        rw [hg] at this
        exact this.symm.trans rfl
    simp only
    have hpq : p = q := by
      have h1 := hx 1
      rw [mul_one] at h1
      calc p = p * (star q * q) := by rw [Unitary.star_mul_self_of_mem hq, mul_one]
        _ = q := by rw [← mul_assoc, h1, one_mul]
    subst hpq
    have hcomm : ∀ x : ℍ[ℝ], p * x = x * p := fun x => by
      have := congrArg (· * p) (hx x)
      simp only [mul_assoc, Unitary.star_mul_self_of_mem hp, mul_one] at this
      exact this
    have hre := eq_coe_of_commute (hcomm _) (hcomm _)
    have hn : p.re ^ 2 = 1 := by
      have := normSq_eq_one_of_mem_unitary ⟨p, hp⟩
      simp only at this
      rw [hre, normSq_coe] at this
      exact this
    rw [sq, mul_self_eq_one_iff] at hn
    rcases hn with h | h
    · left
      have : p = 1 := by rw [hre, h]; rfl
      exact ⟨this, this⟩
    · right
      have : p = -1 := by rw [hre, h]; simp
      exact ⟨this, this⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · apply Subtype.ext
      apply LinearIsometryEquiv.ext
      intro x
      rw [rotHom_apply, h1, h2]
      simp
    · apply Subtype.ext
      apply LinearIsometryEquiv.ext
      intro x
      rw [rotHom_apply, h1, h2]
      simp

/-- Trust check: the kernel is nontrivial, `(-1, -1)` acts as the identity but is not `(1, 1)`. -/
example : (-1 : ℍ[ℝ]) ≠ 1 := by
  intro h
  have := congrArg QuaternionAlgebra.re h
  simp at this
  norm_num at this

end Quaternion
