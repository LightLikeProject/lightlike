import Lightlike.Spin4.Rep

/-!
# Spin(4) = SU(2) × SU(2) is the double cover of SO(4)

`Spin4` is defined in `Lightlike/Spin4/Rep.lean` as `SU2 × SU2`. Here we prove that it is the double
cover of the rotation group of `ℝ⁴`, modelled as the quaternions `ℍ` with Mathlib's Euclidean inner
product `⟪a, b⟫ = Re(a b̄)` (`Quaternion.linearIsometryEquivTuple` identifies `ℍ` with
`EuclideanSpace ℝ (Fin 4)`).

## Implementation notes

* `toMat : ℍ →ₐ[ℝ] M₂(ℂ)`, `a + bi + cj + dk ↦ [[a + bi, c + di], [-c + di, a - bi]]`, the
  standard embedding of the quaternions in `2 × 2` complex matrices. It sends `q̄` to the
  conjugate transpose and has determinant `|q|²`. `quatEquiv : unitary ℍ ≃* SU2` restricts it to
  the unit quaternions, which it maps onto SU(2).
* `rot (p, q) x = p x q⁻¹` for unit quaternions `p`, `q`; `toSO4 : Spin4 →* SO4` is this map
  after `quatEquiv`, where `SO4` is the group of linear isometries of `ℍ` with determinant `1`.

## Main results

* `toSO4_surjective`: every rotation of `ℝ⁴` is `x ↦ p x q⁻¹`. By the Cartan–Dieudonné theorem
  (Mathlib's `LinearIsometryEquiv.reflections_generate_dim`) every isometry is a product of
  reflections; the reflection in `v^⊥` is `x ↦ -u x̄ u` with `u = v/|v|`, so a product of
  reflections is `x ↦ p x q` or `x ↦ p x̄ q`, and only the first kind has determinant `1`.
* `toSO4_eq_one_iff`: the kernel is `{(1, 1), (-1, -1)}`, of order two (`negOne_ne_one`).
* `SO4MatEquiv`: `SO4` is Mathlib's matrix group `Matrix.specialOrthogonalGroup (Fin 4) ℝ`, via
  the orthonormal basis `1, i, j, k`; `toSO4Mat : Spin4 →* SO4Mat` is the double cover in
  matrix form (surjective, kernel `{±(1,1)}`).
* SU(2) is a compact topological group (instances), `continuous_toSO4Mat`, and
  `isCoveringMap_toSO4Mat`: `toSO4Mat` is a covering map (Mathlib's `IsCoveringMap`).

## References

* J. H. Conway, D. A. Smith, *On Quaternions and Octonions*, A K Peters (2003), Ch. 4
  (the rotations of ℝ⁴ as x ↦ p x q̄).
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989), Ch. I
  (Spin(4) as the double cover of SO(4)).
-/

open Quaternion Matrix Submodule

namespace Lightlike.Spin4

open SU2

/-! ## A. Quaternions as `2 × 2` complex matrices -/

/-- The matrix of the quaternion `a + bi + cj + dk`: `[[a + bi, c + di], [-c + di, a - bi]]`. -/
def quatMat (q : ℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

/-- **The quaternions as complex `2 × 2` matrices**, an injective `ℝ`-algebra homomorphism. -/
def toMat : ℍ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := quatMat
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMat]
  map_mul' p q := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [quatMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMat]
  map_add' p q := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMat] <;> ring
  commutes' r := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [quatMat, Algebra.algebraMap_eq_smul_one]

lemma toMat_apply (q : ℍ) : toMat q = quatMat q := rfl

lemma toMat_injective : Function.Injective toMat := by
  intro p q h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp only [toMat_apply, quatMat, of_apply, cons_val', cons_val_zero, empty_val',
    cons_val_fin_one, cons_val_one, Complex.mk.injEq] at h00 h01
  exact Quaternion.ext_iff.mpr ⟨h00.1, h00.2, h01.1, h01.2⟩

/-- Quaternion conjugation is the conjugate transpose. -/
lemma toMat_star (q : ℍ) : toMat (star q) = (toMat q)ᴴ := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toMat_apply, quatMat]

/-- The determinant is the squared norm. -/
lemma det_toMat (q : ℍ) : (toMat q).det = ((normSq q : ℝ) : ℂ) := by
  rw [toMat_apply, quatMat, det_fin_two_of, normSq_def']
  apply Complex.ext <;> simp [sq] <;> ring

/-! ## B. Unit quaternions and SU(2) -/

/-- A unit quaternion has `|q|² = 1`. -/
lemma normSq_unitary (q : unitary ℍ) : normSq (q : ℍ) = 1 := by
  have h := Quaternion.star_mul_self (q : ℍ)
  rw [Unitary.star_mul_self_of_mem q.2, ← Quaternion.coe_one] at h
  exact Quaternion.coe_injective h.symm

/-- A quaternion with `|q|² = 1` is unitary. -/
lemma mem_unitary_of_normSq {q : ℍ} (h : normSq q = 1) : q ∈ unitary ℍ := by
  rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star, h, Quaternion.coe_one]
  exact ⟨rfl, rfl⟩

/-- A unit quaternion gives an element of SU(2). -/
lemma toMat_mem_SU2 (q : unitary ℍ) : toMat (q : ℍ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hn : normSq (q : ℍ) = 1 := normSq_unitary q
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose, ← toMat_star,
    ← map_mul, Unitary.mul_star_self_of_mem q.2, map_one, det_toMat, hn, Complex.ofReal_one]
  exact ⟨rfl, rfl⟩

/-- Every element of SU(2) is the matrix of a unit quaternion: `g = [[α, β], [-β̄, ᾱ]]`. -/
lemma exists_toMat_eq (g : SU2) :
    ∃ q : unitary ℍ, toMat (q : ℍ) = (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨hU, hdet⟩ := mem_specialUnitaryGroup_iff.mp g.2
  set G : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) with hG
  have hstar : star G * G = 1 := mem_unitaryGroup_iff'.mp hU
  -- `star G = G⁻¹ = adjugate G`
  have hadj : star G = adjugate G := by
    have h1 : adjugate G * G = 1 := by rw [adjugate_mul, hdet, one_smul]
    calc star G = star G * (G * adjugate G) := by rw [mul_adjugate, hdet, one_smul, mul_one]
      _ = adjugate G := by rw [← Matrix.mul_assoc, hstar, Matrix.one_mul]
  have e00 := congrFun (congrFun hadj 0) 0
  have e10 := congrFun (congrFun hadj 1) 0
  simp only [adjugate_fin_two, star_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one] at e00 e10
  let q : ℍ := ⟨(G 0 0).re, (G 0 0).im, (G 0 1).re, (G 0 1).im⟩
  have hGq : toMat q = G := by
    ext i j; fin_cases i <;> fin_cases j
    · simp [toMat_apply, quatMat, q]
    · simp [toMat_apply, quatMat, q]
    · have := congrArg Complex.re e10; have h2 := congrArg Complex.im e10
      simp at this h2
      apply Complex.ext <;> simp [toMat_apply, quatMat, q] <;> linarith
    · have := congrArg Complex.re e00; have h2 := congrArg Complex.im e00
      simp at this h2
      apply Complex.ext <;> simp [toMat_apply, quatMat, q] <;> linarith
  have hq : q ∈ unitary ℍ := by
    rw [Unitary.mem_iff]
    constructor
    · apply toMat_injective
      rw [map_mul, toMat_star, hGq, map_one, ← star_eq_conjTranspose, hstar]
    · apply toMat_injective
      rw [map_mul, toMat_star, hGq, map_one, ← star_eq_conjTranspose]
      exact mem_unitaryGroup_iff.mp hU
  exact ⟨⟨q, hq⟩, hGq⟩

/-- **SU(2) is the group of unit quaternions.** -/
noncomputable def quatEquiv : unitary ℍ ≃* SU2 :=
  let f : unitary ℍ →* SU2 :=
    { toFun := fun q => ⟨toMat (q : ℍ), toMat_mem_SU2 q⟩
      map_one' := Subtype.ext (map_one toMat)
      map_mul' := fun p q => Subtype.ext (map_mul toMat (p : ℍ) q) }
  MulEquiv.ofBijective f
    ⟨fun _ _ h => Subtype.ext (toMat_injective (congrArg Subtype.val h)),
      fun g => let ⟨q, hq⟩ := exists_toMat_eq g; ⟨q, Subtype.ext hq⟩⟩

lemma coe_quatEquiv (q : unitary ℍ) :
    (quatEquiv q : Matrix (Fin 2) (Fin 2) ℂ) = toMat (q : ℍ) := rfl

/-! ## C. Determinants -/

/-- The basis `1, i, j, k` of `ℍ` over `ℝ`. -/
noncomputable abbrev basisH : Module.Basis (Fin 4) ℝ ℍ :=
  QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1)

lemma basisH_apply (i : Fin 4) :
    basisH i = ![(1 : ℍ), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] i := by
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

/-- Left multiplication by `q` has determinant `|q|⁴`. -/
lemma det_mulLeft (q : ℍ) : LinearMap.det (LinearMap.mulLeft ℝ q) = normSq q ^ 2 := by
  have hM : LinearMap.toMatrix basisH basisH (LinearMap.mulLeft ℝ q) =
      !![q.re, -q.imI, -q.imJ, -q.imK; q.imI, q.re, -q.imK, q.imJ;
        q.imJ, q.imK, q.re, -q.imI; q.imK, -q.imJ, q.imI, q.re] := by
    ext i j
    rw [LinearMap.toMatrix_apply, basisH_apply]
    fin_cases i <;> fin_cases j <;> simp [basisH]
  rw [← LinearMap.det_toMatrix basisH, hM, det_fin_four, normSq_def']
  ring

/-- Right multiplication by `q` has determinant `|q|⁴`. -/
lemma det_mulRight (q : ℍ) : LinearMap.det (LinearMap.mulRight ℝ q) = normSq q ^ 2 := by
  have hM : LinearMap.toMatrix basisH basisH (LinearMap.mulRight ℝ q) =
      !![q.re, -q.imI, -q.imJ, -q.imK; q.imI, q.re, q.imK, -q.imJ;
        q.imJ, -q.imK, q.re, q.imI; q.imK, q.imJ, -q.imI, q.re] := by
    ext i j
    rw [LinearMap.toMatrix_apply, basisH_apply]
    fin_cases i <;> fin_cases j <;> simp [basisH]
  rw [← LinearMap.det_toMatrix basisH, hM, det_fin_four, normSq_def']
  ring

/-- Quaternion conjugation as a real-linear map. -/
def conjₗ : ℍ →ₗ[ℝ] ℍ where
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

/-- The determinant of `x ↦ p x q` is `|p|⁴ |q|⁴`. -/
lemma det_mulLR (p q : ℍ) :
    LinearMap.det ((LinearMap.mulLeft ℝ p).comp (LinearMap.mulRight ℝ q)) =
      normSq p ^ 2 * normSq q ^ 2 := by
  rw [LinearMap.det_comp, det_mulLeft, det_mulRight]

/-! ## D. Reflections of `ℍ` -/

/-- `v x̄ v = 2⟪v, x⟫ v - |v|² x`. -/
lemma mul_star_mul (v x : ℍ) :
    v * star x * v = (2 * (v * star x).re) • v - normSq v • x := by
  ext <;> simp [normSq_def'] <;> ring

/-- **The reflection of `ℍ` in the hyperplane `v^⊥` is `x ↦ -v x̄ v / |v|²`.** -/
lemma reflection_eq {v : ℍ} (hv : v ≠ 0) (x : ℍ) :
    reflection (ℝ ∙ v)ᗮ x = (-(normSq v)⁻¹) • (v * star x * v) := by
  have hN : normSq v ≠ 0 := normSq_ne_zero.mpr hv
  have hn : ‖v‖ ^ 2 = normSq v := by rw [normSq_eq_norm_mul_self, sq]
  rw [reflection_orthogonal_apply, reflection_singleton_apply, inner_def]
  simp only [RCLike.ofReal_real_eq_id, id, hn, mul_star_mul, two_smul]
  ext <;> simp <;> field_simp <;> ring

/-! ## E. The double cover `Spin(4) → SO(4)` -/

/-- **The rotation group SO(4)** of `ℝ⁴ ≅ ℍ`: linear isometries of `ℍ` with determinant `1`. -/
def SO4 : Subgroup (ℍ ≃ₗᵢ[ℝ] ℍ) where
  carrier := {f | LinearMap.det (f.toLinearEquiv : ℍ →ₗ[ℝ] ℍ) = 1}
  mul_mem' {f g} hf hg := by
    change LinearMap.det _ = 1
    have : ((f * g).toLinearEquiv : ℍ →ₗ[ℝ] ℍ) =
        (f.toLinearEquiv : ℍ →ₗ[ℝ] ℍ) ∘ₗ (g.toLinearEquiv : ℍ →ₗ[ℝ] ℍ) :=
      LinearMap.ext fun x => rfl
    rw [this, LinearMap.det_comp, hf, hg, one_mul]
  one_mem' := by
    change LinearMap.det _ = 1
    have : ((1 : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearEquiv : ℍ →ₗ[ℝ] ℍ) = LinearMap.id := LinearMap.ext fun x => rfl
    rw [this, LinearMap.det_id]
  inv_mem' {f} hf := by
    change LinearMap.det _ = 1
    have h : (f⁻¹.toLinearEquiv : ℍ →ₗ[ℝ] ℍ) ∘ₗ (f.toLinearEquiv : ℍ →ₗ[ℝ] ℍ) = LinearMap.id :=
      LinearMap.ext fun x => f.symm_apply_apply x
    have := congrArg LinearMap.det h
    rwa [LinearMap.det_comp, LinearMap.det_id, hf, mul_one] at this

lemma mem_SO4 {f : ℍ ≃ₗᵢ[ℝ] ℍ} : f ∈ SO4 ↔ LinearMap.det (f.toLinearEquiv : ℍ →ₗ[ℝ] ℍ) = 1 :=
  Iff.rfl

/-- `x ↦ p x q̄` for unit quaternions `p`, `q`: a linear isometry of `ℍ`. -/
noncomputable def rotIso (p q : unitary ℍ) : ℍ ≃ₗᵢ[ℝ] ℍ where
  toFun x := p * x * star (q : ℍ)
  invFun y := star (p : ℍ) * y * q
  map_add' x y := by rw [mul_add, add_mul]
  map_smul' r x := by simp
  left_inv x := by
    simp only [← mul_assoc, Unitary.star_mul_self_of_mem p.2, one_mul]
    rw [mul_assoc, Unitary.star_mul_self_of_mem q.2, mul_one]
  right_inv y := by
    simp only [← mul_assoc, Unitary.mul_star_self_of_mem p.2, one_mul]
    rw [mul_assoc, Unitary.mul_star_self_of_mem q.2, mul_one]
  norm_map' x := by
    change ‖(p : ℍ) * x * star (q : ℍ)‖ = ‖x‖
    rw [norm_mul, norm_mul, norm_star, CStarRing.norm_of_mem_unitary p.2,
      CStarRing.norm_of_mem_unitary q.2, one_mul, mul_one]

lemma rotIso_apply (p q : unitary ℍ) (x : ℍ) : rotIso p q x = p * x * star (q : ℍ) := rfl

lemma rotIso_mem_SO4 (p q : unitary ℍ) : rotIso p q ∈ SO4 := by
  rw [mem_SO4]
  have : ((rotIso p q).toLinearEquiv : ℍ →ₗ[ℝ] ℍ) =
      (LinearMap.mulLeft ℝ (p : ℍ)).comp (LinearMap.mulRight ℝ (star (q : ℍ))) :=
    LinearMap.ext fun x => (mul_assoc _ _ _)
  rw [this, det_mulLR, normSq_unitary, normSq_star, normSq_unitary]
  norm_num

/-- **The double-cover homomorphism** `Spin(4) → SO(4)`, `(g₊, g₋) ↦ (x ↦ p x q⁻¹)` where `p`, `q`
are the unit quaternions of `g₊`, `g₋`. -/
noncomputable def toSO4 : Spin4 →* SO4 where
  toFun g := ⟨rotIso (quatEquiv.symm g.1) (quatEquiv.symm g.2), rotIso_mem_SO4 _ _⟩
  map_one' := by
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    intro x
    simp [rotIso_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    intro x
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Subgroup.coe_mul, LinearIsometryEquiv.coe_mul,
      Function.comp_apply, rotIso_apply, Submonoid.coe_mul, star_mul, mul_assoc]

lemma toSO4_apply (g : Spin4) (x : ℍ) :
    (toSO4 g : ℍ ≃ₗᵢ[ℝ] ℍ) x = (quatEquiv.symm g.1 : ℍ) * x * star (quatEquiv.symm g.2 : ℍ) :=
  rfl

/-- A product of reflections of `ℍ` is `x ↦ P x Q` or `x ↦ P x̄ Q`. -/
lemma prod_reflections (l : List ℍ) :
    (∃ P Q : ℍ, ∀ x, (l.map fun v => reflection (ℝ ∙ v)ᗮ).prod x = P * x * Q) ∨
      (∃ P Q : ℍ, ∀ x, (l.map fun v => reflection (ℝ ∙ v)ᗮ).prod x = P * star x * Q) := by
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

/-- **Every rotation of `ℝ⁴ ≅ ℍ` is `x ↦ p x q⁻¹`** for unit quaternions `p`, `q`: the double
cover `Spin(4) → SO(4)` is surjective. -/
theorem toSO4_surjective : Function.Surjective toSO4 := by
  rintro ⟨f, hf⟩
  obtain ⟨l, -, hl⟩ := f.reflections_generate_dim
  -- `f 1 = P Q` has norm one
  have hnorm : ∀ P Q : ℍ, f 1 = P * Q → normSq P * normSq Q = 1 := by
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
    let p : unitary ℍ := ⟨s⁻¹ • P, mem_unitary_of_normSq hpu⟩
    let q : unitary ℍ := ⟨star (s • Q), mem_unitary_of_normSq hqu'⟩
    refine ⟨(quatEquiv p, quatEquiv q), Subtype.ext (LinearIsometryEquiv.ext fun x => ?_)⟩
    rw [toSO4_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, h]
    simp only [p, q, star_star, smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hP,
      one_smul]
  · exfalso
    rw [← hl] at h
    have hPQ := hnorm P Q (by rw [h, star_one, mul_one])
    have hlin : (f.toLinearEquiv : ℍ →ₗ[ℝ] ℍ) =
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

/-- The unit quaternion of `-1 ∈ SU(2)` is `-1`. -/
lemma quatEquiv_symm_negOne : (quatEquiv.symm negOne : ℍ) = -1 := by
  have hm : (-1 : ℍ) ∈ unitary ℍ := mem_unitary_of_normSq (by simp)
  have : quatEquiv ⟨-1, hm⟩ = negOne := by
    apply Subtype.ext
    rw [coe_quatEquiv, negOne_coe, map_neg, map_one]
  rw [← this, MulEquiv.symm_apply_apply]

/-- A quaternion commuting with `i` and `j` is real. -/
lemma eq_coe_of_commute {p : ℍ} (hi : p * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * p)
    (hj : p * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * p) : p = (p.re : ℍ) := by
  have h1 := congrArg (fun x : ℍ => x.imJ) hi
  have h2 := congrArg (fun x : ℍ => x.imK) hi
  have h3 := congrArg (fun x : ℍ => x.imK) hj
  simp at h1 h2 h3
  ext <;> simp <;> linarith

/-- **The kernel of `Spin(4) → SO(4)` is `{(1, 1), (-1, -1)}`.** -/
theorem toSO4_eq_one_iff (g : Spin4) : toSO4 g = 1 ↔ g = 1 ∨ g = (negOne, negOne) := by
  constructor
  · intro hg
    have hx : ∀ x : ℍ, (quatEquiv.symm g.1 : ℍ) * x * star (quatEquiv.symm g.2 : ℍ) = x :=
      fun x => by
        rw [← toSO4_apply, hg]; rfl
    set p : unitary ℍ := quatEquiv.symm g.1 with hp
    set q : unitary ℍ := quatEquiv.symm g.2 with hq
    -- `p = q`
    have hpq : (p : ℍ) = q := by
      have h1 := hx 1
      rw [mul_one] at h1
      calc (p : ℍ) = p * (star (q : ℍ) * q) := by rw [Unitary.star_mul_self_of_mem q.2, mul_one]
        _ = q := by rw [← mul_assoc, h1, one_mul]
    -- `p` commutes with everything, so `p = ±1`
    have hcomm : ∀ x : ℍ, (p : ℍ) * x = x * p := fun x => by
      have := congrArg (· * (p : ℍ)) (hx x)
      simp only [← hpq, mul_assoc, Unitary.star_mul_self_of_mem p.2, mul_one] at this
      exact this
    have hre := eq_coe_of_commute (hcomm _) (hcomm _)
    have hn : (p : ℍ).re ^ 2 = 1 := by
      have := normSq_unitary p
      rw [hre, normSq_coe] at this
      exact this
    have hg1 : g.1 = quatEquiv p := by rw [hp, MulEquiv.apply_symm_apply]
    have hg2 : g.2 = g.1 := by
      rw [hg1, show g.2 = quatEquiv q by rw [hq, MulEquiv.apply_symm_apply]]
      exact congrArg quatEquiv (Subtype.ext hpq.symm)
    rw [sq, mul_self_eq_one_iff] at hn
    rcases hn with h | h
    · left
      have hp1 : p = 1 := Subtype.ext (by rw [hre, h, Quaternion.coe_one]; rfl)
      have : g.1 = 1 := by rw [hg1, hp1, map_one]
      exact Prod.ext this (hg2.trans this)
    · right
      have : g.1 = negOne := by
        apply Subtype.ext
        rw [hg1, coe_quatEquiv, hre, h, negOne_coe, Quaternion.coe_neg, Quaternion.coe_one, map_neg,
          map_one]
      exact Prod.ext this (hg2.trans this)
  · rintro (rfl | rfl)
    · exact map_one _
    · apply Subtype.ext
      apply LinearIsometryEquiv.ext
      intro x
      rw [toSO4_apply, quatEquiv_symm_negOne, star_neg, star_one]
      simp

/-- The kernel has two elements: `(-1, -1) ≠ (1, 1)`. -/
lemma negOne_ne_one : ((negOne, negOne) : Spin4) ≠ 1 := by
  intro h
  have := congrArg (fun g : Spin4 => (g.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  simp [negOne_coe] at this
  norm_num at this

/-- The unit quaternion of `g ∈ SU(2)`: `g = [[a + bi, c + di], …] ↦ a + bi + cj + dk`. -/
lemma quatEquiv_symm_coe (g : SU2) :
    (quatEquiv.symm g : ℍ) = ⟨((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re,
      ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im, ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re,
      ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im⟩ := by
  obtain ⟨q, hq⟩ := exists_toMat_eq g
  have h1 : quatEquiv.symm g = q := by
    rw [MulEquiv.symm_apply_eq]; exact Subtype.ext hq.symm
  rw [h1, ← hq]
  ext <;> simp [toMat_apply, quatMat]

/-! ## F. Topology: Spin(4) is a compact topological group -/

/-- SU(2) is a topological group (inversion is the conjugate transpose). -/
instance : IsTopologicalGroup SU2 where
  continuous_mul := continuous_mul
  continuous_inv := continuous_induced_rng.2 (by
    change Continuous fun g : SU2 => star (g : Matrix (Fin 2) (Fin 2) ℂ)
    exact continuous_star.comp continuous_subtype_val)

/-- SU(2) is compact: it is closed, and its entries have modulus at most `1`. -/
instance : CompactSpace SU2 := by
  suffices hc : IsCompact (specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) from
    isCompact_iff_compactSpace.mp hc
  have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset ?_ ?_
  · have : (specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
        {A | star A * A = 1} ∩ {A | A * star A = 1} ∩ {A | A.det = 1} := by
      ext A
      simp only [SetLike.mem_coe, mem_specialUnitaryGroup_iff, Unitary.mem_iff,
        Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
    rw [this]
    refine ((isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_const)).inter
      (isClosed_eq ?_ continuous_const)
    · exact continuous_star.matrix_mul continuous_id
    · exact continuous_id.matrix_mul continuous_star
    · exact continuous_id.matrix_det
  · intro A hA
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact entry_norm_bound_of_unitary (mem_specialUnitaryGroup_iff.mp hA).1 i j

/-! ## G. SO(4) as Mathlib's matrix group -/

/-- **SO(4) as matrices**: Mathlib's group of real orthogonal `4 × 4` matrices of determinant
`1`. -/
abbrev SO4Mat := Matrix.specialOrthogonalGroup (Fin 4) ℝ

lemma basisH_equivFun (x : ℍ) : basisH.equivFun x = ![x.re, x.imI, x.imJ, x.imK] := by
  rw [Module.Basis.equivFun_apply]
  exact QuaternionAlgebra.coe_basisOneIJK_repr _ _ _ x

/-- In the orthonormal basis `1, i, j, k`, the inner product of `ℍ` is the dot product. -/
lemma inner_eq_dotProduct (x y : ℍ) :
    inner ℝ x y = basisH.equivFun x ⬝ᵥ basisH.equivFun y := by
  rw [inner_def, basisH_equivFun, basisH_equivFun]
  simp [dotProduct, Fin.sum_univ_four]

lemma equivFun_apply_eq_mulVec (f : ℍ →ₗ[ℝ] ℍ) (x : ℍ) :
    basisH.equivFun (f x) = LinearMap.toMatrix basisH basisH f *ᵥ basisH.equivFun x := by
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
  exact (LinearMap.toMatrix_mulVec_repr basisH basisH f x).symm

lemma dotProduct_mulVec_mulVec (M : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 4 → ℝ) :
    (M *ᵥ a) ⬝ᵥ (M *ᵥ b) = a ⬝ᵥ ((Mᵀ * M) *ᵥ b) := by
  conv_rhs => rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- The matrix of a linear isometry of `ℍ` in the basis `1, i, j, k` is orthogonal. -/
lemma transpose_mul_toMatrix (f : ℍ ≃ₗᵢ[ℝ] ℍ) :
    (LinearMap.toMatrix basisH basisH f.toLinearEquiv.toLinearMap)ᵀ *
      LinearMap.toMatrix basisH basisH f.toLinearEquiv.toLinearMap = 1 := by
  set M := LinearMap.toMatrix basisH basisH f.toLinearEquiv.toLinearMap
  have hcol : ∀ i, basisH.equivFun (f (basisH i)) = fun k => M k i := fun i => by
    funext k
    exact (LinearMap.toMatrix_apply basisH basisH f.toLinearEquiv.toLinearMap k i).symm
  refine Matrix.ext fun i j => ?_
  have h1 : (Mᵀ * M) i j = basisH.equivFun (f (basisH i)) ⬝ᵥ basisH.equivFun (f (basisH j)) := by
    rw [hcol, hcol]; simp [Matrix.mul_apply, dotProduct]
  rw [h1, ← inner_eq_dotProduct, f.inner_map_map, inner_eq_dotProduct]
  fin_cases i <;> fin_cases j <;>
    simp [basisH_apply, dotProduct, Fin.sum_univ_four]

/-- **Isometries of `ℍ` of determinant one are the matrix group SO(4).** -/
noncomputable def SO4MatEquiv : SO4 ≃* SO4Mat :=
  let φ : SO4 →* SO4Mat :=
    { toFun := fun f => ⟨LinearMap.toMatrix basisH basisH
          (f : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearEquiv.toLinearMap, by
        rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff', star_eq_conjTranspose,
          conjTranspose_eq_transpose_of_trivial, LinearMap.det_toMatrix]
        exact ⟨transpose_mul_toMatrix f, f.2⟩⟩
      map_one' := Subtype.ext (by
        change LinearMap.toMatrix basisH basisH LinearMap.id = 1
        exact LinearMap.toMatrix_id basisH)
      map_mul' := fun f g => Subtype.ext (by
        change LinearMap.toMatrix basisH basisH ((f : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearEquiv.toLinearMap ∘ₗ
          (g : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearEquiv.toLinearMap) = _
        rw [LinearMap.toMatrix_comp basisH basisH basisH]; rfl) }
  MulEquiv.ofBijective φ
    ⟨fun f g h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (LinearIsometryEquiv.ext fun x =>
        LinearMap.congr_fun ((LinearMap.toMatrix basisH basisH).injective h') x),
    fun M => by
      obtain ⟨hU, hdet⟩ := mem_specialUnitaryGroup_iff.mp M.2
      have hMT : (M : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * M = 1 := by
        rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
        exact mem_unitaryGroup_iff'.mp hU
      have hTM : (M : Matrix (Fin 4) (Fin 4) ℝ) * (M : Matrix (Fin 4) (Fin 4) ℝ)ᵀ = 1 := by
        rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
        exact mem_unitaryGroup_iff.mp hU
      let L := Matrix.toLin basisH basisH (M : Matrix (Fin 4) (Fin 4) ℝ)
      let L' := Matrix.toLin basisH basisH (M : Matrix (Fin 4) (Fin 4) ℝ)ᵀ
      let e : ℍ ≃ₗ[ℝ] ℍ := LinearEquiv.ofLinearMap L L'
        (by rw [← Matrix.toLin_mul, hTM, Matrix.toLin_one])
        (by rw [← Matrix.toLin_mul, hMT, Matrix.toLin_one])
      let f : ℍ ≃ₗᵢ[ℝ] ℍ := e.isometryOfInner fun x y => by
        change inner ℝ (L x) (L y) = inner ℝ x y
        rw [inner_eq_dotProduct, inner_eq_dotProduct, equivFun_apply_eq_mulVec,
          equivFun_apply_eq_mulVec, LinearMap.toMatrix_toLin, dotProduct_mulVec_mulVec, hMT,
          one_mulVec]
      have hfM : LinearMap.toMatrix basisH basisH f.toLinearEquiv.toLinearMap = M := by
        change LinearMap.toMatrix basisH basisH L = M
        rw [LinearMap.toMatrix_toLin]
      refine ⟨⟨f, ?_⟩, Subtype.ext hfM⟩
      rw [mem_SO4, ← LinearMap.det_toMatrix basisH]
      change (LinearMap.toMatrix basisH basisH f.toLinearEquiv.toLinearMap).det = 1
      rw [hfM, hdet]⟩

lemma SO4MatEquiv_apply (f : SO4) :
    (SO4MatEquiv f : Matrix (Fin 4) (Fin 4) ℝ) =
      LinearMap.toMatrix basisH basisH (f : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearEquiv.toLinearMap := rfl

/-- **The double cover onto the matrix group SO(4).** -/
noncomputable def toSO4Mat : Spin4 →* SO4Mat := SO4MatEquiv.toMonoidHom.comp toSO4

/-- `toSO4Mat` is surjective. -/
theorem toSO4Mat_surjective : Function.Surjective toSO4Mat :=
  SO4MatEquiv.surjective.comp toSO4_surjective

/-- The kernel of `toSO4Mat` is `{(1, 1), (-1, -1)}`. -/
theorem toSO4Mat_eq_one_iff (g : Spin4) : toSO4Mat g = 1 ↔ g = 1 ∨ g = (negOne, negOne) := by
  rw [← toSO4_eq_one_iff]
  change SO4MatEquiv (toSO4 g) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]

/-! ## H. The covering map -/

/-- The unit quaternion of `u x ∈ SU(2)` depends continuously on `x`. -/
lemma continuous_quatEquiv_symm {X : Type*} [TopologicalSpace X] {u : X → SU2}
    (hu : Continuous u) : Continuous fun x => (quatEquiv.symm (u x) : ℍ) := by
  have he : ∀ i j, Continuous fun x => ((u x : Matrix (Fin 2) (Fin 2) ℂ) i j) := fun i j =>
    (continuous_subtype_val.comp hu).matrix_elem i j
  have hform : (fun x => (quatEquiv.symm (u x) : ℍ)) = fun x =>
      ((u x : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re • (1 : ℍ) +
      ((u x : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im • (⟨0, 1, 0, 0⟩ : ℍ) +
      ((u x : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re • (⟨0, 0, 1, 0⟩ : ℍ) +
      ((u x : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im • (⟨0, 0, 0, 1⟩ : ℍ) := by
    funext x
    rw [quatEquiv_symm_coe]
    ext <;> simp
  rw [hform]
  have h1 := Complex.continuous_re.comp (he 0 0)
  have h2 := Complex.continuous_im.comp (he 0 0)
  have h3 := Complex.continuous_re.comp (he 0 1)
  have h4 := Complex.continuous_im.comp (he 0 1)
  exact (((h1.smul continuous_const).add (h2.smul continuous_const)).add
    (h3.smul continuous_const)).add (h4.smul continuous_const)

/-- **`toSO4Mat` is continuous.** -/
theorem continuous_toSO4Mat : Continuous toSO4Mat := by
  have hp := continuous_quatEquiv_symm (u := fun g : Spin4 => g.1) continuous_fst
  have hq := continuous_quatEquiv_symm (u := fun g : Spin4 => g.2) continuous_snd
  have hrot : ∀ x : ℍ, Continuous fun g : Spin4 => (toSO4 g : ℍ ≃ₗᵢ[ℝ] ℍ) x := fun x => by
    simp only [toSO4_apply]
    exact (hp.mul continuous_const).mul (continuous_star.comp hq)
  have hc : Continuous (basisH.equivFun : ℍ → (Fin 4 → ℝ)) :=
    LinearMap.continuous_of_finiteDimensional basisH.equivFun.toLinearMap
  refine continuous_induced_rng.2 (continuous_matrix fun i j => ?_)
  change Continuous fun g : Spin4 => ((toSO4Mat g : SO4Mat) : Matrix (Fin 4) (Fin 4) ℝ) i j
  have : (fun g : Spin4 => ((toSO4Mat g : SO4Mat) : Matrix (Fin 4) (Fin 4) ℝ) i j) =
      fun g => basisH.equivFun ((toSO4 g : ℍ ≃ₗᵢ[ℝ] ℍ) (basisH j)) i := by
    funext g
    exact LinearMap.toMatrix_apply basisH basisH _ i j
  rw [this]
  exact (continuous_apply i).comp (hc.comp (hrot _))

/-- **Spin(4) → SO(4) is a covering map** (a continuous surjective homomorphism from a compact
group with finite kernel, hence a quotient map with discrete kernel). -/
theorem isCoveringMap_toSO4Mat : IsCoveringMap toSO4Mat := by
  have hq : Topology.IsQuotientMap toSO4Mat :=
    Topology.IsQuotientMap.of_surjective_continuous toSO4Mat_surjective continuous_toSO4Mat
  have hker : (toSO4Mat.ker : Set Spin4) = {1, (negOne, negOne)} := by
    ext g
    simp [MonoidHom.mem_ker, toSO4Mat_eq_one_iff]
  have disc : IsDiscrete (toSO4Mat.ker : Set Spin4) := by
    rw [hker]
    exact (Set.toFinite _).isDiscrete
  exact (hq.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom disc).isCoveringMap

end Lightlike.Spin4
