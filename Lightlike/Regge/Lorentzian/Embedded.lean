import Lightlike.Regge.Lorentzian.Complex
import Lightlike.Regge.D4.Embedded
import Lightlike.Spacetime.Minkowski

/-!
# Flat Lorentzian triangulations have zero deficit angles

The Lorentzian counterpart of `Lightlike/Regge/D4/Embedded.lean`, and the RC1 trust check "a flat Lorentzian
triangulation has zero deficits". The vertices of a 4-dimensional simplicial complex are placed in
a real vector space `E` with inertial coordinates `φ : E ≃ₗ[ℝ] (Fin 4 → ℝ)`, and the edges get the
signed squared lengths of Minkowski space, `L {u, v} = η(x v − x u, x v − x u)` with
`η = diag(−1, 1, 1, 1)` (`lorLen`). Around an interior triangle whose 4-simplices fit together
without overlap, the dihedral angles of `Lightlike/Regge/Lorentzian/Complex.lean` add up to the flat value `2π Z_t`:
`−2πi` at a spacelike triangle (Sorkin 1975, Phys. Rev. D 12, 385; Asante, Dittrich and
Padua-Argüelles, arXiv:2104.00485, Section III) and `2π` at a timelike one.

The proof follows the Euclidean one. The plane normal to the triangle is a Minkowski plane at a
spacelike and a Euclidean plane at a timelike triangle (`exists_lorFrame`, `exists_eucFrame`, from
the signature of `η`: `det_gram_neg`, `det_gram_block`). In polar coordinates in that plane the
dihedral angles become Sorkin's angles `Lightlike.ReggeLor.sorkinAngle` of the wedges between consecutive
normal directions, or Euclidean angles, and disjoint 4-simplices give disjoint wedges
(`wedges_disjoint`). The full-turn theorems `Lightlike.ReggeLor.sum_sorkinAngle_eq` and
`Lightlike.Regge.sum_arccos_cos_eq_two_pi` finish the proof. The inner product on `E` is used only to
state that the 4-simplices do not overlap; the metric is `minkG φ`.

## Main definitions

* `minkG φ`: the Minkowski form `η(φ y, φ z)` on `E`.
* `lorLen φ x`: the signed squared edge lengths of a placement `x`.
* `IsNonNull4 K L`: no triangle and no tetrahedron is null.

## Main results

* `lorDeficit_eq_zero_of_spacelike`, `lorDeficit_eq_zero_of_timelike`,
  `lorDeficit_eq_zero_of_embedded`: a non-null triangle whose link is a cycle of non-degenerate,
  non-overlapping 4-simplices has zero Lorentzian deficit; at a spacelike triangle its
  tetrahedra must be non-null.
* `IsGeometric4.lorDeficit_eq_zero`: every interior triangle of a non-null geometric triangulation
  of a region of Minkowski space has zero deficit, and `IsGeometric4.lorReggeAction_eq`: its
  Lorentzian Regge action is a pure boundary term.
-/

open Real Finset Module Matrix

namespace Lightlike.ReggeLor

open Lightlike.FourD (Complex4)
open Lightlike.Regge (InWedge sum_arccos_cos_eq_two_pi ofDist ofDist_pair)
open Lightlike.Regge4 (open4 mem_open4_near polar_nondeg IsCycleLink4 IsGeometric4 IsTriManifold intTris4
  bdryTris4 linIndep_of_affIndep5 openHull_eq_interior4 openHull_eq_open4 card_four)
open Lightlike.FourD.Complex4 (mem_faces)

/-! ## The Minkowski form on a 4-dimensional space -/

section Signature

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (φ : E ≃ₗ[ℝ] (Fin 4 → ℝ))

/-- The Minkowski form `η = diag(−1, 1, 1, 1)` pulled back to `E` along the linear isomorphism
`φ : E ≃ ℝ⁴`: `minkG φ y z = η(φ y, φ z)`. -/
noncomputable def minkG : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun y z => minkowskiForm 4 (φ y) (φ z))
    (fun y y' z => by simp)
    (fun c y z => by simp)
    (fun y z z' => by simp only [map_add])
    (fun c y z => by simp only [map_smul, smul_eq_mul])

/-- `minkG` in coordinates. -/
theorem minkG_apply (y z : E) :
    minkG φ y z = -(φ y 0 * φ z 0) + φ y 1 * φ z 1 + φ y 2 * φ z 2 + φ y 3 * φ z 3 := by
  simp [minkG, Fin.sum_univ_four, etaDiag]

/-- `minkG` is symmetric. -/
theorem minkG_comm (y z : E) : minkG φ y z = minkG φ z y := by
  rw [minkG_apply, minkG_apply]
  ring

/-- **The Gram determinant of a basis is negative**: for linearly independent `y₀, …, y₃`,
`det (minkG φ (yᵢ) (yⱼ)) = −(det Φ)² < 0`, where `Φ` is the matrix of the coordinates of the `yᵢ`.
This is the signature `(−,+,+,+)` in a form usable for any basis. -/
theorem det_gram_neg {y : Fin 4 → E} (h : LinearIndependent ℝ y) :
    (Matrix.of fun i j => minkG φ (y i) (y j)).det < 0 := by
  set Φ : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i k => φ (y i) k with hΦ
  have hG : (Matrix.of fun i j => minkG φ (y i) (y j)) =
      Φ * Matrix.diagonal ![-1, 1, 1, 1] * Φᵀ := by
    ext i j
    simp [Φ, Matrix.mul_apply, Fin.sum_univ_four, minkG_apply]
  have hdet : Φ.det ≠ 0 := by
    have h' : LinearIndependent ℝ Φ.row := h.map' φ.toLinearMap φ.ker
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_row_iff_isUnit.mp h')).ne_zero
  rw [hG, det_mul, det_mul, det_transpose, det_diagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  nlinarith [sq_pos_of_ne_zero hdet]

/-- **No two `minkG`-orthogonal timelike vectors.** -/
theorem minkG_ne_zero_of_timelike {T U : E} (hT : minkG φ T T < 0) (hU : minkG φ U U < 0) :
    minkG φ T U ≠ 0 := by
  intro h
  rw [minkG_apply] at hT hU h
  set t := φ T
  set u := φ U
  have hSt : 0 ≤ t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 := by positivity
  have hSu : 0 ≤ u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by positivity
  have hu0 : 0 < u 0 ^ 2 := by nlinarith
  have hcs : (t 1 * u 1 + t 2 * u 2 + t 3 * u 3) ^ 2 ≤
      (t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2) * (u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) := by
    nlinarith [sq_nonneg (t 1 * u 2 - t 2 * u 1), sq_nonneg (t 1 * u 3 - t 3 * u 1),
      sq_nonneg (t 2 * u 3 - t 3 * u 2)]
  have h1 : (t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2) * (u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) ≤
      (t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2) * u 0 ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hSt
  have h2 : (t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2) * u 0 ^ 2 < t 0 ^ 2 * u 0 ^ 2 :=
    mul_lt_mul_of_pos_right (by nlinarith) hu0
  have h3 : (t 1 * u 1 + t 2 * u 2 + t 3 * u 3) ^ 2 = t 0 ^ 2 * u 0 ^ 2 := by
    rw [show t 1 * u 1 + t 2 * u 2 + t 3 * u 3 = t 0 * u 0 by linarith]
    ring
  linarith

include φ in
/-- `E` has dimension 4. -/
theorem finrank_of_equiv : finrank ℝ E = 4 := by
  rw [LinearEquiv.finrank_eq φ, Module.finrank_fin_fun]

end Signature

/-! ## Frames of the plane orthogonal to a triangle -/

section Frames

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The Gram determinant of `A, B, C, D` with `C, D` orthogonal to `A, B` is the product of the
two `2 × 2` Gram determinants. -/
theorem det_gram_block (g : LinearMap.BilinForm ℝ E) (hg : ∀ y z, g y z = g z y) {A B C D : E}
    (hCA : g C A = 0) (hCB : g C B = 0) (hDA : g D A = 0) (hDB : g D B = 0) :
    (Matrix.of fun i j => g (![A, B, C, D] i) (![A, B, C, D] j)).det =
      (g A A * g B B - g A B ^ 2) * (g C C * g D D - g C D ^ 2) := by
  have hAC : g A C = 0 := by rw [hg, hCA]
  have hBC : g B C = 0 := by rw [hg, hCB]
  have hAD : g A D = 0 := by rw [hg, hDA]
  have hBD : g B D = 0 := by rw [hg, hDB]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, hCA, hCB, hDA, hDB, hAC,
    hBC, hAD, hBD, hg B A, hg D C]
  ring

variable {g : LinearMap.BilinForm ℝ E}

/-- If `A, B, C, D` span the space, `C, D` are orthogonal to `A, B` and the Gram determinant of
`A, B` is non-zero, every vector orthogonal to `A, B` is a combination of `C` and `D`. -/
theorem exists_orth_coeffs (hg : ∀ y z, g y z = g z y) {A B C D : E}
    (hspan : Submodule.span ℝ (Set.range ![A, B, C, D]) = ⊤)
    (hCA : g C A = 0) (hCB : g C B = 0) (hDA : g D A = 0) (hDB : g D B = 0)
    (hG : g A A * g B B - g A B ^ 2 ≠ 0) {y : E} (hyA : g y A = 0) (hyB : g y B = 0) :
    ∃ γ δ : ℝ, y = γ • C + δ • D := by
  have hy : y ∈ Submodule.span ℝ (Set.range ![A, B, C, D]) := hspan ▸ Submodule.mem_top
  obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hk
  have e1 : k 0 * g A A + k 1 * g A B = 0 := by
    rw [← hk] at hyA
    simpa [hCA, hDA, hg B A] using hyA
  have e2 : k 0 * g A B + k 1 * g B B = 0 := by
    rw [← hk] at hyB
    simpa [hCB, hDB] using hyB
  have h0 : k 0 = 0 := by
    have : k 0 * (g A A * g B B - g A B ^ 2) = 0 := by
      linear_combination g B B * e1 - g A B * e2
    exact (mul_eq_zero.mp this).resolve_right hG
  have h1 : k 1 = 0 := by
    have : k 1 * (g A A * g B B - g A B ^ 2) = 0 := by
      linear_combination g A A * e2 - g A B * e1
    exact (mul_eq_zero.mp this).resolve_right hG
  exact ⟨k 2, k 3, by rw [← hk, h0, h1]; simp⟩

/-- Rescaling by `(√c)⁻¹` divides the square by `c`. -/
theorem g_inv_sqrt (v : E) {c : ℝ} (hc : 0 < c) :
    g ((√c)⁻¹ • v) ((√c)⁻¹ • v) = g v v / c := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hc.le]
  ring

omit [AddCommGroup E] [Module ℝ E] in
/-- A vector is `√c` times its rescaling by `(√c)⁻¹`. -/
theorem smul_inv_sqrt {E : Type*} [AddCommGroup E] [Module ℝ E] (v : E) {c : ℝ} (hc : 0 < c) :
    v = √c • (√c)⁻¹ • v := by
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hc).ne', one_smul]

/-- In a `g`-orthonormal pair `e, f` with `g e e = 1`, `g f f = s`, the coefficients of
`y = p e + q f` are `g y e` and `s · g y f`. -/
theorem frame_coeffs (hg : ∀ y z, g y z = g z y) {e f : E} {s : ℝ} (he : g e e = 1)
    (hf : g f f = s) (hef : g e f = 0) (hs : s * s = 1) (p q : ℝ) :
    p • e + q • f = g (p • e + q • f) e • e + (s * g (p • e + q • f) f) • f := by
  have hfe : g f e = 0 := by rw [hg, hef]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, he, hf,
    hef, hfe, mul_zero, add_zero, zero_add, mul_one]
  rw [show s * (q * s) = q * (s * s) by ring, hs, mul_one]

/-- The orthogonal `g`-square of `D` relative to `C`: `F = D − (g C D / g C C) C` is orthogonal to
`C` and `g C C · g F F` is the Gram determinant of `C, D`. -/
theorem orth_step (hg : ∀ y z, g y z = g z y) {C D : E} (hC : g C C ≠ 0) :
    g C (D - (g C D / g C C) • C) = 0 ∧
      g C C * g (D - (g C D / g C C) • C) (D - (g C D / g C C) • C) =
        g C C * g D D - g C D ^ 2 := by
  have hDC : g D C = g C D := hg D C
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hDC]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **A `g`-orthonormal Lorentzian frame of a plane.** If `C, F` are orthogonal with
`g C C · g F F < 0`, there are `e_x, e_t` with `g e_x e_x = 1`, `g e_t e_t = −1`, `g e_x e_t = 0`,
in which every combination of `C, F` expands as `y = g(y, e_x) e_x − g(y, e_t) e_t`. -/
theorem exists_lorFrame_of_orth (hg : ∀ y z, g y z = g z y) {C F : E} (hCF : g C F = 0)
    (hneg : g C C * g F F < 0) :
    ∃ ex et : E, g ex ex = 1 ∧ g et et = -1 ∧ g ex et = 0 ∧
      ∀ γ δ : ℝ, γ • C + δ • F = g (γ • C + δ • F) ex • ex - g (γ • C + δ • F) et • et := by
  have key : ∀ {ex et : E}, g ex ex = 1 → g et et = -1 → g ex et = 0 → ∀ p q : ℝ,
      p • ex + q • et = g (p • ex + q • et) ex • ex - g (p • ex + q • et) et • et := by
    intro ex et h1 h2 h3 p q
    have h4 : g et ex = 0 := by rw [hg, h3]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2,
      h3, h4, mul_zero, add_zero, zero_add, mul_one, mul_neg, neg_smul, sub_neg_eq_add]
  rcases lt_or_gt_of_ne (show g C C ≠ 0 by
      rintro h; rw [h, zero_mul] at hneg; exact lt_irrefl _ hneg)
    with hC | hC
  · have hF : 0 < g F F := by nlinarith
    have hC' : 0 < -g C C := by linarith
    refine ⟨(√(g F F))⁻¹ • F, (√(-g C C))⁻¹ • C, ?_, ?_, ?_, fun γ δ => ?_⟩
    · rw [g_inv_sqrt F hF, div_self hF.ne']
    · rw [g_inv_sqrt C hC', div_neg, div_self hC.ne]
    · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hg F C, hCF, mul_zero]
    · have h1 : γ • C + δ • F = (δ * √(g F F)) • ((√(g F F))⁻¹ • F) +
          (γ * √(-g C C)) • ((√(-g C C))⁻¹ • C) := by
        rw [mul_smul, mul_smul, ← smul_inv_sqrt F hF, ← smul_inv_sqrt C hC']
        abel
      rw [h1]
      exact key (by rw [g_inv_sqrt F hF, div_self hF.ne']) (by rw [g_inv_sqrt C hC', div_neg,
        div_self hC.ne]) (by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hg F C, hCF,
        mul_zero]) _ _
  · have hF : 0 < -g F F := by nlinarith
    refine ⟨(√(g C C))⁻¹ • C, (√(-g F F))⁻¹ • F, ?_, ?_, ?_, fun γ δ => ?_⟩
    · rw [g_inv_sqrt C hC, div_self hC.ne']
    · rw [g_inv_sqrt F hF, div_neg, div_self (by linarith : g F F ≠ 0)]
    · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hCF, mul_zero]
    · have h1 : γ • C + δ • F = (γ * √(g C C)) • ((√(g C C))⁻¹ • C) +
          (δ * √(-g F F)) • ((√(-g F F))⁻¹ • F) := by
        rw [mul_smul, mul_smul, ← smul_inv_sqrt C hC, ← smul_inv_sqrt F hF]
      rw [h1]
      exact key (by rw [g_inv_sqrt C hC, div_self hC.ne']) (by rw [g_inv_sqrt F hF, div_neg,
        div_self (by linarith : g F F ≠ 0)]) (by simp only [map_smul, LinearMap.smul_apply,
        smul_eq_mul, hCF, mul_zero]) _ _

/-- **A `g`-orthonormal Euclidean frame of a plane.** If `C, F` are orthogonal with `g C C > 0` and
`g F F > 0`, there are orthonormal `e₂, e₃` in which every combination of `C, F` expands as
`y = g(y, e₂) e₂ + g(y, e₃) e₃`. -/
theorem exists_eucFrame_of_orth (hg : ∀ y z, g y z = g z y) {C F : E} (hCF : g C F = 0)
    (hC : 0 < g C C) (hF : 0 < g F F) :
    ∃ e₂ e₃ : E, g e₂ e₂ = 1 ∧ g e₃ e₃ = 1 ∧ g e₂ e₃ = 0 ∧
      ∀ γ δ : ℝ, γ • C + δ • F = g (γ • C + δ • F) e₂ • e₂ + g (γ • C + δ • F) e₃ • e₃ := by
  have h1 : g ((√(g C C))⁻¹ • C) ((√(g C C))⁻¹ • C) = 1 := by
    rw [g_inv_sqrt C hC, div_self hC.ne']
  have h2 : g ((√(g F F))⁻¹ • F) ((√(g F F))⁻¹ • F) = 1 := by
    rw [g_inv_sqrt F hF, div_self hF.ne']
  have h3 : g ((√(g C C))⁻¹ • C) ((√(g F F))⁻¹ • F) = 0 := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hCF, mul_zero]
  refine ⟨_, _, h1, h2, h3, fun γ δ => ?_⟩
  have e : γ • C + δ • F = (γ * √(g C C)) • ((√(g C C))⁻¹ • C) +
      (δ * √(g F F)) • ((√(g F F))⁻¹ • F) := by
    rw [mul_smul, mul_smul, ← smul_inv_sqrt C hC, ← smul_inv_sqrt F hF]
  rw [e]
  have := frame_coeffs hg h1 h2 h3 (by norm_num) (γ * √(g C C)) (δ * √(g F F))
  rw [one_mul] at this
  exact this

end Frames

/-! ## Frames of the normal plane of a triangle in Minkowski space -/

section NormalFrames

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (φ : E ≃ₗ[ℝ] (Fin 4 → ℝ))

/-- **The normal plane of a spacelike triangle is a Minkowski plane.** Let `A, B, C, D` be a basis
with `C, D` `minkG`-orthogonal to `A, B`, the triangle spanned by `A, B` spacelike (positive Gram
determinant) and `C` non-null. Then the vectors orthogonal to `A, B` have a Lorentzian frame. -/
theorem exists_lorFrame {A B C D : E} (hli : LinearIndependent ℝ ![A, B, C, D])
    (hCA : minkG φ C A = 0) (hCB : minkG φ C B = 0) (hDA : minkG φ D A = 0)
    (hDB : minkG φ D B = 0)
    (hG : 0 < minkG φ A A * minkG φ B B - minkG φ A B ^ 2) (hCC : minkG φ C C ≠ 0) :
    ∃ ex et : E, minkG φ ex ex = 1 ∧ minkG φ et et = -1 ∧ minkG φ ex et = 0 ∧
      ∀ y, minkG φ y A = 0 → minkG φ y B = 0 →
        y = minkG φ y ex • ex - minkG φ y et • et := by
  have := LinearEquiv.finiteDimensional φ.symm
  have hg := minkG_comm φ
  have hdet := det_gram_neg φ hli
  rw [det_gram_block _ hg hCA hCB hDA hDB] at hdet
  have hW : minkG φ C C * minkG φ D D - minkG φ C D ^ 2 < 0 := by nlinarith
  obtain ⟨hCF, hFF⟩ := orth_step hg (D := D) hCC
  obtain ⟨ex, et, h1, h2, h3, hexp⟩ := exists_lorFrame_of_orth hg hCF (by rw [hFF]; exact hW)
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [finrank_of_equiv φ])
  refine ⟨ex, et, h1, h2, h3, fun y hyA hyB => ?_⟩
  obtain ⟨γ, δ, rfl⟩ := exists_orth_coeffs hg hspan hCA hCB hDA hDB hG.ne' hyA hyB
  have e : γ • C + δ • D = (γ + δ * (minkG φ C D / minkG φ C C)) • C +
      δ • (D - (minkG φ C D / minkG φ C C) • C) := by
    module
  rw [e]
  exact hexp _ _

/-- **The normal plane of a timelike triangle is Euclidean.** Let `A, B, C, D` be a basis with
`C, D` `minkG`-orthogonal to `A, B` and the triangle spanned by `A, B` timelike (negative Gram
determinant). Then the vectors orthogonal to `A, B` have an orthonormal frame. -/
theorem exists_eucFrame {A B C D : E} (hli : LinearIndependent ℝ ![A, B, C, D])
    (hCA : minkG φ C A = 0) (hCB : minkG φ C B = 0) (hDA : minkG φ D A = 0)
    (hDB : minkG φ D B = 0)
    (hG : minkG φ A A * minkG φ B B - minkG φ A B ^ 2 < 0) :
    ∃ e₂ e₃ : E, minkG φ e₂ e₂ = 1 ∧ minkG φ e₃ e₃ = 1 ∧ minkG φ e₂ e₃ = 0 ∧
      ∀ y, minkG φ y A = 0 → minkG φ y B = 0 →
        y = minkG φ y e₂ • e₂ + minkG φ y e₃ • e₃ := by
  have := LinearEquiv.finiteDimensional φ.symm
  have hg := minkG_comm φ
  have hdet := det_gram_neg φ hli
  rw [det_gram_block _ hg hCA hCB hDA hDB] at hdet
  have hW : 0 < minkG φ C C * minkG φ D D - minkG φ C D ^ 2 := by nlinarith
  have hCC : minkG φ C C ≠ 0 := by
    intro h
    rw [h, zero_mul] at hW
    nlinarith [sq_nonneg (minkG φ C D)]
  obtain ⟨hCF, hFF⟩ := orth_step hg (D := D) hCC
  set F := D - (minkG φ C D / minkG φ C C) • C
  have hpos : 0 < minkG φ C C := by
    by_contra hle
    have hC : minkG φ C C < 0 := lt_of_le_of_ne (not_lt.mp hle) hCC
    have hF : minkG φ F F < 0 := by nlinarith
    exact minkG_ne_zero_of_timelike φ hC hF hCF
  have hF : 0 < minkG φ F F := by nlinarith
  obtain ⟨e₂, e₃, h1, h2, h3, hexp⟩ := exists_eucFrame_of_orth hg hCF hpos hF
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [finrank_of_equiv φ])
  refine ⟨e₂, e₃, h1, h2, h3, fun y hyA hyB => ?_⟩
  obtain ⟨γ, δ, rfl⟩ := exists_orth_coeffs hg hspan hCA hCB hDA hDB hG.ne hyA hyB
  have e : γ • C + δ • D = (γ + δ * (minkG φ C D / minkG φ C C)) • C + δ • F := by
    simp only [F]
    module
  rw [e]
  exact hexp _ _

end NormalFrames

/-! ## Polar coordinates in the normal plane -/

section Polar

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {g : LinearMap.BilinForm ℝ E}

/-- Replacing the last two vectors of a basis `A, B, c, d` by their `g`-projections orthogonal to
`A, B` keeps them linearly independent. -/
theorem linIndep_perpL (g : LinearMap.BilinForm ℝ E) {A B c d : E}
    (h : LinearIndependent ℝ ![A, B, c, d]) :
    LinearIndependent ℝ ![A, B, perpL g A B c, perpL g A B d] := by
  obtain ⟨s, t, hc⟩ : ∃ s t : ℝ, perpL g A B c = c - s • A - t • B := ⟨_, _, rfl⟩
  obtain ⟨s', t', hd⟩ : ∃ s t : ℝ, perpL g A B d = d - s • A - t • B := ⟨_, _, rfl⟩
  rw [hc, hd]
  have key := Fintype.linearIndependent_iff.mp h
  refine Fintype.linearIndependent_iff.mpr fun k hk => ?_
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hk
  have h0 := key ![k 0 - k 2 * s - k 3 * s', k 1 - k 2 * t - k 3 * t', k 2, k 3] (by
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    convert hk using 1
    module)
  have e0 := h0 0
  have e1 := h0 1
  have e2 := h0 2
  have e3 := h0 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2 e3
  rw [e2, e3] at e0 e1
  simp only [zero_mul, sub_zero] at e0 e1
  intro i
  fin_cases i
  exacts [e0, e1, e2, e3]

omit [AddCommGroup E] [Module ℝ E] in
/-- **Polar coordinates in a frame.** `p e + q f = ρ (cos α e + sin α f)` with `ρ = |p + iq|` and
`α = arg (p + iq)`. -/
theorem polar_frame {E : Type*} [AddCommGroup E] [Module ℝ E] (e f : E) (p q : ℝ) :
    p • e + q • f = ‖(⟨p, q⟩ : ℂ)‖ •
      (cos (Complex.arg ⟨p, q⟩) • e + sin (Complex.arg ⟨p, q⟩) • f) := by
  have h1 : ‖(⟨p, q⟩ : ℂ)‖ * cos (Complex.arg ⟨p, q⟩) = p := Complex.norm_mul_cos_arg _
  have h2 : ‖(⟨p, q⟩ : ℂ)‖ * sin (Complex.arg ⟨p, q⟩) = q := Complex.norm_mul_sin_arg _
  rw [smul_add, smul_smul, smul_smul, h1, h2]

/-- In a Lorentzian frame (`g e_x e_x = 1`, `g e_t e_t = −1`), the vectors
`ρ (cos α e_x + sin α e_t)` have inner products `ρ ρ' cos (α + α')`. -/
theorem g_lorPolar (hg : ∀ y z, g y z = g z y) {ex et : E} (h1 : g ex ex = 1)
    (h2 : g et et = -1) (h3 : g ex et = 0) (r α r' α' : ℝ) :
    g (r • (cos α • ex + sin α • et)) (r' • (cos α' • ex + sin α' • et)) =
      r * r' * cos (α + α') := by
  have h4 : g et ex = 0 := by rw [hg, h3]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2,
    h3, h4]
  rw [cos_add]
  ring

/-- In an orthonormal frame, the vectors `ρ (cos α e₂ + sin α e₃)` have inner products
`ρ ρ' cos (α' − α)`. -/
theorem g_eucPolar (hg : ∀ y z, g y z = g z y) {e₂ e₃ : E} (h1 : g e₂ e₂ = 1)
    (h2 : g e₃ e₃ = 1) (h3 : g e₂ e₃ = 0) (r α r' α' : ℝ) :
    g (r • (cos α • e₂ + sin α • e₃)) (r' • (cos α' • e₂ + sin α' • e₃)) =
      r * r' * cos (α' - α) := by
  have h4 : g e₃ e₂ = 0 := by rw [hg, h3]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2,
    h3, h4]
  rw [cos_sub]
  ring

end Polar

/-! ## Flat Lorentzian triangulations -/

section Embedded

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Disjoint 4-simplices give disjoint wedges.** If the link vertices of the triangle `abc`
decompose as `x (w k) − x a = ζ_k (x b − x a) + η_k (x c − x a) + ρ_k (cos α_k e + sin α_k f)` with
`ρ_k > 0`, and the open 4-simplices `{a, b, c, w i, w (i+1)}` are pairwise disjoint, then so are
the open wedges between consecutive directions `α_i, α_{i+1}`. Only the affine structure is used;
the frame `e, f` is arbitrary. -/
theorem wedges_disjoint {x : V → E} {a b c : V} {n : ℕ} {w : ℕ → V} {e f : E}
    {ζ η r α : ℕ → ℝ}
    (hdec : ∀ k, x (w k) - x a =
      ζ k • (x b - x a) + η k • (x c - x a) + r k • (cos (α k) • e + sin (α k) • f))
    (hr : ∀ k ≤ n, 0 < r k)
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (open4 (x a) (x b) (x c) (x (w i)) (x (w (i + 1))))
        (open4 (x a) (x b) (x c) (x (w j)) (x (w (j + 1))))) :
    ∀ i < n, ∀ j < n, i ≠ j → ∀ τ, InWedge (α i) (α (i + 1)) τ →
      ¬ InWedge (α j) (α (j + 1)) τ := by
  intro i hi j hj hij τ h1 h2
  obtain ⟨l, m, hl, hm, hcl, hsl⟩ := h1
  obtain ⟨l', m', hl', hm', hcl', hsl'⟩ := h2
  have hx : ∀ k, x (w k) = x a + ζ k • (x b - x a) + η k • (x c - x a) +
      r k • (cos (α k) • e + sin (α k) • f) := by
    intro k
    rw [add_assoc, add_assoc, ← add_assoc (ζ k • _), ← hdec k]
    abel
  obtain ⟨δ₁, hδ₁, H₁⟩ := mem_open4_near (hx i) (hx (i + 1))
    (div_pos hl (hr i hi.le)) (div_pos hm (hr (i + 1) hi))
  obtain ⟨δ₂, hδ₂, H₂⟩ := mem_open4_near (hx j) (hx (j + 1))
    (div_pos hl' (hr j hj.le)) (div_pos hm' (hr (j + 1) hj))
  have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hε : 0 < min δ₁ δ₂ / 2 := half_pos hmin
  have P₁ := H₁ (min δ₁ δ₂ / 2) hε (by linarith [min_le_left δ₁ δ₂])
  have P₂ := H₂ (min δ₁ δ₂ / 2) hε (by linarith [min_le_right δ₁ δ₂])
  have dir : ∀ (k : ℕ) (l m : ℝ), 0 < r k → 0 < r (k + 1) →
      (l / r k) • (r k • (cos (α k) • e + sin (α k) • f)) +
        (m / r (k + 1)) • (r (k + 1) • (cos (α (k + 1)) • e + sin (α (k + 1)) • f)) =
      (l * cos (α k) + m * cos (α (k + 1))) • e + (l * sin (α k) + m * sin (α (k + 1))) • f := by
    intro k l m h h'
    rw [smul_smul, smul_smul, div_mul_cancel₀ _ h.ne', div_mul_cancel₀ _ h'.ne']
    module
  rw [dir i l m (hr i hi.le) (hr (i + 1) hi), ← hcl, ← hsl] at P₁
  rw [dir j l' m' (hr j hj.le) (hr (j + 1) hj), ← hcl', ← hsl'] at P₂
  exact Set.disjoint_left.mp (hdisj i hi j hj hij) P₁ P₂

variable (φ : E ≃ₗ[ℝ] (Fin 4 → ℝ))

/-- The signed squared edge lengths of a placement `x` of the vertices in Minkowski space, in the
inertial coordinates `φ`: `L {u, v} = η(x v − x u, x v − x u)`. -/
noncomputable def lorLen (x : V → E) : Finset V → ℝ :=
  ofDist fun u v => minkG φ (x v - x u) (x v - x u)

/-- `lorLen φ x` gives the edge `{u, v}` the Minkowski square of `x v − x u`. -/
theorem lorLen_pair (x : V → E) {u v : V} (h : u ≠ v) :
    lorLen φ x {u, v} = minkG φ (x v - x u) (x v - x u) :=
  ofDist_pair (d := fun u v => minkG φ (x v - x u) (x v - x u)) (fun u => by simp)
    (fun u v => by simp; ring) h

/-- The signed squared lengths `lorLen φ x` in the form used by the length formulas of
`Lightlike/Regge/Lorentzian/Dihedral.lean`. -/
theorem lorLen_eq (x : V → E) :
    ∀ u v, u ≠ v → lorLen φ x {u, v} = minkG φ (x v - x u) (x v - x u) :=
  fun _ _ h => lorLen_pair φ x h

/-- **A flat Lorentzian triangulation has zero deficit at a spacelike triangle.** Let `x` place the
vertices of `K` in a 4-dimensional real vector space `E` with inertial coordinates `φ`, so that
the edges get the signed squared lengths `L = lorLen φ x` of Minkowski space. Suppose the link of
the triangle `abc` is a cycle `w 0, …, w (n-1)` (`IsCycleLink4`), each 4-simplex
`{a, b, c, w i, w (i+1)}` is non-degenerate, their interiors are pairwise disjoint, the triangle is
spacelike (`gram2L L a b c > 0`) and no tetrahedron `{a, b, c, w i}` is null
(`gram3L L a b c (w i) ≠ 0`). Then the Lorentzian deficit angle at `abc` is zero: Sorkin's
complex dihedral angles add up to `−2πi`. The inner product on `E` serves only to state the
disjointness of the 4-simplices (`open4`); the Minkowski form is `minkG φ`. -/
theorem lorDeficit_eq_zero_of_spacelike (K : Complex4 V) (x : V → E) {a b c : V} {n : ℕ}
    {w : ℕ → V} (hc : IsCycleLink4 K a b c n w)
    (hnd : ∀ i < n, LinearIndependent ℝ
      ![x b - x a, x c - x a, x (w i) - x a, x (w (i + 1)) - x a])
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (open4 (x a) (x b) (x c) (x (w i)) (x (w (i + 1))))
        (open4 (x a) (x b) (x c) (x (w j)) (x (w (j + 1)))))
    (hsp : 0 < gram2L (lorLen φ x) a b c)
    (hnull : ∀ i < n, gram3L (lorLen φ x) a b c (w i) ≠ 0) :
    lorDeficit K (lorLen φ x) {a, b, c} = 0 := by
  have h3 := hc.three_le
  have hn : 0 < n := by omega
  set g := minkG φ with hg_def
  have hg : ∀ y z, g y z = g z y := minkG_comm φ
  have hL := lorLen_eq φ x
  set A := x b - x a with hA
  set B := x c - x a with hB
  have hG : 0 < g A A * g B B - g A B ^ 2 := by
    rw [← gram2L_eq_g hg x hL a b c]
    exact hsp
  set P : ℕ → E := fun k => perpL g A B (x (w k) - x a) with hP
  have hPA : ∀ k, g (P k) A = 0 := fun k => g_perpL_left hg hG.ne' _
  have hPB : ∀ k, g (P k) B = 0 := fun k => g_perpL_right hG.ne' _
  have hPP : ∀ i < n, g (P i) (P i) ≠ 0 := by
    intro i hi h0
    apply hnull i hi
    rw [gram3L_eq_g hg x hL hsp.ne' (w i)]
    change gram2L _ a b c * g (P i) (P i) = 0
    rw [h0, mul_zero]
  have hli := linIndep_perpL g (hnd 0 hn)
  obtain ⟨ex, et, h1, h2, h3', hexp⟩ :=
    exists_lorFrame φ hli (hPA 0) (hPB 0) (hPA 1) (hPB 1) hG (hPP 0 hn)
  -- polar coordinates of the normal components in the Lorentzian frame
  set r : ℕ → ℝ := fun k => ‖(⟨g (P k) ex, -g (P k) et⟩ : ℂ)‖ with hr_def
  set α : ℕ → ℝ := fun k => Complex.arg ⟨g (P k) ex, -g (P k) et⟩ with hα_def
  have hPpol : ∀ k, P k = r k • (cos (α k) • ex + sin (α k) • et) := by
    intro k
    rw [← polar_frame ex et, neg_smul, ← sub_eq_add_neg]
    exact hexp _ (hPA k) (hPB k)
  choose ζ η hζη using fun k =>
    Submodule.mem_span_pair.mp (sub_perpL_mem_span (g := g) (a := A) (b := B) (x (w k) - x a))
  have hdec : ∀ k, x (w k) - x a =
      ζ k • A + η k • B + r k • (cos (α k) • ex + sin (α k) • et) := by
    intro k
    rw [hζη k, ← hPpol k]
    simp only [hP]
    abel
  have hrn : r n = r 0 := by simp only [hr_def, hP, hc.closed]
  have hαn : α n = α 0 := by simp only [hα_def, hP, hc.closed]
  have hnd' := fun i hi => polar_nondeg (hdec i) (hdec (i + 1)) (hnd i hi)
  have hrpos : ∀ i ≤ n, 0 < r i := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact lt_of_le_of_ne (norm_nonneg _) (hnd' i h).1.symm
    · rw [h, hrn]
      exact lt_of_le_of_ne (norm_nonneg _) (hnd' 0 hn).1.symm
  have hW := wedges_disjoint hdec hrpos hdisj
  have hgP : ∀ i j, g (P i) (P j) = r i * r j * cos (α i + α j) := by
    intro i j
    rw [hPpol i, hPpol j]
    exact g_lorPolar hg h1 h2 h3' _ _ _ _
  have hcos : ∀ k ≤ n, cos (2 * α k) ≠ 0 := by
    intro k hk h0
    have hk' : g (P k) (P k) ≠ 0 := by
      rcases Nat.lt_or_eq_of_le hk with h | h
      · exact hPP k h
      · rw [h]
        simp only [hP, hc.closed]
        exact hPP 0 hn
    apply hk'
    rw [hgP, ← two_mul, h0, mul_zero]
  have hsum := sum_sorkinAngle_eq hn α r hrpos hcos (fun i hi => (hnd' i hi).2.2)
    ⟨by rw [hαn], by rw [hαn]⟩ hW
  have hterm : ∀ i ∈ range n,
      lorDihedralAt (lorLen φ x) {a, b, c, w i, w (i + 1)} {a, b, c} =
        sorkinAngle (r i ^ 2 * cos (2 * α i)) (r (i + 1) ^ 2 * cos (2 * α (i + 1)))
          (r i * r (i + 1) * cos (α i + α (i + 1))) := by
    intro i hi
    have hi' := mem_range.mp hi
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hc.simp_distinct hi'
    rw [lorDihedralAt_eq _ hc.ne_ab hc.ne_ac h₁ h₂ hc.ne_bc h₃ h₄ h₅ h₆ h₇,
      lorDihedral4_eq_of_pos hg x hL hsp (w i) (w (i + 1))]
    change sorkinAngle (g (P i) (P i)) (g (P (i + 1)) (P (i + 1))) (g (P i) (P (i + 1))) = _
    rw [hgP, hgP, hgP]
    congr 1 <;> ring_nf
  have hZ : causalZ (lorLen φ x) {a, b, c} = -Complex.I := by
    have h4 : 0 < triHL (lorLen φ x) {a, b, c} := by
      rw [triHL_eq _ hc.ne_ab hc.ne_ac hc.ne_bc]
      linarith
    simp only [causalZ, h4, ↓reduceIte]
  rw [lorDeficit, hZ, lorAngleSum_eq_of_cycleLink hc, sum_congr rfl hterm, hsum]
  ring

/-- **A flat Lorentzian triangulation has zero deficit at a timelike triangle.** As in
`lorDeficit_eq_zero_of_spacelike`, for a timelike triangle `abc` (`gram2L L a b c < 0`): its
normal plane is Euclidean, the dihedral angles are real and add up to `2π`. No condition on the
tetrahedra is needed: in a Euclidean normal plane none of them is null. -/
theorem lorDeficit_eq_zero_of_timelike (K : Complex4 V) (x : V → E) {a b c : V} {n : ℕ}
    {w : ℕ → V} (hc : IsCycleLink4 K a b c n w)
    (hnd : ∀ i < n, LinearIndependent ℝ
      ![x b - x a, x c - x a, x (w i) - x a, x (w (i + 1)) - x a])
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (open4 (x a) (x b) (x c) (x (w i)) (x (w (i + 1))))
        (open4 (x a) (x b) (x c) (x (w j)) (x (w (j + 1)))))
    (htl : gram2L (lorLen φ x) a b c < 0) :
    lorDeficit K (lorLen φ x) {a, b, c} = 0 := by
  have h3 := hc.three_le
  have hn : 0 < n := by omega
  set g := minkG φ with hg_def
  have hg : ∀ y z, g y z = g z y := minkG_comm φ
  have hL := lorLen_eq φ x
  set A := x b - x a with hA
  set B := x c - x a with hB
  have hG : g A A * g B B - g A B ^ 2 < 0 := by
    rw [← gram2L_eq_g hg x hL a b c]
    exact htl
  set P : ℕ → E := fun k => perpL g A B (x (w k) - x a) with hP
  have hPA : ∀ k, g (P k) A = 0 := fun k => g_perpL_left hg hG.ne _
  have hPB : ∀ k, g (P k) B = 0 := fun k => g_perpL_right hG.ne _
  have hli := linIndep_perpL g (hnd 0 hn)
  obtain ⟨e₂, e₃, h1, h2, h3', hexp⟩ :=
    exists_eucFrame φ hli (hPA 0) (hPB 0) (hPA 1) (hPB 1) hG
  set r : ℕ → ℝ := fun k => ‖(⟨g (P k) e₂, g (P k) e₃⟩ : ℂ)‖ with hr_def
  set α : ℕ → ℝ := fun k => Complex.arg ⟨g (P k) e₂, g (P k) e₃⟩ with hα_def
  have hPpol : ∀ k, P k = r k • (cos (α k) • e₂ + sin (α k) • e₃) := fun k =>
    (hexp _ (hPA k) (hPB k)).trans (polar_frame e₂ e₃ _ _)
  choose ζ η hζη using fun k =>
    Submodule.mem_span_pair.mp (sub_perpL_mem_span (g := g) (a := A) (b := B) (x (w k) - x a))
  have hdec : ∀ k, x (w k) - x a =
      ζ k • A + η k • B + r k • (cos (α k) • e₂ + sin (α k) • e₃) := by
    intro k
    rw [hζη k, ← hPpol k]
    simp only [hP]
    abel
  have hrn : r n = r 0 := by simp only [hr_def, hP, hc.closed]
  have hαn : α n = α 0 := by simp only [hα_def, hP, hc.closed]
  have hnd' := fun i hi => polar_nondeg (hdec i) (hdec (i + 1)) (hnd i hi)
  have hrpos : ∀ i ≤ n, 0 < r i := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact lt_of_le_of_ne (norm_nonneg _) (hnd' i h).1.symm
    · rw [h, hrn]
      exact lt_of_le_of_ne (norm_nonneg _) (hnd' 0 hn).1.symm
  have hW := wedges_disjoint hdec hrpos hdisj
  have hgP : ∀ i j, g (P i) (P j) = r i * r j * cos (α j - α i) := by
    intro i j
    rw [hPpol i, hPpol j]
    exact g_eucPolar hg h1 h2 h3' _ _ _ _
  have hsum := sum_arccos_cos_eq_two_pi hn α (fun i hi => (hnd' i hi).2.2)
    ⟨by rw [hαn], by rw [hαn]⟩ hW
  have hterm : ∀ i ∈ range n,
      lorDihedralAt (lorLen φ x) {a, b, c, w i, w (i + 1)} {a, b, c} =
        ((arccos (cos (α (i + 1) - α i)) : ℝ) : ℂ) := by
    intro i hi
    have hi' := mem_range.mp hi
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hc.simp_distinct hi'
    rw [lorDihedralAt_eq _ hc.ne_ab hc.ne_ac h₁ h₂ hc.ne_bc h₃ h₄ h₅ h₆ h₇,
      lorDihedral4_eq_of_neg hg x hL htl (w i) (w (i + 1))]
    change ((arccos (g (P i) (P (i + 1)) /
      √(g (P i) (P i) * g (P (i + 1)) (P (i + 1)))) : ℝ) : ℂ) = _
    have hp : 0 < r i * r (i + 1) := mul_pos (hrpos i hi'.le) (hrpos (i + 1) hi')
    simp only [hgP, sub_self, cos_zero, mul_one]
    rw [show r i * r i * (r (i + 1) * r (i + 1)) = (r i * r (i + 1)) ^ 2 by ring,
      Real.sqrt_sq hp.le, mul_div_cancel_left₀ _ hp.ne']
  have hZ : causalZ (lorLen φ x) {a, b, c} = 1 := by
    have h4 : ¬ 0 < triHL (lorLen φ x) {a, b, c} := by
      rw [triHL_eq _ hc.ne_ab hc.ne_ac hc.ne_bc]
      linarith
    simp only [causalZ, h4, ↓reduceIte]
  rw [lorDeficit, hZ, lorAngleSum_eq_of_cycleLink hc, sum_congr rfl hterm, ← Complex.ofReal_sum,
    hsum]
  push_cast
  ring

/-- **Non-null lengths**: no triangle and no tetrahedron of `K` is null in the signed squared
lengths `L` (in every labelling of its vertices, as in `Lightlike.Regge4.LengthsNondeg4`). At a null
tetrahedron Sorkin's angle has an infinite boost and is undefined. -/
structure IsNonNull4 (K : Complex4 V) (L : Finset V → ℝ) : Prop where
  /-- No null triangles. -/
  tri : ∀ t ∈ K.tris, triHL L t ≠ 0
  /-- No null tetrahedra. -/
  tet : ∀ p q r s : V, ({p, q, r, s} : Finset V) ∈ K.tets → gram3L L p q r s ≠ 0

/-- **A flat Lorentzian triangulation has zero deficit at every non-null triangle whose link is a
cycle**, of either causal type (`lorDeficit_eq_zero_of_spacelike`,
`lorDeficit_eq_zero_of_timelike`). -/
theorem lorDeficit_eq_zero_of_embedded (K : Complex4 V) (x : V → E) {a b c : V} {n : ℕ}
    {w : ℕ → V} (hc : IsCycleLink4 K a b c n w)
    (hnd : ∀ i < n, LinearIndependent ℝ
      ![x b - x a, x c - x a, x (w i) - x a, x (w (i + 1)) - x a])
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (open4 (x a) (x b) (x c) (x (w i)) (x (w (i + 1))))
        (open4 (x a) (x b) (x c) (x (w j)) (x (w (j + 1)))))
    (htri : gram2L (lorLen φ x) a b c ≠ 0)
    (hnull : 0 < gram2L (lorLen φ x) a b c → ∀ i < n, gram3L (lorLen φ x) a b c (w i) ≠ 0) :
    lorDeficit K (lorLen φ x) {a, b, c} = 0 := by
  rcases lt_or_gt_of_ne htri with h | h
  · exact lorDeficit_eq_zero_of_timelike φ K x hc hnd hdisj h
  · exact lorDeficit_eq_zero_of_spacelike φ K x hc hnd hdisj h (hnull h)

/-- **In a geometric triangulation of a region of Minkowski space, a non-null triangle whose link
is a cycle has zero deficit.** -/
theorem IsGeometric4.lorDeficit_eq_zero_of_cycleLink {K : Complex4 V} {x : V → E}
    (hK : IsGeometric4 K x) {a b c : V} {n : ℕ} {w : ℕ → V}
    (hc : IsCycleLink4 K a b c n w) (htri : gram2L (lorLen φ x) a b c ≠ 0)
    (hnull : 0 < gram2L (lorLen φ x) a b c → ∀ i < n, gram3L (lorLen φ x) a b c (w i) ≠ 0) :
    lorDeficit K (lorLen φ x) {a, b, c} = 0 := by
  have := LinearEquiv.finiteDimensional φ.symm
  have hE := finrank_of_equiv φ
  apply lorDeficit_eq_zero_of_embedded φ K x hc _ _ htri hnull
  · intro i hi
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hc.simp_distinct hi
    exact linIndep_of_affIndep5 x hc.ne_ab hc.ne_ac h₁ h₂ hc.ne_bc h₃ h₄ h₅ h₆ h₇
      (hK.nondeg _ (hc.simp_mem hi))
  · intro i hi j hj hij
    have hne : ({a, b, c, w i, w (i + 1)} : Finset V) ≠ {a, b, c, w j, w (j + 1)} := fun h =>
      hij (hc.injOn_simp (by simpa using hi) (by simpa using hj) h)
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hc.simp_distinct hi
    obtain ⟨k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩ := hc.simp_distinct hj
    have hd := hK.disjoint _ (hc.simp_mem hi) _ (hc.simp_mem hj) hne
    rw [← openHull_eq_interior4 hE x (K.card_eq _ (hc.simp_mem hi))
        (hK.nondeg _ (hc.simp_mem hi)),
      ← openHull_eq_interior4 hE x (K.card_eq _ (hc.simp_mem hj))
        (hK.nondeg _ (hc.simp_mem hj)),
      openHull_eq_open4 x hc.ne_ab hc.ne_ac h₁ h₂ hc.ne_bc h₃ h₄ h₅ h₆ h₇,
      openHull_eq_open4 x hc.ne_ab hc.ne_ac k₁ k₂ hc.ne_bc k₃ k₄ k₅ k₆ k₇] at hd
    exact hd

/-- **Flat Minkowski space has zero curvature: every interior triangle of a non-null geometric
triangulation of a region of Minkowski space has Lorentzian deficit angle zero.** Here `K`
satisfies the manifold condition at triangles and is placed in a 4-dimensional real vector space
with inertial coordinates `φ` by a geometric triangulation `x`, with the induced signed squared
lengths. -/
theorem IsGeometric4.lorDeficit_eq_zero {K : Complex4 V} {x : V → E}
    (hK : IsGeometric4 K x) (hM : IsTriManifold K) (hN : IsNonNull4 K (lorLen φ x))
    {t : Finset V} (ht : t ∈ intTris4 K) :
    lorDeficit K (lorLen φ x) t = 0 := by
  have htris : t ∈ K.tris := (mem_filter.mp ht).1
  obtain ⟨a, b, c, n, w, rfl, hc⟩ := hM.mem_intTris4_iff.mp ht
  refine IsGeometric4.lorDeficit_eq_zero_of_cycleLink φ hK hc (fun h0 => hN.tri _ htris ?_)
    (fun _ i hi => hN.tet a b c (w i) ?_)
  · rw [triHL_eq _ hc.ne_ab hc.ne_ac hc.ne_bc, h0, mul_zero]
  · obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hc.simp_distinct hi
    refine mem_faces.mpr ⟨_, hc.simp_mem hi, ?_, card_four hc.ne_ab hc.ne_ac h₁ hc.ne_bc h₃ h₅⟩
    intro v hv
    simp only [mem_insert, mem_singleton] at hv ⊢
    tauto

/-- **The Lorentzian Regge action of a flat region of Minkowski space is a pure boundary term**:
`S = Σ_{boundary triangles} A_t (π Z_t − Σ θ)`. -/
theorem IsGeometric4.lorReggeAction_eq {K : Complex4 V} {x : V → E}
    (hK : IsGeometric4 K x) (hM : IsTriManifold K) (hN : IsNonNull4 K (lorLen φ x)) :
    lorReggeAction K (lorLen φ x) =
      ∑ t ∈ bdryTris4 K, (lorArea (lorLen φ x) t : ℂ) * lorBdryAngle K (lorLen φ x) t := by
  rw [lorReggeAction, sum_eq_zero fun t ht => by rw [IsGeometric4.lorDeficit_eq_zero φ hK hM hN ht,
    mul_zero],
    zero_add]

end Embedded

end Lightlike.ReggeLor
