import Lightlike.Asymptotics.Lorentzian.Classification
import Lightlike.Lorentz.SL2C

/-!
# Parity and the critical equations of the Lorentzian action for `SL(2, ℂ)` group elements

Barrett, Dowdall, Fairbairn, Hellmann and Pereira (arXiv:0907.2440, Section 4.2) reduce the
critical points of the Lorentzian EPRL action to four equations. With the spinor `z_ab`
eliminated, two of them are, for every edge `e = ab` with unit boundary spinors `ξ_ab`, `ξ_ba`,

* eq. (20): `(X_a†)⁻¹ ξ_ab = r c (X_b†)⁻¹ J ξ_ba`,
* eq. (21): `X_a ξ_ab = r⁻¹ c X_b J ξ_ba`,

with `r = ‖Z_ba‖/‖Z_ab‖ > 0` and a phase `c`; the other two are `p = γ k` (eq. (24)) and closure
`Σ k n = 0` (eq. (25)), which do not involve `X`. This file treats the first two.

* `spinAct M v`: the matrix `M` acting on a spinor; `spinAct_mul`, `spinAct_one`,
  `spinAct_inv_spinAct`.
* `parityMap X = (X†)⁻¹`, the parity map of `SL(2, ℂ)` (eqs. (37), (38) of the source), with
  `coe_parityMap`, `parityMap_parityMap` (an involution), `parityMap_ofSU2` (the identity on
  `SU(2)`) and `parityMap_eq_self_iff` (fixed exactly when `X` is unitary).
* `jMap_spinAct`: `J (X v) = (X†)⁻¹ (J v)` (eq. (33) of the source), which for `SU(2)` says that `J`
  commutes with the group (`jMap_spinAct_ofSU2`).
* `IsLorCritical g X`: the equations (20) and (21) on all ten edges.
* `isLorCritical_parity`: parity maps critical configurations to critical configurations
  (Section 5.4.2 of the source), exchanging (20) and (21).
* `isLorCritical_ofSU2_iff`: for `SU(2)` group elements the equations are exactly the `SU(2)`
  critical condition `IsSU2Critical`, and then `r = 1`.
* Trust checks: parity is not the identity on a boost, the twisted data
  have the critical point `X = 1`, and parallel instead of antiparallel normals do not.

Not covered: the existence of a critical `X` outside `SU(2)`, the classification of the critical
points over `SL(2, ℂ)` (Section 5.4.3 of the source, which rests on the bivector reconstruction
theorem), and the elimination of `z` (the predicate here is the result of the elimination).
-/

open Complex
open scoped ComplexConjugate Matrix

namespace Lightlike.Asymptotics.Lorentzian

open Lightlike.Lorentz (SL2C)
open Lightlike.Asymptotics.EPRL

/-- The matrix `M` acting on a spinor of `ℂ²`. -/
noncomputable def spinAct (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Spinor) : Spinor :=
  !₂[M 0 0 * v 0 + M 0 1 * v 1, M 1 0 * v 0 + M 1 1 * v 1]

@[simp] lemma spinAct_zero_apply (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Spinor) :
    spinAct M v 0 = M 0 0 * v 0 + M 0 1 * v 1 := rfl

@[simp] lemma spinAct_one_apply (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Spinor) :
    spinAct M v 1 = M 1 0 * v 0 + M 1 1 * v 1 := rfl

/-- The identity matrix acts trivially. -/
lemma spinAct_one (v : Spinor) : spinAct 1 v = v := by
  ext i; fin_cases i <;> simp

/-- Matrix multiplication is composition of the actions. -/
lemma spinAct_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) (v : Spinor) :
    spinAct (M * N) v = spinAct M (spinAct N v) := by
  ext i; fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- An element of `SL(2, ℂ)` acts injectively: its inverse undoes it. -/
lemma spinAct_inv_spinAct (X : SL2C) (v : Spinor) :
    spinAct ((X⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) (spinAct (X : Matrix (Fin 2) (Fin 2) ℂ) v) =
      v := by
  rw [← spinAct_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, spinAct_one]

lemma spinAct_eq_zero {X : SL2C} {v : Spinor}
    (h : spinAct (X : Matrix (Fin 2) (Fin 2) ℂ) v = 0) : v = 0 := by
  have := spinAct_inv_spinAct X v
  rw [h] at this
  rw [← this]
  ext i; fin_cases i <;> simp

lemma spinAct_smul (M : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (v : Spinor) :
    spinAct M (c • v) = c • spinAct M v := by
  ext i; fin_cases i <;> simp <;> ring

/-- **Parity on `SL(2, ℂ)`**: `X ↦ (X†)⁻¹` (BDFHP Section 5.4.2, eqs. (37), (38)). It is written
with the entries of the inverse, `[[a, b], [c, d]] ↦ [[d̄, -c̄], [-b̄, ā]]`, which is `(X†)⁻¹` for
`det X = 1` (`coe_parityMap`). -/
noncomputable def parityMap (X : SL2C) : SL2C :=
  Lightlike.Lorentz.SL2C.mk (conj (X 1 1)) (-conj (X 1 0)) (-conj (X 0 1)) (conj (X 0 0)) (by
    have h := congrArg (starRingEnd ℂ) (Lightlike.Lorentz.SL2C.det_eq X)
    simp only [map_sub, map_mul, map_one] at h
    linear_combination h)

/-- Parity is `X ↦ (X†)⁻¹`. -/
theorem coe_parityMap (X : SL2C) :
    (parityMap X : Matrix (Fin 2) (Fin 2) ℂ) = ((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  have h := Lightlike.Lorentz.SL2C.det_eq X
  have h' := congrArg (starRingEnd ℂ) h
  simp only [map_sub, map_mul, map_one] at h'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, parityMap, Matrix.conjTranspose_apply] <;>
    first | ring1 | linear_combination h'

/-- Parity is an involution. -/
theorem parityMap_parityMap (X : SL2C) : parityMap (parityMap X) = X := by
  apply Lightlike.Lorentz.SL2C.ext' <;> simp [parityMap]

/-- Parity fixes the elements of `SU(2)`. -/
theorem parityMap_ofSU2 (u : Lightlike.SU2) :
    parityMap (Lightlike.Lorentz.SL2C.ofSU2 u) = Lightlike.Lorentz.SL2C.ofSU2 u := by
  apply Subtype.ext
  rw [coe_parityMap]
  apply Matrix.inv_eq_right_inv
  have := Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup u.2)
  simpa [Matrix.star_eq_conjTranspose] using this

/-- Parity fixes `X` exactly when `X` is unitary, that is, lies in `SU(2)`. -/
theorem parityMap_eq_self_iff (X : SL2C) :
    parityMap X = X ↔ (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (X : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have hu : IsUnit ((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).det := by
    have hd : (X : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := X.2
    rw [Matrix.det_conjTranspose, hd]
    simp
  constructor
  · intro h
    have h2 := congrArg (fun Y : SL2C => (Y : Matrix (Fin 2) (Fin 2) ℂ)) h
    simp only [coe_parityMap] at h2
    have h3 := Matrix.mul_nonsing_inv _ hu
    rwa [h2] at h3
  · intro h
    apply Subtype.ext
    rw [coe_parityMap]
    exact Matrix.inv_eq_right_inv h

/-- **`J` intertwines `X` and `(X†)⁻¹`** (BDFHP eq. (33)): `J (X v) = (X†)⁻¹ (J v)` for
`X ∈ SL(2, ℂ)`. It uses `det X = 1`. -/
theorem jMap_spinAct (X : SL2C) (v : Spinor) :
    jMap (spinAct (X : Matrix (Fin 2) (Fin 2) ℂ) v) =
      spinAct (parityMap X : Matrix (Fin 2) (Fin 2) ℂ) (jMap v) := by
  have h := Lightlike.Lorentz.SL2C.det_eq X
  have h' := congrArg (starRingEnd ℂ) h
  simp only [map_sub, map_mul, map_one] at h'
  ext i
  fin_cases i <;> simp [parityMap]
  ring

/-- For `SU(2)`, `J` commutes with the group action. -/
theorem jMap_spinAct_ofSU2 (u : Lightlike.SU2) (v : Spinor) :
    jMap (spinAct (u : Matrix (Fin 2) (Fin 2) ℂ) v) =
      spinAct (u : Matrix (Fin 2) (Fin 2) ℂ) (jMap v) := by
  have := jMap_spinAct (Lightlike.Lorentz.SL2C.ofSU2 u) v
  rwa [parityMap_ofSU2] at this

/-- **Critical configurations of the Lorentzian EPRL action, with `z` eliminated** (BDFHP
Section 4.2, eqs. (20) and (21)). For boundary data `g` (the unit spinors of the edge `e = ab` are
the first columns `ξ_ab = g_ab e₀` and `ξ_ba = g_ba e₀`), `X : Fin 5 → SL(2, ℂ)` is critical when
for every edge there are a positive real `r` and a unit complex `c` with
`(X_a†)⁻¹ ξ_ab = r c (X_b†)⁻¹ J ξ_ba` and `X_a ξ_ab = r⁻¹ c X_b J ξ_ba`.
The ratio `r` is `‖Z_ba‖/‖Z_ab‖` in the source. The relations `p = γ k` (eq. (24)) and closure
`Σ k n = 0` (eq. (25)), the other two critical equations, do not involve `X` and are not part of
this predicate. This is the set obtained by eliminating `z`; no statement is made that such an `X`
exists outside `SU(2)`, or that there are finitely many. -/
def IsLorCritical (g : BdryData) (X : Fin 5 → SL2C) : Prop :=
  ∀ e : Fin 10, ∃ r : ℝ, 0 < r ∧ ∃ c : ℂ, ‖c‖ = 1 ∧
    spinAct (parityMap (X (edgeSrc e)) : Matrix (Fin 2) (Fin 2) ℂ) (firstCol (g e 0)) =
        ((r : ℂ) * c) • spinAct (parityMap (X (edgeTgt e)) : Matrix (Fin 2) (Fin 2) ℂ)
          (jMap (firstCol (g e 1))) ∧
    spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ) (firstCol (g e 0)) =
        ((r : ℂ)⁻¹ * c) • spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)
          (jMap (firstCol (g e 1)))

/-- **Parity maps critical configurations to critical configurations** (BDFHP Section 5.4.2,
eq. (38)): the ratio `r` is replaced by `r⁻¹`, which exchanges (20) and (21); the phase `c` is
unchanged. No hypothesis on the data. In general the image is a different configuration; on
`SU(2)` it is the same one (`parityMap_ofSU2`). -/
theorem isLorCritical_parity {g : BdryData} {X : Fin 5 → SL2C} (h : IsLorCritical g X) :
    IsLorCritical g (fun a => parityMap (X a)) := by
  intro e
  obtain ⟨r, hr, c, hc, h20, h21⟩ := h e
  refine ⟨r⁻¹, inv_pos.mpr hr, c, hc, ?_, ?_⟩
  · simp only [parityMap_parityMap]
    simpa using h21
  · simpa using h20

/-- The first column of a product is the matrix acting on the first column. -/
lemma firstCol_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    firstCol (M * N) = spinAct M (firstCol N) := by
  ext i; fin_cases i <;> simp [firstCol, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The `SU(2)` critical points are the `SU(2)` solutions of the Lorentzian critical
equations** (BDFHP Section 6.4 item 2, eq. (54); Section 5.3, eq. (36)): for `X : Fin 5 → SU(2)`,
`ofSU2 ∘ X` is Lorentzian critical if and only if `X` is `SU(2)` critical in the sense of the
Euclidean gluing (`IsSU2Critical`). In the direction `→` the two equations (20) and (21) agree
because parity is the identity, and comparing them forces `r = 1`. -/
theorem isLorCritical_ofSU2_iff {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → Lightlike.SU2) :
    IsLorCritical g (fun a => Lightlike.Lorentz.SL2C.ofSU2 (X a)) ↔ IsSU2Critical hg X := by
  have key : ∀ e : Fin 10, ∀ c : ℂ,
      firstCol ((X (edgeSrc e) * (⟨g e 0, hg e 0⟩ : Lightlike.SU2) : Lightlike.SU2) :
          Matrix (Fin 2) (Fin 2) ℂ) =
        c • jMap (firstCol (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) ↔
      spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ) (firstCol (g e 0)) =
        c • spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ) (jMap (firstCol (g e 1))) := by
    intro e c
    simp only [frameTgt, Submonoid.coe_mul, firstCol_mul, jMap_spinAct_ofSU2]
  constructor
  · intro h e
    obtain ⟨r, hr, c, hc, h20, h21⟩ := h e
    simp only [parityMap_ofSU2, Lightlike.Lorentz.SL2C.coe_ofSU2] at h20 h21
    have hne : spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ) (jMap (firstCol (g e 1))) ≠ 0 := by
      intro h0
      have := spinAct_eq_zero (X := Lightlike.Lorentz.SL2C.ofSU2 (X (edgeTgt e))) (by simpa using h0)
      have hn := norm_firstCol (⟨g e 1, hg e 1⟩ : Lightlike.SU2)
      exact jMap_ne_zero (fun h1 => by simp [h1] at hn) this
    have h3 : (((r : ℂ) * c) - (r : ℂ)⁻¹ * c) •
        spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ) (jMap (firstCol (g e 1))) = 0 := by
      rw [sub_smul, ← h20, ← h21, sub_self]
    have h4 : ((r : ℂ) * c) - (r : ℂ)⁻¹ * c = 0 := by
      rcases smul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h hne
    have hc0 : c ≠ 0 := by
      intro h0; simp [h0] at hc
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have h5 : (r : ℂ) = (r : ℂ)⁻¹ := by
      have : ((r : ℂ) - (r : ℂ)⁻¹) * c = 0 := by rw [sub_mul]; exact h4
      rcases mul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hc0
    have h6 : r = 1 := by
      have : r * r = 1 := by
        have h7 : (r : ℂ) * r = 1 := by
          calc (r : ℂ) * r = (r : ℂ) * (r : ℂ)⁻¹ := by rw [← h5]
            _ = 1 := mul_inv_cancel₀ hr0
        exact_mod_cast h7
      nlinarith
    subst h6
    exact ⟨c, hc, (key e c).2 (by simpa using h21)⟩
  · intro h e
    obtain ⟨c, hc, hce⟩ := h e
    have := (key e c).1 hce
    refine ⟨1, one_pos, c, hc, ?_, ?_⟩
    · simp only [parityMap_ofSU2, Lightlike.Lorentz.SL2C.coe_ofSU2]
      simpa using this
    · simpa using this

/-- Non-vacuity: the twisted data have the critical point `X = 1`, also as a Lorentzian critical
point. -/
example (h : Fin 10 → Lightlike.SU2) :
    IsLorCritical (twistData h) (fun _ => 1) := by
  have := (isLorCritical_ofSU2_iff (isSU2Data_twistData h) (fun _ => (1 : Lightlike.SU2))).2
    ((isSU2Critical_iff_glued _ _).2 (twistData_glued h))
  simpa using this

/-- Wrong-model control: with parallel instead of antiparallel normals (`g_ba = g_ab = 1`), `X = 1`
is not Lorentzian critical. -/
example : ¬ IsLorCritical (fun _ => ![1, 1]) (fun _ => 1) := by
  intro hc
  have hg : IsSU2Data (fun _ : Fin 10 => ![(1 : Matrix (Fin 2) (Fin 2) ℂ), 1]) :=
    fun _ i => by fin_cases i <;> exact one_mem _
  have h := (isLorCritical_ofSU2_iff hg (fun _ => (1 : Lightlike.SU2))).1 (by simpa using hc)
  have h0 := (isSU2Critical_iff_glued _ _).1 h 0
  have h3 := bloch_frameSrc hg (fun _ => (1 : Lightlike.SU2)) 0
  have h2 := congrFun (h3.symm.trans h0) 2
  simp [frameTgt, bloch_one] at h2
  norm_num at h2

/-- Trust check: parity is not the identity away from `SU(2)`. For the boost
`diag(2, 1/2)` it is `diag(1/2, 2)`. -/
example : parityMap (Lightlike.Lorentz.SL2C.diagSL 2 two_ne_zero) ≠
    Lightlike.Lorentz.SL2C.diagSL 2 two_ne_zero := by
  intro h
  have h0 := congrArg (fun Y : SL2C => (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  simp [parityMap, Lightlike.Lorentz.SL2C.diagSL, Lightlike.Lorentz.SL2C.mk, map_ofNat] at h0
  norm_num at h0

end Lightlike.Asymptotics.Lorentzian
