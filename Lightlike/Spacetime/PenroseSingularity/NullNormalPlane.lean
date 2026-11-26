import Lightlike.Spacetime.PenroseSingularity.NullNormalAlg
import Lightlike.Spacetime.Lorentzian
import Lightlike.Spacetime.CausalLadder.ConeAlgebra

/-!
# The plane data of a spacelike codimension-two surface at a point (G1-012, step D2)

At a point of `S = f⁻¹(0)` with `df` surjective and `ker df` spacelike for a Lorentzian form `B`, the
metric duals `N₁, N₂` of the two components of `df` span a Lorentzian plane (`PlaneData`).
-/

open Lightlike

noncomputable section

namespace Lightlike.Penrose.NullNormal

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V]

/-- A Lorentzian form has a linear functional (a time coordinate) whose kernel is spacelike for it. -/
theorem IsLorentzianForm.exists_functional {n : ℕ} {B : V →L[ℝ] V →L[ℝ] ℝ}
    (h : IsLorentzianForm n B) {τ : V} (hτ : B τ τ < 0) :
    ∃ φ : V →ₗ[ℝ] ℝ, ∀ v, φ v = 0 → 0 ≤ B v v := by
  obtain ⟨e, he⟩ := h
  have hn : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h0
    subst hn0
    have : τ = 0 := e.ext_elem fun i => i.elim0
    rw [this] at hτ
    simp at hτ
  refine ⟨(Finsupp.lapply (⟨0, hn⟩ : Fin n)).comp e.repr.toLinearMap, fun v hv => ?_⟩
  rw [IsLorentzianForm.apply_eq_sum e he]
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases hi : (i : ℕ) = 0
  · have : i = ⟨0, hn⟩ := Fin.ext hi
    subst this
    have h0 : e.repr v ⟨0, hn⟩ = 0 := hv
    simp [h0]
  · have : etaDiag i = 1 := by simp [etaDiag, hi]
    rw [this]
    nlinarith [sq_nonneg (e.repr v i)]

/-- **The plane data at a point.** -/
theorem planeData_of_df {n : ℕ} {B : V →L[ℝ] V →L[ℝ] ℝ} (hL : IsLorentzianForm n B)
    (Df : V →L[ℝ] (Fin 2 → ℝ)) (hDf : Function.Surjective Df) (N1 N2 : V)
    (hN1 : ∀ v, B N1 v = Df v 0) (hN2 : ∀ v, B N2 v = Df v 1)
    (hsp : ∀ v, Df v = 0 → v ≠ 0 → 0 < B v v) {τ : V} (hτ : B τ τ < 0) :
    PlaneData B.toBilinForm N1 N2 τ := by
  refine ⟨fun v w => hL.symm v w, ?_, ?_, ?_, hτ⟩
  · intro a b hab
    obtain ⟨v1, hv1⟩ := hDf (Pi.single 0 1)
    obtain ⟨v2, hv2⟩ := hDf (Pi.single 1 1)
    have h1 := hab v1
    have h2 := hab v2
    simp only [ContinuousLinearMap.toBilinForm_apply] at h1 h2
    rw [hN1, hN2, hv1] at h1
    rw [hN1, hN2, hv2] at h2
    simp at h1 h2
    exact ⟨h1, h2⟩
  · intro v h1 h2 hv
    simp only [ContinuousLinearMap.toBilinForm_apply] at h1 h2 ⊢
    rw [hN1] at h1
    rw [hN2] at h2
    refine hsp v ?_ hv
    funext i
    fin_cases i
    · exact h1
    · exact h2
  · exact IsLorentzianForm.exists_functional hL hτ

/-- **A null vector in the future cone of one future timelike vector is in the future cone of every
co-oriented one**: if `B(u, T) < 0` for timelike `u, T`, and `ν` is null with `B(ν, u) < 0`, then
`B(ν, T) < 0`. -/
theorem null_neg_of_coorient {n : ℕ} {B : V →L[ℝ] V →L[ℝ] ℝ} (hL : IsLorentzianForm n B)
    {u T ν : V} (hu : B u u < 0) (hT : B T T < 0) (huT : B u T < 0) (hν : B ν ν = 0)
    (hνu : B ν u < 0) : B ν T < 0 := by
  by_contra hcon
  have hβ : 0 ≤ B ν T := not_lt.1 hcon
  set α := B ν u with hα
  set β := B ν T with hβdef
  set t : ℝ := -α / (β - α) with ht
  have hden : 0 < β - α := by linarith
  have ht0 : 0 < t := div_pos (by linarith) hden
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith
  set w : V := (1 - t) • u + t • T with hw
  have hBw : B ν w = 0 := by
    simp only [hw, map_add, map_smul, smul_eq_mul]
    rw [← hα, ← hβdef, ht]
    field_simp
    ring
  have hTu : B T u = B u T := Lightlike.IsLorentzianForm.symm hL T u
  have hww : B w w < 0 := by
    simp only [hw, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rw [hTu]
    have h1 : 0 ≤ (1 - t) := by linarith
    nlinarith [mul_nonneg h1 h1, mul_nonneg h1 ht0.le, mul_pos ht0 ht0,
      mul_nonneg (mul_nonneg h1 ht0.le) (neg_nonneg.2 huT.le)]
  have hνw : B ν w = 0 := hBw
  have h0 := hL.eq_zero_of_orthogonal_timelike (X := w) (w := ν) hww
    hνw (by rw [hν])
  have h00 : α = 0 := by rw [hα, h0]; simp
  linarith

end Lightlike.Penrose.NullNormal
