import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.DiscreteBoundary

/-!
# The principal-series coefficients are orthogonal to the discrete directions

For the opposite-sign block `(l, -s)` and its discrete directions `φ_i` (`l - s ≤ i < l`),
`∫_{(0,∞)} φ_i conj Φ^ν_{s,l} sinh = 0` for every real `ν` (`integral_phiN_mul_conj_mcoefP_eq_zero`).
The radial Casimir is symmetric (`integral_casimir_phiN_mcoefP_eq_zero`), `Φ^ν_{s,l}` is an
eigenfunction with eigenvalue `-w(w + 1) = (ν² + 1)/4 > 0`, and the Casimir acts triangularly on the
`φ_i` with diagonal entries `-(l - i)(l - i - 1) ≤ 0`, so the pairings vanish by induction on `i`.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma neg_wP_mul_wP_add_one (ν : ℝ) : -(wP ν * (wP ν + 1)) = (((ν ^ 2 + 1) / 4 : ℝ) : ℂ) := by
  rw [wP]
  push_cast
  linear_combination (-(ν : ℂ) ^ 2 / 4) * Complex.I_sq

lemma phiN_div_cosh_sub_one (s l i : ℕ) (hi : 1 ≤ i) {x : ℝ} (hx : 0 < x) :
    phiN s l i x / (Real.cosh x - 1) = phiN s l (i - 1) x := by
  have hc1 : Real.cosh x - 1 ≠ 0 := (sub_pos.2 (Real.one_lt_cosh.2 hx.ne')).ne'
  have he : i + s = (i - 1 + s) + 1 := by omega
  rw [phiN, phiN, he, pow_succ]
  field_simp

/-- **Orthogonality to the discrete directions**: `∫_{(0,∞)} φ_i conj Φ^ν_{s,l} sinh = 0` for
`l - s ≤ i < l`. -/
theorem integral_phiN_mul_conj_mcoefP_eq_zero (ν : ℝ) (s l : ℕ) :
    ∀ i : ℕ, l ≤ i + s → i < l →
      ∫ x in Ioi 0, ((phiN s l i x : ℝ) : ℂ) * (starRingEnd ℂ) (mcoefP ν s l x) *
        (Real.sinh x : ℂ) = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hli hil
  set lam : ℝ := -(((l : ℝ) - i) * ((l : ℝ) - i - 1)) with hlam
  set c : ℝ := 2 * i * ((i : ℝ) - l + s) with hc
  set q : ℝ := (ν ^ 2 + 1) / 4 with hq
  have hil' : (1 : ℝ) ≤ (l : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ l := by exact_mod_cast hil
    linarith
  have hne : ((lam : ℝ) : ℂ) - (q : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    have : lam - q < 0 := by
      have h1 : 0 ≤ ((l : ℝ) - i) * ((l : ℝ) - i - 1) := by nlinarith
      have h2 : 0 < q := by rw [hq]; positivity
      linarith
    exact_mod_cast this.ne
  have hg : ∀ j : ℕ, l ≤ j + s → j < l → IntegrableOn (fun x => ((phiN s l j x : ℝ) : ℂ) *
      (starRingEnd ℂ) (mcoefP ν s l x) * (Real.sinh x : ℂ)) (Ioi 0) := fun j h1 h2 =>
    integrableOn_phiN_mul_conj_mcoefP ν s l s l j h1 h2
  -- the symmetric Casimir integrand, pointwise
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      (radialCasimir l (-(s : ℝ)) (fun t => ((phiN s l i t : ℝ) : ℂ)) x *
        (starRingEnd ℂ) (mcoefP ν s l x) - ((phiN s l i x : ℝ) : ℂ) *
          (starRingEnd ℂ) (radialCasimir l (-(s : ℝ)) (mcoefP ν s l) x)) * (Real.sinh x : ℂ) =
      ((lam : ℂ) - q) * (((phiN s l i x : ℝ) : ℂ) * (starRingEnd ℂ) (mcoefP ν s l x) *
        (Real.sinh x : ℂ)) - (c : ℂ) * (((phiN s l i x / (Real.cosh x - 1) : ℝ) : ℂ) *
          (starRingEnd ℂ) (mcoefP ν s l x) * (Real.sinh x : ℂ)) := by
    intro x hx
    have hL := radialCasimir_mcoefP ν (s : ℤ) (l : ℤ) hx
    simp only [Int.cast_natCast] at hL
    rw [radialCasimir_phiN s l i hx, hL, neg_wP_mul_wP_add_one, map_mul, Complex.conj_ofReal,
      ← hlam, ← hc, ← hq]
    push_cast
    ring
  by_cases hc0 : c = 0
  · -- no lower term
    have hf : IntegrableOn (fun x => (radialCasimir l (-(s : ℝ)) (fun t => ((phiN s l i t : ℝ) : ℂ)) x *
        (starRingEnd ℂ) (mcoefP ν s l x) - ((phiN s l i x : ℝ) : ℂ) *
          (starRingEnd ℂ) (radialCasimir l (-(s : ℝ)) (mcoefP ν s l) x)) * (Real.sinh x : ℂ))
        (Ioi 0) :=
      (show IntegrableOn _ (Ioi (0 : ℝ)) volume from
        (hg i hli hil).const_mul ((lam : ℂ) - q)).congr_fun (fun x hx => by
          rw [hpt x hx, hc0]; simp) measurableSet_Ioi
    have h0 := integral_casimir_phiN_mcoefP_eq_zero s l i hli hil ν s l (-(s : ℝ)) hf
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, hc0] at h0
    simp only [Complex.ofReal_zero, zero_mul, sub_zero] at h0
    rw [integral_const_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left hne
  · -- the lower term is the previous direction
    have hi1 : 1 ≤ i := by
      by_contra h
      push Not at h
      have : i = 0 := by omega
      exact hc0 (by rw [hc, this]; simp)
    have hli1 : l ≤ (i - 1) + s := by
      by_contra h
      push Not at h
      have h' : i + s = l := by omega
      have h'' : (i : ℝ) + s = l := by exact_mod_cast h'
      exact hc0 (by rw [hc, show (i : ℝ) - l + s = 0 by linarith, mul_zero])
    have hprev := ih (i - 1) (by omega) hli1 (by omega)
    have hpt2 : ∀ x ∈ Ioi (0 : ℝ),
        (radialCasimir l (-(s : ℝ)) (fun t => ((phiN s l i t : ℝ) : ℂ)) x *
          (starRingEnd ℂ) (mcoefP ν s l x) - ((phiN s l i x : ℝ) : ℂ) *
            (starRingEnd ℂ) (radialCasimir l (-(s : ℝ)) (mcoefP ν s l) x)) * (Real.sinh x : ℂ) =
        ((lam : ℂ) - q) * (((phiN s l i x : ℝ) : ℂ) * (starRingEnd ℂ) (mcoefP ν s l x) *
          (Real.sinh x : ℂ)) - (c : ℂ) * (((phiN s l (i - 1) x : ℝ) : ℂ) *
            (starRingEnd ℂ) (mcoefP ν s l x) * (Real.sinh x : ℂ)) := fun x hx => by
      rw [hpt x hx, phiN_div_cosh_sub_one s l i hi1 hx]
    have hint := ((hg i hli hil).const_mul ((lam : ℂ) - q)).sub
      ((hg (i - 1) hli1 (by omega)).const_mul (c : ℂ))
    have hf := (show IntegrableOn _ (Ioi (0 : ℝ)) volume from hint).congr_fun
      (fun x hx => (hpt2 x hx).symm) measurableSet_Ioi
    have h0 := integral_casimir_phiN_mcoefP_eq_zero s l i hli hil ν s l (-(s : ℝ)) hf
    rw [setIntegral_congr_fun measurableSet_Ioi hpt2,
      integral_sub ((hg i hli hil).const_mul _) ((hg (i - 1) hli1 (by omega)).const_mul _),
      integral_const_mul, integral_const_mul, hprev, mul_zero, sub_zero] at h0
    exact (mul_eq_zero.1 h0).resolve_left hne

end Lightlike.Lorentz.SL2RPlancherel
