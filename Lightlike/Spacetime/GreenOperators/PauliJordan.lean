import Mathlib
import Lightlike.Spacetime.GreenOperators.GreenIdentities

/-!
# The Pauli–Jordan operator `E = G⁺ - G⁻` on `1+1` Minkowski space, any mass

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
`pauliJordan m f = massiveSol m f - massiveAdvancedSol m f` is the difference of the retarded and
advanced Green operators.  We prove that it solves the Klein–Gordon equation
(`kgOp_pauliJordan`), that it kills the image of the Klein–Gordon operator on test functions
(`pauliJordan_kgOp`, one half of the BGP exact sequence `0 → C_c^∞ → C_c^∞ → C_sc^∞ → C_sc^∞`),
and that its support is spacelike compact in the sense that `E f p ≠ 0` forces `p` to be causally
related to a point of `{f ≠ 0}` (`pauliJordan_ne_zero`).

This is a supporting result; no catalogue entry.
-/

namespace Lightlike.GreenOperators

/-- The Pauli–Jordan (causal propagator) operator `E = G⁺ - G⁻` for mass `m` on `1+1` Minkowski
space. -/
noncomputable def pauliJordan (m : ℝ) (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  massiveSol m f - massiveAdvancedSol m f

lemma pauliJordan_apply (m : ℝ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    pauliJordan m f p = massiveSol m f p - massiveAdvancedSol m f p := rfl

/-- `E f` is `C²` for `f` of class `C²` with compact support. -/
lemma pauliJordan_contDiff (m : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ContDiff ℝ 2 (pauliJordan m f) :=
  (massiveSol_contDiff m hf hc).sub (massiveAdvancedSol_contDiff m hf hc)

/-- `E f` is a solution of the homogeneous Klein–Gordon equation. -/
theorem kgOp_pauliJordan (m : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (p : ℝ × ℝ) : kgOp m (pauliJordan m f) p = 0 := by
  unfold pauliJordan
  rw [kgOp_sub m (massiveSol_contDiff m hf hc) (massiveAdvancedSol_contDiff m hf hc),
    kgOp_massiveSol m hf hc, kgOp_massiveAdvancedSol m hf hc, sub_self]

/-- `E P = 0` on test functions: the Pauli–Jordan operator kills `kgOp m g` for `g` of class `C⁴`
with compact support. -/
theorem pauliJordan_kgOp (m : ℝ) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 4 g) (hc : HasCompactSupport g) :
    pauliJordan m (kgOp m g) = 0 := by
  unfold pauliJordan
  rw [massiveSol_kgOp m hg hc, massiveAdvancedSol_kgOp m hg hc, sub_self]

/-- **Spacelike-compact support of `E f`**: if `E f` is nonzero at `p`, then `f` is nonzero at some
point causally related to `p` (in the past or the future). -/
theorem pauliJordan_ne_zero {m : ℝ} {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (h : pauliJordan m f p ≠ 0) :
    ∃ q, f q ≠ 0 ∧ (causalLE2 q p ∨ causalLE2 p q) := by
  by_cases h1 : massiveSol m f p = 0
  · have h2 : massiveAdvancedSol m f p ≠ 0 := by
      intro h2
      apply h
      rw [pauliJordan_apply, h1, h2, sub_zero]
    obtain ⟨q, hq, hc⟩ := massiveAdvancedSol_ne_zero h2
    exact ⟨q, hq, Or.inr hc⟩
  · obtain ⟨q, hq, hc⟩ := massiveSol_ne_zero h1
    exact ⟨q, hq, Or.inl hc⟩

/-- `E f` vanishes at every point not causally related to a point of `{f ≠ 0}`. -/
theorem pauliJordan_eq_zero {m : ℝ} {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (h : ∀ q, f q ≠ 0 → ¬ causalLE2 q p ∧ ¬ causalLE2 p q) : pauliJordan m f p = 0 := by
  by_contra hne
  obtain ⟨q, hq, hc⟩ := pauliJordan_ne_zero hne
  rcases hc with hc | hc
  · exact (h q hq).1 hc
  · exact (h q hq).2 hc

end Lightlike.GreenOperators
