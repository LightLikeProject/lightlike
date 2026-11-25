import Mathlib
import Lightlike.Canonical.PolymerEvolution.Evolution

/-!
# Semiboundedness of the `μ̄` evolution operator

Row G2-017 (milestone CA7).  If the coefficients satisfy `a ≥ 0` and `a(v) + a(v - h) - C ≤ c(v)`
(for the Ashtekar–Pawlowski–Singh model the constant is `C = 16`), then the operator
`Θ = diffOp h a c` is bounded below by `-C` on its domain:
`⟨ψ, Θ ψ⟩ ≥ -C ‖ψ‖²`.  This is the hypothesis of the semibounded self-adjointness criterion of
`Criterion.lean`.

## Main statement

* `diffOp_semibounded`: `-C ‖ψ‖² ≤ Re ⟨ψ, Θ ψ⟩` for `ψ` in the domain.

The proof is the discrete "ground state" argument: `Re ⟨ψ, Θ ψ⟩ = Σ_v [c(v)|ψ(v)|² - 2 a(v) Re(ψ̄(v) ψ(v+h))]`,
then `2 Re(ψ̄(v)ψ(v+h)) ≤ |ψ(v)|² + |ψ(v+h)|²` and a reindexing `v ↦ v + h` of the sums
(all sums have finite support).

References: Ashtekar–Pawlowski–Singh 2006 (`aps-2006`), Kamiński–Lewandowski 2008
(`kaminski-lewandowski-2008`).
-/

open scoped InnerProductSpace

namespace Lightlike.Rows.G2_017

noncomputable section

/-- A real function on `ℝ` that vanishes wherever `ψ` vanishes at `v - h`, `v`, `v + h` is summable
when `ψ` has finite support. -/
theorem summable_of_zero_triple (h : ℝ) {ψ : ℝ → ℂ} (hψ : {v : ℝ | ψ v ≠ 0}.Finite) (f : ℝ → ℝ)
    (hf : ∀ v, ψ (v - h) = 0 → ψ v = 0 → ψ (v + h) = 0 → f v = 0) : Summable f := by
  have h1 : {v : ℝ | ψ (v - h) ≠ 0}.Finite :=
    hψ.preimage (f := fun v => v - h) (fun x _ y _ e => by simpa using e)
  have h2 : {v : ℝ | ψ (v + h) ≠ 0}.Finite :=
    hψ.preimage (f := fun v => v + h) (fun x _ y _ e => by simpa using e)
  have hT := h1.union (hψ.union h2)
  refine summable_of_ne_finset_zero (s := hT.toFinset) ?_
  intro v hv
  by_contra hne
  apply hv
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq]
  by_contra hn
  simp only [not_or, not_not] at hn
  exact hne (hf v hn.1 hn.2.1 hn.2.2)

/-- **Semiboundedness of `Θ`**: if `0 ≤ a` and `a(v) + a(v - h) - C ≤ c(v)` for all `v`, then
`-C ‖ψ‖² ≤ Re ⟨ψ, Θ ψ⟩` for every `ψ` in the domain of finite linear combinations of kets. -/
theorem diffOp_semibounded (h : ℝ) (a c : ℝ → ℝ) (C : ℝ) (ha : ∀ v, 0 ≤ a v)
    (hc : ∀ v, a v + a (v - h) - C ≤ c v) (x : (diffOp h a c).domain) :
    -C * ‖(x : PolymerSpace)‖ ^ 2 ≤ (⟪(x : PolymerSpace), diffOp h a c x⟫_ℂ).re := by
  set ψ : PolymerSpace := (x : PolymerSpace) with hψdef
  have hfin : {v : ℝ | ψ v ≠ 0}.Finite := finite_support_of_mem_polymerDomain x.2
  -- notation
  set r : ℝ → ℝ := fun v => ‖ψ v‖ ^ 2 with hr
  set q : ℝ → ℝ := fun v => ((starRingEnd ℂ) (ψ v) * ψ (v + h)).re with hq
  set F : ℝ → ℝ := fun v => (⟪ψ v, (diffOp h a c x) v⟫_ℂ).re with hF
  have hFsum : HasSum F (⟪ψ, diffOp h a c x⟫_ℂ).re :=
    Complex.hasSum_re (lp.hasSum_inner ψ (diffOp h a c x))
  have hrsum : HasSum r (‖ψ‖ ^ 2) := by
    have := lp.hasSum_norm (p := 2) (by simp) ψ
    simpa using this
  have hFeq : ∀ v, F v = c v * r v - a v * q v - a (v - h) * q (v - h) := by
    intro v
    simp only [hF, hr, hq, diffOp_apply, sub_add_cancel]
    simp only [RCLike.inner_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply]
    ring
  have hr0 : ∀ v, ψ v = 0 → r v = 0 := fun v e => by simp [hr, e]
  have hq0 : ∀ v, ψ v = 0 → q v = 0 := fun v e => by simp [hq, e]
  have hq1 : ∀ v, ψ (v + h) = 0 → q v = 0 := fun v e => by simp [hq, e]
  -- the three nonnegative/auxiliary sequences
  set E1 : ℝ → ℝ := fun v => a v * (r v - q v) with hE1
  set E2 : ℝ → ℝ := fun v => a (v - h) * (r v - q (v - h)) with hE2
  set E3 : ℝ → ℝ := fun w => a w * (r (w + h) - q w) with hE3
  have hE2E3 : ∀ v, E2 v = E3 (v - h) := fun v => by simp [hE2, hE3]
  have s1 : Summable E1 := summable_of_zero_triple h hfin E1 fun v _ e0 e1 => by
    simp [hE1, hr0 v e0, hq0 v e0]
  have s3 : Summable E3 := summable_of_zero_triple h hfin E3 fun v _ e0 e1 => by
    simp [hE3, hr0 _ e1, hq0 v e0]
  have s2 : Summable E2 := by
    have : E2 = fun v => E3 (v - h) := funext hE2E3
    rw [this]
    exact (Equiv.summable_iff (Equiv.subRight h)).mpr s3
  have hsum23 : ∑' v, E2 v = ∑' v, E3 v := by
    have : E2 = fun v => E3 (v - h) := funext hE2E3
    rw [this]
    exact (Equiv.subRight h).tsum_eq E3
  have hnn : 0 ≤ ∑' v, E1 v + ∑' v, E2 v := by
    rw [hsum23, ← s1.tsum_add s3]
    refine tsum_nonneg fun v => ?_
    simp only [hE1, hE3, hr, hq]
    have := ha v
    have key : 2 * ((starRingEnd ℂ) (ψ v) * ψ (v + h)).re ≤ ‖ψ v‖ ^ 2 + ‖ψ (v + h)‖ ^ 2 := by
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
        Complex.normSq_apply]
      nlinarith [sq_nonneg ((ψ v).re - (ψ (v + h)).re), sq_nonneg ((ψ v).im - (ψ (v + h)).im)]
    nlinarith
  have hD : HasSum (fun v => F v + C * r v) ((⟪ψ, diffOp h a c x⟫_ℂ).re + C * ‖ψ‖ ^ 2) :=
    hFsum.add (hrsum.mul_left C)
  have hE12 : HasSum (fun v => E1 v + E2 v) (∑' v, E1 v + ∑' v, E2 v) :=
    s1.hasSum.add s2.hasSum
  have hpt : ∀ v, E1 v + E2 v ≤ F v + C * r v := by
    intro v
    rw [hFeq v]
    have e1 : (c v + C - a v - a (v - h)) * r v ≥ 0 := by
      have := hc v
      have : 0 ≤ r v := by simp only [hr]; positivity
      nlinarith
    simp only [hE1, hE2]
    nlinarith
  have hle := hasSum_le hpt hE12 hD
  linarith

end

end Lightlike.Rows.G2_017
