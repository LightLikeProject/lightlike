module

public import Mathlib

/-!
# A function with zero weak derivative on an interval is constant

**Lemma of du Bois-Reymond**: if `ψ` is locally integrable on an open interval `U` (bounded or
not) and `∫ g' ψ = 0` for every smooth `g` with compact support in `U`, then `ψ` is almost
everywhere equal on `U` to a constant (`exists_ae_eq_const_of_weak_deriv_zero`).  The proof fixes a normalised bump `g₀`; for a
test function `h`, the function `h − (∫ h) g₀` has integral `0`, so it is the derivative of a test
function, and `∫ h (ψ − c) = 0` for `c = ∫ g₀ ψ`; the fundamental lemma of the calculus of
variations (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) ends the proof.  The library's
`Lightlike.OperatorAlgebras.weak_const` is the case `U = (0, 1)` for an integrable `ψ`; the ladder
equations need `U = (0, ∞)` and a function that is only locally integrable.  Mathlib has the
fundamental lemma but not this one.  Used for the
completeness of the ladder images (layer 2c-iv of the Plancherel formula on `SL(2,ℝ)`, milestone
HA3).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- A test function supported in an open set times a locally integrable function is integrable. -/
lemma integrable_smul_of_tsupport_subset {U : Set ℝ} {ψ : ℝ → ℂ} (hψ : LocallyIntegrableOn ψ U)
    {h : ℝ → ℝ} (hh : Continuous h) (hc : HasCompactSupport h) (hsub : tsupport h ⊆ U) :
    Integrable (fun x => h x • ψ x) := by
  have h1 : IntegrableOn ψ (tsupport h) := hψ.integrableOn_compact_subset hsub hc.isCompact
  have h2 : IntegrableOn (fun x => h x • ψ x) (tsupport h) :=
    h1.continuousOn_smul hh.continuousOn hc.isCompact
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h2
  intro x hx
  by_contra hn
  apply hx
  simp [image_eq_zero_of_notMem_tsupport hn]

/-- A nonempty compact set of reals lies in `[s₀, s₁]` for two of its points `s₀ ≤ s₁`. -/
lemma exists_Icc_of_isCompact {S : Set ℝ} (hS : IsCompact S) (hne : S.Nonempty) :
    ∃ s₀ ∈ S, ∃ s₁ ∈ S, s₀ ≤ s₁ ∧ S ⊆ Icc s₀ s₁ := by
  obtain ⟨s₀, hs₀, hmin⟩ := hS.exists_isMinOn hne continuous_id.continuousOn
  obtain ⟨s₁, hs₁, hmax⟩ := hS.exists_isMaxOn hne continuous_id.continuousOn
  exact ⟨s₀, hs₀, s₁, hs₁, hmin hs₀ |>.trans (hmax hs₀), fun x hx => ⟨hmin hx, hmax hx⟩⟩

/-- A smooth function vanishing outside `[s₀, s₁]` with integral `0` is the derivative of a
smooth function vanishing outside `[s₀, s₁]`. -/
lemma exists_primitive_of_integral_eq_zero {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁) (hks : ∀ x, x ∉ Icc s₀ s₁ → k x = 0)
    (hint : ∫ x, k x = 0) :
    ∃ K : ℝ → ℝ, ContDiff ℝ ∞ K ∧ HasCompactSupport K ∧ tsupport K ⊆ Icc s₀ s₁ ∧
      ∀ x, deriv K x = k x := by
  have hkc : Continuous k := hk.continuous
  set K : ℝ → ℝ := fun x => ∫ t in (s₀ - 1)..x, k t with hK
  have hder : ∀ x, HasDerivAt K (k x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hkc.intervalIntegrable _ _)
      (hkc.stronglyMeasurableAtFilter _ _) hkc.continuousAt
  have hdK : deriv K = k := funext fun x => (hder x).deriv
  have hdiff : Differentiable ℝ K := fun x => (hder x).differentiableAt
  have hsmooth : ContDiff ℝ ∞ K := contDiff_infty_iff_deriv.mpr ⟨hdiff, hdK ▸ hk⟩
  -- `K` vanishes left of `s₀`
  have hleft : ∀ x, x < s₀ → K x = 0 := by
    intro x hx
    simp only [hK]
    refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun t ht => ?_)
    apply hks
    intro hmem
    rcases le_total (s₀ - 1) x with h | h
    · rw [uIoc_of_le h] at ht; linarith [ht.2, hmem.1]
    · rw [uIoc_of_ge h] at ht; linarith [ht.2, hmem.1]
  -- `K` vanishes right of `s₁`
  have hright : ∀ x, s₁ < x → K x = 0 := by
    intro x hx
    have hax : s₀ - 1 ≤ x := by linarith
    simp only [hK]
    rw [intervalIntegral.integral_of_le hax, ← hint]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => hks t ?_
    intro hmem
    apply ht
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hsupp : ∀ x, x ∉ Icc s₀ s₁ → K x = 0 := by
    intro x hx
    rcases not_and_or.mp hx with h | h
    · exact hleft x (not_le.mp h)
    · exact hright x (not_le.mp h)
  refine ⟨K, hsmooth, HasCompactSupport.intro isCompact_Icc hsupp, ?_, fun x => by rw [hdK]⟩
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hn
  exact hx (hsupp x hn)

/-- **Lemma of du Bois-Reymond**: a locally integrable function on an open interval `U` (an open,
order-connected, nonempty set of reals, e.g. `(a, b)` or `(a, ∞)`) whose weak derivative vanishes
is almost everywhere constant on `U`. -/
theorem exists_ae_eq_const_of_weak_deriv_zero {U : Set ℝ} (hU : IsOpen U) (hUc : U.OrdConnected)
    (hUne : U.Nonempty) {ψ : ℝ → ℂ} (hψ : LocallyIntegrableOn ψ U)
    (h : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, deriv g x • ψ x = 0) :
    ∃ c : ℂ, ∀ᵐ x, x ∈ U → ψ x = c := by
  -- a normalised bump in `U`
  obtain ⟨m, hm⟩ := hUne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU m hm
  let β : ContDiffBump m := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  set g₀ : ℝ → ℝ := β.normed volume with hg₀
  have hg₀s : ContDiff ℝ ∞ g₀ := β.contDiff_normed
  have hg₀c : HasCompactSupport g₀ := β.hasCompactSupport_normed
  have hg₀sub : tsupport g₀ ⊆ U := by
    rw [hg₀, β.tsupport_normed_eq]
    exact (Metric.closedBall_subset_ball (by simp only [β]; linarith)).trans hball
  have hg₀int : ∫ x, g₀ x = 1 := β.integral_normed
  set c : ℂ := ∫ x, g₀ x • ψ x with hc
  refine ⟨c, ?_⟩
  have hf : LocallyIntegrableOn (fun x => ψ x - c) U :=
    hψ.sub (locallyIntegrableOn_const c)
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hf ?_
  · filter_upwards [key] with x hx hmem
    exact sub_eq_zero.mp (hx hmem)
  intro g hg hgc hgsub
  set I : ℝ := ∫ x, g x with hI
  set k : ℝ → ℝ := fun x => g x - I * g₀ x with hk
  have hks : ContDiff ℝ ∞ k := hg.sub (contDiff_const.mul hg₀s)
  have hSc : IsCompact (tsupport g ∪ tsupport g₀) := hgc.isCompact.union hg₀c.isCompact
  have hSne : (tsupport g ∪ tsupport g₀).Nonempty := by
    refine ⟨m, Or.inr ?_⟩
    rw [hg₀, β.tsupport_normed_eq]
    exact Metric.mem_closedBall_self (by simp only [β]; linarith)
  obtain ⟨s₀, hs₀, s₁, hs₁, hs, hS⟩ := exists_Icc_of_isCompact hSc hSne
  have hIcc : Icc s₀ s₁ ⊆ U :=
    hUc.out (union_subset hgsub hg₀sub hs₀) (union_subset hgsub hg₀sub hs₁)
  have hk0 : ∀ x, x ∉ Icc s₀ s₁ → k x = 0 := by
    intro x hx
    have h1 : x ∉ tsupport g := fun h' => hx (hS (Or.inl h'))
    have h2 : x ∉ tsupport g₀ := fun h' => hx (hS (Or.inr h'))
    simp [hk, image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hg₀i : Integrable g₀ := hg₀s.continuous.integrable_of_hasCompactSupport hg₀c
  have hkint : ∫ x, k x = 0 := by
    simp only [hk]
    rw [integral_sub hgint (hg₀i.const_mul I), integral_const_mul, hg₀int, mul_one, sub_self]
  obtain ⟨K, hKs, hKc, hKsub, hKd⟩ := exists_primitive_of_integral_eq_zero hks hs hk0 hkint
  have hzero := h K hKs hKc (hKsub.trans hIcc)
  simp only [hKd] at hzero
  have hi1 := integrable_smul_of_tsupport_subset hψ hg.continuous hgc hgsub
  have hi2 := integrable_smul_of_tsupport_subset hψ hg₀s.continuous hg₀c hg₀sub
  have hi3 : Integrable (fun x => I • (g₀ x • ψ x)) := hi2.smul I
  have hsplit : ∫ x, k x • ψ x = (∫ x, g x • ψ x) - I • c := by
    simp only [hk, sub_smul, mul_smul]
    rw [integral_sub hi1 hi3, integral_smul]
  rw [hsplit, sub_eq_zero] at hzero
  have hconst : ∫ x, g x • c = I • c := by
    rw [integral_smul_const]
  simp only [smul_sub]
  rw [integral_sub hi1 (hgint.smul_const c), hzero, hconst, sub_self]

end Lightlike.Lorentz.SL2RPlancherel
