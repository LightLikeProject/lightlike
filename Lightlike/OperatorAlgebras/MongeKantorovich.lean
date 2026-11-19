import Lightlike.OperatorAlgebras.Wasserstein
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Monge-Kantorovich duality on a compact metric space

For Borel probability measures `μ`, `ν` on a compact metric space `X` and a continuous cost `h` on `X × X`, there is an
optimal coupling `σ`, and its cost is the dual value:
`min_{π ∈ Π(μ, ν)} ∫ h dπ = sup {∫ f dμ + ∫ g dν | f, g ∈ C(X), f(x) + g(y) ≤ h(x, y)}`.
This is the duality that W. Huang, R. Wang, Y. Wu, D. Meng, arXiv:2610.21070, Section 8.1, (8.1), p. 46 (read) use on a
finite grid; the proof here goes through the Hahn-Banach theorem and the Riesz-Markov-Kakutani theorem.

* `upper μ ν k`, `omega μ ν k = inf {μ f + ν g | k ≤ f ⊕ g}`, a sublinear functional on `C(X × X)` dominating every
  coupling (`integral_le_omega`);
* `exists_linear_le_omega` (Hahn-Banach), `exists_coupling_eq_omega`: a coupling `σ` with `∫ k dσ = ω(k)`, the Riesz
  measure of the extension, whose marginals are `μ` and `ν` (`eq_integral_fst`, `eq_integral_snd`);
* `exists_optimal_coupling`, `integral_optimal_eq_sSup`: the duality, with an optimal coupling.
-/

open MeasureTheory
open scoped Pointwise CompactlySupported

namespace Lightlike.OperatorAlgebras.Transport

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
/-- The first coordinate `X × X → X` as a continuous map. -/
def fstC : C(X × X, X) := ⟨Prod.fst, continuous_fst⟩

/-- The second coordinate `X × X → X` as a continuous map. -/
def sndC : C(X × X, X) := ⟨Prod.snd, continuous_snd⟩

variable (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The values `∫ f dμ + ∫ g dν` over the continuous `f`, `g` with `k ≤ f ⊕ g`. -/
def upper (k : C(X × X, ℝ)) : Set ℝ :=
  {r | ∃ f g : C(X, ℝ), (∀ p : X × X, k p ≤ f p.1 + g p.2) ∧ r = ∫ x, f x ∂μ + ∫ x, g x ∂ν}

/-- **The dual functional** `ω(k) = inf {∫ f dμ + ∫ g dν | k ≤ f ⊕ g}`. -/
noncomputable def omega (k : C(X × X, ℝ)) : ℝ := sInf (upper μ ν k)

variable {μ ν}

lemma integrable_cont {m : Measure X} [IsFiniteMeasure m] (f : C(X, ℝ)) : Integrable f m :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Every coupling is below every dual value: `∫ k dπ ≤ ∫ f dμ + ∫ g dν` when `k ≤ f ⊕ g`. -/
lemma integral_le_of_mem_upper {π : Measure (X × X)} (hπ : π ∈ couplings μ ν) {k : C(X × X, ℝ)} {r : ℝ}
    (hr : r ∈ upper μ ν k) : ∫ p, k p ∂π ≤ r := by
  have := hπ.1
  obtain ⟨f, g, hfg, rfl⟩ := hr
  rw [integral_comp_fst hπ.2.1 f f.continuous, integral_comp_snd hπ.2.2 g g.continuous,
    ← integral_add (integrable_of_continuous (f := fun p : X × X => f p.1) (f.continuous.comp continuous_fst))
      (integrable_of_continuous (f := fun p : X × X => g p.2) (g.continuous.comp continuous_snd))]
  exact integral_mono (integrable_of_continuous k.continuous)
    (integrable_of_continuous ((f.continuous.comp continuous_fst).add (g.continuous.comp continuous_snd))) hfg

variable (μ ν) in
lemma upper_nonempty (k : C(X × X, ℝ)) : (upper μ ν k).Nonempty :=
  ⟨_, ContinuousMap.const X ‖k‖, 0, fun p => by
    simp only [ContinuousMap.const_apply, ContinuousMap.zero_apply, add_zero]
    exact (le_abs_self _).trans (k.norm_coe_le_norm p), rfl⟩

variable (μ ν) in
lemma upper_bddBelow (k : C(X × X, ℝ)) : BddBelow (upper μ ν k) :=
  ⟨_, fun _ hr => integral_le_of_mem_upper (prod_mem_couplings μ ν) hr⟩

/-- **Every coupling is below `ω`**: `∫ k dπ ≤ ω(k)`. -/
theorem integral_le_omega {π : Measure (X × X)} (hπ : π ∈ couplings μ ν) (k : C(X × X, ℝ)) :
    ∫ p, k p ∂π ≤ omega μ ν k :=
  le_csInf (upper_nonempty μ ν k) fun _ hr => integral_le_of_mem_upper hπ hr

lemma omega_le_of_mem {k : C(X × X, ℝ)} {r : ℝ} (hr : r ∈ upper μ ν k) : omega μ ν k ≤ r :=
  csInf_le (upper_bddBelow μ ν k) hr

/-- `ω(k + k') ≤ ω(k) + ω(k')`. -/
lemma omega_add (k k' : C(X × X, ℝ)) : omega μ ν (k + k') ≤ omega μ ν k + omega μ ν k' := by
  have key : ∀ r ∈ upper μ ν k, ∀ r' ∈ upper μ ν k', omega μ ν (k + k') ≤ r + r' := by
    rintro _ ⟨f, g, hfg, rfl⟩ _ ⟨f', g', hfg', rfl⟩
    refine omega_le_of_mem ⟨f + f', g + g', fun p => ?_, ?_⟩
    · simp only [ContinuousMap.add_apply]; linarith [hfg p, hfg' p]
    · rw [show (⇑(f + f') : X → ℝ) = fun x => f x + f' x from rfl,
        show (⇑(g + g') : X → ℝ) = fun x => g x + g' x from rfl,
        integral_add (integrable_cont f) (integrable_cont f'), integral_add (integrable_cont g) (integrable_cont g')]
      ring
  have h1 : ∀ r' ∈ upper μ ν k', omega μ ν (k + k') - r' ≤ omega μ ν k := fun r' hr' =>
    le_csInf (upper_nonempty μ ν k) fun r hr => by linarith [key r hr r' hr']
  have h2 : omega μ ν (k + k') - omega μ ν k ≤ omega μ ν k' :=
    le_csInf (upper_nonempty μ ν k') fun r' hr' => by linarith [h1 r' hr']
  linarith

/-- `ω(c k) = c ω(k)` for `c > 0`. -/
lemma omega_smul {c : ℝ} (hc : 0 < c) (k : C(X × X, ℝ)) : omega μ ν (c • k) = c * omega μ ν k := by
  have hset : upper μ ν (c • k) = c • upper μ ν k := by
    ext r
    constructor
    · rintro ⟨f, g, hfg, rfl⟩
      refine ⟨_, ⟨c⁻¹ • f, c⁻¹ • g, fun p => ?_, rfl⟩, ?_⟩
      · have := hfg p
        simp only [ContinuousMap.smul_apply, smul_eq_mul] at this ⊢
        rw [← mul_add, le_inv_mul_iff₀ hc]; exact this
      · simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
        field_simp
    · rintro ⟨_, ⟨f, g, hfg, rfl⟩, rfl⟩
      refine ⟨c • f, c • g, fun p => ?_, ?_⟩
      · have := hfg p
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        nlinarith
      · simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
        ring
  rw [omega, hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul, omega]

/-- `ω(0) = 0`. -/
lemma omega_zero : omega μ ν 0 = 0 := by
  apply le_antisymm
  · exact omega_le_of_mem ⟨0, 0, fun p => by simp, by simp⟩
  · have := integral_le_omega (prod_mem_couplings μ ν) 0
    simpa using this

/-- `c ω(k) ≤ ω(c k)` for every real `c`. -/
lemma mul_omega_le (c : ℝ) (k : C(X × X, ℝ)) : c * omega μ ν k ≤ omega μ ν (c • k) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have h := omega_add (μ := μ) (ν := ν) (c • k) ((-c) • k)
    rw [← add_smul, add_neg_cancel, zero_smul, omega_zero, omega_smul (neg_pos.mpr hc)] at h
    linarith
  · rw [zero_mul, zero_smul, omega_zero]
  · rw [omega_smul hc]

/-- `ω(k) ≤ 0` for `k ≤ 0`. -/
lemma omega_nonpos {k : C(X × X, ℝ)} (hk : ∀ p, k p ≤ 0) : omega μ ν k ≤ 0 :=
  omega_le_of_mem ⟨0, 0, fun p => by simpa using hk p, by simp⟩

/-- `ω(f ∘ fst) ≤ ∫ f dμ`. -/
lemma omega_fst_le (f : C(X, ℝ)) :
    omega μ ν (f.comp fstC) ≤ ∫ x, f x ∂μ :=
  omega_le_of_mem ⟨f, 0, fun p => by simp [fstC], by simp⟩

/-- `ω(g ∘ snd) ≤ ∫ g dν`. -/
lemma omega_snd_le (g : C(X, ℝ)) :
    omega μ ν (g.comp sndC) ≤ ∫ x, g x ∂ν :=
  omega_le_of_mem ⟨0, g, fun p => by simp [sndC], by simp⟩

/-- A linear functional below `ω` takes `f ∘ fst` to `∫ f dμ`. -/
lemma eq_integral_fst {L : C(X × X, ℝ) →ₗ[ℝ] ℝ} (hL : ∀ k, L k ≤ omega μ ν k) (f : C(X, ℝ)) :
    L (f.comp fstC) = ∫ x, f x ∂μ := by
  apply le_antisymm ((hL _).trans (omega_fst_le f))
  have h := (hL ((-f).comp fstC)).trans (omega_fst_le (-f))
  rw [show (-f).comp fstC = -(f.comp fstC) from rfl, map_neg] at h
  simp only [ContinuousMap.neg_apply, integral_neg] at h
  linarith

/-- A linear functional below `ω` takes `g ∘ snd` to `∫ g dν`. -/
lemma eq_integral_snd {L : C(X × X, ℝ) →ₗ[ℝ] ℝ} (hL : ∀ k, L k ≤ omega μ ν k) (g : C(X, ℝ)) :
    L (g.comp sndC) = ∫ x, g x ∂ν := by
  apply le_antisymm ((hL _).trans (omega_snd_le g))
  have h := (hL ((-g).comp sndC)).trans (omega_snd_le (-g))
  rw [show (-g).comp sndC = -(g.comp sndC) from rfl, map_neg] at h
  simp only [ContinuousMap.neg_apply, integral_neg] at h
  linarith

/-- **Hahn-Banach for `ω`**: a linear functional `L ≤ ω` on `C(X × X)` with `L k₀ = ω(k₀)`. -/
lemma exists_linear_le_omega (k₀ : C(X × X, ℝ)) :
    ∃ L : C(X × X, ℝ) →ₗ[ℝ] ℝ, L k₀ = omega μ ν k₀ ∧ ∀ k, L k ≤ omega μ ν k := by
  have H : ∀ c : ℝ, c • k₀ = 0 → (RingHom.id ℝ) c • omega μ ν k₀ = 0 := by
    intro c hc
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · rw [smul_eq_zero_iff_right hc0] at hc
      simp [hc, omega_zero]
  let f : C(X × X, ℝ) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' k₀ (omega μ ν k₀) H
  obtain ⟨L, hLf, hL⟩ := exists_extension_of_le_sublinear f (omega μ ν) (fun c hc k => omega_smul hc k)
    omega_add fun x => by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 x.2
      have hx : x = ⟨c • k₀, hc ▸ x.2⟩ := Subtype.ext hc.symm
      rw [hx, LinearPMap.mkSpanSingleton'_apply, RingHom.id_apply, smul_eq_mul]
      exact mul_omega_le c k₀
  refine ⟨L, ?_, hL⟩
  have := hLf ⟨k₀, Submodule.mem_span_singleton_self k₀⟩
  rw [this]
  exact LinearPMap.mkSpanSingleton'_apply_self _ _ _ _

/-- **A coupling attaining `ω`**: the Riesz measure of a Hahn-Banach extension `L ≤ ω` with `L k₀ = ω(k₀)`. -/
theorem exists_coupling_eq_omega (k₀ : C(X × X, ℝ)) :
    ∃ σ ∈ couplings μ ν, ∫ p, k₀ p ∂σ = omega μ ν k₀ := by
  obtain ⟨L, hLk, hL⟩ := exists_linear_le_omega (μ := μ) (ν := ν) k₀
  have hpos : ∀ k : C(X × X, ℝ), 0 ≤ k → 0 ≤ L k := fun k hk => by
    have h := (hL (-k)).trans (omega_nonpos fun p => neg_nonpos.mpr (hk p))
    rw [map_neg] at h
    linarith
  let e : C_c(X × X, ℝ) →ₗ[ℝ] C(X × X, ℝ) :=
    { toFun := fun k => k.toContinuousMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Λ : C_c(X × X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ (L ∘ₗ e) fun k hk => hpos _ hk
  set σ := RealRMK.rieszMeasure Λ with hσ
  have hint : ∀ k : C(X × X, ℝ), ∫ p, k p ∂σ = L k := fun k =>
    RealRMK.integral_rieszMeasure Λ (CompactlySupportedContinuousMap.continuousMapEquiv k)
  have : IsFiniteMeasure σ := inferInstance
  have hone : (1 : C(X, ℝ)).comp fstC = (1 : C(X × X, ℝ)) := rfl
  have hprob : IsProbabilityMeasure σ := by
    have h : ∫ p, (1 : C(X × X, ℝ)) p ∂σ = 1 := by
      rw [hint, ← hone, eq_integral_fst hL]
      simp
    simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at h
    exact ⟨by rw [← ENNReal.toReal_eq_one_iff, ← measureReal_def]; exact h⟩
  refine ⟨σ, ⟨hprob, ?_, ?_⟩, hint k₀ ▸ hLk⟩
  · refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
    exact (hint (f.toContinuousMap.comp fstC)).trans (eq_integral_fst hL f.toContinuousMap)
  · refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    exact (hint (f.toContinuousMap.comp sndC)).trans (eq_integral_snd hL f.toContinuousMap)

variable (μ ν) in
/-- The dual values `∫ f dμ + ∫ g dν` over the continuous `f`, `g` with `f(x) + g(y) ≤ h(x, y)`. -/
def dualValues (h : C(X × X, ℝ)) : Set ℝ :=
  {r | ∃ f g : C(X, ℝ), (∀ p : X × X, f p.1 + g p.2 ≤ h p) ∧ r = ∫ x, f x ∂μ + ∫ x, g x ∂ν}

/-- **Monge-Kantorovich duality**: for a continuous cost `h` on `X × X` there is an optimal coupling `σ`, and
`∫ h dσ = min_{π ∈ Π(μ, ν)} ∫ h dπ = sup {∫ f dμ + ∫ g dν | f(x) + g(y) ≤ h(x, y)}`. -/
theorem exists_optimal_coupling (h : C(X × X, ℝ)) :
    ∃ σ ∈ couplings μ ν, (∀ π ∈ couplings μ ν, ∫ p, h p ∂σ ≤ ∫ p, h p ∂π) ∧
      IsLUB (dualValues μ ν h) (∫ p, h p ∂σ) := by
  obtain ⟨σ, hσ, hσe⟩ := exists_coupling_eq_omega (μ := μ) (ν := ν) (-h)
  have := hσ.1
  have hneg : ∀ π : Measure (X × X), ∫ p, (-h) p ∂π = -∫ p, h p ∂π := fun π => by
    simp only [ContinuousMap.neg_apply, integral_neg]
  refine ⟨σ, hσ, fun π hπ => ?_, ⟨?_, fun b hb => ?_⟩⟩
  · have := integral_le_omega hπ (-h)
    rw [← hσe, hneg, hneg] at this
    linarith
  · rintro _ ⟨f, g, hfg, rfl⟩
    have := integral_le_of_mem_upper hσ (k := -h) ⟨-f, -g, fun p => by
      simp only [ContinuousMap.neg_apply]; linarith [hfg p], rfl⟩
    rw [hneg] at this
    simp only [ContinuousMap.neg_apply, integral_neg] at this
    linarith
  · have : -b ≤ omega μ ν (-h) := le_csInf (upper_nonempty μ ν (-h)) fun r ⟨f, g, hfg, hr⟩ => by
      have := hb ⟨-f, -g, fun p => by
        have := hfg p
        simp only [ContinuousMap.neg_apply] at this ⊢
        linarith, rfl⟩
      simp only [ContinuousMap.neg_apply, integral_neg] at this
      linarith
    rw [← hσe, hneg] at this
    linarith

/-- **The duality as an equality**: `min_{π ∈ Π(μ, ν)} ∫ h dπ = sup {∫ f dμ + ∫ g dν | f ⊕ g ≤ h}`. -/
theorem integral_optimal_eq_sSup (h : C(X × X, ℝ)) :
    ∃ σ ∈ couplings μ ν, (∀ π ∈ couplings μ ν, ∫ p, h p ∂σ ≤ ∫ p, h p ∂π) ∧
      ∫ p, h p ∂σ = sSup (dualValues μ ν h) := by
  obtain ⟨σ, hσ, hmin, hlub⟩ := exists_optimal_coupling (μ := μ) (ν := ν) h
  refine ⟨σ, hσ, hmin, (hlub.csSup_eq ⟨_, ContinuousMap.const X (-‖h‖), 0, fun p => ?_, rfl⟩).symm⟩
  simp only [ContinuousMap.const_apply, ContinuousMap.zero_apply, add_zero]
  have := h.norm_coe_le_norm p
  rw [Real.norm_eq_abs] at this
  linarith [neg_abs_le (h p)]

end Lightlike.OperatorAlgebras.Transport
