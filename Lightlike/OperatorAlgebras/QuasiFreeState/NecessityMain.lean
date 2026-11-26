import Lightlike.OperatorAlgebras.QuasiFreeState.NecessityLinear
import Lightlike.OperatorAlgebras.QuasiFreeState.NecessityGauss

/-!
# Necessity: a pure quasi-free state has a compatible complex structure

If the covariance `η` of the quasi-free state is `η = η' + ε ρ ⊗ ρ` with a covariance `η'`, `ε > 0` and `ρ ≠ 0`, the
state is the mean `½ (ψ₊ + ψ₋)` of two states with `ψ₊(W(x)) = κ₊(x)`, `κ_± = exp(-¼ η'(x,x)) ∫ h_±(t) e^{i t ρ(x)} dγ(t)`,
`h₊ = 2·1_{t > 0}`, `h₋ = 2 - h₊`, `γ` the centred Gaussian of variance `ε/2` (`exists_state_of_kernel` and
`posSemidef_kernelOf_gauss`); extremality would give `ψ₊ = ω_η`, hence equal characteristic functions of `γ` and of
`h₊ γ`, which is false (`not_charFun_eq`). Combined with the linear algebra of `NecessityLinear`, a pure quasi-free
state of a nondegenerate finite-dimensional `(V, ω)` has a compatible complex structure
(`exists_compatible_of_pure`), the necessity half of the purity criterion.
-/

open scoped InnerProductSpace ComplexConjugate ComplexOrder

open MeasureTheory ProbabilityTheory

universe u

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Lightlike.OperatorAlgebras

variable {V : Type u} [AddCommGroup V] [Module ℝ V] {ω η η' : LinearMap.BilinForm ℝ V}


/-- The half-line density `h₊ = 2·1_{t > 0}`. -/
noncomputable def hPlus : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator (fun _ => (2 : ℝ))

lemma measurable_hPlus : Measurable hPlus := measurable_const.indicator measurableSet_Ioi

lemma hPlus_nonneg (t : ℝ) : 0 ≤ hPlus t := by
  unfold hPlus; by_cases h : t ∈ Set.Ioi (0 : ℝ) <;> simp [Set.indicator, h]

lemma hPlus_le (t : ℝ) : hPlus t ≤ 2 := by
  unfold hPlus; by_cases h : t ∈ Set.Ioi (0 : ℝ) <;> simp [Set.indicator, h]

section Main

variable [Fact (qfKerM ω η).PosSemidef] {ρ : V →ₗ[ℝ] ℝ} {ε : ℝ}

/-- `κ₊ + κ₋ = 2 exp(-¼ η)`. -/
lemma gauss_pair_sum (hε : 0 < ε) (hrel : ∀ x, η x x = η' x x + ε * ρ x ^ 2) (x : V) :
    gaussFamily η' ρ (gaussianReal 0 (ε / 2).toNNReal) hPlus x +
      gaussFamily η' ρ (gaussianReal 0 (ε / 2).toNNReal) (fun t => 2 - hPlus t) x =
      2 * ((gaussVal η x : ℝ) : ℂ) := by
  set γ := gaussianReal 0 (ε / 2).toNNReal with hγ
  have hb1 : ∀ t, |hPlus t| ≤ 2 := fun t => by rw [abs_of_nonneg (hPlus_nonneg t)]; exact hPlus_le t
  have hb2 : ∀ t, |2 - hPlus t| ≤ 2 := fun t => by
    rw [abs_le]; constructor <;> linarith [hPlus_nonneg t, hPlus_le t]
  rw [← gaussFamily_one hε hrel x]
  unfold gaussFamily
  have e1 := integrable_gphase ρ γ measurable_hPlus hb1 x
  have hm2 : Measurable (fun t => 2 - hPlus t) := measurable_const.sub measurable_hPlus
  have e2 := integrable_gphase ρ γ hm2 hb2 x
  rw [← mul_add, ← integral_add e1 e2]
  have e3 : ∀ t, ((hPlus t : ℝ) : ℂ) * gphase ρ t x + (((2 - hPlus t : ℝ)) : ℂ) * gphase ρ t x =
      2 * (((1 : ℝ) : ℂ) * gphase ρ t x) := fun t => by push_cast; ring
  simp only [e3]
  rw [integral_const_mul]
  ring

end Main


/-- **A covariance `η = η' + ε ρ ⊗ ρ` gives a non-pure quasi-free state**: the state is the mean of two states, and the
first one is not the quasi-free state. -/
theorem not_isPureState_of_sub [Fact (qfKerM ω η).PosSemidef] (hω : ∀ a b, ω a b = -ω b a)
    (hη' : IsCovariance ω η') {ρ : V →ₗ[ℝ] ℝ} (hρ : ρ ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hrel : ∀ x, η x x = η' x x + ε * ρ x ^ 2) : ¬ IsPureState (qfState ω η hω) := by
  intro hpure
  set v : NNReal := (ε / 2).toNNReal with hvdef
  have hv : v ≠ 0 := by
    rw [hvdef]; intro h0
    have := Real.toNNReal_eq_zero.1 h0
    linarith
  set γ := gaussianReal 0 v with hγ
  have hb1 : ∀ t, |hPlus t| ≤ 2 := fun t => by rw [abs_of_nonneg (hPlus_nonneg t)]; exact hPlus_le t
  have hm2 : Measurable (fun t => 2 - hPlus t) := measurable_const.sub measurable_hPlus
  have h20 : ∀ t, 0 ≤ 2 - hPlus t := fun t => by linarith [hPlus_le t]
  have h22 : ∀ t, 2 - hPlus t ≤ 2 := fun t => by linarith [hPlus_nonneg t]
  set κp := gaussFamily η' ρ γ hPlus with hκp
  set κm := gaussFamily η' ρ γ (fun t => 2 - hPlus t) with hκm
  have hsum : ∀ x, κp x + κm x = 2 * ((gaussVal η x : ℝ) : ℂ) := gauss_pair_sum hε hrel
  have hposP := posSemidef_kernelOf_gauss (ρ := ρ) (γ := γ) hω hη' measurable_hPlus hPlus_nonneg hPlus_le
  have hposM := posSemidef_kernelOf_gauss (ρ := ρ) (γ := γ) hω hη' hm2 h20 h22
  -- the kernels add up to `2 qfKer`
  have hker : ∀ κ κ' : V → ℂ, (∀ x, κ x + κ' x = 2 * ((gaussVal η x : ℝ) : ℂ)) →
      (2 : ℂ) • qfKer ω η - kernelOf ω κ = kernelOf ω κ' := fun κ κ' hk => by
    ext φ ψ
    have := hk (ψ - φ)
    simp only [Matrix.sub_apply, Matrix.smul_apply, qfKer_eq_kernelOf, kernelOf, Matrix.of_apply, smul_eq_mul]
    rw [show κ' (ψ - φ) = 2 * ((gaussVal η (ψ - φ) : ℝ) : ℂ) - κ (ψ - φ) by rw [← this]; ring]
    ring
  have hdomP : ((2 : ℂ) • qfKer ω η - kernelOf ω κp).PosSemidef := by
    rw [hker κp κm hsum]; exact hposM
  have hdomM : ((2 : ℂ) • qfKer ω η - kernelOf ω κm).PosSemidef := by
    rw [hker κm κp (fun x => by rw [add_comm]; exact hsum x)]; exact hposP
  -- the normalisations
  have hκp0 : κp 0 = 1 := by
    simp only [hκp, gaussFamily, gphase, gaussVal]
    have h1 : η' 0 0 = 0 := by simp
    have h2 : ∫ t, ((hPlus t : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ) * ((ρ 0 : ℝ) : ℂ)) ∂γ = 1 := by
      simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
      rw [integral_complex_ofReal]
      have h3 : ∫ t, hPlus t ∂γ = 1 := by
        unfold hPlus
        rw [integral_indicator_const _ measurableSet_Ioi]
        have := gaussian_Ioi_half v hv
        simp only [Measure.real, hγ, this, smul_eq_mul]
        simp
      rw [h3]; simp
    rw [h1, h2]; simp
  have hκm0 : κm 0 = 1 := by
    have := hsum 0
    have h0 : ((gaussVal η 0 : ℝ) : ℂ) = 1 := by simp [gaussVal]
    rw [h0, hκp0] at this
    linear_combination this
  obtain ⟨ψp, hψp, hψpc, hψpW⟩ := exists_state_of_kernel hω κp hκp0 hposP hdomP
  obtain ⟨ψm, hψm, hψmc, hψmW⟩ := exists_state_of_kernel hω κm hκm0 hposM hdomM
  -- the mean of the two states is the quasi-free state
  let χ : qfAlgebra ω η hω →L[ℂ] ℂ :=
    { toLinearMap := (1 / 2 : ℂ) • (ψp + ψm)
      cont := (continuous_const.mul (hψpc.add hψmc)) }
  have hχW : ∀ x, χ (qfWA ω η hω x) = ((gaussVal η x : ℝ) : ℂ) := fun x => by
    show (1 / 2 : ℂ) * (ψp (qfWA ω η hω x) + ψm (qfWA ω η hω x)) = _
    rw [hψpW, hψmW, hsum]; ring
  have hχ := qfState_unique ω η hω χ hχW
  have hmean : (1 / 2 : ℝ) • ψp + (1 / 2 : ℝ) • ψm = qfState ω η hω := by
    ext a
    have := hχ a
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Complex.real_smul]
    rw [← this]
    show _ = (1 / 2 : ℂ) * (ψp a + ψm a)
    push_cast; ring
  have hext := hpure.2 hψp hψm ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, hmean⟩
  -- so `κ₊ = exp(-¼ η)`, contradicting the characteristic functions
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ρ x₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hρ (LinearMap.ext hall)
  have hall : ∀ u : ℝ, ∫ t, (((Set.Ioi (0 : ℝ)).indicator (fun _ => (2 : ℝ)) t : ℝ) : ℂ) *
        Complex.exp (Complex.I * t * u) ∂γ = ∫ t, Complex.exp (Complex.I * t * u) ∂γ := fun u => by
    set x := (u / ρ x₀) • x₀ with hx
    have hρx : ρ x = u := by rw [hx, map_smul, smul_eq_mul]; field_simp
    have h1 := congrArg (fun f => f (qfWA ω η hω x)) hext
    simp only [hψpW, qfState_W] at h1
    rw [← gaussFamily_one hε hrel x] at h1
    have hne : ((gaussVal η' x : ℝ) : ℂ) ≠ 0 := by
      simp [gaussVal]
    unfold gaussFamily at h1
    have h2 := mul_left_cancel₀ hne h1
    simp only [gphase, hρx, Complex.ofReal_one, one_mul] at h2
    exact h2
  exact not_charFun_eq v hv hall


/-- **Necessity: a pure quasi-free state has a compatible complex structure.** For a finite-dimensional real vector
space `V` with a nondegenerate antisymmetric form `ω` and a covariance `η`, if the quasi-free state `ω_η` of the Weyl
algebra is pure then there is a real-linear `J` with `J² = -1`, `η` `J`-invariant and positive definite, and
`ω(x, y) = -η(x, J y)`. -/
theorem exists_compatible_of_pure [FiniteDimensional ℝ V] [Fact (qfKerM ω η).PosSemidef]
    (hω : ∀ a b, ω a b = -ω b a) (hnd : ∀ x, (∀ y, ω x y = 0) → x = 0) (hη : IsCovariance ω η)
    (hpure : IsPureState (qfState ω η hω)) : Nonempty (CompatibleComplexStructure ω η) := by
  by_contra hne
  have hno : IsEmpty (CompatibleComplexStructure ω η) := not_nonempty_iff.1 hne
  obtain ⟨ρ, ε, hρ, hε, hcov⟩ := exists_sub_covariance hω hnd hη hno
  refine not_isPureState_of_sub hω hcov hρ hε (fun x => ?_) hpure
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, outerForm_apply, smul_eq_mul]
  ring

/-- **The purity criterion for quasi-free states of the Weyl algebra of a finite-dimensional symplectic space**: the
quasi-free state `ω_η` is pure if and only if `(ω, η)` has a compatible complex structure
(`J² = -1`, `η` `J`-invariant and positive definite, `ω(x, y) = -η(x, J y)`); the converse direction is
`isPureState_qfState_of_complexStructure`. -/
theorem isPureState_iff_compatible [FiniteDimensional ℝ V] [Fact (qfKerM ω η).PosSemidef]
    (hω : ∀ a b, ω a b = -ω b a) (hnd : ∀ x, (∀ y, ω x y = 0) → x = 0) (hη : IsCovariance ω η) :
    IsPureState (qfState ω η hω) ↔ Nonempty (CompatibleComplexStructure ω η) :=
  ⟨exists_compatible_of_pure hω hnd hη, fun ⟨S⟩ => isPureState_qfState_of_complexStructure S⟩

end Lightlike.OperatorAlgebras.QuasiFreeState
