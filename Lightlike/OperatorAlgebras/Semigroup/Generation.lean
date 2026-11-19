import Lightlike.OperatorAlgebras.Semigroup.Generator

/-!
# The Hille–Yosida generation theorem for contraction semigroups

**Theorem** (`hille_yosida_generation`). Let `A` be a densely defined operator on a Banach space `X`
over `ℝ` or `ℂ` such that for every `λ > 0` the operator `λ - A` is bounded below by `λ`
(`λ ‖x‖ ≤ ‖λ x - A x‖`) and surjective onto `X`. Then there is a strongly continuous semigroup of
contractions whose generator is `A`.

The proof is the Yosida approximation: the limit of `exp (t Yos_n)` is a contraction semigroup
(`HYHyp.semigroup`) whose generator `B` contains `A` (`HYHyp.norm_S_sub_smul_le`); the generator of a
contraction semigroup is dissipative, and `λ - A` is already surjective, so `B = A`.

## Source and differences

Source: Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4,
<https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf>, Theorem 1.9 (Hille–Yosida):
"A closed operator `A` is the generator of a contraction semigroup if and only if `(0, ∞) ⊂ ρ(A)` and
`‖R_λ(A)‖ ≤ 1/λ`, `λ > 0`." Differences from the source statement:

* *Representation.* The hypotheses are `dom A` dense, and for every `λ > 0` that `λ - A` is bounded
  below, `λ ‖x‖ ≤ ‖λ x - A x‖`, and surjective. These are equivalent to the source's: bounded below
  and surjective means `λ - A` is bijective with an inverse of norm at most `λ⁻¹`, which is
  `λ ∈ ρ(A)` with `‖R_λ(A)‖ ≤ 1/λ`; a bounded inverse makes `A` closed.
* *Density.* The source's statement says "closed operator" without density, but its Lemma 1.6 is
  stated for a closed densely defined operator and its proof of Theorem 1.9 uses that `D(A)` is
  dense; density of the domain is a hypothesis here. (Approved by the maintainers, 18 November 2026.)
* *Equivalence.* The source states an equivalence; this file proves the generation direction (the
  hypotheses imply that `A` is a generator), and the converse is proved in `Converse.lean`, where the
  two are combined in `hilleYosida_contraction`.
-/

open NormedSpace Filter Topology Set NNReal
open scoped LinearPMap

noncomputable section

namespace Lightlike.OperatorAlgebras

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] {A : X →ₗ.[𝕜] X} (h : HYHyp A)

/-- The difference quotients of the limit semigroup converge to `A x` on the domain of `A`. -/
lemma HYHyp.tendsto_quot (x : A.domain) :
    Tendsto (fun t : ℝ≥0 => h.semigroup.quot t (x : X)) (𝓝[>] 0) (𝓝 (A x)) := by
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  obtain ⟨δ, hδ, hb⟩ := h.norm_S_sub_smul_le x (show 0 < ε' / 5 by positivity)
  have hmem : Ioo (0 : ℝ≥0) (Real.toNNReal δ) ∈ 𝓝[>] (0 : ℝ≥0) :=
    Ioo_mem_nhdsGT (by simpa using hδ)
  filter_upwards [hmem] with t ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht.1
  have htδ : (t : ℝ) ≤ δ := by
    have : (t : ℝ) < ((Real.toNNReal δ : ℝ≥0) : ℝ) := by exact_mod_cast ht.2
    rw [Real.coe_toNNReal δ hδ.le] at this
    exact this.le
  have hb' := hb t htδ
  have e : h.semigroup.quot t (x : X) - A x =
      (((t : ℝ)⁻¹ : ℝ) : 𝕜) • ((h.S t (x : X) - x) - ((t : ℝ) : 𝕜) • A x) := by
    have hne : ((t : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast ht0.ne'
    have hinv : (((t : ℝ)⁻¹ : ℝ) : 𝕜) * ((t : ℝ) : 𝕜) = 1 := by
      rw [← RCLike.ofReal_mul, inv_mul_cancel₀ ht0.ne']; simp
    simp only [ContractionSemigroup.quot, smul_sub, smul_smul, hinv, one_smul]
    rfl
  rw [dist_eq_norm, e]
  calc ‖(((t : ℝ)⁻¹ : ℝ) : 𝕜) • ((h.S t (x : X) - x) - ((t : ℝ) : 𝕜) • A x)‖
      ≤ ‖(((t : ℝ)⁻¹ : ℝ) : 𝕜)‖ * ‖(h.S t (x : X) - x) - ((t : ℝ) : 𝕜) • A x‖ := norm_smul_le _ _
    _ ≤ (t : ℝ)⁻¹ * (4 * (ε' / 5) * (t : ℝ)) := by
        rw [RCLike.norm_ofReal, abs_of_pos (inv_pos.2 ht0)]
        exact mul_le_mul_of_nonneg_left hb' (inv_pos.2 ht0).le
    _ = 4 * (ε' / 5) := by field_simp
    _ < ε' := by linarith

/-- `A` is contained in the generator of the limit semigroup. -/
lemma HYHyp.mem_generatorDomain (x : A.domain) :
    h.semigroup.IsGeneratorDomain (x : X) ∧ h.semigroup.genVal (x : X) = A x :=
  ⟨⟨A x, h.tendsto_quot x⟩, tendsto_nhds_unique (h.semigroup.tendsto_genVal ⟨A x, h.tendsto_quot x⟩)
    (h.tendsto_quot x)⟩

/-- **The generator of a contraction semigroup is dissipative**: `λ ‖x‖ ≤ ‖λ x - A x‖`. -/
theorem ContractionSemigroup.norm_dissip (S : ContractionSemigroup 𝕜 X) {l : ℝ} (hl : 0 < l)
    {x : X} (hx : S.IsGeneratorDomain x) :
    l * ‖x‖ ≤ ‖(l : 𝕜) • x - S.genVal x‖ := by
  have hlim := ((S.tendsto_genVal hx).const_smul (l : 𝕜) |> fun _ => (tendsto_const_nhds (x := (l : 𝕜) • x)).sub
    (S.tendsto_genVal hx)).norm
  refine ge_of_tendsto hlim ?_
  have hmem : Ioi (0 : ℝ≥0) ∈ 𝓝[>] (0 : ℝ≥0) := self_mem_nhdsWithin
  filter_upwards [hmem] with t ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  set v := (l : 𝕜) • x - S.quot t x with hv
  have e : (((l : ℝ) + (t : ℝ)⁻¹ : ℝ) : 𝕜) • x = v + (((t : ℝ)⁻¹ : ℝ) : 𝕜) • S t x := by
    simp only [hv, ContractionSemigroup.quot, smul_sub]
    push_cast
    rw [add_smul]
    abel
  have h1 : ‖(((l : ℝ) + (t : ℝ)⁻¹ : ℝ) : 𝕜) • x‖ = (l + (t : ℝ)⁻¹) * ‖x‖ := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (by positivity)]
  have h2 : ‖(((t : ℝ)⁻¹ : ℝ) : 𝕜) • S t x‖ ≤ (t : ℝ)⁻¹ * ‖x‖ := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 ht0)]
    exact mul_le_mul_of_nonneg_left
      (((S t).le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right (S.norm_le t) (norm_nonneg x)))
      (inv_pos.2 ht0).le
  have h3 := norm_add_le v ((((t : ℝ)⁻¹ : ℝ) : 𝕜) • S t x)
  rw [← e, h1] at h3
  nlinarith

/-- **The generator of the limit semigroup is `A`.** -/
theorem HYHyp.generator_eq : h.semigroup.generator = A := by
  have hdom : h.semigroup.generatorDomain = A.domain := by
    ext x
    constructor
    · intro hx
      -- `z = R 1 (x - B x) ∈ dom A`, and `x - z` is killed by `1 - B`, hence `x = z`
      obtain ⟨z, hz1, hz2⟩ := h.res_mem (l := 1) one_pos
        (((1 : ℝ) : 𝕜) • x - h.semigroup.genVal x)
      have hzgen := h.mem_generatorDomain z
      have hw : h.semigroup.IsGeneratorDomain (x - (z : X)) :=
        h.semigroup.generatorDomain.sub_mem hx hzgen.1
      have hval : h.semigroup.genVal (x - (z : X)) =
          h.semigroup.genVal x - h.semigroup.genVal (z : X) := by
        have := h.semigroup.generator.map_sub ⟨x, hx⟩ ⟨(z : X), hzgen.1⟩
        exact this
      have hd := h.semigroup.norm_dissip (l := 1) one_pos hw
      have h0 : ((1 : ℝ) : 𝕜) • (x - (z : X)) - h.semigroup.genVal (x - (z : X)) = 0 := by
        rw [hval, hzgen.2, smul_sub]
        have : ((1 : ℝ) : 𝕜) • (z : X) - A z = ((1 : ℝ) : 𝕜) • x - h.semigroup.genVal x := hz2
        rw [← sub_eq_zero] at this
        rw [show ((1 : ℝ) : 𝕜) • x - ((1 : ℝ) : 𝕜) • (z : X) - (h.semigroup.genVal x - A z) =
          (((1 : ℝ) : 𝕜) • x - h.semigroup.genVal x) - (((1 : ℝ) : 𝕜) • (z : X) - A z) by abel]
        rw [hz2, sub_self]
      rw [h0, norm_zero] at hd
      have hxz : x - (z : X) = 0 := norm_le_zero_iff.1 (by linarith)
      have : x = (z : X) := sub_eq_zero.1 hxz
      rw [this]
      exact z.2
    · intro hx
      exact (h.mem_generatorDomain ⟨x, hx⟩).1
  refine LinearPMap.ext hdom ?_
  intro x hf hg
  exact (h.mem_generatorDomain ⟨x, hg⟩).2

/-- **The Hille–Yosida generation theorem for contraction semigroups.** If `A` has dense domain and
for every `λ > 0` the operator `λ - A` is bounded below by `λ` and surjective, then `A` is the
generator of a strongly continuous semigroup of contractions. See the module docstring for the source
and the differences from it. -/
theorem hille_yosida_generation (A : X →ₗ.[𝕜] X) (hdense : Dense (A.domain : Set X))
    (hdiss : ∀ l : ℝ, 0 < l → ∀ x : A.domain, l * ‖(x : X)‖ ≤ ‖(l : 𝕜) • (x : X) - A x‖)
    (hsurj : ∀ l : ℝ, 0 < l → ∀ y : X, ∃ x : A.domain, (l : 𝕜) • (x : X) - A x = y) :
    ∃ S : ContractionSemigroup 𝕜 X, S.generator = A :=
  ⟨(HYHyp.mk hdense hdiss hsurj).semigroup, (HYHyp.mk hdense hdiss hsurj).generator_eq⟩

end Lightlike.OperatorAlgebras
