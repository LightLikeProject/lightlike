import Lightlike.Spacetime.EHManifold.BoxVariation

/-!
# The Palatini flux through a coordinate face on which the perturbation vanishes

`Wvec_of_vanishing_on_face`: at a point `x` where the perturbation `h` vanishes together with its derivatives
in all coordinate directions except the `i`-th (as happens on the face `x^i = const` of a box when `h`
vanishes on that face),

`W^i = (g^{iσ} g^{iν} - g^{ii} g^{σν}) ∂_i h_{σν}`.

With the unit normal `n^μ = g^{μi} / √|g^{ii}|` and the induced inverse metric
`h^{αβ} = g^{αβ} - g^{αi} g^{βi} / g^{ii}` of the face this is `-√|g^{ii}| h^{αβ} n^μ ∂_μ δg_{αβ}`, the
integrand of the boundary term in Dyer–Hinterbichler (4.2); that rewriting is not formalised.

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eq. (4.2), p. 20.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- A double sum with a condition on the first index. -/
lemma sum_sum_ite_left (i : Fin n) (F : Fin n → Fin n → ℝ) :
    ∑ σ, ∑ ν, (if σ = i then F σ ν else 0) = ∑ ν, F i ν := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- A double sum with a condition on the second index. -/
lemma sum_sum_ite_right (i : Fin n) (F : Fin n → Fin n → ℝ) :
    ∑ σ, ∑ ν, (if ν = i then F σ ν else 0) = ∑ σ, F σ i :=
  Finset.sum_congr rfl fun σ _ => by simp

/-- **The Palatini vector at a point of a face on which the perturbation vanishes.** -/
theorem Wvec_of_vanishing_on_face (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) (hx0 : h x = 0)
    (htan : ∀ σ a b, σ ≠ i → pd σ (fun z => h z a b) x = 0)
    (hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a) :
    Wvec g h i x = ∑ σ, ∑ ν, ((g x)⁻¹ i σ * (g x)⁻¹ i ν - (g x)⁻¹ i i * (g x)⁻¹ σ ν) *
      pd i (fun z => h z σ ν) x := by
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin n) (Fin n) ℝ, G = (g x)⁻¹ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Fin n → Fin n → ℝ, D = fun a b => pd i (fun z => h z a b) x := ⟨_, rfl⟩
  have hGs : ∀ a b, G a b = G b a := by
    intro a b
    rw [hG]
    exact hinv a b
  have hpd : ∀ σ a b, pd σ (fun z => h z a b) x = if σ = i then D a b else 0 := by
    intro σ a b
    by_cases hσ : σ = i
    · rw [if_pos hσ, hσ, hD]
    · rw [if_neg hσ, htan σ a b hσ]
  -- the variation of the Christoffel symbols at the point
  have hd : ∀ ρ σ ν, dChristoffel g h ρ σ ν x =
      (1 / 2) * ((if σ = i then ∑ l, G ρ l * D l ν else 0) +
        (if ν = i then ∑ l, G ρ l * D l σ else 0) - G ρ i * D σ ν) := by
    intro ρ σ ν
    unfold dChristoffel
    simp only [hx0, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_mul, zero_add,
      hpd, ← hG]
    congr 1
    have h3 : ∑ l, G ρ l * (if l = i then D σ ν else 0) = G ρ i * D σ ν := by
      simp
    by_cases hσ : σ = i <;> by_cases hν : ν = i <;>
      simp only [hσ, hν, if_true, if_false, mul_add, mul_sub, mul_zero, add_zero, zero_add,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, h3]
  obtain ⟨u, hu⟩ : ∃ u : Fin n → ℝ, u = fun ν => ∑ l, G i l * D l ν := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ σ, ∑ ν, G σ ν * D σ ν := ⟨_, rfl⟩
  have hA : ∑ σ, ∑ ν, G σ ν * dChristoffel g h i σ ν x =
      ∑ ν, G i ν * u ν - (1 / 2) * G i i * T := by
    have e1 : ∀ σ ν, G σ ν * dChristoffel g h i σ ν x =
        (1 / 2) * (if σ = i then G σ ν * u ν else 0) +
          (1 / 2) * (if ν = i then G σ ν * u σ else 0) - (1 / 2) * G i i * (G σ ν * D σ ν) := by
      intro σ ν
      rw [hd, hu]
      by_cases hσ : σ = i <;> by_cases hν : ν = i <;> simp only [hσ, hν, if_true, if_false] <;> ring
    simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_sum_ite_left, sum_sum_ite_right, ← hT]
    have e2 : ∑ σ, G σ i * u σ = ∑ ν, G i ν * u ν :=
      Finset.sum_congr rfl fun σ _ => by rw [hGs σ i]
    rw [e2]
    ring
  have hB : ∑ σ, G i σ * ∑ κ, dChristoffel g h κ κ σ x = (1 / 2) * G i i * T := by
    have e1 : ∀ σ, ∑ κ, dChristoffel g h κ κ σ x = (1 / 2) * (if σ = i then T else 0) := by
      intro σ
      have e3 : ∀ κ, dChristoffel g h κ κ σ x =
          (1 / 2) * (if κ = i then ∑ l, G κ l * D l σ else 0) +
            (1 / 2) * (if σ = i then ∑ l, G κ l * D l κ else 0) - (1 / 2) * (G κ i * D κ σ) := by
        intro κ
        rw [hd]
        ring
      simp only [e3, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have e4 : ∑ κ, (if κ = i then ∑ l, G κ l * D l σ else 0) = ∑ l, G i l * D l σ := by
        simp
      have e5 : ∑ κ, G κ i * D κ σ = ∑ l, G i l * D l σ :=
        Finset.sum_congr rfl fun κ _ => by rw [hGs κ i]
      have e6 : ∑ κ, (if σ = i then ∑ l, G κ l * D l κ else 0) = if σ = i then T else 0 := by
        by_cases hσ : σ = i
        · simp only [hσ, if_true, hT]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun κ _ => ?_
          rw [hGs κ l]
        · simp only [hσ, if_false, Finset.sum_const_zero]
      rw [e4, e5, e6]
      ring
    simp only [e1]
    have e7 : ∑ σ, G i σ * ((1 / 2) * (if σ = i then T else 0)) = (1 / 2) * G i i * T := by
      rw [Finset.sum_eq_single i]
      · simp only [if_true]
        ring
      · intro b _ hb
        simp only [hb, if_false, mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    exact e7
  have hW : Wvec g h i x = ∑ ν, G i ν * u ν - G i i * T := by
    unfold Wvec
    rw [← hG, hA, hB]
    ring
  rw [hW, ← hG]
  show _ = ∑ σ, ∑ ν, (G i σ * G i ν - G i i * G σ ν) * D σ ν
  have e8 : ∑ σ, ∑ ν, (G i σ * G i ν - G i i * G σ ν) * D σ ν =
      ∑ σ, ∑ ν, G i σ * G i ν * D σ ν - G i i * T := by
    rw [hT, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    ring
  have e9 : ∑ ν, G i ν * u ν = ∑ σ, ∑ ν, G i σ * G i ν * D σ ν := by
    rw [hu, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e8, e9]

end Lightlike
