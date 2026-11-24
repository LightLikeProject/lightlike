import Lightlike.OperatorAlgebras.CARQuasiFree
import Lightlike.OperatorAlgebras.TestsCARBogoliubov

/-!
# Tests for the fermionic Bogoliubov vacua

For the two-mode mixing `α = c·1`, `β = s·[[0,1],[-1,0]]` (`c² + s² = 1`) the Bogoliubov vacuum of the Jordan-Wigner
representation has occupation `⟪aᵢΨ, aⱼΨ⟫ = s² δᵢⱼ ‖Ψ‖²` and a nonzero anomalous pairing `⟪a₀Ψ, c₁Ψ⟫ = -sc ‖Ψ‖²`;
for the trivial transformation `α = 1, β = 0` the vacuum has no occupation.
-/

open Matrix

namespace Lightlike.OperatorAlgebras

lemma mixBeta_conj_mul (s : ℝ) : (mixBeta s)ᴴ * mixBeta s = ((s : ℂ) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp [mixBeta, sq]

lemma mix_anomalous (c s : ℝ) : ((mixBeta s)ᴴ * mixAlpha c) 0 1 = -((s : ℂ) * c) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, mixBeta, mixAlpha]

/-- The occupation of the two-mode Bogoliubov vacuum. -/
theorem mix_occupation (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    {Ψ : EuclideanSpace ℂ (Fin 2 → Fin 2)}
    (hΨ : ∀ j, bogAnn (mixAlpha c) (mixBeta s)
      (carAnnihilation (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner 2 a)))
      (carCreation (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner 2 a))) j Ψ = 0) (i j : Fin 2) :
    inner ℂ (carAnnihilation (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner 2 a)) i Ψ)
      (carAnnihilation (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner 2 a)) j Ψ) =
      (if i = j then (s : ℂ) ^ 2 else 0) * inner ℂ Ψ Ψ := by
  rw [bogVacuum_inner_a_a (isCAROn_jordanWigner 2) _ _ (mix_cond1 c s hcs) (mix_cond2 c s) hΨ, mixBeta_conj_mul]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Matrix.one_apply]

/-- The anomalous pairing of the two-mode vacuum. -/
theorem mix_pairing (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    {Ψ : EuclideanSpace ℂ (Fin 2 → Fin 2)}
    (hΨ : ∀ j, bogAnn (mixAlpha c) (mixBeta s)
      (carAnnihilation (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner 2 a)))
      (carCreation (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner 2 a))) j Ψ = 0) :
    inner ℂ (carAnnihilation (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner 2 a)) 0 Ψ)
      (carCreation (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner 2 a)) 1 Ψ) =
      -((s : ℂ) * c) * inner ℂ Ψ Ψ := by
  rw [bogVacuum_inner_a_c (isCAROn_jordanWigner 2) _ _ (mix_cond1 c s hcs) (mix_cond2 c s) hΨ, mix_anomalous]

end Lightlike.OperatorAlgebras
