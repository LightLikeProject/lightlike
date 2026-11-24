import Lightlike.OperatorAlgebras.CARBogoliubov

/-!
# Fermionic quasi-free (Bogoliubov) vacua

Let `φ` be a CAR representation on `E` with `aⱼ = carAnnihilation φ j`, `cⱼ = carCreation φ j = aⱼ*`, and let `(α, β)` satisfy
the Bogoliubov conditions (`α α* + β β* = 1`, `α βᵀ + β αᵀ = 0`). A vector `Ψ` killed by all the transformed annihilation
operators `bᵢ = ∑ⱼ (αᵢⱼ aⱼ + βᵢⱼ cⱼ)` is a **Bogoliubov vacuum**: the Fock vacuum for the transformed representation `bogFam φ α β`.
Its state `x ↦ ⟪Ψ, x Ψ⟫/⟪Ψ, Ψ⟫` is the pure quasi-free state with two-point function

* `⟪aᵢΨ, aⱼΨ⟫ = (β* β)ᵢⱼ ‖Ψ‖²`, `⟪cᵢΨ, cⱼΨ⟫ = (α* α)ᵢⱼ ‖Ψ‖²`, `⟪aᵢΨ, cⱼΨ⟫ = (β* α)ᵢⱼ ‖Ψ‖²`
  (`bogVacuum_inner_a_a`, `bogVacuum_inner_c_c`, `bogVacuum_inner_a_c`);

for an irreducible `φ` with a vacuum vector, a Bogoliubov vacuum exists (`bogVacuum_exists`, `Ψ = U Ω` for the implementing
unitary) and is unique up to a scalar (`bogVacuum_unique`); `exists_bogVacuum_jordanWigner` gives it for the Jordan-Wigner
representation. Only the two-point function is computed here; Wick's theorem for the higher correlation functions is not proved,
and no comparison with Bratteli-Robinson 2 or Dereziński Section 7 is claimed.
-/

open scoped InnerProductSpace
open Matrix

namespace Lightlike.OperatorAlgebras

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ}

section Vacuum

variable {φ : Fin (2 * n) → (E →L[ℂ] E)} (h : IsCAROn φ) (α β : Matrix (Fin n) (Fin n) ℂ)
  (h1 : α * αᴴ + β * βᴴ = 1) (h2 : α * βᵀ + β * αᵀ = 0)

include h
/-- The adjoint relation the other way: `⟪bᵢ* p, q⟫ = ⟪p, bᵢ q⟫`. -/
lemma bog_adj' (i : Fin n) (p q : E) :
    ⟪bogCre α β (carAnnihilation φ) (carCreation φ) i p, q⟫_ℂ = ⟪p, bogAnn α β (carAnnihilation φ) (carCreation φ) i q⟫_ℂ := by
  rw [← inner_conj_symm, ← bog_adj h, inner_conj_symm]

include h1 h2

/-- On a Bogoliubov vacuum, `bₖ* Ψ` are orthogonal of norm `‖Ψ‖`. -/
lemma bogVacuum_inner_cre {Ψ : E} (hΨ : ∀ j, bogAnn α β (carAnnihilation φ) (carCreation φ) j Ψ = 0) (k m : Fin n) :
    ⟪bogCre α β (carAnnihilation φ) (carCreation φ) k Ψ, bogCre α β (carAnnihilation φ) (carCreation φ) m Ψ⟫_ℂ =
      if k = m then ⟪Ψ, Ψ⟫_ℂ else 0 := by
  rw [bog_adj' h α β]
  have e := congrArg (fun T : E →L[ℂ] E => T Ψ) (bogAnn_bogCre_anticomm (h.isCARPairs) α β k m)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, hΨ, map_zero, add_zero,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, h1, Matrix.one_apply] at e
  rw [e]
  by_cases hkm : k = m
  · subst hkm; simp
  · simp [hkm]

lemma bogVacuum_a {Ψ : E} (hΨ : ∀ j, bogAnn α β (carAnnihilation φ) (carCreation φ) j Ψ = 0) (l : Fin n) :
    carAnnihilation φ l Ψ = ∑ i, β i l • bogCre α β (carAnnihilation φ) (carCreation φ) i Ψ := by
  have := congrArg (fun T : E →L[ℂ] E => T Ψ) (bog_inv (a := carAnnihilation φ) (c := carCreation φ) α β h1 h2 l).1
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hΨ,
    smul_zero, zero_add] at this
  exact this.symm

lemma bogVacuum_c {Ψ : E} (hΨ : ∀ j, bogAnn α β (carAnnihilation φ) (carCreation φ) j Ψ = 0) (l : Fin n) :
    carCreation φ l Ψ = ∑ i, α i l • bogCre α β (carAnnihilation φ) (carCreation φ) i Ψ := by
  have := congrArg (fun T : E →L[ℂ] E => T Ψ) (bog_inv (a := carAnnihilation φ) (c := carCreation φ) α β h1 h2 l).2
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hΨ,
    smul_zero, zero_add] at this
  exact this.symm

/-- The two-point function of a Bogoliubov vacuum: `⟪aᵢΨ, aⱼΨ⟫ = (β* β)ᵢⱼ ‖Ψ‖²`. -/
theorem bogVacuum_inner_a_a {Ψ : E} (hΨ : ∀ j, bogAnn α β (carAnnihilation φ) (carCreation φ) j Ψ = 0) (i j : Fin n) :
    ⟪carAnnihilation φ i Ψ, carAnnihilation φ j Ψ⟫_ℂ = (βᴴ * β) i j * ⟪Ψ, Ψ⟫_ℂ := by
  rw [bogVacuum_a h α β h1 h2 hΨ, bogVacuum_a h α β h1 h2 hΨ]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, bogVacuum_inner_cre h α β h1 h2 hΨ, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp
  ring

/-- `⟪cᵢΨ, cⱼΨ⟫ = (α* α)ᵢⱼ ‖Ψ‖²`. -/
theorem bogVacuum_inner_c_c {Ψ : E} (hΨ : ∀ j, bogAnn α β (carAnnihilation φ) (carCreation φ) j Ψ = 0) (i j : Fin n) :
    ⟪carCreation φ i Ψ, carCreation φ j Ψ⟫_ℂ = (αᴴ * α) i j * ⟪Ψ, Ψ⟫_ℂ := by
  rw [bogVacuum_c h α β h1 h2 hΨ, bogVacuum_c h α β h1 h2 hΨ]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, bogVacuum_inner_cre h α β h1 h2 hΨ, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp
  ring

/-- `⟪aᵢΨ, cⱼΨ⟫ = (β* α)ᵢⱼ ‖Ψ‖²` (the anomalous term). -/
theorem bogVacuum_inner_a_c {Ψ : E} (hΨ : ∀ j, bogAnn α β (carAnnihilation φ) (carCreation φ) j Ψ = 0) (i j : Fin n) :
    ⟪carAnnihilation φ i Ψ, carCreation φ j Ψ⟫_ℂ = (βᴴ * α) i j * ⟪Ψ, Ψ⟫_ℂ := by
  rw [bogVacuum_a h α β h1 h2 hΨ, bogVacuum_c h α β h1 h2 hΨ]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, bogVacuum_inner_cre h α β h1 h2 hΨ, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp
  ring

/-- **Existence of a Bogoliubov vacuum**: if the irreducible CAR representation `φ` has a nonzero vacuum vector `Ω`
(`aⱼ Ω = 0`), then `Ψ = U Ω` is a nonzero Bogoliubov vacuum, for the unitary `U` implementing the transformation. -/
theorem bogVacuum_exists [Nontrivial E] (hirr : IsIrreducibleCAR φ) {Ω : E} (hΩ0 : Ω ≠ 0)
    (hΩ : ∀ j, carAnnihilation φ j Ω = 0) :
    ∃ Ψ : E, Ψ ≠ 0 ∧ ∀ j, bogAnn α β (carAnnihilation φ) (carCreation φ) j Ψ = 0 := by
  obtain ⟨U, hU⟩ := bogoliubov_implementable h hirr α β h1 h2
  refine ⟨U Ω, fun hz => hΩ0 (by simpa using hz), fun j => ?_⟩
  rw [← carAnnihilation_bogFam]
  have : carAnnihilation (bogFam φ α β) j (U Ω) = U (carAnnihilation φ j Ω) := by
    simp only [carAnnihilation, majorana, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, map_smul, map_add,
      hU]
  rw [this, hΩ, map_zero]

/-- **Uniqueness of the Bogoliubov vacuum up to a scalar**: the vacuum space of the irreducible representation
`bogFam φ α β` is one-dimensional. -/
theorem bogVacuum_unique [Nontrivial E] (hirr : IsIrreducibleCAR φ) {Ψ Ψ' : E} (hΨ0 : Ψ ≠ 0)
    (hΨ : ∀ j, bogAnn α β (carAnnihilation φ) (carCreation φ) j Ψ = 0)
    (hΨ' : ∀ j, bogAnn α β (carAnnihilation φ) (carCreation φ) j Ψ' = 0) : ∃ c : ℂ, Ψ' = c • Ψ := by
  have hb := isCAROn_bogFam h α β h1 h2
  have hfr := (isIrreducibleCAR_iff hb).mp (isIrreducibleCAR_bogFam hirr α β h1 h2)
  haveI : FiniteDimensional ℂ (carVacuum (bogFam φ α β)) := Module.finite_of_finrank_eq_succ hfr
  have m1 : Ψ ∈ carVacuum (bogFam φ α β) := mem_carVacuum.mpr fun j => by rw [carAnnihilation_bogFam]; exact hΨ j
  have m2 : Ψ' ∈ carVacuum (bogFam φ α β) := mem_carVacuum.mpr fun j => by rw [carAnnihilation_bogFam]; exact hΨ' j
  have hne : (⟨Ψ, m1⟩ : carVacuum (bogFam φ α β)) ≠ 0 := fun hz => hΨ0 (congrArg Subtype.val hz)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hfr ⟨Ψ', m2⟩
  exact ⟨c, congrArg Subtype.val hc.symm⟩

end Vacuum

section JordanWigner

/-- **The Jordan-Wigner representation has a Bogoliubov vacuum for every Bogoliubov transformation.** -/
theorem exists_bogVacuum_jordanWigner (n : ℕ) (α β : Matrix (Fin n) (Fin n) ℂ) (h1 : α * αᴴ + β * βᴴ = 1)
    (h2 : α * βᵀ + β * αᵀ = 0) :
    ∃ Ψ : EuclideanSpace ℂ (Fin n → Fin 2), Ψ ≠ 0 ∧ ∀ j, bogAnn α β
      (carAnnihilation (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner n a)))
      (carCreation (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner n a))) j Ψ = 0 := by
  have : Nontrivial (EuclideanSpace ℂ (Fin n → Fin 2)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [finrank_euclideanSpace]; exact Fintype.card_pos)
  refine bogVacuum_exists (isCAROn_jordanWigner n) α β h1 h2 (isIrreducibleCAR_jordanWigner n)
    (Ω := WithLp.toLp 2 (jwVacuum n)) ?_ ?_
  · intro hz
    have := congrFun (congrArg WithLp.ofLp hz) (fun _ => 0)
    simp [jwVacuum] at this
  · intro j
    have e : carAnnihilation (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner n a)) j =
        Matrix.toEuclideanCLM (𝕜 := ℂ) (carAnnihilation (jordanWigner n) j) := by
      simp [carAnnihilation, majorana, map_add, map_smul]
    rw [e]
    rw [Matrix.toEuclideanCLM_toLp, carAnnihilation_jordanWigner_vacuum n j]
    rfl

end JordanWigner

end Lightlike.OperatorAlgebras
