module

public import Lightlike.SU2.Su2Exp

/-!
# The differential of a continuous representation of SU(2)

Stage C, part 2, of group-level completeness (`Completeness.lean`). For a continuous homomorphism
`ρ : SU2 →* M_d(ℂ)` and `X ∈ su(2)`:

* `rho_Γ`: `ρ(exp tX) = exp(t · dρ X)` (stage A), where `dρ X` is the derivative at `0`.
* `dρ_smul`: `dρ(cX) = c · dρ X` (real `c`).
* `dρ_add`: `dρ(X + Y) = dρ X + dρ Y`.

So **the differential is real-linear**. Additivity uses the Lie product formula (stage B) twice:
in `M₂(ℂ)` to write `exp(X + Y)` as a limit of products of `exp(X/n)` and `exp(Y/n)`, and in
`M_d(ℂ)` to evaluate the image of that limit under `ρ`.

**References.** B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed. (Springer, 2015), ch. 3 (a Lie group homomorphism induces a Lie algebra homomorphism) and ch. 4.
-/

@[expose] public section

open Matrix Filter Topology

namespace Lightlike.SU2

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {d : ℕ} [NeZero d] (ρ : SU2 →* Matrix (Fin d) (Fin d) ℂ)

/-- `exp(tA) = exp(tB)` for all real `t` forces `A = B`. -/
lemma exp_smul_injective {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ t : ℝ, NormedSpace.exp (t • A) = NormedSpace.exp (t • B)) : A = B := by
  have hA := hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0
  have hB := hasDerivAt_exp_smul_const (𝕂 := ℝ) B 0
  have hA' : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • B))
      (NormedSpace.exp ((0 : ℝ) • A) * A) 0 :=
    hA.congr_of_eventuallyEq (Eventually.of_forall fun u => (h u).symm)
  have := hA'.unique hB
  simpa using this

open scoped Classical in
/-- The differential of `ρ` at `X ∈ su(2)` (zero off `su(2)`). -/
noncomputable def dρ (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  if hX : IsSu2 X then deriv (fun t => ρ (Γ X hX t)) 0 else 0

variable {ρ}

omit [NeZero d] in
/-- **`ρ(exp tX) = exp(t · dρ X)`.** -/
theorem rho_Γ (hρ : Continuous ρ) {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X) (t : ℝ) :
    ρ (Γ X hX t) = NormedSpace.exp (t • dρ ρ X) := by
  obtain ⟨A, hA⟩ := oneParam_eq_exp (fun t => ρ (Γ X hX t)) (hρ.comp (continuous_Γ hX))
    (by simp only [Γ_zero, map_one]) (fun s t => by simp only [Γ_add, map_mul])
  have hd : deriv (fun t => ρ (Γ X hX t)) 0 = A := by
    rw [show (fun t => ρ (Γ X hX t)) = fun t : ℝ => NormedSpace.exp (t • A) from funext hA]
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at this
    exact this.deriv
  rw [dρ, dite_eq_left hX, hd, hA]
  rfl

lemma IsSu2.smul {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X) (c : ℝ) : IsSu2 (c • X) :=
  ⟨by rw [conjTranspose_smul, star_trivial, hX.1, smul_neg], by rw [trace_smul, hX.2, smul_zero]⟩

lemma IsSu2.add {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X) (hY : IsSu2 Y) : IsSu2 (X + Y) :=
  ⟨by rw [conjTranspose_add, hX.1, hY.1, neg_add], by rw [trace_add, hX.2, hY.2, add_zero]⟩

omit [NeZero d] in
/-- **Homogeneity**: `dρ(cX) = c · dρ X`. -/
theorem dρ_smul (hρ : Continuous ρ) {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X) (c : ℝ) :
    dρ ρ (c • X) = c • dρ ρ X := by
  apply exp_smul_injective
  intro t
  rw [← rho_Γ hρ (hX.smul c), smul_smul, ← rho_Γ hρ hX]
  congr 1
  apply Subtype.ext
  simp only [Γ_coe, smul_smul]

/-- `ρ(exp(X + Y)) = exp(dρ X + dρ Y)`, by the Lie product formula on both sides. -/
lemma rho_Γ_add_one (hρ : Continuous ρ) {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X)
    (hY : IsSu2 Y) : ρ (Γ (X + Y) (hX.add hY) 1) = NormedSpace.exp (dρ ρ X + dρ ρ Y) := by
  set u : ℕ → SU2 := fun n => (Γ X hX (n : ℝ)⁻¹ * Γ Y hY (n : ℝ)⁻¹) ^ n
  have hcoe : ∀ n, ((u n : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      (NormedSpace.exp ((n : ℝ)⁻¹ • X) * NormedSpace.exp ((n : ℝ)⁻¹ • Y)) ^ n := fun n => rfl
  have hlim : ((Γ (X + Y) (hX.add hY) 1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      NormedSpace.exp (X + Y) := by rw [Γ_coe, one_smul]
  have hu : Tendsto u atTop (𝓝 (Γ (X + Y) (hX.add hY) 1)) := by
    rw [tendsto_subtype_rng, hlim]
    have := lie_product X Y
    refine this.congr fun n => ?_
    exact (hcoe n).symm
  have h1 := (hρ.tendsto _).comp hu
  have h2 : Tendsto (ρ ∘ u) atTop (𝓝 (NormedSpace.exp (dρ ρ X + dρ ρ Y))) := by
    have := lie_product (dρ ρ X) (dρ ρ Y)
    refine this.congr fun n => ?_
    simp only [u, Function.comp_apply, map_pow, map_mul, rho_Γ hρ]
    rfl
  exact tendsto_nhds_unique h1 h2

/-- **Additivity**: `dρ(X + Y) = dρ X + dρ Y`. -/
theorem dρ_add (hρ : Continuous ρ) {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X)
    (hY : IsSu2 Y) : dρ ρ (X + Y) = dρ ρ X + dρ ρ Y := by
  apply exp_smul_injective
  intro t
  have hΓ : Γ (X + Y) (hX.add hY) t = Γ (t • X + t • Y) ((hX.smul t).add (hY.smul t)) 1 := by
    apply Subtype.ext
    simp only [Γ_coe, one_smul, smul_add]
  rw [← rho_Γ hρ (hX.add hY), hΓ, rho_Γ_add_one hρ (hX.smul t) (hY.smul t),
    dρ_smul hρ hX, dρ_smul hρ hY, smul_add]

end Lightlike.SU2
