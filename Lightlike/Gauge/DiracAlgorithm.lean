import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The Dirac consistency algorithm, linear case

For a constrained Hamiltonian system whose evolution is linear, `x' = A x + v` with the multiplier `v` ranging
over a subspace `U` (the span of the Hamiltonian vector fields of the primary constraints) and the primary
constraint surface a subspace `C₀`, the evolution is consistent at `x ∈ C` (stays in `C`) iff `A x ∈ C + U`.
The consistency conditions give the secondary constraints, and the process is iterated: `C_{k+1} = C_k ∩ A⁻¹ (C_k + U)`
(Dirac 1950, 1964; Henneaux and Teitelboim 1992, Section 1.1).

* `diracStep`, `diracChain`: one step and the chain `C₀ ⊇ C₁ ⊇ ...`.
* `diracChain_stabilizes`: in finite dimension the chain terminates (no tertiary and later constraints beyond a finite
  stage).
* `exists_multiplier_of_mem_final`: on the final subspace `C_N` every point has a multiplier `v ∈ U` with
  `A x + v ∈ C_N`.
* `le_diracChain`: every subspace `D ⊆ C₀` on which the evolution is consistent lies in every `C_k`, so the final
  subspace is the largest consistent one.

**Scope.** Linear evolution and linear (homogeneous) constraints only. The nonlinear Dirac algorithm (constraint
surfaces that are submanifolds, tangency in place of the subspace condition, termination without finite dimension
arguments of linear algebra) is the follow-up and is not covered here.
-/

namespace Lightlike.Gauge

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **One step of the Dirac algorithm**: the points of `C` where the evolution `x' = A x + v`, `v ∈ U`, can be kept
in `C`, that is `C ∩ A⁻¹ (C + U)`. -/
def diracStep (A : E →ₗ[ℝ] E) (U C : Submodule ℝ E) : Submodule ℝ E :=
  C ⊓ (C ⊔ U).comap A

lemma diracStep_le (A : E →ₗ[ℝ] E) (U C : Submodule ℝ E) : diracStep A U C ≤ C := inf_le_left

lemma diracStep_mono (A : E →ₗ[ℝ] E) (U : Submodule ℝ E) : Monotone (diracStep A U) := fun _ _ h =>
  inf_le_inf h (Submodule.comap_mono (sup_le_sup_right h U))

/-- The chain `C₀ ⊇ C₁ ⊇ ...` of the Dirac algorithm, `C_{k+1} = diracStep C_k`. -/
def diracChain (A : E →ₗ[ℝ] E) (U C₀ : Submodule ℝ E) (n : ℕ) : Submodule ℝ E :=
  (diracStep A U)^[n] C₀

lemma diracChain_succ (A : E →ₗ[ℝ] E) (U C₀ : Submodule ℝ E) (n : ℕ) :
    diracChain A U C₀ (n + 1) = diracStep A U (diracChain A U C₀ n) :=
  Function.iterate_succ_apply' _ _ _

lemma diracChain_antitone (A : E →ₗ[ℝ] E) (U C₀ : Submodule ℝ E) : Antitone (diracChain A U C₀) :=
  antitone_nat_of_succ_le fun n => by
    rw [diracChain_succ]; exact diracStep_le _ _ _

/-- **Termination of the Dirac algorithm** (finite dimension): from some stage on, the consistency conditions give
no new constraints. -/
theorem diracChain_stabilizes [IsArtinian ℝ E] (A : E →ₗ[ℝ] E) (U C₀ : Submodule ℝ E) :
    ∃ N, ∀ m, N ≤ m → diracChain A U C₀ N = diracChain A U C₀ m := by
  let f : ℕ →o (Submodule ℝ E)ᵒᵈ := ⟨fun n => OrderDual.toDual (diracChain A U C₀ n),
    fun a b hab => (diracChain_antitone A U C₀ hab)⟩
  exact IsArtinian.monotone_stabilizes f

/-- **Consistency on the final subspace**: if the chain has stopped at `N` (`C_{N+1} = C_N`), every point of `C_N`
has a multiplier `v ∈ U` with `A x + v ∈ C_N`. -/
theorem exists_multiplier_of_mem_final (A : E →ₗ[ℝ] E) (U C₀ : Submodule ℝ E) {N : ℕ}
    (hN : diracChain A U C₀ (N + 1) = diracChain A U C₀ N) {x : E} (hx : x ∈ diracChain A U C₀ N) :
    ∃ v ∈ U, A x + v ∈ diracChain A U C₀ N := by
  have hx' : x ∈ diracChain A U C₀ (N + 1) := hN ▸ hx
  rw [diracChain_succ] at hx'
  obtain ⟨c, hc, u, hu, hcu⟩ := Submodule.mem_sup.mp hx'.2
  refine ⟨-u, U.neg_mem hu, ?_⟩
  have : A x + -u = c := by rw [← hcu]; abel
  rw [this]; exact hc

/-- **Maximality**: a subspace `D ⊆ C₀` on which the evolution is consistent (`A x ∈ D + U` for `x ∈ D`) lies in
every `C_k`, in particular in the final one. -/
theorem le_diracChain (A : E →ₗ[ℝ] E) (U C₀ D : Submodule ℝ E) (hD : D ≤ C₀)
    (hcons : ∀ x ∈ D, A x ∈ D ⊔ U) (n : ℕ) : D ≤ diracChain A U C₀ n := by
  induction n with
  | zero => exact hD
  | succ n ih =>
    rw [diracChain_succ]
    exact le_inf ih fun x hx => Submodule.mem_comap.mpr (sup_le_sup_right ih U (hcons x hx))

end Lightlike.Gauge
