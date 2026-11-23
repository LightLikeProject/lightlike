import Mathlib

/-!
# The Dirac operator on Euclidean space

The flat layer of the Dirac operator (milestone GE5). We take `ℝⁿ = EuclideanSpace ℝ (Fin n)` with
the negative definite form `Q v = -‖v‖²` (the sign of `Lightlike.Spin4.Qℍ`), so that `v² = -‖v‖²`
in Mathlib's `CliffordAlgebra Q`. A *Clifford module* is a normed real vector space `V` with an
algebra homomorphism `ρ : CliffordAlgebra Q →ₐ[ℝ] (V →L[ℝ] V)`; the Dirac operator on
`V`-valued functions is `D f = ∑ᵢ ρ(eᵢ) ∂ᵢ f`, and we prove `D² f = -Δ f` for `C²` functions
(`dirac_dirac`), the flat case of the Lichnerowicz formula `D² = ∇*∇ + R/4`
(`∇*∇ = -Δ` in flat space, `R = 0`).

## Conventions

* `ρ(v)² = -‖v‖²` because Mathlib's relation is `ι v * ι v = algebraMap (Q v)`. With the other
  sign `Q v = +‖v‖²` one would get `D² = +Δ`.
* No irreducible spinor module is chosen: every Clifford module is allowed (a module of the
  Clifford algebra is what Berline–Getzler–Vergne call a Clifford module).

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); only the definitions are used
  here, no equation number is claimed.
-/

open CliffordAlgebra InnerProductSpace Laplacian

namespace Lightlike.Dirac

/-- Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The negative definite quadratic form `Q v = -‖v‖²` on `ℝⁿ`. -/
noncomputable def Qneg (n : ℕ) : QuadraticForm ℝ (E n) :=
  -(LinearMap.BilinMap.toQuadraticMap (innerₗ (E n)))

lemma Qneg_apply {n : ℕ} (v : E n) : Qneg n v = -‖v‖ ^ 2 := by
  simp [Qneg, LinearMap.BilinMap.toQuadraticMap_apply]

/-- The `i`-th standard basis vector of `ℝⁿ`. -/
noncomputable def e {n : ℕ} (i : Fin n) : E n := EuclideanSpace.single i 1

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A Clifford module structure on `V` over `Cl(ℝⁿ, -‖·‖²)`. -/
abbrev CliffordRep (n : ℕ) (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  CliffordAlgebra (Qneg n) →ₐ[ℝ] (V →L[ℝ] V)

/-- Clifford multiplication by the `i`-th basis vector. -/
noncomputable def gam (ρ : CliffordRep n V) (i : Fin n) : V →L[ℝ] V :=
  ρ (ι (Qneg n) (e i))

/-- `γᵢ² = -1`. -/
lemma gam_sq (ρ : CliffordRep n V) (i : Fin n) (w : V) : gam ρ i (gam ρ i w) = -w := by
  have h := congrArg ρ (ι_sq_scalar (Qneg n) (e i))
  have h2 : gam ρ i * gam ρ i = -1 := by
    simp [gam, Qneg_apply, e]
  have := congrArg (fun L => L w) h2
  simpa using this

/-- `γᵢγⱼ + γⱼγᵢ = 0` for `i ≠ j`. -/
lemma gam_anticomm (ρ : CliffordRep n V) {i j : Fin n} (hij : i ≠ j) (w : V) :
    gam ρ i (gam ρ j w) + gam ρ j (gam ρ i w) = 0 := by
  have h := congrArg ρ (ι_mul_ι_add_swap (e i) (e j))
  have hin : inner ℝ (e i) (e j) = 0 := by
    simp [e, EuclideanSpace.inner_single_left, hij.symm]
  have hp : QuadraticMap.polar (Qneg n) (e i) (e j) = 0 := by
    simp only [QuadraticMap.polar, Qneg_apply, norm_add_sq_real, hin]
    ring
  have h2 : gam ρ i * gam ρ j + gam ρ j * gam ρ i = 0 := by
    simpa [gam, hp] using h
  have := congrArg (fun L => L w) h2
  simpa using this

/-- The Dirac operator `D f = ∑ᵢ γᵢ ∂ᵢ f` on `V`-valued functions on `ℝⁿ`. -/
noncomputable def dirac (ρ : CliffordRep n V) (f : E n → V) : E n → V :=
  fun x => ∑ i, gam ρ i (fderiv ℝ f x (e i))

/-- The derivative of `D f` in the direction `eⱼ`: `∑ᵢ γᵢ ∂ⱼ∂ᵢ f`. -/
lemma fderiv_dirac (ρ : CliffordRep n V) {f : E n → V} (hf : ContDiff ℝ 2 f) (x : E n)
    (j : Fin n) :
    fderiv ℝ (dirac ρ f) x (e j) = ∑ i, gam ρ i (fderiv ℝ (fderiv ℝ f) x (e j) (e i)) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hg : ∀ i, DifferentiableAt ℝ (fun y => fderiv ℝ f y (e i)) x := fun i =>
    ((hd.differentiable (by norm_num)).differentiableAt).clm_apply (differentiableAt_const _)
  have hh : ∀ i, HasFDerivAt (fun y => gam ρ i (fderiv ℝ f y (e i)))
      ((gam ρ i).comp (fderiv ℝ (fun y => fderiv ℝ f y (e i)) x)) x := fun i =>
    (gam ρ i).hasFDerivAt.comp x (hg i).hasFDerivAt
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hh i)
  have : dirac ρ f = fun y => ∑ i ∈ Finset.univ, gam ρ i (fderiv ℝ f y (e i)) := rfl
  rw [this, hsum.fderiv]
  simp only [sum_apply, ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [fderiv_clm_apply (hd.differentiable (by norm_num) x) (differentiableAt_const _)]
  simp

/-- **`D² = -Δ` on Euclidean space.** For a `C²` function `f : ℝⁿ → V` into a Clifford module,
`D (D f) = -Δ f`: the flat case of the Lichnerowicz formula `D² = ∇*∇ + R/4` (here `R = 0`). -/
theorem dirac_dirac (ρ : CliffordRep n V) {f : E n → V} (hf : ContDiff ℝ 2 f) (x : E n) :
    dirac ρ (dirac ρ f) x = -(Δ f) x := by
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    (hf.contDiffAt).isSymmSndFDerivAt (by simp)
  set S : Fin n → Fin n → V := fun j i => fderiv ℝ (fderiv ℝ f) x (e j) (e i) with hS
  have hSsym : ∀ i j, S i j = S j i := fun i j => hsymm.eq (e i) (e j)
  have hD : dirac ρ (dirac ρ f) x = ∑ j, ∑ i, gam ρ j (gam ρ i (S j i)) := by
    simp only [dirac, fderiv_dirac ρ hf, map_sum]
    rfl
  have hL : (Δ f) x = ∑ i, S i i := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin n) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [iteratedFDeriv_two_apply, hS, e]
  have key : ∀ j i, gam ρ j (gam ρ i (S j i)) + gam ρ i (gam ρ j (S i j)) =
      if j = i then (-2 : ℝ) • S j j else 0 := by
    intro j i
    by_cases h : j = i
    · subst h
      simp [gam_sq, two_smul]
    · rw [hSsym i j]
      simp only [h, ↓reduceIte]
      exact gam_anticomm ρ h _
  have h2 : (2 : ℝ) • ∑ j, ∑ i, gam ρ j (gam ρ i (S j i)) = (-2 : ℝ) • ∑ i, S i i := by
    have hc : ∑ j, ∑ i, gam ρ j (gam ρ i (S j i)) = ∑ j, ∑ i, gam ρ i (gam ρ j (S i j)) :=
      Finset.sum_comm
    rw [two_smul]
    nth_rewrite 2 [hc]
    rw [← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib, key]
    simp [Finset.smul_sum]
  rw [hD, hL]
  have := congrArg (fun v => (1 / 2 : ℝ) • v) h2
  simp only [smul_smul] at this
  norm_num at this
  simpa using this

end Lightlike.Dirac
