module

public import Mathlib

/-!
# Lorentzian forms and Lorentzian metrics on smooth manifolds

Conventions: spacetime dimension `n`, coordinate index `0` is time, signature is
"mostly plus" `η = diag(-1, +1, …, +1)` (Misner–Thorne–Wheeler / Wald convention).

## Design notes

* Mathlib (v4.35) has smooth *Riemannian* metrics (`Bundle.ContMDiffRiemannianMetric`) but no
  pseudo-Riemannian / Lorentzian ones. `LorentzianMetric` below follows the Riemannian structure
  field for field (`inner`, `symm`, `contMDiff`) and replaces positivity with a Lorentzian signature.
* Signature is expressed by the existence of a basis whose Gram matrix is `η`
  (a "Lorentz frame"). By Sylvester's law of inertia this is the usual definition; we do not
  need Sylvester's theorem itself for anything below.
-/

@[expose] public section

open Bundle Manifold Matrix
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

/-! ## The Minkowski signature matrix -/

/-- Diagonal entries of the Minkowski matrix: `-1` for the time index `0`, `+1` otherwise. -/
def etaDiag {n : ℕ} (i : Fin n) : ℝ := if (i : ℕ) = 0 then -1 else 1

/-- The Minkowski matrix `η = diag(-1, 1, …, 1)`. -/
def eta (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal etaDiag

@[simp] lemma etaDiag_mul_self {n : ℕ} (i : Fin n) : etaDiag i * etaDiag i = 1 := by
  unfold etaDiag; split_ifs <;> norm_num

lemma etaDiag_ne_zero {n : ℕ} (i : Fin n) : etaDiag i ≠ 0 := by
  unfold etaDiag; split_ifs <;> norm_num

@[simp] lemma eta_mul_eta (n : ℕ) : eta n * eta n = 1 := by
  simp [eta, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]

lemma eta_transpose (n : ℕ) : (eta n)ᵀ = eta n := Matrix.diagonal_transpose _

/-- `η` is its own inverse. -/
lemma eta_inv (n : ℕ) : (eta n)⁻¹ = eta n :=
  Matrix.inv_eq_left_inv (eta_mul_eta n)

lemma eta_apply {n : ℕ} (i j : Fin n) : eta n i j = if i = j then etaDiag i else 0 := by
  simp [eta, Matrix.diagonal_apply]

/-! ## Lorentzian bilinear forms on a vector space -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- A continuous bilinear form `B` on `V` is **Lorentzian of dimension `n`** if `V` admits a basis
`e₀, …, e_{n-1}` (a *Lorentz frame*) with `B(eᵢ, eⱼ) = ηᵢⱼ`. -/
def IsLorentzianForm (n : ℕ) (B : V →L[ℝ] V →L[ℝ] ℝ) : Prop :=
  ∃ e : Module.Basis (Fin n) ℝ V, ∀ i j, B (e i) (e j) = eta n i j

namespace IsLorentzianForm

variable {n : ℕ} {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- Expansion of a Lorentzian form in a Lorentz frame: `B(v,w) = Σᵢ ηᵢᵢ vⁱ wⁱ`. -/
lemma apply_eq_sum (e : Module.Basis (Fin n) ℝ V) (he : ∀ i j, B (e i) (e j) = eta n i j)
    (v w : V) : B v w = ∑ i, etaDiag i * e.repr v i * e.repr w i := by
  conv_lhs => rw [← e.sum_repr v, ← e.sum_repr w]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, he, eta_apply, smul_eq_mul]
  simp [mul_comm, mul_left_comm]

/-- Lorentzian forms are symmetric. -/
lemma symm (h : IsLorentzianForm n B) (v w : V) : B v w = B w v := by
  obtain ⟨e, he⟩ := h
  rw [apply_eq_sum e he, apply_eq_sum e he]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Lorentzian forms are nondegenerate. -/
lemma nondegenerate (h : IsLorentzianForm n B) (v : V) (hv : ∀ w, B v w = 0) : v = 0 := by
  obtain ⟨e, he⟩ := h
  refine e.ext_elem fun i => ?_
  have := hv (e i)
  rw [apply_eq_sum e he] at this
  simp only [Module.Basis.repr_self, Finsupp.single_apply] at this
  rw [Finset.sum_eq_single i (by intro j _ hj; simp [Ne.symm hj]) (by simp)] at this
  simpa [etaDiag_ne_zero] using this

/-- Agreement with Mathlib: the underlying `LinearMap.BilinForm` is symmetric
(Mathlib's `LinearMap.BilinForm.IsSymm`). -/
lemma isSymm (h : IsLorentzianForm n B) : B.toBilinForm.IsSymm :=
  ⟨fun v w => by simpa using h.symm v w⟩

/-- Agreement with Mathlib: the underlying `LinearMap.BilinForm` is nondegenerate
(Mathlib's `LinearMap.BilinForm.Nondegenerate`). -/
lemma bilinForm_nondegenerate (h : IsLorentzianForm n B) :
    B.toBilinForm.Nondegenerate := by
  refine ⟨fun v hv => h.nondegenerate v fun w => by simpa using hv w,
    fun w hw => h.nondegenerate w fun v => ?_⟩
  simpa [h.symm w v] using hw v

/-- Every Lorentzian form (with `n ≥ 1`) has a timelike vector: `B(e₀, e₀) = -1 < 0`. -/
lemma exists_timelike (hn : 0 < n) (h : IsLorentzianForm n B) : ∃ v, B v v < 0 := by
  obtain ⟨e, he⟩ := h
  refine ⟨e ⟨0, hn⟩, ?_⟩
  simp [he, eta_apply, etaDiag]

end IsLorentzianForm

/-! ## Lorentzian metrics on a smooth manifold -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth **Lorentzian metric** of dimension `n` on a smooth manifold `M` modelled on `I`:
a smooth section `g` of the bundle of bilinear forms on the tangent bundle, Lorentzian at each
point.

This mirrors Mathlib's `Bundle.ContMDiffRiemannianMetric` (same `inner`-style field and the same
smoothness condition, stated with `TotalSpace.mk'` in the hom-bundle `T*M ⊗ T*M`), with positive
definiteness replaced by Lorentzian signature. Symmetry and nondegeneracy are *consequences*
(`IsLorentzianForm.symm`, `IsLorentzianForm.nondegenerate`), not extra fields. -/
structure LorentzianMetric (n : ℕ) where
  /-- The metric tensor at each point. -/
  g (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- Pointwise Lorentzian signature. -/
  lorentzian (x : M) : IsLorentzianForm n (g x)
  /-- Smoothness of `x ↦ gₓ` as a section of the bundle `T*M ⊗ T*M`. -/
  contMDiff : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (g x))

variable {I M}

namespace LorentzianMetric

variable {n : ℕ} (g : LorentzianMetric I M n)

lemma symm (x : M) (v w : TangentSpace I x) : g.g x v w = g.g x w v :=
  (g.lorentzian x).symm v w

lemma nondegenerate (x : M) (v : TangentSpace I x) (hv : ∀ w, g.g x v w = 0) : v = 0 :=
  (g.lorentzian x).nondegenerate v hv

/-- A tangent vector is **timelike** if `g(v,v) < 0`. -/
def IsTimelike {x : M} (v : TangentSpace I x) : Prop := g.g x v v < 0

/-- A tangent vector is **null** (lightlike) if it is nonzero and `g(v,v) = 0`. -/
def IsNull {x : M} (v : TangentSpace I x) : Prop := v ≠ 0 ∧ g.g x v v = 0

/-- A tangent vector is **spacelike** if `g(v,v) > 0`. -/
def IsSpacelike {x : M} (v : TangentSpace I x) : Prop := 0 < g.g x v v

end LorentzianMetric

end Lightlike
