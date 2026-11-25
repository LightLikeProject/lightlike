import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Complex conjugation in a Hilbert basis

For a Hilbert basis `c` of `Z` the conjugation `C_c (∑ aᵢ cᵢ) = ∑ āᵢ cᵢ` is a conjugate-linear isometric involution fixing
every `cᵢ`. It is used to turn the antilinear part of a Bogoliubov map into a complex-linear operator, so that the
Hilbert-Schmidt basis independence for linear operators applies.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.OperatorAlgebras.CARShale

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z] {κ : Type*}
  (c : HilbertBasis κ ℂ Z)

/-- The coefficient-wise conjugate of a vector's coordinates in `c`, as an `ℓ²` sequence. -/
noncomputable def conjCoeff (v : Z) : lp (fun _ : κ => ℂ) 2 :=
  ⟨fun i => conj (c.repr v i), by
    have h : Memℓp (fun i => c.repr v i) 2 := (c.repr v).2
    show Memℓp (fun i => conj (c.repr v i)) 2
    rw [memℓp_gen_iff (by norm_num)] at h ⊢
    simpa using h⟩

/-- The conjugation in the Hilbert basis `c`. -/
noncomputable def conjC (v : Z) : Z := c.repr.symm (conjCoeff c v)

/-- Auxiliary lemma `repr_conjC` for the fermionic Shale theorem. -/
lemma repr_conjC (v : Z) (i : κ) : c.repr (conjC c v) i = conj (c.repr v i) := by
  rw [conjC, c.repr.apply_symm_apply]; rfl

/-- Auxiliary lemma `conjC_add` for the fermionic Shale theorem. -/
lemma conjC_add (u v : Z) : conjC c (u + v) = conjC c u + conjC c v := by
  apply c.repr.injective
  ext i
  simp only [map_add, lp.coeFn_add, Pi.add_apply, repr_conjC]

/-- Auxiliary lemma `conjC_smul` for the fermionic Shale theorem. -/
lemma conjC_smul (a : ℂ) (v : Z) : conjC c (a • v) = conj a • conjC c v := by
  apply c.repr.injective
  ext i
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, repr_conjC, smul_eq_mul, map_mul]

/-- Auxiliary lemma `conjC_conjC` for the fermionic Shale theorem. -/
lemma conjC_conjC (v : Z) : conjC c (conjC c v) = v := by
  apply c.repr.injective
  ext i
  rw [repr_conjC, repr_conjC, Complex.conj_conj]

/-- Auxiliary lemma `conjC_basis` for the fermionic Shale theorem. -/
lemma conjC_basis (i : κ) : conjC c (c i) = c i := by
  apply c.repr.injective
  ext j
  classical
  rw [repr_conjC, HilbertBasis.repr_self]
  simp only [lp.single_apply]
  by_cases h : j = i <;> simp [Pi.single_apply, h]

/-- Auxiliary lemma `inner_conjC` for the fermionic Shale theorem. -/
lemma inner_conjC (u v : Z) : ⟪conjC c u, conjC c v⟫_ℂ = conj ⟪u, v⟫_ℂ := by
  rw [← c.repr.inner_map_map, ← c.repr.inner_map_map u v, lp.inner_eq_tsum, lp.inner_eq_tsum]
  have : ∀ i, ⟪(c.repr (conjC c u)) i, (c.repr (conjC c v)) i⟫_ℂ =
      conj ⟪(c.repr u) i, (c.repr v) i⟫_ℂ := fun i => by
    rw [repr_conjC, repr_conjC]
    simp [inner_conj_symm]
  simp only [this]
  exact (Complex.conj_tsum _).symm

/-- Auxiliary lemma `norm_conjC` for the fermionic Shale theorem. -/
lemma norm_conjC (v : Z) : ‖conjC c v‖ = ‖v‖ := by
  have h := inner_conjC c v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖conjC c v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast (by simpa using h : ((‖conjC c v‖ : ℝ) : ℂ) ^ 2 = ((‖v‖ : ℝ) : ℂ) ^ 2)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

end Lightlike.OperatorAlgebras.CARShale
