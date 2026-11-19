import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
/-!
# The CAR on the exterior algebra: creation and annihilation operators

J. Dereziński, arXiv:math-ph/0511030 (read): Section 5.3, p. 20 (the antisymmetric Fock space `Γₐ(Z)`), Section 7.1, p. 29 (the
creation and annihilation operators `a*(w)`, `a(w)` on `Γₐ(Z)`, the field operators `φ(w) = a*(w) + a(w)` and the CAR
`[φ(y₁), φ(y₂)]₊ = 2 y₁·y₂`, Theorem 28). Algebraically, `Γₐ(Z)` is the exterior algebra `Λ(Z)`, `a*(w)` is left multiplication by `w`
and `a(d)` the contraction with a linear form `d`. Here, for any module `M` over a commutative ring: `creation v` and `annihilation d`
on `ExteriorAlgebra R M` (Mathlib's `CliffordAlgebra.contractLeft`), with the CAR in creation-annihilation form
(`annihilation_creation_anticomm`: `{a(d), a*(v)} = d(v)`, `creation_anticomm`, `annihilation_anticomm`) and the vacuum `1` killed by
every annihilation (`annihilation_one`).
-/

namespace Lightlike.OperatorAlgebras

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The creation operator** `a*(v)`: left multiplication by `v` in the exterior algebra. -/
noncomputable def creation (v : M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  LinearMap.mulLeft R (ExteriorAlgebra.ι R v)

/-- **The annihilation operator** `a(d)`: the contraction with a linear form `d`. -/
noncomputable def annihilation (d : Module.Dual R M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.contractLeft d

lemma creation_apply (v : M) (x : ExteriorAlgebra R M) : creation v x = ExteriorAlgebra.ι R v * x := rfl

lemma annihilation_apply (d : Module.Dual R M) (x : ExteriorAlgebra R M) :
    annihilation d x = CliffordAlgebra.contractLeft d x := rfl

/-- **The CAR** `a(d) a*(v) + a*(v) a(d) = d(v)` (Dereziński, Section 7.1, p. 29, in creation-annihilation form). -/
theorem annihilation_creation_anticomm (d : Module.Dual R M) (v : M) :
    annihilation d ∘ₗ creation v + creation v ∘ₗ annihilation d = d v • LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, creation_apply, annihilation_apply, LinearMap.smul_apply,
    LinearMap.id_apply]
  rw [CliffordAlgebra.contractLeft_ι_mul]
  abel

/-- `a*(v) a*(w) + a*(w) a*(v) = 0`. -/
theorem creation_anticomm (v w : M) : creation (R := R) v ∘ₗ creation w + creation w ∘ₗ creation v = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, creation_apply, LinearMap.zero_apply, ← mul_assoc, ← add_mul,
    ExteriorAlgebra.ι_add_mul_swap, zero_mul]

/-- `a(d) a(d') + a(d') a(d) = 0`. -/
theorem annihilation_anticomm (d d' : Module.Dual R M) :
    annihilation (M := M) d ∘ₗ annihilation d' + annihilation d' ∘ₗ annihilation d = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, annihilation_apply, LinearMap.zero_apply]
  rw [CliffordAlgebra.contractLeft_comm, neg_add_cancel]

/-- **The vacuum** `1 ∈ Λ⁰` is killed by every annihilation operator. -/
theorem annihilation_one (d : Module.Dual R M) : annihilation d (1 : ExteriorAlgebra R M) = 0 := by
  simp [annihilation_apply, CliffordAlgebra.contractLeft_one]

/-- `a(d) a*(v) Ω = d(v) Ω` on the vacuum. -/
theorem annihilation_creation_one (d : Module.Dual R M) (v : M) :
    annihilation d (creation v (1 : ExteriorAlgebra R M)) = algebraMap R _ (d v) := by
  rw [creation_apply, mul_one, annihilation_apply, CliffordAlgebra.contractLeft_ι]

end Lightlike.OperatorAlgebras
