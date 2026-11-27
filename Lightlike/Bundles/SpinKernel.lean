import Mathlib
import Lightlike.Bundles.SpinGroup

/-!
# The kernel of the vector action `Spin(n) → SO(n)` is `{±1}`

For the Clifford algebra `Cl(ℝⁿ, -‖·‖²)` and Mathlib's `spinGroup`, a spin element whose vector
action `v ↦ s v s⋆` (`vecConj`, `vectorAction`) is the identity is `1` or `-1`: it commutes with
every generator (`s⋆ = s⁻¹`), it is even, so it is a scalar
(`Lightlike.Dirac.mem_bot_of_commute_of_even`), and a scalar `r` with `r² = 1` is `±1`.

* `vecConj_eq_id_iff`: `vecConj s = id ↔ s = 1 ∨ s = -1` (as elements of the Clifford algebra);
* `vectorAction_eq_one_iff`: the same for `vectorAction n s = 1`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter I, Theorem 2.10 (the kernel of
  `Spin(n) → SO(n)` is `{±1}`).
-/

open CliffordAlgebra

namespace Lightlike.Dirac

variable {n : ℕ}

/-- The scalars embed in `Cl(ℝⁿ, -‖·‖²)`. -/
lemma algebraMap_injective_Qneg : Function.Injective (algebraMap ℝ (CliffordAlgebra (Qneg n))) := by
  have : Nontrivial (CliffordAlgebra (Qneg n)) :=
    (CliffordAlgebra.equivExterior (Qneg n)).toEquiv.nontrivial
  exact (algebraMap ℝ _).injective

/-- A spin element that fixes every vector commutes with every vector: `s ι(v) = ι(v) s`. -/
lemma commute_ι_of_vecConj_eq (s : spinGroup (Qneg n)) {v : E n} (hv : vecConj s v = v) :
    (s : CliffordAlgebra (Qneg n)) * ι (Qneg n) v = ι (Qneg n) v * s := by
  have h := (vecConj_eq_iff s v v).1 hv
  calc (s : CliffordAlgebra (Qneg n)) * ι (Qneg n) v
      = (s : CliffordAlgebra (Qneg n)) * ι (Qneg n) v *
          (star (s : CliffordAlgebra (Qneg n)) * s) := by
        rw [spinGroup.star_mul_self_of_mem s.2, mul_one]
    _ = ι (Qneg n) v * s := by rw [← mul_assoc, h]

/-- **The kernel of the vector action is `{±1}`**: a spin element fixes every vector exactly when
it is `1` or `-1`. -/
theorem vecConj_eq_id_iff (s : spinGroup (Qneg n)) :
    (∀ v, vecConj s v = v) ↔
      (s : CliffordAlgebra (Qneg n)) = 1 ∨ (s : CliffordAlgebra (Qneg n)) = -1 := by
  constructor
  · intro hs
    have hc : ∀ a, cgen a * (s : CliffordAlgebra (Qneg n)) = (s : CliffordAlgebra (Qneg n)) * cgen a :=
      fun a =>
      (commute_ι_of_vecConj_eq s (hs (e a))).symm
    obtain ⟨r, hr⟩ := Algebra.mem_bot.1 (mem_bot_of_commute_of_even hc (spinGroup.involute_eq s.2))
    have h1 := spinGroup.star_mul_self_of_mem s.2
    rw [← hr, star_algebraMap, ← map_mul] at h1
    have hr2 : r * r = 1 := algebraMap_injective_Qneg
      (by simpa using h1)
    rcases mul_self_eq_one_iff.1 hr2 with h | h
    · left; rw [← hr, h, map_one]
    · right; rw [← hr, h, map_neg, map_one]
  · rintro (h | h) v
    · rw [vecConj_eq_iff, h, star_one, one_mul, mul_one]
    · rw [vecConj_eq_iff, h, star_neg, star_one, neg_mul, one_mul, mul_neg, mul_one, neg_neg]

/-- **The kernel of `vectorAction : Spin(n) →* GL(ℝⁿ)` is `{±1}`.** -/
theorem vectorAction_eq_one_iff (s : spinGroup (Qneg n)) :
    vectorAction n s = 1 ↔
      (s : CliffordAlgebra (Qneg n)) = 1 ∨ (s : CliffordAlgebra (Qneg n)) = -1 := by
  rw [← vecConj_eq_id_iff]
  constructor
  · intro h v
    have hv := congrArg (fun f : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) => f (WithLp.ofLp v)) h
    apply ι_injective_Qneg
    rw [ι_vecConj, ← vectorAction_apply]
    simp only [LinearEquiv.coe_one, id] at hv
    rw [hv]
  · intro h
    ext v : 1
    apply (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.injective
    apply ι_injective_Qneg
    change ι (Qneg n) (WithLp.toLp 2 (vectorAction n s v)) = ι (Qneg n) (WithLp.toLp 2 v)
    rw [vectorAction_apply, ← ι_vecConj, h]

/-- A unit vector squares to `-1` in `Cl(ℝⁿ, -‖·‖²)`. -/
lemma ι_mul_self_of_norm_eq_one {u : E n} (hu : ‖u‖ = 1) : ι (Qneg n) u * ι (Qneg n) u = -1 := by
  rw [ι_sq_scalar, Qneg_apply, hu]
  simp

/-- A unit vector as a unit of the Clifford algebra (its inverse is `-u`). -/
noncomputable def vecUnit {u : E n} (hu : ‖u‖ = 1) : (CliffordAlgebra (Qneg n))ˣ where
  val := ι (Qneg n) u
  inv := -ι (Qneg n) u
  val_inv := by rw [mul_neg, ι_mul_self_of_norm_eq_one hu, neg_neg]
  inv_val := by rw [neg_mul, ι_mul_self_of_norm_eq_one hu, neg_neg]

/-- **The product of two unit vectors is a spin element.** -/
theorem ι_mul_ι_mem_spinGroup {u v : E n} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ι (Qneg n) u * ι (Qneg n) v ∈ spinGroup (Qneg n) := by
  refine spinGroup.mem_iff.2 ⟨pinGroup.mem_iff.2 ⟨?_, ?_⟩, ?_⟩
  · refine ⟨vecUnit hu * vecUnit hv, ?_, rfl⟩
    exact mul_mem (Subgroup.subset_closure ⟨u, rfl⟩) (Subgroup.subset_closure ⟨v, rfl⟩)
  · have hs : star (ι (Qneg n) u * ι (Qneg n) v) = ι (Qneg n) v * ι (Qneg n) u := by
      rw [star_mul, star_ι, star_ι, neg_mul_neg]
    refine Unitary.mem_iff.2 ⟨?_, ?_⟩
    · rw [hs, mul_assoc, ← mul_assoc (ι (Qneg n) u), ι_mul_self_of_norm_eq_one hu, neg_one_mul,
        mul_neg, ι_mul_self_of_norm_eq_one hv, neg_neg]
    · rw [hs, mul_assoc, ← mul_assoc (ι (Qneg n) v), ι_mul_self_of_norm_eq_one hv, neg_one_mul,
        mul_neg, ι_mul_self_of_norm_eq_one hu, neg_neg]
  · change _ ∈ (CliffordAlgebra.even (Qneg n)).toSubmodule
    rw [CliffordAlgebra.even_toSubmodule]
    exact ι_mul_ι_mem_evenOdd_zero _ u v

/-- Non-vacuity and trust check: for `n ≥ 1` the kernel of the vector action contains `-1 = e₀e₀`,
which is not `1`; so the kernel is all of `{±1}`. -/
example [NeZero n] : ∃ s : spinGroup (Qneg n), (∀ v, vecConj s v = v) ∧
    (s : CliffordAlgebra (Qneg n)) ≠ 1 := by
  have h0 : ‖e (0 : Fin n)‖ = 1 := by simp [e]
  refine ⟨⟨_, ι_mul_ι_mem_spinGroup h0 h0⟩, (vecConj_eq_id_iff _).2 (Or.inr ?_), ?_⟩
  · exact ι_mul_self_of_norm_eq_one h0
  · change ι (Qneg n) (e 0) * ι (Qneg n) (e 0) ≠ 1
    rw [ι_mul_self_of_norm_eq_one h0]
    intro h
    have h2 : (algebraMap ℝ (CliffordAlgebra (Qneg n))) (-1) = algebraMap ℝ _ 1 := by
      rw [map_neg, map_one, h]
    have := algebraMap_injective_Qneg h2
    norm_num at this

end Lightlike.Dirac
