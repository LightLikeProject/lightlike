import Lightlike.SpinFoam.Removable
import Lightlike.SpinFoam.TwistedCohomologySU2

/-!
# A complex with `H² = 0` beyond the disc: two faces on two edges

The complex `twoFaceCx` has two edges `a, b` and two faces, the first bounded by `a` and the second
by `a b`. The holonomy map `(g_a, g_b) ↦ (g_a, g_a g_b)` is a bijection of `SU(2)²` preserving the
Haar measure, so the face holonomies are independent and Haar distributed. The character expansion of
the cut-off sum then has a single nonzero coefficient, at the labelling `c = 0`, where it is `1`.

## Main results

* `integral_haarE_two`: integration over `SU(2)^(Fin 2)` as an iterated integral.
* `coeff_twoFace`: the expansion coefficient is `1` at `c = 0` and `0` elsewhere.
* `absSummable_twoFace`: the expansion is absolutely summable, so `twoFaceCx` is removable
  (`removable_twoFace`), with `partitionN twoFaceCx N = 1` at every cut-off (`partitionN_twoFace`).
* `twoFace_H2_trivial`, `twoFace_premise`, `h2AbsSummable_twoFace`: `H² = 0` at the trivial
  connection, so the hypothesis `H2AbsSummable` of `Removable.lean` holds here with its premise
  satisfied, a case beyond the disc.
-/

open MeasureTheory Filter Topology Finset Lightlike.SU2 Lightlike.Spin4

namespace Lightlike.SpinFoam

/-- `SU(2)` is second countable (a subspace of the `2 × 2` matrices), so its Borel structure
is compatible with products. -/
instance : SecondCountableTopology SU2 := by
  have : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- Integration over `SU(2)^(Fin 2)` is an iterated integral. -/
lemma integral_haarE_two (f : SU2 → SU2 → ℂ) (hf : Continuous fun p : SU2 × SU2 => f p.1 p.2) :
    ∫ g : Fin 2 → SU2, f (g 0) (g 1) ∂haarE (Fin 2) = ∫ x, ∫ y, f x y ∂haarSU2 ∂haarSU2 := by
  have h := measurePreserving_piFinTwo (fun _ : Fin 2 => haarSU2)
  have := h.integral_comp' (fun p : SU2 × SU2 => f p.1 p.2)
  simp only [MeasurableEquiv.piFinTwo_apply] at this
  rw [haarE, this, integral_prod]
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The complex with two edges and two faces, bounded by `a` and by `a b`. -/
def twoFaceCx : Cell2 Unit (Fin 2) (Fin 2) where
  src _ := ()
  tgt _ := ()
  bdry f := if f = 0 then [(0, true)] else [(0, true), (1, true)]

/-- The expansion coefficient of `twoFaceCx` is `1` at `c = 0` and `0` elsewhere. -/
theorem coeff_twoFace (c : Fin 2 → ℕ) : coeff twoFaceCx c = if c = 0 then 1 else 0 := by
  unfold coeff
  have hint : ∀ g : Fin 2 → SU2, ∏ f, spinChar (c f) (hol g (twoFaceCx.bdry f)) =
      spinChar (c 0) (g 0) * spinChar (c 1) (g 0 * g 1) := by
    intro g
    simp [Fin.prod_univ_two, twoFaceCx, hol, lh]
  simp_rw [hint]
  rw [integral_haarE_two (fun x y => spinChar (c 0) x * spinChar (c 1) (x * y))
    ((continuous_spinChar _).comp continuous_fst |>.mul
      ((continuous_spinChar _).comp (continuous_fst.mul continuous_snd)))]
  have hin : ∀ x : SU2, ∫ y, spinChar (c 0) x * spinChar (c 1) (x * y) ∂haarSU2 =
      spinChar (c 0) x * (if c 1 = 0 then 1 else 0) := by
    intro x
    rw [integral_const_mul, integral_mul_left_eq_self (μ := haarSU2) (fun y => spinChar (c 1) y) x,
      integral_spinChar]
  simp_rw [hin]
  rw [integral_mul_const, integral_spinChar, Fin.prod_univ_two]
  by_cases h0 : c 0 = 0 <;> by_cases h1 : c 1 = 0 <;>
    simp [h0, h1, funext_iff, Fin.forall_fin_two]

/-- The expansion of `twoFaceCx` is absolutely summable. -/
theorem absSummable_twoFace : AbsSummable twoFaceCx := by
  refine summable_of_ne_finset_zero (s := {0}) fun c hc => ?_
  have : c ≠ 0 := by simpa using hc
  simp [coeff_twoFace, this]

/-- The two-face complex is removable (its partition function is `1` at every cut-off). -/
theorem removable_twoFace : Removable twoFaceCx :=
  removable_of_absSummable _ absSummable_twoFace

/-- The cut-off sum of `twoFaceCx` is `1` at every cut-off. -/
theorem partitionN_twoFace (N : ℕ) : partitionN twoFaceCx N = 1 := by
  rw [partitionN_eq_sum]
  have : ∀ c : Fin 2 → ℕ, (∏ f, ((c f : ℂ) + 1)) *
      ∫ g, ∏ f, spinChar (c f) (hol g (twoFaceCx.bdry f)) ∂haarE (Fin 2) =
      if c = 0 then 1 else 0 := fun c => coeff_twoFace c
  simp_rw [this]
  rw [Finset.sum_ite_eq' ]
  simp [Fintype.mem_piFinset]

/-- The trivial connection is flat on `twoFaceCx`. -/
theorem twoFace_flat : Flat twoFaceCx (fun _ => (1 : SU2)) := by
  intro f; fin_cases f <;> simp [twoFaceCx, hol, lh]

/-- **`H² = 0` for `twoFaceCx`.** The differential `d1` at the trivial connection is onto: the
variation `(X₀, X₁)` of the two faces is realised by the edge variation `(X₀, X₁ - X₀)`. -/
theorem twoFace_H2_trivial : Subsingleton (H2 adRep twoFaceCx (fun _ => (1 : SU2))) := by
  refine (d1_surjective_iff _ _ _).1 fun X => ?_
  refine ⟨fun e => if e = 0 then X 0 else X 1 - X 0, ?_⟩
  funext f
  fin_cases f <;> apply Subtype.ext <;> simp [d1, twoFaceCx, dword, lc, lh]

/-- **The hypothesis `H2AbsSummable` holds for `twoFaceCx` in a nontrivial case:** the premise
(a flat connection with `H² = 0`) is satisfied, and the conclusion is proved
(`absSummable_twoFace`). -/
theorem h2AbsSummable_twoFace : H2AbsSummable twoFaceCx := fun _ => absSummable_twoFace

/-- The premise of `H2AbsSummable` holds for `twoFaceCx`, so the hypothesis is not vacuous here. -/
theorem twoFace_premise :
    ∃ g : Fin 2 → SU2, Flat twoFaceCx g ∧ Subsingleton (H2 adRep twoFaceCx g) :=
  ⟨_, twoFace_flat, twoFace_H2_trivial⟩

end Lightlike.SpinFoam
