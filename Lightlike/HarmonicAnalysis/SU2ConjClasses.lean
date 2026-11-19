import Lightlike.HarmonicAnalysis.WeylIntegrationSU2

/-!
# The conjugacy classes of SU(2) are an interval

`su2_conjClasses_homeomorph`: the half-trace `½ tr` induces a homeomorphism from the space of conjugacy
classes of `SU(2)` (the quotient of `SU(2)` by conjugation, with the quotient topology) onto `[-1, 1]`.

## References

* C. Teleman, *Representation Theory* (lecture notes, Cambridge, Lent 2005), Lecture 20, §(20.3),
  Proposition 20.4.
-/

namespace Lightlike.HarmonicAnalysis

noncomputable section

/-- Every `g ∈ SU(2)` is conjugate to the diagonal element with angle `arccos (½ tr g)`. -/
theorem exists_conj_torusExp_arccos (g : SU2) :
    ∃ h : SU2, g = h * Spin4.torusExp (Real.arccos (su2HalfTr g)) * h⁻¹ := by
  obtain ⟨h, θ, h0, hπ, hg⟩ := exists_conj_torusExp_Icc g
  refine ⟨h, ?_⟩
  have hx : su2HalfTr g = Real.cos θ := by rw [hg, su2HalfTr_conj, su2HalfTr_torusExp]
  rw [hx, Real.arccos_cos h0 hπ]
  exact hg

/-- Two elements of SU(2) with the same half-trace are conjugate. -/
theorem su2_isConj_of_halfTr_eq {a b : SU2} (h : su2HalfTr a = su2HalfTr b) : IsConj a b := by
  obtain ⟨h1, ha⟩ := exists_conj_torusExp_arccos a
  obtain ⟨h2, hb⟩ := exists_conj_torusExp_arccos b
  rw [isConj_iff]
  refine ⟨h2 * h1⁻¹, ?_⟩
  rw [hb, ← h]
  nth_rewrite 1 [ha]
  group

/-- Two elements of SU(2) are conjugate iff they have the same half-trace. -/
theorem su2_isConj_iff {a b : SU2} : IsConj a b ↔ su2HalfTr a = su2HalfTr b := by
  refine ⟨fun h => ?_, su2_isConj_of_halfTr_eq⟩
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (su2HalfTr_conj c a).symm

/-- The half-trace on the space of conjugacy classes. -/
def su2ClassHalfTr : Quotient (IsConj.setoid SU2) → Set.Icc (-1 : ℝ) 1 :=
  Quotient.lift (fun g : SU2 => (⟨su2HalfTr g, su2HalfTr_mem_Icc g⟩ : Set.Icc (-1 : ℝ) 1))
    fun _ _ hab => Subtype.ext (su2_isConj_iff.1 hab)

lemma su2ClassHalfTr_mk (g : SU2) :
    (su2ClassHalfTr (Quotient.mk (IsConj.setoid SU2) g) : ℝ) = su2HalfTr g := rfl

lemma continuous_su2ClassHalfTr : Continuous su2ClassHalfTr :=
  Continuous.quotient_lift (continuous_su2HalfTr.subtype_mk _) _

lemma bijective_su2ClassHalfTr : Function.Bijective su2ClassHalfTr := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y fun a b hab => ?_
    exact Quotient.sound (su2_isConj_of_halfTr_eq (congrArg Subtype.val hab))
  · rintro ⟨x, hx⟩
    refine ⟨Quotient.mk (IsConj.setoid SU2) (Spin4.torusExp (Real.arccos x)), Subtype.ext ?_⟩
    show su2HalfTr (Spin4.torusExp (Real.arccos x)) = x
    rw [su2HalfTr_torusExp, Real.cos_arccos hx.1 hx.2]

/-- **The conjugacy classes of SU(2).** The half-trace induces a homeomorphism from the space of conjugacy
classes of `SU(2)` onto the interval `[-1, 1]`. -/
theorem su2_conjClasses_homeomorph :
    ∃ e : Quotient (IsConj.setoid SU2) ≃ₜ Set.Icc (-1 : ℝ) 1,
      ∀ g : SU2, (e (Quotient.mk (IsConj.setoid SU2) g) : ℝ) = su2HalfTr g :=
  ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective su2ClassHalfTr bijective_su2ClassHalfTr)
    continuous_su2ClassHalfTr, fun _ => rfl⟩

end

end Lightlike.HarmonicAnalysis
