import Lightlike.Spacetime.SpaceForms.DeSitter
import Lightlike.Spacetime.InducedKilling
import Lightlike.Spacetime.ImmersionSection
import Lightlike.Spacetime.KillingMinkowski
import Lightlike.Spacetime.LeviCivita

/-!
# The Killing fields of de Sitter space

The Lorentz algebra `so(1, m+1)` of the ambient Minkowski space `ℝ × ℝ^{m+1}` (Library: `skewEta (m + 2)`, the
`η`-skew endomorphisms of `ℝ^{m+2}`, of dimension `(m + 2)(m + 1)/2`) acts on de Sitter space `ℝ × Sᵐ`: for every
`η`-skew `A` the field `dSField A` with `dι (dSField A) = A ∘ ι` (it exists because `A x` is `η`-orthogonal to `x` and
the image of `dι` is the orthogonal complement) is smooth (`contMDiff_dSField`, through `contMDiffAt_section_of_immersion`)
and a Killing field of the Levi-Civita connection (`isKillingAt_dSField`, through `isKillingAt_of_related`).

* `dSForm_eq_minkowski`: in the coordinates `κ = dSModelEquiv (m + 1)` of `ℝ × ℝ^{m+1}`, `η` is `minkowskiForm (m + 2)`;
* `eq_zero_of_vanish_dSIncl`: a linear map that vanishes on the hyperboloid vanishes (the hyperboloid spans);
* `exists_killing_deSitterSpace`: **`n (n + 1)/2` linearly independent smooth Killing fields**, `n = m + 1` the dimension,
  the images of a basis of `skewEta (m + 2)`.
-/

open Manifold Metric Bundle Set Module
open scoped ContDiff RealInnerProductSpace Manifold

set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace Lightlike

variable {m : ℕ}

/-- The coordinates `κ(a, x) = (a, x₀, …, x_m)` of the ambient space `ℝ × ℝ^{m+1}`. -/
abbrev dSCoord (m : ℕ) : DSAmb m ≃L[ℝ] (Fin (m + 2) → ℝ) := dSModelEquiv (m + 1)

/-- `κ(a, x) = (a, x₀, …, x_m)`. -/
theorem dSCoord_apply (u : DSAmb m) : dSCoord m u = Fin.cons u.1 (fun i => u.2 i) := rfl

/-- **The ambient form in coordinates** is the Minkowski form of `ℝ^{m+2}`. -/
theorem dSForm_eq_minkowski (u v : DSAmb m) : dSForm m u v = minkowskiForm (m + 2) (dSCoord m u) (dSCoord m v) := by
  rw [dSForm_apply, minkowskiForm_apply, Fin.sum_univ_succ, dSCoord_apply, dSCoord_apply]
  simp only [Fin.cons_zero, Fin.cons_succ, etaDiag, Fin.val_zero, ite_true, Fin.val_succ, Nat.add_one_ne_zero,
    ite_false, one_mul, neg_one_mul, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- An `η`-skew endomorphism of `ℝ^{m+2}`, transported to `ℝ × ℝ^{m+1}` by `κ`. -/
def dSGen (A : (Fin (m + 2) → ℝ) →L[ℝ] (Fin (m + 2) → ℝ)) : DSAmb m →L[ℝ] DSAmb m :=
  ((dSCoord m).symm : (Fin (m + 2) → ℝ) →L[ℝ] DSAmb m).comp (A.comp (dSCoord m : DSAmb m →L[ℝ] (Fin (m + 2) → ℝ)))

/-- The transport of an `η`-skew map of `ℝ^{m+2}` is skew for the form of `ℝ × ℝ^{m+1}`. -/
theorem dSGen_skew {A : (Fin (m + 2) → ℝ) →L[ℝ] (Fin (m + 2) → ℝ)} (hA : A ∈ skewEta (m + 2)) (u v : DSAmb m) :
    dSForm m (dSGen A u) v + dSForm m u (dSGen A v) = 0 := by
  simp only [dSForm_eq_minkowski, dSGen, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  exact hA _ _

/-- A skew map sends every point to an `η`-orthogonal vector. -/
theorem dSForm_self_skew {B : DSAmb m →L[ℝ] DSAmb m} (hB : ∀ u v, dSForm m (B u) v + dSForm m u (B v) = 0)
    (x : DSAmb m) : dSForm m x (B x) = 0 := by
  have h := hB x x
  rw [dSForm_symm (B x) x] at h
  linarith

variable {L : ℝ}

/-- **The field of de Sitter space induced by an ambient skew map** `B`: the tangent vector with `dι = B ι`. -/
def dSField (hL : L ≠ 0) (B : DSAmb m →L[ℝ] DSAmb m) (hB : ∀ u v, dSForm m (B u) v + dSForm m u (B v) = 0) :
    Π p : deSitterSpace m, TangentSpace (IdS m) p :=
  fun p => Classical.choose (exists_dι_dSIncl_eq hL p (B (dSIncl L p)) (dSForm_self_skew hB _))

/-- The defining property of the induced field: `dι (dSField B) = B ∘ ι`. -/
theorem dι_dSField (hL : L ≠ 0) (B : DSAmb m →L[ℝ] DSAmb m) (hB : ∀ u v, dSForm m (B u) v + dSForm m u (B v) = 0)
    (p : deSitterSpace m) : dι (I := IdS m) (dSIncl L) p (dSField hL B hB p) = B (dSIncl L p) :=
  Classical.choose_spec (exists_dι_dSIncl_eq hL p (B (dSIncl L p)) (dSForm_self_skew hB _))

/-- The induced field is smooth. -/
theorem contMDiff_dSField (hL : L ≠ 0) (B : DSAmb m →L[ℝ] DSAmb m)
    (hB : ∀ u v, dSForm m (B u) v + dSForm m u (B v) = 0) :
    ContMDiff (IdS m) ((IdS m).prod 𝓘(ℝ, Fin (m + 1) → ℝ)) ∞
      (fun q : deSitterSpace m => (⟨q, dSField hL B hB q⟩ : TangentBundle (IdS m) (deSitterSpace m))) := by
  intro p
  refine contMDiffAt_section_of_immersion (contMDiff_dSIncl L) (dι_dSIncl_injective hL p) ?_
  have : (fun q => dι (I := IdS m) (dSIncl L) q (dSField hL B hB q)) = fun q => B (dSIncl L q) :=
    funext (dι_dSField hL B hB)
  rw [this]
  exact B.contMDiff.contMDiffAt.comp p ((contMDiff_dSIncl L) p)

/-- **The induced field is a Killing field** of the Levi-Civita connection of de Sitter space, at every point. -/
theorem isKillingAt_dSField (hL : L ≠ 0) (B : DSAmb m →L[ℝ] DSAmb m)
    (hB : ∀ u v, dSForm m (B u) v + dSForm m u (B v) = 0) (p : deSitterSpace m) :
    IsKillingAt (leviCivita (deSitterSpaceMetric m L hL)) (deSitterSpaceMetric m L hL) (dSField hL B hB) p :=
  isKillingAt_of_related ⟨leviCivita_torsion _, leviCivita_compat _⟩ (contMDiff_dSIncl L)
    (deSitterSpaceMetric_apply hL) B hB (dι_dSField hL B hB)
    ((contMDiff_dSField hL B hB p).mdifferentiableAt (by simp))

/-- The point `e_k` of the unit sphere. -/
def sphereBasisPt (k : Fin (m + 1)) : SphereM m :=
  ⟨EuclideanSpace.single k 1, by simp⟩

/-- **The hyperboloid spans the ambient space**: a linear map vanishing at every point `ι(τ, ω)` is zero. -/
theorem eq_zero_of_vanish_dSIncl (hL : L ≠ 0) (T : DSAmb m →L[ℝ] DSAmb m) (hT : ∀ p, T (dSIncl L p) = 0) : T = 0 := by
  have h0 : ∀ k : Fin (m + 1), T (0, EuclideanSpace.single k 1) = 0 := by
    intro k
    have h := hT (0, sphereBasisPt k)
    have e : dSIncl L ((0 : ℝ), sphereBasisPt (m := m) k) = L • ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)) := by
      simp [dSIncl, dSPhi, sphereBasisPt]
    rw [e, map_smul] at h
    exact (smul_eq_zero.1 h).resolve_left hL
  have h1 : T (1, 0) = 0 := by
    have h := hT (1, sphereBasisPt 0)
    have e : dSIncl L ((1 : ℝ), sphereBasisPt (m := m) 0) =
        (L * Real.sinh 1) • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (m + 1)))) +
          (L * Real.cosh 1) • ((0 : ℝ), EuclideanSpace.single 0 (1 : ℝ)) := by
      simp [dSIncl, dSPhi, sphereBasisPt]
    rw [e, map_add, map_smul, map_smul, h0, smul_zero, add_zero] at h
    exact (smul_eq_zero.1 h).resolve_left (mul_ne_zero hL (Real.sinh_pos_iff.2 one_pos).ne')
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨a, x⟩ := u
  have hx : ((a, x) : DSAmb m) = a • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (m + 1)))) +
      ∑ k, x k • ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add, Prod.snd_sum]
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr x]
      simp
  rw [hx, map_add, map_smul, h1, smul_zero, zero_add, map_sum]
  exact Finset.sum_eq_zero fun k _ => by rw [map_smul, h0, smul_zero]

/-- **De Sitter space has `n (n + 1)/2` independent Killing fields**, `n = m + 1`: smooth fields, Killing for the
Levi-Civita connection at every point, and linearly independent. -/
theorem exists_killing_deSitterSpace (hL : L ≠ 0) :
    ∃ Y : Fin ((m + 1) * (m + 1 + 1) / 2) → Π p : deSitterSpace m, TangentSpace (IdS m) p,
      (∀ i, ContMDiff (IdS m) ((IdS m).prod 𝓘(ℝ, Fin (m + 1) → ℝ)) ∞
          (fun q : deSitterSpace m => (⟨q, Y i q⟩ : TangentBundle (IdS m) (deSitterSpace m))) ∧
        ∀ p, IsKillingAt (leviCivita (deSitterSpaceMetric m L hL)) (deSitterSpaceMetric m L hL) (Y i) p) ∧
      LinearIndependent ℝ Y := by
  have hcard : Fintype.card {q : Fin (m + 2) × Fin (m + 2) // q.1 < q.2} = (m + 1) * (m + 1 + 1) / 2 := by
    rw [card_pairs_lt, show m + 2 - 1 = m + 1 by omega, mul_comm]
  obtain ⟨b⟩ : Nonempty (Basis (Fin ((m + 1) * (m + 1 + 1) / 2)) ℝ (skewEta (m + 2))) :=
    ⟨((Pi.basisFun ℝ {q : Fin (m + 2) × Fin (m + 2) // q.1 < q.2}).map
      ((skewEtaEquiv (m + 2)).trans (antisymmEquiv (m + 2))).symm).reindex
      (Fintype.equivOfCardEq (by rw [hcard, Fintype.card_fin]))⟩
  have hB : ∀ i, ∀ u v, dSForm m (dSGen ((b i : skewEta (m + 2)) : (Fin (m + 2) → ℝ) →L[ℝ] (Fin (m + 2) → ℝ)) u) v +
      dSForm m u (dSGen ((b i : skewEta (m + 2)) : (Fin (m + 2) → ℝ) →L[ℝ] (Fin (m + 2) → ℝ)) v) = 0 := fun i => dSGen_skew (b i).2
  let Y : Fin ((m + 1) * (m + 1 + 1) / 2) → Π p : deSitterSpace m, TangentSpace (IdS m) p :=
    fun i => dSField hL (dSGen ((b i : skewEta (m + 2)) : (Fin (m + 2) → ℝ) →L[ℝ] (Fin (m + 2) → ℝ))) (hB i)
  refine ⟨Y, fun i => ⟨contMDiff_dSField hL _ (hB i), isKillingAt_dSField hL _ (hB i)⟩, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- the ambient map `T = Σ cᵢ Bᵢ` vanishes on the hyperboloid
  set T : DSAmb m →L[ℝ] DSAmb m := ∑ i, c i • dSGen ((b i : skewEta (m + 2)) : (Fin (m + 2) → ℝ) →L[ℝ] (Fin (m + 2) → ℝ)) with hTdef
  have hT : ∀ p, T (dSIncl L p) = 0 := by
    intro p
    have h2 : (∑ i, c i • Y i) p = 0 := congrFun hc p
    rw [Finset.sum_apply] at h2
    simp only [Pi.smul_apply] at h2
    have h3 := congrArg (dι (I := IdS m) (dSIncl L) p) h2
    erw [map_sum, map_zero] at h3
    rw [hTdef, sum_apply, ← h3]
    refine Finset.sum_congr rfl fun x _ => ?_
    erw [map_smul, dι_dSField]
    rfl
  have hT0 := eq_zero_of_vanish_dSIncl hL T hT
  -- so `S = Σ cᵢ bᵢ` is zero on `ℝ^{m+2}`
  have hS : (∑ i, c i • b i : skewEta (m + 2)) = 0 := by
    apply Subtype.ext
    refine ContinuousLinearMap.ext fun y => ?_
    have h := congrArg (fun T' : DSAmb m →L[ℝ] DSAmb m => dSCoord m (T' ((dSCoord m).symm y))) hT0
    simp only [hTdef, dSGen, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, map_sum, map_smul, zero_apply, map_zero] at h
    simpa [Submodule.coe_sum] using h
  intro i
  have h := congrArg (fun v => b.repr v i) hS
  simpa [map_sum, Finsupp.single_apply] using h

end Lightlike
