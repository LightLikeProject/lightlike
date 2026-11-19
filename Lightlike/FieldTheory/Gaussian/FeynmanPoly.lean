import Lightlike.FieldTheory.Gaussian.FeynmanExpansion

/-!
# The Feynman expansion for a general polynomial potential

Polyak, *Feynman diagrams for pedestrians and mathematicians*, arXiv:math/0406251v1, §2.8, p. 8: "the `k`-th degree
term `U_{i₁…i_k} x_{i₁} ⋯ x_{i_k}` of `U` will lead to an appearance of `k`-valent vertices representing factors
`U_{i₁…i_k}`"; the coefficient of `ħ^m` is then the sum over vertex types, labels and pairings of the legs (the same
argument as (18), p. 7).

Here `U = Σ_{κ : K} V_κ` for a finite family of homogeneous parts, `V_κ` of degree `d κ` with coefficient tensor
`c κ` (`polyPot`). For a choice `κ : Fin m → K` of the types of the `m` vertices, the legs are
`Σ_v Fin (d (κ v)) ≃ Fin (Σ_v d (κ v))` (`legLabelsSigma`), and
* `integral_polyPot_pow`: `E_S[U^m] = Σ_{κ : Fin m → K} Σ_{i} (∏_v c_{κ v}(i v)) Σ_c ∏_{(p, q) ∈ c} S_{ℓ_p ℓ_q}`, the sum
  over the vertex types, the labellings `i v : Fin (d (κ v)) → ι` of the vertices, and the full Wick contractions
  `c` of all the legs.

Difference from the source (weaker): labelled contractions, not Feynman graphs with `1/|Aut Γ|` (Proposition 2.17,
p. 9); Polyak's restriction to vertices of valence `≥ 3` is not needed for a fixed order `m`.
-/

namespace Lightlike.FieldTheory

open MeasureTheory Finset ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Fintype K]

/-- A polynomial potential as a finite sum of homogeneous parts: `U(x) = Σ_κ Σ_{i : Fin (d κ) → ι} c_κ(i) ∏_a x_{i a}`. -/
noncomputable def polyPot (d : K → ℕ) (c : (κ : K) → (Fin (d κ) → ι) → ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ κ, homogPoly (c κ) x

/-- The labels of the legs of `m` vertices of types `κ` labelled by `i`, indexed by `Fin (Σ_v d (κ v))`. -/
def legLabelsSigma {d : K → ℕ} {m : ℕ} (κ : Fin m → K) (i : (v : Fin m) → Fin (d (κ v)) → ι)
    (k : Fin (∑ v, d (κ v))) : ι :=
  i (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2

lemma prod_legLabelsSigma {d : K → ℕ} {m : ℕ} (κ : Fin m → K) (i : (v : Fin m) → Fin (d (κ v)) → ι)
    (x : EuclideanSpace ℝ ι) :
    ∏ k : Fin (∑ v, d (κ v)), x (legLabelsSigma κ i k) = ∏ v, ∏ a, x (i v a) := by
  rw [← Fintype.prod_sigma']
  exact Fintype.prod_equiv finSigmaFinEquiv.symm _ _ fun k => rfl

/-- **`U^m` as a sum over vertex types and labellings.** -/
lemma polyPot_pow (d : K → ℕ) (c : (κ : K) → (Fin (d κ) → ι) → ℝ) (m : ℕ) (x : EuclideanSpace ℝ ι) :
    polyPot d c x ^ m = ∑ κ : Fin m → K, ∑ i : (v : Fin m) → Fin (d (κ v)) → ι,
      (∏ v, c (κ v) (i v)) * mono (List.ofFn (legLabelsSigma κ i)) x := by
  rw [polyPot, ← Fin.prod_const, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [homogPoly]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib, mono_ofFn, prod_legLabelsSigma]

/-- **The Feynman expansion for a polynomial potential**: `E_S[U^m]` is the sum over the vertex types, the
labellings and the full Wick contractions of all the legs. -/
theorem integral_polyPot_pow {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (d : K → ℕ)
    (c : (κ : K) → (Fin (d κ) → ι) → ℝ) (m : ℕ) :
    ∫ x, polyPot d c x ^ m ∂(multivariateGaussian 0 S) =
      ∑ κ : Fin m → K, ∑ i : (v : Fin m) → Fin (d (κ v)) → ι,
        (∏ v, c (κ v) (i v)) * pairSum S (legLabelsSigma κ i) := by
  simp_rw [polyPot_pow]
  rw [integral_finsetSum _ fun κ _ => integrable_finset_sum _ fun i _ => (integrable_mono S _).const_mul _]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [integral_finsetSum _ fun i _ => (integrable_mono S _).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, ← moment, moment_ofFn_eq_pairSum_of_posSemidef hS]

end Lightlike.FieldTheory
