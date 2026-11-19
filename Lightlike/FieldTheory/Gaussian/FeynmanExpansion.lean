import Lightlike.FieldTheory.Gaussian.WickSemidef

/-!
# The Feynman expansion of a finite-dimensional Gaussian integral

Source (read 19 November 2026): M. Polyak, *Feynman diagrams for pedestrians and mathematicians*, arXiv:math/0406251v1,
§2.3, Theorem 2.8 (Wick), p. 5; §2.6 (a cubic potential `U = Σ U_{ijk} x_i x_j x_k`), eq. (18), p. 7: the coefficient
of `ħⁿ` in `Z_U = ∫ e^{-½⟨Ax, x⟩ + ħ U(x)} dx` is `(Z₀/n!) Σ_{labels} U ⋯ U Σ_{pairings} ∏ (A⁻¹)_{i_k i_l}`, the sum
over the labels of the `3n` legs of `n` trivalent vertices and over the pairings of the legs ("in general, for the
coefficient of `ħⁿ` we get the same formula", p. 8); §2.8 extends this to `k`-valent vertices for the degree-`k`
terms of `U`.

Here, for a homogeneous polynomial of degree `d` on `ℝ^ι`, `V(x) = Σ_{i : Fin d → ι} c_i x_{i 0} ⋯ x_{i (d-1)}`
(`homogPoly`), and the centred Gaussian measure with covariance `S ≥ 0` (`S = A⁻¹`):
* `integral_homogPoly_pow`: `E_S[V^m] = Σ_{i : Fin m → Fin d → ι} (∏_v c_{i_v}) Σ_c ∏_{(p, q) ∈ c} S_{ℓ_p ℓ_q}`, the sum
  over the labellings `i` of the `m` vertices (`ℓ = legLabels i` the labels of their `md` legs) and the full Wick
  contractions `c` of the legs (`pairSum`); `E_S[V^m]/m!` is the coefficient of `ħ^m` in `Z_V/Z₀`.

Difference from the source (representation): the coefficient of `ħ^m` is stated as the moment `E_S[V^m]` of the
normalised Gaussian measure (Polyak's `Z₀ (1/m!) ∂-form` of (15), (18), with the convergence issues he sets aside not
arising). Difference (weaker): `V` is homogeneous of one degree `d` (Polyak's §2.8 allows a sum of degrees `≥ 3`), and
the sum is over labelled contractions, not over Feynman graphs with `1/|Aut Γ|` (Proposition 2.17, p. 9).
-/

namespace Lightlike.FieldTheory

open MeasureTheory Finset ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A homogeneous polynomial of degree `d` on `ℝ^ι` with coefficient tensor `c`:
`V(x) = Σ_{i : Fin d → ι} c_i x_{i 0} ⋯ x_{i (d-1)}`. -/
noncomputable def homogPoly {d : ℕ} (c : (Fin d → ι) → ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, c i * ∏ a, x (i a)

/-- The labels of the `m d` legs of `m` vertices of degree `d` labelled by `i`. -/
def legLabels {m d : ℕ} (i : Fin m → Fin d → ι) (k : Fin (m * d)) : ι :=
  i (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

lemma prod_legLabels {m d : ℕ} (i : Fin m → Fin d → ι) (x : EuclideanSpace ℝ ι) :
    ∏ k : Fin (m * d), x (legLabels i k) = ∏ v, ∏ a, x (i v a) := by
  rw [← Fintype.prod_prod_type']
  exact Fintype.prod_equiv finProdFinEquiv.symm _ _ fun k => rfl

lemma mono_ofFn {n : ℕ} (f : Fin n → ι) (x : EuclideanSpace ℝ ι) :
    mono (List.ofFn f) x = ∏ k, x (f k) := by
  rw [mono_eq_prod]
  exact Fintype.prod_equiv (finCongr List.length_ofFn) _ _ fun k => by simp [List.getElem_ofFn]; rfl

/-- **`V^m` as a sum over vertex labellings**: `V(x)^m = Σ_i (∏_v c_{i_v}) x_{ℓ_0} ⋯ x_{ℓ_{md-1}}`. -/
lemma homogPoly_pow {d : ℕ} (c : (Fin d → ι) → ℝ) (m : ℕ) (x : EuclideanSpace ℝ ι) :
    homogPoly c x ^ m = ∑ i : Fin m → Fin d → ι, (∏ v, c (i v)) * mono (List.ofFn (legLabels i)) x := by
  rw [homogPoly, ← Fin.prod_const, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib, mono_ofFn, prod_legLabels]

lemma pairSum_comp_cast (S : Matrix ι ι ℝ) {n n' : ℕ} (h : n' = n) (f : Fin n → ι) :
    pairSum S (f ∘ Fin.cast h) = pairSum S f := by
  subst h; rfl

/-- Wick's theorem for `List.ofFn`, positive semidefinite covariance. -/
lemma moment_ofFn_eq_pairSum_of_posSemidef {S : Matrix ι ι ℝ} (hS : S.PosSemidef) {n : ℕ} (f : Fin n → ι) :
    moment S (List.ofFn f) = pairSum S f := by
  rw [moment_eq_pairSum_of_posSemidef hS]
  have h : (List.ofFn f).get = f ∘ Fin.cast List.length_ofFn := by
    funext k; simp [List.get_eq_getElem, List.getElem_ofFn]; rfl
  rw [h, pairSum_comp_cast]

/-- **The Feynman expansion of the moments of a polynomial** (Polyak eq. (18), p. 7, for degree `d`):
`E_S[V^m] = Σ_{i : Fin m → Fin d → ι} (∏_v c_{i_v}) Σ_{c full} ∏_{(p, q) ∈ c} S_{ℓ_p ℓ_q}`. -/
theorem integral_homogPoly_pow {S : Matrix ι ι ℝ} (hS : S.PosSemidef) {d : ℕ} (c : (Fin d → ι) → ℝ) (m : ℕ) :
    ∫ x, homogPoly c x ^ m ∂(multivariateGaussian 0 S) =
      ∑ i : Fin m → Fin d → ι, (∏ v, c (i v)) * pairSum S (legLabels i) := by
  simp_rw [homogPoly_pow]
  rw [integral_finsetSum _ fun i _ => (integrable_mono S _).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, ← moment, moment_ofFn_eq_pairSum_of_posSemidef hS]

/-- For an odd number of legs the moment vanishes: there is no full contraction. -/
theorem integral_homogPoly_pow_of_odd {S : Matrix ι ι ℝ} (hS : S.PosSemidef) {d : ℕ} (c : (Fin d → ι) → ℝ)
    {m : ℕ} (hodd : Odd (m * d)) : ∫ x, homogPoly c x ^ m ∂(multivariateGaussian 0 S) = 0 := by
  rw [integral_homogPoly_pow hS]
  refine Finset.sum_eq_zero fun i _ => ?_
  haveI hempty : IsEmpty {c : WickContraction (m * d) // c.IsFull} := by
    rw [← Fintype.card_eq_zero_iff]; exact WickContraction.card_of_isfull_odd hodd
  rw [pairSum, Fintype.sum_empty, mul_zero]

end Lightlike.FieldTheory
