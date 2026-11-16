import Lightlike.Regge.Conv3.CurvatureCoeffs
import Lightlike.Regge.Linear3.FierzPauli

/-!
# The second `η`-coefficient of the curvature density is the Fierz–Pauli density plus a divergence

For symmetric `h`, `∂h`, `∂∂h` the first coefficient is `F₁ = ½ (Σ ∂_i ∂_j h_ij - Σ ∂_k ∂_k h_ii)` (`F1_eq`), and the second
is `F₂ = fpDens ∂h + divTp h ∂h ∂∂h` (`F2_eq`), where `divTp` is the divergence of the explicit field
`T'_m = ½ tr h Σ_c ∂_c h_cm - ½ tr h ∂_m tr h - ½ Σ_ab h_ab ∂_a h_bm + Σ_a h_am ∂_a tr h + Σ_ab h_ab ∂_m h_ab - (3/2) Σ_ac h_am ∂_c h_ac`
(`∂_m h_ab = dh m a b`, `∂_m ∂_c h_de = dd m c d e`). The identity is polynomial; it was found with exact arithmetic
(`scripts/regge/eh_jet_poly_check.py`) and is proved here by expanding the index sums.

## Main results

* `divTp`: the divergence of `T'`.
* `R1_eq`, `F2_poly`: the polynomial identities for the coefficients.
* `F1_eq`, `F2_eq`: the coefficients `F1`, `F2` of `FetaTaylor`.

**Limits.** Dimension 3; the symmetry hypotheses are those of the jet of a `C²` symmetric field; nothing about integrals.
-/

open Matrix Finset Real
open scoped ContDiff
namespace Lightlike.Regge.Conv3
open Lightlike.Regge.Linear3

variable (H : Fin 3 → Fin 3 → ℝ) (dh : Fin 3 → Fin 3 → Fin 3 → ℝ) (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)

/-- The divergence of the periodic field `T'`. -/
noncomputable def divTp : ℝ := ∑ m, (
  1 / 2 * ((∑ a, dh m a a) * (∑ c, dh c c m) + trH H * ∑ c, dd m c c m)
  - 1 / 2 * ((∑ a, dh m a a) * (∑ i, dh m i i) + trH H * ∑ i, dd m m i i)
  - 1 / 2 * ∑ a, ∑ b, (dh m a b * dh a b m + H a b * dd m a b m)
  + ∑ a, ∑ i, (dh m a m * dh a i i + H a m * dd m a i i)
  + ∑ a, ∑ b, (dh m a b * dh m a b + H a b * dd m m a b)
  - 3 / 2 * ∑ a, ∑ c, (dh m a m * dh c a c + H a m * dd m c a c))

theorem R1_eq (hd1 : ∀ k l i j, dd k l i j = dd l k i j) :
    R1 dd = (∑ i, ∑ j, dd i j i j) - ∑ k, ∑ i, dd k k i i := by
  simp only [R1, I1, D1, Bdd, Fin.sum_univ_three]
  simp only [hd1 1 0, hd1 2 0, hd1 2 1]
  ring

set_option maxRecDepth 100000 in
theorem F2_poly (hH : ∀ i j, H i j = H j i) (hd : ∀ k i j, dh k i j = dh k j i)
    (hd1 : ∀ k l i j, dd k l i j = dd l k i j) (hd2 : ∀ k l i j, dd k l i j = dd k l j i) :
    R2 H dh dd + R1 dd * trH H / 2 = fpDens dh + divTp H dh dd := by
  simp only [R2, R1, I1, I2, D1, D2, Gam1, Bdd, Bdh, trH, divTp, fpDens, Fin.sum_univ_three,
    Fin.isValue, Fin.reduceEq, ↓reduceIte]
  simp only [hH 1 0, hH 2 0, hH 2 1, hd 0 1 0, hd 0 2 0, hd 0 2 1, hd 1 1 0, hd 1 2 0, hd 1 2 1,
    hd 2 1 0, hd 2 2 0, hd 2 2 1, hd1 1 0, hd1 2 0, hd1 2 1, hd2 _ _ 1 0, hd2 _ _ 2 0, hd2 _ _ 2 1]
  ring

/-- **The first coefficient of the curvature density.** -/
theorem F1_eq (J : Jet3) (hd1 : ∀ k l i j, J.2.2 k l i j = J.2.2 l k i j) :
    F1 J = 1 / 2 * ((∑ i, ∑ j, J.2.2 i j i j) - ∑ k, ∑ i, J.2.2 k k i i) := by
  rw [(F_eq J).1, R1_eq J.2.2 hd1]
  ring

/-- **The second coefficient of the curvature density.** -/
theorem F2_eq (J : Jet3) (hH : ∀ i j, J.1 i j = J.1 j i) (hd : ∀ k i j, J.2.1 k i j = J.2.1 k j i)
    (hd1 : ∀ k l i j, J.2.2 k l i j = J.2.2 l k i j) (hd2 : ∀ k l i j, J.2.2 k l i j = J.2.2 k l j i) :
    F2 J = fpDens J.2.1 + divTp J.1 J.2.1 J.2.2 := by
  rw [(F_eq J).2, F2_poly J.1 J.2.1 J.2.2 hH hd hd1 hd2]

end Lightlike.Regge.Conv3
