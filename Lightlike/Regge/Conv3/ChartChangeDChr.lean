import Lightlike.Regge.Conv3.ChartChange
import Lightlike.Regge.Conv3.FlatStarJet
import Lightlike.Regge.Conv3.JetCurvature

/-!
# The derivative of the Christoffel symbols in the shifted flat form

For a coordinate metric `g` on `U` and `m ∈ U`, the derivative of the Christoffel symbols at `m` is
`∂_μ Γ^ρ_{νσ} = ½ Σ_l g^{ρl} (S_{νμ lσ} + S_{σμ lν} - S_{lμ νσ}) - Σ_r Γ^ρ_{μ r} Γ^r_{νσ}` with the
shifted second derivatives `S = Sdd g m` (`dChr_eq_flat`). The proof is index-free: the metric
compatibility `∂_p g_{qa} = Σ_d (g_{qd} Γ^d_{pa} + g_{ad} Γ^d_{pq})` and the contraction of the inverse
metric with the metric (`inv_contract`) turn `dChr` into the stated form, and the remaining terms cancel
by the symmetry of the Christoffel symbols in their lower indices. (An earlier proof by a case split on the
81 index values, with `field_simp; ring` on the adjugate, produced a proof term of 280 MB.)

## Main results

* `inv_contract`: `Σ_l (g m)⁻¹ r l (Σ_x g m l x f x) = f r`.
* `dChr_eq_flat`: the shifted flat form of `dChr` for all indices.

**Limits.** Local to one point `m`; a coordinate metric (smooth, with invertible Gram matrix at `m`).
-/

open Real Matrix Lightlike
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {m : Fin 3 → ℝ} {U : Set (Fin 3 → ℝ)}

/-- Contraction of the inverse metric with the metric. -/
theorem inv_contract (hg : IsCoordMetric g U) (hm : m ∈ U) (r : Fin 3) (f : Fin 3 → ℝ) :
    ∑ l, (g m)⁻¹ r l * (∑ x, g m l x * f x) = f r := by
  have hGiG : ∀ r x, ∑ l, (g m)⁻¹ r l * g m l x = if r = x then 1 else 0 := fun r x => by
    have := congrFun (congrFun (Matrix.nonsing_inv_mul (g m) (hg.isUnit_det m hm)) r) x
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ x, ∑ l, (g m)⁻¹ r l * (g m l x * f x) = (if r = x then 1 else 0) * f x := fun x => by
    rw [← hGiG r x, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [this]
  simp

theorem sum_aux (a : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ) (B : ℝ) :
    (-∑ i, ∑ r, a i r * b r) * (2 * B) = -2 * ∑ i, ∑ r, a i r * (b r * B) := by
  simp only [Fin.sum_univ_three]; ring

/-- **The derivative of the Christoffel symbols at a point, in the shifted flat form.** -/
theorem dChr_eq_flat (hg : IsCoordMetric g U) (hm : m ∈ U) (μ ρ ν σ : Fin 3) :
    dChr g m μ ρ ν σ = (1 / 2) * ∑ l, (g m)⁻¹ ρ l *
        (Sdd g m ν μ l σ + Sdd g m σ μ l ν - Sdd g m l μ ν σ)
      - ∑ r, christoffel g ρ μ r m * christoffel g r ν σ m := by
  have e : ∀ a b c d, pd a (fun y => pd b (fun z => g z c d) y) m = ddv g m b a c d :=
    fun _ _ _ _ => rfl
  have low : ∀ l, pd ν (fun y => g y l σ) m + pd σ (fun y => g y l ν) m - pd l (fun y => g y ν σ) m =
      2 * ∑ x, g m l x * christoffel g x ν σ m := fun l => by
    have := g_mul_christoffel hg hm l ν σ
    linarith
  have sym : ∀ a j k, christoffel g a j k m = christoffel g a k j m := christoffel_symm_low hg hm
  unfold dChr
  simp only [low, e]
  -- the first part, contracted
  have H1 : ∑ l, (-∑ i, ∑ r, (g m)⁻¹ ρ i * pd μ (fun y => g y i r) m * (g m)⁻¹ r l) *
        (2 * ∑ x, g m l x * christoffel g x ν σ m) =
      -2 * ∑ i, ∑ r, (g m)⁻¹ ρ i * pd μ (fun y => g y i r) m * christoffel g r ν σ m := by
    have hc := fun r => inv_contract hg hm r (fun x => christoffel g x ν σ m)
    have : ∀ l, (-∑ i, ∑ r, (g m)⁻¹ ρ i * pd μ (fun y => g y i r) m * (g m)⁻¹ r l) *
        (2 * ∑ x, g m l x * christoffel g x ν σ m) =
        -2 * ∑ i, ∑ r, (g m)⁻¹ ρ i * pd μ (fun y => g y i r) m *
          ((g m)⁻¹ r l * ∑ x, g m l x * christoffel g x ν σ m) := fun l =>
      sum_aux (fun i r => (g m)⁻¹ ρ i * pd μ (fun y => g y i r) m) (fun r => (g m)⁻¹ r l) _
    simp only [this]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.mul_sum, hc r]
  -- the metric-compatibility substitution
  have H2 : ∑ i, ∑ r, (g m)⁻¹ ρ i * pd μ (fun y => g y i r) m * christoffel g r ν σ m =
      ∑ r, christoffel g ρ μ r m * christoffel g r ν σ m +
        ∑ i, ∑ r, ∑ d, (g m)⁻¹ ρ i * (g m r d * christoffel g d μ i m) * christoffel g r ν σ m := by
    have hP : ∀ i r, pd μ (fun y => g y i r) m =
        ∑ d, g m i d * christoffel g d μ r m + ∑ d, g m r d * christoffel g d μ i m := fun i r => by
      rw [pd_g_eq_chr hg hm, Finset.sum_add_distrib]
    simp only [hP]
    have hc := fun r => inv_contract hg hm ρ (fun d => christoffel g d μ r m)
    have h1 : ∑ i, ∑ r, (g m)⁻¹ ρ i * (∑ d, g m i d * christoffel g d μ r m) * christoffel g r ν σ m =
        ∑ r, christoffel g ρ μ r m * christoffel g r ν σ m := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← hc r, Finset.sum_mul]
    have h2 : ∀ i r, (g m)⁻¹ ρ i * (∑ d, g m r d * christoffel g d μ i m) * christoffel g r ν σ m =
        ∑ d, (g m)⁻¹ ρ i * (g m r d * christoffel g d μ i m) * christoffel g r ν σ m := fun i r => by
      rw [Finset.mul_sum, Finset.sum_mul]
    simp only [mul_add, add_mul, Finset.sum_add_distrib, h2, h1]
  -- the second-derivative correction terms
  have corr : ∀ l, Sdd g m ν μ l σ + Sdd g m σ μ l ν - Sdd g m l μ ν σ =
      (ddv g m ν μ l σ + ddv g m σ μ l ν - ddv g m l μ ν σ) -
        2 * ∑ a, ∑ b, g m a b * (christoffel g a ν σ m * christoffel g b μ l m) := fun l => by
    unfold Sdd
    simp only [Fin.sum_univ_three, sym _ l ν, sym _ l σ, sym _ σ ν]
    ring
  rw [Finset.sum_add_distrib, H1, H2]
  simp only [corr, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [Fin.sum_univ_three]
  ring
