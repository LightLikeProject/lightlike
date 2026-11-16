import Lightlike.Regge.Conv3.FlatStarJet

/-!
# The edge polynomial in a chart with non-vanishing metric gradient, as a displaced flat one

At a point `m` the squared length of an edge with midpoint offset `s` and vector `Δ`, to fourth
order, is the edge polynomial `edgePoly` of the jet `(g m, ∂g, ∂∂g)`. Moving the vertices `k` of a star
to `ε k + ε² Γ(k, k) / 2` (`Γ` the Christoffel symbols at `m`) makes the first derivatives of the
metric vanish at `m`; this file proves the edge-level part of that change of chart:

* `edgeC_eq_chr`: the `ε³` coefficient `c` is `2 Δ·g Γ(s, Δ)`, the cross term of the displaced
  flat length;
* `edgeR_eq_displaced`: the `ε⁴` coefficient `r` is `|Γ(s, Δ)|²_g` plus the flat second-order part
  `rf` of the shifted second derivatives `Sdd = ∂∂g - Σ g_ab (Γ^a_{ki} Γ^b_{lj} + Γ^a_{kj} Γ^b_{li})`.

The statement about `r` is a formal identity in the definitions (no hypothesis on `g`), and the one
about `c` uses that `g m` is invertible and symmetric. These two facts are the first step of
reducing the star identity at a general point to the flat case of `FlatStarJet`; the angle-sum and
curvature steps are not in this file.
-/

open Real Matrix Lightlike
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {m : Fin 3 → ℝ}

/-- The second derivatives of the metric in the chart in which its first derivatives vanish at `m`:
`S_{kl,ij} = ∂_l ∂_k g_ij - Σ g_ab (Γ^a_{ki} Γ^b_{lj} + Γ^a_{kj} Γ^b_{li})`. -/
noncomputable def Sdd (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ)
    (k l i j : Fin 3) : ℝ :=
  ddv g m k l i j - ∑ a, ∑ b, g m a b * (christoffel g a k i m * christoffel g b l j m
    + christoffel g a k j m * christoffel g b l i m)

/-- The shifted second-derivative form is the original one minus twice the `g m`-product of
`Γ(u, Δ)` and `Γ(w, Δ)`. -/
theorem ddq_Sdd (u w Δ : Fin 3 → ℝ) :
    ddq (Sdd g m) u w Δ = ddq (ddv g m) u w Δ - 2 * (chr g m u Δ ⬝ᵥ (g m *ᵥ chr g m w Δ)) := by
  simp only [ddq, Sdd, chr, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- The second-derivative form `Δ ⬝ ddmat(u, w) Δ` is `ddq` of `ddv`. -/
theorem dot_ddmat (u w Δ : Fin 3 → ℝ) :
    Δ ⬝ᵥ (ddmat g m u w *ᵥ Δ) = ddq (ddv g m) u w Δ := by
  simp only [ddq, ddv, ddmat, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.of_apply]
  ring

/-- **Second-order part of the edge polynomial in the displaced-flat form.** The `ε⁴` coefficient of the
edge polynomial is the squared `g m`-length of `Γ(s, Δ)` plus the flat second-order part `rf` of the
shifted second derivatives `Sdd`. -/
theorem edgeR_eq_displaced (s Δ : Fin 3 → ℝ) :
    edgeR g m s Δ = chr g m s Δ ⬝ᵥ (g m *ᵥ chr g m s Δ) + rf (Sdd g m) s Δ := by
  have h1 := ddq_Sdd (g := g) (m := m) s s Δ
  have h2 := ddq_Sdd (g := g) (m := m) Δ Δ Δ
  simp only [edgeR, rf, dot_ddmat]
  rw [h1, h2]
  ring

variable {U : Set (Fin 3 → ℝ)}

/-- `g m` times the Christoffel symbols is the lowered Christoffel symbol
`½ (∂_j g_bk + ∂_k g_bj - ∂_b g_jk)`. -/
theorem g_mul_christoffel (hg : IsCoordMetric g U) (hm : m ∈ U) (b j k : Fin 3) :
    ∑ a, g m b a * christoffel g a j k m =
      (1 / 2) * (pd j (fun y => g y b k) m + pd k (fun y => g y b j) m - pd b (fun y => g y j k) m) := by
  have hGi : ∀ b l, ∑ a, g m b a * (g m)⁻¹ a l = if b = l then 1 else 0 := fun b l => by
    have := congrFun (congrFun (Matrix.mul_nonsing_inv (g m) (hg.isUnit_det m hm)) b) l
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  simp only [christoffel, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ l, ∑ a, g m b a * ((1 / 2) * ((g m)⁻¹ a l *
      (pd j (fun y => g y l k) m + pd k (fun y => g y l j) m - pd l (fun y => g y j k) m)))
      = (1 / 2) * ((∑ a, g m b a * (g m)⁻¹ a l) *
      (pd j (fun y => g y l k) m + pd k (fun y => g y l j) m - pd l (fun y => g y j k) m)) := by
    intro l; rw [Finset.sum_mul, Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
  simp only [this, hGi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum]
  simp [Finset.sum_ite_eq]

/-- **The first-order part of the edge polynomial is the displaced-flat cross term:** `c = 2 Δ·G Γ(s, Δ)`. -/
theorem edgeC_eq_chr (hg : IsCoordMetric g U) (hm : m ∈ U) (s Δ : Fin 3 → ℝ) :
    edgeC g m s Δ = 2 * (Δ ⬝ᵥ (g m *ᵥ chr g m s Δ)) := by
  have L : ∀ b j k : Fin 3, g m b 0 * christoffel g 0 j k m + g m b 1 * christoffel g 1 j k m
      + g m b 2 * christoffel g 2 j k m = (1 / 2) * (pd j (fun y => g y b k) m
        + pd k (fun y => g y b j) m - pd b (fun y => g y j k) m) := fun b j k => by
    simpa [Fin.sum_univ_three] using g_mul_christoffel hg hm b j k
  have hs : ∀ k i j : Fin 3, pd k (fun y => g y i j) m = pd k (fun y => g y j i) m :=
    fun k i j => pd_symm_ij hg hm k i j
  have e10 := fun k => hs k 1 0
  have e20 := fun k => hs k 2 0
  have e21 := fun k => hs k 2 1
  simp only [edgeC, dmat, chr, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.of_apply]
  linear_combination (-2) * ((Δ 0 * s 0 * Δ 0) * L 0 0 0 + (Δ 0 * s 0 * Δ 1) * L 0 0 1 + (Δ 0 * s 0 * Δ 2) * L 0 0 2 + (Δ 0 * s 1 * Δ 0) * L 0 1 0 + (Δ 0 * s 1 * Δ 1) * L 0 1 1 + (Δ 0 * s 1 * Δ 2) * L 0 1 2 + (Δ 0 * s 2 * Δ 0) * L 0 2 0 + (Δ 0 * s 2 * Δ 1) * L 0 2 1 + (Δ 0 * s 2 * Δ 2) * L 0 2 2 + (Δ 1 * s 0 * Δ 0) * L 1 0 0 + (Δ 1 * s 0 * Δ 1) * L 1 0 1 + (Δ 1 * s 0 * Δ 2) * L 1 0 2 + (Δ 1 * s 1 * Δ 0) * L 1 1 0 + (Δ 1 * s 1 * Δ 1) * L 1 1 1 + (Δ 1 * s 1 * Δ 2) * L 1 1 2 + (Δ 1 * s 2 * Δ 0) * L 1 2 0 + (Δ 1 * s 2 * Δ 1) * L 1 2 1 + (Δ 1 * s 2 * Δ 2) * L 1 2 2 + (Δ 2 * s 0 * Δ 0) * L 2 0 0 + (Δ 2 * s 0 * Δ 1) * L 2 0 1 + (Δ 2 * s 0 * Δ 2) * L 2 0 2 + (Δ 2 * s 1 * Δ 0) * L 2 1 0 + (Δ 2 * s 1 * Δ 1) * L 2 1 1 + (Δ 2 * s 1 * Δ 2) * L 2 1 2 + (Δ 2 * s 2 * Δ 0) * L 2 2 0 + (Δ 2 * s 2 * Δ 1) * L 2 2 1 + (Δ 2 * s 2 * Δ 2) * L 2 2 2) + (Δ 0 * ((s 1 * Δ 0 - s 0 * Δ 1) * e10 0 + (s 2 * Δ 0 - s 0 * Δ 2) * e20 0 + (s 2 * Δ 1 - s 1 * Δ 2) * e21 0) + Δ 1 * ((s 1 * Δ 0 - s 0 * Δ 1) * e10 1 + (s 2 * Δ 0 - s 0 * Δ 2) * e20 1 + (s 2 * Δ 1 - s 1 * Δ 2) * e21 1) + Δ 2 * ((s 1 * Δ 0 - s 0 * Δ 1) * e10 2 + (s 2 * Δ 0 - s 0 * Δ 2) * e20 2 + (s 2 * Δ 1 - s 1 * Δ 2) * e21 2))

/-- **Metric compatibility at a point.** `∂_p g_qa = Σ_d (g_qd Γ^d_{pa} + g_ad Γ^d_{pq})`. -/
theorem pd_g_eq_chr (hg : IsCoordMetric g U) (hm : m ∈ U) (p q a : Fin 3) :
    pd p (fun y => g y q a) m =
      ∑ d, (g m q d * christoffel g d p a m + g m a d * christoffel g d p q m) := by
  rw [Finset.sum_add_distrib, g_mul_christoffel hg hm q p a, g_mul_christoffel hg hm a p q]
  have h1 := pd_symm_ij hg hm p q a
  have h2 := pd_symm_ij hg hm a q p
  have h3 := pd_symm_ij hg hm q p a
  have h4 := pd_symm_ij hg hm p a q
  have h5 := pd_symm_ij hg hm q a p
  linarith

/-- The Christoffel symbols are symmetric in their lower indices. -/
theorem christoffel_symm_low (hg : IsCoordMetric g U) (hm : m ∈ U) (a j k : Fin 3) :
    christoffel g a j k m = christoffel g a k j m := by
  unfold christoffel
  refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
  rw [pd_symm_ij hg hm l j k]
  ring

/-- The metric matrix at a point of the domain is symmetric, entrywise. -/
theorem g_symm_m (hg : IsCoordMetric g U) (hm : m ∈ U) (i j : Fin 3) : g m i j = g m j i := by
  have := congrFun (congrFun (hg.symm m hm) j) i
  simpa using this


end Lightlike.Regge.Conv3
