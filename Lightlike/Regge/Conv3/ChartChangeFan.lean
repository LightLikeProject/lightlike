import Lightlike.Regge.Conv3.ChartChange
import Lightlike.Regge.Conv3.ClosedFan

/-!
# The star with displaced vertices: lengths and angles

Displace every point `k` of a star to `k + (ε/2) Γ(k, k)`, with `Γ = Γ(m)` the Christoffel symbols
of `g` at `m`. The squared `g m`-lengths of the displaced edges are `q + ε c + ε² r'`, with
`q, c` the Gram and first-order parts of the edge polynomial of the jet of `g` and
`r' = |Γ(s, Δ)|²_g` (`dispLen_eq_lens3`, from `edgeC_eq_chr` and `Pdisp_sub`). The dihedral angle of
a tetrahedron with edge vectors `W, X, Y` for a positive definite `G` is the fan angle
`fanAng G W X Y` (`Dsq_lens3`).

This file does not prove that the angles around an edge of the displaced star add up to `2π`.
-/

open Real Matrix Lightlike
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {m : Fin 3 → ℝ} {U : Set (Fin 3 → ℝ)}

/-- The six squared lengths `(pq, pr, qr, ps, qs, rs)` of the tetrahedron `(0, W, X, Y)` for the
quadratic form of `G`, as in `incQ_eq_vec`. -/
noncomputable def lens3 (G : Matrix (Fin 3) (Fin 3) ℝ) (W X Y : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![W ⬝ᵥ (G *ᵥ W), X ⬝ᵥ (G *ᵥ X), (X - W) ⬝ᵥ (G *ᵥ (X - W)), Y ⬝ᵥ (G *ᵥ Y),
    (Y - W) ⬝ᵥ (G *ᵥ (Y - W)), (Y - X) ⬝ᵥ (G *ᵥ (Y - X))]

/-- **The dihedral angle of a tetrahedron with vectors `W, X, Y` is the fan angle.** -/
theorem Dsq_lens3 {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.PosDef) {W : Fin 3 → ℝ} (hW : W ≠ 0)
    (X Y : Fin 3 → ℝ) : Dsq (lens3 G W X Y) = fanAng G W X Y := by
  have hs := posDef_symm hG
  have ha : W ⬝ᵥ (G *ᵥ W) ≠ 0 := (posDef_dpos hG hW).ne'
  have := cosSq_bf hs W X Y ha
  unfold fanAng
  rw [← this]
  simp only [Dsq, lens3, dihSq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

/-- The displaced position of a point `k`: `k + (ε/2) Γ(k, k)`. -/
noncomputable def Pdisp (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ) (ε : ℝ)
    (k : Fin 3 → ℝ) : Fin 3 → ℝ := k + (ε / 2) • chr g m k k

/-- The displaced edge vector from the vertex `a` to the vertex `b` of the incidence `(σ, h)`. -/
noncomputable def dvec (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ) (ε : ℝ)
    (σ h : Fin 6) (a b : Fin 4) : Fin 3 → ℝ :=
  Pdisp g m ε (fun i => kpos σ h b i) - Pdisp g m ε (fun i => kpos σ h a i)

/-- `Γ` is symmetric in its two arguments. -/
theorem chr_symm (hg : IsCoordMetric g U) (hm : m ∈ U) (u v : Fin 3 → ℝ) :
    chr g m u v = chr g m v u := by
  ext i
  simp only [chr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [christoffel_symm_low hg hm i j k]; ring

/-- The displaced edge vector of an edge with endpoints `ka, kb` is `Δ + ε Γ(s, Δ)`, `Δ = kb - ka`,
`s = (ka + kb)/2`. -/
theorem Pdisp_sub (hg : IsCoordMetric g U) (hm : m ∈ U) (ε : ℝ) (ka kb : Fin 3 → ℝ) :
    Pdisp g m ε kb - Pdisp g m ε ka =
      (kb - ka) + ε • chr g m ((1 / 2 : ℝ) • (ka + kb)) (kb - ka) := by
  ext i
  have c10 := christoffel_symm_low hg hm i 1 0
  have c20 := christoffel_symm_low hg hm i 2 0
  have c21 := christoffel_symm_low hg hm i 2 1
  simp only [Pdisp, chr, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  rw [c10, c20, c21]
  ring

/-- The `ε`-polynomial `q + ε c + ε² r'` of an edge is the squared `g m`-length of the displaced
edge vector. -/
theorem edge_disp (hg : IsCoordMetric g U) (hm : m ∈ U) (ε : ℝ) (ka kb : Fin 3 → ℝ) :
    (Pdisp g m ε kb - Pdisp g m ε ka) ⬝ᵥ (g m *ᵥ (Pdisp g m ε kb - Pdisp g m ε ka)) =
      edgeQ g m (kb - ka) + ε * edgeC g m ((1 / 2 : ℝ) • (ka + kb)) (kb - ka)
        + ε ^ 2 * (chr g m ((1 / 2 : ℝ) • (ka + kb)) (kb - ka) ⬝ᵥ
          (g m *ᵥ chr g m ((1 / 2 : ℝ) • (ka + kb)) (kb - ka))) := by
  have hs : (g m)ᵀ = g m := by ext i j; exact g_symm_m hg hm j i
  have hsym : ∀ a b : Fin 3 → ℝ, a ⬝ᵥ (g m *ᵥ b) = b ⬝ᵥ (g m *ᵥ a) := fun a b => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, dotProduct_comm]
  rw [Pdisp_sub hg hm, edgeC_eq_chr hg hm]
  simp only [edgeQ, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hsym (chr g m _ _) (kb - ka)]
  ring

/-- The squared lengths of the displaced flat star: `q + ε c + ε² r'` with
`r'_{ab} = |Γ(s_{ab}, Δ_{ab})|²_g`. -/
noncomputable def incRd (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ)
    (σ h : Fin 6) : Fin 6 → ℝ :=
  incVec (fun s Δ => chr g m s Δ ⬝ᵥ (g m *ᵥ chr g m s Δ)) σ h

/-- The six squared lengths of the incidence `(σ, h)` with displaced vertices, to second order:
`q + ε c + ε² r'`. -/
noncomputable def dispLen (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ) (ε : ℝ)
    (σ h : Fin 6) : Fin 6 → ℝ :=
  incQ g m σ h + ε • incC g m σ h + ε ^ 2 • incRd g m σ h

/-- The midpoint of two points as a scalar multiple of their sum. -/
theorem midpt_eq (ka kb : Fin 3 → ℝ) :
    (fun i => (ka i + kb i) / 2) = (1 / 2 : ℝ) • (ka + kb) := by
  ext i; simp; ring

/-- **The displaced lengths are the lengths of the displaced tetrahedron.** -/
theorem dispLen_eq_lens3 (hg : IsCoordMetric g U) (hm : m ∈ U) (ε : ℝ) (σ h : Fin 6) :
    dispLen g m ε σ h = lens3 (g m) (dvec g m ε σ h (hP h) (hQ h)) (dvec g m ε σ h (hP h) (hR h))
      (dvec g m ε σ h (hP h) (hS h)) := by
  have e := fun ka kb => edge_disp hg hm ε ka kb
  have d1 : ∀ a b c : Fin 4, dvec g m ε σ h a c - dvec g m ε σ h a b = dvec g m ε σ h b c := by
    intro a b c; unfold dvec; abel
  ext i
  fin_cases i
  all_goals
    simp only [dispLen, incQ, incC, incRd, incVec, lens3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, d1,
      midpt_eq, dvec, Fin.reduceFinMk, Fin.isValue]
    first
    | exact (e _ _).symm
    | (symm; convert e _ _ using 2 <;> first | rfl | simp only [sub_sub_sub_cancel_right])

end Lightlike.Regge.Conv3
