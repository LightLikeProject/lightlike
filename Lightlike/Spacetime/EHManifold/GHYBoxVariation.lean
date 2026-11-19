import Lightlike.Spacetime.EHManifold.GHYBox

/-!
# The Einstein–Hilbert action with the Gibbons–Hawking–York term on a box: only the bulk variation remains

`eh_ghy_variation_box`: for a smooth nondegenerate symmetric coordinate metric `g` on `ℝⁿ⁺¹` with
`g^{ii} ≠ 0`, a box `[a, b]`, and a smooth symmetric perturbation `h` that vanishes on the coordinate
hyperplanes carrying the faces of the box (its normal derivatives are free),

`d/dt [∫_{[a,b]} √|g_t| (R(g_t) - 2Λ) + ∑_i (∫_{x^i = b_i} - ∫_{x^i = a_i}) 2 √|h_t| K_t]
  = -∫_{[a,b]} √|g| (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}) h_{αβ}` at `t = 0`.

This is Dyer–Hinterbichler (4.4): with the Gibbons–Hawking–York term the boundary variation vanishes
without any restriction on the normal derivatives of the perturbation.

Differences from the source: a coordinate box instead of a region with smooth boundary in a manifold; the
perturbation vanishes on the whole hyperplanes; the boundary density `2 √|h| K` is the coordinate expression
`ghyDensity` (outward normals: `+` on the faces `x^i = b_i`, `-` on the faces `x^i = a_i`).

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eqs. (4.1) to (4.4), p. 20.
-/

open Matrix Filter Topology MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The Gibbons–Hawking–York density of a smooth nondegenerate metric with `g^{ii} ≠ 0` is continuous. -/
lemma continuous_ghyDensity (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hdet : ∀ x, (g x).det ≠ 0) (i : Fin n)
    (hii : ∀ x, (g x)⁻¹ i i ≠ 0) : Continuous (ghyDensity g i) := by
  have hGc : Continuous g := continuous_matrix fun a b => (hg a b).continuous
  have hsd : Continuous (fun x => √|(g x).det|) :=
    Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det)
  have hinv : ∀ a b, Continuous (fun x => (g x)⁻¹ a b) := fun a b =>
    (contDiff_inv_entry g hg hdet a b).continuous
  have hsG : Continuous (fun x => √|(g x)⁻¹ i i|) :=
    Real.continuous_sqrt.comp (continuous_abs.comp (hinv i i))
  have hne : ∀ x, √|(g x)⁻¹ i i| ≠ 0 := fun x => (Real.sqrt_pos.2 (abs_pos.2 (hii x))).ne'
  have hsum : Continuous (fun x => ∑ α, ∑ β,
      ((g x)⁻¹ α β - (g x)⁻¹ α i * (g x)⁻¹ β i / (g x)⁻¹ i i) * christoffel g i α β x) :=
    continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
      ((hinv α β).sub (((hinv α i).mul (hinv β i)).div (hinv i i) hii)).mul
        (contDiff_christoffel g hg hdet i α β).continuous
  show Continuous fun x => 2 * √|(g x).det| * √|(g x)⁻¹ i i| * (-(1 / √|(g x)⁻¹ i i|) *
    ∑ α, ∑ β, ((g x)⁻¹ α β - (g x)⁻¹ α i * (g x)⁻¹ β i / (g x)⁻¹ i i) * christoffel g i α β x)
  exact ((continuous_const.mul hsd).mul hsG).mul (((continuous_const.div hsG hne).neg).mul hsum)

variable (g h : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)
include hg hh hgs hhs hdet

/-- On a hyperplane on which the perturbation vanishes, the Gibbons–Hawking–York density of `g + t h` is
the one of `g` minus `t` times the Palatini flux. -/
theorem ghyDensity_add_smul_on_hyperplane (i : Fin (n + 1)) (hii : ∀ x, (g x)⁻¹ i i ≠ 0)
    (x : Fin (n + 1) → ℝ) (hz : ∀ y, y i = x i → h y = 0) (t : ℝ) :
    ghyDensity (fun y => g y + t • h y) i x = ghyDensity g i x + t * -ehFlux g h i x := by
  have hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a := by
    intro a b
    have hT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by
      have : (g x)ᵀ = g x := by ext i j; exact hgs x j i
      rw [Matrix.transpose_nonsing_inv, this]
    have := congrFun (congrFun hT a) b
    rw [Matrix.transpose_apply] at this
    exact this.symm
  have htan : ∀ σ a b, σ ≠ i → pd σ (fun z => h z a b) x = 0 := fun σ a b hσ =>
    pd_eq_zero_of_vanishing_on_hyperplane
      ((hh a b).differentiable (by simp)).differentiableAt i σ hσ
      (fun y hy => by rw [hz y hy]; rfl)
  rw [ghyDensity_add_smul_of_zero g h x i
    (fun l k => ((hg l k).differentiable (by simp)).differentiableAt)
    (fun l k => ((hh l k).differentiable (by simp)).differentiableAt) (hii x) (hz x rfl) t,
    ghySlope_eq_neg_ehFlux g h x i (hz x rfl) htan hinv (hii x)]

/-- The derivative of the Gibbons–Hawking–York term of one face of a hyperplane on which the perturbation
vanishes is minus the flux through the face. -/
theorem hasDerivAt_ghy_face (i : Fin (n + 1)) (hii : ∀ x, (g x)⁻¹ i i ≠ 0) (c : ℝ)
    (hz : ∀ y : Fin (n + 1) → ℝ, y i = c → h y = 0) (lo hi : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y in Icc lo hi,
        ghyDensity (fun z => g z + t • h z) i (Fin.insertNth i c y))
      (-∫ y in Icc lo hi, ehFlux g h i (Fin.insertNth i c y)) 0 := by
  have hins : Continuous (fun y : Fin n → ℝ => (Fin.insertNth i c y : Fin (n + 1) → ℝ)) :=
    Continuous.finInsertNth i continuous_const continuous_id
  have hK : IsCompact (Icc lo hi) := isCompact_Icc
  have i1 : IntegrableOn (fun y : Fin n → ℝ => ghyDensity g i (Fin.insertNth i c y)) (Icc lo hi)
      volume :=
    ((continuous_ghyDensity g hg hdet i hii).comp hins).continuousOn.integrableOn_compact hK
  have i2 : IntegrableOn (fun y : Fin n → ℝ => ehFlux g h i (Fin.insertNth i c y)) (Icc lo hi)
      volume :=
    ((contDiff_flux g h hg hh hdet i).continuous.comp hins).continuousOn.integrableOn_compact hK
  have hfun : (fun t : ℝ => ∫ y in Icc lo hi,
        ghyDensity (fun z => g z + t • h z) i (Fin.insertNth i c y)) =
      fun t => (∫ y in Icc lo hi, ghyDensity g i (Fin.insertNth i c y)) +
        t * -∫ y in Icc lo hi, ehFlux g h i (Fin.insertNth i c y) := by
    funext t
    have hpt : ∀ y : Fin n → ℝ, ghyDensity (fun z => g z + t • h z) i (Fin.insertNth i c y) =
        ghyDensity g i (Fin.insertNth i c y) + t * -ehFlux g h i (Fin.insertNth i c y) := fun y =>
      ghyDensity_add_smul_on_hyperplane g h hg hh hgs hhs hdet i hii _
        (fun z hzi => hz z (by rw [hzi, Fin.insertNth_apply_same])) t
    simp only [hpt]
    have i3 : IntegrableOn (fun y : Fin n → ℝ => t * -ehFlux g h i (Fin.insertNth i c y)) (Icc lo hi)
        volume := i2.neg.const_mul t
    rw [integral_add i1 i3, integral_const_mul, integral_neg]
  rw [hfun]
  have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const
    (-∫ y in Icc lo hi, ehFlux g h i (Fin.insertNth i c y))).const_add
    (∫ y in Icc lo hi, ghyDensity g i (Fin.insertNth i c y))
  simpa using h1

/-- **The Einstein–Hilbert action with the Gibbons–Hawking–York term on a box**: for a perturbation
vanishing on the boundary hyperplanes, only the bulk variation remains. -/
theorem eh_ghy_variation_box (a b : Fin (n + 1) → ℝ) (hle : a ≤ b) (Λ : ℝ)
    (hii : ∀ (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ), (g x)⁻¹ i i ≠ 0)
    (hbd : ∀ i : Fin (n + 1), ∀ y : Fin (n + 1) → ℝ, (y i = a i ∨ y i = b i) → h y = 0) :
    HasDerivAt (fun t : ℝ => (∫ x in Icc a b, lagDensity g h Λ t x) +
        ∑ i : Fin (n + 1),
          ((∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              ghyDensity (fun z => g z + t • h z) i (Fin.insertNth i (b i) y)) -
            ∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              ghyDensity (fun z => g z + t • h z) i (Fin.insertNth i (a i) y)))
      (-∫ x in Icc a b, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) 0 := by
  have hbox := eh_variation_box g h hg hh hgs hhs hdet a b hle Λ
  have hfaces := HasDerivAt.fun_sum (u := Finset.univ) fun (i : Fin (n + 1)) _ =>
    (hasDerivAt_ghy_face g h hg hh hgs hhs hdet i (hii i) (b i)
        (fun y hy => hbd i y (Or.inr hy)) (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i)).fun_sub
      (hasDerivAt_ghy_face g h hg hh hgs hhs hdet i (hii i) (a i)
        (fun y hy => hbd i y (Or.inl hy)) (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i))
  have hsum := hbox.fun_add hfaces
  have hval : ((-∫ x in Icc a b, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) +
        ∑ i : Fin (n + 1),
          ((∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              ehFlux g h i (Fin.insertNth i (b i) y)) -
            ∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              ehFlux g h i (Fin.insertNth i (a i) y))) +
      ∑ i : Fin (n + 1),
        ((-∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
            ehFlux g h i (Fin.insertNth i (b i) y)) -
          -∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
            ehFlux g h i (Fin.insertNth i (a i) y)) =
      -∫ x in Icc a b, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β := by
    rw [add_assoc, ← Finset.sum_add_distrib]
    have : ∑ i : Fin (n + 1),
        (((∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              ehFlux g h i (Fin.insertNth i (b i) y)) -
            ∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              ehFlux g h i (Fin.insertNth i (a i) y)) +
          ((-∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              ehFlux g h i (Fin.insertNth i (b i) y)) -
            -∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              ehFlux g h i (Fin.insertNth i (a i) y))) = 0 :=
      Finset.sum_eq_zero fun i _ => by ring
    rw [this, add_zero]
  rw [hval] at hsum
  exact hsum

end Lightlike
