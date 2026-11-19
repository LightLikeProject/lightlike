import Lightlike.Spacetime.EHManifold.FaceFlux

/-!
# The boundary term of the Einstein–Hilbert variation for a perturbation vanishing on the boundary

`eh_variation_box_dirichlet`: for a smooth nondegenerate symmetric coordinate metric `g` on `ℝⁿ⁺¹`, a box
`[a, b]` and a smooth symmetric perturbation `h` that vanishes on the coordinate hyperplanes carrying the
faces of the box (its normal derivatives are not restricted),

`d/dt ∫_{[a,b]} √|g_t| (R(g_t) - 2Λ) = -∫_{[a,b]} √|g| (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}) h_{αβ}
  + ∑_i (∫_{x^i = b_i} - ∫_{x^i = a_i}) √|g| (g^{iσ} g^{iν} - g^{ii} g^{σν}) ∂_i h_{σν}` at `t = 0`.

The boundary term involves only the normal derivative `∂_i h` of the perturbation: this is the term that
the Gibbons–Hawking–York boundary term cancels (Dyer–Hinterbichler (4.2), (4.3)).

Differences from the source: the region is a coordinate box, not a region with smooth boundary in a
manifold; the perturbation is assumed to vanish on the whole hyperplanes `x^i = a_i`, `x^i = b_i`; the
boundary integrand is written with the inverse metric of the coordinates, not with the induced metric and
the unit normal; the Gibbons–Hawking–York term itself is not treated.

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eqs. (4.2), (4.3), p. 20.
-/

open Matrix Filter Topology MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- A function vanishing on the hyperplane `y_i = x_i` has vanishing partial derivatives at `x` in the
other coordinate directions. -/
lemma pd_eq_zero_of_vanishing_on_hyperplane {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (i σ : Fin n) (hσ : σ ≠ i) (hz : ∀ y, y i = x i → f y = 0) :
    pd σ f x = 0 := by
  have hc : HasDerivAt (fun s : ℝ => x + s • (Pi.single σ (1 : ℝ) : Fin n → ℝ))
      (Pi.single σ (1 : ℝ) : Fin n → ℝ) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single σ (1 : ℝ) : Fin n → ℝ)).const_add x
    simpa using h1
  have hcomp : HasDerivAt (fun s : ℝ => f (x + s • (Pi.single σ (1 : ℝ) : Fin n → ℝ)))
      (fderiv ℝ f x (Pi.single σ 1)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hf.hasFDerivAt hc (by simp)
  have hzero : (fun s : ℝ => f (x + s • (Pi.single σ (1 : ℝ) : Fin n → ℝ))) = fun _ => (0 : ℝ) := by
    funext s
    refine hz _ ?_
    simp [Pi.single_apply, hσ.symm]
  rw [hzero] at hcomp
  unfold pd
  exact hcomp.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))

variable (g h : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)
include hg hh hgs hhs hdet

/-- **The flux through a hyperplane on which the perturbation vanishes** involves only the normal derivative
of the perturbation. -/
theorem ehFlux_of_vanishing_on_hyperplane (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ)
    (hz : ∀ y, y i = x i → h y = 0) :
    ehFlux g h i x = √|(g x).det| * ∑ σ, ∑ ν,
      ((g x)⁻¹ i σ * (g x)⁻¹ i ν - (g x)⁻¹ i i * (g x)⁻¹ σ ν) * pd i (fun z => h z σ ν) x := by
  have hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a := by
    intro a b
    have hT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by
      have : (g x)ᵀ = g x := by ext i j; exact hgs x j i
      rw [Matrix.transpose_nonsing_inv, this]
    have := congrFun (congrFun hT a) b
    rw [Matrix.transpose_apply] at this
    exact this.symm
  unfold ehFlux
  rw [Wvec_of_vanishing_on_face g h x i (hz x rfl)
    (fun σ a b hσ => pd_eq_zero_of_vanishing_on_hyperplane
      ((hh a b).differentiable (by simp)).differentiableAt i σ hσ
      (fun y hy => by rw [hz y hy]; rfl)) hinv]

/-- **The variation of the Einstein–Hilbert action over a box, for a perturbation vanishing on the
boundary hyperplanes**: the bulk term plus a boundary term in the normal derivatives of the perturbation. -/
theorem eh_variation_box_dirichlet (a b : Fin (n + 1) → ℝ) (hle : a ≤ b) (Λ : ℝ)
    (hbd : ∀ i : Fin (n + 1), ∀ y : Fin (n + 1) → ℝ, (y i = a i ∨ y i = b i) → h y = 0) :
    HasDerivAt (fun t : ℝ => ∫ x in Icc a b, lagDensity g h Λ t x)
      ((-∫ x in Icc a b, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) +
        ∑ i : Fin (n + 1),
          ((∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              (fun x => √|(g x).det| * ∑ σ, ∑ ν,
                ((g x)⁻¹ i σ * (g x)⁻¹ i ν - (g x)⁻¹ i i * (g x)⁻¹ σ ν) * pd i (fun z => h z σ ν) x)
                (Fin.insertNth i (b i) y)) -
            ∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              (fun x => √|(g x).det| * ∑ σ, ∑ ν,
                ((g x)⁻¹ i σ * (g x)⁻¹ i ν - (g x)⁻¹ i i * (g x)⁻¹ σ ν) * pd i (fun z => h z σ ν) x)
                (Fin.insertNth i (a i) y))) 0 := by
  have hmain := eh_variation_box g h hg hh hgs hhs hdet a b hle Λ
  have hfront : ∀ (i : Fin (n + 1)) (y : Fin n → ℝ),
      ehFlux g h i (Fin.insertNth i (b i) y) =
        (fun x => √|(g x).det| * ∑ σ, ∑ ν,
          ((g x)⁻¹ i σ * (g x)⁻¹ i ν - (g x)⁻¹ i i * (g x)⁻¹ σ ν) * pd i (fun z => h z σ ν) x)
          (Fin.insertNth i (b i) y) := fun i y =>
    ehFlux_of_vanishing_on_hyperplane g h hg hh hgs hhs hdet i _ fun z hzi =>
      hbd i z (Or.inr (by rw [hzi, Fin.insertNth_apply_same]))
  have hback : ∀ (i : Fin (n + 1)) (y : Fin n → ℝ),
      ehFlux g h i (Fin.insertNth i (a i) y) =
        (fun x => √|(g x).det| * ∑ σ, ∑ ν,
          ((g x)⁻¹ i σ * (g x)⁻¹ i ν - (g x)⁻¹ i i * (g x)⁻¹ σ ν) * pd i (fun z => h z σ ν) x)
          (Fin.insertNth i (a i) y) := fun i y =>
    ehFlux_of_vanishing_on_hyperplane g h hg hh hgs hhs hdet i _ fun z hzi =>
      hbd i z (Or.inl (by rw [hzi, Fin.insertNth_apply_same]))
  simp only [hfront, hback] at hmain
  exact hmain

end Lightlike
