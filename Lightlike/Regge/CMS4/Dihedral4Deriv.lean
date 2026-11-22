import Mathlib
import Lightlike.Regge.D4.Dihedral
import Lightlike.Regge.Conv3.DihedralDeriv

/-!
# First variation of the dihedral angle of a 4-simplex in the squared edge lengths

`Lightlike.Regge4.cosDihedral4` depends on the lengths only through the squared lengths
`sq ℓ : V → V → ℝ`. This file restates it as a function `cosS` of a matrix `s` of squared lengths
and proves that along a line `s + ε δ` of squared lengths the dihedral angle `dihS` is
differentiable at `ε = 0` (the faces non-degenerate, the angle not `0` or `π`), with a derivative
written in closed form from the derivatives of the two Gram determinants and of the mixed
determinant. It is the dimension-4 counterpart of `Conv3.hasDerivAt_dihSq`.

## Main results

* `hasDerivAt_det3`: derivative of a `3 × 3` determinant with entries linear in `ε`, as the sum of
  the three determinants with one row replaced by its derivative.
* `cosDihedral4_eq_cosS`: `cosDihedral4 ℓ = cosS (sq ℓ)`, by `rfl`.
* `hasDerivAt_dihS`: the first variation of `dihS` along `s + ε δ`.
-/

open Real

namespace Lightlike.Regge4

private lemma hasDerivAt_lin (x y : ℝ) : HasDerivAt (fun ε : ℝ => x + ε * y) y 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).const_add x

/-- Derivative at `0` of a `3 × 3` determinant whose entries are `xᵢ + ε yᵢ`: the sum of the three
determinants in which one row of `x` is replaced by the same row of `y`. -/
theorem hasDerivAt_det3 (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) :
    HasDerivAt (fun ε : ℝ => det3 (x₁ + ε * y₁) (x₂ + ε * y₂) (x₃ + ε * y₃) (x₄ + ε * y₄)
        (x₅ + ε * y₅) (x₆ + ε * y₆) (x₇ + ε * y₇) (x₈ + ε * y₈) (x₉ + ε * y₉))
      (det3 y₁ y₂ y₃ x₄ x₅ x₆ x₇ x₈ x₉ + det3 x₁ x₂ x₃ y₄ y₅ y₆ x₇ x₈ x₉
        + det3 x₁ x₂ x₃ x₄ x₅ x₆ y₇ y₈ y₉) 0 := by
  have hA := hasDerivAt_lin x₁ y₁
  have hB := hasDerivAt_lin x₂ y₂
  have hC := hasDerivAt_lin x₃ y₃
  have hD := hasDerivAt_lin x₄ y₄
  have hE := hasDerivAt_lin x₅ y₅
  have hF := hasDerivAt_lin x₆ y₆
  have hG := hasDerivAt_lin x₇ y₇
  have hH := hasDerivAt_lin x₈ y₈
  have hI := hasDerivAt_lin x₉ y₉
  have := ((hA.mul ((hE.mul hI).sub (hF.mul hH))).sub
    (hB.mul ((hD.mul hI).sub (hF.mul hG)))).add (hC.mul ((hD.mul hH).sub (hE.mul hG)))
  convert this using 1
  · funext ε
    simp only [det3, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  · simp only [det3, Pi.sub_apply, Pi.mul_apply]
    ring

variable {V : Type*}

/-- The inner product `⟨a - o, b - o⟩` from a matrix `s` of squared lengths. -/
noncomputable def ipS (s : V → V → ℝ) (o a b : V) : ℝ := (s o a + s o b - s a b) / 2

/-- The Gram determinant of the tetrahedron `pqrs` from squared lengths. -/
noncomputable def gram3S (s : V → V → ℝ) (p q r t : V) : ℝ :=
  det3 (ipS s p q q) (ipS s p q r) (ipS s p q t) (ipS s p r q) (ipS s p r r) (ipS s p r t)
    (ipS s p t q) (ipS s p t r) (ipS s p t t)

/-- The mixed determinant at the triangle `pqr` of `pqrsu` from squared lengths. -/
noncomputable def mixedS (s : V → V → ℝ) (p q r t u : V) : ℝ :=
  det3 (ipS s p q q) (ipS s p q r) (ipS s p q u) (ipS s p r q) (ipS s p r r) (ipS s p r u)
    (ipS s p t q) (ipS s p t r) (ipS s p t u)

/-- The cosine of the dihedral angle, from squared lengths. -/
noncomputable def cosS (s : V → V → ℝ) (p q r t u : V) : ℝ :=
  mixedS s p q r t u / √(gram3S s p q r t * gram3S s p q r u)

/-- The dihedral angle at the triangle `pqr` of `pqrtu`, from squared lengths. -/
noncomputable def dihS (s : V → V → ℝ) (p q r t u : V) : ℝ := arccos (cosS s p q r t u)

/-- The entries of the Gram matrices are linear along `s + ε δ`. -/
theorem ipS_line (s δ : V → V → ℝ) (ε : ℝ) (o a b : V) :
    ipS (fun x y => s x y + ε * δ x y) o a b = ipS s o a b + ε * ipS δ o a b := by
  simp only [ipS]; ring

/-- Derivative of `gram3S` along `s + ε δ`. -/
noncomputable def gram3S' (s δ : V → V → ℝ) (p q r t : V) : ℝ :=
  det3 (ipS δ p q q) (ipS δ p q r) (ipS δ p q t) (ipS s p r q) (ipS s p r r) (ipS s p r t)
      (ipS s p t q) (ipS s p t r) (ipS s p t t)
    + det3 (ipS s p q q) (ipS s p q r) (ipS s p q t) (ipS δ p r q) (ipS δ p r r) (ipS δ p r t)
      (ipS s p t q) (ipS s p t r) (ipS s p t t)
    + det3 (ipS s p q q) (ipS s p q r) (ipS s p q t) (ipS s p r q) (ipS s p r r) (ipS s p r t)
      (ipS δ p t q) (ipS δ p t r) (ipS δ p t t)

/-- Derivative of `mixedS` along `s + ε δ`. -/
noncomputable def mixedS' (s δ : V → V → ℝ) (p q r t u : V) : ℝ :=
  det3 (ipS δ p q q) (ipS δ p q r) (ipS δ p q u) (ipS s p r q) (ipS s p r r) (ipS s p r u)
      (ipS s p t q) (ipS s p t r) (ipS s p t u)
    + det3 (ipS s p q q) (ipS s p q r) (ipS s p q u) (ipS δ p r q) (ipS δ p r r) (ipS δ p r u)
      (ipS s p t q) (ipS s p t r) (ipS s p t u)
    + det3 (ipS s p q q) (ipS s p q r) (ipS s p q u) (ipS s p r q) (ipS s p r r) (ipS s p r u)
      (ipS δ p t q) (ipS δ p t r) (ipS δ p t u)

theorem hasDerivAt_gram3S (s δ : V → V → ℝ) (p q r t : V) :
    HasDerivAt (fun ε : ℝ => gram3S (fun x y => s x y + ε * δ x y) p q r t)
      (gram3S' s δ p q r t) 0 := by
  have := hasDerivAt_det3 (ipS s p q q) (ipS s p q r) (ipS s p q t) (ipS s p r q) (ipS s p r r)
    (ipS s p r t) (ipS s p t q) (ipS s p t r) (ipS s p t t) (ipS δ p q q) (ipS δ p q r)
    (ipS δ p q t) (ipS δ p r q) (ipS δ p r r) (ipS δ p r t) (ipS δ p t q) (ipS δ p t r)
    (ipS δ p t t)
  simpa only [gram3S, gram3S', ipS_line] using this

theorem hasDerivAt_mixedS (s δ : V → V → ℝ) (p q r t u : V) :
    HasDerivAt (fun ε : ℝ => mixedS (fun x y => s x y + ε * δ x y) p q r t u)
      (mixedS' s δ p q r t u) 0 := by
  have := hasDerivAt_det3 (ipS s p q q) (ipS s p q r) (ipS s p q u) (ipS s p r q) (ipS s p r r)
    (ipS s p r u) (ipS s p t q) (ipS s p t r) (ipS s p t u) (ipS δ p q q) (ipS δ p q r)
    (ipS δ p q u) (ipS δ p r q) (ipS δ p r r) (ipS δ p r u) (ipS δ p t q) (ipS δ p t r)
    (ipS δ p t u)
  simpa only [mixedS, mixedS', ipS_line] using this

/-- **First variation of a dihedral angle of a 4-simplex in the squared edge lengths.** Along the
line `s + ε δ`, the dihedral angle at `pqr` between `pqrt` and `pqru` has the derivative below at
`ε = 0`, as long as both tetrahedra are non-degenerate and the angle is not `0` or `π`. -/
theorem hasDerivAt_dihS (s δ : V → V → ℝ) (p q r t u : V)
    (h1 : 0 < gram3S s p q r t) (h2 : 0 < gram3S s p q r u)
    (hc1 : cosS s p q r t u ≠ 1) (hc2 : cosS s p q r t u ≠ -1) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => s x y + ε * δ x y) p q r t u)
      (-(1 / √(1 - (cosS s p q r t u) ^ 2)) *
        ((mixedS' s δ p q r t u * √(gram3S s p q r t * gram3S s p q r u) -
          mixedS s p q r t u * ((gram3S' s δ p q r t * gram3S s p q r u +
            gram3S s p q r t * gram3S' s δ p q r u) /
            (2 * √(gram3S s p q r t * gram3S s p q r u)))) /
          √(gram3S s p q r t * gram3S s p q r u) ^ 2)) 0 := by
  have hu := hasDerivAt_mixedS s δ p q r t u
  have hv := hasDerivAt_gram3S s δ p q r t
  have hw := hasDerivAt_gram3S s δ p q r u
  have hs0 : (fun x y => s x y + (0 : ℝ) * δ x y) = s := by funext x y; simp
  have key := Lightlike.Regge.Conv3.hasDerivAt_arccos_div_sqrt hu hv hw
    (by simpa only [hs0] using h1) (by simpa only [hs0] using h2)
    (by simpa only [hs0, cosS] using hc1) (by simpa only [hs0, cosS] using hc2)
  simpa only [hs0, dihS, cosS] using key

section Bridge

variable [DecidableEq V]

/-- `cosDihedral4` is `cosS` of the squared lengths. -/
theorem cosDihedral4_eq_cosS (ℓ : Finset V → ℝ) (p q r t u : V) :
    cosDihedral4 ℓ p q r t u = cosS (sq ℓ) p q r t u := rfl

/-- `dihedral4` is `dihS` of the squared lengths. -/
theorem dihedral4_eq_dihS (ℓ : Finset V → ℝ) (p q r t u : V) :
    dihedral4 ℓ p q r t u = dihS (sq ℓ) p q r t u := rfl

end Bridge

end Lightlike.Regge4
