import Lightlike.Regge.CMS4.Quot4

/-!
# The Plücker identity for the plane quotient in dimension 4

For an axis `(w₁, w₂)` the quotient form `bf2` and the area form `det4 w₁ w₂` satisfy, on the
two-dimensional quotient, the identities
`bf2(u,t) det(t,v) + det(u,t) bf2(t,v) = bf2(t,t) det(u,v)` (imaginary part) and
`bf2(u,t) bf2(t,v) - (det G / gramW) det(u,t) det(t,v) = bf2(t,t) bf2(u,v)` (real part, from
`bf2_gram`). Together they say `ζ(u,t) ζ(t,v) = bf2(t,t) ζ(u,v)` for `ζ = bf2 + i κ det`.

## Main results

* `cramer4`: the five-vector relation behind the identity;
* `bf2_add`, `bf2_smul`, `bf2_axis₁`, `bf2_axis₂`: linearity and the axis is in the kernel;
* `pl_im4`, `pl_re4`: the two identities.
-/

open Matrix

namespace Lightlike.Regge4

variable {G : Matrix (Fin 4) (Fin 4) ℝ}

/-- The `3 × 3` minor of three vectors on the coordinates `i j k`. -/
def d3 (a b c : Fin 4 → ℝ) (i j k : Fin 4) : ℝ :=
  a i * (b j * c k - b k * c j) - a j * (b i * c k - b k * c i) + a k * (b i * c j - b j * c i)

/-- Cofactor expansion of `det4` along the first row, with explicit `3 × 3` minors. -/
theorem det4_expand (a b c d : Fin 4 → ℝ) :
    det4 a b c d = a 0 * d3 b c d 1 2 3 - a 1 * d3 b c d 0 2 3 + a 2 * d3 b c d 0 1 3
      - a 3 * d3 b c d 0 1 2 := by
  simp only [det4, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove, Fin.lt_def, d3]
  ring

/-- **Five-vector relation**: in `ℝ⁴`, expanding the `5 × 5` determinant with a repeated column. -/
theorem cramer4 (w₁ w₂ t u v : Fin 4 → ℝ) :
    det4 w₂ t u v • w₁ - det4 w₁ t u v • w₂ + det4 w₁ w₂ u v • t - det4 w₁ w₂ t v • u
      + det4 w₁ w₂ t u • v = 0 := by
  ext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  simp only [det4_expand, d3]
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> ring

/-- `bf2` is additive in the first slot. -/
theorem bf2_add (w₁ w₂ x y v : Fin 4 → ℝ) :
    bf2 G w₁ w₂ (x + y) v = bf2 G w₁ w₂ x v + bf2 G w₁ w₂ y v := by
  unfold bf2
  simp only [add_dotProduct]
  ring

/-- `bf2` is homogeneous in the first slot. -/
theorem bf2_smul (w₁ w₂ x v : Fin 4 → ℝ) (a : ℝ) :
    bf2 G w₁ w₂ (a • x) v = a * bf2 G w₁ w₂ x v := by
  unfold bf2
  simp only [smul_dotProduct, smul_eq_mul]
  ring

/-- The first axis vector is in the kernel of the quotient form. -/
theorem bf2_axis₁ (hs : Gᵀ = G) (w₁ w₂ v : Fin 4 → ℝ) (hD : gramW G w₁ w₂ ≠ 0) :
    bf2 G w₁ w₂ w₁ v = 0 := by
  have e1 := sym_pair hs w₂ w₁
  unfold bf2
  have hDeq : gramW G w₁ w₂ = (w₁ ⬝ᵥ (G *ᵥ w₁)) * (w₂ ⬝ᵥ (G *ᵥ w₂))
      - (w₁ ⬝ᵥ (G *ᵥ w₂)) * (w₁ ⬝ᵥ (G *ᵥ w₂)) := by unfold gramW; rw [e1]
  rw [hDeq] at hD ⊢
  simp only [e1]
  generalize w₁ ⬝ᵥ (G *ᵥ w₁) = A at *
  generalize w₂ ⬝ᵥ (G *ᵥ w₂) = B at *
  generalize w₁ ⬝ᵥ (G *ᵥ w₂) = c at *
  generalize w₁ ⬝ᵥ (G *ᵥ v) = p at *
  generalize w₂ ⬝ᵥ (G *ᵥ v) = q at *
  have hD2 : A * B - c ^ 2 ≠ 0 := fun h => hD (by linear_combination h)
  have hD3 : B * A - c ^ 2 ≠ 0 := fun h => hD (by linear_combination h)
  field_simp
  ring

/-- The second axis vector is in the kernel of the quotient form. -/
theorem bf2_axis₂ (hs : Gᵀ = G) (w₁ w₂ v : Fin 4 → ℝ) (hD : gramW G w₁ w₂ ≠ 0) :
    bf2 G w₁ w₂ w₂ v = 0 := by
  have e1 := sym_pair hs w₂ w₁
  unfold bf2
  have hDeq : gramW G w₁ w₂ = (w₁ ⬝ᵥ (G *ᵥ w₁)) * (w₂ ⬝ᵥ (G *ᵥ w₂))
      - (w₁ ⬝ᵥ (G *ᵥ w₂)) * (w₁ ⬝ᵥ (G *ᵥ w₂)) := by unfold gramW; rw [e1]
  rw [hDeq] at hD ⊢
  simp only [e1]
  generalize w₁ ⬝ᵥ (G *ᵥ w₁) = A at *
  generalize w₂ ⬝ᵥ (G *ᵥ w₂) = B at *
  generalize w₁ ⬝ᵥ (G *ᵥ w₂) = c at *
  generalize w₁ ⬝ᵥ (G *ᵥ v) = p at *
  generalize w₂ ⬝ᵥ (G *ᵥ v) = q at *
  have hD2 : A * B - c ^ 2 ≠ 0 := fun h => hD (by linear_combination h)
  have hD3 : B * A - c ^ 2 ≠ 0 := fun h => hD (by linear_combination h)
  field_simp
  ring

/-- **Imaginary part of the Plücker identity** `ζ(u,t) ζ(t,v) = bf2(t,t) ζ(u,v)`. -/
theorem pl_im4 (hs : Gᵀ = G) (w₁ w₂ u v t : Fin 4 → ℝ) (hD : gramW G w₁ w₂ ≠ 0) :
    bf2 G w₁ w₂ u t * det4 w₁ w₂ t v + det4 w₁ w₂ u t * bf2 G w₁ w₂ t v
      = bf2 G w₁ w₂ t t * det4 w₁ w₂ u v := by
  have h := cramer4 w₁ w₂ t u v
  have h' := congrArg (fun x => bf2 G w₁ w₂ x t) h
  simp only [sub_eq_add_neg, ← neg_smul] at h'
  simp only [bf2_add, bf2_smul, bf2_axis₁ hs w₁ w₂ t hD, bf2_axis₂ hs w₁ w₂ t hD] at h'
  have z : bf2 G w₁ w₂ 0 t = 0 := by
    have := bf2_smul (G := G) w₁ w₂ (0 : Fin 4 → ℝ) t 0
    simpa using this
  rw [z] at h'
  have hanti : det4 w₁ w₂ t u = - det4 w₁ w₂ u t := by
    unfold det4
    have : (Matrix.of ![w₁, w₂, t, u]) =
        (Matrix.of ![w₁, w₂, u, t]).submatrix (Equiv.swap (2 : Fin 4) 3) id := by
      ext i j
      fin_cases i <;> simp [Equiv.swap_apply_def]
    rw [this, Matrix.det_permute]
    simp
  rw [bf2_symm hs w₁ w₂ v t, hanti] at h'
  linarith

/-- **Real part of the Plücker identity**. -/
theorem pl_re4 (w₁ w₂ u v t : Fin 4 → ℝ) (hD : gramW G w₁ w₂ ≠ 0) :
    bf2 G w₁ w₂ u t * bf2 G w₁ w₂ t v - G.det / gramW G w₁ w₂ * (det4 w₁ w₂ u t * det4 w₁ w₂ t v)
      = bf2 G w₁ w₂ t t * bf2 G w₁ w₂ u v := by
  have h := bf2_gram G w₁ w₂ u t t v hD
  have : G.det * det4 w₁ w₂ u t * det4 w₁ w₂ t v / gramW G w₁ w₂
      = G.det / gramW G w₁ w₂ * (det4 w₁ w₂ u t * det4 w₁ w₂ t v) := by ring
  linarith

end Lightlike.Regge4
