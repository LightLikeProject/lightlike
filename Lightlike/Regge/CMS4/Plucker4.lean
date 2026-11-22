import Lightlike.Regge.CMS4.Quot4
import Lightlike.Regge.Conv3.StarAngle

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
* `pl_im4`, `pl_re4`: the two identities;
* `zeta4`, `iota4`, `conj_iota_mul4`: the complex coordinate of the plane quotient;
* `quad_fan4`, `hex_fan4`: the dihedral angles of a closed fan of four or six consecutive positively
  oriented vectors add up to `2π` (the 4D analogue of Conv3 `quad_fan`, `hex_fan`).
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

/-- The area form is antisymmetric. -/
theorem det4_swap (w₁ w₂ t u : Fin 4 → ℝ) : det4 w₁ w₂ t u = - det4 w₁ w₂ u t := by
  unfold det4
  have : (Matrix.of ![w₁, w₂, t, u]) =
      (Matrix.of ![w₁, w₂, u, t]).submatrix (Equiv.swap (2 : Fin 4) 3) id := by
    ext i j
    fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [this, Matrix.det_permute]
  simp

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
  have hanti : det4 w₁ w₂ t u = - det4 w₁ w₂ u t := det4_swap w₁ w₂ t u
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

/-- The `3 × 3` minor is unchanged by adding combinations of the axis (used through `det4`). -/
theorem det4_add_axis (w₁ w₂ t v : Fin 4 → ℝ) (a b : ℝ) :
    det4 w₁ w₂ t (v + a • w₁ + b • w₂) = det4 w₁ w₂ t v := by
  simp only [det4_expand, d3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The area form is odd in the last slot. -/
theorem det4_neg (w₁ w₂ t v : Fin 4 → ℝ) : det4 w₁ w₂ t (-v) = - det4 w₁ w₂ t v := by
  simp only [det4_expand, d3, Pi.neg_apply]
  ring

/-! ### The complex coordinate of the plane quotient -/

open Complex Real

/-- The complex number `bf2 u v + i κ det4 w₁ w₂ u v`, with `κ = √(det G / gramW)`. -/
noncomputable def zeta4 (G : Matrix (Fin 4) (Fin 4) ℝ) (w₁ w₂ u v : Fin 4 → ℝ) : ℂ :=
  ⟨bf2 G w₁ w₂ u v, √(G.det / gramW G w₁ w₂) * det4 w₁ w₂ u v⟩

/-- The squared norm of `zeta4 u v` is `bf2 u u * bf2 v v`. -/
theorem zeta4_normSq (hG : G.PosDef) {w₁ w₂ : Fin 4 → ℝ} (hD : 0 < gramW G w₁ w₂)
    (u v : Fin 4 → ℝ) : Complex.normSq (zeta4 G w₁ w₂ u v) = bf2 G w₁ w₂ u u * bf2 G w₁ w₂ v v := by
  have hd := hG.det_pos
  have hs : Gᵀ = G := by simpa using hG.isHermitian.eq
  have hk : √(G.det / gramW G w₁ w₂) ^ 2 = G.det / gramW G w₁ w₂ :=
    Real.sq_sqrt (div_pos hd hD).le
  have h := bf2_gram G w₁ w₂ u v u v hD.ne'
  rw [bf2_symm hs w₁ w₂ v u] at h
  rw [Complex.normSq_apply]
  simp only [zeta4]
  linear_combination (-1 : ℝ) * h + (det4 w₁ w₂ u v) ^ 2 * hk

/-- If `det (w₁, w₂, u, v) ≠ 0`, `bf2 u u` and `bf2 v v` are positive. -/
theorem bf2_pos_of_det4 (hG : G.PosDef) {w₁ w₂ : Fin 4 → ℝ} (hD : 0 < gramW G w₁ w₂)
    {u v : Fin 4 → ℝ} (h : det4 w₁ w₂ u v ≠ 0) :
    0 < bf2 G w₁ w₂ u u ∧ 0 < bf2 G w₁ w₂ v v :=
  ⟨bf2_diag_pos hG w₁ w₂ u v hD h,
    bf2_diag_pos hG w₁ w₂ v u hD (by rw [det4_swap]; exact neg_ne_zero.2 h)⟩

/-- **The dihedral angle is the argument of `zeta4`.** -/
theorem arccos_eq_arg4 (hG : G.PosDef) {w₁ w₂ : Fin 4 → ℝ} (hD : 0 < gramW G w₁ w₂)
    {x y : Fin 4 → ℝ} (h : 0 < det4 w₁ w₂ x y) :
    arccos (bf2 G w₁ w₂ x y / √(bf2 G w₁ w₂ x x * bf2 G w₁ w₂ y y))
      = arg (zeta4 G w₁ w₂ x y) := by
  have hd := hG.det_pos
  have him : 0 ≤ (zeta4 G w₁ w₂ x y).im := by
    simp only [zeta4]; exact mul_nonneg (Real.sqrt_nonneg _) h.le
  have hne : zeta4 G w₁ w₂ x y ≠ 0 := by
    intro e
    have := congrArg Complex.im e
    simp only [zeta4, Complex.zero_im] at this
    have hk : 0 < √(G.det / gramW G w₁ w₂) := Real.sqrt_pos.2 (div_pos hd hD)
    exact (mul_pos hk h).ne' this
  rw [Complex.arg_of_im_nonneg_of_ne_zero him hne]
  have : ‖zeta4 G w₁ w₂ x y‖ = √(bf2 G w₁ w₂ x x * bf2 G w₁ w₂ y y) := by
    rw [Complex.norm_def, zeta4_normSq hG hD]
  rw [this]; rfl

/-- The Plücker identity `ζ(u,t) ζ(t,v) = bf2(t,t) ζ(u,v)` for the complex numbers `zeta4`. -/
theorem zeta4_mul (hG : G.PosDef) {w₁ w₂ : Fin 4 → ℝ} (hD : 0 < gramW G w₁ w₂)
    (u t v : Fin 4 → ℝ) :
    zeta4 G w₁ w₂ u t * zeta4 G w₁ w₂ t v = (bf2 G w₁ w₂ t t : ℂ) * zeta4 G w₁ w₂ u v := by
  have hd := hG.det_pos
  have hs : Gᵀ = G := by simpa using hG.isHermitian.eq
  have hk : √(G.det / gramW G w₁ w₂) ^ 2 = G.det / gramW G w₁ w₂ :=
    Real.sq_sqrt (div_pos hd hD).le
  have r := pl_re4 (G := G) w₁ w₂ u v t hD.ne'
  have i := pl_im4 hs w₁ w₂ u v t hD.ne'
  apply Complex.ext
  · simp only [zeta4, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linear_combination r - (det4 w₁ w₂ u t * det4 w₁ w₂ t v) * hk
  · simp only [zeta4, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    linear_combination (√(G.det / gramW G w₁ w₂)) * i

/-- The complex coordinate of `v` in the plane quotient, with `t` on the real axis. -/
noncomputable def iota4 (G : Matrix (Fin 4) (Fin 4) ℝ) (w₁ w₂ t v : Fin 4 → ℝ) : ℂ :=
  zeta4 G w₁ w₂ t v / (√(bf2 G w₁ w₂ t t) : ℝ)

/-- `conj (ι u) * ι v = ζ(u,v)`. -/
theorem conj_iota_mul4 (hG : G.PosDef) {w₁ w₂ : Fin 4 → ℝ} (hD : 0 < gramW G w₁ w₂)
    {t : Fin 4 → ℝ} (ht : 0 < bf2 G w₁ w₂ t t) (u v : Fin 4 → ℝ) :
    starRingEnd ℂ (iota4 G w₁ w₂ t u) * iota4 G w₁ w₂ t v = zeta4 G w₁ w₂ u v := by
  have hs : Gᵀ = G := by simpa using hG.isHermitian.eq
  have hconj : starRingEnd ℂ (zeta4 G w₁ w₂ t u) = zeta4 G w₁ w₂ u t := by
    apply Complex.ext
    · simp [zeta4, bf2_symm hs w₁ w₂ t u]
    · simp [zeta4, det4_swap w₁ w₂ u t]
  have h2 : ((√(bf2 G w₁ w₂ t t) : ℝ) : ℂ) ^ 2 = (bf2 G w₁ w₂ t t : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht.le]
  have hs0 : ((√(bf2 G w₁ w₂ t t) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ht).ne'
  have hb0 : (bf2 G w₁ w₂ t t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  unfold iota4
  rw [map_div₀, hconj, Complex.conj_ofReal]
  rw [div_mul_div_comm, zeta4_mul hG hD, ← pow_two, h2]
  field_simp

/-- Adding a combination of the axis does not change the complex coordinate. -/
theorem iota4_add_axis (hs : Gᵀ = G) {w₁ w₂ : Fin 4 → ℝ} (hD : gramW G w₁ w₂ ≠ 0)
    (t v : Fin 4 → ℝ) (a b : ℝ) :
    iota4 G w₁ w₂ t (v + a • w₁ + b • w₂) = iota4 G w₁ w₂ t v := by
  have e1 : bf2 G w₁ w₂ t (v + a • w₁ + b • w₂) = bf2 G w₁ w₂ t v := by
    rw [bf2_symm hs w₁ w₂ t (v + a • w₁ + b • w₂), bf2_symm hs w₁ w₂ t v, bf2_add, bf2_add,
      bf2_smul, bf2_smul, bf2_axis₁ hs w₁ w₂ t hD, bf2_axis₂ hs w₁ w₂ t hD]
    ring
  unfold iota4 zeta4
  rw [e1, det4_add_axis]

/-- The complex coordinate is odd. -/
theorem iota4_neg (hs : Gᵀ = G) {w₁ w₂ : Fin 4 → ℝ} (t v : Fin 4 → ℝ) :
    iota4 G w₁ w₂ t (-v) = - iota4 G w₁ w₂ t v := by
  have e1 : bf2 G w₁ w₂ t (-v) = - bf2 G w₁ w₂ t v := by
    have : -v = (-1 : ℝ) • v := by simp
    rw [bf2_symm hs w₁ w₂ t (-v), bf2_symm hs w₁ w₂ t v, this, bf2_smul]
    ring
  unfold iota4 zeta4
  rw [e1, det4_neg]
  apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> ring

/-- The angle between the quotient vectors of `x` and `y` modulo the axis plane. -/
noncomputable def fanAng4 (G : Matrix (Fin 4) (Fin 4) ℝ) (w₁ w₂ x y : Fin 4 → ℝ) : ℝ :=
  arccos (bf2 G w₁ w₂ x y / √(bf2 G w₁ w₂ x x * bf2 G w₁ w₂ y y))

/-- The complex coordinate of a vector off the axis plane is nonzero. -/
theorem iota4_ne (hG : G.PosDef) {w₁ w₂ : Fin 4 → ℝ} (hD : 0 < gramW G w₁ w₂)
    {t v : Fin 4 → ℝ} (ht : 0 < bf2 G w₁ w₂ t t) (hv : 0 < bf2 G w₁ w₂ v v) :
    iota4 G w₁ w₂ t v ≠ 0 := by
  intro e
  have h1 : zeta4 G w₁ w₂ t v = 0 := by
    have hs : ((√(bf2 G w₁ w₂ t t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 ht).ne'
    unfold iota4 at e
    exact (div_eq_zero_iff.1 e).resolve_right hs
  have := zeta4_normSq hG hD t v
  rw [h1] at this
  simp at this
  rcases this with h | h <;> linarith

/-- **A fan of four** in the plane quotient: four consecutive positively oriented vectors that
close up modulo the axis plane have angles adding to `2π`. -/
theorem quad_fan4 (hG : G.PosDef) {w₁ w₂ : Fin 4 → ℝ} (hD : 0 < gramW G w₁ w₂)
    (v : ℕ → Fin 4 → ℝ) (hpos : ∀ i < 4, 0 < det4 w₁ w₂ (v i) (v (i + 1)))
    (hc : ∃ a b : ℝ, v 4 = v 0 + a • w₁ + b • w₂) :
    ∑ i ∈ Finset.range 4, fanAng4 G w₁ w₂ (v i) (v (i + 1)) = 2 * π := by
  have hs : Gᵀ = G := by simpa using hG.isHermitian.eq
  have hp : ∀ i < 4, 0 < bf2 G w₁ w₂ (v i) (v i) ∧ 0 < bf2 G w₁ w₂ (v (i + 1)) (v (i + 1)) :=
    fun i hi => bf2_pos_of_det4 hG hD (hpos i hi).ne'
  have ht : 0 < bf2 G w₁ w₂ (v 0) (v 0) := (hp 0 (by norm_num)).1
  have hpos' : ∀ i ≤ 4, 0 < bf2 G w₁ w₂ (v i) (v i) := by
    intro i hi
    rcases Nat.lt_or_ge i 4 with h | h
    · exact (hp i h).1
    · have : i = 4 := by omega
      subst this; exact (hp 3 (by norm_num)).2
  set z : ℕ → ℂ := fun i => iota4 G w₁ w₂ (v 0) (v i) with hz
  have hz0 : ∀ i ≤ 4, z i ≠ 0 := fun i hi => iota4_ne hG hD ht (hpos' i hi)
  have him : ∀ i < 4, 0 < (starRingEnd ℂ (z i) * z (i + 1)).im := by
    intro i hi
    simp only [hz]
    rw [conj_iota_mul4 hG hD ht]
    simp only [zeta4]
    exact mul_pos (Real.sqrt_pos.2 (div_pos hG.det_pos hD)) (hpos i hi)
  obtain ⟨a, b, hc⟩ := hc
  have h4 : z 4 = z 0 := by simp only [hz]; rw [hc, iota4_add_axis hs hD.ne']
  have := Lightlike.Regge.Conv3.fan_two_pi_quad z hz0 him h4
  rw [← this]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  simp only [hz]
  rw [conj_iota_mul4 hG hD ht, ← arccos_eq_arg4 hG hD (hpos i hi')]
  rfl

/-- **A fan of six** with `v (i+3) = -v i` modulo the axis plane: the angles add to `2π`. -/
theorem hex_fan4 (hG : G.PosDef) {w₁ w₂ : Fin 4 → ℝ} (hD : 0 < gramW G w₁ w₂)
    (v : ℕ → Fin 4 → ℝ) (hpos : ∀ i < 6, 0 < det4 w₁ w₂ (v i) (v (i + 1)))
    (h3 : ∃ a b : ℝ, v 3 = -v 0 + a • w₁ + b • w₂)
    (h6 : ∃ a b : ℝ, v 6 = -v 3 + a • w₁ + b • w₂) :
    ∑ i ∈ Finset.range 6, fanAng4 G w₁ w₂ (v i) (v (i + 1)) = 2 * π := by
  have hs : Gᵀ = G := by simpa using hG.isHermitian.eq
  have hp : ∀ i < 6, 0 < bf2 G w₁ w₂ (v i) (v i) ∧ 0 < bf2 G w₁ w₂ (v (i + 1)) (v (i + 1)) :=
    fun i hi => bf2_pos_of_det4 hG hD (hpos i hi).ne'
  have ht : 0 < bf2 G w₁ w₂ (v 0) (v 0) := (hp 0 (by norm_num)).1
  have hpos' : ∀ i ≤ 6, 0 < bf2 G w₁ w₂ (v i) (v i) := by
    intro i hi
    rcases Nat.lt_or_ge i 6 with h | h
    · exact (hp i h).1
    · have : i = 6 := by omega
      subst this; exact (hp 5 (by norm_num)).2
  set z : ℕ → ℂ := fun i => iota4 G w₁ w₂ (v 0) (v i) with hz
  have hz0 : ∀ i ≤ 6, z i ≠ 0 := fun i hi => iota4_ne hG hD ht (hpos' i hi)
  have him : ∀ i < 6, 0 < (starRingEnd ℂ (z i) * z (i + 1)).im := by
    intro i hi
    simp only [hz]
    rw [conj_iota_mul4 hG hD ht]
    simp only [zeta4]
    exact mul_pos (Real.sqrt_pos.2 (div_pos hG.det_pos hD)) (hpos i hi)
  obtain ⟨a3, b3, hc3⟩ := h3
  obtain ⟨a6, b6, hc6⟩ := h6
  have e3 : z 3 = -(1 : ℝ) * z 0 := by
    simp only [hz]; rw [hc3, iota4_add_axis hs hD.ne', iota4_neg hs]; push_cast; ring
  have e6 : z 6 = -(1 : ℝ) * z 3 := by
    simp only [hz]; rw [hc6, iota4_add_axis hs hD.ne', iota4_neg hs]; push_cast; ring
  have A := Lightlike.Regge.Conv3.fan_pi_three z (fun i hi => hz0 i (by omega))
    (fun i hi => him i (by omega)) one_pos (by simpa using e3)
  have B := Lightlike.Regge.Conv3.fan_pi_three (fun i => z (i + 3))
    (fun i hi => hz0 (i + 3) (by omega))
    (fun i hi => him (i + 3) (by omega)) one_pos (by simpa using e6)
  have key : ∀ i < 6, fanAng4 G w₁ w₂ (v i) (v (i + 1))
      = arg (starRingEnd ℂ (z i) * z (i + 1)) := by
    intro i hi
    simp only [hz]
    rw [conj_iota_mul4 hG hD ht, ← arccos_eq_arg4 hG hD (hpos i hi)]
    rfl
  rw [Finset.sum_congr rfl fun i hi => key i (Finset.mem_range.1 hi)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at A B ⊢
  linarith

end Lightlike.Regge4
