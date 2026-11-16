import Lightlike.Regge.Dihedral

/-!
# The Schläfli identity for a Euclidean tetrahedron

For a tetrahedron with edge lengths `ℓ_e` and interior dihedral angles `θ_e`, **Schläfli's
identity** says `Σ_e ℓ_e dθ_e = 0` for every variation of the lengths. Equivalently, the
tetrahedron's Regge action `Σ_e ℓ_e (π - θ_e)` has gradient `π - θ_e`, the exterior dihedral
angles. This is the lemma behind Regge's equations of motion.

## Implementation notes

Everything is reduced to polynomials in the edge lengths. For the edge `pq` of the tetrahedron
`pqrs`, with `H_F = 16 · area(F)²` (`heron`) for the two faces `F = pqr, pqs` at the edge:

* `cosDihedral_eq_numN`: `cos θ_pq = N_pq / √(H_pqr H_pqs)` with a polynomial `N_pq` (`numN`).
* `heron_mul_sub_numN_sq`: `H_pqr H_pqs - N_pq² = 576 ℓ_pq² V²`, so `sin θ_pq = 24 V ℓ_pq / √(H H)`.
* `numN_face`: on each face, the three `N` of its edges add up to `H` of the face.

Differentiating, `ℓ_e dθ_e = -(dN_e - N_e (dH_F₁/H_F₁ + dH_F₂/H_F₂)/2) / (24 V)`
(`hasDerivAt_dihedral_line`). Summed over the six edges and regrouped by faces, the face identity
turns the sum into the derivative of `Σ_e N_e - ½ Σ_F H_F`, which is identically zero.

These identities are also checked symbolically, with a failing control, in
`scripts/regge/schlaefli_check.py`.
-/

open Real

namespace Lightlike.Regge

open Lightlike.PR (cosDihedral dihedral vol2)

/-! ## Polynomial forms -/

/-- Sixteen times the squared area of a triangle with side lengths `a, b, c` (Heron's formula):
`2(a²b² + b²c² + c²a²) - (a⁴ + b⁴ + c⁴)`. -/
def heron (a b c : ℝ) : ℝ :=
  2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a ^ 4 + b ^ 4 + c ^ 4)

/-- The polynomial numerator of the cosine of the dihedral angle at the edge `pq` of the
tetrahedron `pqrs`, in the argument order of `Lightlike.PR.cosDihedral`:
`2 pq² (pr² + ps² - rs²) - (pr² + pq² - qr²)(ps² + pq² - qs²)`. -/
def numN (pq pr qr ps qs rs : ℝ) : ℝ :=
  2 * pq ^ 2 * (pr ^ 2 + ps ^ 2 - rs ^ 2) - (pr ^ 2 + pq ^ 2 - qr ^ 2) * (ps ^ 2 + pq ^ 2 - qs ^ 2)

/-- The derivative of `heron` along the line `(a + τ a', b + τ b', c + τ c')` at `τ = 0`. -/
def dHeron (a b c a' b' c' : ℝ) : ℝ :=
  4 * (a * a' * (b ^ 2 + c ^ 2) + b * b' * (a ^ 2 + c ^ 2) + c * c' * (a ^ 2 + b ^ 2)) -
    4 * (a ^ 3 * a' + b ^ 3 * b' + c ^ 3 * c')

/-- The derivative of `numN` along the line `(pq + τ pq', …, rs + τ rs')` at `τ = 0`. -/
def dNumN (pq pr qr ps qs rs pq' pr' qr' ps' qs' rs' : ℝ) : ℝ :=
  4 * pq * pq' * (pr ^ 2 + ps ^ 2 - rs ^ 2) +
    2 * pq ^ 2 * (2 * pr * pr' + 2 * ps * ps' - 2 * rs * rs') -
    (2 * pr * pr' + 2 * pq * pq' - 2 * qr * qr') * (ps ^ 2 + pq ^ 2 - qs ^ 2) -
    (pr ^ 2 + pq ^ 2 - qr ^ 2) * (2 * ps * ps' + 2 * pq * pq' - 2 * qs * qs')

/-- **The cosine of a dihedral angle as a polynomial over a square root**:
`cos θ_pq = N_pq / √(H_pqr H_pqs)`, for a nonzero edge length `pq`. -/
theorem cosDihedral_eq_numN {pq : ℝ} (hpq : pq ≠ 0) (pr qr ps qs rs : ℝ)
    (hH : 0 ≤ heron pq pr qr * heron pq ps qs) :
    cosDihedral pq pr qr ps qs rs =
      numN pq pr qr ps qs rs / √(heron pq pr qr * heron pq ps qs) := by
  have h4 : (4 * pq ^ 2) ≠ 0 := by positivity
  have e1 : pr ^ 2 - ((pr ^ 2 + pq ^ 2 - qr ^ 2) / (2 * pq)) ^ 2 = heron pq pr qr / (4 * pq ^ 2) := by
    unfold heron
    field_simp
    ring
  have e2 : ps ^ 2 - ((ps ^ 2 + pq ^ 2 - qs ^ 2) / (2 * pq)) ^ 2 = heron pq ps qs / (4 * pq ^ 2) := by
    unfold heron
    field_simp
    ring
  have e3 : (pr ^ 2 + ps ^ 2 - rs ^ 2) / 2 -
      (pr ^ 2 + pq ^ 2 - qr ^ 2) / (2 * pq) * ((ps ^ 2 + pq ^ 2 - qs ^ 2) / (2 * pq)) =
      numN pq pr qr ps qs rs / (4 * pq ^ 2) := by
    unfold numN
    field_simp
    ring
  simp only [cosDihedral]
  rw [e1, e2, e3, show heron pq pr qr / (4 * pq ^ 2) * (heron pq ps qs / (4 * pq ^ 2)) =
      (heron pq pr qr * heron pq ps qs) / (4 * pq ^ 2) ^ 2 by ring,
    Real.sqrt_div hH, Real.sqrt_sq (by positivity), div_div_div_cancel_right₀ h4]

/-- **The sine of a dihedral angle**: `H_pqr H_pqs - N_pq² = 576 pq² V²`, with `V²` the squared
volume (`Lightlike.PR.vol2`, labelled `A, B, C, D = p, q, r, s`). -/
theorem heron_mul_sub_numN_sq (pq pr qr ps qs rs : ℝ) :
    heron pq pr qr * heron pq ps qs - numN pq pr qr ps qs rs ^ 2 =
      576 * pq ^ 2 * vol2 pq qr pr rs ps qs := by
  unfold heron numN vol2
  ring

/-- **The face identity**: on the face `pqr` (with fourth vertex `s`), the numerators of the three
edges `pq, qr, rp` add up to `heron` of the face. -/
theorem numN_face (pq pr qr ps qs rs : ℝ) :
    numN pq pr qr ps qs rs + numN qr pq pr qs rs ps + numN pr pq qr ps rs qs = heron pq qr pr := by
  unfold numN heron
  ring

/-! ## Derivatives along a line in the space of lengths -/

/-- The derivative of `τ ↦ x + τ x'` is `x'`. -/
theorem hasDerivAt_line (x x' : ℝ) : HasDerivAt (fun τ : ℝ => x + τ * x') x' 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const x').const_add x

/-- `heron` along a line has derivative `dHeron`. -/
theorem hasDerivAt_heron (a b c a' b' c' : ℝ) :
    HasDerivAt (fun τ => heron (a + τ * a') (b + τ * b') (c + τ * c')) (dHeron a b c a' b' c') 0 :=
  by
  have ha := hasDerivAt_line a a'
  have hb := hasDerivAt_line b b'
  have hc := hasDerivAt_line c c'
  have h := ((((ha.pow 2).mul (hb.pow 2)).add ((hb.pow 2).mul (hc.pow 2))).add
    ((hc.pow 2).mul (ha.pow 2))).const_mul 2 |>.sub (((ha.pow 4).add (hb.pow 4)).add (hc.pow 4))
  unfold heron dHeron
  convert h using 1
  simp
  ring

/-- `numN` along a line has derivative `dNumN`. -/
theorem hasDerivAt_numN (pq pr qr ps qs rs pq' pr' qr' ps' qs' rs' : ℝ) :
    HasDerivAt (fun τ => numN (pq + τ * pq') (pr + τ * pr') (qr + τ * qr') (ps + τ * ps')
      (qs + τ * qs') (rs + τ * rs')) (dNumN pq pr qr ps qs rs pq' pr' qr' ps' qs' rs') 0 := by
  have h1 := hasDerivAt_line pq pq'
  have h2 := hasDerivAt_line pr pr'
  have h3 := hasDerivAt_line qr qr'
  have h4 := hasDerivAt_line ps ps'
  have h5 := hasDerivAt_line qs qs'
  have h6 := hasDerivAt_line rs rs'
  have h := (((h1.pow 2).const_mul 2).mul (((h2.pow 2).add (h4.pow 2)).sub (h6.pow 2))).sub
    ((((h2.pow 2).add (h1.pow 2)).sub (h3.pow 2)).mul (((h4.pow 2).add (h1.pow 2)).sub (h5.pow 2)))
  unfold numN dNumN
  convert h using 1
  simp
  ring

/-- **The derivative of a dihedral angle.** At a non-degenerate tetrahedron (positive edge length
`pq`, non-degenerate faces `pqr, pqs`, positive volume), the dihedral angle at the edge `pq`, along
the line of lengths `(pq + τ pq', …, rs + τ rs')`, has derivative
`-(dN - N (dH_pqr/H_pqr + dH_pqs/H_pqs)/2) / (24 V pq)` at `τ = 0`. -/
theorem hasDerivAt_dihedral_line {pq pr qr ps qs rs : ℝ} (pq' pr' qr' ps' qs' rs' : ℝ)
    (hpq : 0 < pq) (h1 : 0 < heron pq pr qr) (h2 : 0 < heron pq ps qs)
    (hV : 0 < vol2 pq qr pr rs ps qs) :
    HasDerivAt (fun τ => dihedral (pq + τ * pq') (pr + τ * pr') (qr + τ * qr') (ps + τ * ps')
        (qs + τ * qs') (rs + τ * rs'))
      (-(dNumN pq pr qr ps qs rs pq' pr' qr' ps' qs' rs' -
          numN pq pr qr ps qs rs * (dHeron pq pr qr pq' pr' qr' / heron pq pr qr +
            dHeron pq ps qs pq' ps' qs' / heron pq ps qs) / 2) /
        (24 * √(vol2 pq qr pr rs ps qs) * pq)) 0 := by
  have hP0 : 0 < heron pq pr qr * heron pq ps qs := mul_pos h1 h2
  have hN := hasDerivAt_numN pq pr qr ps qs rs pq' pr' qr' ps' qs' rs'
  have hH1 := hasDerivAt_heron pq pr qr pq' pr' qr'
  have hH2 := hasDerivAt_heron pq ps qs pq' ps' qs'
  have hP := hH1.mul hH2
  simp only [zero_mul, add_zero] at hP
  have hS := hP.sqrt (by simpa using hP0.ne')
  have hsP : √(heron pq pr qr * heron pq ps qs) ≠ 0 := (Real.sqrt_pos.mpr hP0).ne'
  have hC := hN.div hS (by simpa using hsP)
  try simp only [zero_mul, add_zero] at hC
  -- `|cos θ| < 1`
  have hid := heron_mul_sub_numN_sq pq pr qr ps qs rs
  have hgap : 0 < 576 * pq ^ 2 * vol2 pq qr pr rs ps qs := by positivity
  have hsq : (numN pq pr qr ps qs rs / √(heron pq pr qr * heron pq ps qs)) ^ 2 < 1 := by
    rw [div_pow, Real.sq_sqrt hP0.le, div_lt_one hP0]
    linarith
  have hbd := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hsq)
  have hA := (Real.hasDerivAt_arccos (by simpa using hbd.1.ne') (by simpa using hbd.2.ne)).comp 0 hC
  -- near `τ = 0` the dihedral angle is `arccos (N / √(H H))`
  have hev : (fun τ => dihedral (pq + τ * pq') (pr + τ * pr') (qr + τ * qr') (ps + τ * ps')
      (qs + τ * qs') (rs + τ * rs')) =ᶠ[nhds 0]
      (Real.arccos ∘ fun τ => numN (pq + τ * pq') (pr + τ * pr') (qr + τ * qr') (ps + τ * ps')
        (qs + τ * qs') (rs + τ * rs') / √(heron (pq + τ * pq') (pr + τ * pr') (qr + τ * qr') *
          heron (pq + τ * pq') (ps + τ * ps') (qs + τ * qs'))) := by
    have e1 : ∀ᶠ τ in nhds (0 : ℝ), 0 < pq + τ * pq' :=
      (hasDerivAt_line pq pq').continuousAt.eventually (lt_mem_nhds (by simpa using hpq))
    have e2 : ∀ᶠ τ in nhds (0 : ℝ), 0 < heron (pq + τ * pq') (pr + τ * pr') (qr + τ * qr') *
        heron (pq + τ * pq') (ps + τ * ps') (qs + τ * qs') :=
      hP.continuousAt.eventually (lt_mem_nhds (by simpa using hP0))
    filter_upwards [e1, e2] with τ hτ1 hτ2
    simp only [Function.comp, dihedral]
    rw [cosDihedral_eq_numN hτ1.ne' _ _ _ _ _ hτ2.le]
  refine (hA.congr_of_eventuallyEq hev).congr_deriv ?_
  -- simplify the derivative
  simp only [Pi.div_apply, Pi.mul_apply, zero_mul, add_zero]
  have hsin : √(1 - (numN pq pr qr ps qs rs / √(heron pq pr qr * heron pq ps qs)) ^ 2) =
      24 * pq * √(vol2 pq qr pr rs ps qs) / √(heron pq pr qr * heron pq ps qs) := by
    rw [div_pow, Real.sq_sqrt hP0.le,
      show 1 - numN pq pr qr ps qs rs ^ 2 / (heron pq pr qr * heron pq ps qs) =
        (24 * pq) ^ 2 * vol2 pq qr pr rs ps qs / (heron pq pr qr * heron pq ps qs) by
        field_simp
        linarith,
      Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsin]
  have hV' : √(vol2 pq qr pr rs ps qs) ≠ 0 := (Real.sqrt_pos.mpr hV).ne'
  have hss : √(heron pq pr qr * heron pq ps qs) ^ 2 = heron pq pr qr * heron pq ps qs :=
    Real.sq_sqrt hP0.le
  field_simp
  rw [hss]

/-! ## Schläfli's identity for a tetrahedron -/

/-- The tetrahedron with edge lengths `l = (AB, BC, CA, CD, AD, BD)` (the labelling of
`Lightlike.PR.extAngles`) is non-degenerate: positive lengths, non-degenerate faces `ABC, ABD, ACD, BCD`,
positive volume. -/
def TetNondeg (l : Fin 6 → ℝ) : Prop :=
  (∀ i, 0 < l i) ∧ 0 < heron (l 0) (l 1) (l 2) ∧ 0 < heron (l 0) (l 5) (l 4) ∧
    0 < heron (l 2) (l 3) (l 4) ∧ 0 < heron (l 1) (l 3) (l 5) ∧
    0 < vol2 (l 0) (l 1) (l 2) (l 3) (l 4) (l 5)

/-- **Schläfli's identity.** At a non-degenerate tetrahedron, for every direction `v` of change of
the six edge lengths, `Σ_e ℓ_e dθ_e = 0`: the derivative at `τ = 0` of
`Σ_e l_e θ_e(l + τ v)` (lengths `l_e` held fixed, angles varying) vanishes. Here
`θ_e = π - Lightlike.PR.extAngles l e` is the interior dihedral angle at the edge `e`. -/
theorem schlaefli (l v : Fin 6 → ℝ) (h : TetNondeg l) :
    HasDerivAt (fun τ => ∑ e, l e * (π - Lightlike.PR.extAngles (fun i => l i + τ * v i) e)) 0 0 := by
  obtain ⟨hl, hABC, hABD, hACD, hBCD, hV⟩ := h
  have pos : ∀ {x y : ℝ}, x = y → 0 < y → 0 < x := fun h hy => h ▸ hy
  -- the six dihedral angles, edge by edge (labelling as in `Lightlike.PR.extAngles`)
  have d0 := (hasDerivAt_dihedral_line (pq := l 0) (pr := l 2) (qr := l 1) (ps := l 4) (qs := l 5)
    (rs := l 3) (v 0) (v 2) (v 1) (v 4) (v 5) (v 3) (hl 0)
    (pos (by unfold heron; ring) hABC) (pos (by unfold heron; ring) hABD)
    (pos (by unfold vol2; ring) hV)).const_mul (l 0)
  have d1 := (hasDerivAt_dihedral_line (pq := l 1) (pr := l 0) (qr := l 2) (ps := l 5) (qs := l 3)
    (rs := l 4) (v 1) (v 0) (v 2) (v 5) (v 3) (v 4) (hl 1)
    (pos (by unfold heron; ring) hABC) (pos (by unfold heron; ring) hBCD)
    (pos (by unfold vol2; ring) hV)).const_mul (l 1)
  have d2 := (hasDerivAt_dihedral_line (pq := l 2) (pr := l 1) (qr := l 0) (ps := l 3) (qs := l 4)
    (rs := l 5) (v 2) (v 1) (v 0) (v 3) (v 4) (v 5) (hl 2)
    (pos (by unfold heron; ring) hABC) (pos (by unfold heron; ring) hACD)
    (pos (by unfold vol2; ring) hV)).const_mul (l 2)
  have d3 := (hasDerivAt_dihedral_line (pq := l 3) (pr := l 2) (qr := l 4) (ps := l 1) (qs := l 5)
    (rs := l 0) (v 3) (v 2) (v 4) (v 1) (v 5) (v 0) (hl 3)
    (pos (by unfold heron; ring) hACD) (pos (by unfold heron; ring) hBCD)
    (pos (by unfold vol2; ring) hV)).const_mul (l 3)
  have d4 := (hasDerivAt_dihedral_line (pq := l 4) (pr := l 0) (qr := l 5) (ps := l 2) (qs := l 3)
    (rs := l 1) (v 4) (v 0) (v 5) (v 2) (v 3) (v 1) (hl 4)
    (pos (by unfold heron; ring) hABD) (pos (by unfold heron; ring) hACD)
    (pos (by unfold vol2; ring) hV)).const_mul (l 4)
  have d5 := (hasDerivAt_dihedral_line (pq := l 5) (pr := l 0) (qr := l 4) (ps := l 1) (qs := l 3)
    (rs := l 2) (v 5) (v 0) (v 4) (v 1) (v 3) (v 2) (hl 5)
    (pos (by unfold heron; ring) hABD) (pos (by unfold heron; ring) hBCD)
    (pos (by unfold vol2; ring) hV)).const_mul (l 5)
  have hsum := (((((d0.add d1).add d2).add d3).add d4).add d5)
  convert hsum using 1
  · funext τ
    simp [Fin.sum_univ_six, Lightlike.PR.extAngles]
  · -- the derivative: `Σ_e l_e θ_e' = 0` by the face identities
    -- one volume
    rw [show vol2 (l 1) (l 2) (l 0) (l 4) (l 5) (l 3) = vol2 (l 0) (l 1) (l 2) (l 3) (l 4) (l 5) by
        unfold vol2; ring,
      show vol2 (l 2) (l 0) (l 1) (l 5) (l 3) (l 4) = vol2 (l 0) (l 1) (l 2) (l 3) (l 4) (l 5) by
        unfold vol2; ring,
      show vol2 (l 3) (l 4) (l 2) (l 0) (l 1) (l 5) = vol2 (l 0) (l 1) (l 2) (l 3) (l 4) (l 5) by
        unfold vol2; ring,
      show vol2 (l 4) (l 5) (l 0) (l 1) (l 2) (l 3) = vol2 (l 0) (l 1) (l 2) (l 3) (l 4) (l 5) by
        unfold vol2; ring,
      show vol2 (l 5) (l 4) (l 0) (l 2) (l 1) (l 3) = vol2 (l 0) (l 1) (l 2) (l 3) (l 4) (l 5) by
        unfold vol2; ring]
    -- one logarithmic derivative `dH/H` per face
    obtain ⟨y₁, hy₁⟩ : ∃ y, dHeron (l 0) (l 1) (l 2) (v 0) (v 1) (v 2) / heron (l 0) (l 1) (l 2) = y :=
      ⟨_, rfl⟩
    obtain ⟨y₂, hy₂⟩ : ∃ y, dHeron (l 0) (l 5) (l 4) (v 0) (v 5) (v 4) / heron (l 0) (l 5) (l 4) = y :=
      ⟨_, rfl⟩
    obtain ⟨y₃, hy₃⟩ : ∃ y, dHeron (l 2) (l 3) (l 4) (v 2) (v 3) (v 4) / heron (l 2) (l 3) (l 4) = y :=
      ⟨_, rfl⟩
    obtain ⟨y₄, hy₄⟩ : ∃ y, dHeron (l 1) (l 3) (l 5) (v 1) (v 3) (v 5) / heron (l 1) (l 3) (l 5) = y :=
      ⟨_, rfl⟩
    have q : ∀ {a b c a' b' c' x y z x' y' z' w : ℝ}, heron a b c = heron x y z →
        dHeron a b c a' b' c' = dHeron x y z x' y' z' →
        dHeron x y z x' y' z' / heron x y z = w → dHeron a b c a' b' c' / heron a b c = w :=
      fun h1 h2 h3 => by rw [h1, h2, h3]
    rw [q (x := l 0) (y := l 1) (z := l 2) (x' := v 0) (y' := v 1) (z' := v 2)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₁,
      q (x := l 0) (y := l 5) (z := l 4) (x' := v 0) (y' := v 5) (z' := v 4)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₂,
      q (x := l 0) (y := l 1) (z := l 2) (x' := v 0) (y' := v 1) (z' := v 2)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₁,
      q (x := l 1) (y := l 3) (z := l 5) (x' := v 1) (y' := v 3) (z' := v 5)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₄,
      q (x := l 0) (y := l 1) (z := l 2) (x' := v 0) (y' := v 1) (z' := v 2)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₁,
      q (x := l 2) (y := l 3) (z := l 4) (x' := v 2) (y' := v 3) (z' := v 4)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₃,
      q (x := l 2) (y := l 3) (z := l 4) (x' := v 2) (y' := v 3) (z' := v 4)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₃,
      q (x := l 1) (y := l 3) (z := l 5) (x' := v 1) (y' := v 3) (z' := v 5)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₄,
      q (x := l 0) (y := l 5) (z := l 4) (x' := v 0) (y' := v 5) (z' := v 4)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₂,
      q (x := l 2) (y := l 3) (z := l 4) (x' := v 2) (y' := v 3) (z' := v 4)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₃,
      q (x := l 0) (y := l 5) (z := l 4) (x' := v 0) (y' := v 5) (z' := v 4)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₂,
      q (x := l 1) (y := l 3) (z := l 5) (x' := v 1) (y' := v 3) (z' := v 5)
        (by unfold heron; ring) (by unfold dHeron; ring) hy₄]
    -- `y_F H_F = dH_F`
    have e₁ : y₁ * heron (l 0) (l 1) (l 2) = dHeron (l 0) (l 1) (l 2) (v 0) (v 1) (v 2) := by
      rw [← hy₁]; field_simp
    have e₂ : y₂ * heron (l 0) (l 5) (l 4) = dHeron (l 0) (l 5) (l 4) (v 0) (v 5) (v 4) := by
      rw [← hy₂]; field_simp
    have e₃ : y₃ * heron (l 2) (l 3) (l 4) = dHeron (l 2) (l 3) (l 4) (v 2) (v 3) (v 4) := by
      rw [← hy₃]; field_simp
    have e₄ : y₄ * heron (l 1) (l 3) (l 5) = dHeron (l 1) (l 3) (l 5) (v 1) (v 3) (v 5) := by
      rw [← hy₄]; field_simp
    -- the face identities
    have f₁ : numN (l 0) (l 2) (l 1) (l 4) (l 5) (l 3) + numN (l 1) (l 0) (l 2) (l 5) (l 3) (l 4) +
        numN (l 2) (l 1) (l 0) (l 3) (l 4) (l 5) = heron (l 0) (l 1) (l 2) := by
      unfold numN heron; ring
    have f₂ : numN (l 0) (l 2) (l 1) (l 4) (l 5) (l 3) + numN (l 4) (l 0) (l 5) (l 2) (l 3) (l 1) +
        numN (l 5) (l 0) (l 4) (l 1) (l 3) (l 2) = heron (l 0) (l 5) (l 4) := by
      unfold numN heron; ring
    have f₃ : numN (l 2) (l 1) (l 0) (l 3) (l 4) (l 5) + numN (l 3) (l 2) (l 4) (l 1) (l 5) (l 0) +
        numN (l 4) (l 0) (l 5) (l 2) (l 3) (l 1) = heron (l 2) (l 3) (l 4) := by
      unfold numN heron; ring
    have f₄ : numN (l 1) (l 0) (l 2) (l 5) (l 3) (l 4) + numN (l 3) (l 2) (l 4) (l 1) (l 5) (l 0) +
        numN (l 5) (l 0) (l 4) (l 1) (l 3) (l 2) = heron (l 1) (l 3) (l 5) := by
      unfold numN heron; ring
    -- cancel the edge lengths
    have hs : 0 < √(vol2 (l 0) (l 1) (l 2) (l 3) (l 4) (l 5)) := Real.sqrt_pos.mpr hV
    have hterm : ∀ {L X : ℝ}, L ≠ 0 →
        L * (-X / (24 * √(vol2 (l 0) (l 1) (l 2) (l 3) (l 4) (l 5)) * L)) =
          -X / (24 * √(vol2 (l 0) (l 1) (l 2) (l 3) (l 4) (l 5))) := fun hL => by
      field_simp
    rw [hterm (hl 0).ne', hterm (hl 1).ne', hterm (hl 2).ne', hterm (hl 3).ne', hterm (hl 4).ne',
      hterm (hl 5).ne']
    rw [← add_div, ← add_div, ← add_div, ← add_div, ← add_div,
      eq_comm, div_eq_zero_iff]
    left
    clear d0 d1 d2 d3 d4 d5 hsum hterm
    simp only [numN, dNumN, heron, dHeron] at f₁ f₂ f₃ f₄ e₁ e₂ e₃ e₄ ⊢
    linear_combination ((1 / 2 : ℝ) * y₁) * f₁ + ((1 / 2 : ℝ) * y₂) * f₂ +
      ((1 / 2 : ℝ) * y₃) * f₃ + ((1 / 2 : ℝ) * y₄) * f₄ + (1 / 2 : ℝ) * (e₁ + e₂ + e₃ + e₄)

/-- Each exterior dihedral angle of a non-degenerate tetrahedron is differentiable along every line
of edge lengths. -/
theorem differentiableAt_extAngles (l v : Fin 6 → ℝ) (h : TetNondeg l) (e : Fin 6) :
    DifferentiableAt ℝ (fun τ => Lightlike.PR.extAngles (fun i => l i + τ * v i) e) 0 := by
  obtain ⟨hl, hABC, hABD, hACD, hBCD, hV⟩ := h
  have pos : ∀ {x y : ℝ}, x = y → 0 < y → 0 < x := fun h hy => h ▸ hy
  fin_cases e <;> simp only [Lightlike.PR.extAngles] <;> simp only [Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Matrix.cons_val] <;> refine DifferentiableAt.const_sub ?_ π
  · exact (hasDerivAt_dihedral_line (pq := l 0) (pr := l 2) (qr := l 1) (ps := l 4) (qs := l 5)
      (rs := l 3) (v 0) (v 2) (v 1) (v 4) (v 5) (v 3) (hl 0) (pos (by unfold heron; ring) hABC)
      (pos (by unfold heron; ring) hABD) (pos (by unfold vol2; ring) hV)).differentiableAt
  · exact (hasDerivAt_dihedral_line (pq := l 1) (pr := l 0) (qr := l 2) (ps := l 5) (qs := l 3)
      (rs := l 4) (v 1) (v 0) (v 2) (v 5) (v 3) (v 4) (hl 1) (pos (by unfold heron; ring) hABC)
      (pos (by unfold heron; ring) hBCD) (pos (by unfold vol2; ring) hV)).differentiableAt
  · exact (hasDerivAt_dihedral_line (pq := l 2) (pr := l 1) (qr := l 0) (ps := l 3) (qs := l 4)
      (rs := l 5) (v 2) (v 1) (v 0) (v 3) (v 4) (v 5) (hl 2) (pos (by unfold heron; ring) hABC)
      (pos (by unfold heron; ring) hACD) (pos (by unfold vol2; ring) hV)).differentiableAt
  · exact (hasDerivAt_dihedral_line (pq := l 3) (pr := l 2) (qr := l 4) (ps := l 1) (qs := l 5)
      (rs := l 0) (v 3) (v 2) (v 4) (v 1) (v 5) (v 0) (hl 3) (pos (by unfold heron; ring) hACD)
      (pos (by unfold heron; ring) hBCD) (pos (by unfold vol2; ring) hV)).differentiableAt
  · exact (hasDerivAt_dihedral_line (pq := l 4) (pr := l 0) (qr := l 5) (ps := l 2) (qs := l 3)
      (rs := l 1) (v 4) (v 0) (v 5) (v 2) (v 3) (v 1) (hl 4) (pos (by unfold heron; ring) hABD)
      (pos (by unfold heron; ring) hACD) (pos (by unfold vol2; ring) hV)).differentiableAt
  · exact (hasDerivAt_dihedral_line (pq := l 5) (pr := l 0) (qr := l 4) (ps := l 1) (qs := l 3)
      (rs := l 2) (v 5) (v 0) (v 4) (v 1) (v 3) (v 2) (hl 5) (pos (by unfold heron; ring) hABD)
      (pos (by unfold heron; ring) hBCD) (pos (by unfold vol2; ring) hV)).differentiableAt

/-- **The gradient of a tetrahedron's Regge action is its exterior dihedral angles.** At a
non-degenerate tetrahedron, along every direction `v` of change of the edge lengths, the
derivative of `Lightlike.PR.reggeAction = Σ_e ℓ_e (π - θ_e)` (the phase of the Ponzano–Regge asymptotic
formula) is `Σ_e v_e (π - θ_e)`. -/
theorem hasDerivAt_reggeAction_tet (l v : Fin 6 → ℝ) (h : TetNondeg l) :
    HasDerivAt (fun τ => Lightlike.PR.reggeAction (fun i => l i + τ * v i))
      (∑ e, v e * Lightlike.PR.extAngles l e) 0 := by
  have hS := schlaefli l v h
  have hg : DifferentiableAt ℝ (fun τ => ∑ e, v e * Lightlike.PR.extAngles (fun i => l i + τ * v i) e) 0 :=
    by
    have : (fun τ => ∑ e, v e * Lightlike.PR.extAngles (fun i => l i + τ * v i) e) =
        ∑ e, fun τ => v e * Lightlike.PR.extAngles (fun i => l i + τ * v i) e := by
      funext τ
      simp
    rw [this]
    exact DifferentiableAt.sum fun e _ => (differentiableAt_extAngles l v h e).const_mul (v e)
  have key : (fun τ => Lightlike.PR.reggeAction (fun i => l i + τ * v i)) = fun τ =>
      (π * ∑ e, l e - ∑ e, l e * (π - Lightlike.PR.extAngles (fun i => l i + τ * v i) e)) +
        id τ * ∑ e, v e * Lightlike.PR.extAngles (fun i => l i + τ * v i) e := by
    funext τ
    simp only [Lightlike.PR.reggeAction, id, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [key]
  convert (hS.const_sub (π * ∑ e, l e)).add ((hasDerivAt_id (0 : ℝ)).mul hg.hasDerivAt) using 1
  simp

end Lightlike.Regge
