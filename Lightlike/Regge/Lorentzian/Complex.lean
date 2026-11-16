import Lightlike.Regge.Lorentzian.Dihedral
import Lightlike.Regge.D4.Manifold

/-!
# Lorentzian deficit angles and the Lorentzian Regge action

The Lorentzian counterpart of `Lightlike/Regge/D4/Complex.lean`, in the conventions of Asante, Dittrich and
Padua-Argüelles (ADP, arXiv:2104.00485, Section III, eq. 3.1), following Sorkin (Phys. Rev. D 12
(1975) 385; arXiv:1908.10022). The data are the signed squared lengths `L` of the edges of a
4-dimensional simplicial complex.

A triangle `t` is **spacelike** if `16 A_t² = triHL L t > 0` and **timelike** if it is negative.
Its causal factor `Z_t` (`causalZ`) is `−i` for a spacelike and `1` for a timelike triangle, the
flat value of the angle sum around it being `2π Z_t`: `−2πi` (four light rays, Sorkin's convention)
or `2π`. The **deficit angle** is `ε_t = 2π Z_t − Σ_{σ ⊃ t} θ_{tσ}` and the action is
`S = Σ_t A_t ε_t`, with positive areas `A_t = √|triHL L t| / 4` for both causal types, plus the
boundary term with `π Z_t` (ADP's `Z_t / 2`) in place of `2π Z_t`. The action is complex valued.

## Main results

* `lorDihedralAt L σ t`: the dihedral angle of the 4-simplex `σ` at its triangle `t`, without
  choosing a labelling (`Lightlike.Regge4.angleAvg4` of its real and imaginary parts).
* `triHL L t`: sixteen times the signed squared area, Heron's formula in squared lengths.
* `causalZ L t`, `lorAngleSum`, `lorDeficit`, `lorBdryAngle`, `lorArea`, `lorReggeAction`.

* `lorDihedralAt_eq`: in any labelling, `lorDihedralAt` is the length formula `lorDihedral4`.
* `triHL_eq`: `triHL L {p, q, r} = 4 · gram2L L p q r`; `triHL_sq`: for `L = ℓ²` it is the
  Heron polynomial `Lightlike.Regge.triH ℓ` of M7.
* `lorArea_eq`: `A_t = √|gram2L| / 2`.
* `lorAngleSum_eq_of_cycleLink`: around an interior triangle whose link is a cycle, the angle sum
  runs once over the 4-simplices of the link.
* `lorReggeAction_of_bdryTets_eq_empty`: for a closed triangulation the action is `Σ_t A_t ε_t`.
-/

open Real Finset

namespace Lightlike.ReggeLor

open Lightlike.FourD (Complex4)
open Lightlike.Regge4 (angleAvg4 IsSymm4 angleAvg4_eq intTris4 bdryTris4 IsCycleLink4)

variable {V : Type*} [DecidableEq V]

/-! ## Labelling-free dihedral angles -/

/-- The real part of the Lorentzian dihedral angle formula is symmetric. -/
theorem isSymm4_lorDihedral4_re :
    IsSymm4 (fun L p q r s u => (lorDihedral4 (V := V) L p q r s u).re) :=
  ⟨fun L p q r s u => by rw [lorDihedral4_swap_pq], fun L p q r s u => by rw [lorDihedral4_swap_qr],
    fun L p q r s u => by rw [lorDihedral4_swap_su]⟩

/-- The imaginary part of the Lorentzian dihedral angle formula is symmetric. -/
theorem isSymm4_lorDihedral4_im :
    IsSymm4 (fun L p q r s u => (lorDihedral4 (V := V) L p q r s u).im) :=
  ⟨fun L p q r s u => by rw [lorDihedral4_swap_pq], fun L p q r s u => by rw [lorDihedral4_swap_qr],
    fun L p q r s u => by rw [lorDihedral4_swap_su]⟩

/-- The Lorentzian dihedral angle of the 4-simplex `σ` at its triangle `t`, without choosing a
labelling: the real and imaginary parts of `lorDihedral4`, each averaged over the `12` labellings
of `t` and of `σ \ t`. -/
noncomputable def lorDihedralAt (L : Finset V → ℝ) (σ t : Finset V) : ℂ :=
  ⟨angleAvg4 (fun L p q r s u => (lorDihedral4 L p q r s u).re) L σ t,
    angleAvg4 (fun L p q r s u => (lorDihedral4 L p q r s u).im) L σ t⟩

/-- The dihedral angle of the 4-simplex `{p, q, r, s, u}` at its triangle `{p, q, r}` is the
length formula in this labelling. -/
theorem lorDihedralAt_eq (L : Finset V → ℝ) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s)
    (hru : r ≠ u) (hsu : s ≠ u) :
    lorDihedralAt L {p, q, r, s, u} {p, q, r} = lorDihedral4 L p q r s u := by
  apply Complex.ext
  · exact angleAvg4_eq isSymm4_lorDihedral4_re L hpq hpr hps hpu hqr hqs hqu hrs hru hsu
  · exact angleAvg4_eq isSymm4_lorDihedral4_im L hpq hpr hps hpu hqr hqs hqu hrs hru hsu

/-! ## Areas and causal types -/

/-- Sixteen times the signed squared area of the triangle `t`, from its signed squared edge
lengths (Heron's formula, `(Σ_e L_e)² − 2 Σ_e L_e²`): positive for a spacelike, negative for a
timelike triangle. -/
noncomputable def triHL (L : Finset V → ℝ) (t : Finset V) : ℝ :=
  (∑ e ∈ t.powersetCard 2, L e) ^ 2 - 2 * ∑ e ∈ t.powersetCard 2, L e ^ 2

/-- Heron's formula in squared lengths is four times the Gram determinant. -/
theorem triHL_eq (L : Finset V → ℝ) {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    triHL L {p, q, r} = 4 * gram2L L p q r := by
  rw [triHL, Lightlike.Regge.sum_powersetCard_two_three hpq hpr hqr,
    Lightlike.Regge.sum_powersetCard_two_three hpq hpr hqr]
  simp only [gram2L, ipL, sqL, hpq, hpr, hqr, Ne.symm hqr, ↓reduceIte, pair_comm r p,
    pair_comm r q]
  ring

omit [DecidableEq V] in
/-- For `L = ℓ²`, `triHL` is the Heron polynomial `Lightlike.Regge.triH` of the Euclidean theory. -/
theorem triHL_sq (ℓ : Finset V → ℝ) (t : Finset V) :
    triHL (fun e => ℓ e ^ 2) t = Lightlike.Regge.triH ℓ t := by
  simp only [triHL, Lightlike.Regge.triH, ← pow_mul]

/-- The **causal factor** `Z_t` of the triangle `t` (ADP eq. 3.1): `−i` for a spacelike and `1` for
a timelike triangle. `2π Z_t` is the angle sum around a flat interior triangle. -/
noncomputable def causalZ (L : Finset V → ℝ) (t : Finset V) : ℂ :=
  if 0 < triHL L t then -Complex.I else 1

/-- The area of the triangle `t`, positive for both causal types: `√|triHL| / 4`. -/
noncomputable def lorArea (L : Finset V → ℝ) (t : Finset V) : ℝ := √|triHL L t| / 4

/-- The area of the triangle `pqr` is `√|gram2L| / 2`. -/
theorem lorArea_eq (L : Finset V → ℝ) {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    lorArea L {p, q, r} = √|gram2L L p q r| / 2 := by
  rw [lorArea, triHL_eq L hpq hpr hqr, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  ring

/-! ## Deficit angles and the action -/

/-- The sum of the dihedral angles at `t` of the 4-simplices around it. -/
noncomputable def lorAngleSum (K : Complex4 V) (L : Finset V → ℝ) (t : Finset V) : ℂ :=
  ∑ σ ∈ K.star t, lorDihedralAt L σ t

/-- The **Lorentzian deficit angle** `ε_t = 2π Z_t − Σ_{σ ⊃ t} θ_{tσ}` at an interior triangle. -/
noncomputable def lorDeficit (K : Complex4 V) (L : Finset V → ℝ) (t : Finset V) : ℂ :=
  2 * π * causalZ L t - lorAngleSum K L t

/-- The boundary angle `π Z_t − Σ_{σ ⊃ t} θ_{tσ}` at a boundary triangle. -/
noncomputable def lorBdryAngle (K : Complex4 V) (L : Finset V → ℝ) (t : Finset V) : ℂ :=
  π * causalZ L t - lorAngleSum K L t

/-- The **Lorentzian Regge action** (ADP eq. 3.1): `Σ_t A_t ε_t` over the interior triangles plus
the boundary term `Σ_{t ∈ ∂} A_t (π Z_t − Σ θ)`. -/
noncomputable def lorReggeAction (K : Complex4 V) (L : Finset V → ℝ) : ℂ :=
  ∑ t ∈ intTris4 K, (lorArea L t : ℂ) * lorDeficit K L t +
    ∑ t ∈ bdryTris4 K, (lorArea L t : ℂ) * lorBdryAngle K L t

/-- For a closed triangulation (no boundary tetrahedra) the action is `Σ_t A_t ε_t`. -/
theorem lorReggeAction_of_bdryTets_eq_empty {K : Complex4 V} (h : K.bdryTets = ∅)
    (L : Finset V → ℝ) :
    lorReggeAction K L = ∑ t ∈ K.tris, (lorArea L t : ℂ) * lorDeficit K L t := by
  simp [lorReggeAction, intTris4, bdryTris4, h]

variable {K : Complex4 V} {a b c : V} {n : ℕ} {w : ℕ → V}

/-- Around a triangle whose link is a cycle, the angle sum runs once over the 4-simplices
`{a, b, c, w i, w (i+1)}`. -/
theorem lorAngleSum_eq_of_cycleLink (h : IsCycleLink4 K a b c n w) (L : Finset V → ℝ) :
    lorAngleSum K L {a, b, c} =
      ∑ i ∈ range n, lorDihedralAt L {a, b, c, w i, w (i + 1)} {a, b, c} := by
  rw [lorAngleSum, h.star_eq, sum_image h.injOn_simp]

end Lightlike.ReggeLor
