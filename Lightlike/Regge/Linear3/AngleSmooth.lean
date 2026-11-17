import Lightlike.Regge.Schlaefli
import Lightlike.Regge.Conv3.DihedralTaylor2
import Lightlike.Regge.ReggeEquations

/-!
# Dihedral angles along a line of squared lengths

For non-degenerate lengths `ℓ₀` on a 3-complex and a direction `a`, `lenLine ℓ₀ a ε` is the length
assignment whose squares are `ℓ₀² + ε a`. The dihedral angle of a tetrahedron at one of its edges is
a `C³` function of `ε` at `0` (`contDiffAt_dihedralAt`): the length formula is the angle `Dsq` of the
squared lengths (`dihedral_sqrt_eq`), which is `C³` at admissible tuples
(`Lightlike.Regge.Conv3.contDiffAt_Dsq`), and a non-degenerate tetrahedron has admissible squared
lengths (`valid_of_tetNondeg`).

## Main results

* `valid_of_tetNondeg`: non-degenerate lengths give admissible squared lengths.
* `dihedral_sqrt_eq`: `dihedral (√A) … (√F) = Dsq ![A, …, F]` for positive `A`.
* `contDiffAt_dihedralAt`: smoothness of the angle along the line.
-/

open Real
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3 Lightlike.PR

/-- A non-degenerate tetrahedron (in the labelling `pq, qr, pr, rs, ps, qs` of `labLen`) has
admissible squared lengths `(pq², pr², qr², ps², qs², rs²)` for the dihedral angle at `pq`. -/
theorem valid_of_tetNondeg {pq pr qr ps qs rs : ℝ}
    (h : TetNondeg ![pq, qr, pr, rs, ps, qs]) :
    Valid ![pq ^ 2, pr ^ 2, qr ^ 2, ps ^ 2, qs ^ 2, rs ^ 2] := by
  obtain ⟨hl, hH1, hH2, -, -, hV⟩ := h
  have hpq : 0 < pq := by simpa using hl 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at hH1 hH2 hV
  have e1 : heron pq pr qr = heron pq qr pr := by unfold heron; ring
  have e2 : heron pq ps qs = heron pq qs ps := by unfold heron; ring
  have a : 0 < pq ^ 2 := by positivity
  have hP1 : 0 < Conv3.Pp (pq ^ 2) (pr ^ 2) (qr ^ 2) := by
    have : Conv3.Pp (pq ^ 2) (pr ^ 2) (qr ^ 2) = heron pq qr pr / (4 * pq ^ 2) := by
      unfold Conv3.Pp heron; field_simp; ring
    rw [this]; positivity
  have hP2 : 0 < Conv3.Pp (pq ^ 2) (ps ^ 2) (qs ^ 2) := by
    have : Conv3.Pp (pq ^ 2) (ps ^ 2) (qs ^ 2) = heron pq qs ps / (4 * pq ^ 2) := by
      unfold Conv3.Pp heron; field_simp; ring
    rw [this]; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using a
  · simpa using hP1
  · simpa using hP2
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    have hN : Conv3.Nn (pq ^ 2) (pr ^ 2) (qr ^ 2) (ps ^ 2) (qs ^ 2) (rs ^ 2) =
        numN pq pr qr ps qs rs / (4 * pq ^ 2) := by
      unfold Conv3.Nn numN; field_simp; ring
    have hP1' : Conv3.Pp (pq ^ 2) (pr ^ 2) (qr ^ 2) = heron pq qr pr / (4 * pq ^ 2) := by
      unfold Conv3.Pp heron; field_simp; ring
    have hP2' : Conv3.Pp (pq ^ 2) (ps ^ 2) (qs ^ 2) = heron pq qs ps / (4 * pq ^ 2) := by
      unfold Conv3.Pp heron; field_simp; ring
    have key := heron_mul_sub_numN_sq pq pr qr ps qs rs
    rw [e1, e2] at key
    have hlt : Conv3.Nn (pq ^ 2) (pr ^ 2) (qr ^ 2) (ps ^ 2) (qs ^ 2) (rs ^ 2) ^ 2 <
        Conv3.Pp (pq ^ 2) (pr ^ 2) (qr ^ 2) * Conv3.Pp (pq ^ 2) (ps ^ 2) (qs ^ 2) := by
      have hpos : 0 < heron pq qr pr * heron pq qs ps - numN pq pr qr ps qs rs ^ 2 := by
        rw [key]; positivity
      rw [hN, hP1', hP2', ← sub_pos]
      have : heron pq qr pr / (4 * pq ^ 2) * (heron pq qs ps / (4 * pq ^ 2)) -
          (numN pq pr qr ps qs rs / (4 * pq ^ 2)) ^ 2 =
          (heron pq qr pr * heron pq qs ps - numN pq pr qr ps qs rs ^ 2) / (4 * pq ^ 2) ^ 2 := by
        field_simp
      rw [this]; positivity
    unfold Conv3.cosSq
    rw [div_pow, Real.sq_sqrt (mul_pos hP1 hP2).le, sub_pos, div_lt_one (mul_pos hP1 hP2)]
    exact hlt


open Filter Topology Finset
open Lightlike.PR (Complex3)

variable {V : Type*} [DecidableEq V]

/-- The squared lengths `ℓ₀² + ε a` along the direction `a`. -/
def sqLine (ℓ₀ a : Finset V → ℝ) (ε : ℝ) (f : Finset V) : ℝ := ℓ₀ f ^ 2 + ε * a f

/-- The lengths whose squares are `sqLine ℓ₀ a ε`. -/
noncomputable def lenLine (ℓ₀ a : Finset V → ℝ) (ε : ℝ) (f : Finset V) : ℝ := √(sqLine ℓ₀ a ε f)

/-- For positive squared lengths the dihedral angle of the length formula is `Dsq` of the squares. -/
theorem dihedral_sqrt_eq {A B C D E F : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hF : 0 ≤ F) :
    dihedral (√A) (√B) (√C) (√D) (√E) (√F) = Dsq ![A, B, C, D, E, F] := by
  unfold dihedral Dsq dihSq
  rw [cosDihedral_sqrt hA hB hC hD hE hF]
  rfl

/-- **The dihedral angles are `C³` along a line of squared lengths.** For non-degenerate `ℓ₀` and
the tetrahedron `{p, q, r, s}`, the dihedral angle at `{p, q}` of the lengths `lenLine ℓ₀ a ε` is a
`C³` function of `ε` at `0`. -/
theorem contDiffAt_dihedralAt {K : Complex3 V} {ℓ₀ : Finset V → ℝ} (hK : LengthsNondeg K ℓ₀)
    (a : Finset V → ℝ) {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) (ht : ({p, q, r, s} : Finset V) ∈ K.tets) :
    ContDiffAt ℝ 3 (fun ε => dihedralAt (lenLine ℓ₀ a ε) {p, q, r, s} {p, q}) 0 := by
  have hnd := hK.tetNondeg hpq hpr hps hqr hqs hrs ht
  have hpos : ∀ x y : V, x ≠ y → x ∈ ({p, q, r, s} : Finset V) → y ∈ ({p, q, r, s} : Finset V) →
      0 < ℓ₀ {x, y} := fun x y hxy hx hy =>
    (hK _ ht).1 _ (mem_powersetCard.mpr ⟨by simp [insert_subset_iff, hx, hy], card_pair hxy⟩)
  have hv : Valid ![ℓ₀ {p, q} ^ 2, ℓ₀ {p, r} ^ 2, ℓ₀ {q, r} ^ 2, ℓ₀ {p, s} ^ 2, ℓ₀ {q, s} ^ 2,
      ℓ₀ {r, s} ^ 2] := valid_of_tetNondeg (by
      have := hnd
      simp only [labLen, pair_comm r p] at this
      simpa using this)
  have hL0 : (fun ε : ℝ => (![sqLine ℓ₀ a ε {p, q}, sqLine ℓ₀ a ε {p, r}, sqLine ℓ₀ a ε {q, r},
      sqLine ℓ₀ a ε {p, s}, sqLine ℓ₀ a ε {q, s}, sqLine ℓ₀ a ε {r, s}] : Fin 6 → ℝ)) 0 =
      ![ℓ₀ {p, q} ^ 2, ℓ₀ {p, r} ^ 2, ℓ₀ {q, r} ^ 2, ℓ₀ {p, s} ^ 2, ℓ₀ {q, s} ^ 2, ℓ₀ {r, s} ^ 2] := by
    simp [sqLine]
  have hsm : ContDiff ℝ 3 (fun ε : ℝ => (![sqLine ℓ₀ a ε {p, q}, sqLine ℓ₀ a ε {p, r},
      sqLine ℓ₀ a ε {q, r}, sqLine ℓ₀ a ε {p, s}, sqLine ℓ₀ a ε {q, s}, sqLine ℓ₀ a ε {r, s}] : Fin 6 → ℝ)) := by
    unfold sqLine
    refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have hG : ContDiffAt ℝ 3 (fun ε : ℝ => Dsq ![sqLine ℓ₀ a ε {p, q}, sqLine ℓ₀ a ε {p, r},
      sqLine ℓ₀ a ε {q, r}, sqLine ℓ₀ a ε {p, s}, sqLine ℓ₀ a ε {q, s}, sqLine ℓ₀ a ε {r, s}]) 0 := by
    have h1 := contDiffAt_Dsq (L := (fun ε : ℝ => (![sqLine ℓ₀ a ε {p, q}, sqLine ℓ₀ a ε {p, r},
      sqLine ℓ₀ a ε {q, r}, sqLine ℓ₀ a ε {p, s}, sqLine ℓ₀ a ε {q, s}, sqLine ℓ₀ a ε {r, s}] : Fin 6 → ℝ)) 0)
      (by rw [hL0]; exact hv)
    exact ContDiffAt.comp (g := Dsq) 0 h1 hsm.contDiffAt
  refine hG.congr_of_eventuallyEq ?_
  have hev : ∀ x y : V, x ≠ y → x ∈ ({p, q, r, s} : Finset V) → y ∈ ({p, q, r, s} : Finset V) →
      ∀ᶠ ε : ℝ in 𝓝 0, 0 < sqLine ℓ₀ a ε {x, y} := fun x y hxy hx hy => by
    have hc : Continuous (fun ε : ℝ => sqLine ℓ₀ a ε {x, y}) := by unfold sqLine; fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa [sqLine] using pow_pos (hpos x y hxy hx hy) 2))
  filter_upwards [hev p q hpq (by simp) (by simp), hev p r hpr (by simp) (by simp),
    hev q r hqr (by simp) (by simp), hev p s hps (by simp) (by simp),
    hev q s hqs (by simp) (by simp), hev r s hrs (by simp) (by simp)] with ε h1 h2 h3 h4 h5 h6
  have hne : lenLine ℓ₀ a ε {p, q} ≠ 0 := (Real.sqrt_pos.2 h1).ne'
  rw [dihedralAt_eq _ hpq hpr hps hqr hqs hrs hne]
  exact dihedral_sqrt_eq h1 h2.le h3.le h4.le h5.le h6.le

end Lightlike.Regge.Linear3
