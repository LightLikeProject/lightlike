import Lightlike.Regge.D4.ReggeEquations
import Lightlike.Regge.D4.Embedded

/-!
# Flat space solves Regge's equations in 4D

A geometric triangulation of a region of a 4-dimensional Euclidean space (`IsGeometric4`) has
zero deficit angles at its interior triangles (`Lightlike/Regge/D4/Embedded.lean`). Here we show
that its edge lengths are non-degenerate, so that Regge's equations apply, and conclude that its
Regge action is stationary under every variation of the lengths that keeps the boundary fixed.

Positivity of the Gram determinants is obtained from the components orthogonal to a triangle
(`perp2`): `gram3 = gram2 · ‖P c‖²` and, by Desnanot–Jacobi,
`gram4 = gram2 · (‖P c‖² ‖P d‖² - ⟪P c, P d⟫²)`, both positive for linearly independent edge
vectors.

## Main results

* `gram3_pos_of_linIndep`, `gram4_pos_of_linIndep`: positive volumes and 4-volumes.
* `IsGeometric4.lengthsNondeg4`: the lengths of a geometric triangulation are non-degenerate.
* `IsGeometric4.reggeAction4_stationary`: **flat space solves Regge's equations**.
-/

open Real Finset InnerProductSpace Module

namespace Lightlike.Regge4

open Lightlike.FourD (Complex4)
open Lightlike.FourD.Complex4 (mem_faces mem_star card_of_mem_faces)
open Lightlike.Regge (ofDist ofDist_pair)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `c - perp2 a b c` is an explicit combination of `a` and `b`. -/
theorem sub_perp2_eq (a b c : E) :
    c - perp2 a b c =
      ((⟪c, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪c, b⟫_ℝ * ⟪a, b⟫_ℝ) / (⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2)) • a +
        ((⟪c, b⟫_ℝ * ⟪a, a⟫_ℝ - ⟪c, a⟫_ℝ * ⟪a, b⟫_ℝ) /
          (⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2)) • b := by
  simp only [perp2]
  abel

/-- For linearly independent `a, b, c, d`, the components of `c` and `d` orthogonal to `a, b` are
linearly independent. -/
theorem linIndep_perp2 {a b c d : E} (h : LinearIndependent ℝ ![a, b, c, d]) :
    LinearIndependent ℝ ![perp2 a b c, perp2 a b d] := by
  rw [LinearIndependent.pair_iff]
  intro α β hαβ
  set X := (⟪c, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪c, b⟫_ℝ * ⟪a, b⟫_ℝ) / (⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2)
  set Y := (⟪c, b⟫_ℝ * ⟪a, a⟫_ℝ - ⟪c, a⟫_ℝ * ⟪a, b⟫_ℝ) / (⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2)
  set X' := (⟪d, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪d, b⟫_ℝ * ⟪a, b⟫_ℝ) / (⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2)
  set Y' := (⟪d, b⟫_ℝ * ⟪a, a⟫_ℝ - ⟪d, a⟫_ℝ * ⟪a, b⟫_ℝ) / (⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2)
  have key := Fintype.linearIndependent_iff.mp h ![-(α * X + β * X'), -(α * Y + β * Y'), α, β]
    (by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      have hc : perp2 a b c = c - X • a - Y • b := rfl
      have hd : perp2 a b d = d - X' • a - Y' • b := rfl
      rw [hc, hd] at hαβ
      rw [← hαβ]
      module)
  exact ⟨by simpa using key 2, by simpa using key 3⟩

/-- For linearly independent `a, b, c`, the component of `c` orthogonal to `a, b` is nonzero. -/
theorem perp2_ne_zero {a b c : E} (h : LinearIndependent ℝ ![a, b, c]) : perp2 a b c ≠ 0 := by
  intro h0
  set X := (⟪c, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪c, b⟫_ℝ * ⟪a, b⟫_ℝ) / (⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2)
  set Y := (⟪c, b⟫_ℝ * ⟪a, a⟫_ℝ - ⟪c, a⟫_ℝ * ⟪a, b⟫_ℝ) / (⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2)
  have hc : perp2 a b c = c - X • a - Y • b := rfl
  have key := Fintype.linearIndependent_iff.mp h ![-X, -Y, 1]
    (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hc] at h0
      rw [← h0]
      module) 2
  simp at key

variable {V : Type*} [DecidableEq V]

/-- Four vertices forming a 4-element set are distinct. -/
theorem distinct_of_card_four {p q r s : V} (h : #({p, q, r, s} : Finset V) = 4) :
    p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;>
    simp only [insert_eq_of_mem, mem_insert, mem_singleton, true_or, or_true] at h <;>
    exact absurd h (ne_of_lt (lt_of_le_of_lt card_le_three (by norm_num)))

/-- Five vertices forming a 5-element set are distinct. -/
theorem distinct_of_card_five {p q r s u : V} (h : #({p, q, r, s, u} : Finset V) = 5) :
    p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ p ≠ u ∧ q ≠ r ∧ q ≠ s ∧ q ≠ u ∧ r ≠ s ∧ r ≠ u ∧ s ≠ u := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;>
    simp only [insert_eq_of_mem, mem_insert, mem_singleton, true_or, or_true] at h <;>
    exact absurd h (ne_of_lt (lt_of_le_of_lt card_le_four (by norm_num)))

section Placement

variable (x : V → E) {ℓ : Finset V → ℝ}

/-- **Positive volume.** For the lengths of a placement whose edge vectors `q - p, r - p, s - p`
are linearly independent, `gram3 > 0`. -/
theorem gram3_pos_of_linIndep (hℓ : ∀ a b, a ≠ b → ℓ {a, b} = dist (x a) (x b)) {p q r s : V}
    (h : LinearIndependent ℝ ![x q - x p, x r - x p, x s - x p]) : 0 < gram3 ℓ p q r s := by
  have h2 : LinearIndependent ℝ ![x q - x p, x r - x p] := by
    have := h.comp ![0, 1] (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    convert this using 1
    ext i
    fin_cases i <;> rfl
  have hG := gram_two_pos h2
  have hG' : gram2 ℓ p q r ≠ 0 := by rw [gram2_eq_inner x hℓ]; exact hG.ne'
  rw [gram3_eq_norm x hℓ hG', gram2_eq_inner x hℓ]
  have := norm_pos_iff.mpr (perp2_ne_zero h)
  positivity

/-- **Positive 4-volume.** For the lengths of a placement whose edge vectors
`q - p, r - p, s - p, u - p` are linearly independent, `gram4 > 0`. -/
theorem gram4_pos_of_linIndep (hℓ : ∀ a b, a ≠ b → ℓ {a, b} = dist (x a) (x b))
    {p q r s u : V} (h : LinearIndependent ℝ ![x q - x p, x r - x p, x s - x p, x u - x p]) :
    0 < gram4 ℓ p q r s u := by
  have h2 : LinearIndependent ℝ ![x q - x p, x r - x p] := by
    have := h.comp ![0, 1] (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    convert this using 1
    ext i
    fin_cases i <;> rfl
  have hG := gram_two_pos h2
  have hG' : gram2 ℓ p q r ≠ 0 := by rw [gram2_eq_inner x hℓ]; exact hG.ne'
  have hPP := gram_two_pos (linIndep_perp2 h)
  have hdj := desnanot_jacobi ℓ p q r s u
  rw [gram3_eq_norm x hℓ hG', gram3_eq_norm x hℓ hG', mixed_eq_inner x hℓ hG'] at hdj
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hPP
  have hpos : 0 < gram2 ℓ p q r := by rw [gram2_eq_inner x hℓ]; exact hG
  have : gram2 ℓ p q r * gram4 ℓ p q r s u = gram2 ℓ p q r * (gram2 ℓ p q r *
      (‖perp2 (x q - x p) (x r - x p) (x s - x p)‖ ^ 2 *
        ‖perp2 (x q - x p) (x r - x p) (x u - x p)‖ ^ 2 -
        ⟪perp2 (x q - x p) (x r - x p) (x s - x p),
          perp2 (x q - x p) (x r - x p) (x u - x p)⟫_ℝ ^ 2)) := by
    rw [← hdj]
    ring
  have h4 := mul_left_cancel₀ hpos.ne' this
  rw [h4]
  positivity

end Placement

/-- **Geometric triangulations have non-degenerate lengths**: the edge lengths of a geometric
triangulation of a region of 4-space satisfy `LengthsNondeg4`, so Regge's equations apply. -/
theorem IsGeometric4.lengthsNondeg4 {K : Complex4 V} {x : V → E} (hK : IsGeometric4 K x) :
    LengthsNondeg4 K (ofDist fun u v => dist (x u) (x v)) := by
  have hℓ : ∀ u v, u ≠ v → ofDist (fun u v => dist (x u) (x v)) {u, v} = dist (x u) (x v) :=
    fun u v h => ofDist_pair (d := fun u v => dist (x u) (x v)) (fun u => dist_self (x u))
      (fun u v => dist_comm (x u) (x v)) h
  -- every labelling of a 4-simplex has linearly independent edge vectors
  have L : ∀ {p q r s u : V}, ({p, q, r, s, u} : Finset V) ∈ K.simps → p ≠ q → p ≠ r → p ≠ s →
      p ≠ u → q ≠ r → q ≠ s → q ≠ u → r ≠ s → r ≠ u → s ≠ u →
      LinearIndependent ℝ ![x q - x p, x r - x p, x s - x p, x u - x p] :=
    fun hσ hpq hpr hps hpu hqr hqs hqu hrs hru hsu =>
      linIndep_of_affIndep5 x hpq hpr hps hpu hqr hqs hqu hrs hru hsu (hK.nondeg _ hσ)
  refine ⟨fun t ht => ?_, fun p q r s hτ => ?_, fun p q r s u hσ => ?_⟩
  · obtain ⟨σ, hσ, htσ, ht3⟩ := mem_faces.mp ht
    obtain ⟨a, b, c, y, z, hab, hac, hay, haz, hbc, hby, hbz, hcy, hcz, hyz, rfl, rfl⟩ :=
      exists_label4 (K.card_eq σ hσ) ht3 htσ
    have h4 := L hσ hab hac hay haz hbc hby hbz hcy hcz hyz
    have h2 : LinearIndependent ℝ ![x b - x a, x c - x a] := by
      have := h4.comp ![0, 1] (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
      convert this using 1
      ext i
      fin_cases i <;> rfl
    rw [triH_eq_gram2 _ hab hac hbc, gram2_eq_inner x hℓ]
    linarith [gram_two_pos h2]
  · obtain ⟨σ, hσ, hτσ, hτ4⟩ := mem_faces.mp hτ
    have hd : #(σ \ {p, q, r, s}) = 1 := by
      rw [card_sdiff_of_subset hτσ, K.card_eq σ hσ, hτ4]
    obtain ⟨y, hy⟩ := card_eq_one.mp hd
    have hyσ : y ∈ σ \ {p, q, r, s} := hy ▸ mem_singleton_self y
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hyσ
    obtain ⟨hpq, hpr, hps, hqr, hqs, hrs⟩ := distinct_of_card_four hτ4
    have hσ' : σ = {p, q, r, s, y} := by
      rw [← union_sdiff_of_subset hτσ, hy]
      ext z
      simp only [mem_union, mem_insert, mem_singleton]
      tauto
    have h4 := L (hσ' ▸ hσ) hpq hpr hps (Ne.symm hyσ.2.1) hqr hqs (Ne.symm hyσ.2.2.1) hrs
      (Ne.symm hyσ.2.2.2.1) (Ne.symm hyσ.2.2.2.2)
    have h3 : LinearIndependent ℝ ![x q - x p, x r - x p, x s - x p] := by
      have := h4.comp ![0, 1, 2] (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
      convert this using 1
      ext i
      fin_cases i <;> rfl
    exact gram3_pos_of_linIndep x hℓ h3
  · have h5 : #({p, q, r, s, u} : Finset V) = 5 := K.card_eq _ hσ
    have hd := distinct_of_card_five h5
    obtain ⟨hpq, hpr, hps, hpu, hqr, hqs, hqu, hrs, hru, hsu⟩ := hd
    exact gram4_pos_of_linIndep x hℓ (L hσ hpq hpr hps hpu hqr hqs hqu hrs hru hsu)

/-- **Flat space solves Regge's equations in 4D.** Let `K` satisfy the manifold condition at
triangles and let `x` be a geometric triangulation of a region of a 4-dimensional real inner
product space, with the induced edge lengths. Then the Regge action is stationary under every
variation of the edge lengths that keeps the boundary lengths fixed. -/
theorem IsGeometric4.reggeAction4_stationary [FiniteDimensional ℝ E] (hE : finrank ℝ E = 4)
    {K : Complex4 V} {x : V → E} (hK : IsGeometric4 K x) (hM : IsTriManifold K)
    (v : Finset V → ℝ) (hv : ∀ e ∈ bdryEdges4 K, v e = 0) :
    HasDerivAt (fun τ => reggeAction4 K (lineL (ofDist fun u v => dist (x u) (x v)) v τ)) 0 0 :=
  (reggeAction4_stationary_iff hK.lengthsNondeg4).mpr (fun _ _ => sum_eq_zero fun t ht => by
    rw [hK.deficit4_eq_zero hE hM (mem_filter.mp ht).1, mul_zero]) v hv

end Lightlike.Regge4
