import Lightlike.Regge.CMS4.JetCore4

/-!
# The class angle sum at scale `ε`, in dimension four

For one jet, the dihedral angles of the star of a triangle class at scale `ε` add up to
`2π + ε² c₂` up to `M ε³`, where `c₂` is the class sum of the second-order coefficients. It is the
dimension-4 counterpart of `Conv3.JetStarCore.class_expansion`.

## Main results

* `dihS_smul`, `incAng4_smul`: the dihedral angle is invariant under `s ↦ t • s`, `t > 0`.
* `class_sum_expansion4`: the class sum for abstract incidence data.
* `JetStarCore4.class_expansion`: the class sum of the star at scale `ε` under `JetStarCore4`.
-/

open Lightlike Real

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3

variable {V : Type*}

private lemma det3_smul (t a b c d e f g h i : ℝ) :
    det3 (t * a) (t * b) (t * c) (t * d) (t * e) (t * f) (t * g) (t * h) (t * i)
      = t ^ 3 * det3 a b c d e f g h i := by
  unfold det3; ring

/-- The dihedral angle from squared lengths is invariant under scaling the squared lengths by a
positive number. -/
theorem dihS_smul {t : ℝ} (ht : 0 < t) (s : V → V → ℝ) (p q r a u : V) :
    dihS (t • s) p q r a u = dihS s p q r a u := by
  have hip : ∀ o x y, ipS (t • s) o x y = t * ipS s o x y := fun o x y => by
    simp only [ipS, Pi.smul_apply, smul_eq_mul]; ring
  have hg : gram3S (t • s) p q r a = t ^ 3 * gram3S s p q r a := by
    simp only [gram3S, hip, det3_smul]
  have hg' : gram3S (t • s) p q r u = t ^ 3 * gram3S s p q r u := by
    simp only [gram3S, hip, det3_smul]
  have hm : mixedS (t • s) p q r a u = t ^ 3 * mixedS s p q r a u := by
    simp only [mixedS, hip, det3_smul]
  unfold dihS cosS
  rw [hm, hg, hg']
  have h3 : 0 < t ^ 3 := pow_pos ht 3
  have : √(t ^ 3 * gram3S s p q r a * (t ^ 3 * gram3S s p q r u))
      = t ^ 3 * √(gram3S s p q r a * gram3S s p q r u) := by
    rw [show t ^ 3 * gram3S s p q r a * (t ^ 3 * gram3S s p q r u)
        = (t ^ 3) ^ 2 * (gram3S s p q r a * gram3S s p q r u) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq h3.le]
  rw [this, mul_div_mul_left _ _ h3.ne']

/-- The dihedral angle of the incidence at hinge `h` is invariant under positive scaling. -/
theorem incAng4_smul {t : ℝ} (ht : 0 < t) (h : Fin 10) (s : Fin 5 → Fin 5 → ℝ) :
    incAng4 h (t • s) = incAng4 h s := dihS_smul ht s _ _ _ _ _

/-- **The class angle sum at scale `ε`, for abstract incidence data.** If the class sum of the base
angles is `2π` and the class sum of the first-order coefficients is `0`, then the class sum of the
angles of `ε² (q + ε c + ε² ρ)` is `2π + ε² c₂` up to `M ε³`. -/
theorem class_sum_expansion4 (cl : Fin 4 → Fin 3) (q c ρ : Fin 24 → Fin 10 → Fin 5 → Fin 5 → ℝ)
    (hv : ∀ σ h, Valid4 (hP h) (hQ h) (hR h) (hS h) (hU h) (q σ h))
    (hsum : clsSum4 cl (fun σ h => incAng4 h (q σ h)) = 2 * π)
    (hfirst : clsSum4 cl (fun σ h => fderiv ℝ (incAng4 h) (q σ h) (c σ h)) = 0) :
    ∃ M r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      |clsSum4 cl (fun σ h => incAng4 h (ε ^ 2 • (q σ h + ε • c σ h + ε ^ 2 • ρ σ h))) - 2 * π
        - ε ^ 2 * clsSum4 cl (fun σ h => fderiv ℝ (incAng4 h) (q σ h) (ρ σ h)
          + (1 / 2) * fderiv ℝ (fderiv ℝ (incAng4 h)) (q σ h) (c σ h) (c σ h))| ≤ M * ε ^ 3 := by
  classical
  obtain ⟨B, hB0, hBc, hBρ⟩ : ∃ B : ℝ, 0 ≤ B ∧ (∀ σ h, ‖c σ h‖ ≤ B) ∧ (∀ σ h, ‖ρ σ h‖ ≤ B) := by
    refine ⟨∑ p : Fin 24 × Fin 10, (‖c p.1 p.2‖ + ‖ρ p.1 p.2‖),
      Finset.sum_nonneg fun p _ => by positivity, fun σ h => ?_, fun σ h => ?_⟩
    · have := Finset.single_le_sum (f := fun p : Fin 24 × Fin 10 => ‖c p.1 p.2‖ + ‖ρ p.1 p.2‖)
        (fun p _ => by positivity) (Finset.mem_univ (σ, h))
      have := norm_nonneg (ρ σ h)
      simp only at *; linarith
    · have := Finset.single_le_sum (f := fun p : Fin 24 × Fin 10 => ‖c p.1 p.2‖ + ‖ρ p.1 p.2‖)
        (fun p _ => by positivity) (Finset.mem_univ (σ, h))
      have := norm_nonneg (c σ h)
      simp only at *; linarith
  have hex : ∀ h : Fin 10, ∃ M r : ℝ, 0 < r ∧ ∀ σ : Fin 24, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      |incAng4 h (ε ^ 2 • (q σ h + ε • c σ h + ε ^ 2 • ρ σ h)) - incAng4 h (q σ h)
        - ε * fderiv ℝ (incAng4 h) (q σ h) (c σ h)
        - ε ^ 2 * (fderiv ℝ (incAng4 h) (q σ h) (ρ σ h)
          + (1 / 2) * fderiv ℝ (fderiv ℝ (incAng4 h)) (q σ h) (c σ h) (c σ h))| ≤ M * ε ^ 3 := by
    intro h
    have hK : IsCompact (Set.range (fun σ : Fin 24 => q σ h)) := (Set.finite_range _).isCompact
    obtain ⟨M, r0, hr0, hexp⟩ := dihS_curve_expansion hK (p := hP h) (q := hQ h) (r := hR h)
      (t := hS h) (u := hU h) (by rintro _ ⟨σ, rfl⟩; exact hv σ h) hB0
    refine ⟨M, r0, hr0, fun σ ε hε hεr => ?_⟩
    have e := hexp (q σ h) ⟨σ, rfl⟩ (c σ h) (ρ σ h) (hBc σ h) (hBρ σ h) ε hε hεr
    rw [incAng4_smul (pow_pos hε 2)]
    exact e
  choose M r hr hM using hex
  have hrpos : 0 < Finset.univ.inf' Finset.univ_nonempty r :=
    (Finset.lt_inf'_iff _).2 fun h _ => hr h
  refine ⟨240 * ∑ h, |M h|, Finset.univ.inf' Finset.univ_nonempty r, hrpos, fun ε hε hεr => ?_⟩
  have hinc : ∀ σ h, |incAng4 h (ε ^ 2 • (q σ h + ε • c σ h + ε ^ 2 • ρ σ h))
      - incAng4 h (q σ h) - ε * fderiv ℝ (incAng4 h) (q σ h) (c σ h)
      - ε ^ 2 * (fderiv ℝ (incAng4 h) (q σ h) (ρ σ h)
        + (1 / 2) * fderiv ℝ (fderiv ℝ (incAng4 h)) (q σ h) (c σ h) (c σ h))|
      ≤ (∑ h, |M h|) * ε ^ 3 := fun σ h => by
    refine (hM h σ ε hε (hεr.trans (Finset.inf'_le _ (Finset.mem_univ h)))).trans ?_
    refine mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (by positivity)
    exact Finset.single_le_sum (f := fun h => |M h|) (fun _ _ => abs_nonneg _) (Finset.mem_univ h)
  set A1 : Fin 24 → Fin 10 → ℝ := fun σ h => fderiv ℝ (incAng4 h) (q σ h) (c σ h) with hA1
  set A2 : Fin 24 → Fin 10 → ℝ := fun σ h => fderiv ℝ (incAng4 h) (q σ h) (ρ σ h)
    + (1 / 2) * fderiv ℝ (fderiv ℝ (incAng4 h)) (q σ h) (c σ h) (c σ h) with hA2
  set err : Fin 24 → Fin 10 → ℝ := fun σ h =>
    incAng4 h (ε ^ 2 • (q σ h + ε • c σ h + ε ^ 2 • ρ σ h)) - incAng4 h (q σ h)
      - ε * A1 σ h - ε ^ 2 * A2 σ h with herr
  have hsplit : clsSum4 cl (fun σ h => incAng4 h (ε ^ 2 • (q σ h + ε • c σ h + ε ^ 2 • ρ σ h))) =
      clsSum4 cl (fun σ h => incAng4 h (q σ h)) + ε * clsSum4 cl A1
        + ε ^ 2 * clsSum4 cl A2 + clsSum4 cl err := by
    simp only [clsSum4, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun h _ => ?_
    split_ifs
    · simp only [herr]; ring
    · simp
  have herrb : |clsSum4 cl err| ≤ 240 * (∑ h, |M h|) * ε ^ 3 := by
    unfold clsSum4
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ σ : Fin 24, |∑ h : Fin 10, (if InClass4 cl σ h then err σ h else 0)|
        ≤ ∑ σ : Fin 24, ∑ h : Fin 10, (∑ h, |M h|) * ε ^ 3 :=
          Finset.sum_le_sum fun σ _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun h _ => by
              split_ifs
              · exact hinc σ h
              · simp only [abs_zero]; positivity)
      _ = 240 * (∑ h, |M h|) * ε ^ 3 := by simp; ring
  have h2 : clsSum4 cl A1 = 0 := hfirst
  have : clsSum4 cl (fun σ h => incAng4 h (ε ^ 2 • (q σ h + ε • c σ h + ε ^ 2 • ρ σ h))) - 2 * π
      - ε ^ 2 * clsSum4 cl A2 = clsSum4 cl err := by
    rw [hsplit, hsum, h2]; ring
  rw [this]
  exact herrb

/-- **The class angle sum at scale `ε`.** Under `JetStarCore4`, for each admissible triangle class
the sum of the dihedral angles of the star at scale `ε` is `2π + ε² c₂` up to `M ε³`, where `c₂` is
the class sum of `angC24`. -/
theorem JetStarCore4.class_expansion {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {m : Fin 4 → ℝ} (H : JetStarCore4 g m) (cl : Fin 4 → Fin 3) (hcl : ClsOK cl) :
    ∃ M r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      |clsSum4 cl (fun σ h => incAng4 h (incLen4 g m ε σ h)) - 2 * π
        - ε ^ 2 * clsSum4 cl (angC24 g m)| ≤ M * ε ^ 3 := by
  obtain ⟨M, r, hr, h⟩ := class_sum_expansion4 cl (incQ4 g m) (incC4 g m) (incR4 g m)
    H.valid (H.angle_sum cl hcl) (H.first_order cl hcl)
  refine ⟨M, r, hr, fun ε hε hεr => ?_⟩
  have := h ε hε hεr
  simp only [incLen4_eq]
  exact this

end Lightlike.Regge4
