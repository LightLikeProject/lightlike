import Lightlike.Asymptotics.ContourIdentity

/-!
# Trust checks for the contour identity

For the regular tetrahedron with unit spins the face sums are `aᵢ = 3`, the quadrilateral sums
`bₖ = 4`, and Racah's sum has the two terms `t = 3, 4`:
`racahSum = −4! + 5! = 96`, so that `{1 1 1; 1 1 1} = 96 / 24² = 1/6`.

* **Known value.** Racah's sum of the regular tetrahedron is `96` (`racahSum_regular`), and the
  residues of Racah's kernel at `t = 3` and `t = 4` are the two Racah terms `−24` and `120`
  (`racahT_regular`, `tendsto_mul_racahKernel_regular`). The integral form
  `racahSum = −(1/π) Im ∫ f` is checked numerically on three paths and four spin sets, with
  maximal relative error `8 · 10⁻²⁸` (`scripts/asymptotics/contour_identity_check.py`).
* **Wrong input fails.** For the single pole `1/z` with residue `1`, the logarithmic primitive
  `log(−i z)` gives `Im (Φ(1/2) − Φ(−1/2)) = −π`, but `0` when both end points lie right of the
  pole (`im_log_pole_wrong`). So the hypothesis `x₁ < n < x₂` for every pole `n ∈ M` is needed;
  the script shows the same for Racah's kernel when `x₁` is put between two poles.
* **Non-vacuity.** `racahSum_eq_im_primitive` applies to the regular tetrahedron with `x₁ = 0`
  and `x₂ = 5` and gives `−Im (Φ(5) − Φ(0)) / π = 96` (`im_primitive_regular`); its proof
  applies `exists_primitive_im_sub`, so the hypotheses of that lemma can all be met.
* **Junk values.** Lean's `x / 0 = 0` makes `racahKernel a b n = 0` at every integer `n`
  (`racahKernel_intCast`), where the true kernel has a pole; this is why the derivative statement
  excludes the integers and the residues are limits over punctured neighbourhoods. Mathlib's
  `Γ(−n) = 0` gives `(Γ(−n))⁻¹ = 0`, which is the true value of the entire function `1/Γ`
  (`inv_Gamma_intCast_add_one` matches it with `invFact`). `Complex.log 0 = 0` is never used: the
  end points `x₁, x₂` lie outside `M`, so `−i (xⱼ − m) ≠ 0` for every `m ∈ M`.
-/

open Complex Set Filter Topology Finset PhyslibAlpha.Sl2
open scoped Real

namespace Lightlike.Asymptotics

/-- The face sums of the regular unit tetrahedron are `3`. -/
lemma faceN_regular (i : Fin 4) : faceN (fun _ => 1) i = 3 := by
  fin_cases i <;> rfl

/-- The quadrilateral sums of the regular unit tetrahedron are `4`. -/
lemma quadN_regular (k : Fin 3) : quadN (fun _ => 1) k = 4 := by
  fin_cases k <;> rfl

/-- **Known value**: Racah's sum of the regular unit tetrahedron is `−4! + 5! = 96`. -/
theorem racahSum_regular : racahSum (fun _ => 1) = 96 := by
  rw [racahSum]
  simp only [faceN_regular, quadN_regular, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.prod_univ_four, Fin.prod_univ_three]
  norm_num [invFact, Nat.factorial]

/-- **Known value**: the entire factor of Racah's kernel at `t = 3` and `t = 4` is Racah's term
without its sign, `4! = 24` and `5! = 120`, for the regular unit tetrahedron. -/
theorem racahT_regular :
    racahT (faceN fun _ => 1) (quadN fun _ => 1) (3 : ℕ) = 24 ∧
      racahT (faceN fun _ => 1) (quadN fun _ => 1) (4 : ℕ) = 120 := by
  simp only [racahT_natCast, faceN_regular, quadN_regular, Fin.prod_univ_four,
    Fin.prod_univ_three]
  norm_num [invFact, Nat.factorial]

/-- **Known value**: the residue of Racah's kernel of the regular unit tetrahedron at `t = 3` is
Racah's term `−4! = −24`. -/
theorem tendsto_mul_racahKernel_regular :
    Tendsto (fun z => (z - (3 : ℤ)) * racahKernel (faceN fun _ => 1) (quadN fun _ => 1) z)
      (𝓝[≠] ((3 : ℤ) : ℂ)) (𝓝 (-24)) := by
  have h := tendsto_mul_racahKernel (faceN fun _ => 1) (quadN fun _ => 1) 3
  have e : ((3 : ℤ) : ℂ) = ((3 : ℕ) : ℂ) := by norm_num
  rw [e, racahT_regular.1] at h
  rw [e]
  convert h using 2
  norm_num

/-- **Wrong input fails**: for the single pole `1/z` with residue `1`, the logarithmic primitive
gives `Im (Φ(1/2) − Φ(−1/2)) = −π` when the pole lies between the end points, but `0` when both
end points `1` and `2` lie right of it. -/
theorem im_log_pole_wrong :
    (Complex.log (-I * (((1 / 2 : ℝ) : ℂ) - ((0 : ℤ) : ℂ))) -
        Complex.log (-I * (((-1 / 2 : ℝ) : ℂ) - ((0 : ℤ) : ℂ)))).im = -π ∧
      (Complex.log (-I * (((2 : ℝ) : ℂ) - ((0 : ℤ) : ℂ))) -
        Complex.log (-I * (((1 : ℝ) : ℂ) - ((0 : ℤ) : ℂ)))).im = 0 := by
  rw [sub_im, sub_im, im_log_neg_I_mul_of_gt (n := 0) (x := 1 / 2) (by norm_num),
    im_log_neg_I_mul_of_lt (n := 0) (x := -1 / 2) (by norm_num),
    im_log_neg_I_mul_of_gt (n := 0) (x := 2) (by norm_num),
    im_log_neg_I_mul_of_gt (n := 0) (x := 1) (by norm_num)]
  constructor <;> ring

/-- **Non-vacuity** of `racahSum_eq_im_primitive`: for the regular unit tetrahedron, with end
points `0 < 3` and `5 > 4`, Racah's kernel has a primitive `Φ`, continuous at `0` and `5`, with
`−Im (Φ(5) − Φ(0)) / π = 96`. -/
theorem im_primitive_regular : ∃ Φ : ℂ → ℂ, (∀ z : ℂ, 0 ≤ z.im → (∀ n : ℤ, z ≠ n) →
      HasDerivAt Φ (racahKernel (faceN fun _ => 1) (quadN fun _ => 1) z) z) ∧
    ContinuousAt Φ ((0 : ℝ) : ℂ) ∧ ContinuousAt Φ ((5 : ℝ) : ℂ) ∧
      -(Φ ((5 : ℝ) : ℂ) - Φ ((0 : ℝ) : ℂ)).im / π = 96 := by
  obtain ⟨Φ, hd, h0, h5, h⟩ := racahSum_eq_im_primitive (fun _ => 1) (x₁ := 0) (x₂ := 5)
    ⟨0, by rw [faceN_regular]; norm_num⟩ ⟨0, by rw [quadN_regular]; norm_num⟩
  exact ⟨Φ, hd, h0, h5, h ▸ racahSum_regular⟩

/-- **Junk value**: Lean's `x / 0 = 0` makes Racah's kernel vanish at every integer, where the
true kernel has a pole. The contour identity therefore uses the kernel only off the integers. -/
theorem racahKernel_intCast (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (n : ℤ) :
    racahKernel a b n = 0 := by
  rw [racahKernel, sin_pi_mul_intCast, div_zero]

end Lightlike.Asymptotics
