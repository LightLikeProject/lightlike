import Lightlike.Asymptotics.Contour
import Lightlike.Asymptotics.Lift

/-!
# Descent paths of the continued phase

This is the descent step of the steepest-descent proof of `RacahSumAsymptotics`. Write
`ψ = phaseC A B` for the continued phase of a Euclidean tetrahedron (`Contour.lean`), with face
sums `A`, quadrilateral sums `B` and saddle point `s = saddle l`.

The **descent field** `v = −1/ψ'` (`descentField`) is `C¹` on the **descent domain**
`H ∖ {s}` (`descentDomain`, `IsEuclid.contDiffAt_descentField`), with `H` the open upper
half-plane. Along a solution of `z' = v z`, `ψ (z t) = ψ (z 0) − t` (`IsEuclid.phaseC_lift`):
`Re ψ` falls at unit rate and `Im ψ` stays constant.

**Main result** (`IsEuclid.exists_descent`). From every `z₀ ∈ H` with
`Re ψ z₀ < Re ψ s`, the descent path exists up to a time `T > 0` and lands at a **real** point
`x`, with `ψ x = ψ z₀ − T`. In particular `bdry A B x = Im ψ z₀`: the landing point is one of
the points of the real axis where the explicit piecewise-linear function `bdry` takes the level
`Im ψ z₀`.

The proof applies the escape lemma `exists_isLift_tendsto_not_mem` (`Lift.lean`) and needs three
a-priori bounds, all of which hold for every lift with no continuity argument, because
`ψ (z t) = ψ z₀ − t` holds pointwise:

* the path stays bounded (`exists_norm_le_of_phaseC`, from the behaviour of `ψ` at infinity,
  `norm_phaseC_add_le`);
* it stays away from the saddle, since `Re ψ < Re ψ s` along it (`exists_le_norm_sub_of_re_lt`);
* so its speed is bounded (`IsEuclid.exists_norm_descentField_le`, from the lower bound on `ψ'`,
  `IsEuclid.norm_dphaseC_ge`), and its lifetime is bounded because `Re ψ` is bounded below on
  compact sets (`exists_le_re_phaseC`).

The landing point is not in `H ∖ {s}` (escape lemma), is not `s` (it stays away from it), and
lies in the closed upper half-plane, so it is real.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace Lightlike.Asymptotics

/-- The descent field `v = −1/ψ'` of the continued phase `ψ = phaseC A B`. Along `z' = v z`,
`ψ` decreases at unit speed. At a zero of `ψ'` (the saddle) its value is Lean's junk `0`; the
descent domain excludes that point. -/
noncomputable def descentField (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (z : ℂ) : ℂ :=
  -(dphaseC A B z)⁻¹

/-- The domain of the descent flow: the open upper half-plane without the saddle point. -/
def descentDomain (l : Fin 6 → ℝ) : Set ℂ := {z | 0 < z.im ∧ z ≠ saddle l}

/-- The open upper half-plane is open. -/
lemma isOpen_upperHalf : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im

/-- The descent domain is open. -/
lemma isOpen_descentDomain (l : Fin 6 → ℝ) : IsOpen (descentDomain l) :=
  isOpen_upperHalf.inter isOpen_ne

/-- `ψ'` is holomorphic on the open upper half-plane. -/
lemma differentiableOn_dphaseC (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) :
    DifferentiableOn ℂ (dphaseC A B) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz : 0 < z.im := hz
  have hl : ∀ c : ℝ, DifferentiableAt ℂ (fun w : ℂ => log (w - c)) z := fun c =>
    (differentiableAt_fun_id.sub_const (c : ℂ)).clog (mem_slitPlane_sub hz c)
  have h0 : DifferentiableAt ℂ (fun w : ℂ => log w) z :=
    differentiableAt_fun_id.clog (mem_slitPlane_of_im_pos hz)
  have : dphaseC A B = fun w => log w - ∑ i, log (w - A i) + ∑ k, log (w - B k) - 2 * π * I :=
    rfl
  rw [this]
  exact (((h0.sub (DifferentiableAt.fun_sum (u := Finset.univ) fun i _ => hl (A i))).add
    (DifferentiableAt.fun_sum (u := Finset.univ) fun k _ => hl (B k))).sub_const _)
    |>.differentiableWithinAt

/-- For `z` in the open upper half-plane, `∏ᵢ (z − Aᵢ) ≠ 0`. -/
lemma prod_sub_ne_zero {z : ℂ} (hz : 0 < z.im) (A : Fin 4 → ℝ) : ∏ i, (z - A i) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ h0 => by
    have := congrArg im h0
    simp only [sub_im, ofReal_im, sub_zero, zero_im] at this
    linarith

/-- `ψ'` has no zero on the descent domain. -/
theorem IsEuclid.dphaseC_ne_zero {l : Fin 6 → ℝ} (h : IsEuclid l) {z : ℂ}
    (hz : z ∈ descentDomain l) : dphaseC (faceSum l) (quadSum l) z ≠ 0 := by
  have hP := norm_pos_iff.2 (prod_sub_ne_zero hz.1 (faceSum l))
  have hn : 0 < ‖z - saddle l‖ := norm_pos_iff.2 (sub_ne_zero.2 hz.2)
  have hpos : 0 < min 1 (qa l * ‖z - saddle l‖ * (saddle l).im /
      (2 * ‖∏ i, (z - faceSum l i)‖)) :=
    lt_min one_pos (div_pos (mul_pos (mul_pos h.qa_pos hn) h.saddle_im_pos) (mul_pos two_pos hP))
  exact norm_pos_iff.1 (hpos.trans_le (h.norm_dphaseC_ge hz.1))

/-- The descent field is `C¹` (as a map of the real plane) on the descent domain. -/
theorem IsEuclid.contDiffAt_descentField {l : Fin 6 → ℝ} (h : IsEuclid l) {z : ℂ}
    (hz : z ∈ descentDomain l) : ContDiffAt ℝ 1 (descentField (faceSum l) (quadSum l)) z := by
  have hc : ContDiffAt ℂ 1 (dphaseC (faceSum l) (quadSum l)) z :=
    ((differentiableOn_dphaseC _ _).contDiffOn isOpen_upperHalf).contDiffAt
      (isOpen_upperHalf.mem_nhds hz.1)
  exact ((hc.inv (h.dphaseC_ne_zero hz)).neg).restrict_scalars ℝ

/-- **`ψ` along a descent path.** Along a lift of the descent field from `z₀`,
`ψ (α t) = ψ z₀ − t`. -/
theorem IsEuclid.phaseC_lift {l : Fin 6 → ℝ} (h : IsEuclid l) {z₀ : ℂ} {T : ℝ} {α : ℝ → ℂ}
    (hα : IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) z₀ T α) :
    ∀ t ∈ Ico 0 T,
      phaseC (faceSum l) (quadSum l) (α t) = phaseC (faceSum l) (quadSum l) z₀ - t := by
  set F : ℝ → ℂ := fun t => phaseC (faceSum l) (quadSum l) (α t) + t
  have hF : ∀ t ∈ Ico 0 T, HasDerivWithinAt F 0 (Ico 0 T) t := by
    intro t ht
    have h1 := (hasDerivAt_phaseC (faceSum l) (quadSum l) (hα.mem t ht).1).comp_hasDerivWithinAt t
      (hα.deriv t ht)
    have h2 := h1.add ((hasDerivAt_id t).ofReal_comp.hasDerivWithinAt (s := Ico 0 T))
    convert h2 using 1
    · funext τ; rfl
    · simp [descentField, h.dphaseC_ne_zero (hα.mem t ht)]
  intro t ht
  have hsub : Icc 0 t ⊆ Ico 0 T := fun τ hτ => ⟨hτ.1, hτ.2.trans_lt ht.2⟩
  have hc := constant_of_has_deriv_right_zero (f := F) (a := 0) (b := t)
    (fun τ hτ => (hF τ (hsub hτ)).continuousWithinAt.mono hsub)
    (fun τ hτ => (hF τ (hsub (Ico_subset_Icc_self hτ))).mono_of_mem_nhdsWithin
      (Ico_mem_nhdsGE_of_mem' (hsub (Ico_subset_Icc_self hτ)))) t ⟨ht.1, le_rfl⟩
  simp only [F, hα.start, ofReal_zero, add_zero] at hc
  linear_combination hc

/-- **The phase from its derivative.** The coefficients of `log` in `ψ` and `z ψ'` cancel, so
`ψ z − z ψ' z = Σᵢ Aᵢ log (z − Aᵢ) − Σₖ Bₖ log (z − Bₖ) + iπ Σₖ Bₖ` for every `z`. -/
lemma phaseC_sub_mul_dphaseC (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (z : ℂ) :
    phaseC A B z - z * dphaseC A B z = ∑ i, (A i : ℂ) * log (z - A i) -
      ∑ k, (B k : ℂ) * log (z - B k) + π * I * ∑ k, (B k : ℂ) := by
  have : dphaseC A B z = log z - ∑ i, log (z - A i) + ∑ k, log (z - B k) - 2 * π * I := rfl
  rw [this]
  simp only [phaseC, xlog, Fin.sum_univ_four, Fin.sum_univ_three]
  ring

/-- **The saddle value.** At the saddle `ψ' = 0`, so
`Re ψ s = Σᵢ Aᵢ log |s − Aᵢ| − Σₖ Bₖ log |s − Bₖ|`. This is the level `D` below which the descent
paths run. -/
theorem IsEuclid.re_phaseC_saddle {l : Fin 6 → ℝ} (h : IsEuclid l) :
    (phaseC (faceSum l) (quadSum l) (saddle l)).re =
      ∑ i, faceSum l i * Real.log ‖saddle l - faceSum l i‖ -
        ∑ k, quadSum l k * Real.log ‖saddle l - quadSum l k‖ := by
  have := phaseC_sub_mul_dphaseC (faceSum l) (quadSum l) (saddle l)
  rw [h.dphaseC_saddle, mul_zero, sub_zero] at this
  rw [this]
  simp [re_sum, im_sum, mul_re, log_re]

/-- **Boundedness.** For balanced weights, the set of points of the open upper half-plane where
`Re ψ ≤ c₁` and `|Im ψ| ≤ c₂` is bounded. -/
theorem exists_norm_le_of_phaseC {A : Fin 4 → ℝ} {B : Fin 3 → ℝ} (hbal : ∑ i, A i = ∑ k, B k)
    (c₁ c₂ : ℝ) : ∃ R, ∀ z : ℂ, 0 < z.im → (phaseC A B z).re ≤ c₁ →
      |(phaseC A B z).im| ≤ c₂ → ‖z‖ ≤ R := by
  set R₀ := 2 * (∑ i, |A i| + ∑ k, |B k|) + 1
  set C := 2 * (∑ i, A i ^ 2 + ∑ k, B k ^ 2)
  set Sb := ∑ k, B k
  refine ⟨max R₀ ((c₁ + C) / (2 * π) + (c₂ + π * |Sb| + C) / (2 * π)), fun z hz h1 h2 => ?_⟩
  by_cases hzR : ‖z‖ ≤ R₀
  · exact hzR.trans (le_max_left _ _)
  have hzR := (not_le.1 hzR).le
  have hsA := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (A i)
  have hsB := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => abs_nonneg (B k)
  have hA : ∀ i, 2 * |A i| ≤ ‖z‖ := fun i => by
    have := Finset.single_le_sum (fun j _ => abs_nonneg (A j)) (Finset.mem_univ i)
    linarith
  have hB : ∀ k, 2 * |B k| ≤ ‖z‖ := fun k => by
    have := Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_univ k)
    linarith
  have hC : 0 ≤ C := by positivity
  set E := phaseC A B z + 2 * π * I * z - π * I * ∑ k, (B k : ℂ) with hEdef
  have hE : ‖E‖ ≤ C := (norm_phaseC_add_le hbal hz hA hB).trans (div_le_self hC (by linarith))
  have hre := (abs_re_le_norm E).trans hE
  have him := (abs_im_le_norm E).trans hE
  have hEre : E.re = (phaseC A B z).re - 2 * π * z.im := by
    simp [hEdef, mul_re, mul_im, re_sum, im_sum]; ring
  have hEim : E.im = (phaseC A B z).im + 2 * π * z.re - π * Sb := by
    simp [hEdef, Sb, mul_re, mul_im, re_sum, im_sum]
  rw [hEre] at hre
  rw [hEim] at him
  have hpi := Real.pi_pos
  have hSb : π * Sb ≤ π * |Sb| := mul_le_mul_of_nonneg_left (le_abs_self _) hpi.le
  have hSb' : -(π * |Sb|) ≤ π * Sb := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le _) hpi.le
  obtain ⟨hre1, -⟩ := abs_le.1 hre
  obtain ⟨him1, him2⟩ := abs_le.1 him
  obtain ⟨h21, h22⟩ := abs_le.1 h2
  have hzim : |z.im| ≤ (c₁ + C) / (2 * π) := by
    rw [abs_of_pos hz, le_div_iff₀ (by positivity)]; linarith
  have hzre : |z.re| ≤ (c₂ + π * |Sb| + C) / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    rcases abs_cases z.re with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;> nlinarith
  calc ‖z‖ ≤ |z.re| + |z.im| := norm_le_abs_re_add_abs_im z
    _ ≤ _ := by linarith
    _ ≤ _ := le_max_right _ _

/-- **Away from the saddle.** If `Re ψ s > c` at a point `s` of the open upper half-plane, the
points where `Re ψ ≤ c` keep a positive distance from `s`. -/
theorem exists_le_norm_sub_of_re_lt {A : Fin 4 → ℝ} {B : Fin 3 → ℝ} {s : ℂ} (hs : 0 < s.im)
    {c : ℝ} (hc : c < (phaseC A B s).re) :
    ∃ ρ > 0, ∀ z, (phaseC A B z).re ≤ c → ρ ≤ ‖z - s‖ := by
  have hcont : ContinuousAt (fun z => (phaseC A B z).re) s :=
    continuous_re.continuousAt.comp (hasDerivAt_phaseC A B hs).continuousAt
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds (Ioi_mem_nhds hc))
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  by_contra hlt
  have hzb : z ∈ ball s ρ := by rw [mem_ball, dist_eq_norm]; exact not_le.1 hlt
  have : c < (phaseC A B z).re := hball hzb
  linarith

/-- **Speed bound.** On the part of the open upper half-plane with `‖z‖ ≤ R` and
`‖z − s‖ ≥ ρ > 0`, the descent field is bounded. -/
theorem IsEuclid.exists_norm_descentField_le {l : Fin 6 → ℝ} (h : IsEuclid l) (R : ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ M, ∀ z : ℂ, 0 < z.im → ‖z‖ ≤ R → ρ ≤ ‖z - saddle l‖ →
      ‖descentField (faceSum l) (quadSum l) z‖ ≤ M := by
  set P := ∏ i, (|R| + |faceSum l i|) + 1
  have hP : 0 < P := by
    have : 0 ≤ ∏ i, (|R| + |faceSum l i|) := Finset.prod_nonneg fun i _ => by positivity
    linarith
  have hpos : 0 < min 1 (qa l * ρ * (saddle l).im / (2 * P)) :=
    lt_min one_pos (div_pos (mul_pos (mul_pos h.qa_pos hρ) h.saddle_im_pos) (mul_pos two_pos hP))
  refine ⟨(min 1 (qa l * ρ * (saddle l).im / (2 * P)))⁻¹, fun z hz hzR hzs => ?_⟩
  have hPz : ‖∏ i, (z - faceSum l i)‖ ≤ P := by
    calc ‖∏ i, (z - faceSum l i)‖ ≤ ∏ i, ‖z - faceSum l i‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ i, (|R| + |faceSum l i|) := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
          fun i _ => (norm_sub_le _ _).trans (by
            rw [Complex.norm_real, Real.norm_eq_abs]; linarith [le_abs_self R])
      _ ≤ P := le_add_of_nonneg_right zero_le_one
  have hPz0 := norm_pos_iff.2 (prod_sub_ne_zero hz (faceSum l))
  have hmono : min 1 (qa l * ρ * (saddle l).im / (2 * P)) ≤
      min 1 (qa l * ‖z - saddle l‖ * (saddle l).im / (2 * ‖∏ i, (z - faceSum l i)‖)) :=
    min_le_min_left _ (div_le_div₀
      (mul_nonneg (mul_nonneg h.qa_pos.le (norm_nonneg _)) h.saddle_im_pos.le)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzs h.qa_pos.le)
        h.saddle_im_pos.le)
      (mul_pos two_pos hPz0) (mul_le_mul_of_nonneg_left hPz two_pos.le))
  rw [descentField, norm_neg, norm_inv]
  exact inv_anti₀ hpos (hmono.trans (h.norm_dphaseC_ge hz))

/-- **`Re ψ` is bounded below on bounded parts of the closed upper half-plane.** -/
theorem exists_le_re_phaseC (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (R : ℝ) :
    ∃ m, ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ R → m ≤ (phaseC A B z).re := by
  have hK : IsCompact (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) :=
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_im)
  obtain ⟨m, hm⟩ := hK.bddBelow_image
    ((continuous_re.comp_continuousOn (continuousOn_phaseC A B)).mono inter_subset_right)
  exact ⟨m, fun z hz hzR => hm (mem_image_of_mem _ ⟨mem_closedBall_zero_iff.2 hzR, hz⟩)⟩

/-- **Descent paths land on the real axis.** Let `l` be a Euclidean tetrahedron and
`z₀` a point of the open upper half-plane with `Re ψ z₀ < Re ψ s`, where `ψ` is the continued
phase and `s` the saddle point. Then the descent path from `z₀` (a lift of `z' = −1/ψ'(z)` in
the upper half-plane minus `s`) exists on some `[0, T)` and converges, as `t → T⁻`, to a real
point `x` with `ψ x = ψ z₀ − T`. So `bdry A B x = Im ψ z₀` and `Re ψ x < Re ψ z₀`. -/
theorem IsEuclid.exists_descent {l : Fin 6 → ℝ} (h : IsEuclid l) {z₀ : ℂ} (hz₀ : 0 < z₀.im)
    (hD : (phaseC (faceSum l) (quadSum l) z₀).re <
      (phaseC (faceSum l) (quadSum l) (saddle l)).re) :
    ∃ T α, ∃ x : ℝ,
      IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) z₀ T α ∧
      Tendsto α (𝓝[<] T) (𝓝 (x : ℂ)) ∧
      phaseC (faceSum l) (quadSum l) x = phaseC (faceSum l) (quadSum l) z₀ - T ∧
      bdry (faceSum l) (quadSum l) x = (phaseC (faceSum l) (quadSum l) z₀).im ∧
      (phaseC (faceSum l) (quadSum l) x).re < (phaseC (faceSum l) (quadSum l) z₀).re := by
  have hz₀U : z₀ ∈ descentDomain l := ⟨hz₀, fun he => by rw [he] at hD; exact lt_irrefl _ hD⟩
  set c₁ := (phaseC (faceSum l) (quadSum l) z₀).re
  obtain ⟨R, hR⟩ := exists_norm_le_of_phaseC (sum_faceSum_eq_sum_quadSum l) c₁
    |(phaseC (faceSum l) (quadSum l) z₀).im|
  obtain ⟨ρ, hρ, hρs⟩ := exists_le_norm_sub_of_re_lt h.saddle_im_pos hD
  obtain ⟨M, hM⟩ := h.exists_norm_descentField_le R hρ
  obtain ⟨m, hm⟩ := exists_le_re_phaseC (faceSum l) (quadSum l) R
  -- A-priori bounds along every lift from `z₀`.
  have hb : ∀ T α, IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) z₀ T α →
      ∀ t ∈ Ico 0 T, ‖α t‖ ≤ R ∧ ρ ≤ ‖α t - saddle l‖ ∧
        (phaseC (faceSum l) (quadSum l) (α t)).re = c₁ - t := by
    intro T α hα t ht
    have he := h.phaseC_lift hα t ht
    have hre : (phaseC (faceSum l) (quadSum l) (α t)).re = c₁ - t := by rw [he]; simp [c₁]
    have him : (phaseC (faceSum l) (quadSum l) (α t)).im =
        (phaseC (faceSum l) (quadSum l) z₀).im := by rw [he]; simp
    exact ⟨hR _ (hα.mem t ht).1 (by linarith [ht.1]) (by rw [him]),
      hρs _ (by linarith [ht.1]), hre⟩
  have hT : ∀ T α, IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) z₀ T α →
      T ≤ c₁ - m := by
    intro T α hα
    by_contra hlt
    have hlt := not_le.1 hlt
    have ht : (max 0 (c₁ - m) + T) / 2 ∈ Ico 0 T :=
      ⟨by linarith [le_max_left 0 (c₁ - m), hα.pos], by linarith [max_lt hα.pos hlt]⟩
    obtain ⟨hn, -, hre⟩ := hb T α hα _ ht
    have := hm _ (hα.mem _ ht).1.le hn
    linarith [le_max_right 0 (c₁ - m), max_lt hα.pos hlt]
  have hMb : ∀ T α, IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) z₀ T α →
      ∀ t ∈ Ico 0 T, ‖descentField (faceSum l) (quadSum l) (α t)‖ ≤ M := fun T α hα t ht =>
    hM _ (hα.mem t ht).1 (hb T α hα t ht).1 (hb T α hα t ht).2.1
  obtain ⟨T, α, p, hα, hp, hpU⟩ := exists_isLift_tendsto_not_mem (isOpen_descentDomain l)
    (fun z hz => h.contDiffAt_descentField hz) hz₀U hT hMb
  -- Where the lift lands.
  have hev : ∀ᶠ t in 𝓝[<] T, t ∈ Ico 0 T :=
    mem_of_superset (Ioo_mem_nhdsLT hα.pos) Ioo_subset_Ico_self
  have him0 : 0 ≤ p.im := (isClosed_le continuous_const continuous_im).mem_of_tendsto hp
    (hev.mono fun t ht => (hα.mem t ht).1.le)
  have hps : ρ ≤ ‖p - saddle l‖ :=
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).mem_of_tendsto hp
      (hev.mono fun t ht => (hb T α hα t ht).2.1)
  have him : p.im = 0 := by
    by_contra hne
    refine hpU ⟨lt_of_le_of_ne him0 (Ne.symm hne), fun he => ?_⟩
    rw [he, sub_self, norm_zero] at hps
    linarith
  have hpx : p = (p.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have h1 : Tendsto (fun t => phaseC (faceSum l) (quadSum l) (α t)) (𝓝[<] T)
      (𝓝 (phaseC (faceSum l) (quadSum l) p)) :=
    ((continuousOn_phaseC (faceSum l) (quadSum l)) p him0).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hp, hev.mono fun t ht => (hα.mem t ht).1.le⟩)
  have h2 : Tendsto (fun t => phaseC (faceSum l) (quadSum l) (α t)) (𝓝[<] T)
      (𝓝 (phaseC (faceSum l) (quadSum l) z₀ - T)) := by
    have : Tendsto (fun t : ℝ => phaseC (faceSum l) (quadSum l) z₀ - t) (𝓝[<] T)
        (𝓝 (phaseC (faceSum l) (quadSum l) z₀ - T)) :=
      ((continuous_const.sub continuous_ofReal).tendsto T).mono_left nhdsWithin_le_nhds
    exact this.congr' (hev.mono fun t ht => (h.phaseC_lift hα t ht).symm)
  have hψp := tendsto_nhds_unique h1 h2
  rw [hpx] at hψp hp
  refine ⟨T, α, p.re, hα, hp, hψp, ?_, ?_⟩
  · rw [← im_phaseC_ofReal, hψp]; simp
  · rw [hψp, sub_re, ofReal_re]; exact sub_lt_self _ hα.pos

end Lightlike.Asymptotics
