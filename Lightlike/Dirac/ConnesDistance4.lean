import Mathlib
import Lightlike.Dirac.ConnesDistance3

/-!
# Connes' distance on the circle: smooth test functions

On the circle `ℝ / Lℤ` the Dirac operator is `D = γ d/dx` and `‖[D, f]‖ = ‖f'‖_∞`. The extremal
function for the distance is the triangle wave `x ↦ dist (x, Lℤ)`, which is not `C¹`; we approximate
it by the explicit smooth `L`-periodic functions
`circFn L k x = (L / 2π) · arcsin (cos (2π x / L) / k)` (`k > 1`), whose derivative is
`-sin u / √(k² - cos² u)` (`u = 2π x / L`), of absolute value `≤ 1`, and which tend to the triangle wave
as `k ↓ 1`.

## References

Connes' distance formula (definition only); Dirac operator: `bgv-1992`.
-/

open Real

namespace Lightlike.Dirac

/-- The smooth approximation `x ↦ ω⁻¹ arcsin (cos (ω x) / k)` of the triangle wave, `ω = 2π / L`. -/
noncomputable def circFn (ω k : ℝ) (x : ℝ) : ℝ := ω⁻¹ * arcsin (cos (ω * x) / k)

lemma circFn_periodic {ω : ℝ} (hω : ω ≠ 0) (k : ℝ) : Function.Periodic (circFn ω k) (2 * π / ω) := by
  intro x
  unfold circFn
  have : ω * (x + 2 * π / ω) = ω * x + 2 * π := by field_simp
  rw [this, cos_add_two_pi]

lemma cos_div_ne_one {k : ℝ} (hk : 1 < k) (t : ℝ) : cos t / k ≠ 1 := by
  intro h
  have hk0 : 0 < k := by linarith
  have : cos t = k := by field_simp at h; linarith
  have := cos_le_one t
  linarith

lemma cos_div_ne_neg_one {k : ℝ} (hk : 1 < k) (t : ℝ) : cos t / k ≠ -1 := by
  intro h
  have hk0 : 0 < k := by linarith
  have : cos t = -k := by field_simp at h; linarith
  have := neg_one_le_cos t
  linarith

lemma hasDerivAt_circFn {ω k : ℝ} (hk : 1 < k) (x : ℝ) :
    HasDerivAt (circFn ω k)
      (ω⁻¹ * (1 / √(1 - (cos (ω * x) / k) ^ 2) * (-sin (ω * x) * ω / k))) x := by
  have h1 : HasDerivAt (fun x : ℝ => cos (ω * x) / k) (-sin (ω * x) * ω / k) x := by
    have := (((hasDerivAt_id x).const_mul ω).cos).div_const k
    simpa [id] using this
  have h2 := (hasDerivAt_arcsin (cos_div_ne_neg_one hk (ω * x)) (cos_div_ne_one hk (ω * x))).comp
    x h1
  exact h2.const_mul ω⁻¹

lemma contDiff_circFn (ω : ℝ) {k : ℝ} (hk : 1 < k) : ContDiff ℝ 1 (circFn ω k) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h1 : ContDiffAt ℝ 1 (fun x : ℝ => cos (ω * x) / k) x :=
    ((contDiff_const.mul contDiff_id).cos.div_const k).contDiffAt
  have h2 : ContDiffAt ℝ 1 arcsin ((fun x : ℝ => cos (ω * x) / k) x) :=
    contDiffAt_arcsin (cos_div_ne_neg_one hk (ω * x)) (cos_div_ne_one hk (ω * x))
  have h3 : ContDiffAt ℝ 1 (arcsin ∘ fun x : ℝ => cos (ω * x) / k) x := ContDiffAt.comp x h2 h1
  exact contDiffAt_const.mul h3

lemma abs_deriv_circFn_le {ω k : ℝ} (hω : 0 < ω) (hk : 1 < k) (x : ℝ) :
    |deriv (circFn ω k) x| ≤ 1 := by
  rw [(hasDerivAt_circFn (ω := ω) hk x).deriv]
  set s := sin (ω * x)
  set c := cos (ω * x)
  have hk0 : 0 < k := by linarith
  have hsc : s ^ 2 + c ^ 2 = 1 := sin_sq_add_cos_sq _
  have hle : |s| / k ≤ √(1 - (c / k) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_pow, sq_abs]
    have : 1 - c ^ 2 / k ^ 2 = (k ^ 2 - c ^ 2) / k ^ 2 := by field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hpos : 0 < √(1 - (c / k) ^ 2) := by
    apply Real.sqrt_pos.mpr
    have : (c / k) ^ 2 < 1 := by
      rw [div_pow]
      rw [div_lt_one (by positivity)]
      nlinarith [sq_nonneg s]
    linarith
  have heq : ω⁻¹ * (1 / √(1 - (c / k) ^ 2) * (-s * ω / k)) = -(s / k) / √(1 - (c / k) ^ 2) := by
    field_simp
  rw [heq, abs_div, abs_neg, abs_of_pos hpos, abs_div, abs_of_pos hk0]
  rw [div_le_one hpos]
  exact hle

lemma circFn_even (ω k x : ℝ) : circFn ω k (-x) = circFn ω k x := by
  simp [circFn]

/-- As `k → 1` the gap `circFn 0 - circFn d` tends to `d` for `0 ≤ ω d ≤ π`: the triangle wave. -/
lemma circFn_gap_tendsto {ω d : ℝ} (hω : 0 < ω) (h0 : 0 ≤ ω * d) (hπ : ω * d ≤ π) :
    Filter.Tendsto (fun k => circFn ω k 0 - circFn ω k d) (nhds 1) (nhds d) := by
  have hc : ContinuousAt (fun k : ℝ => ω⁻¹ * (arcsin (1 / k) - arcsin (cos (ω * d) / k))) 1 := by
    have h1 : ContinuousAt (fun k : ℝ => 1 / k) 1 :=
      continuousAt_const.div continuousAt_id one_ne_zero
    have h2 : ContinuousAt (fun k : ℝ => cos (ω * d) / k) 1 :=
      continuousAt_const.div continuousAt_id one_ne_zero
    exact continuousAt_const.mul
      ((continuous_arcsin.continuousAt.comp h1).sub (continuous_arcsin.continuousAt.comp h2))
  have hval : ω⁻¹ * (arcsin (1 / 1) - arcsin (cos (ω * d) / 1)) = d := by
    rw [div_one, div_one, arcsin_one, arcsin_eq_pi_div_two_sub_arccos, arccos_cos h0 hπ]
    field_simp
    ring
  have := hc.tendsto
  rw [hval] at this
  refine this.congr (fun k => ?_)
  simp [circFn, mul_sub]

/-- Test functions on the circle `ℝ / Lℤ`: `L`-periodic `C¹` functions with `‖[D, f]‖ = |f'| ≤ 1`
(on the circle `D = γ d/dx`, so `[D, f] = γ f'` and `‖γ‖ = 1`). -/
def LipCirc (L : ℝ) (f : ℝ → ℝ) : Prop :=
  Function.Periodic f L ∧ ContDiff ℝ 1 f ∧ ∀ x, |deriv f x| ≤ 1

/-- Connes' distance on the circle `ℝ / Lℤ`. -/
noncomputable def circConnesDist (L p q : ℝ) : ℝ :=
  sSup {r | ∃ f, LipCirc L f ∧ r = |f p - f q|}

/-- Upper bound: a test function is `1`-Lipschitz on the line, and periodic, hence moves by at most
`|p - q - m L|` for every integer `m`. -/
lemma LipCirc.abs_sub_le {L : ℝ} {f : ℝ → ℝ} (hf : LipCirc L f) (p q : ℝ) (m : ℤ) :
    |f p - f q| ≤ |p - q - m * L| := by
  have hper : f (q + m * L) = f q := by
    have := hf.1.int_mul m q
    simpa [add_comm] using this
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := f) (C := 1)
    (fun x _ => (hf.2.1.differentiable one_ne_zero).differentiableAt)
    (fun x _ => by simpa [Real.norm_eq_abs] using hf.2.2 x)
    (Set.mem_univ (q + m * L)) (Set.mem_univ p)
  rw [hper] at h
  have e : p - (q + m * L) = p - q - m * L := by ring
  simpa [Real.norm_eq_abs, e] using h

lemma lipCirc_zero (L : ℝ) : LipCirc L (fun _ => 0) :=
  ⟨fun _ => rfl, contDiff_const, fun x => by simp⟩

lemma circConnesDist_bdd {L : ℝ} (p q : ℝ) :
    BddAbove {r | ∃ f, LipCirc L f ∧ r = |f p - f q|} :=
  ⟨|p - q|, by
    rintro r ⟨f, hf, rfl⟩
    simpa using hf.abs_sub_le p q 0⟩

/-- Upper bound on the circle distance: `d(p, q) ≤ |p - q - m L|` for every integer `m`. -/
lemma circConnesDist_le {L : ℝ} (p q : ℝ) (m : ℤ) : circConnesDist L p q ≤ |p - q - m * L| :=
  csSup_le ⟨_, 0, lipCirc_zero L, rfl⟩ (by rintro r ⟨f, hf, rfl⟩; exact hf.abs_sub_le p q m)

/-- The translated smooth approximants are test functions on the circle of length `L`. -/
lemma lipCirc_circFn {L : ℝ} (hL : 0 < L) {k : ℝ} (hk : 1 < k) (q : ℝ) :
    LipCirc L (fun x => circFn (2 * π / L) k (x - q)) := by
  have hω : 0 < 2 * π / L := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have := (circFn_periodic hω.ne' k).sub_const q
    have e : 2 * π / (2 * π / L) = L := by field_simp
    rw [e] at this
    exact this
  · exact (contDiff_circFn _ hk).comp (contDiff_id.sub contDiff_const)
  · intro x
    rw [deriv_comp_sub_const]
    exact abs_deriv_circFn_le hω hk _

lemma circConnesDist_comm (L p q : ℝ) : circConnesDist L p q = circConnesDist L q p := by
  unfold circConnesDist
  congr 1
  ext r
  constructor <;> rintro ⟨f, hf, rfl⟩ <;> exact ⟨f, hf, abs_sub_comm _ _⟩

/-- Lower bound: points at distance `d ≤ L / 2` have circle distance `≥ d`. -/
lemma le_circConnesDist_aux {L : ℝ} (hL : 0 < L) (q : ℝ) {d : ℝ} (h0 : 0 ≤ d) (hd : d ≤ L / 2) :
    d ≤ circConnesDist L (q + d) q := by
  have hω : 0 < 2 * π / L := by positivity
  have h1 : 0 ≤ 2 * π / L * d := by positivity
  have h2 : 2 * π / L * d ≤ π := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    nlinarith [Real.pi_pos]
  have hT := (circFn_gap_tendsto hω h1 h2).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
  refine le_of_tendsto hT (eventually_nhdsWithin_of_forall fun k hk => ?_)
  have hk' : 1 < k := hk
  have hmem := le_csSup (circConnesDist_bdd (L := L) (q + d) q)
    ⟨_, lipCirc_circFn hL hk' q, rfl⟩
  refine le_trans ?_ hmem
  have : circFn (2 * π / L) k (q + d - q) = circFn (2 * π / L) k d := by rw [add_sub_cancel_left]
  simp only [sub_self, this]
  rw [← neg_sub]
  exact neg_le_abs _ |>.trans' (le_refl _)

/-- **Connes' distance on the circle** (short arcs): on the circle `ℝ / Lℤ` with Dirac operator
`D = γ d/dx`, two points with `|p - q| ≤ L / 2` are at spectral distance `|p - q|`. -/
theorem circConnesDist_eq {L : ℝ} (hL : 0 < L) {p q : ℝ} (h : |p - q| ≤ L / 2) :
    circConnesDist L p q = |p - q| := by
  refine le_antisymm (by simpa using circConnesDist_le (L := L) p q 0) ?_
  rcases le_total q p with hqp | hpq
  · have hp : p = q + (p - q) := by ring
    have := le_circConnesDist_aux hL q (sub_nonneg.mpr hqp)
      (by rwa [abs_of_nonneg (sub_nonneg.mpr hqp)] at h)
    rw [← hp] at this
    rwa [abs_of_nonneg (sub_nonneg.mpr hqp)]
  · rw [circConnesDist_comm, abs_sub_comm] at *
    have hq : q = p + (q - p) := by ring
    have := le_circConnesDist_aux hL p (sub_nonneg.mpr hpq)
      (by rwa [abs_of_nonneg (sub_nonneg.mpr hpq)] at h)
    rw [← hq] at this
    rwa [abs_of_nonneg (sub_nonneg.mpr hpq)]

end Lightlike.Dirac
