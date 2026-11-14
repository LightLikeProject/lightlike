module

public import Lightlike.Lorentz.PlancherelKernel
public import Lightlike.Lorentz.SU2Average

/-!
# The trace of `π_{n,ρ}(F)` as an orbital integral

For `F` continuous with compact support on `M₂(ℂ)`, the diagonal of the integral kernel
`K_F(z, w)` of `π_{n,ρ}(F)` (`psKernel`, `PlancherelKernel.lean`) integrates to an orbital
integral of the `SU(2)` conjugation average `F♮` (`su2Avg`, `SU2Average.lean`):

    ∫ K_F(z, z) d²z = π ∫ m_{n,ρ}(λ) · orbInt F♮ (1/λ) d²λ      (`integral_psKernel_diag`),

with `orbInt Φ μ = ∫ Φ([[μ, x], [0, μ⁻¹]]) d²x` (`LimitFormula.lean`) and
`m_{n,ρ}(λ) = |λ|^{2iρ-2} (λ/|λ|)^n`. The proof has three parts.

* **(A) Stabiliser of `z`** (`chartPt_diag`, `psKernel_diag`). With `S = 1 + |z|²` and
  `A_z = [[1, -z̄], [z, 1]]`, the fibre of the chart at `z` over `(z, z)` is
  `g_z(b, z, λ) = S⁻¹ A_z* [[λ⁻¹, x], [0, λ]] A_z` with `x = S b + z̄ (λ⁻¹ - λ)`, so
  `K_F(z, z) = S⁻² ∫ m(λ) G_z(1/λ) d²λ` with `G_z(μ) = ∫ F(S⁻¹ A_z* [[μ, x], [0, μ⁻¹]] A_z) d²x`.
* **(B) Average over the sphere** (`integral_sw_stabInt`). For `v ∈ ℂ²` with `v₀ ≠ 0`,
  conjugation by `K_v` (`conjV`) is conjugation by `A_z` for `z = v₁/v̄₀` up to a phase in `x`
  (`conjV_triMat`). The push-forward of `ψ(|v|²) d⁴v` under `v ↦ v₁/v̄₀` is
  `C_ψ (1 + |z|²)⁻² d²z` (`integral_avgWeight_comp`), and `∫ ψ(|v|²) d⁴v = π C_ψ`
  (`avgNorm_eq`). Hence `∫ S⁻² G_z(μ) d²z = π · orbInt F♮(μ)`.
* **(C) Exchange of the integrals** over `z` and `λ` (`integrable_diag_stab`): `G_z(μ)` vanishes
  unless `|μ|, |μ⁻¹| ≤ 4C` for a support radius `C` of `F`, uniformly in `z` (`stab_bound`).

The weight `∫ (1 + |z|²)⁻² d²z = π` is `integral_sz_inv_sq`; complex scalings of Lebesgue
measure on `ℂ` are `integral_comp_mul_left_complex` and `integral_comp_real_mul_complex`.

## References

- I. M. Gel'fand, M. A. Naimark, *Unitary representations of the Lorentz group*, Izv. Akad. Nauk
  SSSR 11 (1947).
- M. A. Naimark, *Linear representations of the Lorentz group*, Pergamon (1964), ch. III.
- Harish-Chandra, *The Plancherel formula for complex semisimple Lie groups*, Trans. AMS 76
  (1954).
-/

@[expose] public section

open MeasureTheory Complex Metric Set Filter Topology
open scoped Matrix ComplexConjugate

local notation "M2" => Matrix (Fin 2) (Fin 2) ℂ
local notation "P2" => Fin 2 → Fin 2 → ℂ

namespace Lightlike.Lorentz

/-! ## Changes of variables in `ℂ` -/

/-- Multiplication by `c ≠ 0` scales Lebesgue measure on `ℂ` by `|c|²`: its real determinant
is `normSq c`. -/
lemma map_mul_left_complex {c : ℂ} (hc : c ≠ 0) :
    Measure.map (fun x : ℂ => c * x) volume = ENNReal.ofReal (‖c‖ ^ 2)⁻¹ • volume := by
  set L : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ c).restrictScalars ℝ
  have hdet : LinearMap.det L = ‖c‖ ^ 2 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_mulLeft, Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) (f := L)
    (by rw [hdet]; positivity)
  rw [hdet, abs_of_pos (by positivity)] at h
  have hL : (⇑L : ℂ → ℂ) = fun x => c * x := by funext x; simp [L]
  rwa [hL] at h

/-- **Complex scaling**: `∫ g(c x) d²x = |c|⁻² ∫ g` for `c ≠ 0`. -/
lemma integral_comp_mul_left_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℂ → E) {c : ℂ} (hc : c ≠ 0) :
    ∫ x : ℂ, g (c * x) = (‖c‖ ^ 2)⁻¹ • ∫ x : ℂ, g x := by
  have he := (Homeomorph.mulLeft₀ c hc).measurableEmbedding
  calc ∫ x : ℂ, g (c * x) = ∫ y, g y ∂(Measure.map (fun x : ℂ => c * x) volume) :=
        (he.integral_map g).symm
    _ = (‖c‖ ^ 2)⁻¹ • ∫ x : ℂ, g x := by
        rw [map_mul_left_complex hc, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

/-- **Real scaling** in `ℂ`: `∫ g(r x) d²x = r⁻² ∫ g` for `r > 0`. -/
lemma integral_comp_real_mul_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℂ → E) {r : ℝ} (hr : 0 < r) :
    ∫ x : ℂ, g ((r : ℂ) * x) = (r ^ 2)⁻¹ • ∫ x : ℂ, g x := by
  have h := integral_comp_mul_left_complex g (c := (r : ℂ)) (by exact_mod_cast hr.ne')
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h

/-! ## The weight `(1 + |z|²)⁻²` -/

/-- `S(z) = 1 + |z|²`. -/
noncomputable def sz (z : ℂ) : ℝ := 1 + ‖z‖ ^ 2

/-- `S(z) = 1 + |z|² > 0`. -/
lemma sz_pos (z : ℂ) : 0 < sz z := by unfold sz; positivity

/-- `S` is continuous. -/
lemma continuous_sz : Continuous sz := by unfold sz; fun_prop

/-- `(1 + |z|²)⁻²` is integrable on `ℂ`. -/
lemma integrable_sz_inv_sq : Integrable fun z : ℂ => ((sz z) ^ 2)⁻¹ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [sz]
  rw [show (-4 / 2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg]
  norm_cast

/-- `∫₀^∞ y (1 + y²)⁻² dy = 1/2`. -/
lemma integral_Ioi_mul_inv_one_add_sq_sq :
    ∫ y in Ioi (0 : ℝ), y * ((1 + y ^ 2) ^ 2)⁻¹ = 1 / 2 := by
  have hd : ∀ y ∈ Ici (0 : ℝ), HasDerivAt (fun y : ℝ => -(1 / 2) * (1 + y ^ 2)⁻¹)
      (y * ((1 + y ^ 2) ^ 2)⁻¹) y := fun y _ => by
    have h1 : (1 + y ^ 2) ≠ 0 := by positivity
    have h2 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * y) y := by
      simpa using ((hasDerivAt_id y).pow 2).const_add 1
    have := (h2.inv h1).const_mul (-(1 / 2 : ℝ))
    convert this using 1
    rw [div_eq_mul_inv]
    ring
  have ht : Tendsto (fun y : ℝ => -(1 / 2) * (1 + y ^ 2)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
    simpa using this.inv_tendsto_atTop.const_mul (-(1 / 2 : ℝ))
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun y hy => by
    have : 0 < y := hy; positivity) ht]
  norm_num

/-- **`∫ (1 + |z|²)⁻² d²z = π`** (polar coordinates). -/
theorem integral_sz_inv_sq : ∫ z : ℂ, ((sz z) ^ 2)⁻¹ = Real.pi := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ) (fun y : ℝ => ((1 + y ^ 2) ^ 2)⁻¹)
  simp only [Complex.finrank_real_complex] at h
  rw [show (fun z : ℂ => ((sz z) ^ 2)⁻¹) = fun z : ℂ => ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ from rfl, h]
  simp only [Nat.add_one_sub_one, pow_one, smul_eq_mul, Measure.real, Complex.volume_ball,
    ENNReal.ofReal_one, one_pow, one_mul, ENNReal.coe_toReal, NNReal.coe_real_pi]
  rw [integral_Ioi_mul_inv_one_add_sq_sq]
  ring

/-! ## The stabiliser of `z` -/

/-- `A_z = [[1, -z̄], [z, 1]]`, a multiple of an `SU(2)` matrix: `A_z A_z* = (1 + |z|²) 1`. -/
noncomputable def aMat (z : ℂ) : P2 := mat2 1 (-conj z) z 1

/-- `A_z* = [[1, z̄], [-z, 1]]`. -/
noncomputable def aMatS (z : ℂ) : P2 := mat2 1 (conj z) (-z) 1

/-- **The stabiliser of `z`**: `S(z)⁻¹ A_z* [[μ, x], [0, μ⁻¹]] A_z`. These are the elements `g` with
`mob g z = z`; `den g z = μ⁻¹`. -/
noncomputable def stabPt (z μ x : ℂ) : P2 := (sz z)⁻¹ • mm3 (aMatS z) (triMat μ x) (aMat z)

/-- `S(z) = 1 + z z̄` in `ℂ`. -/
lemma ofReal_sz (z : ℂ) : ((sz z : ℝ) : ℂ) = 1 + z * conj z := by
  rw [mul_conj, normSq_eq_norm_sq, sz]; push_cast; ring

/-- `1 + z z̄ ≠ 0`. -/
lemma one_add_mul_conj_ne_zero (z : ℂ) : 1 + z * conj z ≠ 0 := by
  rw [← ofReal_sz]; exact_mod_cast (sz_pos z).ne'

/-- The entries of `stabPt`. -/
lemma stabPt_apply (z μ x : ℂ) :
    stabPt z μ x = mat2 ((μ + x * z + conj z * μ⁻¹ * z) / (1 + z * conj z))
      ((x - μ * conj z + conj z * μ⁻¹) / (1 + z * conj z))
      ((-(z * μ) - x * z * z + μ⁻¹ * z) / (1 + z * conj z))
      ((μ * z * conj z - x * z + μ⁻¹) / (1 + z * conj z)) := by
  have hS := one_add_mul_conj_ne_zero z
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [stabPt, mm3_apply, aMat, aMatS, triMat, Fin.sum_univ_two, Complex.real_smul,
        ofReal_inv, ofReal_sz]
      field_simp
      ring

/-- **The diagonal fibre is the stabiliser.** For `λ ≠ 0` the chart point `g_z(b, z, λ)` is
`S(z)⁻¹ A_z* [[μ, x], [0, μ⁻¹]] A_z` with `μ = 1/λ` and `x = S(z) b + z̄ (1/λ - λ)`. -/
theorem chartPt_diag (z b l : ℂ) (hl : l ≠ 0) :
    ((chartPt z z (b, l) : M2) : P2) = stabPt z l⁻¹ ((sz z : ℂ) * b + conj z * (l⁻¹ - l)) := by
  have hS := one_add_mul_conj_ne_zero z
  have hg := fixChart_apply z (y := ![b, z, l]) (by simpa using hl)
  rw [stabPt_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [chartPt, hg, ofReal_sz]
      field_simp
      ring

/-- **The SU(2) conjugates of `[[μ, x], [0, μ⁻¹]]`.** For `v₀ ≠ 0`, conjugation by `K_v / |v|`
lands in the stabiliser of `z = v₁ / v̄₀`, with `x` turned by the phase `v̄₀ / v₀`. -/
theorem conjV_triMat {v : Fin 2 → ℂ} (h0 : v 0 ≠ 0) (μ x : ℂ) :
    conjV v (triMat μ x) = stabPt (v 1 / conj (v 0)) μ (conj (v 0) / v 0 * x) := by
  have h0' : conj (v 0) ≠ 0 := (map_ne_zero _).2 h0
  have hz := one_add_mul_conj_ne_zero (v 1 / conj (v 0))
  have hn : ((nsq v : ℝ) : ℂ) = v 0 * conj (v 0) + v 1 * conj (v 1) := by
    rw [nsq_ofReal]
  have hn0 : v 0 * conj (v 0) + v 1 * conj (v 1) ≠ 0 := by
    rw [← hn]; exact_mod_cast (by
      have : 0 < nsq v := by
        unfold nsq; have := norm_pos_iff.2 h0; positivity
      exact this.ne')
  rw [stabPt_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [conjV, mm3_apply, kv, kvs, triMat, Fin.sum_univ_two, Complex.real_smul, ofReal_inv,
        hn, map_div₀]
      field_simp
      ring

/-! ## Measurability and bounds -/

/-- A `2 × 2` matrix with measurable entries is measurable. -/
lemma measurable_mat2 {X : Type*} [MeasurableSpace X] {a b c d : X → ℂ} (ha : Measurable a)
    (hb : Measurable b) (hc : Measurable c) (hd : Measurable d) :
    Measurable fun x => mat2 (a x) (b x) (c x) (d x) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simpa

/-- `stabPt` is measurable in all three arguments. -/
lemma measurable_stabPt {X : Type*} [MeasurableSpace X] {a b c : X → ℂ} (ha : Measurable a)
    (hb : Measurable b) (hc : Measurable c) :
    Measurable fun x => stabPt (a x) (b x) (c x) := by
  simp_rw [stabPt_apply]
  apply measurable_mat2 <;> fun_prop

/-- `A_z` and `A_z*` have sup norm at most `√S(z)`. -/
lemma norm_aMat_le (z : ℂ) : ‖aMat z‖ ≤ √(sz z) ∧ ‖aMatS z‖ ≤ √(sz z) := by
  have h1 : ‖(1 : ℂ)‖ ≤ √(sz z) := by
    rw [norm_one, Real.one_le_sqrt]; unfold sz; nlinarith [sq_nonneg ‖z‖]
  have h2 : ‖z‖ ≤ √(sz z) := Real.le_sqrt_of_sq_le (by unfold sz; linarith)
  have hs : 0 ≤ √(sz z) := Real.sqrt_nonneg _
  refine ⟨norm_mat2_le hs h1 (by rwa [norm_neg, Complex.norm_conj]) h2 h1,
    norm_mat2_le hs h1 (by rwa [Complex.norm_conj]) (by rwa [norm_neg]) h1⟩

/-- Inverting `stabPt`: `[[μ, x], [0, μ⁻¹]] = S⁻¹ A_z (stabPt z μ x) A_z*`. -/
lemma triMat_eq (z μ x : ℂ) : triMat μ x = (sz z)⁻¹ • mm3 (aMat z) (stabPt z μ x) (aMatS z) := by
  have hS := one_add_mul_conj_ne_zero z
  rw [stabPt_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [mm3_apply, aMat, aMatS, triMat, Fin.sum_univ_two, Complex.real_smul, ofReal_inv,
        ofReal_sz]
      field_simp
      ring

/-- `‖[[μ, x], [0, μ⁻¹]]‖ ≤ 4 ‖stabPt z μ x‖`, uniformly in `z`. -/
lemma norm_triMat_le (z μ x : ℂ) : ‖triMat μ x‖ ≤ 4 * ‖stabPt z μ x‖ := by
  obtain ⟨hA, hA'⟩ := norm_aMat_le z
  have hS := sz_pos z
  rw [triMat_eq z, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hS.le)]
  calc (sz z)⁻¹ * ‖mm3 (aMat z) (stabPt z μ x) (aMatS z)‖
      ≤ (sz z)⁻¹ * (4 * √(sz z) * ‖stabPt z μ x‖ * √(sz z)) := by
        gcongr
        exact (norm_mm3_le _ _ _).trans (by gcongr)
    _ = 4 * ‖stabPt z μ x‖ := by
        rw [show 4 * √(sz z) * ‖stabPt z μ x‖ * √(sz z) =
          4 * ‖stabPt z μ x‖ * (√(sz z) * √(sz z)) by ring, Real.mul_self_sqrt hS.le]
        field_simp

/-- **Support bound in the stabiliser.** If `F` vanishes outside the ball of radius `C` and
`F(stabPt z μ x) ≠ 0`, then `|μ|, |μ⁻¹|, |x| ≤ 4C`, uniformly in `z`. -/
lemma stab_bound {F : P2 → ℂ} {C : ℝ} (hC : ∀ X : P2, C ≤ ‖X‖ → F X = 0) {z μ x : ℂ}
    (h : F (stabPt z μ x) ≠ 0) : ‖μ‖ ≤ 4 * C ∧ ‖μ⁻¹‖ ≤ 4 * C ∧ ‖x‖ ≤ 4 * C := by
  have hY : ‖stabPt z μ x‖ ≤ C := by
    by_contra h'; exact h (hC _ (not_le.1 h').le)
  have hT := (norm_triMat_le z μ x).trans (by linarith : 4 * ‖stabPt z μ x‖ ≤ 4 * C)
  refine ⟨?_, ?_, ?_⟩
  · simpa [triMat] using (norm_apply_le (triMat μ x) 0 0).trans hT
  · simpa [triMat] using (norm_apply_le (triMat μ x) 1 1).trans hT
  · simpa [triMat] using (norm_apply_le (triMat μ x) 0 1).trans hT

/-! ## The `x`-integral over the stabiliser -/

/-- **`G_z(μ) = ∫ F(S⁻¹ A_z* [[μ, x], [0, μ⁻¹]] A_z) d²x`**, the integral of `F` over the
`x`-line of the stabiliser of `z`. -/
noncomputable def stabInt (F : P2 → ℂ) (z μ : ℂ) : ℂ := ∫ x, F (stabPt z μ x)

/-- `G_z(μ) = 0` unless `|μ|, |μ⁻¹| ≤ 4C`. -/
lemma stabInt_eq_zero {F : P2 → ℂ} {C : ℝ} (hC : ∀ X : P2, C ≤ ‖X‖ → F X = 0) (z : ℂ) {μ : ℂ}
    (hμ : ¬(‖μ‖ ≤ 4 * C ∧ ‖μ⁻¹‖ ≤ 4 * C)) : stabInt F z μ = 0 := by
  have h : ∀ x, F (stabPt z μ x) = 0 := fun x => by
    by_contra h
    obtain ⟨h1, h2, _⟩ := stab_bound hC h
    exact hμ ⟨h1, h2⟩
  simp [stabInt, h]

/-- The bound `|F| ≤ B` times the indicator of the `x`-ball of radius `4C`. -/
noncomputable def stabMass (B C : ℝ) : ℝ := ∫ x : ℂ, (closedBall (0 : ℂ) (4 * C)).indicator
  (fun _ => B) x

/-- `|G_z(μ)| ≤ B · π (4C)²`, uniformly in `z` and `μ`. -/
lemma norm_stabInt_le {F : P2 → ℂ} {B C : ℝ} (hB : ∀ X, ‖F X‖ ≤ B)
    (hC : ∀ X : P2, C ≤ ‖X‖ → F X = 0) (z μ : ℂ) : ‖stabInt F z μ‖ ≤ stabMass B C := by
  refine norm_integral_le_of_norm_le (integrable_indicator_isCompact (isCompact_closedBall _ _) B)
    (Eventually.of_forall fun x => ?_)
  by_cases h : F (stabPt z μ x) = 0
  · rw [h, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => (norm_nonneg _).trans (hB 0)) _
  · rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 (stab_bound hC h).2.2)]
    exact hB _

/-- `(z, μ) ↦ G_z(μ)` is strongly measurable. -/
lemma stronglyMeasurable_stabInt {F : P2 → ℂ} (hF : Continuous F) :
    StronglyMeasurable fun p : ℂ × ℂ => stabInt F p.1 p.2 := by
  have hm : Measurable fun q : (ℂ × ℂ) × ℂ => F (stabPt q.1.1 q.1.2 q.2) :=
    hF.measurable.comp (measurable_stabPt (by fun_prop) (by fun_prop) (by fun_prop))
  exact hm.stronglyMeasurable.integral_prod_right'

/-! ## The diagonal kernel as an integral over the stabiliser -/

/-- The weight `S(z)⁻² = (1 + |z|²)⁻²`. -/
noncomputable def sw (z : ℂ) : ℝ := ((sz z) ^ 2)⁻¹

/-- The weight is positive. -/
lemma sw_pos (z : ℂ) : 0 < sw z := by unfold sw; have := sz_pos z; positivity

/-- The weight `(1 + |z|²)⁻²` is integrable. -/
lemma integrable_sw : Integrable sw := integrable_sz_inv_sq

/-- `∫ (1 + |z|²)⁻² d²z = π`. -/
lemma integral_sw : ∫ z, sw z = Real.pi := integral_sz_inv_sq

/-- The weight is continuous. -/
lemma continuous_sw : Continuous sw := by
  unfold sw
  exact (continuous_sz.pow 2).inv₀ fun z => pow_ne_zero 2 (sz_pos z).ne'

/-- The integrand of `K_F(z, z)` after `chartPt_diag`. -/
noncomputable def diagIntegrand (F : P2 → ℂ) (n : ℤ) (ρ : ℝ) (z : ℂ) (q : ℂ × ℂ) : ℂ :=
  F (stabPt z q.2⁻¹ ((sz z : ℂ) * q.1 + conj z * (q.2⁻¹ - q.2))) * mult n ρ q.2

/-- The integrand of `K_F(z, z)` equals `diagIntegrand`, also at `λ = 0` where both vanish. -/
lemma diagIntegrand_eq (F : P2 → ℂ) (n : ℤ) (ρ : ℝ) (z : ℂ) (q : ℂ × ℂ) :
    F (chartPt z z q : M2) * mult n ρ q.2 = diagIntegrand F n ρ z q := by
  unfold diagIntegrand
  by_cases hq : q.2 = 0
  · simp [hq, mult_zero_right]
  · rw [chartPt_diag z q.1 q.2 hq]

/-- The integrand of `K_F(z, z)` is integrable in `(b, λ)`: it is bounded and vanishes
outside a ball. -/
lemma integrable_diagIntegrand {F : P2 → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (n : ℤ) (ρ : ℝ) (z : ℂ) : Integrable (diagIntegrand F n ρ z) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_support hFc
  obtain ⟨B, hB⟩ := hF.bounded_above_of_compact_support hFc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set R := 4 * C + 8 * C * ‖z‖
  refine (integrable_indicator_isCompact (μ := (volume : Measure (ℂ × ℂ)))
    (isCompact_closedBall (0 : ℂ × ℂ) R) (B * (4 * C) ^ 2)).mono' ?_
    (Eventually.of_forall fun q => ?_)
  · have hs : Measurable fun q : ℂ × ℂ =>
        stabPt z q.2⁻¹ ((sz z : ℂ) * q.1 + conj z * (q.2⁻¹ - q.2)) :=
      measurable_stabPt measurable_const (by fun_prop) (by fun_prop)
    exact ((hF.measurable.comp hs).mul
      ((measurable_mult n ρ).comp measurable_snd)).aestronglyMeasurable
  have hnn : 0 ≤ (closedBall (0 : ℂ × ℂ) R).indicator (fun _ => B * (4 * C) ^ 2) q :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  unfold diagIntegrand
  by_cases hq : q.2 = 0
  · simpa [hq, mult_zero_right] using hnn
  by_cases h : F (stabPt z q.2⁻¹ ((sz z : ℂ) * q.1 + conj z * (q.2⁻¹ - q.2))) = 0
  · simpa [h] using hnn
  obtain ⟨h1, h2, h3⟩ := stab_bound hC h
  rw [inv_inv] at h2
  have hS : 1 ≤ sz z := by unfold sz; nlinarith [sq_nonneg ‖z‖]
  have hb : ‖q.1‖ ≤ R := by
    have e : (sz z : ℂ) * q.1 = ((sz z : ℂ) * q.1 + conj z * (q.2⁻¹ - q.2)) -
        conj z * (q.2⁻¹ - q.2) := by ring
    have h4 : ‖(sz z : ℂ) * q.1‖ ≤ 4 * C + ‖z‖ * (4 * C + 4 * C) := by
      rw [e]
      refine (norm_sub_le _ _).trans (add_le_add h3 ?_)
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2))
        (norm_nonneg _)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sz_pos z).le] at h4
    calc ‖q.1‖ ≤ sz z * ‖q.1‖ := le_mul_of_one_le_left (norm_nonneg _) hS
      _ ≤ R := by linarith
  have hqR : ‖q‖ ≤ R := by
    rw [Prod.norm_def]
    exact max_le hb (h2.trans (by have := norm_nonneg z; nlinarith))
  have hm : ‖mult n ρ q.2‖ ≤ (4 * C) ^ 2 := by
    rw [norm_mult n ρ hq, ← inv_pow, ← norm_inv]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 hqR), norm_mul]
  exact mul_le_mul (hB _) hm (norm_nonneg _) hB0

/-- **(A) The diagonal kernel as a stabiliser integral**:
`K_F(z, z) = S(z)⁻² ∫ m(λ) G_z(1/λ) d²λ`. The fibre over `(z, z)` is the stabiliser of `z`
(`chartPt_diag`), and `b ↦ x = S(z) b + z̄(1/λ - λ)` has Jacobian `S(z)²`. -/
theorem psKernel_diag {F : P2 → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F) (n : ℤ)
    (ρ : ℝ) (z : ℂ) :
    psKernel n ρ (fun g => F (g : M2)) z z =
      ∫ l, (sw z : ℂ) * (mult n ρ l * stabInt F z l⁻¹) := by
  have h1 : psKernel n ρ (fun g => F (g : M2)) z z = ∫ q, diagIntegrand F n ρ z q := by
    unfold psKernel
    exact integral_congr_ae (Eventually.of_forall fun q => diagIntegrand_eq F n ρ z q)
  rw [h1, Measure.volume_eq_prod, integral_prod_symm _ (integrable_diagIntegrand hF hFc n ρ z)]
  refine integral_congr_ae (Eventually.of_forall fun l => ?_)
  simp only [diagIntegrand]
  rw [integral_mul_const]
  have h2 := integral_comp_real_mul_complex
    (fun y => F (stabPt z l⁻¹ (y + conj z * (l⁻¹ - l)))) (sz_pos z)
  rw [h2, integral_add_right_eq_self (fun y => F (stabPt z l⁻¹ y)), sw, stabInt]
  rw [Complex.real_smul]
  push_cast
  ring

/-! ## Push-forward of `ψ(|v|²) d⁴v` to the Riemann sphere -/

/-- A bounded measurable function that vanishes outside a closed ball is integrable. -/
lemma integrable_of_bound_ball {X : Type*} [NormedAddCommGroup X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [ProperSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) {B R : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (hR : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) : Integrable f μ := by
  refine (integrable_indicator_isCompact (isCompact_closedBall (0 : X) R) B).mono' hf
    (Eventually.of_forall fun x => ?_)
  by_cases h : f x = 0
  · rw [h, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => (norm_nonneg _).trans (hB x)) _
  · rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 (hR x h))]
    exact hB x

/-- On the support of `ψ`, `1/2 < t < 3/2`. -/
lemma lt_of_avgBump_ne_zero {t : ℝ} (h : avgBump t ≠ 0) : 1 / 2 < t ∧ t < 3 / 2 := by
  have h1 : t ∈ Function.support ⇑avgBump := h
  have hr : avgBump.rOut = 1 / 2 := rfl
  rw [avgBump.support_eq, hr, mem_ball, Real.dist_eq] at h1
  obtain ⟨h2, h3⟩ := abs_lt.1 h1
  constructor <;> linarith

/-- **`C_ψ = ∫ |w|² ψ(|w|²) d²w`**, the constant of the push-forward. -/
noncomputable def bumpMass : ℝ := ∫ w : ℂ, ‖w‖ ^ 2 * avgBump (‖w‖ ^ 2)

/-- `∫ |a|² ψ(s |a|²) d²a = s⁻² C_ψ` for `s > 0` (substitute `a = w/√s`). -/
lemma integral_bump_scale {s : ℝ} (hs : 0 < s) :
    ∫ a : ℂ, ‖a‖ ^ 2 * avgBump (‖a‖ ^ 2 * s) = (s ^ 2)⁻¹ * bumpMass := by
  have hr : 0 < (√s)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hs)
  have hr2 : ((√s)⁻¹) ^ 2 = s⁻¹ := by rw [inv_pow, Real.sq_sqrt hs.le]
  have hs0 := hs.ne'
  have h := integral_comp_real_mul_complex (fun a : ℂ => ‖a‖ ^ 2 * avgBump (‖a‖ ^ 2 * s)) hr
  have he : ∀ w : ℂ, ‖(((√s)⁻¹ : ℝ) : ℂ) * w‖ ^ 2 * avgBump (‖(((√s)⁻¹ : ℝ) : ℂ) * w‖ ^ 2 * s) =
      s⁻¹ * (‖w‖ ^ 2 * avgBump (‖w‖ ^ 2)) := fun w => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, mul_pow, hr2,
      show s⁻¹ * ‖w‖ ^ 2 * s = ‖w‖ ^ 2 by field_simp]
    ring
  rw [integral_congr_ae (Eventually.of_forall he), integral_const_mul, hr2, inv_inv,
    smul_eq_mul] at h
  set I := ∫ a : ℂ, ‖a‖ ^ 2 * avgBump (‖a‖ ^ 2 * s)
  calc I = s⁻¹ * (s * I) := by field_simp
    _ = (s ^ 2)⁻¹ * bumpMass := by rw [← h, bumpMass]; ring

/-- The kernel `|a|² ψ(|a|² S(z))` of the push-forward, after `b = ā z`. -/
noncomputable def pfKernel (a z : ℂ) : ℝ := ‖a‖ ^ 2 * avgBump (‖a‖ ^ 2 * sz z)

/-- The push-forward kernel is continuous. -/
lemma continuous_pfKernel : Continuous fun p : ℂ × ℂ => pfKernel p.1 p.2 := by
  unfold pfKernel
  exact ((continuous_norm.comp continuous_fst).pow 2).mul (avgBump.continuous.comp
    (((continuous_norm.comp continuous_fst).pow 2).mul (continuous_sz.comp continuous_snd)))

/-- The push-forward kernel is nonnegative. -/
lemma pfKernel_nonneg (a z : ℂ) : 0 ≤ pfKernel a z :=
  mul_nonneg (by positivity) avgBump.nonneg

/-- On its support the push-forward kernel has `|a| ≤ 2` and value at most `2`. -/
lemma pfKernel_bound {a z : ℂ} (h : pfKernel a z ≠ 0) : ‖a‖ ≤ 2 ∧ pfKernel a z ≤ 2 := by
  have hb : avgBump (‖a‖ ^ 2 * sz z) ≠ 0 := fun h0 => h (by simp [pfKernel, h0])
  have h1 := (lt_of_avgBump_ne_zero hb).2
  have hS : 1 ≤ sz z := by unfold sz; nlinarith [sq_nonneg ‖z‖]
  have ha : ‖a‖ ^ 2 < 3 / 2 := by
    nlinarith [mul_nonneg (sq_nonneg ‖a‖) (sub_nonneg.2 hS)]
  refine ⟨by nlinarith [norm_nonneg a], ?_⟩
  unfold pfKernel
  calc ‖a‖ ^ 2 * avgBump (‖a‖ ^ 2 * sz z) ≤ ‖a‖ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left avgBump.le_one (by positivity)
    _ ≤ 2 := by linarith

/-- `∫ |a|² ψ(|a|² S(z)) d²a = (1 + |z|²)⁻² C_ψ`. -/
lemma integral_pfKernel (z : ℂ) : ∫ a, pfKernel a z = sw z * bumpMass := by
  unfold pfKernel sw
  exact integral_bump_scale (sz_pos z)

/-- For `a ≠ 0`, the substitution `b = ā z` in the fibre over `a`. -/
lemma integral_bump_fibre (H : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0) :
    ∫ b : ℂ, (avgBump (‖a‖ ^ 2 + ‖b‖ ^ 2) : ℂ) * H (b / conj a) =
      ∫ z, (pfKernel a z : ℂ) * H z := by
  have hc : conj a ≠ 0 := (map_ne_zero _).2 ha
  have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ha
  have h := integral_comp_mul_left_complex
    (fun b : ℂ => (avgBump (‖a‖ ^ 2 + ‖b‖ ^ 2) : ℂ) * H (b / conj a)) hc
  have he : ∀ z : ℂ, (avgBump (‖a‖ ^ 2 + ‖conj a * z‖ ^ 2) : ℂ) * H (conj a * z / conj a) =
      (avgBump (‖a‖ ^ 2 * sz z) : ℂ) * H z := fun z => by
    rw [mul_div_cancel_left₀ z hc, norm_mul, Complex.norm_conj, sz,
      show ‖a‖ ^ 2 + (‖a‖ * ‖z‖) ^ 2 = ‖a‖ ^ 2 * (1 + ‖z‖ ^ 2) by ring]
  rw [integral_congr_ae (Eventually.of_forall he), Complex.norm_conj, Complex.real_smul] at h
  have h2 : ∫ z, (pfKernel a z : ℂ) * H z =
      (‖a‖ : ℂ) ^ 2 * ∫ z, (avgBump (‖a‖ ^ 2 * sz z) : ℂ) * H z := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [pfKernel]
    push_cast
    ring
  rw [h2, h]
  push_cast
  field_simp

/-- `(a, z) ↦ |a|² ψ(|a|² S(z)) H(z)` is integrable for bounded measurable `H`. -/
lemma integrable_pfKernel_mul {H : ℂ → ℂ} (hH : StronglyMeasurable H) {M : ℝ}
    (hM : ∀ z, ‖H z‖ ≤ M) :
    Integrable (fun p : ℂ × ℂ => (pfKernel p.1 p.2 : ℂ) * H p.2) (volume.prod volume) := by
  have hm : AEStronglyMeasurable (fun p : ℂ × ℂ => (pfKernel p.1 p.2 : ℂ) * H p.2)
      (volume.prod volume) :=
    ((Complex.continuous_ofReal.comp continuous_pfKernel).stronglyMeasurable.mul
      (hH.comp_measurable measurable_snd)).aestronglyMeasurable
  have hn : ∀ a z : ℂ, ‖(pfKernel a z : ℂ) * H z‖ = pfKernel a z * ‖H z‖ := fun a z => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pfKernel_nonneg a z)]
  refine (integrable_prod_iff' hm).2 ⟨Eventually.of_forall fun z => ?_, ?_⟩
  · have hc : Continuous fun a : ℂ => (pfKernel a z : ℂ) * H z :=
      (Complex.continuous_ofReal.comp (continuous_pfKernel.comp
        (continuous_id.prodMk continuous_const))).mul continuous_const
    refine integrable_of_bound_ball hc.aestronglyMeasurable (B := 2 * M) (R := 2)
      (fun a => ?_) (fun a ha => ?_)
    · rw [hn]
      by_cases h0 : pfKernel a z = 0
      · rw [h0, zero_mul]; linarith [(norm_nonneg _).trans (hM 0)]
      · exact mul_le_mul (pfKernel_bound h0).2 (hM z) (norm_nonneg _) (by norm_num)
    · exact (pfKernel_bound (z := z) fun h0 => ha (by simp [h0])).1
  · have he : (fun z => ∫ a, ‖(pfKernel a z : ℂ) * H z‖) = fun z => ‖H z‖ * (sw z * bumpMass) := by
      funext z
      simp_rw [hn]
      rw [integral_mul_const, integral_pfKernel, mul_comm]
    simp only [he]
    exact (integrable_sw.mul_const bumpMass).bdd_mul (hH.norm.aestronglyMeasurable)
      (c := M) (Eventually.of_forall fun z => by rw [norm_norm]; exact hM z)

/-- **Push-forward of `ψ(|v|²) d⁴v` to the Riemann sphere**:
`∫ ψ(|v|²) H(v₁/v̄₀) d⁴v = C_ψ ∫ (1 + |z|²)⁻² H(z) d²z` for bounded measurable `H`. -/
theorem integral_avgWeight_comp {H : ℂ → ℂ} (hH : StronglyMeasurable H) {M : ℝ}
    (hM : ∀ z, ‖H z‖ ≤ M) :
    ∫ v : Fin 2 → ℂ, (avgWeight v : ℂ) * H (v 1 / conj (v 0)) =
      (bumpMass : ℂ) * ∫ z, (sw z : ℂ) * H z := by
  have h1 : ∫ v : Fin 2 → ℂ, (avgWeight v : ℂ) * H (v 1 / conj (v 0)) =
      ∫ p : ℂ × ℂ, (avgBump (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) : ℂ) * H (p.2 / conj p.1) := by
    rw [← (volume_preserving_finTwoArrow ℂ).integral_comp'
      (fun p : ℂ × ℂ => (avgBump (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) : ℂ) * H (p.2 / conj p.1))]
    rfl
  have hfi : Integrable (fun p : ℂ × ℂ => (avgBump (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) : ℂ) *
      H (p.2 / conj p.1)) (volume.prod volume) := by
    have hc : Continuous fun p : ℂ × ℂ => (avgBump (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) : ℂ) :=
      Complex.continuous_ofReal.comp (avgBump.continuous.comp (by fun_prop))
    have hm : StronglyMeasurable fun p : ℂ × ℂ => H (p.2 / conj p.1) :=
      hH.comp_measurable (g := fun p : ℂ × ℂ => p.2 / conj p.1) (by fun_prop)
    refine integrable_of_bound_ball (hc.stronglyMeasurable.mul hm).aestronglyMeasurable
      (B := M) (R := 2) (fun p => ?_) (fun p hp => ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg avgBump.nonneg]
      exact (mul_le_of_le_one_left (norm_nonneg _) avgBump.le_one).trans (hM _)
    · have hb : avgBump (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) ≠ 0 := fun h0 => hp (by simp [h0])
      have h3 := (lt_of_avgBump_ne_zero hb).2
      rw [Prod.norm_def]
      exact max_le (by nlinarith [norm_nonneg p.1, sq_nonneg ‖p.2‖])
        (by nlinarith [norm_nonneg p.2, sq_nonneg ‖p.1‖])
  have hae : ∀ᵐ a : ℂ, a ≠ 0 := by
    rw [ae_iff]
    simp
  rw [h1, Measure.volume_eq_prod, integral_prod _ hfi,
    integral_congr_ae (hae.mono fun a ha => integral_bump_fibre H ha),
    integral_integral_swap (integrable_pfKernel_mul hH hM), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [integral_mul_const, integral_complex_ofReal, integral_pfKernel]
  push_cast
  ring

/-- **The normalisation of the average**: `∫ ψ(|v|²) d⁴v = π C_ψ`. -/
theorem avgNorm_eq : avgNorm = Real.pi * bumpMass := by
  have h := integral_avgWeight_comp (H := fun _ => (1 : ℂ)) stronglyMeasurable_const (M := 1)
    (fun _ => by simp)
  simp only [mul_one] at h
  rw [integral_complex_ofReal, integral_complex_ofReal, integral_sw] at h
  unfold avgNorm
  exact_mod_cast h.trans (mul_comm _ _)

/-- `C_ψ > 0`. -/
lemma bumpMass_pos : 0 < bumpMass := by
  have h := avgNorm_pos
  rw [avgNorm_eq] at h
  exact pos_of_mul_pos_right h Real.pi_pos.le

/-! ## Averaging the stabiliser integral over `z` -/

/-- **(B)** `∫ (1 + |z|²)⁻² G_z(μ) d²z = π · orbInt F♮(μ)`: averaging over the sphere of the
fixed point `z` is the `SU(2)` conjugation average. -/
theorem integral_sw_stabInt {F : P2 → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (μ : ℂ) : ∫ z, (sw z : ℂ) * stabInt F z μ = Real.pi * orbInt (su2Avg F) μ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_support hFc
  obtain ⟨B, hB⟩ := hF.bounded_above_of_compact_support hFc
  have hc : Continuous (Function.uncurry (avgIntegrand F)) :=
    (contDiff_avgIntegrand (n := 0) (contDiff_zero.2 hF)).continuous
  have htri : Measurable fun p : ℂ × (Fin 2 → ℂ) => triMat μ p.1 :=
    measurable_mat2 measurable_const measurable_fst measurable_const measurable_const
  have hm : Measurable fun p : ℂ × (Fin 2 → ℂ) =>
      (avgWeight p.2 : ℂ) * F (conjV p.2 (triMat μ p.1)) :=
    hc.measurable.comp ((measurable_avgParam.comp measurable_snd).prodMk htri)
  have hi : Integrable (fun p : ℂ × (Fin 2 → ℂ) =>
      (avgWeight p.2 : ℂ) * F (conjV p.2 (triMat μ p.1))) (volume.prod volume) := by
    refine integrable_of_bound_ball hm.aestronglyMeasurable (B := B) (R := max (32 * C) 2)
      (fun p => ?_) (fun p hp => ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (avgWeight_nonneg _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (avgWeight_le_one _)).trans (hB _)
    · have hw : avgWeight p.2 ≠ 0 := fun h => hp (by simp [h])
      have hF0 : F (conjV p.2 (triMat μ p.1)) ≠ 0 := fun h => hp (by simp [h])
      have h1 : ‖conjV p.2 (triMat μ p.1)‖ ≤ C := by
        by_contra h'
        exact hF0 (hC _ (not_le.1 h').le)
      have h2 := norm_le_conjV hw (triMat μ p.1)
      have h3 : ‖p.1‖ ≤ ‖triMat μ p.1‖ := by
        simpa [triMat] using norm_apply_le (triMat μ p.1) 0 1
      have h4 : ‖p.2‖ ≤ 2 := by
        have := support_avgWeight_subset hw
        rwa [mem_closedBall, dist_zero_right] at this
      rw [Prod.norm_def]
      exact max_le_max (by linarith) h4
  have hinner : ∀ v : Fin 2 → ℂ, v 0 ≠ 0 →
      ∫ x : ℂ, (avgWeight v : ℂ) * F (conjV v (triMat μ x)) =
        (avgWeight v : ℂ) * stabInt F (v 1 / conj (v 0)) μ := by
    intro v h0
    rw [integral_const_mul]
    congr 1
    simp_rw [conjV_triMat h0]
    have hu : conj (v 0) / v 0 ≠ 0 := div_ne_zero ((map_ne_zero _).2 h0) h0
    rw [integral_comp_mul_left_complex (fun x => F (stabPt (v 1 / conj (v 0)) μ x)) hu,
      norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0), one_pow, inv_one,
      one_smul, stabInt]
  have hae : ∀ᵐ v : Fin 2 → ℂ, v 0 ≠ 0 := by
    rw [volume_pi]
    exact Measure.ae_eval_ne (α := fun _ : Fin 2 => ℂ) (fun _ => volume) 0 0
  have hHm : StronglyMeasurable fun z : ℂ => stabInt F z μ :=
    (stronglyMeasurable_stabInt hF).comp_measurable (g := fun z : ℂ => (z, μ))
      measurable_prodMk_right
  have hPF := integral_avgWeight_comp hHm (M := stabMass B C)
    (fun z => norm_stabInt_le hB hC z μ)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hbm : (bumpMass : ℂ) ≠ 0 := by exact_mod_cast bumpMass_pos.ne'
  unfold orbInt
  simp_rw [su2Avg]
  rw [integral_const_mul, integral_integral_swap (f := fun (x : ℂ) (v : Fin 2 → ℂ) =>
    (avgWeight v : ℂ) * F (conjV v (triMat μ x))) hi,
    integral_congr_ae (hae.mono fun v h0 => hinner v h0), hPF, avgNorm_eq]
  push_cast
  field_simp

/-! ## The trace -/

/-- **Exchange of the `z`- and `λ`-integrals**: `(z, λ) ↦ S⁻² m(λ) G_z(1/λ)` is integrable,
bounded by `S⁻²` times a multiple of the indicator of `|λ| ≤ 4C`. -/
lemma integrable_diag_stab {F : P2 → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (n : ℤ) (ρ : ℝ) :
    Integrable (fun p : ℂ × ℂ => (sw p.1 : ℂ) * (mult n ρ p.2 * stabInt F p.1 p.2⁻¹))
      (volume.prod volume) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_support hFc
  obtain ⟨B, hB⟩ := hF.bounded_above_of_compact_support hFc
  have hS0 : 0 ≤ stabMass B C := (norm_nonneg _).trans (norm_stabInt_le hB hC 0 0)
  have hK : Integrable ((closedBall (0 : ℂ) (4 * C)).indicator
      fun _ => (4 * C) ^ 2 * stabMass B C) :=
    integrable_indicator_isCompact (isCompact_closedBall _ _) _
  have h1 : StronglyMeasurable fun p : ℂ × ℂ => stabInt F p.1 p.2⁻¹ :=
    (stronglyMeasurable_stabInt hF).comp_measurable (measurable_fst.prodMk measurable_snd.inv)
  have hm : AEStronglyMeasurable (fun p : ℂ × ℂ =>
      (sw p.1 : ℂ) * (mult n ρ p.2 * stabInt F p.1 p.2⁻¹)) (volume.prod volume) :=
    ((Complex.continuous_ofReal.comp (continuous_sw.comp continuous_fst)).aestronglyMeasurable).mul
      ((((measurable_mult n ρ).comp measurable_snd).aestronglyMeasurable).mul
        h1.aestronglyMeasurable)
  refine (integrable_sw.mul_prod hK).mono' hm (Eventually.of_forall fun p => ?_)
  have hKn : 0 ≤ (closedBall (0 : ℂ) (4 * C)).indicator
      (fun _ => (4 * C) ^ 2 * stabMass B C) p.2 :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sw_pos _).le]
  refine mul_le_mul_of_nonneg_left ?_ (sw_pos _).le
  by_cases hl0 : p.2 = 0
  · rw [hl0, mult_zero_right, norm_zero, zero_mul]
    simpa [hl0] using hKn
  by_cases hG : stabInt F p.1 p.2⁻¹ = 0
  · rw [hG, norm_zero, mul_zero]
    exact hKn
  have hl : ‖p.2⁻¹‖ ≤ 4 * C ∧ ‖p.2⁻¹⁻¹‖ ≤ 4 * C := by
    by_contra h
    exact hG (stabInt_eq_zero hC p.1 h)
  rw [inv_inv] at hl
  rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 hl.2)]
  have hm' : ‖mult n ρ p.2‖ ≤ (4 * C) ^ 2 := by
    rw [norm_mult n ρ hl0, ← inv_pow, ← norm_inv]
    exact pow_le_pow_left₀ (norm_nonneg _) hl.1 2
  exact mul_le_mul hm' (norm_stabInt_le hB hC _ _) (norm_nonneg _) (by positivity)

/-- The diagonal `z ↦ K_F(z, z)` is integrable. -/
theorem integrable_psKernel_diag {F : P2 → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (n : ℤ) (ρ : ℝ) : Integrable fun z => psKernel n ρ (fun g => F (g : M2)) z z := by
  have h := (integrable_diag_stab hF hFc n ρ).integral_prod_left
  dsimp only at h
  simp_rw [psKernel_diag hF hFc n ρ]
  exact h

/-- **(C) The trace of `π_{n,ρ}(F)` as an orbital integral**:
`∫ K_F(z, z) d²z = π ∫ m_{n,ρ}(λ) · orbInt F♮(1/λ) d²λ`, with `F♮` the `SU(2)`
conjugation average of `F`. -/
theorem integral_psKernel_diag {F : P2 → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (n : ℤ) (ρ : ℝ) :
    ∫ z, psKernel n ρ (fun g => F (g : M2)) z z =
      Real.pi * ∫ l, mult n ρ l * orbInt (su2Avg F) l⁻¹ := by
  simp_rw [psKernel_diag hF hFc n ρ]
  rw [integral_integral_swap (f := fun z l : ℂ => (sw z : ℂ) * (mult n ρ l * stabInt F z l⁻¹))
    (integrable_diag_stab hF hFc n ρ), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun l => ?_)
  have h := integral_sw_stabInt hF hFc l⁻¹
  calc ∫ z, (sw z : ℂ) * (mult n ρ l * stabInt F z l⁻¹)
      = mult n ρ l * ∫ z, (sw z : ℂ) * stabInt F z l⁻¹ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        ring
    _ = _ := by rw [h]; ring

end Lightlike.Lorentz
