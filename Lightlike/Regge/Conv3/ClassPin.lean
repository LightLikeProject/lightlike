import Lightlike.Regge.Conv3.ChartChangeFan
import Lightlike.Regge.Conv3.ClosedFan

/-!
# A closed fan of displaced vectors still adds up to `2π`

For a positive definite `G`, a hinge axis `w ε` and the vectors `xs 0 ε, …, xs n ε` of a closed fan
(`xs n = xs 0`), all continuous in a parameter `ε`: if the dihedral angles of the fan add up to `2π`
at `ε = 0` and the orientation is positive there, then they add up to `2π` for all small `ε`
(`closed_class_pin`). The proof is the complex coordinate of `StarAngle.lean` (the sum is `2πk`
by `closed_fan_sum`) and continuity of the sum, which pins `k` (`eventually_eq_of_int_mul`).

**Limits.** The statement is local in `ε` (a neighbourhood of `0`, not an explicit bound) and is about
one fan; applying it to the seven edge classes of the Kuhn star is a separate step.
-/

open Complex Real Filter Topology Matrix
namespace Lightlike.Regge.Conv3

/-- The quadratic form of `G` on two continuous curves is continuous. -/
theorem continuous_quad {G : Matrix (Fin 3) (Fin 3) ℝ} {u v : ℝ → Fin 3 → ℝ}
    (hu : Continuous u) (hv : Continuous v) : Continuous (fun t => u t ⬝ᵥ (G *ᵥ v t)) := by
  simp only [dotProduct, Matrix.mulVec]
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_pi_iff.1 hu i).mul ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul (continuous_pi_iff.1 hv j)

/-- The Schur form `bf` of continuous curves is continuous where the hinge is not null. -/
theorem continuousAt_bf {G : Matrix (Fin 3) (Fin 3) ℝ} {w x y : ℝ → Fin 3 → ℝ} {ε : ℝ}
    (hw : Continuous w) (hx : Continuous x) (hy : Continuous y)
    (ha : w ε ⬝ᵥ (G *ᵥ w ε) ≠ 0) : ContinuousAt (fun t => bf G (w t) (x t) (y t)) ε := by
  unfold bf
  have h1 := (continuous_quad (G := G) hx hy).continuousAt (x := ε)
  have h2 := (continuous_quad (G := G) hx hw).continuousAt (x := ε)
  have h3 := (continuous_quad (G := G) hw hy).continuousAt (x := ε)
  have h4 := (continuous_quad (G := G) hw hw).continuousAt (x := ε)
  exact h1.sub ((h2.mul h3).div h4 ha)

/-- The triple product of continuous curves is continuous. -/
theorem continuous_trip {w u v : ℝ → Fin 3 → ℝ} (hw : Continuous w) (hu : Continuous u)
    (hv : Continuous v) : Continuous (fun t => trip (w t) (u t) (v t)) := by
  have h := fun i : Fin 3 => continuous_pi_iff.1 hw i
  have h' := fun i : Fin 3 => continuous_pi_iff.1 hu i
  have h'' := fun i : Fin 3 => continuous_pi_iff.1 hv i
  unfold trip
  fun_prop

/-- The fan angle of continuous curves is continuous where both faces are nondegenerate. -/
theorem continuousAt_fanAng {G : Matrix (Fin 3) (Fin 3) ℝ} {w x y : ℝ → Fin 3 → ℝ} {ε : ℝ}
    (hw : Continuous w) (hx : Continuous x) (hy : Continuous y)
    (ha : w ε ⬝ᵥ (G *ᵥ w ε) ≠ 0) (hxx : 0 < bf G (w ε) (x ε) (x ε))
    (hyy : 0 < bf G (w ε) (y ε) (y ε)) :
    ContinuousAt (fun t => fanAng G (w t) (x t) (y t)) ε := by
  unfold fanAng
  have hxy := continuousAt_bf (G := G) hw hx hy ha
  have hxx' := continuousAt_bf (G := G) hw hx hx ha
  have hyy' := continuousAt_bf (G := G) hw hy hy ha
  have hs : ContinuousAt (fun t => √(bf G (w t) (x t) (x t) * bf G (w t) (y t) (y t))) ε :=
    (Real.continuous_sqrt.continuousAt).comp (hxx'.mul hyy')
  have hne : √(bf G (w ε) (x ε) (x ε) * bf G (w ε) (y ε) (y ε)) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos hxx hyy)).ne'
  exact Real.continuous_arccos.continuousAt.comp (hxy.div hs hne)

/-- **A closed fan of displaced vectors still adds up to `2π`.** Let `w ε` be the hinge axis and
`xs 0 ε, …, xs n ε` the vectors of a fan, all continuous in `ε`, with `xs n = xs 0` and positive
orientation at `ε = 0`. If the angles add up to `2π` at `ε = 0`, they do for all small `ε`. -/
theorem closed_class_pin {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.PosDef) {n : ℕ} (hn : 0 < n)
    (w : ℝ → Fin 3 → ℝ) (xs : ℕ → ℝ → Fin 3 → ℝ) (hwc : Continuous w)
    (hxc : ∀ i, Continuous (xs i)) (hw0 : w 0 ≠ 0)
    (hpos0 : ∀ i < n, 0 < trip (w 0) (xs i 0) (xs (i + 1) 0))
    (hclose : ∀ ε, xs n ε = xs 0 ε)
    (hS0 : ∑ i ∈ Finset.range n, fanAng G (w 0) (xs i 0) (xs (i + 1) 0) = 2 * π) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∑ i ∈ Finset.range n, fanAng G (w ε) (xs i ε) (xs (i + 1) ε) = 2 * π := by
  have hbf0 : ∀ i ≤ n, 0 < bf G (w 0) (xs i 0) (xs i 0) := by
    intro i hi
    rcases Nat.lt_or_ge i n with h | h
    · exact (bf_pos_of_trip hG hw0 (hpos0 i h).ne').1
    · have : i = n := by omega
      subst this
      have := (bf_pos_of_trip hG hw0 (hpos0 (i - 1) (by omega)).ne').2
      rwa [Nat.sub_add_cancel hn] at this
  -- eventual hypotheses
  have hw_ev : ∀ᶠ ε in 𝓝 (0 : ℝ), w ε ≠ 0 :=
    (hwc.continuousAt (x := 0)).eventually_ne hw0
  have ha_ev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < w ε ⬝ᵥ (G *ᵥ w ε) := by
    have hc := (continuous_quad (G := G) hwc hwc).continuousAt (x := (0 : ℝ))
    exact hc.eventually (lt_mem_nhds (posDef_dpos hG hw0))
  have hpos_ev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i ∈ Finset.range n,
      0 < trip (w ε) (xs i ε) (xs (i + 1) ε) := by
    refine (Filter.eventually_all_finset _).2 fun i hi => ?_
    have hc := (continuous_trip hwc (hxc i) (hxc (i + 1))).continuousAt (x := (0 : ℝ))
    exact hc.eventually (lt_mem_nhds (hpos0 i (Finset.mem_range.1 hi)))
  -- the sum is continuous at 0
  have hcont : ContinuousAt (fun ε => ∑ i ∈ Finset.range n,
      fanAng G (w ε) (xs i ε) (xs (i + 1) ε)) 0 := by
    have hterm : ∀ i ∈ Finset.range n, ContinuousAt
        (fun ε => fanAng G (w ε) (xs i ε) (xs (i + 1) ε)) 0 := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have h1 := hbf0 i (by omega)
      have h2 := hbf0 (i + 1) (by omega)
      exact continuousAt_fanAng hwc (hxc i) (hxc (i + 1)) (posDef_dpos hG hw0).ne' h1 h2
    exact tendsto_finsetSum _ hterm
  -- multiple of 2π eventually
  have hint : ∀ᶠ ε in 𝓝 (0 : ℝ), ∃ k : ℤ, ∑ i ∈ Finset.range n,
      fanAng G (w ε) (xs i ε) (xs (i + 1) ε) = 2 * π * k := by
    filter_upwards [hw_ev, ha_ev, hpos_ev] with ε hwε haε hpε
    have hpε' : ∀ i < n, 0 < trip (w ε) (xs i ε) (xs (i + 1) ε) := fun i hi =>
      hpε i (Finset.mem_range.2 hi)
    have hb : ∀ i < n, 0 < bf G (w ε) (xs i ε) (xs i ε) ∧
        0 < bf G (w ε) (xs (i + 1) ε) (xs (i + 1) ε) := fun i hi =>
      bf_pos_of_trip hG hwε (hpε' i hi).ne'
    have ht : 0 < bf G (w ε) (xs 0 ε) (xs 0 ε) := (hb 0 hn).1
    have hpos' : ∀ i ≤ n, 0 < bf G (w ε) (xs i ε) (xs i ε) := by
      intro i hi
      rcases Nat.lt_or_ge i n with h | h
      · exact (hb i h).1
      · have : i = n := by omega
        subst this
        have := (hb (i - 1) (by omega)).2
        rwa [Nat.sub_add_cancel hn] at this
    set z : ℕ → ℂ := fun i => iota G (w ε) (xs 0 ε) (xs i ε) with hz
    have hz0 : ∀ i ≤ n, z i ≠ 0 := fun i hi => iota_ne hG hwε ht (hpos' i hi)
    have him : ∀ i < n, 0 < (starRingEnd ℂ (z i) * z (i + 1)).im := by
      intro i hi
      simp only [hz]
      rw [conj_iota_mul hG hwε ht]
      simp only [zeta]
      exact mul_pos (Real.sqrt_pos.2 (div_pos hG.det_pos (posDef_dpos hG hwε))) (hpε' i hi)
    have hcl : z n = z 0 := by simp only [hz]; rw [hclose]
    obtain ⟨k, hk, -, -⟩ := closed_fan_sum hn z hz0 him hcl
    refine ⟨k, ?_⟩
    rw [← hk]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    simp only [hz]
    rw [conj_iota_mul hG hwε ht, ← arccos_eq_arg hG hwε (hpε' i hi')]
    rfl
  exact eventually_eq_of_int_mul hcont hS0 hint

end Lightlike.Regge.Conv3
