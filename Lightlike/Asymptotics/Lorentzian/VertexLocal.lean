import Lightlike.Asymptotics.Lorentzian.Vertex

/-!
# The vertex asymptotics for an action that is smooth only on an open set

`weighted_asymptotics` and `lorVertex_asymptotics` assume that the action is smooth on all of `ℝⁿ`,
which the Lorentzian action is not (it has logarithms of the overlaps and of the norms). Here the
hypothesis is `ContDiffOn ℝ ∞ S U` on an open set `U` containing the support of the localised
amplitude: a smooth cutoff `S' = χ S` equal to `S` on a neighbourhood of that support reduces the
statement to the global one (`exists_smooth_extension`), and the remainder `a_far` is still
controlled by its hypotheses for `S` itself.

## Main results

* `exists_smooth_extension`: a function smooth on an open `U` agrees near a compact `K ⊆ U` with a
  globally smooth function.
* `weighted_asymptotics_local`: `weighted_asymptotics` with `ContDiffOn ℝ ∞ S U`.
* `lorVertex_asymptotics_local`: `lorVertex_asymptotics` with `ContDiffOn ℝ ∞ (lorChartAction …) U`.
-/

open Complex Filter Asymptotics MeasureTheory Lightlike.Oscillatory Lightlike.Asymptotics.EPRL Metric
open scoped Real ContDiff Topology Matrix
open Lightlike.Lorentz (SL2C)

namespace Lightlike.Asymptotics.Lorentzian

variable {n : ℕ}

/-- **A smooth cutoff of a function that is smooth only on an open set**: if `S` is smooth on the
open set `U` and `K ⊆ U` is compact, there are a smooth function `S̃` on `ℝⁿ` and an open
neighbourhood `W` of `K` with `S̃ = S` on `W`. -/
theorem exists_smooth_extension {S : (Fin n → ℝ) → ℂ} {U K : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ S U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ S' : (Fin n → ℝ) → ℂ, ContDiff ℝ ∞ S' ∧ ∃ W : Set (Fin n → ℝ), IsOpen W ∧ K ⊆ W ∧
      ∀ x ∈ W, S' x = S x := by
  obtain ⟨δ, hδ, hcU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hd : Disjoint (thickening (δ / 2) K)ᶜ (cthickening (δ / 4) K) := by
    rw [Set.disjoint_compl_left_iff_subset]
    exact cthickening_subset_thickening' (by linarith) (by linarith) K
  obtain ⟨f, hf, -, hf0, hf1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (isOpen_thickening.isClosed_compl) isClosed_cthickening hd
  have hsupp : tsupport f ⊆ U := by
    have h1 : Function.support f ⊆ thickening (δ / 2) K := by
      intro x hx
      by_contra hxs
      exact hx ((hf0 x).1 hxs)
    have h2 : tsupport f ⊆ cthickening (δ / 2) K :=
      closure_minimal (h1.trans (thickening_subset_cthickening _ _)) isClosed_cthickening
    exact h2.trans ((cthickening_mono (by linarith) K).trans hcU)
  refine ⟨fun x => (f x : ℂ) * S x, ?_, thickening (δ / 4) K, isOpen_thickening,
    self_subset_thickening (by linarith) K, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (Complex.ofRealCLM.contDiff.comp hf).contDiffAt.mul
        ((hS.contDiffAt (hU.mem_nhds hx)))
    · have hz : ∀ᶠ y in nhds x, f y = 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsupp h)))
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hz] with y hy
      simp [hy]
  · intro x hx
    have : f x = 1 := (hf1 x).1 (thickening_subset_cthickening _ _ hx)
    simp [this]

/-- **`weighted_asymptotics` for an action that is smooth only on an open set `U`** containing the
support of `a_loc` (the Lorentzian action has logarithms and is not smooth everywhere). The
conclusion is that of `weighted_asymptotics`: the hypotheses `hK`, `hnd` are on `S` itself and the
remainder `a_far` is controlled by `hint` and `hfar` for `S`. -/
theorem weighted_asymptotics_local {S aLoc aFar : (Fin n → ℝ) → ℂ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hS : ContDiffOn ℝ ∞ S U) (hsU : tsupport aLoc ⊆ U)
    (ha : ContDiff ℝ ∞ aLoc) (hc : HasCompactSupport aLoc)
    (hRe : ∀ x ∈ tsupport aLoc, (S x).re ≤ 0) (K : Finset (Fin n → ℝ))
    (hK : ∀ x ∈ tsupport aLoc, ((S x).re = 0 ∧ fderiv ℝ S x = 0) ↔ x ∈ K)
    (hKs : ∀ x ∈ K, x ∈ tsupport aLoc) (hnd : ∀ x ∈ K, (-hessMat S x).det ≠ 0)
    (hint : ∀ τ : ℝ, Integrable fun x => aFar x * cexp (τ * S x))
    (hfar : (fun lam : ℕ => ∫ x, aFar x * cexp ((lam : ℝ) * S x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-((n : ℝ) / 2) - 1)))
    (w : ℕ → ℂ) (m : ℝ) (hw : w =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ m)) :
    (fun lam : ℕ => w lam * (∫ x, (aLoc x + aFar x) * cexp ((lam : ℝ) * S x)) -
        w lam * ∑ x₀ ∈ K, cexp ((lam : ℝ) * S x₀) *
          ((2 * π / (lam : ℝ)) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-hessMat S x₀) * aLoc x₀)
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (n : ℝ) / 2 - 1)) := by
  obtain ⟨S', hS', W, hW, hKW, hSW⟩ := exists_smooth_extension hU hS hc hsU
  have hfd : ∀ x ∈ W, fderiv ℝ S' x = fderiv ℝ S x := fun x hx =>
    Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hW.mem_nhds hx) hSW)
  have hhess : ∀ x ∈ W, hessMat S' x = hessMat S x := by
    intro x hx
    ext i j
    simp only [hessMat, coordDeriv]
    refine Filter.EventuallyEq.fderiv_eq ?_ |> fun h => by rw [h]
    filter_upwards [hW.mem_nhds hx] with y hy
    rw [hfd y hy]
  have hloc := expPhase_asymptotics hS' ha hc (fun x hx => by rw [hSW x (hKW hx)]; exact hRe x hx) K
    (fun x hx => by rw [hSW x (hKW hx), hfd x (hKW hx)]; exact hK x hx) hKs
    (fun x hx => by rw [hhess x (hKW (hKs x hx))]; exact hnd x hx)
  have hloc' := hloc.comp_tendsto tendsto_natCast_atTop_atTop
  have hint' : ∀ τ : ℝ, (fun x => aLoc x * cexp (τ * S' x)) = fun x => aLoc x * cexp (τ * S x) := by
    intro τ; funext x
    by_cases hx : x ∈ tsupport aLoc
    · rw [hSW x (hKW hx)]
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp
  have hsplit : ∀ τ : ℝ, ∫ x, (aLoc x + aFar x) * cexp (τ * S x) =
      (∫ x, aLoc x * cexp (τ * S' x)) + ∫ x, aFar x * cexp (τ * S x) := fun τ => by
    have h1 : Integrable fun x => aLoc x * cexp (τ * S' x) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (hc.mul_right)
      exact ha.continuous.mul (Complex.continuous_exp.comp (continuous_const.mul hS'.continuous))
    rw [hint' τ] at h1 ⊢
    simp only [add_mul]
    exact integral_add h1 (hint τ)
  have hsum : ∀ lam : ℕ, ∑ x₀ ∈ K, cexp ((lam : ℝ) * S' x₀) * ((2 * π / (lam : ℝ)) ^ ((n : ℝ) / 2) : ℝ) *
      invSqrtDet (-hessMat S' x₀) * aLoc x₀ = ∑ x₀ ∈ K, cexp ((lam : ℝ) * S x₀) *
      ((2 * π / (lam : ℝ)) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-hessMat S x₀) * aLoc x₀ := by
    intro lam
    refine Finset.sum_congr rfl fun x₀ hx₀ => ?_
    rw [hSW x₀ (hKW (hKs x₀ hx₀)), hhess x₀ (hKW (hKs x₀ hx₀))]
  have hmain : (fun lam : ℕ => (∫ x, (aLoc x + aFar x) * cexp ((lam : ℝ) * S x)) -
      ∑ x₀ ∈ K, cexp ((lam : ℝ) * S x₀) *
          ((2 * π / (lam : ℝ)) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-hessMat S x₀) * aLoc x₀)
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (-((n : ℝ) / 2) - 1)) := by
    have := hloc'.add hfar
    refine this.congr_left fun lam => ?_
    simp only [Function.comp, hsplit, ← hsum]
    ring
  have hprod := hw.mul hmain
  refine hprod.congr' (Eventually.of_forall fun lam => by simp only [mul_sub]) ?_
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  have : (0 : ℝ) < lam := by exact_mod_cast hlam
  rw [← Real.rpow_add this, sub_sub, add_sub_assoc']
  ring_nf


/-- **The vertex asymptotics in a chart on which the action is smooth only on an open set `U`**
(the local version of `lorVertex_asymptotics`): `hS : ContDiffOn ℝ ∞ (lorChartAction …) U` with
`tsupport aLoc ⊆ U`; all other hypotheses and the conclusion are those of `lorVertex_asymptotics`. -/
theorem lorVertex_asymptotics_local {n : ℕ} {j p : Fin 10 → ℝ} (hj : ∀ e, 0 ≤ j e) {g : BdryData}
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    {chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hS : ContDiffOn ℝ ∞ (lorChartAction j p g chart) U)
    {aLoc aFar : (Fin n → ℝ) → ℂ} (hsU : tsupport aLoc ⊆ U)
    (ha : ContDiff ℝ ∞ aLoc) (hc : HasCompactSupport aLoc)
    (hZ : ∀ x ∈ tsupport aLoc, ∀ e,
      spinAct ((chart x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e) ≠ 0)
    (hZ' : ∀ x ∈ tsupport aLoc, ∀ e,
      spinAct ((chart x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e) ≠ 0)
    (h1 : ∀ x ∈ tsupport aLoc, ∀ e,
      inner ℂ (spinAct ((chart x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e))
        (firstCol (g e 0)) ≠ 0)
    (h2 : ∀ x ∈ tsupport aLoc, ∀ e,
      inner ℂ (jMap (firstCol (g e 1)))
        (spinAct ((chart x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e)) ≠ 0)
    (K : Finset (Fin n → ℝ))
    (hK : ∀ x ∈ tsupport aLoc,
      ((lorChartAction j p g chart x).re = 0 ∧
        fderiv ℝ (lorChartAction j p g chart) x = 0) ↔ x ∈ K)
    (hKs : ∀ x ∈ K, x ∈ tsupport aLoc)
    (hdet : ∀ x ∈ K, (-lorHessian j p g chart x).det ≠ 0)
    (hint : ∀ τ : ℝ, Integrable fun x => aFar x * cexp (τ * lorChartAction j p g chart x))
    (hfar : (fun lam : ℕ => ∫ x, aFar x * cexp ((lam : ℝ) * lorChartAction j p g chart x))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (-((n : ℝ) / 2) - 1)))
    (w : ℕ → ℂ) (m : ℝ) (hw : w =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ m)) :
    (fun lam : ℕ => w lam * (∫ x, (aLoc x + aFar x) *
        cexp ((lam : ℝ) * lorChartAction j p g chart x)) -
      w lam * ∑ x₀ ∈ K, cexp ((lam : ℝ) * lorChartAction j p g chart x₀) *
        ((2 * π / (lam : ℝ)) ^ ((n : ℝ) / 2) : ℝ) *
          invSqrtDet (-lorHessian j p g chart x₀) * aLoc x₀)
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (n : ℝ) / 2 - 1)) :=
  weighted_asymptotics_local hU hS hsU ha hc
    (fun x hx => re_lorAction_le_zero hj (hZ x hx) (hZ' x hx) hξ hξ' (h1 x hx) (h2 x hx))
    K hK hKs hdet hint hfar w m hw

end Lightlike.Asymptotics.Lorentzian
