import Mathlib

/-!
# Smooth extension of a function smooth on an open set

For a finite-dimensional real normed space `E`, a real function smooth on an open `U ⊆ E` agrees near any compact
`K ⊆ U` with a function smooth on all of `E` (`exists_contDiff_eqOn_nhds`): multiply by a smooth function that is `1`
near `K` and vanishes outside a closed thickening of `K` contained in `U`
(`exists_contDiff_zero_iff_one_iff_of_isClosed`).

This is the real-valued form, on any finite-dimensional space (for instance a product `P × ℝⁿ` of a parameter space
and normal coordinates), of `Lightlike.Asymptotics.Lorentzian.exists_smooth_extension` (complex values on `ℝⁿ`),
with the same proof. It turns a function defined only near the diagonal, such as the transport coefficient in normal
coordinates, into the globally smooth input of `Lightlike.eulerPrimitive`.
-/

open Set Metric Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Smooth extension**: a function smooth on an open `U` agrees on a neighbourhood of a compact `K ⊆ U` with a
function smooth on the whole space. -/
theorem exists_contDiff_eqOn_nhds {f : E → ℝ} {U K : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ ∀ x ∈ W, F x = f x := by
  obtain ⟨δ, hδ, hcU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hd : Disjoint (thickening (δ / 2) K)ᶜ (cthickening (δ / 4) K) := by
    rw [Set.disjoint_compl_left_iff_subset]
    exact cthickening_subset_thickening' (by linarith) (by linarith) K
  obtain ⟨χ, hχ, -, hχ0, hχ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (isOpen_thickening.isClosed_compl) isClosed_cthickening hd
  have hsupp : tsupport χ ⊆ U := by
    have h1 : Function.support χ ⊆ thickening (δ / 2) K := by
      intro x hx
      by_contra hxs
      exact hx ((hχ0 x).1 hxs)
    have h2 : tsupport χ ⊆ cthickening (δ / 2) K :=
      closure_minimal (h1.trans (thickening_subset_cthickening _ _)) isClosed_cthickening
    exact h2.trans ((cthickening_mono (by linarith) K).trans hcU)
  refine ⟨fun x => χ x * f x, ?_, thickening (δ / 4) K, isOpen_thickening,
    self_subset_thickening (by linarith) K, fun x hx => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hχ.of_le (by exact_mod_cast le_top)).contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
    · have hz : ∀ᶠ y in 𝓝 x, χ y = 0 :=
        notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hsupp h)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hz] with y hy
      simp [hy]
  · have : χ x = 1 := (hχ1 x).1 (thickening_subset_cthickening _ _ hx)
    simp [this]

end Lightlike
