import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PlancherelEvenBlocks
import Lightlike.Lorentz.SL2RPlancherel.DiscreteBlock

/-!
# Conjugation and the discrete parts of the opposite-sign blocks

Complex conjugation `F ↦ star F` on `L²(SL(2,ℝ))` reverses the `K`-types:
`kkL2 (star F) (-m) = star (kkL2 F m)` for continuous `F` (`kkL2_star_toLp`), and the discrete part
of an opposite-sign block commutes with conjugation, its directions being real
(`starProjection_discSpan_star`). Hence the discrete part of the component `(-2s, -2l)` of `F` has the
norm of the discrete part of the component `(2s, 2l)` of `star F`
(`norm_projection_discSpan_kkL2_neg`), the form in which the holomorphic discrete series enter
`tsum_norm_sq_discrete_even`.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped Real ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

section StarLp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma star_add_Lp2 (a b : Lp ℂ 2 μ) : star (a + b) = star a + star b := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (a + b), Lp.coeFn_add (star a) (star b), Lp.coeFn_star a,
    Lp.coeFn_star b, Lp.coeFn_add a b] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, Pi.star_apply, Pi.star_apply, Pi.star_apply, h5, Pi.add_apply,
    star_add]

lemma star_smul_Lp2 (c : ℂ) (a : Lp ℂ 2 μ) : star (c • a) = (starRingEnd ℂ c) • star a := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (c • a), Lp.coeFn_smul (starRingEnd ℂ c) (star a), Lp.coeFn_star a,
    Lp.coeFn_smul c a] with x h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, Pi.star_apply, Pi.star_apply, h4, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, star_mul', RCLike.star_def]

lemma star_zero_Lp2 : star (0 : Lp ℂ 2 μ) = 0 := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (0 : Lp ℂ 2 μ), Lp.coeFn_zero ℂ 2 μ] with x h1 h2
  rw [h1, Pi.star_apply, h2, Pi.zero_apply, star_zero]

lemma star_sub_Lp2 (a b : Lp ℂ 2 μ) : star (a - b) = star a - star b := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (a - b), Lp.coeFn_sub (star a) (star b), Lp.coeFn_star a,
    Lp.coeFn_star b, Lp.coeFn_sub a b] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, h3, h4, Pi.star_apply, Pi.star_apply, Pi.star_apply, h5, Pi.sub_apply,
    star_sub]

lemma norm_star_Lp2 (a : Lp ℂ 2 μ) : ‖star a‖ = ‖a‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star a), eLpNorm_star]

end StarLp

lemma star_phiVec (s l : ℕ) (i : DiscIdx s l) : star (phiVec s l i) = phiVec s l i := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (phiVec s l i),
    MemLp.coeFn_toLp (memLp_phiSrc s l i.1 i.2 i.1.2)] with x h1 h2
  rw [h1, Pi.star_apply, show (phiVec s l i : ℝ → ℂ) x = phiSrc s l i.1 x from h2, phiSrc,
    RCLike.star_def, Complex.conj_ofReal]

lemma star_mem_discSpan (s l : ℕ) {v : L2Ioi} (hv : v ∈ discSpan s l) : star v ∈ discSpan s l := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [star_phiVec]
    exact Submodule.subset_span (Set.mem_range_self i)
  | zero => rw [star_zero_Lp2]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [star_add_Lp2]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [star_smul_Lp2]; exact Submodule.smul_mem _ _ hx

/-- **The discrete part commutes with conjugation.** -/
theorem starProjection_discSpan_star (s l : ℕ) (H : L2Ioi) :
    (discSpan s l).starProjection (star H) = star ((discSpan s l).starProjection H) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (star_mem_discSpan s l ((discSpan s l).starProjection_apply_mem H)) fun w hw => ?_
  have hw' : star w ∈ discSpan s l := star_mem_discSpan s l hw
  have horth := Submodule.sub_starProjection_mem_orthogonal (K := discSpan s l) H
  have h0 : inner ℂ (H - (discSpan s l).starProjection H) (star w) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hw' horth
  have hww : star (star w) = w := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_star (star w), Lp.coeFn_star w] with x h1 h2
    rw [h1, Pi.star_apply, h2, Pi.star_apply, star_star]
  rw [← star_sub_Lp2, ← hww, inner_star_star, h0, map_zero]

lemma norm_projection_discSpan_star (s l : ℕ) (H : L2Ioi) :
    ‖(discSpan s l).orthogonalProjectionOnto (star H)‖ =
      ‖(discSpan s l).orthogonalProjectionOnto H‖ := by
  have e : ∀ v : L2Ioi, ‖(discSpan s l).orthogonalProjectionOnto v‖ =
      ‖(discSpan s l).starProjection v‖ := fun v => by
    rw [Submodule.starProjection_apply, Submodule.norm_coe]
  rw [e, e, starProjection_discSpan_star, norm_star_Lp2]

/-- **Conjugation reverses the `K`-types**: `kkL2 (star F) (-m) = star (kkL2 F m)` for continuous
`F`. -/
theorem kkL2_star_toLp {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR) (m : Fin 2 → ℤ) :
    kkL2 (star (hf.toLp f)) (-m) = star (kkL2 (hf.toLp f) m) := by
  have hs : star (hf.toLp f) = hf.star.toLp (star f) := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_star (hf.toLp f), hf.coeFn_toLp, hf.star.coeFn_toLp] with x h1 h2 h3
    rw [h1, h3, Pi.star_apply, Pi.star_apply, h2]
  have hsc : Continuous (star f) := hfc.star
  rw [hs]
  refine Lp.ext ?_
  filter_upwards [kkL2_toLp_ae hsc hf.star (-m), Lp.coeFn_star (kkL2 (hf.toLp f) m),
    kkL2_toLp_ae hfc hf m] with ξ h1 h2 h3
  rw [h1, h2, Pi.star_apply, h3, kkSrc, kkSrc]
  have e : (star f : SL2R → ℂ) = fun g => (starRingEnd ℂ) (f g) := by
    funext g; rw [Pi.star_apply, RCLike.star_def]
  rw [e, kkCoeff_conj, star_mul', RCLike.star_def, Complex.conj_ofReal]

/-- The discrete part of the component `(-2s, -2l)` of `F` has the norm of the discrete part of the
component `(2s, 2l)` of `star F`. -/
theorem norm_projection_discSpan_kkL2_neg {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR)
    (s l : ℕ) :
    ‖(discSpan s l).orthogonalProjectionOnto (kkL2 (hf.toLp f) ![2 * -(s : ℤ), 2 * -(l : ℤ)])‖ =
      ‖(discSpan s l).orthogonalProjectionOnto
        (kkL2 (star (hf.toLp f)) ![(2 * s : ℤ), (2 * l : ℤ)])‖ := by
  have hm : (![(2 * s : ℤ), (2 * l : ℤ)] : Fin 2 → ℤ) = -![2 * -(s : ℤ), 2 * -(l : ℤ)] := by
    ext i; fin_cases i <;> simp
  rw [hm, kkL2_star_toLp hfc hf, norm_projection_discSpan_star]

end Lightlike.Lorentz.SL2RPlancherel
