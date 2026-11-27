import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.OppositeL2
import Lightlike.Lorentz.SL2RPlancherel.KTypeOppositeIso
import Lightlike.Lorentz.SL2RPlancherel.LadderOppositeSurjective

/-!
# The opposite-sign block isometry is the principal-series transform on every test function

For natural `l, s` and a smooth `χ` with compact support in `(0, ∞)`, let `src χ = π √(sinh ξ) χ`
in `L²(0, ∞)` (`srcL`) and `T χ = oppTrans s l χ` (`transL`). This file proves that the
continuous part of `src χ`, mapped by the block isometry `blockL2N`, is `T χ`.

The first step (`transL_eq_of_orth`) is the case `src χ ⊥ φ_i` for every discrete direction: then
`χ` is a ladder image (`exists_hLRN_eq`), so `src χ = blockEN G`, its continuous part is itself,
and `T χ = blockTgt G = blockL2N (blockEN G)` (`oppTrans_HcN`, `blockL2N_apply`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The source function `π √(sinh ξ) χ(ξ)` of a test function. -/
def srcFun (χ : ℝ → ℂ) (ξ : ℝ) : ℂ := ((Real.pi * Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) * χ ξ

theorem memLp_srcFun (F : smoothCS) :
    MemLp (srcFun F) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hcont : Continuous (srcFun F) :=
    (Complex.continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_sqrt.comp Real.continuous_sinh))).mul F.2.1.continuous
  exact hcont.memLp_of_hasCompactSupport F.2.2.mul_left

/-- The source map `χ ↦ π √(sinh ξ) χ` from the test functions of `(0, ∞)` to `L²(0, ∞)`. -/
def srcL : testPos →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) where
  toFun K := (memLp_srcFun K.1).toLp (srcFun K.1)
  map_add' F G := by
    have h : srcFun ((F + G : testPos).1 : ℝ → ℂ) = srcFun F.1 + srcFun G.1 := by
      funext ξ
      simp only [srcFun, Pi.add_apply]
      rw [show ((F + G : testPos).1 : ℝ → ℂ) = (F.1 : ℝ → ℂ) + G.1 from rfl, Pi.add_apply, mul_add]
    rw [← MemLp.toLp_add (memLp_srcFun F.1) (memLp_srcFun G.1)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)
  map_smul' c F := by
    have h : srcFun ((c • F : testPos).1 : ℝ → ℂ) = c • srcFun F.1 := by
      funext ξ
      simp only [srcFun, Pi.smul_apply, smul_eq_mul]
      rw [show ((c • F : testPos).1 : ℝ → ℂ) = c • (F.1 : ℝ → ℂ) from rfl, Pi.smul_apply,
        smul_eq_mul]
      ring
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_srcFun F.1)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)

lemma integrableOn_pairing (s l : ℕ) (ν : ℝ) {χ : ℝ → ℂ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) :
    IntegrableOn (fun x => χ x * (starRingEnd ℂ) (mcoefP ν s l x) * (Real.sinh x : ℂ)) (Ioi 0) :=
  (((hχ.mul (Complex.continuous_conj.comp (continuous_mcoefP ν s l))).mul
    (Complex.continuous_ofReal.comp Real.continuous_sinh)).integrable_of_hasCompactSupport
    (hc.mul_right.mul_right)).integrableOn

lemma oppPairing_add (s l : ℕ) {χ ψ : ℝ → ℂ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (ν : ℝ) :
    oppPairing s l (χ + ψ) ν = oppPairing s l χ ν + oppPairing s l ψ ν := by
  unfold oppPairing
  rw [← integral_add (integrableOn_pairing s l ν hχ hχc) (integrableOn_pairing s l ν hψ hψc)]
  congr 1
  funext x
  simp only [Pi.add_apply]
  ring

lemma oppPairing_smul (s l : ℕ) (c : ℂ) (χ : ℝ → ℂ) (ν : ℝ) :
    oppPairing s l (c • χ) ν = c * oppPairing s l χ ν := by
  unfold oppPairing
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The pairing only sees `χ` on `(0, ∞)`. -/
lemma oppPairing_congr (s l : ℕ) {χ ψ : ℝ → ℂ} (h : ∀ x, 0 < x → χ x = ψ x) (ν : ℝ) :
    oppPairing s l χ ν = oppPairing s l ψ ν := by
  unfold oppPairing
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [h x hx]

/-- The transform `χ ↦ T χ` from the test functions of `(0, ∞)` to `L²(0, ∞)`. -/
def transL (s l : ℕ) : testPos →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) where
  toFun K := (memLp_oppTrans s l K.1.2.1 K.1.2.2 K.2).toLp (oppTrans s l K.1)
  map_add' F G := by
    have h : oppTrans s l ((F + G : testPos).1 : ℝ → ℂ) = oppTrans s l F.1 + oppTrans s l G.1 := by
      funext ρ
      rw [show ((F + G : testPos).1 : ℝ → ℂ) = (F.1 : ℝ → ℂ) + G.1 from rfl, Pi.add_apply,
        oppTrans, oppTrans, oppTrans, oppPairing_add s l F.1.2.1.continuous F.1.2.2
          G.1.2.1.continuous G.1.2.2]
      ring
    rw [← MemLp.toLp_add (memLp_oppTrans s l F.1.2.1 F.1.2.2 F.2)
      (memLp_oppTrans s l G.1.2.1 G.1.2.2 G.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)
  map_smul' c F := by
    have h : oppTrans s l ((c • F : testPos).1 : ℝ → ℂ) = c • oppTrans s l F.1 := by
      funext ρ
      rw [show ((c • F : testPos).1 : ℝ → ℂ) = c • (F.1 : ℝ → ℂ) from rfl, Pi.smul_apply,
        smul_eq_mul, oppTrans, oppTrans, oppPairing_smul]
      ring
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_oppTrans s l F.1.2.1 F.1.2.2 F.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)

/-- `⟪φ_i, src χ⟫ = π ∫_{(0,∞)} χ φ_i sinh`. -/
theorem inner_phiVec_srcL (s l : ℕ) (i : DiscIdx s l) (K : testPos) :
    inner ℂ (phiVec s l i) (srcL K) = ((Real.pi : ℝ) : ℂ) *
      ∫ ξ in Ioi (0 : ℝ), (K.1 : ℝ → ℂ) ξ * ((phiN s l i.1 ξ : ℝ) : ℂ) * (Real.sinh ξ : ℂ) := by
  rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
  have h1 : (phiVec s l i : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] phiSrc s l i.1 :=
    MemLp.coeFn_toLp (memLp_phiSrc s l i.1 i.2 i.1.2)
  have h2 : (srcL K : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] srcFun K.1 :=
    MemLp.coeFn_toLp (memLp_srcFun K.1)
  refine integral_congr_ae ?_
  filter_upwards [h1, h2, ae_restrict_mem measurableSet_Ioi] with ξ e1 e2 hξ
  rw [e1, e2, phiSrc, srcFun, RCLike.inner_apply', Complex.conj_ofReal]
  have hs : 0 ≤ Real.sinh ξ := (Real.sinh_pos_iff.2 hξ).le
  have hr : Real.sqrt (Real.sinh ξ) * phiN s l i.1 ξ * (Real.pi * Real.sqrt (Real.sinh ξ)) =
      Real.pi * phiN s l i.1 ξ * Real.sinh ξ := by
    have := Real.mul_self_sqrt hs
    linear_combination (Real.pi * phiN s l i.1 ξ) * this
  calc (((Real.sqrt (Real.sinh ξ) * phiN s l i.1 ξ : ℝ)) : ℂ) *
        (((Real.pi * Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) * (K.1 : ℝ → ℂ) ξ)
      = ((Real.sqrt (Real.sinh ξ) * phiN s l i.1 ξ * (Real.pi * Real.sqrt (Real.sinh ξ)) : ℝ) : ℂ) *
        (K.1 : ℝ → ℂ) ξ := by push_cast; ring
    _ = _ := by rw [hr]; push_cast; ring

/-- **On test functions orthogonal to the discrete directions**, the block isometry of the continuous
part is the principal-series transform: `blockL2N (P_cont (src χ)) = T χ`. -/
theorem transL_eq_of_orth (s l : ℕ) (K : testPos)
    (hK : ∀ i, inner ℂ (phiVec s l i) (srcL K) = 0) :
    transL s l K = blockL2N s l ((contPartN s l).orthogonalProjectionOnto (srcL K)) := by
  have hmom : ∀ i : ℕ, l ≤ i + s → i < l →
      ∫ ξ in Ioi (0 : ℝ), (K.1 : ℝ → ℂ) ξ * ((phiN s l i ξ : ℝ) : ℂ) * (Real.sinh ξ : ℂ) = 0 := by
    intro i hli hil
    have h := hK ⟨⟨i, hil⟩, hli⟩
    rw [inner_phiVec_srcL] at h
    exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast Real.pi_ne_zero)
  obtain ⟨G, hG, hGc, hGeq⟩ := exists_hLRN_eq s l K.1.2.1 K.1.2.2 K.2 hmom
  set G' : smoothCS := ⟨G, hG, hGc⟩ with hG'
  have hHcN : ∀ ξ, 0 < ξ → HcN s G l ξ = (K.1 : ℝ → ℂ) ξ := fun ξ hξ => by
    rw [HcN_eq_hLRN s hG l hξ, hGeq ξ hξ]
  have hsrc : srcL K = blockEN s l G' := by
    refine MemLp.toLp_congr (memLp_srcFun K.1) (memLp_blockSrcN s l hG hGc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    show srcFun K.1 ξ = blockSrcN s l G ξ
    rw [srcFun, blockSrcN, hHcN ξ hξ]
  have hmem : srcL K = (blockENc s l G' : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) := hsrc
  have hproj : (contPartN s l).orthogonalProjectionOnto (srcL K) = blockENc s l G' := by
    rw [hmem, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [hproj, blockL2N_apply]
  refine MemLp.toLp_congr (memLp_oppTrans s l K.1.2.1 K.1.2.2 K.2) (memLp_blockTgt s l hG hGc)
    (Filter.EventuallyEq.of_eq (funext fun ρ => ?_))
  show oppTrans s l K.1 ρ = blockTgt s l G ρ
  rw [← oppTrans_HcN s l hG hGc ρ]
  unfold oppTrans
  rw [oppPairing_congr s l (fun ξ hξ => (hHcN ξ hξ).symm)]

end Lightlike.Lorentz.SL2RPlancherel
