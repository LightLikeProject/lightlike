import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PlancherelEvenSum

/-!
# The even `K`-types of `L²(SL(2,ℝ))`: continuous plus discrete

For a smooth compactly supported `f` on `SL(2,ℝ)`, summing the Plancherel identities of the even
`K`-types (`norm_sq_kkL2_even`) gives (`tsum_norm_sq_kkL2_even`)
`(2π)² ∑_{a,b} ‖kkL2 f (2a, 2b)‖² = (2π)² ∑_{a,b} contEven f a b + ∑_ν ‖P_{D̄_{2ν+2}} f‖² + ∑_ν ‖P_{D_{2ν+2}} f‖²`:
the discrete parts of the opposite-sign blocks `a, b ≥ 1` add up to the antiholomorphic series
(`tsum_norm_sq_discreteBar_even`) and those of `a, b ≤ -1`, by conjugation
(`norm_projection_discSpan_kkL2_neg`), to the holomorphic series (`tsum_norm_sq_discrete_even`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped Real ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The `K × K` components are square summable. -/
lemma summable_norm_sq_kkL2 (F : Lp ℂ 2 haarR) : Summable fun m => ‖kkL2 F m‖ ^ 2 := by
  have h := (lp.memℓp (kkIso F)).summable (p := 2) (by norm_num)
  refine (h.mul_left (((2 * π) ^ 2)⁻¹)).congr fun m => ?_
  show ((2 * π) ^ 2)⁻¹ * ‖(kkIso F : ∀ _ : Fin 2 → ℤ, L2Ioi) m‖ ^ (2 : ENNReal).toReal =
    ‖(((2 * π : ℝ) : ℂ))⁻¹ • (kkIso F : ∀ _ : Fin 2 → ℤ, L2Ioi) m‖ ^ 2
  rw [ENNReal.toReal_ofNat, Real.rpow_two, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  ring

/-- The even `K`-types. -/
def evenIdx (p : ℤ × ℤ) : Fin 2 → ℤ := ![2 * p.1, 2 * p.2]

lemma evenIdx_injective : Function.Injective evenIdx := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [evenIdx, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact Prod.ext (by omega) (by omega)

lemma contEven_nonneg (f : SL2R → ℂ) (a b : ℤ) : 0 ≤ contEven f a b := by
  refine setIntegral_nonneg measurableSet_Ioi fun ρ hρ => ?_
  have hρ0 : (0 : ℝ) < ρ := hρ
  have := tanh_nonneg_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi * ρ)
  positivity

lemma discEven_nonneg (F : Lp ℂ 2 haarR) (a b : ℤ) : 0 ≤ discEven F a b := by
  unfold discEven
  split_ifs <;> positivity

lemma discSpan_eq_bot_of_zero {s l : ℕ} (h : s = 0 ∨ l = 0) : discSpan s l = ⊥ := by
  have he : IsEmpty (DiscIdx s l) := ⟨fun i => by have := i.1.2; have := i.2; omega⟩
  rw [discSpan, Set.range_eq_empty, Submodule.span_empty]

lemma norm_projection_discSpan_of_zero {s l : ℕ} (h : s = 0 ∨ l = 0) (v : L2Ioi) :
    ‖(discSpan s l).orthogonalProjectionOnto v‖ = 0 := by
  have hmem : ((discSpan s l).orthogonalProjectionOnto v : L2Ioi) ∈ discSpan s l :=
    ((discSpan s l).orthogonalProjectionOnto v).2
  have h0 := (Submodule.mem_bot ℂ).1 ((discSpan_eq_bot_of_zero h).le hmem)
  rw [← Submodule.norm_coe, h0, norm_zero]

lemma norm_projection_discSpan_congr {s s' l l' : ℕ} (hs : s = s') (hl : l = l') (v : L2Ioi) :
    ‖(discSpan s l).orthogonalProjectionOnto v‖ = ‖(discSpan s' l').orthogonalProjectionOnto v‖ := by
  subst hs hl; rfl

/-- **The even `K`-types: continuous plus discrete.** -/
theorem tsum_norm_sq_kkL2_even {f : SL2R → ℂ} {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hfF : ∀ g : SL2R, f g = F fun i j => g i j)
    (hc : HasCompactSupport f) (hf : MemLp f 2 haarR) :
    (2 * π) ^ 2 * ∑' p : ℤ × ℤ, ‖kkL2 (hf.toLp f) (evenIdx p)‖ ^ 2 =
      (2 * π) ^ 2 * ∑' p : ℤ × ℤ, contEven f p.1 p.2 +
        (∑' ν : ℕ, ‖(discreteSpaceBar (show 2 ≤ 2 * (ν + 1) by omega)).starProjection
            (hf.toLp f)‖ ^ 2 +
          ∑' ν : ℕ, ‖(discreteSpace (show 2 ≤ 2 * (ν + 1) by omega)).starProjection
            (hf.toLp f)‖ ^ 2) := by
  have hfc : Continuous f := continuous_of_entries hF.continuous hfF
  set Fl := hf.toLp f with hFl
  have hS : Summable fun p : ℤ × ℤ => ‖kkL2 Fl (evenIdx p)‖ ^ 2 :=
    (summable_norm_sq_kkL2 Fl).comp_injective evenIdx_injective
  have he : ∀ p : ℤ × ℤ, ‖kkL2 Fl (evenIdx p)‖ ^ 2 = contEven f p.1 p.2 + discEven Fl p.1 p.2 :=
    fun p => norm_sq_kkL2_even hF hfF hc hf p.1 p.2
  have hSc : Summable fun p : ℤ × ℤ => contEven f p.1 p.2 :=
    hS.of_nonneg_of_le (fun p => contEven_nonneg f _ _)
      (fun p => by rw [he]; linarith [discEven_nonneg Fl p.1 p.2])
  have hSd : Summable fun p : ℤ × ℤ => discEven Fl p.1 p.2 :=
    hS.of_nonneg_of_le (fun p => discEven_nonneg Fl _ _)
      (fun p => by rw [he]; linarith [contEven_nonneg f p.1 p.2])
  -- the discrete parts, split into the two quadrants
  set dP : ℕ × ℕ → ℝ := fun q =>
    ‖(discSpan q.1 q.2).starProjection (kkL2 Fl ![(2 * q.1 : ℤ), (2 * q.2 : ℤ)])‖ ^ 2 with hdP
  set dM : ℕ × ℕ → ℝ := fun q =>
    ‖(discSpan q.1 q.2).starProjection (kkL2 (star Fl) ![(2 * q.1 : ℤ), (2 * q.2 : ℤ)])‖ ^ 2
    with hdM
  have hsp : ∀ (s l : ℕ) (v : L2Ioi), ‖(discSpan s l).starProjection v‖ =
      ‖(discSpan s l).orthogonalProjectionOnto v‖ := fun s l v => by
    rw [Submodule.starProjection_apply, Submodule.norm_coe]
  set eP : ℤ × ℤ → ℝ := fun p => if 1 ≤ p.1 ∧ 1 ≤ p.2 then discEven Fl p.1 p.2 else 0 with heP
  set eM : ℤ × ℤ → ℝ := fun p => if p.1 ≤ -1 ∧ p.2 ≤ -1 then discEven Fl p.1 p.2 else 0 with heM
  have hsplit : ∀ p : ℤ × ℤ, discEven Fl p.1 p.2 = eP p + eM p := fun p => by
    by_cases h1 : 1 ≤ p.1 ∧ 1 ≤ p.2
    · have h2 : ¬ (p.1 ≤ -1 ∧ p.2 ≤ -1) := by omega
      simp only [heP, heM, h1, h2, and_self, ↓reduceIte, add_zero]
    · by_cases h2 : p.1 ≤ -1 ∧ p.2 ≤ -1
      · simp only [heP, heM, h1, h2, and_self, ↓reduceIte, zero_add]
      · simp only [heP, heM, h1, h2, ↓reduceIte, add_zero, discEven]
  set ιP : ℕ × ℕ → ℤ × ℤ := fun q => ((q.1 : ℤ), (q.2 : ℤ)) with hιP
  set ιM : ℕ × ℕ → ℤ × ℤ := fun q => (-(q.1 : ℤ), -(q.2 : ℤ)) with hιM
  have hιP_inj : Function.Injective ιP := fun q q' h => by
    simp only [hιP, Prod.mk.injEq, Nat.cast_inj] at h; exact Prod.ext h.1 h.2
  have hιM_inj : Function.Injective ιM := fun q q' h => by
    simp only [hιM, Prod.mk.injEq, neg_inj, Nat.cast_inj] at h; exact Prod.ext h.1 h.2
  have hPq : ∀ q, eP (ιP q) = dP q := fun q => by
    simp only [heP, hιP, hdP]
    by_cases h : 1 ≤ (q.1 : ℤ) ∧ 1 ≤ (q.2 : ℤ)
    · simp only [h, and_self, ↓reduceIte]
      simp only [discEven, h, and_self, ↓reduceIte, Int.toNat_natCast]
      rw [hsp]
    · simp only [h, ↓reduceIte]; rw [hsp, norm_projection_discSpan_of_zero (by omega), zero_pow two_ne_zero]
  have hMq : ∀ q, eM (ιM q) = dM q := fun q => by
    simp only [heM, hιM, hdM]
    by_cases h : -(q.1 : ℤ) ≤ -1 ∧ -(q.2 : ℤ) ≤ -1
    · simp only [h, and_self, ↓reduceIte]
      have h' : ¬ (1 ≤ -(q.1 : ℤ) ∧ 1 ≤ -(q.2 : ℤ)) := by omega
      simp only [discEven, h, h', and_self, ↓reduceIte]
      have hn := norm_projection_discSpan_kkL2_neg hfc hf q.1 q.2
      rw [← hFl] at hn
      rw [hsp, ← hn, norm_projection_discSpan_congr (s' := q.1) (l' := q.2) (by simp) (by simp)]
    · simp only [h, ↓reduceIte]; rw [hsp, norm_projection_discSpan_of_zero (by omega), zero_pow two_ne_zero]
  have hsuppP : Function.support eP ⊆ Set.range ιP := fun p hp => by
    simp only [Function.mem_support, heP] at hp
    split_ifs at hp with h
    · exact ⟨(p.1.toNat, p.2.toNat), Prod.ext (by simp [hιP]; omega) (by simp [hιP]; omega)⟩
    · exact absurd rfl hp
  have hsuppM : Function.support eM ⊆ Set.range ιM := fun p hp => by
    simp only [Function.mem_support, heM] at hp
    split_ifs at hp with h
    · exact ⟨((-p.1).toNat, (-p.2).toNat), Prod.ext (by simp [hιM]; omega) (by simp [hιM]; omega)⟩
    · exact absurd rfl hp
  have hSP : Summable eP := hSd.of_nonneg_of_le
    (fun p => by simp only [heP]; split_ifs <;> simp [discEven_nonneg])
    (fun p => by rw [hsplit p]; have : 0 ≤ eM p := by simp only [heM]; split_ifs <;> simp [discEven_nonneg]
                 linarith)
  have hSM : Summable eM := hSd.of_nonneg_of_le
    (fun p => by simp only [heM]; split_ifs <;> simp [discEven_nonneg])
    (fun p => by rw [hsplit p]; have : 0 ≤ eP p := by simp only [heP]; split_ifs <;> simp [discEven_nonneg]
                 linarith)
  have hdisc : ∑' p : ℤ × ℤ, discEven Fl p.1 p.2 = ∑' q, dP q + ∑' q, dM q := by
    rw [tsum_congr hsplit, hSP.tsum_add hSM, ← hιP_inj.tsum_eq hsuppP, ← hιM_inj.tsum_eq hsuppM,
      tsum_congr hPq, tsum_congr hMq]
  rw [tsum_congr he, hSc.tsum_add hSd, mul_add, hdisc, mul_add, tsum_norm_sq_discreteBar_even Fl,
    tsum_norm_sq_discrete_even Fl]

end Lightlike.Lorentz.SL2RPlancherel
