import Mathlib
import Lightlike.Dirac.SphereSpectrumCount
import Lightlike.Dirac.SphereTransition

/-!
# The Dirac spectrum of the unit 2-sphere

A smooth spinor field of the round unit 2-sphere is a smooth spinor `f : ℝ² → V` in the stereographic chart of the
north pole whose transfer `f_S (ι y) = T(y) f(y)` to the chart of the south pole (`ι y = y/‖y‖²`, `T(y) = ‖y‖⁻¹ ρ(y) J`
the Pin lift of the frame change, see `Lightlike/Dirac/SphereTransition.lean`) extends to a smooth spinor `f_S` on
the whole plane.  `SphereEigenspace ρ λ` is the real vector space of such fields with `D f = λ f`.

**Theorem** (`sphere_spectrum`).  For a `Cl₂`-module `V` of real dimension `4` (the spinor module `ℂ² ≅ ℍ`):

* `SphereEigenspace ρ λ ≠ ⊥` if and only if `λ = ±(k+1)` for a natural number `k`;
* `SphereEigenspace ρ (±(k+1))` has real dimension `4(k+1)`, i.e. complex multiplicity `2(k+1)`.

The upper bound is `chartEigen_finrank_le` (Fourier modes and the mode ODE of the chart, for bounded `C¹` spinors; a
smooth field is bounded since `f_S` is continuous at `0`, `SphereEigenspace_le_ChartEigen`); the lower bound is
`sphere_dirac_lower_bound` together with the explicit smooth transfer of its modes (`modeFnS_inv2`).
-/

namespace Lightlike.Dirac

open CliffordAlgebra Polynomial
open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma sphereT_add (ρ : CliffordRep 2 V) (y : E 2) (a b : V) :
    sphereT ρ y (a + b) = sphereT ρ y a + sphereT ρ y b := by
  simp only [sphereT, map_add, cliffV_add, smul_add]

lemma sphereT_zero (ρ : CliffordRep 2 V) (y : E 2) : sphereT ρ y 0 = 0 := by
  simp [sphereT, cliffV]

lemma cliffV_smul (ρ : CliffordRep 2 V) (y : E 2) (a : ℝ) (x : V) :
    cliffV ρ y (a • x) = a • cliffV ρ y x := by
  simp only [cliffV, map_smul, smul_add, smul_comm a]

/-- `J γ₁ = -γ₁ J`. -/
lemma Jop_gam1 (ρ : CliffordRep 2 V) (x : V) : Jop ρ (gam ρ 1 x) = -gam ρ 1 (Jop ρ x) := by
  simp only [Jop_apply]
  rw [gam_sq ρ 1, gam10 ρ (gam ρ 1 x), gam_sq ρ 1]
  simp

lemma Jop_cliffV (ρ : CliffordRep 2 V) (y : E 2) (x : V) :
    Jop ρ (cliffV ρ y x) = -cliffV ρ y (Jop ρ x) := by
  simp only [cliffV, map_add, map_smul, Jop_gam0, Jop_gam1, smul_neg, neg_add]

/-- `ρ(y)² = -‖y‖²`. -/
lemma cliffV_cliffV (ρ : CliffordRep 2 V) (y : E 2) (x : V) :
    cliffV ρ y (cliffV ρ y x) = -(‖y‖ ^ 2) • x := by
  simp only [cliffV, map_add, map_smul, gam_sq ρ 0, gam_sq ρ 1, gam10, smul_neg]
  rw [norm_sq_E2]
  module

/-- `T(y)² = -1`: the transfer back is `-T(y)`. -/
lemma sphereT_sq (ρ : CliffordRep 2 V) {y : E 2} (hy : y ≠ 0) (x : V) :
    sphereT ρ y (sphereT ρ y x) = -x := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have h1 : Jop ρ (cliffV ρ y (Jop ρ x)) = cliffV ρ y x := by
    rw [Jop_cliffV, Jop_sq, cliffV_neg, neg_neg]
  unfold sphereT
  rw [map_smul, cliffV_smul, h1, smul_smul, cliffV_cliffV, smul_smul]
  field_simp
  simp

/-- A bound for the transfer: `‖T(y) x‖ ≤ M ‖x‖` for `y ≠ 0`. -/
lemma sphereT_bound (ρ : CliffordRep 2 V) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : E 2, y ≠ 0 → ∀ x : V, ‖sphereT ρ y x‖ ≤ M * ‖x‖ := by
  refine ⟨‖(gam ρ 0).comp (Jop ρ)‖ + ‖(gam ρ 1).comp (Jop ρ)‖, by positivity, fun y hy x => ?_⟩
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h0 : ‖y 0‖ ≤ ‖y‖ := PiLp.norm_apply_le y 0
  have h1 : ‖y 1‖ ≤ ‖y‖ := PiLp.norm_apply_le y 1
  have ha : ‖gam ρ 0 (Jop ρ x)‖ ≤ ‖(gam ρ 0).comp (Jop ρ)‖ * ‖x‖ :=
    ((gam ρ 0).comp (Jop ρ)).le_opNorm x
  have hb : ‖gam ρ 1 (Jop ρ x)‖ ≤ ‖(gam ρ 1).comp (Jop ρ)‖ * ‖x‖ :=
    ((gam ρ 1).comp (Jop ρ)).le_opNorm x
  have hsum : ‖y 0 • gam ρ 0 (Jop ρ x) + y 1 • gam ρ 1 (Jop ρ x)‖ ≤
      ‖y‖ * (‖(gam ρ 0).comp (Jop ρ)‖ * ‖x‖) + ‖y‖ * (‖(gam ρ 1).comp (Jop ρ)‖ * ‖x‖) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul]; exact mul_le_mul h0 ha (norm_nonneg _) (norm_nonneg _)
    · rw [norm_smul]; exact mul_le_mul h1 hb (norm_nonneg _) (norm_nonneg _)
  unfold sphereT cliffV
  rw [norm_smul, norm_inv, norm_norm]
  calc ‖y‖⁻¹ * ‖y 0 • gam ρ 0 (Jop ρ x) + y 1 • gam ρ 1 (Jop ρ x)‖
      ≤ ‖y‖⁻¹ * (‖y‖ * (‖(gam ρ 0).comp (Jop ρ)‖ * ‖x‖) + ‖y‖ * (‖(gam ρ 1).comp (Jop ρ)‖ * ‖x‖)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = (‖(gam ρ 0).comp (Jop ρ)‖ + ‖(gam ρ 1).comp (Jop ρ)‖) * ‖x‖ := by field_simp

/-- **The smooth spinor fields of the unit 2-sphere with `D f = λ f`.** -/
noncomputable def SphereEigenspace (ρ : CliffordRep 2 V) (lam : ℝ) : Submodule ℝ (E 2 → V) where
  carrier := {f | ContDiff ℝ ∞ f ∧ (∀ x, diracF ρ stereoF stereoOmega f x = lam • f x) ∧
    ∃ fS : E 2 → V, ContDiff ℝ ∞ fS ∧ ∀ y : E 2, y ≠ 0 → fS (inv2 y) = sphereT ρ y (f y)}
  add_mem' := by
    rintro f g ⟨hf, hfe, fS, hfS, hfg⟩ ⟨hg, hge, gS, hgS, hgg⟩
    refine ⟨hf.add hg, fun x => ?_, fS + gS, hfS.add hgS, fun y hy => ?_⟩
    · rw [diracF_add ρ (hf.differentiable (by simp) x) (hg.differentiable (by simp) x), hfe, hge,
        Pi.add_apply, smul_add]
    · simp only [Pi.add_apply, hfg y hy, hgg y hy, sphereT_add]
  zero_mem' := by
    refine ⟨contDiff_const, fun x => ?_, 0, contDiff_const, fun y hy => ?_⟩
    · simp [diracF_zero]
    · simp [sphereT_zero]
  smul_mem' := by
    rintro a f ⟨hf, hfe, fS, hfS, hfg⟩
    refine ⟨hf.const_smul a, fun x => ?_, a • fS, hfS.const_smul a, fun y hy => ?_⟩
    · rw [diracF_smul ρ a (hf.differentiable (by simp) x), hfe, Pi.smul_apply, smul_comm]
    · simp only [Pi.smul_apply, hfg y hy, sphereT_smul]

/-- A smooth spinor field of the sphere is a bounded `C¹` chart spinor: the norm is bounded near infinity because
`f_S` is continuous at `0` and `T(y)² = -1`. -/
lemma sphereEigenspace_le_chartEigen (ρ : CliffordRep 2 V) (lam : ℝ) :
    SphereEigenspace ρ lam ≤ ChartEigen ρ lam := by
  rintro f ⟨hf, hfe, fS, hfS, hfg⟩
  refine ⟨hf.of_le (by simp), ?_, hfe⟩
  obtain ⟨M, hM0, hM⟩ := sphereT_bound ρ
  obtain ⟨B₁, hB₁⟩ := (isCompact_closedBall (0 : E 2) 1).exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨B₂, hB₂⟩ := (isCompact_closedBall (0 : E 2) 1).exists_bound_of_continuousOn hfS.continuous.continuousOn
  refine ⟨max B₁ (M * B₂), fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ 1
  · exact (hB₁ x (by simpa using hx)).trans (le_max_left _ _)
  · have hx1 : 1 < ‖x‖ := not_le.mp hx
    have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx1
    have hι : ‖inv2 x‖ ≤ 1 := by rw [norm_inv2 hx0]; exact inv_le_one_of_one_le₀ hx1.le
    have h1 : f x = -sphereT ρ x (fS (inv2 x)) := by
      rw [hfg x hx0, sphereT_sq ρ hx0, neg_neg]
    rw [h1, norm_neg]
    exact ((hM x hx0 _).trans (mul_le_mul_of_nonneg_left (hB₂ _ (by simpa using hι)) hM0)).trans
      (le_max_right _ _)

/-! ### The explicit modes are smooth sections -/

lemma contDiff_stereoH_rpow_inf :
    ContDiff ℝ ∞ (fun y : E 2 => stereoH y ^ ((((2 : ℕ) : ℝ) - 1) / 2)) := by
  have h : ContDiff ℝ ∞ (stereoH : E 2 → ℝ) := by
    unfold stereoH
    exact (contDiff_const.add (contDiff_norm_sq ℝ)).div_const 2
  exact h.rpow_const_of_ne (fun x => (stereoH_pos x).ne')

lemma contDiff_angProfile (s m : ℕ) (P : ℝ[X]) :
    ContDiff ℝ ∞ (angProfile (fun u => ((1 + u) ^ s)⁻¹ * P.eval u) m) := by
  unfold angProfile
  have h1 : ContDiff ℝ ∞ fun y : E 2 => ‖y‖ ^ 2 := contDiff_norm_sq ℝ
  have h2 : ContDiff ℝ ∞ fun y : E 2 => ((1 + ‖y‖ ^ 2) ^ s)⁻¹ * P.eval (‖y‖ ^ 2) := by
    refine ContDiff.mul (ContDiff.inv ((contDiff_const.add h1).pow s) (fun y => by positivity)) ?_
    have hP : ContDiff ℝ ∞ fun x : ℝ => P.eval x := by
      simpa [Polynomial.aeval_def, Polynomial.eval₂_id] using Polynomial.contDiff_aeval (𝕜 := ℝ) P ∞
    exact hP.comp h1
  exact (Complex.ofRealCLM.contDiff.comp h2).mul ((zcL.contDiff).pow m)

lemma contDiff_angG (ρ : CliffordRep 2 V) (v : V) (n s : ℕ) (G F : ℝ[X]) :
    ContDiff ℝ ∞ (angG ρ v n s G F) := by
  unfold angG angSpinor
  exact ((Lv ρ v).contDiff.comp (contDiff_angProfile s (n + 1) G)).add
    ((gam ρ 0).contDiff.comp ((Lv ρ v).contDiff.comp (contDiff_angProfile s n F)))

lemma contDiff_modeFn (ρ : CliffordRep 2 V) (k : ℕ) (ε : ℝ) (n : ℕ) (v : V) :
    ContDiff ℝ ∞ (modeFn ρ k ε n v) :=
  contDiff_stereoH_rpow_inf.smul (contDiff_angG ρ v n (k + 1) _ _)

lemma contDiff_modeFnS (ρ : CliffordRep 2 V) (k : ℕ) (ε : ℝ) (n : ℕ) (v : V) :
    ContDiff ℝ ∞ (modeFnS ρ k ε n v) :=
  contDiff_stereoH_rpow_inf.smul (contDiff_angG ρ (Jop ρ v) n (k + 1) _ _)

/-- Each explicit mode is a smooth spinor field of the sphere. -/
lemma modeFn_mem (ρ : CliffordRep 2 V) (k n : ℕ) (hn : n ≤ k) {ε : ℝ} (hε : ε * ε = 1) (v : V) :
    modeFn ρ k ε n v ∈ SphereEigenspace ρ (ε * ((k + 1 : ℕ) : ℝ)) :=
  ⟨contDiff_modeFn ρ k ε n v, fun x => modeFn_eigen ρ k hε hn v x, modeFnS ρ k ε n v,
    contDiff_modeFnS ρ k ε n v, fun y hy => modeFnS_inv2 ρ k ε hn v hy⟩

lemma modeMap_mem (ρ : CliffordRep 2 V) (k : ℕ) {ε : ℝ} (hε : ε * ε = 1) (w : Fin (k + 1) → V) :
    modeMap ρ k ε w ∈ SphereEigenspace ρ (ε * ((k + 1 : ℕ) : ℝ)) := by
  have : modeMap ρ k ε w = ∑ n : Fin (k + 1), modeFn ρ k ε n (w n) := by
    funext y; simp [modeMap]
  rw [this]
  exact Submodule.sum_mem _ fun n _ => modeFn_mem ρ k n (Nat.lt_succ_iff.mp n.2) hε (w n)

/-! ### The spectrum -/

section Main

variable [FiniteDimensional ℝ V] (ρ : CliffordRep 2 V) (hV : Module.finrank ℝ V = 4)

include hV

lemma exists_ne_zero_vec : ∃ v : V, v ≠ 0 := by
  have : 0 < Module.finrank ℝ V := by omega
  have := Module.finrank_pos_iff.mp this
  exact exists_ne 0

/-- **No other eigenvalue.** There is no nonzero smooth spinor field with `D f = λ f` unless `λ = ±(k+1)`. -/
theorem sphereEigenspace_eq_bot {lam : ℝ}
    (hnot : ¬ ∃ k : ℕ, lam = ((k + 1 : ℕ) : ℝ) ∨ lam = -((k + 1 : ℕ) : ℝ)) :
    SphereEigenspace ρ lam = ⊥ := by
  obtain ⟨v, hv⟩ := exists_ne_zero_vec (V := V) hV
  have h : ChartEigen ρ lam = ⊥ := by
    refine chartEigen_eq_bot ρ hv hV fun k hk => ⟨fun h => hnot ⟨k - 1, Or.inl ?_⟩, fun h => hnot ⟨k - 1, Or.inr ?_⟩⟩
    · rw [h]; congr 1; omega
    · rw [h]; congr 2; omega
  exact le_bot_iff.mp (h ▸ sphereEigenspace_le_chartEigen ρ lam)

/-- **The multiplicity.** For `ε = ±1` and every `k`, the smooth spinor fields of the sphere with `D f = ε (k+1) f`
have real dimension `4 (k+1)`, i.e. complex multiplicity `2 (k+1)`. -/
theorem sphereEigenspace_finrank (k : ℕ) {ε : ℝ} (hε : ε * ε = 1) :
    Module.finrank ℝ (SphereEigenspace ρ (ε * ((k + 1 : ℕ) : ℝ))) = 4 * (k + 1) := by
  obtain ⟨v, hv⟩ := exists_ne_zero_vec (V := V) hV
  have hlam : ε * ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) ∨ ε * ((k + 1 : ℕ) : ℝ) = -((k + 1 : ℕ) : ℝ) := by
    rcases mul_self_eq_one_iff.mp hε with h | h
    · left; rw [h]; ring
    · right; rw [h]; ring
  haveI := chartEigen_finite ρ hv hV (k := k + 1) (by omega) hlam
  have hle := sphereEigenspace_le_chartEigen ρ (ε * ((k + 1 : ℕ) : ℝ))
  haveI : Module.Finite ℝ (SphereEigenspace ρ (ε * ((k + 1 : ℕ) : ℝ))) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  apply le_antisymm
  · have h1 := LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hle)
    have h2 := chartEigen_finrank_le ρ hv hV (k := k + 1) (by omega) hlam
    omega
  · let Φ : (Fin (k + 1) → V) →ₗ[ℝ] SphereEigenspace ρ (ε * ((k + 1 : ℕ) : ℝ)) :=
      (modeMap ρ k ε).codRestrict _ (modeMap_mem ρ k hε)
    have hΦ : Function.Injective Φ := by
      intro w w' h
      exact modeMap_injective ρ k hε (congrArg Subtype.val h)
    have h1 := LinearMap.finrank_le_finrank_of_injective hΦ
    have h2 : Module.finrank ℝ (Fin (k + 1) → V) = (k + 1) * 4 := by
      rw [Module.finrank_pi_fintype]
      simp [hV]
    omega

/-- **The Dirac spectrum of the unit 2-sphere** (trust check).  For a Clifford module `V` of real dimension `4`:
a smooth spinor field with `D f = λ f` exists exactly for `λ = ±(k+1)`, `k ∈ ℕ`, and these eigenvalues have real
multiplicity `4 (k+1)`, i.e. complex multiplicity `2 (k+1)`. -/
theorem sphere_spectrum (lam : ℝ) :
    (SphereEigenspace ρ lam ≠ ⊥ ↔ ∃ k : ℕ, lam = ((k + 1 : ℕ) : ℝ) ∨ lam = -((k + 1 : ℕ) : ℝ)) ∧
    ∀ (k : ℕ) {ε : ℝ}, ε * ε = 1 →
      Module.finrank ℝ (SphereEigenspace ρ (ε * ((k + 1 : ℕ) : ℝ))) = 4 * (k + 1) := by
  refine ⟨⟨fun h => ?_, fun ⟨k, hk⟩ => ?_⟩, fun k ε hε => sphereEigenspace_finrank ρ hV k hε⟩
  · by_contra hno
    exact h (sphereEigenspace_eq_bot ρ hV hno)
  · intro hbot
    have hε : (1 : ℝ) * 1 = 1 := by norm_num
    rcases hk with h | h
    · have := sphereEigenspace_finrank ρ hV k hε
      rw [one_mul, ← h, hbot] at this
      simp at this
    · have hε' : (-1 : ℝ) * -1 = 1 := by norm_num
      have := sphereEigenspace_finrank ρ hV k hε'
      rw [show (-1 : ℝ) * ((k + 1 : ℕ) : ℝ) = lam by rw [h]; ring, hbot] at this
      simp at this

end Main

end Lightlike.Dirac
