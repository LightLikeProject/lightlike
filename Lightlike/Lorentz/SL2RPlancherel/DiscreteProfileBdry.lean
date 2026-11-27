module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileImages

/-!
# Orthogonality to the ladder images of generators that do not vanish near `ξ = 0`

`DiscreteProfileImages` treats test functions vanishing near `0`. The ladder images of the radial generators of
the opposite-sign blocks do not vanish near `0`, but they are continuous on `[0, ∞)` (so the boundary term
`F conj(G) sinh` vanishes at `0`) and vanish for large `ξ`. `integral_ladUp_mul_conj_of_cont` is the adjointness of
`ladUp` and `ladDown` in this setting, and `integral_chain_mul_conj_eq_zero` is the orthogonality of the chain
`H_{i+1} = ladUp i r H_i` of such functions to the family `G_k` with `ladDown (ν+k+1) r G_{k+1} = c_k G_k`,
`ladDown ν r G_0 = 0`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The derivative of the pairing** `F conj(G) sinh` at `ξ > 0`. -/
lemma hasDerivAt_ladPair (l r : ℝ) {F G : ℝ → ℂ} {ξ : ℝ} (hξ : 0 < ξ) (hF : DifferentiableAt ℝ F ξ)
    (hG : DifferentiableAt ℝ G ξ) :
    HasDerivAt (fun ξ => F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ))
      (ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) -
        F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ)) ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have h1 := hF.hasDerivAt.mul (hG.hasDerivAt.star)
  have h2 := h1.mul ((Real.hasDerivAt_sinh ξ).ofReal_comp)
  refine HasDerivAt.congr_deriv h2 ?_
  have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hcs : (starRingEnd ℂ) (Complex.sinh (ξ : ℂ)) = Complex.sinh ξ := by
    rw [← Complex.ofReal_sinh, Complex.conj_ofReal]
  have hcc : (starRingEnd ℂ) (Complex.cosh (ξ : ℂ)) = Complex.cosh ξ := by
    rw [← Complex.ofReal_cosh, Complex.conj_ofReal]
  have hs'' : Complex.sinh (ξ : ℂ) ≠ 0 := by rw [← Complex.ofReal_sinh]; exact_mod_cast hs
  simp [ladUp, ladDown, ladCoeff, Complex.conj_ofReal, hcs, hcc]
  field_simp
  ring

/-- **Adjointness of `ladUp` and `ladDown` for functions continuous on `[0, ∞)`** that vanish for `ξ ≥ R`. -/
theorem integral_ladUp_mul_conj_of_cont (l r : ℝ) {F G Lc Rc : ℝ → ℂ} {R : ℝ} (hR : 0 < R)
    (hFc : ContinuousOn F (Ici 0)) (hF1 : ContDiffOn ℝ 1 F (Ioi 0)) (hFR : ∀ ξ, R ≤ ξ → F ξ = 0)
    (hGc : ContinuousOn G (Ici 0)) (hG1 : ContDiffOn ℝ 1 G (Ioi 0))
    (hLc : ContinuousOn Lc (Ici 0)) (hL : ∀ ξ, 0 < ξ → ladUp l r F ξ = Lc ξ)
    (hRc : ContinuousOn Rc (Ici 0)) (hRr : ∀ ξ, 0 < ξ → ladDown (l + 1) r G ξ = Rc ξ) :
    ∫ ξ in Ioi (0 : ℝ), ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) =
      ∫ ξ in Ioi (0 : ℝ), F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) := by
  have hsc : Continuous fun ξ : ℝ => (Real.sinh ξ : ℂ) :=
    Complex.continuous_ofReal.comp Real.continuous_sinh
  set D : ℝ → ℂ := fun ξ => Lc ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) -
    F ξ * (starRingEnd ℂ) (Rc ξ) * (Real.sinh ξ : ℂ) with hD
  have hDc : ContinuousOn D (Ici 0) := by
    refine ContinuousOn.sub ?_ ?_
    · exact (hLc.mul (Complex.continuous_conj.comp_continuousOn hGc)).mul hsc.continuousOn
    · exact (hFc.mul (Complex.continuous_conj.comp_continuousOn hRc)).mul hsc.continuousOn
  set P : ℝ → ℂ := fun ξ => F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) with hP
  have hPc : ContinuousOn P (Icc 0 R) := by
    have := (hFc.mul (Complex.continuous_conj.comp_continuousOn hGc)).mul hsc.continuousOn
    exact this.mono Icc_subset_Ici_self
  have hder : ∀ x ∈ Ioo (0 : ℝ) R, HasDerivAt P (D x) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hFd : DifferentiableAt ℝ F x := ((hF1.differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds hx0))
    have hGd : DifferentiableAt ℝ G x := ((hG1.differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds hx0))
    have := hasDerivAt_ladPair l r hx0 hFd hGd
    rw [hL x hx0, hRr x hx0] at this
    exact this
  have hDi : IntervalIntegrable D volume 0 R := (hDc.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hR.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hPc hder hDi
  have hPR : P R = 0 := by simp [hP, hFR R le_rfl]
  have hP0 : P 0 = 0 := by simp [hP]
  rw [hPR, hP0, sub_zero] at hFTC
  have hLz : ∀ ξ ∈ Ioi (0 : ℝ) \ Ioc 0 R,
      ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) = 0 := by
    intro ξ hξ
    have hξR : R < ξ := by
      by_contra h
      exact hξ.2 ⟨hξ.1, not_lt.1 h⟩
    have h0 : F =ᶠ[𝓝 ξ] 0 := by
      filter_upwards [Ioi_mem_nhds hξR] with y hy using hFR y hy.le
    simp [ladUp, h0.deriv_eq, h0.self_of_nhds]
  have hRz : ∀ ξ ∈ Ioi (0 : ℝ) \ Ioc 0 R,
      F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) = 0 := by
    intro ξ hξ
    have hξR : R < ξ := by
      by_contra h
      exact hξ.2 ⟨hξ.1, not_lt.1 h⟩
    simp [hFR ξ hξR.le]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self hLz,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self hRz,
    ← intervalIntegral.integral_of_le hR.le, ← intervalIntegral.integral_of_le hR.le]
  have hLi : IntervalIntegrable (fun ξ => Lc ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ)) volume 0 R :=
    (((hLc.mul (Complex.continuous_conj.comp_continuousOn hGc)).mul hsc.continuousOn).mono
      Icc_subset_Ici_self).intervalIntegrable_of_Icc hR.le
  have hRi : IntervalIntegrable (fun ξ => F ξ * (starRingEnd ℂ) (Rc ξ) * (Real.sinh ξ : ℂ)) volume 0 R :=
    (((hFc.mul (Complex.continuous_conj.comp_continuousOn hRc)).mul hsc.continuousOn).mono
      Icc_subset_Ici_self).intervalIntegrable_of_Icc hR.le
  have e1 : ∫ ξ in (0 : ℝ)..R, ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) =
      ∫ ξ in (0 : ℝ)..R, Lc ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) := by
    rw [intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_of_le hR.le]
    refine setIntegral_congr_fun measurableSet_Ioc (fun ξ hξ => ?_)
    rw [hL ξ hξ.1]
  have e2 : ∫ ξ in (0 : ℝ)..R, F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) =
      ∫ ξ in (0 : ℝ)..R, F ξ * (starRingEnd ℂ) (Rc ξ) * (Real.sinh ξ : ℂ) := by
    rw [intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_of_le hR.le]
    refine setIntegral_congr_fun measurableSet_Ioc (fun ξ hξ => ?_)
    rw [hRr ξ hξ.1]
  rw [e1, e2]
  have : ∫ ξ in (0 : ℝ)..R, D ξ = (∫ ξ in (0 : ℝ)..R, Lc ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ)) -
      ∫ ξ in (0 : ℝ)..R, F ξ * (starRingEnd ℂ) (Rc ξ) * (Real.sinh ξ : ℂ) :=
    intervalIntegral.integral_sub hLi hRi
  rw [this] at hFTC
  exact sub_eq_zero.1 hFTC

/-- **Orthogonality of a chain of images to the family `G_k`** (boundary version): if `H_{i+1} = ladUp i r H_i` on
`ξ > 0` with every `H_i` continuous on `[0, ∞)`, `C¹` on `(0, ∞)` and vanishing for `ξ ≥ R`, and the `G_k` satisfy
`ladDown ν r G_0 = 0`, `ladDown (ν+k+1) r G_{k+1} = c_k G_k`, then `∫_0^∞ H_{ν+k} conj(G_k) sinh = 0`. -/
theorem integral_chain_mul_conj_eq_zero (r : ℝ) (ν : ℕ) (hν : 1 ≤ ν) {G : ℕ → ℝ → ℂ} (c : ℕ → ℝ)
    (hG : ∀ k, ContDiffOn ℝ 1 (G k) (Ioi 0)) (hGc : ∀ k, ContinuousOn (G k) (Ici 0))
    (h0 : ∀ ξ : ℝ, 0 < ξ → ladDown (ν : ℝ) r (G 0) ξ = 0)
    (hs : ∀ (k : ℕ) (ξ : ℝ), 0 < ξ → ladDown ((ν + k + 1 : ℕ) : ℝ) r (G (k + 1)) ξ = (c k : ℂ) * G k ξ)
    {H : ℕ → ℝ → ℂ}
    (hH1 : ∀ i, ContDiffOn ℝ 1 (H i) (Ioi 0)) (hHc : ∀ i, ContinuousOn (H i) (Ici 0))
    (hHR : ∀ i, ∃ R : ℝ, 0 < R ∧ ∀ ξ, R ≤ ξ → H i ξ = 0)
    (hstep : ∀ (i : ℕ) (ξ : ℝ), 0 < ξ → H (i + 1) ξ = ladUp (i : ℝ) r (H i) ξ) :
    ∀ k : ℕ, ∫ ξ in Ioi (0 : ℝ), H (ν + k) ξ * (starRingEnd ℂ) (G k ξ) * (Real.sinh ξ : ℂ) = 0 := by
  obtain ⟨ν', rfl⟩ : ∃ ν', ν = ν' + 1 := ⟨ν - 1, by omega⟩
  intro k
  induction k with
  | zero =>
    obtain ⟨R, hR, hHR'⟩ := hHR ν'
    have e : ∀ ξ : ℝ, 0 < ξ → ladUp (ν' : ℝ) r (H ν') ξ = H (ν' + 1 + 0) ξ := fun ξ hξ => (hstep ν' ξ hξ).symm
    have key := integral_ladUp_mul_conj_of_cont (ν' : ℝ) r (F := H ν') (G := G 0) (Lc := H (ν' + 1 + 0))
      (Rc := fun _ => 0) hR (hHc ν') (hH1 ν') hHR' (hGc 0) (hG 0) (hHc _) e continuousOn_const
      (fun ξ hξ => by
        have := h0 ξ hξ
        push_cast at this ⊢
        simpa using this)
    have e2 : ∀ ξ ∈ Ioi (0 : ℝ), ladUp (ν' : ℝ) r (H ν') ξ * (starRingEnd ℂ) (G 0 ξ) * (Real.sinh ξ : ℂ) =
        H (ν' + 1 + 0) ξ * (starRingEnd ℂ) (G 0 ξ) * (Real.sinh ξ : ℂ) := by
      intro ξ hξ; rw [e ξ hξ]
    have e4 : ∀ ξ ∈ Ioi (0 : ℝ), H ν' ξ * (starRingEnd ℂ) (ladDown ((ν' : ℝ) + 1) r (G 0) ξ) *
        (Real.sinh ξ : ℂ) = 0 := by
      intro ξ hξ
      have := h0 ξ hξ
      push_cast at this
      simp [this]
    rw [← setIntegral_congr_fun measurableSet_Ioi e2, key, setIntegral_congr_fun measurableSet_Ioi e4]
    simp
  | succ k ih =>
    obtain ⟨R, hR, hHR'⟩ := hHR (ν' + 1 + k)
    have e : ∀ ξ : ℝ, 0 < ξ → ladUp ((ν' + 1 + k : ℕ) : ℝ) r (H (ν' + 1 + k)) ξ = H (ν' + 1 + (k + 1)) ξ :=
      fun ξ hξ => (hstep (ν' + 1 + k) ξ hξ).symm
    have key := integral_ladUp_mul_conj_of_cont ((ν' + 1 + k : ℕ) : ℝ) r (F := H (ν' + 1 + k)) (G := G (k + 1))
      (Lc := H (ν' + 1 + (k + 1))) (Rc := fun ξ => (c k : ℂ) * G k ξ) hR (hHc _) (hH1 _) hHR' (hGc _) (hG _)
      (hHc _) e (continuousOn_const.mul (hGc k))
      (fun ξ hξ => by
        have h1 := hs k ξ hξ
        have h2 : (((ν' + 1 + k : ℕ) : ℝ) + 1) = ((ν' + 1 + k + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [h2, h1])
    have e2 : ∀ ξ ∈ Ioi (0 : ℝ), ladUp ((ν' + 1 + k : ℕ) : ℝ) r (H (ν' + 1 + k)) ξ *
        (starRingEnd ℂ) (G (k + 1) ξ) * (Real.sinh ξ : ℂ) =
        H (ν' + 1 + (k + 1)) ξ * (starRingEnd ℂ) (G (k + 1) ξ) * (Real.sinh ξ : ℂ) := by
      intro ξ hξ; rw [e ξ hξ]
    rw [← setIntegral_congr_fun measurableSet_Ioi e2, key]
    have e3 : ∀ ξ ∈ Ioi (0 : ℝ), H (ν' + 1 + k) ξ *
        (starRingEnd ℂ) (ladDown (((ν' + 1 + k : ℕ) : ℝ) + 1) r (G (k + 1)) ξ) * (Real.sinh ξ : ℂ) =
        (c k : ℂ) * (H (ν' + 1 + k) ξ * (starRingEnd ℂ) (G k ξ) * (Real.sinh ξ : ℂ)) := by
      intro ξ hξ
      have h1 := hs k ξ hξ
      have h2 : (((ν' + 1 + k : ℕ) : ℝ) + 1) = ((ν' + 1 + k + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [h2, h1]
      simp only [map_mul, Complex.conj_ofReal]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi e3, integral_const_mul, ih]
    simp

end Lightlike.Lorentz.SL2RPlancherel
