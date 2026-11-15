import Mathlib
import Lightlike.Regge.Linear.Local
import Lightlike.Regge.Linear.Taylor
import Lightlike.Regge.Linear.Riemann

/-!
# Convergence of the linearized vertex deficits to the linearized curvature

For a smooth compactly supported symmetric perturbation `h` of the flat metric of the plane and a
`C¹` compactly supported weight `f`, the weighted sum of the linearized vertex deficits of the
diagonal grids of mesh `1/n` differs from the integral of `f` against the linearized curvature
`∂₀∂₁ h₀₁ - ½ (∂₁² h₀₀ + ∂₀² h₁₁)` by at most `C / n`.
-/

open Set MeasureTheory Lightlike

namespace Lightlike.Regge.Linear

noncomputable section

/-- The linearized Gauss curvature (half the linearized scalar curvature) of the perturbation `h` of
the flat metric:
`∂₀∂₁ h₀₁ - ½ (∂₁² h₀₀ + ∂₀² h₁₁)`, which is `½ (∂ᵢ∂ⱼ hᵢⱼ - Δ tr h)`. -/
def linCurv (h : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) : ℝ :=
  curv (jetOf (fun y => h y 0 0) x) (jetOf (fun y => h y 0 1) x) (jetOf (fun y => h y 1 1) x)

lemma contDiff_pd {u : (Fin 2 → ℝ) → ℝ} {m : ℕ} (hu : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u)
    (k : Fin 2) : ContDiff ℝ (m : WithTop ℕ∞) (Lightlike.pd k u) := by
  have := (hu.fderiv_right (m := m) (by simp)).clm_apply
    (contDiff_const (c := (Pi.single k 1 : Fin 2 → ℝ)))
  exact this

lemma hasCompactSupport_pd {u : (Fin 2 → ℝ) → ℝ} (hc : HasCompactSupport u) (k : Fin 2) :
    HasCompactSupport (Lightlike.pd k u) := hc.fderiv_apply (𝕜 := ℝ) _

section
variable {h : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ}

lemma contDiff_linCurv (h00 : ContDiff ℝ 3 fun x => h x 0 0) (h01 : ContDiff ℝ 3 fun x => h x 0 1)
    (h11 : ContDiff ℝ 3 fun x => h x 1 1) : ContDiff ℝ 1 (linCurv h) := by
  have a : ∀ {u : (Fin 2 → ℝ) → ℝ}, ContDiff ℝ 3 u → ∀ i j : Fin 2,
      ContDiff ℝ 1 (Lightlike.pd i (Lightlike.pd j u)) := by
    intro u hu i j
    have h2 : ContDiff ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) (u) := by simpa using hu
    have h1 := contDiff_pd (m := 2) h2 j
    have h1' : ContDiff ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) (Lightlike.pd j u) := by simpa using h1
    simpa using contDiff_pd (m := 1) h1' i
  have e : linCurv h = fun x => Lightlike.pd 0 (Lightlike.pd 1 fun y => h y 0 1) x
      - (Lightlike.pd 1 (Lightlike.pd 1 fun y => h y 0 0) x
        + Lightlike.pd 0 (Lightlike.pd 0 fun y => h y 1 1) x) / 2 := rfl
  rw [e]
  exact (a h01 0 1).sub (((a h00 1 1).add (a h11 0 0)).div_const 2)

lemma hasCompactSupport_linCurv (c00 : HasCompactSupport fun x => h x 0 0)
    (c01 : HasCompactSupport fun x => h x 0 1) (c11 : HasCompactSupport fun x => h x 1 1) :
    HasCompactSupport (linCurv h) := by
  have e : linCurv h = fun x => Lightlike.pd 0 (Lightlike.pd 1 fun y => h y 0 1) x
      - (Lightlike.pd 1 (Lightlike.pd 1 fun y => h y 0 0) x
        + Lightlike.pd 0 (Lightlike.pd 0 fun y => h y 1 1) x) / 2 := rfl
  rw [e]
  have hh := ((hasCompactSupport_pd (hasCompactSupport_pd c00 1) 1).add
      (hasCompactSupport_pd (hasCompactSupport_pd c11 0) 0)).comp_left (g := fun t : ℝ => t / 2)
      (by simp)
  exact (hasCompactSupport_pd (hasCompactSupport_pd c01 1) 0).sub hh

/-- **Local error of the linearized deficit.** For smooth compactly supported entries there is a
single `K ≥ 0` such that at every point `P` and every mesh `s > 0`,
`|linDef h s P - s² linCurv h P| ≤ 336 K s³`. -/
theorem linDef_local_error (h00 : ContDiff ℝ 3 fun x => h x 0 0)
    (h01 : ContDiff ℝ 3 fun x => h x 0 1) (h11 : ContDiff ℝ 3 fun x => h x 1 1)
    (c00 : HasCompactSupport fun x => h x 0 0) (c01 : HasCompactSupport fun x => h x 0 1)
    (c11 : HasCompactSupport fun x => h x 1 1) (hsym : ∀ x, h x 1 0 = h x 0 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : Fin 2 → ℝ) (s : ℝ), 0 < s →
      |linDef h s P - s ^ 2 * linCurv h P| ≤ 336 * K * s ^ 3 := by
  obtain ⟨K0, hK0⟩ := taylor_bound h00 c00
  obtain ⟨K1, hK1⟩ := taylor_bound h01 c01
  obtain ⟨K2, hK2⟩ := taylor_bound h11 c11
  refine ⟨max 0 (max K0 (max K1 K2)), le_max_left _ _, fun P s hs => ?_⟩
  set K := max 0 (max K0 (max K1 K2)) with hK
  have hcont : ∀ i j, Continuous fun x => h x i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00.continuous
    · exact h01.continuous
    · have : (fun x => h x 1 0) = fun x => h x 0 1 := funext hsym
      simpa [this] using h01.continuous
    · exact h11.continuous
  have hs3 : ∀ y : Fin 2 → ℝ, ‖y‖ ≤ s → ∀ K' ≤ K, K' * ‖y‖ ^ 3 ≤ K * s ^ 3 := by
    intro y hy K' hK'
    have hK'0 : K' ≤ K := hK'
    have h0 : 0 ≤ K := le_max_left _ _
    calc K' * ‖y‖ ^ 3 ≤ K * ‖y‖ ^ 3 := by gcongr
      _ ≤ K * s ^ 3 := by gcongr
  have := linDef_taylor (K := K) hcont hs (jetOf (fun y => h y 0 0) P) (jetOf (fun y => h y 0 1) P)
    (jetOf (fun y => h y 1 1) P) (by
      intro x hx i j
      have hy : P + (x - P) = x := by abel
      have e0 := hK0 P (x - P)
      have e1 := hK1 P (x - P)
      have e2 := hK2 P (x - P)
      rw [hy] at e0 e1 e2
      fin_cases i <;> fin_cases j
      · simpa [modelField] using e0.trans (hs3 _ hx K0 (le_trans (le_max_left _ _)
          (le_max_right _ _)))
      · simpa [modelField] using e1.trans (hs3 _ hx K1 (le_trans (le_max_left _ _)
          ((le_max_right _ _).trans (le_max_right _ _))))
      · simpa [modelField, hsym] using e1.trans (hs3 _ hx K1 (le_trans (le_max_left _ _)
          ((le_max_right _ _).trans (le_max_right _ _))))
      · simpa [modelField] using e2.trans (hs3 _ hx K2 (le_trans (le_max_right _ _)
          ((le_max_right _ _).trans (le_max_right _ _)))))
  simpa [linCurv] using this

lemma card_gbox_le (R n : ℕ) (hn : 0 < n) : ((gbox R n).card : ℝ) ≤ ((2 * R + 1) * n) ^ 2 := by
  rw [card_gbox]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2

/-- **Convergence of the linearized Regge curvature (dimension 2).** Let `h` be a symmetric
perturbation of the flat metric of the plane with smooth compactly supported entries, and `f` a
`C¹` compactly supported weight. Then the weighted sum of the linearized vertex deficits of the
diagonal grids of mesh `1/n` (one vertex at every lattice point `v / n`) differs from the integral
of `f` against the linearized scalar curvature by at most `C / n`. -/
theorem linearized_regge_converges (h00 : ContDiff ℝ 3 fun x => h x 0 0)
    (h01 : ContDiff ℝ 3 fun x => h x 0 1) (h11 : ContDiff ℝ 3 fun x => h x 1 1)
    (c00 : HasCompactSupport fun x => h x 0 0) (c01 : HasCompactSupport fun x => h x 0 1)
    (c11 : HasCompactSupport fun x => h x 1 1) (hsym : ∀ x, h x 1 0 = h x 0 1)
    {f : (Fin 2 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ n : ℕ, 0 < n →
      |∑' v : ℤ × ℤ, f (gpt n v) * linDef h (1 / (n : ℝ)) (gpt n v)
        - ∫ x, f x * linCurv h x| ≤ C / n := by
  obtain ⟨K, hK0, hK⟩ := linDef_local_error h00 h01 h11 c00 c01 c11 hsym
  obtain ⟨Mf, hMf⟩ := hfc.exists_bound_of_continuous hf.continuous
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf 0)
  have hFd : ContDiff ℝ 1 fun x => f x * linCurv h x :=
    hf.mul (contDiff_linCurv h00 h01 h11)
  have hFc : HasCompactSupport fun x => f x * linCurv h x :=
    (hasCompactSupport_linCurv c00 c01 c11).mul_left
  obtain ⟨Λ, hΛ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) (n := 1)
    (f := fun x => f x * linCurv h x) hFc hFd (by simp)
  obtain ⟨R0, hR0⟩ : ∃ R : ℝ, ∀ x, R < ‖x‖ → f x = 0 := by
    obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.exists_norm_le
    refine ⟨R, fun x hx => ?_⟩
    by_contra hne
    have : x ∈ tsupport f := subset_tsupport _ hne
    have := hR x this
    linarith
  obtain ⟨R, hR⟩ := exists_nat_ge R0
  have hRf : ∀ x, (R : ℝ) < ‖x‖ → f x = 0 := fun x hx => hR0 x (lt_of_le_of_lt hR hx)
  have hRF : ∀ x, (R : ℝ) < ‖x‖ → f x * linCurv h x = 0 := fun x hx => by
    rw [hRf x hx, zero_mul]
  refine ⟨(336 * Mf * K + Λ) * (2 * R + 1) ^ 2, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (0 : ℝ) < 1 / n := by positivity
  -- the sum over the lattice is a sum over the box
  have hbox : ∀ v ∉ gbox R n, f (gpt n v) * linDef h (1 / (n : ℝ)) (gpt n v) = 0 := by
    intro v hv
    have : f (gpt n v) = 0 := by
      apply hRf
      by_contra hle
      rw [not_lt] at hle
      apply hv
      -- norm of gpt at most R forces the lattice point into the box
      have hk : ∀ k, |(gpt n v) k| ≤ R := fun k => (norm_le_pi_norm _ k).trans hle |>.trans' (by
        rw [Real.norm_eq_abs])
      have h0 := hk 0
      have h1 := hk 1
      simp only [gpt, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      rw [abs_div, abs_of_pos hn', div_le_iff₀ hn', ← Int.cast_abs] at h0 h1
      simp only [gbox, Finset.mem_product, Finset.mem_Icc]
      have g0 : |v.1| ≤ ((R * n : ℕ) : ℤ) := by exact_mod_cast h0
      have g1 : |v.2| ≤ ((R * n : ℕ) : ℤ) := by exact_mod_cast h1
      exact ⟨abs_le.mp g0, abs_le.mp g1⟩
    rw [this, zero_mul]
  rw [tsum_eq_sum hbox]
  have hRiem := riemann_sum hΛ hRF hn
  have hloc : |∑ v ∈ gbox R n, f (gpt n v) * linDef h (1 / (n : ℝ)) (gpt n v)
      - ∑ v ∈ gbox R n, (1 / (n : ℝ)) ^ 2 * (f (gpt n v) * linCurv h (gpt n v))| ≤
      336 * Mf * K * (2 * R + 1) ^ 2 / n := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ v ∈ gbox R n, |f (gpt n v) * linDef h (1 / (n : ℝ)) (gpt n v)
            - (1 / (n : ℝ)) ^ 2 * (f (gpt n v) * linCurv h (gpt n v))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ gbox R n, Mf * (336 * K * (1 / (n : ℝ)) ^ 3) := by
          refine Finset.sum_le_sum fun v _ => ?_
          have e : f (gpt n v) * linDef h (1 / (n : ℝ)) (gpt n v)
              - (1 / (n : ℝ)) ^ 2 * (f (gpt n v) * linCurv h (gpt n v)) =
              f (gpt n v) * (linDef h (1 / (n : ℝ)) (gpt n v)
                - (1 / (n : ℝ)) ^ 2 * linCurv h (gpt n v)) := by ring
          rw [e, abs_mul]
          have := hK (gpt n v) (1 / n) hs
          have hf1 : |f (gpt n v)| ≤ Mf := by simpa using hMf (gpt n v)
          exact mul_le_mul hf1 this (abs_nonneg _) hMf0
      _ = (gbox R n).card * (Mf * (336 * K * (1 / (n : ℝ)) ^ 3)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 * R + 1) * n) ^ 2 * (Mf * (336 * K * (1 / (n : ℝ)) ^ 3)) := by
          gcongr
          exact card_gbox_le R n hn
      _ = 336 * Mf * K * (2 * R + 1) ^ 2 / n := by field_simp
  calc _ = |(∑ v ∈ gbox R n, f (gpt n v) * linDef h (1 / (n : ℝ)) (gpt n v)
          - ∑ v ∈ gbox R n, (1 / (n : ℝ)) ^ 2 * (f (gpt n v) * linCurv h (gpt n v)))
        + (∑ v ∈ gbox R n, (1 / (n : ℝ)) ^ 2 * (f (gpt n v) * linCurv h (gpt n v))
          - ∫ x, f x * linCurv h x)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hloc hRiem)
    _ = _ := by ring

end

end

end Lightlike.Regge.Linear
