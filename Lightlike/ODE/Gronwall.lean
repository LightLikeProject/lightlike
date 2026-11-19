import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Two-sided Grönwall estimates and short-time linear equations

Mathlib's Grönwall inequality (`norm_le_gronwallBound_of_norm_deriv_right_le`) runs forward in
time from the initial point. Flows are used for times of both signs, so this file restates the
estimate on a symmetric interval `[-T, T]` around the initial time `0`, and derives from it the
three facts about ordinary differential equations that the differentiability of a flow needs.

Throughout, a curve is differentiable on `[-T, T]` in the sense of `HasDerivWithinAt … (Icc (-T) T)`.

## Main results

* `Lightlike.ODE.norm_le_gronwallBound_abs`: Grönwall's inequality on `[-T, T]`.
* `Lightlike.ODE.gronwallBound_zero_le`: `gronwallBound 0 K ε x ≤ ε x e^{K x}`.
* `Lightlike.ODE.norm_sub_le_of_trajectories`: two solutions of `ẋ = V x` in a set where `V` is
  `K`-Lipschitz stay within `e^{K |t|}` times their initial distance.
* `Lightlike.ODE.exists_linear_solution`: a linear equation `u̇ = A(t) u` with continuous
  coefficient, `‖A‖ ≤ K` and `K T ≤ 1/2` has a solution on `[-T, T]` with a given value at `0`.
* `Lightlike.ODE.norm_sub_le_of_linear`: two linear equations with close coefficients have close
  solutions.
-/

open Set Metric
open scoped NNReal

noncomputable section

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The reflection `t ↦ -t` maps `[-T, T]` to itself. -/
lemma mapsTo_neg_Icc (T : ℝ) : MapsTo (fun t : ℝ => -t) (Icc (-T) T) (Icc (-T) T) := by
  intro t ht
  exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- Time reversal of a curve that is differentiable on `[-T, T]`. -/
lemma hasDerivWithinAt_comp_neg {f f' : ℝ → E} {T t : ℝ}
    (hf : HasDerivWithinAt f (f' (-t)) (Icc (-T) T) (-t)) :
    HasDerivWithinAt (fun s => f (-s)) (-f' (-t)) (Icc (-T) T) t := by
  have h := HasDerivWithinAt.scomp t hf (hasDerivAt_neg t).hasDerivWithinAt (mapsTo_neg_Icc T)
  simpa [Function.comp_def] using h

/-- **Grönwall's inequality on a symmetric interval.** If `f` is differentiable on `[-T, T]` with
`‖f'‖ ≤ K ‖f‖ + ε` there and `‖f 0‖ ≤ δ`, then `‖f t‖ ≤ gronwallBound δ K ε |t|` on `[-T, T]`. -/
theorem norm_le_gronwallBound_abs {f f' : ℝ → E} {δ K ε T : ℝ}
    (hf : ∀ t ∈ Icc (-T) T, HasDerivWithinAt f (f' t) (Icc (-T) T) t)
    (h0 : ‖f 0‖ ≤ δ) (bound : ∀ t ∈ Icc (-T) T, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ t ∈ Icc (-T) T, ‖f t‖ ≤ gronwallBound δ K ε |t| := by
  -- the forward estimate, for any curve on `[-T, T]`
  have key : ∀ (g g' : ℝ → E), (∀ t ∈ Icc (-T) T, HasDerivWithinAt g (g' t) (Icc (-T) T) t) →
      ‖g 0‖ ≤ δ → (∀ t ∈ Icc (-T) T, ‖g' t‖ ≤ K * ‖g t‖ + ε) →
      ∀ t ∈ Icc (0 : ℝ) T, ‖g t‖ ≤ gronwallBound δ K ε t := by
    intro g g' hg hg0 hb t ht
    have hsub : Icc (0 : ℝ) T ⊆ Icc (-T) T := fun s hs => ⟨by linarith [hs.1, hs.2], hs.2⟩
    have hcont : ContinuousOn g (Icc 0 T) := fun s hs =>
      ((hg s (hsub hs)).continuousWithinAt).mono hsub
    have hder : ∀ s ∈ Ico (0 : ℝ) T, HasDerivWithinAt g (g' s) (Ici s) s := by
      intro s hs
      have hs' : s ∈ Icc (-T) T := hsub ⟨hs.1, hs.2.le⟩
      refine (hg s hs').mono_of_mem_nhdsWithin ?_
      exact Filter.mem_of_superset (Icc_mem_nhdsGE_of_mem ⟨le_rfl, hs.2⟩)
        (fun u hu => ⟨by linarith [hu.1, hs.1, hs'.1], hu.2⟩)
    have := norm_le_gronwallBound_of_norm_deriv_right_le hcont hder hg0
      (fun s hs => hb s (hsub ⟨hs.1, hs.2.le⟩)) t ht
    simpa using this
  intro t ht
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
    exact key f f' hf h0 bound t ⟨h, ht.2⟩
  · rw [abs_of_nonpos h]
    have := key (fun s => f (-s)) (fun s => -f' (-s))
      (fun s hs => hasDerivWithinAt_comp_neg (hf (-s) (mapsTo_neg_Icc T hs)))
      (by simpa using h0)
      (fun s hs => by simpa using bound (-s) (mapsTo_neg_Icc T hs))
      (-t) ⟨by linarith, by linarith [ht.1]⟩
    simpa using this

/-- With zero initial value, Grönwall's bound is at most `ε x e^{K x}`. -/
theorem gronwallBound_zero_le {K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound 0 K ε x ≤ ε * x * Real.exp (K * x) := by
  rcases eq_or_lt_of_le hK with rfl | hK'
  · simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hK'.ne']
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have h2 := Real.add_one_le_exp (-(K * x))
      have h3 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by
        rw [← Real.exp_add]; simp
      have h4 : 0 < Real.exp (K * x) := Real.exp_pos _
      nlinarith
    have hK0 : K ≠ 0 := hK'.ne'
    have h5 : ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
      mul_le_mul_of_nonneg_left h1 (div_nonneg hε hK)
    have h6 : ε / K * (K * x * Real.exp (K * x)) = ε * x * Real.exp (K * x) := by
      rw [div_mul_eq_mul_div, div_eq_iff hK0]
      ring
    rw [h6] at h5
    simp only [zero_mul, zero_add]
    exact h5

/-- A curve on `[-T, T]` with zero initial value whose derivative is bounded by
`K ‖f‖ + ε` is bounded by `ε T e^{K T}`. -/
theorem norm_le_of_deriv_le {f f' : ℝ → E} {K ε T : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hf : ∀ t ∈ Icc (-T) T, HasDerivWithinAt f (f' t) (Icc (-T) T) t)
    (h0 : f 0 = 0) (bound : ∀ t ∈ Icc (-T) T, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ t ∈ Icc (-T) T, ‖f t‖ ≤ ε * T * Real.exp (K * T) := by
  intro t ht
  have habs : |t| ≤ T := abs_le.2 ht
  have h1 := norm_le_gronwallBound_abs hf (by simp [h0] : ‖f 0‖ ≤ 0) bound t ht
  have h2 := gronwallBound_zero_le (x := |t|) hK hε
  have h3 : ε * |t| * Real.exp (K * |t|) ≤ ε * T * Real.exp (K * T) := by
    have : Real.exp (K * |t|) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left habs hK)
    have hT : 0 ≤ T := (abs_nonneg t).trans habs
    exact mul_le_mul (mul_le_mul_of_nonneg_left habs hε) this (Real.exp_pos _).le
      (mul_nonneg hε hT)
  linarith

/-- A curve on `[-T, T]` whose derivative is bounded by `K ‖f‖` is bounded by
`‖f 0‖ e^{K |t|}`. -/
theorem norm_le_exp_of_deriv_le {f f' : ℝ → E} {K T : ℝ}
    (hf : ∀ t ∈ Icc (-T) T, HasDerivWithinAt f (f' t) (Icc (-T) T) t)
    (bound : ∀ t ∈ Icc (-T) T, ‖f' t‖ ≤ K * ‖f t‖) :
    ∀ t ∈ Icc (-T) T, ‖f t‖ ≤ ‖f 0‖ * Real.exp (K * |t|) := by
  intro t ht
  have := norm_le_gronwallBound_abs hf le_rfl (ε := 0) (fun s hs => by simpa using bound s hs) t ht
  rwa [gronwallBound_ε0] at this

/-- **Lipschitz dependence on the initial point.** Two solutions of `ẋ = V x` on `[-T, T]` that
stay in a set where `V` is `K`-Lipschitz satisfy `‖f t - g t‖ ≤ ‖f 0 - g 0‖ e^{K |t|}`. -/
theorem norm_sub_le_of_trajectories {V : E → E} {s : Set E} {K : ℝ≥0} {f g : ℝ → E} {T : ℝ}
    (hV : LipschitzOnWith K V s)
    (hf : ∀ t ∈ Icc (-T) T, HasDerivWithinAt f (V (f t)) (Icc (-T) T) t) (hfs : ∀ t ∈ Icc (-T) T, f t ∈ s)
    (hg : ∀ t ∈ Icc (-T) T, HasDerivWithinAt g (V (g t)) (Icc (-T) T) t) (hgs : ∀ t ∈ Icc (-T) T, g t ∈ s) :
    ∀ t ∈ Icc (-T) T, ‖f t - g t‖ ≤ ‖f 0 - g 0‖ * Real.exp (K * |t|) := by
  refine norm_le_exp_of_deriv_le (f := fun t => f t - g t) (f' := fun t => V (f t) - V (g t))
    (fun t ht => (hf t ht).sub (hg t ht)) (fun t ht => ?_)
  exact hV.norm_sub_le (hfs t ht) (hgs t ht)

/-- Two solutions of `ẋ = V x` on `[-T, T]` with the same value at `0`, staying in a set where
`V` is Lipschitz, agree on `[-T, T]`. -/
theorem eqOn_of_trajectories {V : E → E} {s : Set E} {K : ℝ≥0} {f g : ℝ → E} {T : ℝ}
    (hV : LipschitzOnWith K V s)
    (hf : ∀ t ∈ Icc (-T) T, HasDerivWithinAt f (V (f t)) (Icc (-T) T) t) (hfs : ∀ t ∈ Icc (-T) T, f t ∈ s)
    (hg : ∀ t ∈ Icc (-T) T, HasDerivWithinAt g (V (g t)) (Icc (-T) T) t) (hgs : ∀ t ∈ Icc (-T) T, g t ∈ s)
    (h0 : f 0 = g 0) : EqOn f g (Icc (-T) T) := by
  intro t ht
  have := norm_sub_le_of_trajectories hV hf hfs hg hgs t ht
  rw [h0, sub_self, norm_zero, zero_mul] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

section Linear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A solution of a linear equation `u̇ = A(t) u` on `[-T, T]` with `‖A‖ ≤ K` is bounded by
`‖u 0‖ e^{K |t|}`. -/
theorem norm_le_of_linear {A : ℝ → F →L[ℝ] F} {u : ℝ → F} {K T : ℝ}
    (hA : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ K)
    (hu : ∀ t ∈ Icc (-T) T, HasDerivWithinAt u (A t (u t)) (Icc (-T) T) t) :
    ∀ t ∈ Icc (-T) T, ‖u t‖ ≤ ‖u 0‖ * Real.exp (K * |t|) :=
  norm_le_exp_of_deriv_le hu fun t ht =>
    ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA t ht) (norm_nonneg _))

/-- **Uniqueness for a linear equation.** Two solutions of `u̇ = A(t) u` on `[-T, T]` with
`‖A‖ ≤ K` and the same value at `0` agree. -/
theorem eqOn_of_linear {A : ℝ → F →L[ℝ] F} {u v : ℝ → F} {K T : ℝ}
    (hA : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ K)
    (hu : ∀ t ∈ Icc (-T) T, HasDerivWithinAt u (A t (u t)) (Icc (-T) T) t)
    (hv : ∀ t ∈ Icc (-T) T, HasDerivWithinAt v (A t (v t)) (Icc (-T) T) t)
    (h0 : u 0 = v 0) : EqOn u v (Icc (-T) T) := by
  intro t ht
  have := norm_le_of_linear (u := fun t => u t - v t) hA
    (fun t ht => by simp only [map_sub]; exact (hu t ht).sub (hv t ht)) t ht
  simp only [h0, sub_self, norm_zero, zero_mul] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- **Continuous dependence on the coefficient.** If `u̇ = A(t) u` and `v̇ = B(t) v` on `[-T, T]`
with the same value at `0`, `‖B‖ ≤ K`, `‖A - B‖ ≤ η` and `‖u‖ ≤ M`, then
`‖u - v‖ ≤ η M T e^{K T}`. -/
theorem norm_sub_le_of_linear {A B : ℝ → F →L[ℝ] F} {u v : ℝ → F} {K η M T : ℝ}
    (hK : 0 ≤ K) (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hB : ∀ t ∈ Icc (-T) T, ‖B t‖ ≤ K) (hAB : ∀ t ∈ Icc (-T) T, ‖A t - B t‖ ≤ η)
    (hu : ∀ t ∈ Icc (-T) T, HasDerivWithinAt u (A t (u t)) (Icc (-T) T) t)
    (huM : ∀ t ∈ Icc (-T) T, ‖u t‖ ≤ M)
    (hv : ∀ t ∈ Icc (-T) T, HasDerivWithinAt v (B t (v t)) (Icc (-T) T) t)
    (h0 : u 0 = v 0) : ∀ t ∈ Icc (-T) T, ‖u t - v t‖ ≤ η * M * T * Real.exp (K * T) := by
  have := norm_le_of_deriv_le (f := fun t => u t - v t) (f' := fun t => A t (u t) - B t (v t))
    (ε := η * M) hK (mul_nonneg hη hM) (fun t ht => (hu t ht).sub (hv t ht)) (by simp [h0])
    (fun t ht => ?_)
  · exact this
  · have h1 : A t (u t) - B t (v t) = B t (u t - v t) + (A t - B t) (u t) := by
      simp [map_sub]
    rw [h1]
    calc ‖B t (u t - v t) + (A t - B t) (u t)‖
        ≤ ‖B t‖ * ‖u t - v t‖ + ‖A t - B t‖ * ‖u t‖ :=
          (norm_add_le _ _).trans (add_le_add ((B t).le_opNorm _) ((A t - B t).le_opNorm _))
      _ ≤ K * ‖u t - v t‖ + η * M :=
          add_le_add (mul_le_mul_of_nonneg_right (hB t ht) (norm_nonneg _))
            (mul_le_mul (hAB t ht) (huM t ht) (norm_nonneg _) hη)

/-- **Short-time existence for a linear equation.** If `A` is continuous on `[-T, T]` with
`‖A‖ ≤ K` there and `K T ≤ 1/2`, then `u̇ = A(t) u` has a solution on `[-T, T]` with `u 0 = u₀`.

The restriction `K T ≤ 1/2` comes from Mathlib's Picard–Lindelöf theorem, which is stated on a
ball; linear equations have global solutions, but that is not needed here. -/
theorem exists_linear_solution [CompleteSpace F] {A : ℝ → F →L[ℝ] F} {K : ℝ≥0} {T : ℝ}
    (hT : 0 ≤ T) (hKT : K * T ≤ 1 / 2) (hA : ContinuousOn A (Icc (-T) T))
    (hK : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ K) (u₀ : F) :
    ∃ u : ℝ → F, u 0 = u₀ ∧
      ∀ t ∈ Icc (-T) T, HasDerivWithinAt u (A t (u t)) (Icc (-T) T) t := by
  set a : ℝ≥0 := ‖u₀‖₊ + 1 with ha
  set L : ℝ≥0 := K * (‖u₀‖₊ + a) with hL
  have h0mem : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hPL : IsPicardLindelof (fun t u => A t u) (tmin := -T) (tmax := T) ⟨0, h0mem⟩ u₀ a 0 L K := by
    refine ⟨fun t ht => ?_, fun u _ => ?_, fun t ht u hu => ?_, ?_⟩
    · refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x y => ?_)
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _))
    · exact hA.clm_apply continuousOn_const
    · have hu' : ‖u‖ ≤ ‖u₀‖ + a := by
        have := mem_closedBall_iff_norm.1 hu
        calc ‖u‖ = ‖(u - u₀) + u₀‖ := by simp
          _ ≤ ‖u - u₀‖ + ‖u₀‖ := norm_add_le _ _
          _ ≤ ‖u₀‖ + a := by linarith
      calc ‖A t u‖ ≤ ‖A t‖ * ‖u‖ := (A t).le_opNorm _
        _ ≤ K * (‖u₀‖ + a) := mul_le_mul (hK t ht) hu' (norm_nonneg _) K.2
        _ = L := by simp [hL]
    · have hmax : max (T - (0 : ℝ)) ((0 : ℝ) - -T) = T := by simp
      show (L : ℝ) * max (T - (0 : ℝ)) ((0 : ℝ) - -T) ≤ (a : ℝ) - ((0 : ℝ≥0) : ℝ)
      rw [hmax]
      have h1 : (L : ℝ) * T = (K * T) * (‖u₀‖ + a) := by simp [hL]; ring
      have h2 : (a : ℝ) = ‖u₀‖ + 1 := by simp [ha]
      have h3 : (K : ℝ) * T * (‖u₀‖ + a) ≤ 1 / 2 * (‖u₀‖ + a) :=
        mul_le_mul_of_nonneg_right hKT (by positivity)
      rw [h1]
      simp only [NNReal.coe_zero, sub_zero]
      nlinarith [norm_nonneg u₀]
  obtain ⟨u, hu0, hu⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨u, hu0, hu⟩

end Linear

end Lightlike.ODE
