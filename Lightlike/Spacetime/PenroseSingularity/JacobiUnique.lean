import Lightlike.Spacetime.PenroseSingularity.JacobiAffine
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Local uniqueness of Jacobi fields (G1-012, step D4)

A Jacobi field with vanishing value and covariant derivative at a point vanishes near it. The Jacobi equation is a
linear first-order system `(J, P)' = A (t) (J, P)` with continuous coefficients, so this is Picard–Lindelöf
uniqueness.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

open Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- A coarse bound on the Christoffel contraction. -/
theorem norm_gammaApply_le (x v u : Fin n → ℝ) :
    ‖gammaApply g x v u‖ ≤ (∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k x|) * ‖v‖ * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [gammaApply, Real.norm_eq_abs]
  calc |∑ j, ∑ k, Lightlike.christoffel g i j k x * v j * u k|
      ≤ ∑ j, ∑ k, |Lightlike.christoffel g i j k x| * ‖v‖ * ‖u‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul, abs_mul]
        have hv : |v j| ≤ ‖v‖ := by simpa using norm_le_pi_norm v j
        have hu : |u k| ≤ ‖u‖ := by simpa using norm_le_pi_norm u k
        gcongr
    _ ≤ (∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k x|) * ‖v‖ * ‖u‖ := by
        have : ∑ j, ∑ k, |Lightlike.christoffel g i j k x| * ‖v‖ * ‖u‖ =
            (∑ j, ∑ k, |Lightlike.christoffel g i j k x|) * ‖v‖ * ‖u‖ := by
          simp only [Finset.sum_mul]
        rw [this]
        have h1 : ∑ j, ∑ k, |Lightlike.christoffel g i j k x| ≤
            ∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k x| :=
          Finset.single_le_sum (f := fun i => ∑ j, ∑ k, |Lightlike.christoffel g i j k x|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (Finset.mem_univ i)
        gcongr

/-- A coarse bound on the curvature contraction. -/
theorem norm_riemannApply_le (x w J : Fin n → ℝ) :
    ‖riemannApply g x w J‖ ≤ (∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν x|) * ‖w‖ * ‖J‖ * ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [riemannApply, Real.norm_eq_abs]
  have hw : ∀ k, |w k| ≤ ‖w‖ := fun k => by simpa using norm_le_pi_norm w k
  have hJ : ∀ k, |J k| ≤ ‖J‖ := fun k => by simpa using norm_le_pi_norm J k
  calc |∑ σ, ∑ μ, ∑ ν, Lightlike.riemann g i σ μ ν x * w σ * J μ * w ν|
      ≤ ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν x| * ‖w‖ * ‖J‖ * ‖w‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
        rw [abs_mul, abs_mul, abs_mul]
        gcongr
        · exact hw σ
        · exact hJ μ
        · exact hw ν
    _ ≤ (∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν x|) * ‖w‖ * ‖J‖ * ‖w‖ := by
        have : ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν x| * ‖w‖ * ‖J‖ * ‖w‖ =
            (∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν x|) * ‖w‖ * ‖J‖ * ‖w‖ := by
          simp only [Finset.sum_mul]
        rw [this]
        have h1 : ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν x| ≤
            ∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν x| :=
          Finset.single_le_sum (f := fun i => ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν x|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
              abs_nonneg _) (Finset.mem_univ i)
        gcongr

theorem gammaApply_sub_right (x v u u' : Fin n → ℝ) :
    gammaApply g x v (u - u') = gammaApply g x v u - gammaApply g x v u' := by
  funext i
  simp [gammaApply, mul_sub, Finset.sum_sub_distrib]

theorem riemannApply_sub_right (x w J K : Fin n → ℝ) :
    riemannApply g x w (J - K) = riemannApply g x w J - riemannApply g x w K := by
  funext i
  simp only [riemannApply, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- The Jacobi system as a vector field on `(J, P)`. -/
def jacSystem (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) (y : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (y.2 - gammaApply g x w y.1, -gammaApply g x w y.2 - riemannApply g x w y.1)

/-- The Jacobi system is additive. -/
theorem jacSystem_sub (x w : Fin n → ℝ) (y y' : (Fin n → ℝ) × (Fin n → ℝ)) :
    jacSystem g x w y - jacSystem g x w y' = jacSystem g x w (y - y') := by
  simp only [jacSystem, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk, gammaApply_sub_right, riemannApply_sub_right]
  refine Prod.ext ?_ ?_ <;> simp <;> abel

/-- The Jacobi system is bounded by a constant multiple. -/
theorem norm_jacSystem_le (x w : Fin n → ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ‖jacSystem g x w z‖ ≤ (1 + (∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k x|) * ‖w‖ +
      (∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν x|) * ‖w‖ * ‖w‖) * ‖z‖ := by
  set cG := ∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k x| with hcG
  set cR := ∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν x| with hcR
  have hcG0 : 0 ≤ cG := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    abs_nonneg _
  have hcR0 : 0 ≤ cR := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have h2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  have hw0 := norm_nonneg w
  have hz0 := norm_nonneg z
  have e1 : ‖z.2 - gammaApply g x w z.1‖ ≤ (1 + cG * ‖w‖ + cR * ‖w‖ * ‖w‖) * ‖z‖ := by
    calc ‖z.2 - gammaApply g x w z.1‖ ≤ ‖z.2‖ + ‖gammaApply g x w z.1‖ := norm_sub_le _ _
      _ ≤ ‖z‖ + cG * ‖w‖ * ‖z.1‖ := by
          have := norm_gammaApply_le (g := g) x w z.1
          linarith
      _ ≤ (1 + cG * ‖w‖ + cR * ‖w‖ * ‖w‖) * ‖z‖ := by
          have : cG * ‖w‖ * ‖z.1‖ ≤ cG * ‖w‖ * ‖z‖ := by gcongr
          nlinarith [mul_nonneg (mul_nonneg hcR0 hw0) hw0, mul_nonneg (mul_nonneg hcR0 hw0) hw0]
  have e2 : ‖-gammaApply g x w z.2 - riemannApply g x w z.1‖ ≤ (1 + cG * ‖w‖ + cR * ‖w‖ * ‖w‖) * ‖z‖ := by
    calc ‖-gammaApply g x w z.2 - riemannApply g x w z.1‖ ≤ ‖gammaApply g x w z.2‖ + ‖riemannApply g x w z.1‖ := by
          rw [sub_eq_add_neg]
          calc _ ≤ ‖-gammaApply g x w z.2‖ + ‖-riemannApply g x w z.1‖ := norm_add_le _ _
            _ = _ := by simp
      _ ≤ cG * ‖w‖ * ‖z‖ + cR * ‖w‖ * ‖w‖ * ‖z‖ := by
          have a1 := norm_gammaApply_le (g := g) x w z.2
          have a2 := norm_riemannApply_le (g := g) x w z.1
          have b1 : cG * ‖w‖ * ‖z.2‖ ≤ cG * ‖w‖ * ‖z‖ := by gcongr
          have b2 : cR * ‖w‖ * ‖z.1‖ * ‖w‖ ≤ cR * ‖w‖ * ‖z‖ * ‖w‖ := by gcongr
          nlinarith
      _ ≤ (1 + cG * ‖w‖ + cR * ‖w‖ * ‖w‖) * ‖z‖ := by nlinarith
  show max ‖z.2 - gammaApply g x w z.1‖ ‖-gammaApply g x w z.2 - riemannApply g x w z.1‖ ≤ _
  exact max_le e1 e2

/-- **Local uniqueness of Jacobi fields.** A Jacobi field whose value and covariant derivative vanish at `a`
vanishes near `a`. -/
theorem IsJacobiOn.eventually_zero (hg : Lightlike.IsCoordMetric g U) {γ w J P : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hJ : IsJacobiOn g γ w J P I) (hIo : IsOpen I) {a : ℝ} (ha : a ∈ I) (hγU : ∀ t ∈ I, γ t ∈ U)
    (hJa : J a = 0) (hPa : P a = 0) : ∀ᶠ t in 𝓝 a, J t = 0 ∧ P t = 0 := by
  have hnhds : I ∈ 𝓝 a := hIo.mem_nhds ha
  -- continuity of the coefficients at `a`
  have hγd : ∀ t ∈ I, HasDerivAt γ (w t) t := fun t ht => hJ.geodesic.1 t ht
  have hwd : ∀ t ∈ I, HasDerivAt w (accel g (γ t) (w t)) t := fun t ht => hJ.geodesic.2 t ht
  have hγc : ContinuousAt γ a := (hγd a ha).continuousAt
  have hwc : ContinuousAt w a := (hwd a ha).continuousAt
  have hU : U ∈ 𝓝 (γ a) := hg.isOpen.mem_nhds (hγU a ha)
  have hchr : ∀ i j k, ContinuousAt (fun t => |Lightlike.christoffel g i j k (γ t)|) a := fun i j k =>
    ContinuousAt.abs (ContinuousAt.comp (g := Lightlike.christoffel g i j k)
      ((hg.contDiffOn_christoffel i j k).continuousOn.continuousAt hU) hγc)
  have hrie : ∀ i σ μ ν, ContinuousAt (fun t => |Lightlike.riemann g i σ μ ν (γ t)|) a := fun i σ μ ν =>
    ContinuousAt.abs (ContinuousAt.comp (g := Lightlike.riemann g i σ μ ν)
      ((hg.contDiffOn_riemann i σ μ ν).continuousOn.continuousAt hU) hγc)
  have hcG : ContinuousAt (fun t => ∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k (γ t)|) a :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ => hchr i j k
  have hcR : ContinuousAt (fun t => ∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν (γ t)|) a :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun σ _ => tendsto_finsetSum _ fun μ _ =>
      tendsto_finsetSum _ fun ν _ => hrie i σ μ ν
  have hwn : ContinuousAt (fun t => ‖w t‖) a := hwc.norm
  -- the uniform Lipschitz constant
  set K : ℝ := 1 + ((∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k (γ a)|) + 1) * (‖w a‖ + 1) +
    ((∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν (γ a)|) + 1) * (‖w a‖ + 1) * (‖w a‖ + 1) with hK
  have hKnn : 0 ≤ K := by positivity
  have hbd : ∀ᶠ t in 𝓝 a,
      (∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k (γ t)|) < (∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k (γ a)|) + 1 ∧
      (∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν (γ t)|) < (∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν (γ a)|) + 1 ∧
      ‖w t‖ < ‖w a‖ + 1 :=
    (hcG.eventually (gt_mem_nhds (by linarith))).and ((hcR.eventually (gt_mem_nhds (by linarith))).and
      (hwn.eventually (gt_mem_nhds (by linarith))))
  have hlip : ∀ᶠ t in 𝓝 a, LipschitzOnWith (Real.toNNReal K) (jacSystem g (γ t) (w t)) univ := by
    filter_upwards [hbd] with t ⟨h1, h2, h3⟩
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun y y' => ?_)
    rw [dist_eq_norm, dist_eq_norm, jacSystem_sub, Real.coe_toNNReal _ hKnn]
    refine (norm_jacSystem_le _ _ _).trans ?_
    have hw0 := norm_nonneg (w t)
    have hcG0 : 0 ≤ ∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k (γ t)| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hcR0 : 0 ≤ ∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν (γ t)| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [hK]
    have e1 : (∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k (γ t)|) * ‖w t‖ ≤
        ((∑ i, ∑ j, ∑ k, |Lightlike.christoffel g i j k (γ a)|) + 1) * (‖w a‖ + 1) := by gcongr
    have e2 : (∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν (γ t)|) * ‖w t‖ * ‖w t‖ ≤
        ((∑ i, ∑ σ, ∑ μ, ∑ ν, |Lightlike.riemann g i σ μ ν (γ a)|) + 1) * (‖w a‖ + 1) * (‖w a‖ + 1) := by
      gcongr
    linarith
  have hsol : ∀ᶠ t in 𝓝 a, HasDerivAt (fun t => (J t, P t)) (jacSystem g (γ t) (w t) (J t, P t)) t ∧
      (J t, P t) ∈ (univ : Set _) := by
    filter_upwards [hnhds] with t ht
    refine ⟨?_, mem_univ _⟩
    have h1 := hJ.deriv_field t ht
    have h2 := hJ.deriv_cov t ht
    exact h1.prodMk h2 |>.congr_deriv (by simp [jacSystem])
  have hzero : ∀ᶠ t in 𝓝 a, HasDerivAt (fun _ : ℝ => ((0 : Fin n → ℝ), (0 : Fin n → ℝ)))
      (jacSystem g (γ t) (w t) ((0 : Fin n → ℝ), (0 : Fin n → ℝ))) t ∧
      ((0 : Fin n → ℝ), (0 : Fin n → ℝ)) ∈ (univ : Set _) := by
    refine Filter.Eventually.of_forall fun t => ⟨?_, mem_univ _⟩
    have : jacSystem g (γ t) (w t) ((0 : Fin n → ℝ), (0 : Fin n → ℝ)) = (0, 0) := by
      have hr : riemannApply g (γ t) (w t) (0 : Fin n → ℝ) = 0 := by funext i; simp [riemannApply]
      simp [jacSystem, gammaApply_zero_right, hr]
    rw [this]
    exact hasDerivAt_const t _
  have huniq := ODE_solution_unique_of_eventually (v := fun t => jacSystem g (γ t) (w t)) (s := fun _ => univ)
    (K := Real.toNNReal K) hlip hsol hzero (by simp [hJa, hPa])
  filter_upwards [huniq] with t ht
  exact ⟨congrArg Prod.fst ht, congrArg Prod.snd ht⟩

/-- **A Jacobi field vanishing at `a` whose covariant derivative is parallel to the velocity is a multiple of
the velocity near `a`.** -/
theorem IsJacobiOn.eventually_eq_smul_w (hg : Lightlike.IsCoordMetric g U) {γ w J P : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hJ : IsJacobiOn g γ w J P I) (hIo : IsOpen I) {a : ℝ} (ha : a ∈ I) (hγU : ∀ t ∈ I, γ t ∈ U)
    (hJa : J a = 0) {c : ℝ} (hPa : P a = c • w a) :
    ∀ᶠ t in 𝓝 a, J t = (c * (t - a)) • w t := by
  have hA := IsJacobiOn.affine_w hJ.geodesic (-c * a) c
  have hE := IsJacobiOn.add hJ (IsJacobiOn.smul hA (-1))
  have h0 := IsJacobiOn.eventually_zero hg hE hIo ha hγU (by simp [hJa]) (by simp [hPa])
  filter_upwards [h0] with t ht
  have := ht.1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  have h2 : J t = (c * t + -c * a) • w t := by
    have : J t + (-1 : ℝ) • ((-c * a + c * t) • w t) = 0 := by simpa using this
    rw [neg_one_smul, add_neg_eq_zero] at this
    rw [this]; congr 1; ring
  rw [h2]; congr 1; ring

end Lightlike.Penrose
