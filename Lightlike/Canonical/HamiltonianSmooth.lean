import Mathlib
import Lightlike.Canonical.SmoothDensity
import Lightlike.Canonical.DensityCovariance
import Lightlike.Canonical.ParamIntegral

/-!
# The Hamiltonian density as a smooth function of jets, and its derivative under the integral

`Phi c ((H, P), J) = kinJ c H P − √det H · Rjet J` is `C^∞` where `det H > 0` and the metric of `J` is invertible, and
the Hamiltonian density of a smooth metric `g` at `x` is `Phi` of the jet data `Zpt g π x`. Along `g + t k` the data
move on a line `Z + t V`. So the density is jointly smooth in `(t, x)`, and the derivative of the smeared constraint
along a compactly supported variation `k` can be taken under the integral (`dirDeriv_hamiltonianConstraint`).
-/

open Matrix MeasureTheory Metric Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- The Hamiltonian density as a function of the jet data `((H, P), J)`. -/
def Phi (c : ℝ) (W : Arr d × Jet d) : ℝ :=
  Kfun c W.1 - Real.sqrt (Matrix.of W.1.1).det * Rjet W.2

/-- The jet data of `(g, π)` at `x`. -/
def Zpt (g π : TensorField d) (x : Fin d → ℝ) : Arr d × Jet d :=
  (((fun a b => g x a b, fun a b => π x a b) : Arr d), jetAt g x)

lemma hamiltonianDensity_eq_Phi {g π : TensorField d} (hg : SmoothTensor g) {x : Fin d → ℝ}
    (hH : 0 < (g x).det) :
    hamiltonianDensity g π x = Phi (1 / ((d : ℝ) - 1)) (Zpt g π x) := by
  unfold hamiltonianDensity Phi Zpt
  rw [scalarCurvature_eq_Rjet hg hH.ne', kineticDensity_eq_kinJ]
  rfl

lemma contDiffAt_Phi (c : ℝ) {W : Arr d × Jet d} (hH : 0 < (Matrix.of W.1.1).det)
    (hJ : (Matrix.of W.2.1).det ≠ 0) : ContDiffAt ℝ ∞ (Phi c) W := by
  have h1 : ∀ i j, ContDiffAt ℝ ∞ (fun W : Arr d × Jet d => (Matrix.of W.1.1) i j) W := fun i j => by
    simp only [Matrix.of_apply]; fun_prop
  have hK : ContDiffAt ℝ ∞ (fun W : Arr d × Jet d => Kfun c W.1) W :=
    (contDiffAt_Kfun c hH).comp W contDiffAt_fst
  have hs : ContDiffAt ℝ ∞ (fun W : Arr d × Jet d => Real.sqrt (Matrix.of W.1.1).det) W :=
    (contDiffAt_det (fun W : Arr d × Jet d => Matrix.of W.1.1) h1).sqrt hH.ne'
  have hR : ContDiffAt ℝ ∞ (fun W : Arr d × Jet d => Rjet W.2) W :=
    (contDiffAt_Rjet hJ).comp W contDiffAt_snd
  exact hK.sub (hs.mul hR)

/-- The direction `V` of the jet data along the line `h + t k`. -/
def Vdir (k : TensorField d) (x : Fin d → ℝ) : Arr d × Jet d :=
  (((fun a b => k x a b, fun _ _ => 0) : Arr d), jetAt k x)

lemma Zpt_add_smul {h k π : TensorField d} (hh : SmoothTensor h) (hk : SmoothTensor k) (t : ℝ)
    (x : Fin d → ℝ) : Zpt (fun y => h y + t • k y) π x = Zpt h π x + t • Vdir k x := by
  unfold Zpt Vdir
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a b; simp
  · funext a b; simp
  · exact jetAt_add_smul hh hk t x

/-- **A uniform `ε`**: for a compactly supported `k`, `h + t k` is invertible everywhere for small `t`. -/
lemma exists_eps_det {h k : TensorField d} (hh : SmoothTensor h) (hpos : ∀ y, (h y).PosDef)
    (hkc : ∀ i j, HasCompactSupport (fun x => k x i j)) (hk : SmoothTensor k) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x, 0 < (h x + t • k x).det := by
  set S : Set (Fin d → ℝ) := ⋃ i, ⋃ j, tsupport (fun x => k x i j) with hS
  have hSc : IsCompact S := isCompact_iUnion fun i => isCompact_iUnion fun j => hkc i j
  have hout : ∀ x, x ∉ S → ∀ t : ℝ, k x = 0 := by
    intro x hx t
    ext i j
    have : x ∉ tsupport (fun x => k x i j) := fun hxx => hx (by simp only [hS, mem_iUnion]; exact ⟨i, j, hxx⟩)
    simpa using image_eq_zero_of_notMem_tsupport this
  have hcont : Continuous (fun p : ℝ × (Fin d → ℝ) => (h p.2 + p.1 • k p.2).det) := by
    refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((hh i j).continuous.comp continuous_snd).add (continuous_fst.mul ((hk i j).continuous.comp continuous_snd))
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ S, 0 < (h x + t • k x).det := by
    refine hSc.eventually_forall_of_forall_eventually (P := fun t x => 0 < (h x + t • k x).det) ?_
    intro x _
    have h0 : 0 < (h x + (0 : ℝ) • k x).det := by simpa using (hpos x).det_pos
    exact (hcont.continuousAt (x := ((0 : ℝ), x))).eventually (lt_mem_nhds (by simpa using h0))
  obtain ⟨ε, hε, hεt⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun t ht x => ?_⟩
  by_cases hx : x ∈ S
  · exact hεt (by simpa [Real.dist_eq] using ht) x hx
  · rw [hout x hx t]; simpa using (hpos x).det_pos

lemma continuous_Zpt {h π : TensorField d} (hh : SmoothTensor h) (hπ : ∀ i j, Continuous (fun x => π x i j)) :
    Continuous (fun x => Zpt h π x) := by
  have hj : Continuous (fun x : Fin d → ℝ => jetAt h x) := (differentiable_jetAt hh).continuous
  refine Continuous.prodMk (Continuous.prodMk ?_ ?_) hj
  · exact continuous_pi fun a => continuous_pi fun b => (hh a b).continuous
  · exact continuous_pi fun a => continuous_pi fun b => hπ a b

lemma continuous_Vdir {k : TensorField d} (hk : SmoothTensor k) : Continuous (fun x => Vdir k x) := by
  have hj : Continuous (fun x : Fin d → ℝ => jetAt k x) := (differentiable_jetAt hk).continuous
  refine Continuous.prodMk (Continuous.prodMk ?_ continuous_const) hj
  exact continuous_pi fun a => continuous_pi fun b => (hk a b).continuous

lemma Wt_det {h k π : TensorField d} (t : ℝ) (x : Fin d → ℝ) :
    Matrix.of (Zpt h π x + t • Vdir k x).1.1 = h x + t • k x ∧
      Matrix.of (Zpt h π x + t • Vdir k x).2.1 = h x + t • k x := by
  constructor <;> (ext a b; simp [Zpt, Vdir, jetAt])

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Differentiation of the smeared Hamiltonian constraint along a compactly supported variation**:
`d/dt H[N](h + t k, π) = ∫ N · (derivative of the density)`. -/
theorem dirDeriv_hamiltonianConstraint {N : (Fin d → ℝ) → ℝ} (hN : ContDiff ℝ ∞ N) (hNc : HasCompactSupport N)
    {h π k : TensorField d} (hh : SmoothTensor h) (hpos : ∀ y, (h y).PosDef)
    (hπ : ∀ i j, Continuous (fun x => π x i j)) (hk : SmoothTensor k)
    (hkc : ∀ i j, HasCompactSupport (fun x => k x i j)) :
    Integrable (fun x => N x * hamDirDeriv h π k x) volume ∧
      dirDeriv (hamiltonianConstraint N) h π k 0 = ∫ x, N x * hamDirDeriv h π k x := by
  set c : ℝ := 1 / ((d : ℝ) - 1) with hc
  obtain ⟨ε, hε, hεdet⟩ := exists_eps_det hh hpos hkc hk
  -- the smoothness of `Phi` along the line
  have hΦ : ∀ t : ℝ, |t| < ε → ∀ x, ContDiffAt ℝ ∞ (Phi c) (Zpt h π x + t • Vdir k x) := by
    intro t ht x
    have hd := hεdet t ht x
    obtain ⟨e1, e2⟩ := Wt_det (h := h) (k := k) (π := π) t x
    exact contDiffAt_Phi c (by rw [e1]; exact hd) (by rw [e2]; exact hd.ne')
  have hD : ∀ t : ℝ, |t| < ε → ∀ x, hamiltonianDensity (fun y => h y + t • k y) π x =
      Phi c (Zpt h π x + t • Vdir k x) := by
    intro t ht x
    rw [hamiltonianDensity_eq_Phi (smoothTensor_add_smul hh hk t) (hεdet t ht x), Zpt_add_smul hh hk t x]
  -- the integrand and its derivative
  set F : ℝ → (Fin d → ℝ) → ℝ := fun t x => N x * Phi c (Zpt h π x + t • Vdir k x) with hF
  set F' : ℝ → (Fin d → ℝ) → ℝ := fun t x =>
    N x * fderiv ℝ (Phi c) (Zpt h π x + t • Vdir k x) (Vdir k x) with hF'
  have hline : ∀ (t : ℝ) (x : Fin d → ℝ), HasDerivAt (fun s : ℝ => Zpt h π x + s • Vdir k x) (Vdir k x) t := by
    intro t x
    have := ((hasDerivAt_id t).smul_const (Vdir k x)).const_add (Zpt h π x)
    exact HasDerivAt.congr_deriv this (by simp)
  have hderiv : ∀ t ∈ ball (0 : ℝ) ε, ∀ x, HasDerivAt (fun s => F s x) (F' t x) t := by
    intro t ht x
    have ht' : |t| < ε := by simpa [Real.dist_eq] using mem_ball.mp ht
    have := ((hΦ t ht' x).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hline t x)
    exact this.const_mul (N x)
  have hzero : ∀ t x, x ∉ tsupport N → F t x = 0 ∧ F' t x = 0 := by
    intro t x hx
    have : N x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hF, hF', this]
  have hcZ : ∀ t : ℝ, Continuous (fun x => Zpt h π x + t • Vdir k x) := fun t =>
    (continuous_Zpt hh hπ).add ((continuous_Vdir hk).const_smul t)
  have hFc : ∀ t ∈ ball (0 : ℝ) ε, Continuous (F t) := by
    intro t ht
    have ht' : |t| < ε := by simpa [Real.dist_eq] using mem_ball.mp ht
    refine continuous_iff_continuousAt.mpr fun x => ?_
    exact hN.continuous.continuousAt.mul (ContinuousAt.comp (g := Phi c) (f := fun x => Zpt h π x + t • Vdir k x) (hΦ t ht' x).continuousAt
      (hcZ t).continuousAt)
  have hF'c : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F' p.1 p.2) (closedBall (0 : ℝ) (ε / 2) ×ˢ univ) := by
    intro p hp
    have ht : |p.1| < ε := by
      have := mem_closedBall.mp hp.1
      rw [Real.dist_eq, sub_zero] at this
      linarith
    refine ContinuousAt.continuousWithinAt ?_
    have hW : Continuous (fun q : ℝ × (Fin d → ℝ) => Zpt h π q.2 + q.1 • Vdir k q.2) :=
      ((continuous_Zpt hh hπ).comp continuous_snd).add (continuous_fst.smul ((continuous_Vdir hk).comp continuous_snd))
    have hfd : ContinuousAt (fun q : ℝ × (Fin d → ℝ) => fderiv ℝ (Phi c) (Zpt h π q.2 + q.1 • Vdir k q.2)) p := by
      have h1 : ContinuousAt (fderiv ℝ (Phi c)) (Zpt h π p.2 + p.1 • Vdir k p.2) :=
        ((hΦ p.1 ht p.2).fderiv_right (m := 0) (by simp)).continuousAt
      exact ContinuousAt.comp (g := fderiv ℝ (Phi c))
        (f := fun q : ℝ × (Fin d → ℝ) => Zpt h π q.2 + q.1 • Vdir k q.2) h1 hW.continuousAt
    have hV : Continuous (fun q : ℝ × (Fin d → ℝ) => Vdir k q.2) := (continuous_Vdir hk).comp continuous_snd
    exact (hN.continuous.comp continuous_snd).continuousAt.mul (hfd.clm_apply hV.continuousAt)
  have hDI := hasDerivAt_integral_compact (F := F) (F' := F') (K := tsupport N) hNc hε hzero hderiv hFc hF'c
  -- identification of the derivative of the density
  have hid : ∀ x, fderiv ℝ (Phi c) (Zpt h π x) (Vdir k x) = hamDirDeriv h π k x := by
    intro x
    have hH : 0 < (h x).det := (hpos x).det_pos
    have h0 : HasDerivAt (fun s : ℝ => Phi c (Zpt h π x + s • Vdir k x)) (fderiv ℝ (Phi c) (Zpt h π x) (Vdir k x)) 0 := by
      have := ((hΦ 0 (by simpa using hε) x).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline 0 x)
      refine HasDerivAt.congr_deriv this ?_
      simp
    have h1 := hasDerivAt_hamiltonianDensity_dir (π := π) hh hk hH
    have hev : (fun s : ℝ => hamiltonianDensity (fun y => h y + s • k y) π x) =ᶠ[𝓝 (0 : ℝ)]
        fun s => Phi c (Zpt h π x + s • Vdir k x) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with s hs
      exact hD s (by simpa [Real.dist_eq] using mem_ball.mp hs) x
    exact h0.unique (h1.congr_of_eventuallyEq hev.symm)
  -- the integral
  have hint : ∀ᶠ t in 𝓝 (0 : ℝ), hamiltonianConstraint N (fun x => h x + t • k x) π = ∫ x, F t x := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    have ht' : |t| < ε := by simpa [Real.dist_eq] using mem_ball.mp ht
    unfold hamiltonianConstraint
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF]
    rw [← hD t ht' x]
  have hDD : HasDerivAt (fun t : ℝ => hamiltonianConstraint N (fun x => h x + t • k x) π) (∫ x, F' 0 x) 0 :=
    hDI.2.congr_of_eventuallyEq hint
  have hF'eq : ∀ x, F' 0 x = N x * hamDirDeriv h π k x := fun x => by
    simp only [hF']
    rw [zero_smul, add_zero, hid x]
  refine ⟨?_, ?_⟩
  · have h1 : F' 0 = fun x => N x * hamDirDeriv h π k x := funext hF'eq
    have := hDI.1
    rwa [h1] at this
  unfold dirDeriv
  simp only [Pi.zero_apply, smul_zero, add_zero]
  rw [hDD.deriv]
  exact integral_congr_ae (Filter.Eventually.of_forall hF'eq)

end Lightlike.Canonical

end
