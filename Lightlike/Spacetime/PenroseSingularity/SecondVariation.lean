import Lightlike.Spacetime.PenroseSingularity.JacobiIdentity
import Lightlike.Spacetime.PenroseSingularity.JacobiCompat
import Lightlike.Spacetime.PenroseSingularity.JacobiGeom
import Lightlike.Spacetime.PenroseSingularity.FormContinuity
import Lightlike.Spacetime.PenroseSingularity.NegativeJet
import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.Spacetime.ConjugatePoints.JacobiVariation

/-!
# The commutator of covariant derivatives in a chart (G1-012, step D4)

For a two-parameter family `α (s, t)` and a field `X` along it, in a chart the commutator of the covariant
derivatives is the curvature: `D_t D_s X - D_s D_t X = R (∂_t α, ∂_s α) X`. This file proves the algebraic
identity between the jets (`riemS` is the Riemann tensor from the symbols).
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ}

/-- `D_t D_s X` in terms of the jets: `A = α_s`, `B = α_t`, `C = α_{st}`, `X1 = X_s`, `X2 = X_t`, `X12 = X_{st}`. -/
def covDtDs (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (A B C X X1 X2 X12 : Fin n → ℝ) (a : Fin n) : ℝ :=
  (X12 a + ∑ d, ∑ b, ∑ c, dG d a b c * B d * A b * X c + ∑ b, ∑ c, G a b c * C b * X c +
      ∑ b, ∑ c, G a b c * A b * X2 c) +
    ∑ b, ∑ c, G a b c * B b * (X1 c + ∑ d, ∑ e, G c d e * A d * X e)

/-- `D_s D_t X` in terms of the same jets. -/
def covDsDt (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (A B C X X1 X2 X12 : Fin n → ℝ) (a : Fin n) : ℝ :=
  (X12 a + ∑ d, ∑ b, ∑ c, dG d a b c * A d * B b * X c + ∑ b, ∑ c, G a b c * C b * X c +
      ∑ b, ∑ c, G a b c * B b * X1 c) +
    ∑ b, ∑ c, G a b c * A b * (X2 c + ∑ d, ∑ e, G c d e * B d * X e)

/-- **The commutator of covariant derivatives is the curvature.** -/
theorem covDtDs_sub_covDsDt (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (A B C X X1 X2 X12 : Fin n → ℝ) (a : Fin n) :
    covDtDs G dG A B C X X1 X2 X12 a - covDsDt G dG A B C X X1 X2 X12 a =
      ∑ σ, ∑ μ, ∑ ν, riemS G dG a σ μ ν * X σ * B μ * A ν := by
  unfold covDtDs covDsDt riemS
  -- the derivative terms
  have r1 : ∑ σ, ∑ μ, ∑ ν, dG μ a ν σ * X σ * B μ * A ν =
      ∑ d, ∑ b, ∑ c, dG d a b c * B d * A b * X c := by
    rw [sum3_rot]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  have r2 : ∑ σ, ∑ μ, ∑ ν, dG ν a μ σ * X σ * B μ * A ν =
      ∑ d, ∑ b, ∑ c, dG d a b c * A d * B b * X c := by
    rw [sum3_swap23, sum3_swap12, sum3_swap23]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  -- the quadratic terms
  have r3 : ∑ σ, ∑ μ, ∑ ν, (∑ l, G a μ l * G l ν σ) * X σ * B μ * A ν =
      ∑ b, ∑ c, G a b c * B b * ∑ d, ∑ e, G c d e * A d * X e := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [sum3_swap23, sum3_swap12, sum3_swap23]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  have r4 : ∑ σ, ∑ μ, ∑ ν, (∑ l, G a ν l * G l μ σ) * X σ * B μ * A ν =
      ∑ b, ∑ c, G a b c * A b * ∑ d, ∑ e, G c d e * B d * X e := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [sum3_swap23, sum3_swap12, sum3_swap23]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [sum3_rot, sum3_rot]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  have e : ∀ σ μ ν, (dG μ a ν σ - dG ν a μ σ + ∑ l, (G a μ l * G l ν σ - G a ν l * G l μ σ)) * X σ * B μ * A ν =
      dG μ a ν σ * X σ * B μ * A ν - dG ν a μ σ * X σ * B μ * A ν +
        ((∑ l, G a μ l * G l ν σ) * X σ * B μ * A ν - (∑ l, G a ν l * G l μ σ) * X σ * B μ * A ν) := by
    intro σ μ ν
    rw [Finset.sum_sub_distrib]; ring
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => e σ μ ν]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [r1, r2, r3, r4]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

section Jets

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- `covDAlong` is the derivative plus the Christoffel term. -/
theorem covDAlong_eq (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x v W W' : Fin n → ℝ) :
    (fun a => covDAlong g x v W W' a) = W' + Lightlike.Geodesic.gammaApply g x v W := by
  funext a
  simp [covDAlong, Lightlike.Geodesic.gammaApply]

/-- The covariant derivative `D_s Y = Y' + Γ(c, c', Y)` of a field along a curve. -/
def covK (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (c c1 Y Y1 : ℝ → Fin n → ℝ) (s : ℝ) : Fin n → ℝ :=
  Y1 s + Lightlike.Geodesic.gammaApply g (c s) (c1 s) (Y s)

/-- The derivative of `covK`. -/
def covK' (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (c c1 c2 Y Y1 Y2 : ℝ → Fin n → ℝ) (s : ℝ) :
    Fin n → ℝ :=
  Y2 s + (Lightlike.Geodesic.gammaDeriv g (c s) (c1 s) (c1 s) (Y s) +
    Lightlike.Geodesic.gammaApply g (c s) (c2 s) (Y s) + Lightlike.Geodesic.gammaApply g (c s) (c1 s) (Y1 s))

/-- **First derivative** of `s ↦ g(c)(Y, Y)`. -/
theorem hasDerivAt_normK (hg : Lightlike.IsCoordMetric g U) {c c1 Y Y1 : ℝ → Fin n → ℝ} {s : ℝ}
    (hc : HasDerivAt c (c1 s) s) (hY : HasDerivAt Y (Y1 s) s) (hs : c s ∈ U) :
    HasDerivAt (fun r => gpairAt g (c r) (Y r) (Y r)) (2 * gpairAt g (c s) (covK g c c1 Y Y1 s) (Y s)) s := by
  have h := hasDerivAt_gpair hg hc hs hY hY
  refine h.congr_deriv ?_
  rw [gpairAt_symm hg hs (Y s)]
  have e : (fun a => covDAlong g (c s) (c1 s) (Y s) (Y1 s) a) = covK g c c1 Y Y1 s := by
    rw [covDAlong_eq]; rfl
  rw [e]; ring

/-- The derivative of `covK`. -/
theorem hasDerivAt_covK (hg : Lightlike.IsCoordMetric g U) {c c1 c2 Y Y1 Y2 : ℝ → Fin n → ℝ} {s : ℝ}
    (hc : HasDerivAt c (c1 s) s) (hc1 : HasDerivAt c1 (c2 s) s) (hY : HasDerivAt Y (Y1 s) s)
    (hY1 : HasDerivAt Y1 (Y2 s) s) (hs : c s ∈ U) :
    HasDerivAt (covK g c c1 Y Y1) (covK' g c c1 c2 Y Y1 Y2 s) s := by
  have hch : ∀ i j k, DifferentiableAt ℝ (Lightlike.christoffel g i j k) (c s) := fun i j k =>
    ((hg.contDiffOn_christoffel i j k).contDiffAt (hg.isOpen.mem_nhds hs)).differentiableAt (by simp)
  have hG := Lightlike.Geodesic.hasDerivAt_gammaApply (g := g) hch hc hc1 hY
  have := hY1.fun_add hG
  refine this.congr_deriv ?_
  unfold covK'
  abel

/-- **Second derivative** of `s ↦ g(c)(Y, Y)`: `f''/2 = g(K' + Γ(c', K), Y) + g(K, K)`. -/
theorem hasDerivAt_normK_second (hg : Lightlike.IsCoordMetric g U) {c c1 c2 Y Y1 Y2 : ℝ → Fin n → ℝ} {s : ℝ}
    (hc : HasDerivAt c (c1 s) s) (hc1 : HasDerivAt c1 (c2 s) s) (hY : HasDerivAt Y (Y1 s) s)
    (hY1 : HasDerivAt Y1 (Y2 s) s) (hs : c s ∈ U) :
    HasDerivAt (fun r => 2 * gpairAt g (c r) (covK g c c1 Y Y1 r) (Y r))
      (2 * (gpairAt g (c s) (covK' g c c1 c2 Y Y1 Y2 s +
            Lightlike.Geodesic.gammaApply g (c s) (c1 s) (covK g c c1 Y Y1 s)) (Y s) +
        gpairAt g (c s) (covK g c c1 Y Y1 s) (covK g c c1 Y Y1 s))) s := by
  have h := hasDerivAt_gpair hg hc hs (hasDerivAt_covK hg hc hc1 hY hY1 hs) hY
  refine (h.const_mul 2).congr_deriv ?_
  have e1 : (fun a => covDAlong g (c s) (c1 s) (covK g c c1 Y Y1 s) (covK' g c c1 c2 Y Y1 Y2 s) a) =
      covK' g c c1 c2 Y Y1 Y2 s + Lightlike.Geodesic.gammaApply g (c s) (c1 s) (covK g c c1 Y Y1 s) :=
    covDAlong_eq g _ _ _ _
  have e2 : (fun a => covDAlong g (c s) (c1 s) (Y s) (Y1 s) a) = covK g c c1 Y Y1 s := by
    rw [covDAlong_eq]; rfl
  rw [e1, e2]

/-- `gammaDeriv` is continuous in all of its arguments (the metric is smooth on `U`). -/
theorem continuousAt_gammaDeriv (hg : Lightlike.IsCoordMetric g U) {α : Type*} [TopologicalSpace α]
    {x y v u : α → Fin n → ℝ} {a : α} (hx : ContinuousAt x a) (hy : ContinuousAt y a)
    (hv : ContinuousAt v a) (hu : ContinuousAt u a) (hxU : x a ∈ U) :
    ContinuousAt (fun s => Lightlike.Geodesic.gammaDeriv g (x s) (y s) (v s) (u s)) a := by
  rw [continuousAt_pi]
  intro i
  unfold Lightlike.Geodesic.gammaDeriv
  have key : ∀ p q : Fin n, ContinuousAt (fun s => fderiv ℝ (Lightlike.christoffel g i p q) (x s) (y s) * v s p * u s q) a :=
    fun p q => by
      have hd : ContDiffOn ℝ ∞ (fun z => fderiv ℝ (Lightlike.christoffel g i p q) z) U := by
        have h := hg.contDiffOn_christoffel i p q
        exact (h.fderiv_of_isOpen hg.isOpen (by simp))
      have hc : ContinuousAt (fun z => fderiv ℝ (Lightlike.christoffel g i p q) z) (x a) :=
        hd.continuousOn.continuousAt (hg.isOpen.mem_nhds hxU)
      have h1 : ContinuousAt (fun s => fderiv ℝ (Lightlike.christoffel g i p q) (x s) (y s)) a :=
        (hc.comp hx).clm_apply hy
      exact (h1.mul ((continuous_apply p).continuousAt.comp hv)).mul ((continuous_apply q).continuousAt.comp hu)
  exact tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ => key p q

/-- The second-order coefficient `g(K' + Γ(c', K), Y) + g(K, K)` of `g(α)(α_t, α_t)` at `(s, t)`. -/
def coeffK (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (c c1 c2 Y Y1 Y2 : ℝ → ℝ → Fin n → ℝ) (s t : ℝ) : ℝ :=
  gpairAt g (c s t) (covK' g (fun r => c r t) (fun r => c1 r t) (fun r => c2 r t) (fun r => Y r t)
      (fun r => Y1 r t) (fun r => Y2 r t) s +
    Lightlike.Geodesic.gammaApply g (c s t) (c1 s t) (Y1 s t + Lightlike.Geodesic.gammaApply g (c s t) (c1 s t) (Y s t)))
    (Y s t) + gpairAt g (c s t) (Y1 s t + Lightlike.Geodesic.gammaApply g (c s t) (c1 s t) (Y s t))
      (Y1 s t + Lightlike.Geodesic.gammaApply g (c s t) (c1 s t) (Y s t))

/-- **Local uniform negativity.** Near `(0, t₀)`, if the first jet in `s` of `g(α)(α_t, α_t)` vanishes for all
`t` and the second-order coefficient is negative at `(0, t₀)`, then `g(α)(α_t, α_t) < 0` for `0 < |s|` small and `t`
near `t₀`. -/
theorem uniform_neg_local (hg : Lightlike.IsCoordMetric g U) {c c1 c2 Y Y1 Y2 : ℝ → ℝ → Fin n → ℝ}
    {V : Set (ℝ × ℝ)} {t₀ : ℝ} (hVt : V ∈ 𝓝 ((0 : ℝ), t₀))
    (hc : ∀ p ∈ V, HasDerivAt (fun r => c r p.2) (c1 p.1 p.2) p.1)
    (hc1 : ∀ p ∈ V, HasDerivAt (fun r => c1 r p.2) (c2 p.1 p.2) p.1)
    (hY : ∀ p ∈ V, HasDerivAt (fun r => Y r p.2) (Y1 p.1 p.2) p.1)
    (hY1 : ∀ p ∈ V, HasDerivAt (fun r => Y1 r p.2) (Y2 p.1 p.2) p.1)
    (hcU : ∀ p ∈ V, c p.1 p.2 ∈ U)
    (hcont : ContinuousAt (fun p : ℝ × ℝ => (c p.1 p.2, c1 p.1 p.2, Y p.1 p.2, Y1 p.1 p.2)) (0, t₀))
    (hcont2 : ContinuousAt (fun p : ℝ × ℝ => (c2 p.1 p.2, Y2 p.1 p.2)) (0, t₀))
    (h0 : ∀ᶠ t in 𝓝 t₀, gpairAt g (c 0 t) (Y 0 t) (Y 0 t) = 0)
    (h0' : ∀ᶠ t in 𝓝 t₀, gpairAt g (c 0 t) (Y1 0 t + Lightlike.Geodesic.gammaApply g (c 0 t) (c1 0 t) (Y 0 t))
      (Y 0 t) = 0)
    (hneg : coeffK g c c1 c2 Y Y1 Y2 0 t₀ < 0) :
    ∃ δ > 0, ∃ ε > 0, ∀ t, |t - t₀| < ε → ∀ s, |s| < δ → s ≠ 0 →
      gpairAt g (c s t) (Y s t) (Y s t) < 0 := by
  classical
  -- continuity of the coefficient at `(0, t₀)`
  have hC : ContinuousAt (fun p : ℝ × ℝ => c p.1 p.2) (0, t₀) := continuous_fst.continuousAt.comp hcont
  have hC1 : ContinuousAt (fun p : ℝ × ℝ => c1 p.1 p.2) (0, t₀) :=
    (continuous_fst.comp continuous_snd).continuousAt.comp hcont
  have hYc : ContinuousAt (fun p : ℝ × ℝ => Y p.1 p.2) (0, t₀) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt.comp hcont
  have hY1c : ContinuousAt (fun p : ℝ × ℝ => Y1 p.1 p.2) (0, t₀) :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt.comp hcont
  have hC2 : ContinuousAt (fun p : ℝ × ℝ => c2 p.1 p.2) (0, t₀) := continuous_fst.continuousAt.comp hcont2
  have hY2c : ContinuousAt (fun p : ℝ × ℝ => Y2 p.1 p.2) (0, t₀) := continuous_snd.continuousAt.comp hcont2
  have hxU : c 0 t₀ ∈ U := hcU (0, t₀) (mem_of_mem_nhds hVt)
  have hKc : ContinuousAt (fun p : ℝ × ℝ => Y1 p.1 p.2 +
      Lightlike.Geodesic.gammaApply g (c p.1 p.2) (c1 p.1 p.2) (Y p.1 p.2)) (0, t₀) :=
    hY1c.add (continuousAt_gammaApply hg hC hC1 hYc hxU)
  have hK'c : ContinuousAt (fun p : ℝ × ℝ => covK' g (fun r => c r p.2) (fun r => c1 r p.2) (fun r => c2 r p.2)
      (fun r => Y r p.2) (fun r => Y1 r p.2) (fun r => Y2 r p.2) p.1) (0, t₀) := by
    unfold covK'
    exact hY2c.add (((continuousAt_gammaDeriv hg hC hC1 hC1 hYc hxU).add
      (continuousAt_gammaApply hg hC hC2 hYc hxU)).add (continuousAt_gammaApply hg hC hC1 hY1c hxU))
  have hcfc : ContinuousAt (fun p : ℝ × ℝ => coeffK g c c1 c2 Y Y1 Y2 p.1 p.2) (0, t₀) := by
    unfold coeffK
    refine (continuousAt_gpairAt hg hC (hK'c.add (continuousAt_gammaApply hg hC hC1 hKc hxU)) hYc hxU).add
      (continuousAt_gpairAt hg hC hKc hKc hxU)
  have hev : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀), p ∈ V ∧ coeffK g c c1 c2 Y Y1 Y2 p.1 p.2 < 0 :=
    (show ∀ᶠ p in 𝓝 ((0 : ℝ), t₀), p ∈ V from hVt).and (hcfc.eventually (Iio_mem_nhds hneg))
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨ε₁, hε₁, hball1⟩ := Metric.eventually_nhds_iff.1 (h0.and h0')
  refine ⟨ε₂, hε₂, min ε₁ ε₂, lt_min hε₁ hε₂, fun t ht s hs hs0 => ?_⟩
  have ht₁ : |t - t₀| < ε₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : |t - t₀| < ε₂ := lt_of_lt_of_le ht (min_le_right _ _)
  have hmem : ∀ r ∈ Ioo (-ε₂) ε₂, ((r, t) : ℝ × ℝ) ∈ V ∧ coeffK g c c1 c2 Y Y1 Y2 r t < 0 := by
    intro r hr
    apply hball
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨by simpa using abs_lt.2 ⟨by linarith [hr.1], hr.2⟩, by simpa using ht₂⟩
  obtain ⟨h0t, h0't⟩ := hball1 (by simpa [Real.dist_eq] using ht₁)
  have := neg_of_second_neg
    (f := fun r => gpairAt g (c r t) (Y r t) (Y r t))
    (f' := fun r => 2 * gpairAt g (c r t) (covK g (fun r => c r t) (fun r => c1 r t) (fun r => Y r t)
      (fun r => Y1 r t) r) (Y r t))
    (f'' := fun r => 2 * coeffK g c c1 c2 Y Y1 Y2 r t) (δ := ε₂)
    (fun r hr => hasDerivAt_normK hg (hc (r, t) (hmem r hr).1) (hY (r, t) (hmem r hr).1) (hcU (r, t) (hmem r hr).1))
    (fun r hr => hasDerivAt_normK_second hg (hc (r, t) (hmem r hr).1) (hc1 (r, t) (hmem r hr).1)
      (hY (r, t) (hmem r hr).1) (hY1 (r, t) (hmem r hr).1) (hcU (r, t) (hmem r hr).1))
    (fun r hr => by have := (hmem r hr).2; linarith) h0t (by simp only [covK]; rw [h0't]; norm_num) hε₂
  exact this s (abs_lt.1 hs |> fun h => ⟨h.1, h.2⟩) hs0

/-- **The second-order coefficient in terms of curvature**: with `K = W' + Γ(W, w)`,
`K' = C2' + ∂_WΓ(W, w) + Γ(C2, w) + Γ(W, W')` and `E = C2 + Γ(W, W)`, one has
`K' + Γ(W, K) = D_t E - R(w, W) W` where `D_t E = E' + Γ(w, E)`. -/
theorem coeff_algebra (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (w W W1 C2 C2d : Fin n → ℝ) :
    (C2d + (Lightlike.Geodesic.gammaDeriv g x W W w + Lightlike.Geodesic.gammaApply g x C2 w +
        Lightlike.Geodesic.gammaApply g x W W1)) +
      Lightlike.Geodesic.gammaApply g x W (W1 + Lightlike.Geodesic.gammaApply g x W w) =
    ((C2d + Lightlike.Geodesic.gammaDeriv g x w W W + Lightlike.Geodesic.gammaApply g x W1 W +
        Lightlike.Geodesic.gammaApply g x W W1) +
      Lightlike.Geodesic.gammaApply g x w (C2 + Lightlike.Geodesic.gammaApply g x W W)) -
      Lightlike.Geodesic.riemannApply g x W w := by
  rw [Lightlike.Geodesic.riemannApply_eq, Lightlike.Geodesic.gammaApply_add_right,
    Lightlike.Geodesic.gammaApply_add_right, Lightlike.Geodesic.gammaApply_comm hg hx C2 w,
    Lightlike.Geodesic.gammaApply_comm hg hx W1 W, Lightlike.Geodesic.gammaApply_comm hg hx W w,
    Lightlike.Geodesic.gammaDeriv_comm hg hx W w W]
  funext a
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Along a geodesic, `d/dt g(E, γ') = g(D_t E, γ')`. -/
theorem hasDerivAt_gpair_geodesic (hg : Lightlike.IsCoordMetric g U) {γ w E : ℝ → Fin n → ℝ} {E' : Fin n → ℝ}
    {t : ℝ} (hγ : HasDerivAt γ (w t) t) (hw : HasDerivAt w (Lightlike.Geodesic.accel g (γ t) (w t)) t)
    (hE : HasDerivAt E E' t) (hs : γ t ∈ U) :
    HasDerivAt (fun r => gpairAt g (γ r) (E r) (w r))
      (gpairAt g (γ t) (E' + Lightlike.Geodesic.gammaApply g (γ t) (w t) (E t)) (w t)) t := by
  have h := hasDerivAt_gpair hg hγ hs hE hw
  refine h.congr_deriv ?_
  have hcw : (fun a => covDAlong g (γ t) (w t) (w t) (Lightlike.Geodesic.accel g (γ t) (w t)) a) = 0 := by
    funext a
    simp [covDAlong, Lightlike.Geodesic.accel]
  rw [hcw, covDAlong_eq]
  have h0 : gpairAt g (γ t) (E t) (0 : Fin n → ℝ) = 0 := by simp [gpairAt]
  rw [h0, add_zero]

theorem gpairAt_sub_left (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u v w : Fin n → ℝ) :
    gpairAt g x (u - v) w = gpairAt g x u w - gpairAt g x v w := by
  unfold gpairAt
  simp only [Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem gpairAt_add_left (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u v w : Fin n → ℝ) :
    gpairAt g x (u + v) w = gpairAt g x u w + gpairAt g x v w := by
  unfold gpairAt
  simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- **The second-order coefficient is `|D_t W|² - g(R(w, W) W, w) + g(D_t E, w)`.** -/
theorem coeffK_zero_eq (hg : Lightlike.IsCoordMetric g U) {c c1 c2 Y Y1 Y2 : ℝ → ℝ → Fin n → ℝ} {t : ℝ}
    (hx : c 0 t ∈ U) :
    coeffK g c c1 c2 Y Y1 Y2 0 t =
      gpairAt g (c 0 t) (Y1 0 t + Lightlike.Geodesic.gammaApply g (c 0 t) (c1 0 t) (Y 0 t))
        (Y1 0 t + Lightlike.Geodesic.gammaApply g (c 0 t) (c1 0 t) (Y 0 t)) -
      gpairAt g (c 0 t) (Lightlike.Geodesic.riemannApply g (c 0 t) (c1 0 t) (Y 0 t)) (Y 0 t) +
      gpairAt g (c 0 t)
        (((Y2 0 t + Lightlike.Geodesic.gammaDeriv g (c 0 t) (Y 0 t) (c1 0 t) (c1 0 t) +
            Lightlike.Geodesic.gammaApply g (c 0 t) (Y1 0 t) (c1 0 t) +
            Lightlike.Geodesic.gammaApply g (c 0 t) (c1 0 t) (Y1 0 t)) +
          Lightlike.Geodesic.gammaApply g (c 0 t) (Y 0 t)
            (c2 0 t + Lightlike.Geodesic.gammaApply g (c 0 t) (c1 0 t) (c1 0 t))))
        (Y 0 t) := by
  unfold coeffK covK'
  have h := coeff_algebra hg hx (Y 0 t) (c1 0 t) (Y1 0 t) (c2 0 t) (Y2 0 t)
  rw [h, gpairAt_sub_left]
  ring

/-- **The `t`-derivative of `g(E, γ')`, `E = α_{ss} + Γ(α_s, α_s)`, is the second-order coefficient** up to the
curvature and `|D_t W|²` terms: along the geodesic `t ↦ c 0 t`,
`d/dt g(E, γ') = coeff - |D_tW|² + g(R(γ', W) W, γ')`. -/
theorem hasDerivAt_E_gpair (hg : Lightlike.IsCoordMetric g U) {c c1 c2 Y Y1 Y2 : ℝ → ℝ → Fin n → ℝ} {t : ℝ}
    (hx : c 0 t ∈ U)
    (hc : HasDerivAt (fun r => c 0 r) (Y 0 t) t) (hc1 : HasDerivAt (fun r => c1 0 r) (Y1 0 t) t)
    (hc2 : HasDerivAt (fun r => c2 0 r) (Y2 0 t) t)
    (hw : HasDerivAt (fun r => Y 0 r) (Lightlike.Geodesic.accel g (c 0 t) (Y 0 t)) t) :
    HasDerivAt (fun r => gpairAt g (c 0 r)
        (c2 0 r + Lightlike.Geodesic.gammaApply g (c 0 r) (c1 0 r) (c1 0 r)) (Y 0 r))
      (coeffK g c c1 c2 Y Y1 Y2 0 t -
        gpairAt g (c 0 t) (Y1 0 t + Lightlike.Geodesic.gammaApply g (c 0 t) (c1 0 t) (Y 0 t))
          (Y1 0 t + Lightlike.Geodesic.gammaApply g (c 0 t) (c1 0 t) (Y 0 t)) +
        gpairAt g (c 0 t) (Lightlike.Geodesic.riemannApply g (c 0 t) (c1 0 t) (Y 0 t)) (Y 0 t)) t := by
  have hch : ∀ i j k, DifferentiableAt ℝ (Lightlike.christoffel g i j k) (c 0 t) := fun i j k =>
    ((hg.contDiffOn_christoffel i j k).contDiffAt (hg.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hGE := Lightlike.Geodesic.hasDerivAt_gammaApply (g := g) hch hc hc1 hc1
  have hE := hc2.fun_add hGE
  have h := hasDerivAt_gpair_geodesic hg hc hw hE hx
  refine h.congr_deriv ?_
  rw [coeffK_zero_eq hg hx]
  ring_nf

/-- **Pair symmetry of the tidal term**: `g(R(w, W) W, w) = g(R(W, w) w, W)`. -/
theorem tidal_swap (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (w W : Fin n → ℝ) :
    gpairAt g x (Lightlike.Geodesic.riemannApply g x W w) w =
      gpairAt g x (Lightlike.Geodesic.riemannApply g x w W) W := by
  rw [gpair_riemannApply hg hx, gpair_riemannApply hg hx]
  have hboth : ∀ b σ μ ν, Lightlike.riemannLower g b σ μ ν x = Lightlike.riemannLower g σ b ν μ x := by
    intro b σ μ ν
    have h1 := hg.riemannLower_antisymm_first hx b σ μ ν
    have h2 := hg.riemannLower_pair_symm hx σ b μ ν
    have h3 := hg.riemannLower_antisymm_first hx μ ν σ b
    have h4 := hg.riemannLower_pair_symm hx ν μ σ b
    linarith
  calc ∑ b, ∑ σ, ∑ μ, ∑ ν, Lightlike.riemannLower g b σ μ ν x * w b * W σ * w μ * W ν
      = ∑ b, ∑ σ, ∑ μ, ∑ ν, Lightlike.riemannLower g σ b ν μ x * w b * W σ * w μ * W ν :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun μ _ =>
          Finset.sum_congr rfl fun ν _ => by rw [hboth b σ μ ν]
    _ = ∑ σ, ∑ b, ∑ ν, ∑ μ, Lightlike.riemannLower g σ b ν μ x * w b * W σ * w μ * W ν := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ σ, ∑ μ, ∑ ν, Lightlike.riemannLower g b σ μ ν x * W b * w σ * W μ * w ν :=
        Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun ν _ =>
          Finset.sum_congr rfl fun μ _ => by ring

end Jets

end Lightlike.Penrose
