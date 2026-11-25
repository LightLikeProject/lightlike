import Mathlib

/-!
# The vacuum Bianchi IX Wainwright–Hsu system (row G1-040, milestone CO14)

Hubble-normalized variables `x = (Σ₊, Σ₋, N₁, N₂, N₃) ∈ ℝ⁵` (as `Fin 5 → ℝ`), in the logarithmic
time `τ` with `τ → -∞` towards the singularity. The vacuum equations are
`Σ±' = -(2 - q) Σ± - 3 S±`, `N₁' = (q - 4Σ₊) N₁`, `N₂' = (q + 2Σ₊ + 2√3 Σ₋) N₂`,
`N₃' = (q + 2Σ₊ - 2√3 Σ₋) N₃`, with `q = 2 Σ²` and the constraint `Σ² + K = 1`.
The right-hand side is the standard Hubble-normalized one (the setting of heinzle-uggla-2009a,
Section 3 and heinzle-uggla-2009b, Section 1); the source text was not available, so the formulas
were not read there, and their consistency is *checked here*: the constraint is preserved
(`constraint_deriv`). `N₁N₂N₃` is monotone (`IsSol.prod_monotone`), the first step of the attractor
theorem: `(N₁N₂N₃)' = 3 q N₁N₂N₃`.
-/

namespace Lightlike.Cosmology.BianchiIXWainwrightHsu

open Real

noncomputable section

/-- The Hubble-normalized shear component `Σ₊`. -/
def sp (x : Fin 5 → ℝ) : ℝ := x 0
/-- The Hubble-normalized shear component `Σ₋`. -/
def sm (x : Fin 5 → ℝ) : ℝ := x 1
/-- The curvature variable `N₁`. -/
def n1 (x : Fin 5 → ℝ) : ℝ := x 2
/-- The curvature variable `N₂`. -/
def n2 (x : Fin 5 → ℝ) : ℝ := x 3
/-- The curvature variable `N₃`. -/
def n3 (x : Fin 5 → ℝ) : ℝ := x 4

/-- The deceleration parameter in vacuum, `q = 2 Σ² = 2 (Σ₊² + Σ₋²)`. -/
def qd (x : Fin 5 → ℝ) : ℝ := 2 * (sp x ^ 2 + sm x ^ 2)

/-- The curvature `S₊ = ½ [(N₂ - N₃)² - N₁ (2N₁ - N₂ - N₃)]`. -/
def Sp (x : Fin 5 → ℝ) : ℝ :=
  (1 / 2) * ((n2 x - n3 x) ^ 2 - n1 x * (2 * n1 x - n2 x - n3 x))

/-- The curvature `S₋ = (√3/2) (N₃ - N₂) (N₁ - N₂ - N₃)`. -/
def Sm (x : Fin 5 → ℝ) : ℝ :=
  (√3 / 2) * (n3 x - n2 x) * (n1 x - n2 x - n3 x)

/-- The spatial-curvature term `K = ¾ [N₁² + N₂² + N₃² - 2 (N₁N₂ + N₂N₃ + N₃N₁)]`. -/
def Kc (x : Fin 5 → ℝ) : ℝ :=
  (3 / 4) * (n1 x ^ 2 + n2 x ^ 2 + n3 x ^ 2 - 2 * (n1 x * n2 x + n2 x * n3 x + n3 x * n1 x))

/-- The vacuum constraint function `G = Σ² + K - 1`; the constraint is `G = 0`. -/
def Gc (x : Fin 5 → ℝ) : ℝ := sp x ^ 2 + sm x ^ 2 + Kc x - 1

/-- The vector field of the vacuum Wainwright–Hsu system of Bianchi type IX. -/
def vf (x : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![-(2 - qd x) * sp x - 3 * Sp x, -(2 - qd x) * sm x - 3 * Sm x, (qd x - 4 * sp x) * n1 x,
    (qd x + 2 * sp x + 2 * √3 * sm x) * n2 x, (qd x + 2 * sp x - 2 * √3 * sm x) * n3 x]

/-- A solution of the system on all of `ℝ` (log-time). -/
def IsSol (γ : ℝ → Fin 5 → ℝ) : Prop := ∀ t, HasDerivAt γ (vf (γ t)) t

/-- The derivative of the constraint function along the vector field. -/
def dG (x : Fin 5 → ℝ) : ℝ :=
  2 * sp x * (vf x 0) + 2 * sm x * (vf x 1)
    + (3 / 4) * ((2 * n1 x - 2 * n2 x - 2 * n3 x) * vf x 2
      + (2 * n2 x - 2 * n1 x - 2 * n3 x) * vf x 3
      + (2 * n3 x - 2 * n1 x - 2 * n2 x) * vf x 4)

/-- **The constraint is preserved**: along the vector field `G' = 2 q G`. This is the consistency
check of the right-hand side `vf` against the constraint `Σ² + K = 1`. -/
lemma constraint_deriv (x : Fin 5 → ℝ) : dG x = 2 * qd x * Gc x := by
  simp only [dG, vf, Gc, Kc, qd, Sp, Sm, sp, sm, n1, n2, n3]
  simp
  ring_nf

/-- The components of a solution are differentiable with the components of `vf`. -/
lemma IsSol.comp {γ : ℝ → Fin 5 → ℝ} (h : IsSol γ) (i : Fin 5) (t : ℝ) :
    HasDerivAt (fun s => γ s i) (vf (γ t) i) t :=
  (hasDerivAt_pi.1 (h t)) i

/-- **The product `N₁N₂N₃` along a solution**: its derivative is `3 q N₁N₂N₃`, so it is
non-decreasing in `τ`, hence non-increasing towards the singularity `τ → -∞`. -/
lemma IsSol.prod_deriv {γ : ℝ → Fin 5 → ℝ} (h : IsSol γ) (t : ℝ) :
    HasDerivAt (fun s => n1 (γ s) * n2 (γ s) * n3 (γ s))
      (3 * qd (γ t) * (n1 (γ t) * n2 (γ t) * n3 (γ t))) t := by
  have h2 := h.comp 2 t
  have h3 := h.comp 3 t
  have h4 := h.comp 4 t
  have h5 := (h2.mul h3).mul h4
  refine HasDerivAt.congr_deriv h5 ?_
  simp only [vf, n1, n2, n3, qd, sp, sm, Pi.mul_apply]
  simp
  ring

/-- `q = 2Σ² ≥ 0`, so `N₁N₂N₃` is monotone along solutions. -/
lemma qd_nonneg (x : Fin 5 → ℝ) : 0 ≤ qd x := by
  unfold qd; positivity

/-- **Monotonicity of `N₁N₂N₃`**: where `N₁N₂N₃ ≥ 0` (type IX: all `Nᵢ > 0`), it is non-decreasing
in `τ` along a solution. -/
lemma IsSol.prod_monotone {γ : ℝ → Fin 5 → ℝ} (h : IsSol γ)
    (hp : ∀ t, 0 ≤ n1 (γ t) * n2 (γ t) * n3 (γ t)) :
    Monotone (fun s => n1 (γ s) * n2 (γ s) * n3 (γ s)) := by
  apply monotone_of_deriv_nonneg
  · exact fun t => (h.prod_deriv t).differentiableAt
  · intro t
    rw [(h.prod_deriv t).deriv]
    exact mul_nonneg (mul_nonneg (by norm_num) (qd_nonneg _)) (hp t)

end

end Lightlike.Cosmology.BianchiIXWainwrightHsu

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.Gc := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.Gc
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.IsSol := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.IsSol
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.IsSol.comp := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.IsSol.comp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.IsSol.prod_deriv := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.IsSol.prod_deriv
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.IsSol.prod_monotone := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.IsSol.prod_monotone
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.Kc := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.Kc
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.Sm := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.Sm
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.Sp := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.Sp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.constraint_deriv := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.constraint_deriv
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.dG := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.dG
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.n1 := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.n1
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.n2 := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.n2
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.n3 := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.n3
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.qd := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.qd
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.qd_nonneg := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.qd_nonneg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.sm := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.sm
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.sp := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.sp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.vf := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.vf
