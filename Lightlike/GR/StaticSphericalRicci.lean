import Lightlike.GR.StaticSphericalJet

/-!
# The Ricci tensor of a static spherical metric

For `ds² = -f dt² + dr²/f + r² dΩ²` (`ssMetric f`) on `r > 0`, `f ≠ 0`, `0 < θ < π` (`ssU f`), with `f` smooth on `r > 0`
and `f' = deriv f`, `f'' = deriv (deriv f)`:
`R_tt = f (f''/2 + f'/r)`, `R_rr = -(f''/(2f) + f'/(r f))`, `R_θθ = 1 - f - r f'`, `R_φφ = sin²θ R_θθ`, all other
components vanish (`ricci_ss`). Obtained from `Regge.Conv3.riemann_jet` and the generated jet formulas of
`StaticSphericalJet`. Schwarzschild-AdS and the Λ-vacuum equation are in `SAdSVacuum`.

Gap row G3-022, supporting file.
-/

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike

/-- Quotients of functions differentiable at `y`. -/
theorem dDiv {f g : (Fin 4 → ℝ) → ℝ} {y : Fin 4 → ℝ} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (h : g y ≠ 0) : DifferentiableAt ℝ (fun z => f z / g z) y := by
  exact (hf.mul (hg.inv h)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by simp [div_eq_mul_inv])

/-- The domain `r > 0`, `f(r) ≠ 0`, `0 < θ < π`. -/
def ssU (f : ℝ → ℝ) : Set (Fin 4 → ℝ) := {y | 0 < y 1 ∧ f (y 1) ≠ 0 ∧ 0 < y 2 ∧ y 2 < π}

/-- The static spherical metric `-f dt² + dr²/f + r² dΩ²`. -/
def ssMetric (f : ℝ → ℝ) (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  diagonal ![-f (y 1), 1 / f (y 1), y 1 ^ 2, y 1 ^ 2 * sin (y 2) ^ 2]

/-- The diagonal entries of the static spherical metric after the derivatives ``, by index. -/
def gjetS0 (f0 f1 f2 : ℝ → ℝ) (r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then ssgg00 f0 f1 f2 r t
  else if i = 1 ∧ j = 1 then ssgg11 f0 f1 f2 r t
  else if i = 2 ∧ j = 2 then ssgg22 f0 f1 f2 r t
  else if i = 3 ∧ j = 3 then ssgg33 f0 f1 f2 r t
  else 0

/-- The diagonal entries of the static spherical metric after the derivatives `R`, by index. -/
def gjetSR (f0 f1 f2 : ℝ → ℝ) (r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then ssgg00R f0 f1 f2 r t
  else if i = 1 ∧ j = 1 then ssgg11R f0 f1 f2 r t
  else if i = 2 ∧ j = 2 then ssgg22R f0 f1 f2 r t
  else if i = 3 ∧ j = 3 then ssgg33R f0 f1 f2 r t
  else 0

/-- The diagonal entries of the static spherical metric after the derivatives `T`, by index. -/
def gjetST (f0 f1 f2 : ℝ → ℝ) (r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then ssgg00T f0 f1 f2 r t
  else if i = 1 ∧ j = 1 then ssgg11T f0 f1 f2 r t
  else if i = 2 ∧ j = 2 then ssgg22T f0 f1 f2 r t
  else if i = 3 ∧ j = 3 then ssgg33T f0 f1 f2 r t
  else 0

/-- The diagonal entries of the static spherical metric after the derivatives `RR`, by index. -/
def gjetSRR (f0 f1 f2 : ℝ → ℝ) (r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then ssgg00RR f0 f1 f2 r t
  else if i = 1 ∧ j = 1 then ssgg11RR f0 f1 f2 r t
  else if i = 2 ∧ j = 2 then ssgg22RR f0 f1 f2 r t
  else if i = 3 ∧ j = 3 then ssgg33RR f0 f1 f2 r t
  else 0

/-- The diagonal entries of the static spherical metric after the derivatives `RT`, by index. -/
def gjetSRT (f0 f1 f2 : ℝ → ℝ) (r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then ssgg00RT f0 f1 f2 r t
  else if i = 1 ∧ j = 1 then ssgg11RT f0 f1 f2 r t
  else if i = 2 ∧ j = 2 then ssgg22RT f0 f1 f2 r t
  else if i = 3 ∧ j = 3 then ssgg33RT f0 f1 f2 r t
  else 0

/-- The diagonal entries of the static spherical metric after the derivatives `TR`, by index. -/
def gjetSTR (f0 f1 f2 : ℝ → ℝ) (r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then ssgg00TR f0 f1 f2 r t
  else if i = 1 ∧ j = 1 then ssgg11TR f0 f1 f2 r t
  else if i = 2 ∧ j = 2 then ssgg22TR f0 f1 f2 r t
  else if i = 3 ∧ j = 3 then ssgg33TR f0 f1 f2 r t
  else 0

/-- The diagonal entries of the static spherical metric after the derivatives `TT`, by index. -/
def gjetSTT (f0 f1 f2 : ℝ → ℝ) (r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then ssgg00TT f0 f1 f2 r t
  else if i = 1 ∧ j = 1 then ssgg11TT f0 f1 f2 r t
  else if i = 2 ∧ j = 2 then ssgg22TT f0 f1 f2 r t
  else if i = 3 ∧ j = 3 then ssgg33TT f0 f1 f2 r t
  else 0

theorem ssMetric_eq_gjet (f : ℝ → ℝ) (z : Fin 4 → ℝ) (i j : Fin 4) (f1 f2 : ℝ → ℝ) :
    ssMetric f z i j = gjetS0 f f1 f2 (z 1) (z 2) i j := by
  fin_cases i <;> fin_cases j <;> simp [ssMetric, gjetS0, ssgg00, ssgg11, ssgg22, ssgg33, diagonal_apply]

theorem pd_ssg00 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg00 f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg00R f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg00T f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg00 f0 f1 f2) ?_ (hdSS_g00_R f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g00_T f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg00
  exact (dD0.neg)

theorem pd_ssg00R (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg00R f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg00RR f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg00RT f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg00R f0 f1 f2) ?_ (hdSS_g00_RR f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g00_RT f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg00R
  exact (dD1.neg)

theorem pd_ssg00T (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg00T f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg00TR f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg00TT f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg00T f0 f1 f2) ?_ (hdSS_g00_TR f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g00_TT f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg00T
  exact (differentiableAt_const (0 : ℝ))

theorem pd_ssg11 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg11 f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg11R f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg11T f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg11 f0 f1 f2) ?_ (hdSS_g11_R f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g11_T f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg11
  exact (dDiv (differentiableAt_const (1 : ℝ)) dD0 (by (try dsimp only); (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, npowRec]); apply_rules [mul_ne_zero, pow_ne_zero, hr, hf, one_ne_zero]))

theorem pd_ssg11R (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg11R f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg11RR f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg11RT f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg11R f0 f1 f2) ?_ (hdSS_g11_RR f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g11_RT f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg11R
  exact (dDiv (dD1.neg) (dD0.pow 2) (by (try dsimp only); (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, npowRec]); apply_rules [mul_ne_zero, pow_ne_zero, hr, hf, one_ne_zero]))

theorem pd_ssg11T (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg11T f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg11TR f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg11TT f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg11T f0 f1 f2) ?_ (hdSS_g11_TR f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g11_TT f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg11T
  exact (differentiableAt_const (0 : ℝ))

theorem pd_ssg22 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg22 f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg22R f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg22T f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg22 f0 f1 f2) ?_ (hdSS_g22_R f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g22_T f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg22
  exact ((show DifferentiableAt ℝ (fun z : Fin 4 → ℝ => z 1) y by fun_prop).pow 2)

theorem pd_ssg22R (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg22R f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg22RR f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg22RT f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg22R f0 f1 f2) ?_ (hdSS_g22_RR f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g22_RT f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg22R
  exact ((differentiableAt_const (2 : ℝ)).mul (show DifferentiableAt ℝ (fun z : Fin 4 → ℝ => z 1) y by fun_prop))

theorem pd_ssg22T (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg22T f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg22TR f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg22TT f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg22T f0 f1 f2) ?_ (hdSS_g22_TR f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g22_TT f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg22T
  exact (differentiableAt_const (0 : ℝ))

theorem pd_ssg33 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg33 f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg33R f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg33T f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg33 f0 f1 f2) ?_ (hdSS_g33_R f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g33_T f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg33
  exact (((show DifferentiableAt ℝ (fun z : Fin 4 → ℝ => z 1) y by fun_prop).pow 2).mul (((show DifferentiableAt ℝ (fun z : Fin 4 → ℝ => z 2) y by fun_prop).sin).pow 2))

theorem pd_ssg33R (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg33R f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg33RR f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg33RT f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg33R f0 f1 f2) ?_ (hdSS_g33_RR f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g33_RT f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg33R
  exact (((differentiableAt_const (2 : ℝ)).mul (show DifferentiableAt ℝ (fun z : Fin 4 → ℝ => z 1) y by fun_prop)).mul (((show DifferentiableAt ℝ (fun z : Fin 4 → ℝ => z 2) y by fun_prop).sin).pow 2))

theorem pd_ssg33T (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (k : Fin 4) :
    pd k (fun z => ssgg33T f0 f1 f2 (z 1) (z 2)) y =
      if k = 1 then ssgg33TR f0 f1 f2 (y 1) (y 2) else if k = 2 then ssgg33TT f0 f1 f2 (y 1) (y 2) else 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hA0 := hA (y 1) hy.1
  have hB0 := hB (y 1) hy.1
  have dD0 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f0 (z 1)) y :=
    hA0.differentiableAt.comp y (by fun_prop)
  have dD1 : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => f1 (z 1)) y :=
    hB0.differentiableAt.comp y (by fun_prop)
  refine pd_rθ (ssgg33T f0 f1 f2) ?_ (hdSS_g33_TR f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0)
    (hdSS_g33_TT f0 f1 f2 (y 1) (y 2) hr hf hA0 hB0) k
  unfold ssgg33T
  exact (((show DifferentiableAt ℝ (fun z : Fin 4 → ℝ => z 1) y by fun_prop).pow 2).mul (((differentiableAt_const (2 : ℝ)).mul ((show DifferentiableAt ℝ (fun z : Fin 4 → ℝ => z 2) y by fun_prop).sin)).mul ((show DifferentiableAt ℝ (fun z : Fin 4 → ℝ => z 2) y by fun_prop).cos)))

/-- `pd` of the entries after the derivatives ``. -/
theorem pd_gjetS0 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (i j k : Fin 4) :
    pd k (fun z => gjetS0 f0 f1 f2 (z 1) (z 2) i j) y =
      if k = 1 then gjetSR f0 f1 f2 (y 1) (y 2) i j else if k = 2 then gjetST f0 f1 f2 (y 1) (y 2) i j else 0 := by
  by_cases hg00 : i = 0 ∧ j = 0
  · simp only [gjetS0, gjetSR, gjetST, hg00, and_self, ite_true]
    exact pd_ssg00 f0 f1 f2 hA hB hy k
  by_cases hg11 : i = 1 ∧ j = 1
  · simp only [gjetS0, gjetSR, gjetST, hg00, hg11, and_self, ite_true, ite_false]
    exact pd_ssg11 f0 f1 f2 hA hB hy k
  by_cases hg22 : i = 2 ∧ j = 2
  · simp only [gjetS0, gjetSR, gjetST, hg00, hg11, hg22, and_self, ite_true, ite_false]
    exact pd_ssg22 f0 f1 f2 hA hB hy k
  by_cases hg33 : i = 3 ∧ j = 3
  · simp only [gjetS0, gjetSR, gjetST, hg00, hg11, hg22, hg33, and_self, ite_true, ite_false]
    exact pd_ssg33 f0 f1 f2 hA hB hy k
  simp only [gjetS0, gjetSR, gjetST, hg00, hg11, hg22, hg33, ite_false]
  simp [pd_const]

/-- `pd` of the entries after the derivatives `R`. -/
theorem pd_gjetSR (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (i j k : Fin 4) :
    pd k (fun z => gjetSR f0 f1 f2 (z 1) (z 2) i j) y =
      if k = 1 then gjetSRR f0 f1 f2 (y 1) (y 2) i j else if k = 2 then gjetSRT f0 f1 f2 (y 1) (y 2) i j else 0 := by
  by_cases hg00 : i = 0 ∧ j = 0
  · simp only [gjetSR, gjetSRR, gjetSRT, hg00, and_self, ite_true]
    exact pd_ssg00R f0 f1 f2 hA hB hy k
  by_cases hg11 : i = 1 ∧ j = 1
  · simp only [gjetSR, gjetSRR, gjetSRT, hg00, hg11, and_self, ite_true, ite_false]
    exact pd_ssg11R f0 f1 f2 hA hB hy k
  by_cases hg22 : i = 2 ∧ j = 2
  · simp only [gjetSR, gjetSRR, gjetSRT, hg00, hg11, hg22, and_self, ite_true, ite_false]
    exact pd_ssg22R f0 f1 f2 hA hB hy k
  by_cases hg33 : i = 3 ∧ j = 3
  · simp only [gjetSR, gjetSRR, gjetSRT, hg00, hg11, hg22, hg33, and_self, ite_true, ite_false]
    exact pd_ssg33R f0 f1 f2 hA hB hy k
  simp only [gjetSR, gjetSRR, gjetSRT, hg00, hg11, hg22, hg33, ite_false]
  simp [pd_const]

/-- `pd` of the entries after the derivatives `T`. -/
theorem pd_gjetST (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (i j k : Fin 4) :
    pd k (fun z => gjetST f0 f1 f2 (z 1) (z 2) i j) y =
      if k = 1 then gjetSTR f0 f1 f2 (y 1) (y 2) i j else if k = 2 then gjetSTT f0 f1 f2 (y 1) (y 2) i j else 0 := by
  by_cases hg00 : i = 0 ∧ j = 0
  · simp only [gjetST, gjetSTR, gjetSTT, hg00, and_self, ite_true]
    exact pd_ssg00T f0 f1 f2 hA hB hy k
  by_cases hg11 : i = 1 ∧ j = 1
  · simp only [gjetST, gjetSTR, gjetSTT, hg00, hg11, and_self, ite_true, ite_false]
    exact pd_ssg11T f0 f1 f2 hA hB hy k
  by_cases hg22 : i = 2 ∧ j = 2
  · simp only [gjetST, gjetSTR, gjetSTT, hg00, hg11, hg22, and_self, ite_true, ite_false]
    exact pd_ssg22T f0 f1 f2 hA hB hy k
  by_cases hg33 : i = 3 ∧ j = 3
  · simp only [gjetST, gjetSTR, gjetSTT, hg00, hg11, hg22, hg33, and_self, ite_true, ite_false]
    exact pd_ssg33T f0 f1 f2 hA hB hy k
  simp only [gjetST, gjetSTR, gjetSTT, hg00, hg11, hg22, hg33, ite_false]
  simp [pd_const]

theorem pd_ssMetric {f0 : ℝ → ℝ} (f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r)
    (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (i j k : Fin 4) :
    pd k (fun z => ssMetric f0 z i j) y =
      if k = 1 then gjetSR f0 f1 f2 (y 1) (y 2) i j else if k = 2 then gjetST f0 f1 f2 (y 1) (y 2) i j else 0 := by
  simp only [ssMetric_eq_gjet f0 _ i j f1 f2]
  exact pd_gjetS0 f0 f1 f2 hA hB hy i j k

theorem pd_pd_ssMetric {f0 : ℝ → ℝ} (f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r)
    (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0)) (i j ν μ : Fin 4) :
    pd μ (fun w => pd ν (fun z => ssMetric f0 z i j) w) y =
      if μ = 1 then (if ν = 1 then gjetSRR f0 f1 f2 (y 1) (y 2) i j else if ν = 2 then gjetSTR f0 f1 f2 (y 1) (y 2) i j else 0)
      else if μ = 2 then (if ν = 1 then gjetSRT f0 f1 f2 (y 1) (y 2) i j else if ν = 2 then gjetSTT f0 f1 f2 (y 1) (y 2) i j else 0)
      else 0 := by
  have hev : (fun w => pd ν (fun z => ssMetric f0 z i j) w) =ᶠ[nhds y]
      fun w => if ν = 1 then gjetSR f0 f1 f2 (w 1) (w 2) i j else if ν = 2 then gjetST f0 f1 f2 (w 1) (w 2) i j else 0 := by
    filter_upwards [hU.mem_nhds hy] with w hw
    exact pd_ssMetric f1 f2 hA hB hw i j ν
  rw [pd_congr hev]
  by_cases h1 : ν = 1
  · simp only [h1, ite_true]
    exact pd_gjetSR f0 f1 f2 hA hB hy i j μ
  by_cases h2 : ν = 2
  · simp only [h1, h2, ite_true, ite_false]
    exact pd_gjetST f0 f1 f2 hA hB hy i j μ
  simp only [h1, h2, ite_false]
  rw [pd_const]
  split_ifs <;> rfl

/-- The inverse of the static spherical metric. -/
theorem ssMetric_inv (f : ℝ → ℝ) {y : Fin 4 → ℝ} (hy : y ∈ ssU f) :
    (ssMetric f y)⁻¹ = diagonal ![-(1 / f (y 1)), f (y 1), 1 / y 1 ^ 2, 1 / (y 1 ^ 2 * sin (y 2) ^ 2)] := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f (y 1) ≠ 0 := hy.2.1
  have hs : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  refine Matrix.inv_eq_right_inv ?_
  rw [ssMetric, diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Matrix.diagonal_apply] <;> field_simp

open Lightlike.Regge.Conv3 in
/-- The `(0, 0)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_00 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 0 0 y = f0 (y 1) * (f2 (y 1) / 2 + f1 (y 1) / y 1) := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(0, 1)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_01 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 0 1 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(0, 2)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_02 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 0 2 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(0, 3)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_03 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 0 3 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(1, 0)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_10 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 1 0 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(1, 1)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_11 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 1 1 y = -(f2 (y 1) / (2 * f0 (y 1)) + f1 (y 1) / (y 1 * f0 (y 1))) := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(1, 2)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_12 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 1 2 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(1, 3)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_13 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 1 3 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(2, 0)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_20 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 2 0 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(2, 1)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_21 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 2 1 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(2, 2)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_22 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 2 2 y = 1 - f0 (y 1) - y 1 * f1 (y 1) := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(2, 3)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_23 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 2 3 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(3, 0)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_30 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 3 0 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(3, 1)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_31 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 3 1 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(3, 2)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_32 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 3 2 y = 0 := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

open Lightlike.Regge.Conv3 in
/-- The `(3, 3)` component of the Ricci tensor of the static spherical metric. -/
theorem ricci_ss_33 (f0 f1 f2 : ℝ → ℝ) (hA : ∀ r, 0 < r → HasDerivAt f0 (f1 r) r) (hB : ∀ r, 0 < r → HasDerivAt f1 (f2 r) r) {y : Fin 4 → ℝ} (hy : y ∈ ssU f0) (hU : IsOpen (ssU f0))
    (hg : IsCoordMetric (ssMetric f0) (ssU f0)) :
    ricci (ssMetric f0) 3 3 y = sin (y 2) ^ 2 * (1 - f0 (y 1) - y 1 * f1 (y 1)) := by
  have hinv := ssMetric_inv f0 hy
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : f0 (y 1) ≠ 0 := hy.2.1
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_ssMetric f1 f2 hA hB hy,
    pd_pd_ssMetric f1 f2 hA hB hy hU, hinv, Fin.sum_univ_four]
  simp [ssgg00R, ssgg00T, ssgg00RR, ssgg00RT, ssgg00TR, ssgg00TT, ssgg11R, ssgg11T, ssgg11RR, ssgg11RT, ssgg11TR, ssgg11TT, ssgg22R, ssgg22T, ssgg22RR, ssgg22RT, ssgg22TR, ssgg22TT, ssgg33R, ssgg33T, ssgg33RR, ssgg33RT, ssgg33TR, ssgg33TT, gjetSR, gjetST, gjetSRR, gjetSRT, gjetSTR, gjetSTT, ssgg00, ssgg11, ssgg22, ssgg33]
  try field_simp
  first
    | (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)
    | ring
    | skip

end Lightlike
