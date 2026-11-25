import Mathlib
import Lightlike.Cosmology.GrowthEquation.GrowthCore

/-!
# Growth equation from the linearized Euler–Poisson system (row G1-032)

Fields live on `ℝ × Space` (time, comoving position) with `Space = Fin 3 → ℝ`. Spatial partials and
the time partial are directional Fréchet derivatives of the uncurried field, so that the commutation
`∂ₜ∂ᵢ = ∂ᵢ∂ₜ` is Mathlib's symmetry of the second derivative (`ContDiffAt.isSymmSndFDerivAt`).

`LinearizedEulerPoisson` is the linearization of the Euler–Poisson system in comoving coordinates
about a homogeneous background of density `ρ(t)` (Bernardeau et al. 2002, Section 2.3, source key
`bernardeau-2002`): continuity, Euler with sound speed `c_s`, Poisson. `growth_equation` derives
`δ'' + 2Hδ' - 4πGρδ = (c_s²/a²) Δδ`; with `c_s = 0` this is the growth equation.
-/

open Filter Topology

namespace Lightlike.Cosmology.GrowthEquation

/-- Comoving position space. -/
abbrev Space := Fin 3 → ℝ

/-- Time partial derivative of a field on `ℝ × Space`. -/
noncomputable def dt (f : ℝ × Space → ℝ) (p : ℝ × Space) : ℝ :=
  fderiv ℝ f p ((1 : ℝ), (0 : Space))

/-- Spatial partial derivative `∂ᵢ`. -/
noncomputable def dx (i : Fin 3) (f : ℝ × Space → ℝ) (p : ℝ × Space) : ℝ :=
  fderiv ℝ f p ((0 : ℝ), (Pi.single i (1 : ℝ) : Space))

/-- Divergence of a vector field given by components. -/
noncomputable def divg (u : Fin 3 → ℝ × Space → ℝ) (p : ℝ × Space) : ℝ :=
  ∑ i, dx i (u i) p

/-- Comoving Laplacian. -/
noncomputable def lap (f : ℝ × Space → ℝ) (p : ℝ × Space) : ℝ :=
  ∑ i, dx i (dx i f) p

/-- The linearized Euler–Poisson system in comoving coordinates, for the density contrast `δ`,
the peculiar velocity `u` and the potential `φ`, scale factor `a`, background density `ρ`,
Newton constant `G` and sound speed `cs`:
continuity `∂ₜδ + (1/a)∇·u = 0`, Euler `∂ₜu + Hu = -(1/a)∇φ - (cs²/a)∇δ`, Poisson `Δφ = 4πGa²ρδ`. -/
structure LinearizedEulerPoisson (a ρ : ℝ → ℝ) (G cs : ℝ) (δ φ : ℝ × Space → ℝ)
    (u : Fin 3 → ℝ × Space → ℝ) : Prop where
  continuity : ∀ p, dt δ p = -divg u p / a p.1
  euler : ∀ i p, dt (u i) p =
    -(deriv a p.1 / a p.1) * u i p - dx i φ p / a p.1 - cs ^ 2 * dx i δ p / a p.1
  poisson : ∀ p, lap φ p = 4 * Real.pi * G * a p.1 ^ 2 * ρ p.1 * δ p

section Calculus

variable {f : ℝ × Space → ℝ}

/-- A directional derivative of a `C²` field is `C¹`. -/
lemma contDiff_dir (hf : ContDiff ℝ 2 f) (w : ℝ × Space) :
    ContDiff ℝ 1 (fun q => fderiv ℝ f q w) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma contDiff_dx (hf : ContDiff ℝ 2 f) (i : Fin 3) : ContDiff ℝ 1 (dx i f) :=
  contDiff_dir hf _

/-- Derivative of a directional derivative: the second derivative. -/
lemma fderiv_dir (hf : ContDiff ℝ 2 f) (v w p : ℝ × Space) :
    fderiv ℝ (fun q => fderiv ℝ f q w) p v = fderiv ℝ (fderiv ℝ f) p v w := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) p
  have h2 : HasFDerivAt (fun q => fderiv ℝ f q w)
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ f) p)) p :=
    (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp p h1.hasFDerivAt
  rw [h2.fderiv]
  rfl

/-- `∂ₜ∂ᵢ = ∂ᵢ∂ₜ` on `C²` fields. -/
lemma dt_dx_comm (hf : ContDiff ℝ 2 f) (i : Fin 3) (p : ℝ × Space) :
    dt (dx i f) p = dx i (dt f) p := by
  unfold dt dx
  rw [fderiv_dir hf, fderiv_dir hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- Time slice: the derivative of `s ↦ f (s, x)` is `∂ₜ f`. -/
lemma hasDerivAt_slice {t : ℝ} {x : Space} (hf : DifferentiableAt ℝ f (t, x)) :
    HasDerivAt (fun s => f (s, x)) (dt f (t, x)) t := by
  have hs : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Space)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact hf.hasFDerivAt.comp_hasDerivAt t hs

/-- A factor depending on time only passes through a spatial derivative. -/
lemma dx_mul_time {h : ℝ → ℝ} {p : ℝ × Space} (i : Fin 3) (hh : DifferentiableAt ℝ h p.1)
    (hf : DifferentiableAt ℝ f p) :
    dx i (fun q => h q.1 * f q) p = h p.1 * dx i f p := by
  have h1 : HasFDerivAt (fun q : ℝ × Space => h q.1)
      (deriv h p.1 • (ContinuousLinearMap.fst ℝ ℝ Space)) p :=
    hh.hasDerivAt.comp_hasFDerivAt p (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun q : ℝ × Space => h q.1 * f q)
      (h p.1 • fderiv ℝ f p + f p • deriv h p.1 • (ContinuousLinearMap.fst ℝ ℝ Space)) p :=
    h1.mul hf.hasFDerivAt
  unfold dx
  rw [h2.fderiv]
  simp

lemma dx_sub {g : ℝ × Space → ℝ} {p : ℝ × Space} (i : Fin 3) (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) :
    dx i (fun q => f q - g q) p = dx i f p - dx i g p := by
  unfold dx
  rw [fderiv_fun_sub hf hg]
  rfl

lemma dx_neg {p : ℝ × Space} (i : Fin 3) :
    dx i (fun q => -f q) p = -dx i f p := by
  unfold dx
  rw [fderiv_fun_neg]
  rfl

end Calculus

/-- **Growth equation with pressure.** If `(δ, u, φ)` solve the linearized Euler–Poisson system
about a background with scale factor `a` (`C²`, nowhere zero) and density `ρ`, all fields `C²`, then
at every point `δ'' + 2Hδ' - 4πGρδ = (c_s²/a²) Δδ`, where `'` is the time derivative at fixed
comoving position and `H = a'/a`. -/
theorem growth_equation {a ρ : ℝ → ℝ} {G cs : ℝ} {δ φ : ℝ × Space → ℝ}
    {u : Fin 3 → ℝ × Space → ℝ} (hsys : LinearizedEulerPoisson a ρ G cs δ φ u)
    (ha : ContDiff ℝ 2 a) (ha0 : ∀ t, a t ≠ 0)
    (hδ : ContDiff ℝ 2 δ) (hφ : ContDiff ℝ 2 φ) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (t : ℝ) (x : Space) :
    deriv (deriv fun s => δ (s, x)) t + 2 * (deriv a t / a t) * deriv (fun s => δ (s, x)) t
      - 4 * Real.pi * G * ρ t * δ (t, x) = cs ^ 2 / a t ^ 2 * lap δ (t, x) := by
  have hda : ContDiff ℝ 1 (deriv a) := by
    have h := (ha.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiff_const (c := (1 : ℝ)))
    exact h
  have hHd : Differentiable ℝ (fun s => deriv a s / a s) :=
    (hda.differentiable (by simp)).div (ha.differentiable (by simp)) ha0
  have hid : Differentiable ℝ (fun s => cs ^ 2 * (a s)⁻¹) :=
    (differentiable_const _).mul ((ha.differentiable (by simp)).inv ha0)
  have hiv : Differentiable ℝ (fun s => (a s)⁻¹) := (ha.differentiable (by simp)).inv ha0
  have dpr : ∀ g : ℝ → ℝ, Differentiable ℝ g → Differentiable ℝ (fun q : ℝ × Space => g q.1) :=
    fun g hg => hg.comp differentiable_fst
  have dDx : ∀ {g : ℝ × Space → ℝ}, ContDiff ℝ 2 g → ∀ i, Differentiable ℝ (dx i g) :=
    fun hg i => (contDiff_dx hg i).differentiable (by simp)
  have hdx : ∀ i p, dx i (dt (u i)) p =
      -(deriv a p.1 / a p.1 * dx i (u i) p) - (a p.1)⁻¹ * dx i (dx i φ) p
        - cs ^ 2 * (a p.1)⁻¹ * dx i (dx i δ) p := by
    intro i p
    have e : dt (u i) = fun q => -((deriv a q.1 / a q.1) * u i q)
        - ((a q.1)⁻¹ * dx i φ q) - ((cs ^ 2 * (a q.1)⁻¹) * dx i δ q) := by
      funext q
      rw [hsys.euler i q]
      ring
    rw [e, dx_sub, dx_sub, dx_neg, dx_mul_time i (hHd _) ((hu i).differentiable (by simp) p),
      dx_mul_time i (hiv _) (dDx hφ i p), dx_mul_time i (hid _) (dDx hδ i p)]
    · exact (((dpr _ hHd).mul ((hu i).differentiable (by simp))) p).neg
    · exact ((dpr _ hiv).mul (dDx hφ i)) p
    · exact (((dpr _ hHd).mul ((hu i).differentiable (by simp))).neg.sub
        ((dpr _ hiv).mul (dDx hφ i))) p
    · exact ((dpr _ hid).mul (dDx hδ i)) p
  have hD : ∀ i, HasDerivAt (fun s => dx i (u i) (s, x)) (dt (dx i (u i)) (t, x)) t :=
    fun i => hasDerivAt_slice ((dDx (hu i) i) _)
  have hDs : HasDerivAt (fun s => divg u (s, x)) (∑ i, dt (dx i (u i)) (t, x)) t :=
    HasDerivAt.fun_sum (fun i _ => hD i)
  have hDsum : ∑ i, dt (dx i (u i)) (t, x) =
      -(deriv a t / a t) * divg u (t, x) - lap φ (t, x) / a t - cs ^ 2 * lap δ (t, x) / a t := by
    have : ∀ i, dt (dx i (u i)) (t, x) =
        -(deriv a t / a t * dx i (u i) (t, x)) - (a t)⁻¹ * dx i (dx i φ) (t, x)
          - cs ^ 2 * (a t)⁻¹ * dx i (dx i δ) (t, x) := fun i => by
      rw [dt_dx_comm (hu i) i]
      exact hdx i (t, x)
    simp only [this, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, divg, lap]
    ring
  refine sub_eq_zero.mp ?_
  have key := growth_core a (fun s => δ (s, x)) (fun s => divg u (s, x)) (fun s => lap φ (s, x))
    (fun s => lap δ (s, x)) ρ G cs t (ha.differentiable (by simp) t) (ha0 t) hDs.differentiableAt
    (Filter.Eventually.of_forall fun s => by
      rw [(hasDerivAt_slice (hδ.differentiable (by simp) (s, x))).deriv]
      exact hsys.continuity (s, x))
    (by rw [hDs.deriv, hDsum]) (hsys.poisson (t, x))
  linarith

/-- **Growth equation** `δ'' + 2Hδ' - 4πGρδ = 0` for pressureless matter (`c_s = 0`), from the
linearized Euler–Poisson system in comoving coordinates (Bernardeau et al. 2002, Section 2.3). -/
theorem growth_equation_pressureless {a ρ : ℝ → ℝ} {G : ℝ} {δ φ : ℝ × Space → ℝ}
    {u : Fin 3 → ℝ × Space → ℝ} (hsys : LinearizedEulerPoisson a ρ G 0 δ φ u)
    (ha : ContDiff ℝ 2 a) (ha0 : ∀ t, a t ≠ 0)
    (hδ : ContDiff ℝ 2 δ) (hφ : ContDiff ℝ 2 φ) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (t : ℝ) (x : Space) :
    deriv (deriv fun s => δ (s, x)) t + 2 * (deriv a t / a t) * deriv (fun s => δ (s, x)) t
      - 4 * Real.pi * G * ρ t * δ (t, x) = 0 := by
  have := growth_equation hsys ha ha0 hδ hφ hu t x
  simpa using this

end Lightlike.Cosmology.GrowthEquation

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.LinearizedEulerPoisson := _root_.Lightlike.Cosmology.GrowthEquation.LinearizedEulerPoisson
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.LinearizedEulerPoisson.continuity := _root_.Lightlike.Cosmology.GrowthEquation.LinearizedEulerPoisson.continuity
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.LinearizedEulerPoisson.euler := _root_.Lightlike.Cosmology.GrowthEquation.LinearizedEulerPoisson.euler
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.LinearizedEulerPoisson.poisson := _root_.Lightlike.Cosmology.GrowthEquation.LinearizedEulerPoisson.poisson
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.Space := _root_.Lightlike.Cosmology.GrowthEquation.Space
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.contDiff_dir := _root_.Lightlike.Cosmology.GrowthEquation.contDiff_dir
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.contDiff_dx := _root_.Lightlike.Cosmology.GrowthEquation.contDiff_dx
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.divg := _root_.Lightlike.Cosmology.GrowthEquation.divg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.dt := _root_.Lightlike.Cosmology.GrowthEquation.dt
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.dt_dx_comm := _root_.Lightlike.Cosmology.GrowthEquation.dt_dx_comm
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.dx := _root_.Lightlike.Cosmology.GrowthEquation.dx
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.dx_mul_time := _root_.Lightlike.Cosmology.GrowthEquation.dx_mul_time
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.dx_neg := _root_.Lightlike.Cosmology.GrowthEquation.dx_neg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.dx_sub := _root_.Lightlike.Cosmology.GrowthEquation.dx_sub
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.fderiv_dir := _root_.Lightlike.Cosmology.GrowthEquation.fderiv_dir
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.growth_equation := _root_.Lightlike.Cosmology.GrowthEquation.growth_equation
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.growth_equation_pressureless := _root_.Lightlike.Cosmology.GrowthEquation.growth_equation_pressureless
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.hasDerivAt_slice := _root_.Lightlike.Cosmology.GrowthEquation.hasDerivAt_slice
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_032.lap := _root_.Lightlike.Cosmology.GrowthEquation.lap
