import Mathlib
import Lightlike.Spacetime.Curvature

/-!
# The curvature of a metric at a point, from its second-order jet

For a coordinate metric `g` (`IsCoordMetric`), the Christoffel symbols and the Riemann tensor at a
point `m` are explicit expressions in `g m`, its inverse, the first partial derivatives
`∂_k g_ij (m)` and the second partial derivatives `∂_μ ∂_ν g_ij (m)`. The one analytic input is the
derivative of the inverse metric, `∂_k g⁻¹ = -g⁻¹ (∂_k g) g⁻¹` (`pd_inv`), which needs `g` to be
smooth and invertible near `m`.

## Main results

* `pd_inv`: the derivative of the inverse metric.
* `pd_christoffel`: the derivative of the Christoffel symbols at `m`.
* `riemann_jet`: the Riemann tensor at `m` in terms of the jet of `g`.
-/

open Matrix Lightlike
open scoped ContDiff

namespace Lightlike.Regge.Conv3

variable {n : ℕ}

/-- The determinant of a matrix of `C^k` functions is `C^k`. -/
theorem cdo_det {U : Set (Fin n → ℝ)} {k : WithTop ℕ∞} (M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i j, ContDiffOn ℝ k (fun y => M y i j) U) :
    ContDiffOn ℝ k (fun y => (M y).det) U := by
  simp_rw [Matrix.det_apply]
  refine ContDiffOn.sum fun σ _ => ?_
  refine ContDiffOn.const_smul _ ?_
  exact contDiffOn_prod fun i _ => h _ _

/-- The adjugate of a matrix of `C^k` functions has `C^k` entries. -/
theorem cdo_adj {U : Set (Fin n → ℝ)} {k : WithTop ℕ∞} (M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i j, ContDiffOn ℝ k (fun y => M y i j) U) (i j : Fin n) :
    ContDiffOn ℝ k (fun y => (M y).adjugate i j) U := by
  simp_rw [Matrix.adjugate_apply]
  refine cdo_det _ fun a b => ?_
  by_cases ha : a = j
  · subst ha
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simp only [Matrix.updateRow_ne ha]
    exact h a b

/-- The inverse of a coordinate metric has smooth entries on `U`. -/
theorem cdo_inv {U : Set (Fin n → ℝ)} (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : IsCoordMetric g U) (i j : Fin n) : ContDiffOn ℝ ∞ (fun y => (g y)⁻¹ i j) U := by
  have hd : ContDiffOn ℝ ∞ (fun y => (g y).det) U := cdo_det g hg.smooth
  refine ContDiffOn.congr (f := fun y => ((g y).det)⁻¹ * (g y).adjugate i j) ?_ ?_
  · exact (hd.inv fun y hy => (hg.isUnit_det y hy).ne_zero).mul (cdo_adj g hg.smooth i j)
  · intro y hy
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp

/-- Entries of a coordinate metric are smooth at a point of `U`. -/
theorem cdat_g {U : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsCoordMetric g U) {m : Fin n → ℝ} (hm : m ∈ U) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => g y i j) m :=
  (hg.smooth i j).contDiffAt (hg.isOpen.mem_nhds hm)

/-- Entries of the inverse of a coordinate metric are smooth at a point of `U`. -/
theorem cdat_ginv {U : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsCoordMetric g U) {m : Fin n → ℝ} (hm : m ∈ U) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => (g y)⁻¹ i j) m :=
  (cdo_inv g hg i j).contDiffAt (hg.isOpen.mem_nhds hm)

/-- Product rule for `pd`. -/
theorem pd_mul {f h : (Fin n → ℝ) → ℝ} {m : Fin n → ℝ} (k : Fin n)
    (hf : DifferentiableAt ℝ f m) (hh : DifferentiableAt ℝ h m) :
    pd k (fun y => f y * h y) m = pd k f m * h m + f m * pd k h m := by
  unfold pd
  rw [fderiv_fun_mul hf hh]
  simp
  ring

/-- Sum rule for `pd` over a finite set. -/
theorem pd_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin n → ℝ) → ℝ} {m : Fin n → ℝ} (k : Fin n)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) m) :
    pd k (fun y => ∑ i ∈ s, f i y) m = ∑ i ∈ s, pd k (f i) m := by
  unfold pd
  rw [fderiv_fun_sum hf]
  simp

/-- **Derivative of the inverse metric.** `∂_k (g⁻¹)_{ab} = -Σ (g⁻¹)_{ai} (∂_k g_{il}) (g⁻¹)_{lb}`, at a point where `g` is a coordinate metric. -/
theorem pd_inv {U : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsCoordMetric g U) {m : Fin n → ℝ} (hm : m ∈ U) (k a b : Fin n) :
    pd k (fun y => (g y)⁻¹ a b) m =
      -∑ i, ∑ l, (g m)⁻¹ a i * pd k (fun y => g y i l) m * (g m)⁻¹ l b := by
  have hU := hg.isOpen.mem_nhds hm
  -- the entry identity near m
  have key : ∀ i j, pd k (fun y => ∑ l, g y i l * (g y)⁻¹ l j) m = 0 := by
    intro i j
    have : (fun y => ∑ l, g y i l * (g y)⁻¹ l j) =ᶠ[nhds m] fun _ => (if i = j then (1:ℝ) else 0) := by
      filter_upwards [hU] with y hy
      have := Matrix.mul_nonsing_inv (g y) (hg.isUnit_det y hy)
      have := congrFun (congrFun this i) j
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    unfold pd
    rw [this.fderiv_eq]
    simp
  have key2 : ∀ i j, ∑ l, (pd k (fun y => g y i l) m * (g m)⁻¹ l j
      + g m i l * pd k (fun y => (g y)⁻¹ l j) m) = 0 := by
    intro i j
    have := key i j
    rw [pd_sum (f := fun l y => g y i l * (g y)⁻¹ l j) _ k (fun l _ => ((cdat_g hg hm i l).differentiableAt (by simp)).mul
      ((cdat_ginv hg hm l j).differentiableAt (by simp)))] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pd_mul k ((cdat_g hg hm i l).differentiableAt (by simp))
      ((cdat_ginv hg hm l j).differentiableAt (by simp))]
  set P : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun l j => pd k (fun y => (g y)⁻¹ l j) m with hP
  set Dm : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i l => pd k (fun y => g y i l) m with hD
  have hm1 : Dm * (g m)⁻¹ + g m * P = 0 := by
    ext i j
    simpa [Matrix.mul_apply, hP, hD, Finset.sum_add_distrib] using key2 i j
  have hP2 : P = -((g m)⁻¹ * Dm * (g m)⁻¹) := by
    have h1 : (g m)⁻¹ * (Dm * (g m)⁻¹ + g m * P) = 0 := by rw [hm1]; simp
    rw [mul_add, ← mul_assoc ((g m)⁻¹) (g m) P, Matrix.nonsing_inv_mul _ (hg.isUnit_det m hm),
      one_mul] at h1
    rw [← mul_assoc] at h1
    exact eq_neg_of_add_eq_zero_right (by exact h1)
  have := congrFun (congrFun hP2 a) b
  simp only [hP, hD, Matrix.mul_apply, Matrix.neg_apply, Matrix.of_apply, Finset.sum_mul] at this
  rw [Finset.sum_comm] at this
  exact this

/-- The partial derivatives of the entries of a coordinate metric are smooth at a point of `U`. -/
theorem cdat_pd {U : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsCoordMetric g U) {m : Fin n → ℝ} (hm : m ∈ U) (j i l : Fin n) :
    ContDiffAt ℝ ∞ (fun y => pd j (fun z => g z i l) y) m := by
  unfold pd
  exact ((cdat_g hg hm i l).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

/-- Sum rule for `pd`. -/
theorem pd_add {f h : (Fin n → ℝ) → ℝ} {m : Fin n → ℝ} (k : Fin n)
    (hf : DifferentiableAt ℝ f m) (hh : DifferentiableAt ℝ h m) :
    pd k (fun y => f y + h y) m = pd k f m + pd k h m := by
  unfold pd; rw [fderiv_fun_add hf hh]; rfl

/-- Difference rule for `pd`. -/
theorem pd_sub {f h : (Fin n → ℝ) → ℝ} {m : Fin n → ℝ} (k : Fin n)
    (hf : DifferentiableAt ℝ f m) (hh : DifferentiableAt ℝ h m) :
    pd k (fun y => f y - h y) m = pd k f m - pd k h m := by
  unfold pd; rw [fderiv_fun_sub hf hh]; rfl

/-- Constant-factor rule for `pd`. -/
theorem pd_const_mul {f : (Fin n → ℝ) → ℝ} {m : Fin n → ℝ} (k : Fin n) (c : ℝ)
    (hf : DifferentiableAt ℝ f m) :
    pd k (fun y => c * f y) m = c * pd k f m := by
  unfold pd; rw [fderiv_const_mul hf]; simp

/-- The derivative `∂_μ Γ^ρ_{νσ}` of the Christoffel symbols at `m`, written with the derivative
of the inverse metric substituted: a function of `(g m)⁻¹`, `∂ g (m)` and `∂ ∂ g (m)` only. -/
noncomputable def dChr (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ)
    (μ ρ ν σ : Fin n) : ℝ :=
  (1 / 2) * ∑ l,
      ((-∑ i, ∑ r, (g m)⁻¹ ρ i * pd μ (fun y => g y i r) m * (g m)⁻¹ r l) *
          (pd ν (fun y => g y l σ) m + pd σ (fun y => g y l ν) m - pd l (fun y => g y ν σ) m)
        + (g m)⁻¹ ρ l *
          (pd μ (fun y => pd ν (fun z => g z l σ) y) m + pd μ (fun y => pd σ (fun z => g z l ν) y) m
            - pd μ (fun y => pd l (fun z => g z ν σ) y) m))

/-- The derivative of the Christoffel symbols at `m`, in terms of the jet of `g`. -/
theorem pd_christoffel {U : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsCoordMetric g U) {m : Fin n → ℝ} (hm : m ∈ U) (μ ρ ν σ : Fin n) :
    pd μ (christoffel g ρ ν σ) m = dChr g m μ ρ ν σ := by
  unfold dChr
  have hd := fun a b => (cdat_g hg hm a b).differentiableAt (by simp)
  have hdi := fun a b => (cdat_ginv hg hm a b).differentiableAt (by simp)
  have hdp := fun j a b => (cdat_pd hg hm j a b).differentiableAt (by simp)
  have e : christoffel g ρ ν σ = fun y => (1 / 2 : ℝ) * ∑ l, (g y)⁻¹ ρ l *
      (pd ν (fun z => g z l σ) y + pd σ (fun z => g z l ν) y - pd l (fun z => g z ν σ) y) := by
    funext y; simp [christoffel]
  have hterm : ∀ l, DifferentiableAt ℝ (fun y => (g y)⁻¹ ρ l *
      (pd ν (fun z => g z l σ) y + pd σ (fun z => g z l ν) y - pd l (fun z => g z ν σ) y)) m :=
    fun l => (hdi ρ l).mul (((hdp ν l σ).add (hdp σ l ν)).sub (hdp l ν σ))
  rw [e, pd_const_mul _ _ (DifferentiableAt.fun_sum fun l _ => hterm l),
    pd_sum (f := fun l y => (g y)⁻¹ ρ l *
      (pd ν (fun z => g z l σ) y + pd σ (fun z => g z l ν) y - pd l (fun z => g z ν σ) y)) _ μ
      (fun l _ => hterm l)]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 := hdp ν l σ
  have h2 := hdp σ l ν
  have h3 := hdp l ν σ
  rw [pd_mul (f := fun y => (g y)⁻¹ ρ l)
      (h := fun y => pd ν (fun z => g z l σ) y + pd σ (fun z => g z l ν) y - pd l (fun z => g z ν σ) y)
      μ (hdi ρ l) ((h1.add h2).sub h3),
    pd_sub (f := fun y => pd ν (fun z => g z l σ) y + pd σ (fun z => g z l ν) y)
      (h := fun y => pd l (fun z => g z ν σ) y) μ (h1.add h2) h3,
    pd_add (f := fun y => pd ν (fun z => g z l σ) y) (h := fun y => pd σ (fun z => g z l ν) y) μ h1 h2,
    pd_inv hg hm]

/-- **The Riemann tensor at a point in terms of the jet of the metric.** `riemann g ρ σ μ ν m` is
`∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ Γ - Γ Γ` with `∂Γ` given by `dChr`, which involves only
`(g m)⁻¹`, `∂ g (m)` and `∂ ∂ g (m)`. -/
theorem riemann_jet {U : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsCoordMetric g U) {m : Fin n → ℝ} (hm : m ∈ U) (ρ σ μ ν : Fin n) :
    riemann g ρ σ μ ν m = dChr g m μ ρ ν σ - dChr g m ν ρ μ σ +
      ∑ l, (christoffel g ρ μ l m * christoffel g l ν σ m
        - christoffel g ρ ν l m * christoffel g l μ σ m) := by
  rw [riemann, pd_christoffel hg hm, pd_christoffel hg hm]

/-- **The scalar curvature at a point in terms of the jet of the metric.** -/
theorem scalarCurvature_jet {U : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsCoordMetric g U) {m : Fin n → ℝ} (hm : m ∈ U) :
    scalarCurvature g m = ∑ σ, ∑ ν, (g m)⁻¹ σ ν * ∑ ρ,
      (dChr g m ρ ρ ν σ - dChr g m ν ρ ρ σ +
        ∑ l, (christoffel g ρ ρ l m * christoffel g l ν σ m
          - christoffel g ρ ν l m * christoffel g l ρ σ m)) := by
  simp only [scalarCurvature, ricci, riemann_jet hg hm]

end Lightlike.Regge.Conv3
