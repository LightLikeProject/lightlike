import Mathlib
import Lightlike.Canonical.MatrixDeriv
import Lightlike.Canonical.LieDeriv

/-!
# Partial derivatives of the kinetic density and of `√det h`

For smooth `h`, `π` with `det h > 0`, the partial derivatives of `x ↦ kinJ c (h x) (π x)` and of
`x ↦ √det (h x)` are the directional derivatives `dkinJ` and `det H tr (H⁻¹ ∂_k h)/(2 √det H)` of the
matrix functions of `Lightlike/Canonical/MatrixDeriv.lean`, along `(∂_k h, ∂_k π)`: the chain rule, identifying the
Fréchet derivative with the derivative along lines.
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- **Chain rule through the line derivative**: if `F` is differentiable at `z` and `D v` is its derivative
along the line `z + t v`, then `∂_k (F ∘ g) = D (∂_k g)`. -/
lemma pd_comp_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) {z : E}
    (hF : DifferentiableAt ℝ F z) (D : E → ℝ) (hD : ∀ v, HasDerivAt (fun t : ℝ => F (z + t • v)) (D v) 0)
    (g : (Fin d → ℝ) → E) {x : Fin d → ℝ} (hg : DifferentiableAt ℝ g x) (hgx : g x = z) (k : Fin d) :
    Lightlike.pd k (fun y => F (g y)) x = D (fderiv ℝ g x (Pi.single k 1)) := by
  have hFg : HasFDerivAt F (fderiv ℝ F z) (g x) := by rw [hgx]; exact hF.hasFDerivAt
  have h1 : HasFDerivAt (fun y => F (g y)) ((fderiv ℝ F z).comp (fderiv ℝ g x)) x :=
    hFg.comp x hg.hasFDerivAt
  have hDv : ∀ v, D v = fderiv ℝ F z v := by
    intro v
    have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
      refine HasDerivAt.congr_deriv this ?_
      simp
    have h2 : HasFDerivAt F (fderiv ℝ F z) (z + (0 : ℝ) • v) := by simpa using hF.hasFDerivAt
    exact (hD v).unique (h2.comp_hasDerivAt (0 : ℝ) hline)
  simp only [Lightlike.pd]
  rw [h1.fderiv]
  simp [hDv]

/-- A pair of `d × d` arrays: a value `(H, P)` of the metric and the momentum at a point. -/
abbrev Arr (d : ℕ) := (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)

lemma dm_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F G : E → Matrix (Fin d) (Fin d) ℝ} {x : E}
    (hF : ∀ i j, DifferentiableAt ℝ (fun z => F z i j) x) (hG : ∀ i j, DifferentiableAt ℝ (fun z => G z i j) x)
    (i j : Fin d) : DifferentiableAt ℝ (fun z => (F z * G z) i j) x := by
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (hF i k).mul (hG k j)

lemma dm_trace {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → Matrix (Fin d) (Fin d) ℝ} {x : E}
    (hF : ∀ i j, DifferentiableAt ℝ (fun z => F z i j) x) :
    DifferentiableAt ℝ (fun z => (F z).trace) x := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact DifferentiableAt.fun_sum fun i _ => hF i i

/-- The kinetic term as a function of the pair of arrays. -/
def Kfun (c : ℝ) (Z : Arr d) : ℝ := kinJ c (Matrix.of Z.1) (Matrix.of Z.2)

lemma differentiableAt_Kfun (c : ℝ) {Z : Arr d} (hZ : 0 < (Matrix.of Z.1).det) :
    DifferentiableAt ℝ (Kfun c) Z := by
  have h1 : ∀ i j, DifferentiableAt ℝ (fun Z : Arr d => (Matrix.of Z.1) i j) Z := fun i j => by
    simp only [Matrix.of_apply]; fun_prop
  have h2 : ∀ i j, DifferentiableAt ℝ (fun Z : Arr d => (Matrix.of Z.2) i j) Z := fun i j => by
    simp only [Matrix.of_apply]; fun_prop
  have hHP := dm_mul h1 h2
  have hHPHP := dm_mul (dm_mul hHP h1) h2
  have hnum : DifferentiableAt ℝ (fun Z : Arr d => ((Matrix.of Z.1) * (Matrix.of Z.2) * (Matrix.of Z.1) *
      (Matrix.of Z.2)).trace - c * ((Matrix.of Z.1) * (Matrix.of Z.2)).trace ^ 2) Z :=
    (dm_trace hHPHP).sub (((dm_trace hHP).pow 2).const_mul c)
  have hdet : DifferentiableAt ℝ (fun Z : Arr d => (Matrix.of Z.1).det) Z :=
    Gauge.differentiableAt_det (fun Z : Arr d => Matrix.of Z.1) h1
  have hs : DifferentiableAt ℝ (fun Z : Arr d => Real.sqrt (Matrix.of Z.1).det) Z := hdet.sqrt hZ.ne'
  have hne : Real.sqrt (Matrix.of Z.1).det ≠ 0 := (Real.sqrt_pos.mpr hZ).ne'
  unfold Kfun kinJ
  simp only [div_eq_mul_inv]
  exact hnum.mul (hs.inv hne)

/-- The line derivative of `Kfun`: `dkinJ`. -/
lemma hasDerivAt_Kfun_line (c : ℝ) {Z : Arr d} (hZ : 0 < (Matrix.of Z.1).det) (V : Arr d) :
    HasDerivAt (fun t : ℝ => Kfun c (Z + t • V))
      (dkinJ c (Matrix.of Z.1) (Matrix.of Z.2) (Matrix.of V.1) (Matrix.of V.2)) 0 := by
  have e : ∀ t : ℝ, Kfun c (Z + t • V) = kinJ c (Matrix.of Z.1 + t • Matrix.of V.1)
      (Matrix.of Z.2 + t • Matrix.of V.2) := by
    intro t
    unfold Kfun
    congr 1
  simp only [e]
  exact hasDerivAt_kinJ c _ _ _ _ hZ

/-- The map `y ↦ (h y, π y)` into pairs of arrays is differentiable with the partial derivatives of the entries. -/
lemma hasFDerivAt_pair {h π : TensorField d} (hh : SmoothTensor h) (hπ : SmoothTensor π) (x : Fin d → ℝ) :
    HasFDerivAt (fun y : Fin d → ℝ => ((fun a b => h y a b, fun a b => π y a b) : Arr d))
      (ContinuousLinearMap.prod
        (ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b => fderiv ℝ (fun y => h y a b) x)
        (ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b => fderiv ℝ (fun y => π y a b) x)) x := by
  refine HasFDerivAt.prodMk (hasFDerivAt_pi'.2 fun a => hasFDerivAt_pi'.2 fun b => ?_)
    (hasFDerivAt_pi'.2 fun a => hasFDerivAt_pi'.2 fun b => ?_)
  · exact (diff_of_smooth (hh a b) x).hasFDerivAt
  · exact (diff_of_smooth (hπ a b) x).hasFDerivAt

/-- **The partial derivative of the kinetic density.** -/
lemma pd_kinJ {h π : TensorField d} (hh : SmoothTensor h) (hπ : SmoothTensor π) (c : ℝ)
    {x : Fin d → ℝ} (hpos : 0 < (h x).det) (k : Fin d) :
    Lightlike.pd k (fun y => kinJ c (h y) (π y)) x =
      dkinJ c (h x) (π x) (Matrix.of fun a b => Lightlike.pd k (fun y => h y a b) x)
        (Matrix.of fun a b => Lightlike.pd k (fun y => π y a b) x) := by
  set Z : Arr d := ((fun a b => h x a b, fun a b => π x a b) : Arr d) with hZ
  have hZpos : 0 < (Matrix.of Z.1).det := hpos
  have := pd_comp_line (Kfun c) (differentiableAt_Kfun c hZpos)
    (fun V => dkinJ c (Matrix.of Z.1) (Matrix.of Z.2) (Matrix.of V.1) (Matrix.of V.2))
    (hasDerivAt_Kfun_line c hZpos)
    (fun y => ((fun a b => h y a b, fun a b => π y a b) : Arr d)) (hasFDerivAt_pair hh hπ x).differentiableAt rfl k
  refine this.trans ?_
  have hf := (hasFDerivAt_pair hh hπ x).fderiv
  rw [hf]
  rfl

/-- **The partial derivative of `√det h`**: `det H tr (H⁻¹ ∂_k h)/(2 √det H)`. -/
lemma pd_sqrt_det {h : TensorField d} (hh : SmoothTensor h) {x : Fin d → ℝ} (hpos : 0 < (h x).det) (k : Fin d) :
    Lightlike.pd k (fun y => Real.sqrt (h y).det) x =
      (h x).det * ((h x)⁻¹ * Matrix.of fun a b => Lightlike.pd k (fun y => h y a b) x).trace /
        (2 * Real.sqrt (h x).det) := by
  set Z : Arr d := ((fun a b => h x a b, fun a b => h x a b) : Arr d) with hZ
  have hZpos : 0 < (Matrix.of Z.1).det := hpos
  have h1 : ∀ i j, DifferentiableAt ℝ (fun Z : Arr d => (Matrix.of Z.1) i j) Z := fun i j => by
    simp only [Matrix.of_apply]; fun_prop
  have hdet : DifferentiableAt ℝ (fun Z : Arr d => (Matrix.of Z.1).det) Z :=
    Gauge.differentiableAt_det (fun Z : Arr d => Matrix.of Z.1) h1
  have hF : DifferentiableAt ℝ (fun Z : Arr d => Real.sqrt (Matrix.of Z.1).det) Z := hdet.sqrt hZpos.ne'
  have hD : ∀ V : Arr d, HasDerivAt (fun t : ℝ => (fun Z : Arr d => Real.sqrt (Matrix.of Z.1).det) (Z + t • V))
      ((Matrix.of Z.1).det * ((Matrix.of Z.1)⁻¹ * Matrix.of V.1).trace / (2 * Real.sqrt (Matrix.of Z.1).det)) 0 := by
    intro V
    have e : ∀ t : ℝ, Matrix.of (Z + t • V).1 = Matrix.of Z.1 + t • Matrix.of V.1 := fun t => by ext a b; simp
    simp only [e]
    exact hasDerivAt_sqrt_det _ _ hZpos
  have := pd_comp_line (fun Z : Arr d => Real.sqrt (Matrix.of Z.1).det) hF _ hD
    (fun y => ((fun a b => h y a b, fun a b => h y a b) : Arr d)) (hasFDerivAt_pair hh hh x).differentiableAt rfl k
  refine this.trans ?_
  have hf := (hasFDerivAt_pair hh hh x).fderiv
  rw [hf]
  rfl

end Lightlike.Canonical

end
