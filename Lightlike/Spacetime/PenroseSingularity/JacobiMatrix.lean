import Lightlike.Spacetime.RiccatiFocusing
import Lightlike.Canonical.MatrixSmooth

/-!
# Focusing of a Jacobi matrix (G1-012, step D3a)

A matrix `Y(t)` (`m × m`) with `Y'' = -R Y`, symmetric Wronskian `Y'ᵀ Y = Yᵀ Y'`, and `tr R ≥ 0`, which is
invertible on `[0, T)` and has `tr (Y' Y⁻¹)(0) < 0`, has `T ≤ m / |tr (Y' Y⁻¹)(0)|`: the expansion
`θ = tr (Y' Y⁻¹)` satisfies the Riccati inequality `θ' ≤ -θ²/m`.
-/

open Set Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {m : ℕ}

/-- The first derivative of a matrix function, entrywise. -/
def mderiv (Y : ℝ → Matrix (Fin m) (Fin m) ℝ) (t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => deriv (fun s => Y s i j) t

/-- The expansion `θ = tr (Y' Y⁻¹)`. -/
def jacExpansion (Y : ℝ → Matrix (Fin m) (Fin m) ℝ) (t : ℝ) : ℝ :=
  trace (mderiv Y t * (Y t)⁻¹)

variable {Y : ℝ → Matrix (Fin m) (Fin m) ℝ} {t : ℝ}

/-- **The derivative of the inverse of a smooth matrix function.** -/
theorem hasDerivAt_inv_entry (hY : ∀ i j, ContDiffAt ℝ ∞ (fun s => Y s i j) t)
    (hdet : (Y t).det ≠ 0) (i j : Fin m) :
    HasDerivAt (fun s => (Y s)⁻¹ i j) ((-((Y t)⁻¹ * mderiv Y t * (Y t)⁻¹)) i j) t := by
  have hZc : ∀ a b, ContDiffAt ℝ ∞ (fun s => (Y s)⁻¹ a b) t := fun a b =>
    Lightlike.Canonical.contDiffAt_inv_entry Y hY hdet a b
  have hZd : ∀ a b, HasDerivAt (fun s => (Y s)⁻¹ a b) (deriv (fun s => (Y s)⁻¹ a b) t) t := fun a b =>
    ((hZc a b).differentiableAt (by simp)).hasDerivAt
  have hYd : ∀ a b, HasDerivAt (fun s => Y s a b) (mderiv Y t a b) t := fun a b =>
    (((hY a b).differentiableAt (by simp)).hasDerivAt)
  set Z' : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun a b => deriv (fun s => (Y s)⁻¹ a b) t with hZ'
  -- the determinant is nonzero near `t`
  have hdetc : ContinuousAt (fun s => (Y s).det) t :=
    (Lightlike.Canonical.contDiffAt_det Y hY).continuousAt
  have hnear : ∀ᶠ s in 𝓝 t, (Y s).det ≠ 0 := hdetc.eventually_ne hdet
  have hprod : ∀ a b, HasDerivAt (fun s => ∑ k, Y s a k * (Y s)⁻¹ k b)
      (∑ k, (mderiv Y t a k * (Y t)⁻¹ k b + Y t a k * Z' k b)) t := fun a b =>
    HasDerivAt.fun_sum fun k _ => (hYd a k).mul (hZd k b)
  have hconst : ∀ a b, HasDerivAt (fun s => ∑ k, Y s a k * (Y s)⁻¹ k b) 0 t := by
    intro a b
    refine (hasDerivAt_const t (if a = b then (1 : ℝ) else 0)).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with s hs
    have := congrFun (congrFun (Matrix.mul_nonsing_inv (Y s) (isUnit_iff_ne_zero.2 hs)) a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hmat : mderiv Y t * (Y t)⁻¹ + Y t * Z' = 0 := by
    ext a b
    have := (hprod a b).unique (hconst a b)
    simpa [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using this
  have hZ : (Y t)⁻¹ * Y t = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
  have hZ'eq : Z' = -((Y t)⁻¹ * mderiv Y t * (Y t)⁻¹) := by
    have h1 : Y t * Z' = -(mderiv Y t * (Y t)⁻¹) := eq_neg_of_add_eq_zero_right hmat
    calc Z' = ((Y t)⁻¹ * Y t) * Z' := by rw [hZ, one_mul]
      _ = (Y t)⁻¹ * (Y t * Z') := by rw [Matrix.mul_assoc]
      _ = -((Y t)⁻¹ * mderiv Y t * (Y t)⁻¹) := by rw [h1]; simp [Matrix.mul_assoc]
  have := hZd i j
  rw [show deriv (fun s => (Y s)⁻¹ i j) t = (-((Y t)⁻¹ * mderiv Y t * (Y t)⁻¹)) i j from by
    rw [← hZ'eq]; rfl] at this
  exact this

/-- The matrix `B = Y' Y⁻¹` is symmetric when the Wronskian is. -/
theorem jac_B_symm (hdet : (Y t).det ≠ 0)
    (hwron : (mderiv Y t)ᵀ * Y t = (Y t)ᵀ * mderiv Y t) :
    (mderiv Y t * (Y t)⁻¹)ᵀ = mderiv Y t * (Y t)⁻¹ := by
  have hu : IsUnit (Y t).det := isUnit_iff_ne_zero.2 hdet
  have hYZ : Y t * (Y t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hZY : (Y t)⁻¹ * Y t = 1 := Matrix.nonsing_inv_mul _ hu
  have hYZt : ((Y t)⁻¹)ᵀ * (Y t)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hYZ, Matrix.transpose_one]
  calc (mderiv Y t * (Y t)⁻¹)ᵀ = ((Y t)⁻¹)ᵀ * (mderiv Y t)ᵀ := Matrix.transpose_mul _ _
    _ = ((Y t)⁻¹)ᵀ * ((mderiv Y t)ᵀ * (Y t * (Y t)⁻¹)) := by rw [hYZ, Matrix.mul_one]
    _ = ((Y t)⁻¹)ᵀ * (((mderiv Y t)ᵀ * Y t) * (Y t)⁻¹) := by rw [Matrix.mul_assoc]
    _ = ((Y t)⁻¹)ᵀ * (((Y t)ᵀ * mderiv Y t) * (Y t)⁻¹) := by rw [hwron]
    _ = (((Y t)⁻¹)ᵀ * (Y t)ᵀ) * (mderiv Y t * (Y t)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = mderiv Y t * (Y t)⁻¹ := by rw [hYZt, Matrix.one_mul]

/-- For a symmetric matrix, `tr B² ≥ (tr B)² / m`. -/
theorem trace_sq_ge (hm : 0 < m) {B : Matrix (Fin m) (Fin m) ℝ} (hB : Bᵀ = B) :
    (trace B) ^ 2 / m ≤ trace (B * B) := by
  have h1 : trace (B * B) = ∑ i, ∑ j, B i j ^ 2 := by
    simp only [trace, diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : B j i = B i j := by
      have := congrFun (congrFun hB i) j
      simpa [Matrix.transpose_apply] using this
    rw [this]; ring
  have h2 : (∑ i, B i i) ^ 2 ≤ (m : ℝ) * ∑ i, B i i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin m => B i i)
    simpa using this
  have h3 : ∑ i, B i i ^ 2 ≤ ∑ i, ∑ j, B i j ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.single_le_sum (f := fun j => B i j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [h1, div_le_iff₀ (by exact_mod_cast hm)]
  simp only [trace, diag]
  nlinarith [h2, h3]

/-- **The Riccati equation for the expansion**: `θ' = -tr R - tr (B²)`. -/
theorem hasDerivAt_jacExpansion {R : Matrix (Fin m) (Fin m) ℝ}
    (hY : ∀ i j, ContDiffAt ℝ ∞ (fun s => Y s i j) t) (hdet : (Y t).det ≠ 0)
    (hY1 : ∀ i j, HasDerivAt (fun s => mderiv Y s i j) (mderiv (mderiv Y) t i j) t)
    (hjac : mderiv (mderiv Y) t = -(R * Y t)) :
    HasDerivAt (jacExpansion Y) (-(trace R) - trace ((mderiv Y t * (Y t)⁻¹) * (mderiv Y t * (Y t)⁻¹))) t := by
  have hZ := hasDerivAt_inv_entry hY hdet
  have hu : IsUnit (Y t).det := isUnit_iff_ne_zero.2 hdet
  have hYZ : Y t * (Y t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hterm : ∀ i k, HasDerivAt (fun s => mderiv Y s i k * (Y s)⁻¹ k i)
      (mderiv (mderiv Y) t i k * (Y t)⁻¹ k i +
        mderiv Y t i k * (-((Y t)⁻¹ * mderiv Y t * (Y t)⁻¹)) k i) t := fun i k =>
    (hY1 i k).mul (hZ k i)
  have hsum : HasDerivAt (fun s => ∑ i, ∑ k, mderiv Y s i k * (Y s)⁻¹ k i)
      (∑ i, ∑ k, (mderiv (mderiv Y) t i k * (Y t)⁻¹ k i +
        mderiv Y t i k * (-((Y t)⁻¹ * mderiv Y t * (Y t)⁻¹)) k i)) t :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun k _ => hterm i k
  have hθ : jacExpansion Y = fun s => ∑ i, ∑ k, mderiv Y s i k * (Y s)⁻¹ k i := by
    funext s; simp [jacExpansion, trace, diag, Matrix.mul_apply]
  rw [hθ]
  convert hsum using 1
  -- identify the derivative
  have e1 : ∑ i, ∑ k, mderiv (mderiv Y) t i k * (Y t)⁻¹ k i = trace (mderiv (mderiv Y) t * (Y t)⁻¹) := by
    simp [trace, diag, Matrix.mul_apply]
  have e2 : ∑ i, ∑ k, mderiv Y t i k * (-((Y t)⁻¹ * mderiv Y t * (Y t)⁻¹)) k i =
      trace (mderiv Y t * (-((Y t)⁻¹ * mderiv Y t * (Y t)⁻¹))) := by
    simp [trace, diag, Matrix.mul_apply]
  have e3 : ∑ i, ∑ k, (mderiv (mderiv Y) t i k * (Y t)⁻¹ k i +
        mderiv Y t i k * (-((Y t)⁻¹ * mderiv Y t * (Y t)⁻¹)) k i) =
      trace (mderiv (mderiv Y) t * (Y t)⁻¹) +
        trace (mderiv Y t * (-((Y t)⁻¹ * mderiv Y t * (Y t)⁻¹))) := by
    rw [← e1, ← e2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
  rw [e3, hjac]
  have e4 : trace (-(R * Y t) * (Y t)⁻¹) = -(trace R) := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, hYZ, Matrix.mul_one, trace_neg]
  have e5 : trace (mderiv Y t * (-((Y t)⁻¹ * mderiv Y t * (Y t)⁻¹))) =
      -(trace ((mderiv Y t * (Y t)⁻¹) * (mderiv Y t * (Y t)⁻¹))) := by
    rw [Matrix.mul_neg, trace_neg]
    congr 1
    simp only [Matrix.mul_assoc]
  rw [e4, e5]; ring

/-- **Focusing of a Jacobi matrix.** `Y'' = -R Y` with symmetric Wronskian and `tr R ≥ 0`, invertible on
`[0, T)`, with `θ(0) = tr (Y' Y⁻¹)(0) < 0`: then `T ≤ m / |θ(0)|`. -/
theorem jacobi_focusing (hm : 0 < m) {T : ℝ} {R : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (hY : ∀ t ∈ Ico 0 T, ∀ i j, ContDiffAt ℝ ∞ (fun s => Y s i j) t)
    (hdet : ∀ t ∈ Ico 0 T, (Y t).det ≠ 0)
    (hY1 : ∀ t ∈ Ico 0 T, ∀ i j,
      HasDerivAt (fun s => mderiv Y s i j) (mderiv (mderiv Y) t i j) t)
    (hjac : ∀ t ∈ Ico 0 T, mderiv (mderiv Y) t = -(R t * Y t))
    (hwron : ∀ t ∈ Ico 0 T, (mderiv Y t)ᵀ * Y t = (Y t)ᵀ * mderiv Y t)
    (hR : ∀ t ∈ Ico 0 T, 0 ≤ trace (R t))
    (h0 : jacExpansion Y 0 < 0) : T ≤ m / |jacExpansion Y 0| := by
  refine Lightlike.focusing (Θ := jacExpansion Y)
    (Θ' := fun t => -(trace (R t)) - trace ((mderiv Y t * (Y t)⁻¹) * (mderiv Y t * (Y t)⁻¹))) (by exact_mod_cast hm)
    (fun t ht => hasDerivAt_jacExpansion (hY t ht) (hdet t ht) (hY1 t ht) (hjac t ht)) ?_ h0
  intro t ht
  have hsym := jac_B_symm (hdet t ht) (hwron t ht)
  have h2 := trace_sq_ge hm hsym
  have hθ : jacExpansion Y t = trace (mderiv Y t * (Y t)⁻¹) := rfl
  rw [hθ, neg_div]
  have := hR t ht
  have h3 : (trace (mderiv Y t * (Y t)⁻¹)) ^ 2 / m ≤
      trace ((mderiv Y t * (Y t)⁻¹) * (mderiv Y t * (Y t)⁻¹)) := h2
  linarith

end Lightlike.Penrose
