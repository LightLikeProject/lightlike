import Lightlike.Canonical.SpinVariation
import Lightlike.Canonical.MatrixDeriv
import Lightlike.Spacetime.VariationDet

/-!
# The symplectic potentials of the Ashtekar–Barbero and the ADM variables

For a co-triad `e` with `det e > 0`, the metric `h = eᵀ e`, a symmetric `K_ab` and the ADM momentum
`π^{ab} = √h (K^{ab} − K h^{ab})` (indices raised with `h`, `K = h^{ab} K_ab`): along the path `(e + t δe, K + t δK)`,
the triad part of the Ashtekar–Barbero potential is the variation of `√h K` plus half the ADM potential,
`E^a_i δK^i_a = δ(√h K) + ½ π^{ab} δh_ab` with `K^i_a = K_ab e^b_i` (`triad_potential`).

Here `K` is the extrinsic curvature in the sign of Ashtekar–Lewandowski (2.18), `K_ab = q_a^α q_b^β ∇_α n_β` with `n`
future directed, the opposite of the sign `K(u, v) = −u · ∇_v n` (Gourgoulhon (2.43)) of the library's extrinsic
curvature of a foliation; in that sign `π` is Gourgoulhon's `π^{ij} = √γ (K γ^{ij} − K^{ij})` (4.108).
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

/-- `Σ_ab X_ab Y_ab = tr(Xᵀ Y)`. -/
lemma sum_entry_mul_eq_trace (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ a, ∑ b, X a b * Y a b = (Xᵀ * Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- The matrix algebra behind `triad_potential`, with `f = e⁻¹` and `δf = −f δe f`. -/
lemma triad_potential_alg (e f δe K δK : Matrix (Fin 3) (Fin 3) ℝ) (hef : e * f = 1) (hK : Kᵀ = K) :
    (fᵀ * (δK * f - K * (f * δe * f))).trace =
      (f * δe).trace * (f * fᵀ * K).trace +
        (-(f * δe * f) * fᵀ * K + f * (-(f * δe * f))ᵀ * K + f * fᵀ * δK).trace +
      (1 / 2) * ((f * fᵀ * K * (f * fᵀ) - (f * fᵀ * K).trace • (f * fᵀ))ᵀ * (δeᵀ * e + eᵀ * δe)).trace := by
  have hfeT : fᵀ * eᵀ = 1 := by rw [← Matrix.transpose_mul, hef, Matrix.transpose_one]
  set M := f * fᵀ * K * (f * fᵀ) - (f * fᵀ * K).trace • (f * fᵀ) with hM
  have hMT : Mᵀ = M := by
    rw [hM]
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hK,
      Matrix.mul_assoc]
  have h1 : (M * (δeᵀ * e)).trace = ((fᵀ * K * (f * fᵀ) - (f * fᵀ * K).trace • fᵀ) * δeᵀ).trace := by
    rw [← Matrix.mul_assoc M, Matrix.trace_mul_cycle M δeᵀ e, hM, Matrix.mul_sub, Matrix.mul_smul]
    simp only [← Matrix.mul_assoc, hef, Matrix.one_mul]
  have h2 : (M * (eᵀ * δe)).trace = ((f * fᵀ * K * f - (f * fᵀ * K).trace • f) * δe).trace := by
    rw [← Matrix.mul_assoc M, hM, Matrix.sub_mul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc, hfeT, Matrix.mul_one]
  rw [hMT, Matrix.mul_add, Matrix.trace_add (M * (δeᵀ * e)) (M * (eᵀ * δe)), h1, h2]
  have h10 : K 1 0 = K 0 1 := by rw [← Matrix.transpose_apply K 0 1, hK]
  have h20 : K 2 0 = K 0 2 := by rw [← Matrix.transpose_apply K 0 2, hK]
  have h21 : K 2 1 = K 1 2 := by rw [← Matrix.transpose_apply K 1 2, hK]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.neg_apply, Matrix.transpose_apply, Fin.sum_univ_three, smul_eq_mul, h10, h20, h21]
  ring

/-- The variation of `K^i_a = K_ab e^b_i` (`triadK`) along `(e + t δe, K + t δK)`:
`δ(K e⁻¹) = δK e⁻¹ − K e⁻¹ δe e⁻¹`. -/
lemma hasDerivAt_triadK_path (e δe K δK : Matrix (Fin 3) (Fin 3) ℝ) (hdet : e.det ≠ 0) (a i : Fin 3) :
    HasDerivAt (fun t : ℝ => ((K + t • δK) * (e + t • δe)⁻¹) a i) ((δK * e⁻¹ - K * (e⁻¹ * δe * e⁻¹)) a i) 0 := by
  have hKd : ∀ p q, HasDerivAt (fun t : ℝ => (K + t • δK) p q) (δK p q) 0 := fun p q => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δK p q)).const_add (K p q)
  have h := HasDerivAt.fun_sum fun b (_ : b ∈ Finset.univ) =>
    (hKd a b).mul (Lightlike.hasDerivAt_inv_add_smul e δe hdet b i)
  have hf : (fun t : ℝ => ((K + t • δK) * (e + t • δe)⁻¹) a i) =
      fun t => ∑ b, (K + t • δK) a b * (e + t • δe)⁻¹ b i := funext fun t => Matrix.mul_apply
  rw [hf]
  convert h using 1
  simp only [zero_smul, add_zero, Matrix.sub_apply, mul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Matrix.mul_apply (M := δK), Matrix.mul_apply (M := K), sub_eq_add_neg]

/-- **The triad part of the Ashtekar–Barbero potential**: for `det e > 0` and symmetric `K`, along the path
`(e + t δe, K + t δK)` with `h_t = (e + t δe)ᵀ (e + t δe)`,
`E^a_i δK^i_a = δ(√h h^{ab} K_ab) + ½ π^{ab} δh_ab`, where `E = |det e| e⁻¹` (`densTriad`), `K^i_a = (K e⁻¹)_{ai}`
(`triadK`) and `π = √h (h⁻¹ K h⁻¹ − tr(h⁻¹ K) h⁻¹)`. -/
theorem triad_potential (e δe K δK : Matrix (Fin 3) (Fin 3) ℝ) (hpos : 0 < e.det) (hK : Kᵀ = K) :
    ∑ a, ∑ i, (|e.det| • e⁻¹) a i * deriv (fun t : ℝ => ((K + t • δK) * (e + t • δe)⁻¹) a i) 0 =
      deriv (fun t : ℝ => Real.sqrt ((e + t • δe)ᵀ * (e + t • δe)).det *
        (((e + t • δe)ᵀ * (e + t • δe))⁻¹ * (K + t • δK)).trace) 0 +
      (1 / 2) * ∑ a, ∑ b, (Real.sqrt (eᵀ * e).det • ((eᵀ * e)⁻¹ * K * (eᵀ * e)⁻¹ -
          ((eᵀ * e)⁻¹ * K).trace • (eᵀ * e)⁻¹)) a b *
        deriv (fun t : ℝ => ((e + t • δe)ᵀ * (e + t • δe)) a b) 0 := by
  have hu : IsUnit e.det := isUnit_iff_ne_zero.2 hpos.ne'
  have hef : e * e⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hsq : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, Real.sqrt (Mᵀ * M).det = |M.det| := fun M => by
    rw [Matrix.det_mul, Matrix.det_transpose, Real.sqrt_mul_self_eq_abs]
  have hinv : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, (Mᵀ * M)⁻¹ = M⁻¹ * (M⁻¹)ᵀ := fun M => by
    rw [Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]
  have hE : ∀ p q, HasDerivAt (fun t : ℝ => (e + t • δe) p q) (δe p q) 0 := fun p q => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δe p q)).const_add (e p q)
  have hKd : ∀ p q, HasDerivAt (fun t : ℝ => (K + t • δK) p q) (δK p q) 0 := fun p q => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δK p q)).const_add (K p q)
  have hD : ∀ p q, HasDerivAt (fun t : ℝ => (e + t • δe)⁻¹ p q) ((-(e⁻¹ * δe * e⁻¹)) p q) 0 := fun p q =>
    Lightlike.hasDerivAt_inv_add_smul e δe hpos.ne' p q
  -- the variation of `K^i_a = K_ab e^b_i`
  have hL : ∀ a i, deriv (fun t : ℝ => ((K + t • δK) * (e + t • δe)⁻¹) a i) 0 =
      (δK * e⁻¹ - K * (e⁻¹ * δe * e⁻¹)) a i := fun a i =>
    (hasDerivAt_triadK_path e δe K δK hpos.ne' a i).deriv
  -- the variation of `h`
  have hH : ∀ a b, deriv (fun t : ℝ => ((e + t • δe)ᵀ * (e + t • δe)) a b) 0 = (δeᵀ * e + eᵀ * δe) a b := by
    intro a b
    have h := HasDerivAt.fun_sum fun l (_ : l ∈ Finset.univ) => (hE l a).mul (hE l b)
    have hf : (fun t : ℝ => ((e + t • δe)ᵀ * (e + t • δe)) a b) =
        fun t => ∑ l, (e + t • δe) l a * (e + t • δe) l b := funext fun t => by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [hf]
    refine h.deriv.trans ?_
    simp only [zero_smul, Matrix.add_apply, Matrix.zero_apply, add_zero, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_add_distrib]
  -- the variation of `h^{ab} K_ab = tr(e⁻¹ e⁻ᵀ K)`
  have hT : HasDerivAt (fun t : ℝ => ((e + t • δe)⁻¹ * ((e + t • δe)⁻¹)ᵀ * (K + t • δK)).trace)
      ((-(e⁻¹ * δe * e⁻¹) * (e⁻¹)ᵀ * K + e⁻¹ * (-(e⁻¹ * δe * e⁻¹))ᵀ * K + e⁻¹ * (e⁻¹)ᵀ * δK).trace) 0 := by
    have hf : (fun t : ℝ => ((e + t • δe)⁻¹ * ((e + t • δe)⁻¹)ᵀ * (K + t • δK)).trace) =
        fun t => ∑ p, ∑ r, ∑ q, (e + t • δe)⁻¹ p q * (e + t • δe)⁻¹ r q * (K + t • δK) r p :=
      funext fun t => by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [hf]
    have h := HasDerivAt.fun_sum fun p (_ : p ∈ Finset.univ) =>
      HasDerivAt.fun_sum fun r (_ : r ∈ Finset.univ) =>
        HasDerivAt.fun_sum fun q (_ : q ∈ Finset.univ) => ((hD p q).mul (hD r q)).mul (hKd r p)
    convert h using 1
    simp only [Pi.mul_apply, zero_smul, add_zero]
    generalize -(e⁻¹ * δe * e⁻¹) = D
    generalize e⁻¹ = f
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
      Fin.sum_univ_three]
    ring
  -- the variation of `√h = det e`
  have hdet : HasDerivAt (fun t : ℝ => |(e + t • δe).det|) (e.det * (e⁻¹ * δe).trace) 0 := by
    have h := hasDerivAt_det_add_smul e δe hu
    have hev : (fun t : ℝ => |(e + t • δe).det|) =ᶠ[nhds 0] fun t => (e + t • δe).det := by
      have hc : ContinuousAt (fun t : ℝ => (e + t • δe).det) 0 := h.continuousAt
      have : ∀ᶠ t in nhds (0 : ℝ), 0 < (e + t • δe).det := hc.eventually (lt_mem_nhds (by simpa using hpos))
      filter_upwards [this] with t ht
      exact abs_of_pos ht
    exact h.congr_of_eventuallyEq hev
  have hG : deriv (fun t : ℝ => Real.sqrt ((e + t • δe)ᵀ * (e + t • δe)).det *
      (((e + t • δe)ᵀ * (e + t • δe))⁻¹ * (K + t • δK)).trace) 0 =
      e.det * (e⁻¹ * δe).trace * (e⁻¹ * (e⁻¹)ᵀ * K).trace + |e.det| *
        (-(e⁻¹ * δe * e⁻¹) * (e⁻¹)ᵀ * K + e⁻¹ * (-(e⁻¹ * δe * e⁻¹))ᵀ * K + e⁻¹ * (e⁻¹)ᵀ * δK).trace := by
    have hf : (fun t : ℝ => Real.sqrt ((e + t • δe)ᵀ * (e + t • δe)).det *
        (((e + t • δe)ᵀ * (e + t • δe))⁻¹ * (K + t • δK)).trace) =
        fun t => |(e + t • δe).det| * ((e + t • δe)⁻¹ * ((e + t • δe)⁻¹)ᵀ * (K + t • δK)).trace :=
      funext fun t => by rw [hsq, hinv]
    rw [hf]
    refine (hdet.mul hT).deriv.trans ?_
    simp only [zero_smul, add_zero]
  simp only [hL, hH]
  rw [hG, hsq e, hinv e, sum_entry_mul_eq_trace, sum_entry_mul_eq_trace]
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, abs_of_pos hpos]
  linear_combination e.det * triad_potential_alg e e⁻¹ δe K δK hef hK


/-- **The Ashtekar–Barbero potential is `γ` times the ADM potential plus an exact term**: for a smooth positively
oriented co-triad `e`, a smooth compactly supported `δe`, a symmetric `K` and any `δK`, along
`(e + t δe, K + t δK)` with `h_t = (e + t δe)ᵀ (e + t δe)` and `A_t = Γ_t + γ K_t` (`abConn`),
`∫ (E^a_i δA^i_a − γ (δ(√h K) + ½ π^{ab} δh_ab)) = 0`: the triad part is `triad_potential` and the spin-connection part
`∫ E δΓ` vanishes (`integral_E_deriv_spinConn_eq_zero`). -/
theorem integral_E_dAbConn (γ : ℝ) (e δe : CoTriad) (K δK : TensorField 3)
    (hs : ∀ k b, ContDiff ℝ ∞ (fun y => e y k b)) (hδ : ∀ k b, ContDiff ℝ ∞ (fun y => δe y k b))
    (hδc : ∀ k b, HasCompactSupport (fun y => δe y k b)) (hpos : ∀ y, 0 < (e y).det)
    (hK : ∀ y, (K y)ᵀ = K y) :
    ∫ y, (∑ a, ∑ i, densTriad e y a i *
        deriv (fun t : ℝ => abConn γ (fun z => e z + t • δe z) (fun z => (e z + t • δe z)ᵀ * (e z + t • δe z))
          (fun z => K z + t • δK z) y a i) 0 -
      γ * (deriv (fun t : ℝ => Real.sqrt ((e y + t • δe y)ᵀ * (e y + t • δe y)).det *
          (((e y + t • δe y)ᵀ * (e y + t • δe y))⁻¹ * (K y + t • δK y)).trace) 0 +
        (1 / 2) * ∑ a, ∑ b, (Real.sqrt ((e y)ᵀ * e y).det • (((e y)ᵀ * e y)⁻¹ * K y * ((e y)ᵀ * e y)⁻¹ -
            (((e y)ᵀ * e y)⁻¹ * K y).trace • ((e y)ᵀ * e y)⁻¹)) a b *
          deriv (fun t : ℝ => ((e y + t • δe y)ᵀ * (e y + t • δe y)) a b) 0)) = 0 := by
  refine (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)).trans
    (integral_E_deriv_spinConn_eq_zero e δe hs hδ hδc hpos)
  have hde : ∀ k b, DifferentiableAt ℝ (fun z => e z k b) y := fun k b => ((hs k b).differentiable (by simp)) y
  have hdl : ∀ k b, DifferentiableAt ℝ (fun z => δe z k b) y := fun k b => ((hδ k b).differentiable (by simp)) y
  have hsplit : ∀ a i, deriv (fun t : ℝ => abConn γ (fun z => e z + t • δe z)
      (fun z => (e z + t • δe z)ᵀ * (e z + t • δe z)) (fun z => K z + t • δK z) y a i) 0 =
      deriv (fun t : ℝ => spinConn (fun z => e z + t • δe z)
        (fun z => (e z + t • δe z)ᵀ * (e z + t • δe z)) y a i) 0 +
      γ * deriv (fun t : ℝ => ((K y + t • δK y) * (e y + t • δe y)⁻¹) a i) 0 := by
    intro a i
    have h1 := ((contDiffAt_spinConn_path e δe y hde hdl (hpos y).ne' a i).differentiableAt
      (by simp)).hasDerivAt
    have h2 := (hasDerivAt_triadK_path (e y) (δe y) (K y) (δK y) (hpos y).ne' a i).differentiableAt.hasDerivAt
    exact (h1.add (h2.const_mul γ)).deriv
  rw [← triad_potential (e y) (δe y) (K y) (δK y) (hpos y) (hK y)]
  simp only [hsplit, densTriad, Fin.sum_univ_three]
  ring

end Lightlike.Canonical
