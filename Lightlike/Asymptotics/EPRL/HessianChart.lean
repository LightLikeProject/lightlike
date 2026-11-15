import Lightlike.Asymptotics.EPRL.Amplitude
import Lightlike.Asymptotics.EPRL.HessianSlice
import Lightlike.Asymptotics.EPRL.HaarChart

/-!
# The Hessian of the amplitude in the gnomonic and in the exponential chart

The Haar measure of `SU(2)^4` is written in the gnomonic chart `q ↦ (γ(q_a))_a` (`HaarChart.lean`),
while the Hessian `hessAmp` of the amplitude is taken in the exponential chart
`θ ↦ (X_a exp(su2Gen θ_a))_a`. Both charts agree to second order up to the factor 2 and the swap
of the coordinates `0 ↔ 2` in each block (`su2Gen_two_swp`), so that the Hessians are related by
`H_q = 4 · P H_θ P` (`hessMat_qchart`). The comparison goes through the second derivative along
lines and curves of `HessianSlice.lean`.
-/

open Matrix Complex Lightlike.Oscillatory MeasureTheory
open scoped ContDiff

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma contDiff_prop (g : BdryData) (e : Fin 10) :
    ContDiff ℝ ∞ (fun X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ => prop g X e) := by
  unfold prop
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  have hX : ∀ (a : Fin 5) (i j : Fin 2),
      ContDiff ℝ ∞ (fun X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ => X a i j) := fun a i j =>
    by
    let L : (Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) →ₗ[ℝ] ℂ :=
      { toFun := fun X => X a i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap L).contDiff
  have hs : ∀ (a : Fin 5) (i j : Fin 2),
      ContDiff ℝ ∞ (fun X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ => star (X a i j)) := fun a i j =>
    Complex.conjCLE.contDiff.comp (hX a i j)
  have := hX (edgeSrc e) 0 0
  have := hs (edgeSrc e) 0 0
  have := hX (edgeSrc e) 0 1
  have := hs (edgeSrc e) 0 1
  have := hX (edgeSrc e) 1 0
  have := hs (edgeSrc e) 1 0
  have := hX (edgeSrc e) 1 1
  have := hs (edgeSrc e) 1 1
  have := hX (edgeTgt e) 0 0
  have := hs (edgeTgt e) 0 0
  have := hX (edgeTgt e) 0 1
  have := hs (edgeTgt e) 0 1
  have := hX (edgeTgt e) 1 0
  have := hs (edgeTgt e) 1 0
  have := hX (edgeTgt e) 1 1
  have := hs (edgeTgt e) 1 1
  repeat' (first | exact contDiff_const | assumption | apply ContDiff.add | apply ContDiff.mul)

lemma contDiff_cohAmp' (n : Fin 10 → ℕ) (g : BdryData) :
    ContDiff ℝ ∞ (fun X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ => cohAmp n g X) := by
  unfold cohAmp
  exact contDiff_prod fun e _ => (contDiff_prop g e).pow _

/-- `t ↦ (1 + t² s)^(-1/2)`. -/
noncomputable def gscal (s : ℝ) (t : ℝ) : ℝ := (1 + t ^ 2 * s) ^ (-(1/2 : ℝ))

lemma gscal_hasDerivAt {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    HasDerivAt (gscal s) (-(t * s) * (1 + t ^ 2 * s) ^ (-(3/2 : ℝ))) t := by
  have hpos : 0 < 1 + t ^ 2 * s := by positivity
  have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2 * s) (2 * t * s) t := by
    have := ((hasDerivAt_pow 2 t).mul_const s).const_add 1
    simpa using this
  have := h1.rpow_const (p := -(1/2 : ℝ)) (Or.inl hpos.ne')
  have e : (1 + t ^ 2 * s) ^ (-(1/2 : ℝ) - 1) = (1 + t ^ 2 * s) ^ (-(3/2 : ℝ)) := by norm_num
  rw [e] at this
  unfold gscal
  convert this using 1
  ring

lemma gscal_deriv {s : ℝ} (hs : 0 ≤ s) :
    deriv (gscal s) = fun t => -(t * s) * (1 + t ^ 2 * s) ^ (-(3/2 : ℝ)) :=
  funext fun t => (gscal_hasDerivAt hs t).deriv

lemma gscal_hasDerivAt₂ {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (deriv (gscal s)) (-s) 0 := by
  rw [gscal_deriv hs]
  have hpos : ∀ t : ℝ, 0 < 1 + t ^ 2 * s := fun t => by positivity
  have h1 : HasDerivAt (fun t : ℝ => -(t * s)) (-s) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).mul_const s).neg
    convert this using 1
    · funext t; simp
    · simp
  have h2 : HasDerivAt (fun t : ℝ => (1 + t ^ 2 * s) ^ (-(3/2 : ℝ))) 0 0 := by
    have h : HasDerivAt (fun t : ℝ => 1 + t ^ 2 * s) (2 * 0 * s) 0 := by
      have := ((hasDerivAt_pow 2 (0:ℝ)).mul_const s).const_add 1
      simpa using this
    have := h.rpow_const (p := -(3/2 : ℝ)) (Or.inl (hpos 0).ne')
    simpa using this
  have := h1.mul h2
  convert this using 1
  simp

lemma contDiff_gscal {s : ℝ} (hs : 0 ≤ s) : ContDiff ℝ ∞ (gscal s) := by
  unfold gscal
  refine ContDiff.rpow_const_of_ne (by fun_prop) fun t => ?_
  positivity

/-- The matrix `N(w)`: the first-order part of the gnomonic quaternion `(1, w)`. -/
noncomputable def Nmat (w : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![I * w 0, w 1 + I * w 2; -(w 1 : ℂ) + I * w 2, -(I * w 0)]

/-- The gnomonic curve `t ↦ (1 + tN(w)) / √(1 + t²|w|²)`. -/
noncomputable def gcurve (w : Fin 3 → ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  gscal (∑ k, w k ^ 2) t • (1 + t • Nmat w)

lemma gcurve_hasDerivAt (w : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (gcurve w) ((-(t * ∑ k, w k ^ 2) * (1 + t ^ 2 * ∑ k, w k ^ 2) ^ (-(3/2 : ℝ))) •
      (1 + t • Nmat w) + gscal (∑ k, w k ^ 2) t • Nmat w) t := by
  have hs : 0 ≤ ∑ k, w k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h2 : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) + t • Nmat w) (Nmat w) t := by
    have := ((hasDerivAt_id t).smul_const (Nmat w)).const_add (1 : Matrix (Fin 2) (Fin 2) ℂ)
    convert this using 1 <;> first | rfl | simp
  have := (gscal_hasDerivAt hs t).smul h2
  convert this using 1 <;> first | rfl | (rw [add_comm])

lemma gcurve_deriv (w : Fin 3 → ℝ) : deriv (gcurve w) = fun t =>
    (-(t * ∑ k, w k ^ 2) * (1 + t ^ 2 * ∑ k, w k ^ 2) ^ (-(3/2 : ℝ))) • (1 + t • Nmat w) +
      gscal (∑ k, w k ^ 2) t • Nmat w := funext fun t => (gcurve_hasDerivAt w t).deriv

lemma gcurve_zero (w : Fin 3 → ℝ) : gcurve w 0 = 1 := by simp [gcurve, gscal]

lemma gcurve_deriv_zero (w : Fin 3 → ℝ) : deriv (gcurve w) 0 = Nmat w := by
  rw [gcurve_deriv]; simp [gscal]

lemma gcurve_deriv₂_zero (w : Fin 3 → ℝ) :
    deriv (deriv (gcurve w)) 0 = -(∑ k, w k ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hs : 0 ≤ ∑ k, w k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [gcurve_deriv]
  have hA : HasDerivAt (fun t : ℝ => (-(t * ∑ k, w k ^ 2) *
      (1 + t ^ 2 * ∑ k, w k ^ 2) ^ (-(3/2 : ℝ))) • (1 + t • Nmat w)) (-(∑ k, w k ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 := by
    have h1 := gscal_hasDerivAt₂ hs
    rw [gscal_deriv hs] at h1
    have h2 : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) + t • Nmat w) (Nmat w) 0 := by
      have := ((hasDerivAt_id (0:ℝ)).smul_const (Nmat w)).const_add (1 : Matrix (Fin 2) (Fin 2) ℂ)
      convert this using 1 <;> first | rfl | simp
    have := h1.smul h2
    convert this using 1 <;> first | rfl | simp
  have hB : HasDerivAt (fun t : ℝ => gscal (∑ k, w k ^ 2) t • Nmat w) 0 0 := by
    have := (gscal_hasDerivAt hs 0).smul_const (Nmat w)
    convert this using 1 <;> first | rfl | simp
  exact (hA.add hB).deriv.trans (by simp)

/-- The swap `0 ↔ 2` of the three coordinates of a block. -/
def swp : Fin 3 → Fin 3 := ![2, 1, 0]

lemma su2Gen_two_swp (w : Fin 3 → ℝ) : su2Gen (fun k => 2 * w (swp k)) = Nmat w := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [su2Gen, Nmat, swp]

lemma Nmat_mul_self (w : Fin 3 → ℝ) :
    Nmat w * Nmat w = (-(∑ k, w k ^ 2) : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Nmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, pow_two] <;> ring

lemma su2Gen_smul (t : ℝ) (θ : Fin 3 → ℝ) : su2Gen (t • θ) = t • su2Gen θ := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [su2Gen] <;> ring

/-- The exponential curve `t ↦ exp(t B)`. -/
noncomputable def ecurve (B : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp (t • B)

lemma ecurve_hasDerivAt (B : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (ecurve B) (ecurve B t * B) t := hasDerivAt_exp_smul_const B t

lemma ecurve_deriv (B : Matrix (Fin 2) (Fin 2) ℂ) :
    deriv (ecurve B) = fun t => ecurve B t * B := funext fun t => (ecurve_hasDerivAt B t).deriv

lemma ecurve_zero (B : Matrix (Fin 2) (Fin 2) ℂ) : ecurve B 0 = 1 := by simp [ecurve]

lemma ecurve_deriv_zero (B : Matrix (Fin 2) (Fin 2) ℂ) : deriv (ecurve B) 0 = B := by
  rw [ecurve_deriv]; simp [ecurve_zero]

lemma ecurve_deriv₂_zero (B : Matrix (Fin 2) (Fin 2) ℂ) :
    deriv (deriv (ecurve B)) 0 = B * B := by
  rw [ecurve_deriv]
  have := (ecurve_hasDerivAt B 0).mul_const B
  exact this.deriv.trans (by simp [ecurve_zero])

lemma contDiff_ecurve (B : Matrix (Fin 2) (Fin 2) ℂ) : ContDiff ℝ ∞ (ecurve B) := by
  have h1 : ContDiff ℝ ∞ (fun x : Matrix (Fin 2) (Fin 2) ℂ => NormedSpace.exp x) :=
    contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact h1.comp (contDiff_id.smul contDiff_const)

/-- The block curve `t ↦ (X_a F_a(t))_{a<4}`, with the entry `E_4` in the last slot. -/
noncomputable def pcurve (X E : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    (F : Fin 4 → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun a => if h : (a : ℕ) < 4 then X a * F ⟨a, h⟩ t else E a

lemma pcurve_hasDerivAt (X E : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    (F F' : Fin 4 → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hF : ∀ a t, HasDerivAt (F a) (F' a t) t) (t : ℝ) :
    HasDerivAt (pcurve X E F) (pcurve X 0 F' t) t := by
  refine hasDerivAt_pi.mpr fun a => ?_
  by_cases h : (a : ℕ) < 4
  · simp only [pcurve, h, dite_true]
    exact (hF ⟨a, h⟩ t).const_mul (X a)
  · simp only [pcurve, h, dite_false]
    exact hasDerivAt_const _ _

lemma contDiff_pcurve (X E : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    {F : Fin 4 → ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hF : ∀ a, ContDiff ℝ ∞ (F a)) :
    ContDiff ℝ ∞ (pcurve X E F) := by
  refine contDiff_pi.mpr fun a => ?_
  by_cases h : (a : ℕ) < 4
  · simp only [pcurve, h, dite_true]
    exact contDiff_const.mul (hF ⟨a, h⟩)
  · simp only [pcurve, h, dite_false]
    exact contDiff_const

lemma hasDerivAt_deriv_of_contDiff {F : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    HasDerivAt F (deriv F t) t :=
  ((hF.differentiable (by simp)) t).hasDerivAt

lemma pcurve_deriv (X E : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    {F : Fin 4 → ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hF : ∀ a, ContDiff ℝ ∞ (F a)) :
    deriv (pcurve X E F) = pcurve X 0 (fun a => deriv (F a)) :=
  funext fun t => (pcurve_hasDerivAt X E F _ (fun a t => hasDerivAt_deriv_of_contDiff (hF a) t) t).deriv

lemma pcurve_deriv₂ (X E : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    {F : Fin 4 → ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hF : ∀ a, ContDiff ℝ ∞ (F a)) :
    deriv (deriv (pcurve X E F)) = pcurve X 0 (fun a => deriv (deriv (F a))) := by
  rw [pcurve_deriv X E hF]
  have hF' : ∀ a, ContDiff ℝ ∞ (deriv (F a)) := fun a => (contDiff_infty_iff_deriv.mp (hF a)).2
  funext t
  exact (pcurve_hasDerivAt X 0 (fun a => deriv (F a)) _
    (fun a t => hasDerivAt_deriv_of_contDiff (hF' a) t) t).deriv

/-- Two block curves whose blocks have the same 2-jet at `0` give the same second derivative of
any smooth function along them. -/
theorem iteratedDeriv_two_pcurve_eq {Φ : (Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (X E : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    {F G : Fin 4 → ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (hG : ∀ a, ContDiff ℝ ∞ (G a)) (h0 : ∀ a, F a 0 = G a 0)
    (h1 : ∀ a, deriv (F a) 0 = deriv (G a) 0)
    (h2 : ∀ a, deriv (deriv (F a)) 0 = deriv (deriv (G a)) 0) :
    iteratedDeriv 2 (Φ ∘ pcurve X E F) 0 = iteratedDeriv 2 (Φ ∘ pcurve X E G) 0 := by
  refine iteratedDeriv_two_comp_eq hΦ (contDiff_pcurve X E hF) (contDiff_pcurve X E hG) ?_ ?_ ?_
  · funext a; simp only [pcurve, h0]
  · refine (congrFun (pcurve_deriv X E hF) 0).trans (Eq.trans ?_ (congrFun (pcurve_deriv X E hG) 0).symm)
    funext a; simp only [pcurve, h1]
  · refine (congrFun (pcurve_deriv₂ X E hF) 0).trans
      (Eq.trans ?_ (congrFun (pcurve_deriv₂ X E hG) 0).symm)
    funext a; simp only [pcurve, h2]

/-! ## The charts -/

/-- `N` as an `ℝ`-linear map, to get smoothness. -/
noncomputable def NmatL : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := Nmat
  map_add' x y := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [Nmat] <;> ring
  map_smul' c x := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [Nmat]

lemma contDiff_Nmat : ContDiff ℝ ∞ Nmat := (LinearMap.toContinuousLinearMap NmatL).contDiff

lemma Nmat_smul (t : ℝ) (w : Fin 3 → ℝ) : Nmat (t • w) = t • Nmat w := NmatL.map_smul t w

/-- `su2Gen` as an `ℝ`-linear map. -/
noncomputable def su2GenL : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := su2Gen
  map_add' x y := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [su2Gen] <;> ring
  map_smul' c x := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [su2Gen] <;> ring

lemma contDiff_su2Gen : ContDiff ℝ ∞ su2Gen := (LinearMap.toContinuousLinearMap su2GenL).contDiff

/-- The `a`-th block of coordinates of a point of `ℝ^12`. -/
def blk (q : Fin 12 → ℝ) (a : Fin 4) : Fin 3 → ℝ := fun k => q (finProdFinEquiv (a, k))

lemma blk_smul (t : ℝ) (q : Fin 12 → ℝ) (a : Fin 4) : blk (t • q) a = t • blk q a := rfl

lemma contDiff_blk (a : Fin 4) : ContDiff ℝ ∞ (fun q : Fin 12 → ℝ => blk q a) :=
  contDiff_pi.mpr fun k =>
    show ContDiff ℝ ∞ (fun q : Fin 12 → ℝ => q (finProdFinEquiv (a, k))) from
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 12 => ℝ)
        (finProdFinEquiv (a, k) : Fin 12)).contDiff

/-- The gnomonic matrix `(1 + N(w)) / √(1 + |w|²)`, the quaternion `(1, w) / √(1 + |w|²)`. -/
noncomputable def gmat (w : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 + ∑ k, w k ^ 2) ^ (-(1/2 : ℝ)) • (1 + Nmat w)

lemma contDiff_gmat : ContDiff ℝ ∞ gmat := by
  unfold gmat
  refine ContDiff.smul (ContDiff.rpow_const_of_ne (by fun_prop) fun w => ?_) (contDiff_const.add contDiff_Nmat)
  have : 0 ≤ ∑ k, w k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  positivity

lemma gmat_smul (t : ℝ) (w : Fin 3 → ℝ) : gmat (t • w) = gcurve w t := by
  unfold gmat gcurve gscal
  rw [Nmat_smul]
  congr 2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]

/-- The gnomonic chart of `SU(2)^4` around `X`. -/
noncomputable def qchart (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (q : Fin 12 → ℝ) :
    Fin 5 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun a => if h : (a : ℕ) < 4 then X a * gmat (blk q ⟨a, h⟩) else X a

lemma qchart_smul (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) (v : Fin 12 → ℝ) :
    qchart X (t • v) = pcurve X X (fun a t => gcurve (blk v a) t) t := by
  funext a
  simp only [qchart, pcurve, blk_smul, gmat_smul]

lemma contDiff_qchart (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) : ContDiff ℝ ∞ (qchart X) := by
  refine contDiff_pi.mpr fun a => ?_
  by_cases h : (a : ℕ) < 4
  · simp only [qchart, h, dite_true]
    exact contDiff_const.mul (contDiff_gmat.comp (contDiff_blk _))
  · simp only [qchart, h, dite_false]
    exact contDiff_const

lemma chart_smul (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) (u : Fin 12 → ℝ) :
    chart X (t • u) = pcurve X X (fun a t => ecurve (su2Gen (blk u a)) t) t := by
  funext a
  by_cases h : (a : ℕ) < 4
  · simp only [chart, pcurve, h, dite_true, ecurve]
    have : (fun k => (t • u) (finProdFinEquiv (⟨a, h⟩, k))) = t • blk u ⟨a, h⟩ := rfl
    rw [this, su2Gen_smul]
  · simp [chart, pcurve, h]

lemma contDiff_chartE (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) : ContDiff ℝ ∞ (chart X) := by
  refine contDiff_pi.mpr fun a => ?_
  by_cases h : (a : ℕ) < 4
  · simp only [chart, h, dite_true]
    have h1 : ContDiff ℝ ∞ (fun x : Matrix (Fin 2) (Fin 2) ℂ => NormedSpace.exp x) :=
      contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    exact contDiff_const.mul (h1.comp (contDiff_su2Gen.comp (contDiff_blk ⟨a, h⟩)))
  · simp only [chart, h, dite_false]
    exact contDiff_const

/-! ## The Hessian comparison -/

lemma contDiff_gcurve (w : Fin 3 → ℝ) : ContDiff ℝ ∞ (gcurve w) := by
  have hs : 0 ≤ ∑ k, w k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  unfold gcurve
  exact (contDiff_gscal hs).smul (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- The swap `0 ↔ 2` inside each block of three coordinates of `ℝ^12`. -/
def perm12 : Equiv.Perm (Fin 12) :=
  finProdFinEquiv.symm.trans ((Equiv.prodCongr (Equiv.refl (Fin 4)) (Equiv.swap (0 : Fin 3) 2)).trans
    finProdFinEquiv)

lemma perm12_apply (a : Fin 4) (k : Fin 3) :
    perm12 (finProdFinEquiv (a, k)) = finProdFinEquiv (a, Equiv.swap (0 : Fin 3) 2 k) := by
  simp [perm12]

lemma swap_eq_swp (k : Fin 3) : Equiv.swap (0 : Fin 3) 2 k = swp k := by
  fin_cases k
  · simp [swp]
  · simp [swp]; exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  · simp [swp]

lemma perm12_perm12 (i : Fin 12) : perm12 (perm12 i) = i := by
  obtain ⟨⟨a, k⟩, rfl⟩ := (finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12).surjective i
  rw [perm12_apply, perm12_apply]
  simp

/-- **The two charts have the same second derivative** along `t ↦ qchart X (t v)` and
`t ↦ chart X (t u)` for `u = 2 v ∘ perm12`. -/
theorem iteratedDeriv_two_qchart (n : Fin 10 → ℕ) (g : BdryData)
    (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 12 → ℝ) :
    iteratedDeriv 2 (fun t : ℝ => cohAmp n g (qchart X (t • v))) 0 =
      iteratedDeriv 2 (fun t : ℝ => cohAmp n g (chart X (t • fun i => 2 * v (perm12 i)))) 0 := by
  have hblk : ∀ a : Fin 4, blk (fun i => 2 * v (perm12 i)) a = fun k => 2 * blk v a (swp k) := by
    intro a; funext k
    simp only [blk, perm12_apply, swap_eq_swp]
  have e1 : (fun t : ℝ => cohAmp n g (qchart X (t • v))) =
      (cohAmp n g) ∘ pcurve X X (fun a t => gcurve (blk v a) t) := by
    funext t; simp only [Function.comp, qchart_smul]
  have e2 : (fun t : ℝ => cohAmp n g (chart X (t • fun i => 2 * v (perm12 i)))) =
      (cohAmp n g) ∘ pcurve X X (fun a t => ecurve (su2Gen (blk (fun i => 2 * v (perm12 i)) a)) t) := by
    funext t; simp only [Function.comp, chart_smul]
  rw [e1, e2]
  refine iteratedDeriv_two_pcurve_eq (contDiff_cohAmp' n g) X X
    (fun a => contDiff_gcurve _) (fun a => contDiff_ecurve _) (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · rw [gcurve_zero, ecurve_zero]
  · rw [gcurve_deriv_zero, ecurve_deriv_zero, hblk, su2Gen_two_swp]
  · rw [gcurve_deriv₂_zero, ecurve_deriv₂_zero, hblk, su2Gen_two_swp, Nmat_mul_self]

/-- **The Hessian in the gnomonic chart** is `4 P H_θ P`, with `H_θ` the Hessian in the exponential
chart and `P` the block swap `perm12`. -/
theorem hessMat_qchart (n : Fin 10 → ℕ) (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) :
    hessMat (fun q => cohAmp n g (qchart X q)) 0 =
      (4 : ℂ) • (hessMat (fun θ => cohAmp n g (chart X θ)) 0).submatrix perm12 perm12 := by
  have hq : ContDiff ℝ ∞ (fun q => cohAmp n g (qchart X q)) :=
    (contDiff_cohAmp' n g).comp (contDiff_qchart X)
  have hθ : ContDiff ℝ ∞ (fun θ => cohAmp n g (chart X θ)) :=
    (contDiff_cohAmp' n g).comp (contDiff_chartE X)
  rw [← sub_eq_zero]
  refine eq_zero_of_isSymm_of_qform ?_ fun v => ?_
  · refine (hessMat_isSymm hq 0).sub ?_
    refine Matrix.IsSymm.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.submatrix_apply]
    have := (hessMat_isSymm hθ 0).apply (perm12 i) (perm12 j)
    rw [this]
  · have h1 := iteratedDeriv_two_line hq v
    have h2 := iteratedDeriv_two_line hθ (fun i => 2 * v (perm12 i))
    have h3 := iteratedDeriv_two_qchart n g X v
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib]
    rw [← h1, h3, h2]
    have hre : ∑ i, ∑ j, (v i : ℂ) * v j * (4 * hessMat (fun θ => cohAmp n g (chart X θ)) 0
        (perm12 i) (perm12 j)) =
        ∑ i, ∑ j, ((2 * v (perm12 i) : ℝ) : ℂ) * (2 * v (perm12 j) : ℝ) *
          hessMat (fun θ => cohAmp n g (chart X θ)) 0 i j := by
      rw [← Equiv.sum_comp perm12 (fun i => ∑ j, ((2 * v (perm12 i) : ℝ) : ℂ) * (2 * v (perm12 j) : ℝ) *
          hessMat (fun θ => cohAmp n g (chart X θ)) 0 i j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Equiv.sum_comp perm12]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [perm12_perm12]
      push_cast
      ring
    rw [hre]
    ring

/-! ## The gradient -/

/-- The derivative of a function along a line through `0` is the Fréchet derivative applied to the
direction. -/
lemma deriv_line {n : ℕ} {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (u : Fin n → ℝ) :
    deriv (fun t : ℝ => φ (t • u)) 0 = fderiv ℝ φ 0 u := by
  have h1 : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have h2 : HasFDerivAt φ (fderiv ℝ φ ((0 : ℝ) • u)) ((0 : ℝ) • u) :=
    ((hφ.differentiable (by simp)) _).hasFDerivAt
  have h3 := (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
  rw [show (fun t : ℝ => φ (t • u)) = φ ∘ fun t : ℝ => t • u from rfl]
  simpa using h3

/-- A function with vanishing partial derivatives at `0` has vanishing derivative there. -/
lemma fderiv_eq_zero_of_coordDeriv {n : ℕ} {φ : (Fin n → ℝ) → ℂ}
    (h : ∀ l, Lightlike.Oscillatory.coordDeriv φ l 0 = 0) : fderiv ℝ φ 0 = 0 := by
  classical
  refine ContinuousLinearMap.ext fun u => ?_
  have hu : u = ∑ l, u l • (Pi.single l 1 : Fin n → ℝ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  rw [hu, map_sum]
  simp only [map_smul, _root_.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  have := h l
  unfold Lightlike.Oscillatory.coordDeriv at this
  rw [this]; simp

/-- The first derivatives along the two charts agree (up to the factor 2 and the swap `perm12`). -/
theorem deriv_qchart (n : Fin 10 → ℕ) (g : BdryData)
    (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 12 → ℝ) :
    deriv (fun t : ℝ => cohAmp n g (qchart X (t • v))) 0 =
      deriv (fun t : ℝ => cohAmp n g (chart X (t • fun i => 2 * v (perm12 i)))) 0 := by
  have hblk : ∀ a : Fin 4, blk (fun i => 2 * v (perm12 i)) a = fun k => 2 * blk v a (swp k) := by
    intro a; funext k
    simp only [blk, perm12_apply, swap_eq_swp]
  have e1 : (fun t : ℝ => cohAmp n g (qchart X (t • v))) =
      (cohAmp n g) ∘ pcurve X X (fun a t => gcurve (blk v a) t) := by
    funext t; simp only [Function.comp, qchart_smul]
  have e2 : (fun t : ℝ => cohAmp n g (chart X (t • fun i => 2 * v (perm12 i)))) =
      (cohAmp n g) ∘ pcurve X X (fun a t => ecurve (su2Gen (blk (fun i => 2 * v (perm12 i)) a)) t) := by
    funext t; simp only [Function.comp, chart_smul]
  rw [e1, e2]
  have hF : ∀ a, ContDiff ℝ ∞ (fun t => gcurve (blk v a) t) := fun a => contDiff_gcurve _
  have hG : ∀ a, ContDiff ℝ ∞ (fun t => ecurve (su2Gen (blk (fun i => 2 * v (perm12 i)) a)) t) :=
    fun a => contDiff_ecurve _
  have hc1 := contDiff_pcurve X X hF
  have hc2 := contDiff_pcurve X X hG
  have d1 := fderiv_comp_deriv (𝕜 := ℝ) (0 : ℝ) (((contDiff_cohAmp' n g).differentiable (by simp)) _)
    ((hc1.differentiable (by simp)) 0)
  have d2 := fderiv_comp_deriv (𝕜 := ℝ) (0 : ℝ) (((contDiff_cohAmp' n g).differentiable (by simp)) _)
    ((hc2.differentiable (by simp)) 0)
  have hv : pcurve X X (fun a t => gcurve (blk v a) t) 0 =
      pcurve X X (fun a t => ecurve (su2Gen (blk (fun i => 2 * v (perm12 i)) a)) t) 0 := by
    funext a; simp only [pcurve, gcurve_zero, ecurve_zero]
  have hd : deriv (pcurve X X (fun a t => gcurve (blk v a) t)) 0 =
      deriv (pcurve X X (fun a t => ecurve (su2Gen (blk (fun i => 2 * v (perm12 i)) a)) t)) 0 := by
    refine (congrFun (pcurve_deriv X X hF) 0).trans (Eq.trans ?_ (congrFun (pcurve_deriv X X hG) 0).symm)
    funext a
    simp only [pcurve, gcurve_deriv_zero, ecurve_deriv_zero, hblk, su2Gen_two_swp]
  rw [show deriv ((cohAmp n g) ∘ pcurve X X (fun a t => gcurve (blk v a) t)) 0 =
      fderiv ℝ (cohAmp n g) (pcurve X X (fun a t => gcurve (blk v a) t) 0)
        (deriv (pcurve X X (fun a t => gcurve (blk v a) t)) 0) from d1,
    show deriv ((cohAmp n g) ∘ pcurve X X (fun a t => ecurve
      (su2Gen (blk (fun i => 2 * v (perm12 i)) a)) t)) 0 =
      fderiv ℝ (cohAmp n g) (pcurve X X (fun a t => ecurve
        (su2Gen (blk (fun i => 2 * v (perm12 i)) a)) t) 0)
        (deriv (pcurve X X (fun a t => ecurve
          (su2Gen (blk (fun i => 2 * v (perm12 i)) a)) t)) 0) from d2, hv, hd]

/-- **Stationarity transfers to the gnomonic chart**: if the partial derivatives of the coherent
amplitude in the exponential chart vanish, so do those in the gnomonic chart. -/
theorem coordDeriv_qchart_eq_zero (n : Fin 10 → ℕ) (g : BdryData)
    (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ l : Fin 12, Lightlike.Oscillatory.coordDeriv (fun θ => cohAmp n g (chart X θ)) l 0 = 0) :
    ∀ l : Fin 12, Lightlike.Oscillatory.coordDeriv (fun q => cohAmp n g (qchart X q)) l 0 = 0 := by
  have hq : ContDiff ℝ ∞ (fun q => cohAmp n g (qchart X q)) :=
    (contDiff_cohAmp' n g).comp (contDiff_qchart X)
  have hθ : ContDiff ℝ ∞ (fun θ => cohAmp n g (chart X θ)) :=
    (contDiff_cohAmp' n g).comp (contDiff_chartE X)
  have h0 := fderiv_eq_zero_of_coordDeriv h
  intro l
  have h1 := deriv_qchart n g X (Pi.single l 1)
  rw [deriv_line hq, deriv_line hθ, h0] at h1
  unfold Lightlike.Oscillatory.coordDeriv
  simpa using h1

end Lightlike.Asymptotics.EPRL
