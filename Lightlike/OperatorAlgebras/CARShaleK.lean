import Lightlike.OperatorAlgebras.CARShaleVec

/-!
# The operator `K = β*β` of a Bogoliubov map

`R` is a surjective real-linear map of `Z` preserving `Re⟪·,·⟫`, `S` its inverse, `J = i·`. With `X = S J R J` and
`Y = J S J R` (`X Y = Y X = 1`), the operator `K = (2 + X + Y)/4` is complex-linear, symmetric and satisfies
`⟪β u, β v⟫ = ⟪K v, u⟫` where `β v = (R v + i R(i v))/2` is the antilinear part of `R`. The operator `A = (X - Y)/2` commutes
with `K` and `Re⟪α u, β v⟫ = Re⟪u, A v⟫/2`, so `α u` and `β v` are orthogonal for eigenvectors of `K` of different
eigenvalues.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.CARShale

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z] (R : Z →ₗ[ℝ] Z)
  (hR : ∀ w w', (⟪R w, R w'⟫_ℂ).re = (⟪w, w'⟫_ℂ).re)

include hR in
/-- A map preserving `Re⟪·,·⟫` is injective. -/
lemma R_injective : Function.Injective R := by
  intro u v h
  have h1 := norm_R R hR (u - v)
  rw [map_sub, h, sub_self, norm_zero] at h1
  exact sub_eq_zero.1 (norm_eq_zero.1 h1.symm)

/-- Multiplication by `i` as a real-linear map. -/
noncomputable def Jr : Z →ₗ[ℝ] Z := (LinearMap.lsmul ℂ Z Complex.I : Z →ₗ[ℂ] Z).restrictScalars ℝ

@[simp] lemma Jr_apply (v : Z) : Jr (Z := Z) v = Complex.I • v := rfl

/-- Auxiliary lemma `Jr_Jr` for the fermionic Shale theorem. -/
lemma Jr_Jr (v : Z) : Jr (Z := Z) (Jr v) = -v := by simp [smul_smul]

variable (hRs : Function.Surjective R)

/-- The inverse of `R`. -/
noncomputable def Sinv : Z →ₗ[ℝ] Z := (LinearEquiv.ofBijective R ⟨R_injective R hR, hRs⟩).symm

include hR hRs in
/-- Auxiliary lemma `R_Sinv` for the fermionic Shale theorem. -/
lemma R_Sinv (w : Z) : R (Sinv R hR hRs w) = w :=
  (LinearEquiv.ofBijective R ⟨R_injective R hR, hRs⟩).apply_symm_apply w

include hR hRs in
/-- Auxiliary lemma `Sinv_R` for the fermionic Shale theorem. -/
lemma Sinv_R (v : Z) : Sinv R hR hRs (R v) = v :=
  (LinearEquiv.ofBijective R ⟨R_injective R hR, hRs⟩).symm_apply_apply v

include hR hRs in
/-- `Re⟪R u, w⟫ = Re⟪u, S w⟫`. -/
lemma re_inner_R_left (u w : Z) : (⟪R u, w⟫_ℂ).re = (⟪u, Sinv R hR hRs w⟫_ℂ).re := by
  conv_lhs => rw [← R_Sinv R hR hRs w]
  exact hR _ _

include hR hRs in
/-- `Re⟪S u, w⟫ = Re⟪u, R w⟫`. -/
lemma re_inner_S_left (u w : Z) : (⟪Sinv R hR hRs u, w⟫_ℂ).re = (⟪u, R w⟫_ℂ).re := by
  conv_rhs => rw [← R_Sinv R hR hRs u]
  rw [hR]

/-- `X = S J R J`. -/
noncomputable def Xr : Z →ₗ[ℝ] Z := Sinv R hR hRs ∘ₗ Jr ∘ₗ R ∘ₗ Jr

/-- `Y = J S J R`. -/
noncomputable def Yr : Z →ₗ[ℝ] Z := Jr ∘ₗ Sinv R hR hRs ∘ₗ Jr ∘ₗ R

include hR hRs in
/-- Auxiliary lemma `Yr_Xr` for the fermionic Shale theorem. -/
lemma Yr_Xr (v : Z) : Yr R hR hRs (Xr R hR hRs v) = v := by
  simp only [Xr, Yr, LinearMap.comp_apply, Jr_apply, R_Sinv R hR hRs, Jr_Jr, Sinv_R R hR hRs, map_neg, smul_neg,
    smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg, Jr_apply, map_smul]

include hR hRs in
/-- Auxiliary lemma `Xr_Yr` for the fermionic Shale theorem. -/
lemma Xr_Yr (v : Z) : Xr R hR hRs (Yr R hR hRs v) = v := by
  simp only [Xr, Yr, LinearMap.comp_apply, Jr_apply, R_Sinv R hR hRs, Sinv_R R hR hRs, map_neg, smul_neg,
    smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg, Jr_apply, map_smul]

/-- `K = (2 + X + Y) / 4`. -/
noncomputable def Kr : Z →ₗ[ℝ] Z :=
  (1 / 2 : ℝ) • (LinearMap.id : Z →ₗ[ℝ] Z) + (1 / 4 : ℝ) • (Xr R hR hRs + Yr R hR hRs)

include hR hRs in
/-- Auxiliary lemma `Kr_apply` for the fermionic Shale theorem. -/
lemma Kr_apply (v : Z) : Kr R hR hRs v = (1 / 2 : ℝ) • v + (1 / 4 : ℝ) • (Xr R hR hRs v + Yr R hR hRs v) := rfl

include hR hRs in
/-- `K` commutes with `i`. -/
lemma Kr_I (v : Z) : Kr R hR hRs (Complex.I • v) = Complex.I • Kr R hR hRs v := by
  have hX : Xr R hR hRs (Complex.I • v) = Complex.I • Yr R hR hRs v := by
    simp only [Xr, Yr, LinearMap.comp_apply, Jr_apply, map_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul,
      map_neg, smul_neg]
  have hY : Yr R hR hRs (Complex.I • v) = Complex.I • Xr R hR hRs v := by
    simp only [Xr, Yr, LinearMap.comp_apply, Jr_apply]
  rw [Kr_apply, Kr_apply, hX, hY]
  have e1 : ∀ (r : ℝ) (w : Z), Complex.I • (r • w) = r • (Complex.I • w) := fun r w => smul_comm _ _ _
  rw [smul_add, smul_add, e1, e1, smul_add, smul_add, add_comm ((1 / 4 : ℝ) • Complex.I • Yr R hR hRs v)]

/-- Auxiliary lemma `re_inner_I_swap` for the fermionic Shale theorem. -/
lemma re_inner_I_swap (x y : Z) : (⟪Complex.I • x, y⟫_ℂ).re = -(⟪x, Complex.I • y⟫_ℂ).re := by
  rw [re_inner_I_left, re_inner_I_right, neg_neg]

include hR hRs in
/-- `Re⟪X u, v⟫ = Re⟪u, Y v⟫`. -/
lemma re_inner_Xr (u v : Z) : (⟪Xr R hR hRs u, v⟫_ℂ).re = (⟪u, Yr R hR hRs v⟫_ℂ).re := by
  simp only [Xr, Yr, LinearMap.comp_apply, Jr_apply]
  rw [re_inner_S_left R hR hRs, re_inner_I_swap, re_inner_R_left R hR hRs, re_inner_I_swap]
  rw [neg_neg]

include hR hRs in
/-- `Re⟪Y u, v⟫ = Re⟪u, X v⟫`. -/
lemma re_inner_Yr (u v : Z) : (⟪Yr R hR hRs u, v⟫_ℂ).re = (⟪u, Xr R hR hRs v⟫_ℂ).re := by
  simp only [Xr, Yr, LinearMap.comp_apply, Jr_apply]
  rw [re_inner_I_swap, re_inner_S_left R hR hRs, re_inner_I_swap, re_inner_R_left R hR hRs]
  exact neg_neg _

include hR hRs in
/-- `K v = v/2 + (X v + Y v)/4` with complex coefficients. -/
lemma Kr_apply_c (v : Z) : Kr R hR hRs v = (1 / 2 : ℂ) • v + (1 / 4 : ℂ) • (Xr R hR hRs v + Yr R hR hRs v) := by
  rw [Kr_apply]
  have h1 : ∀ (r : ℝ) (w : Z), r • w = (r : ℂ) • w := fun r w => (Complex.coe_smul r w).symm
  rw [h1, h1]; push_cast; rfl

include hR hRs in
/-- `K` is real-symmetric: `Re⟪K u, v⟫ = Re⟪u, K v⟫`. -/
lemma re_inner_Kr (u v : Z) : (⟪Kr R hR hRs u, v⟫_ℂ).re = (⟪u, Kr R hR hRs v⟫_ℂ).re := by
  rw [Kr_apply_c, Kr_apply_c, inner_add_left, inner_add_right, Complex.add_re, Complex.add_re, inner_smul_left,
    inner_smul_right, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right]
  have e1 := re_inner_Xr R hR hRs u v
  have e2 := re_inner_Yr R hR hRs u v
  have e3 := re_inner_Xr R hR hRs v u
  have e4 := re_inner_Yr R hR hRs v u
  have c2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have c4 : starRingEnd ℂ (1 / 4 : ℂ) = 1 / 4 := by rw [map_div₀, map_one, map_ofNat]
  rw [c2, c4]
  simp only [Complex.mul_re, Complex.add_re, Complex.div_re, Complex.one_re, Complex.one_im]
  norm_num
  linarith

include hR hRs in
/-- Auxiliary lemma `Kr_smul` for the fermionic Shale theorem. -/
lemma Kr_smul (c : ℂ) (v : Z) : Kr R hR hRs (c • v) = c • Kr R hR hRs v := by
  have he : c • v = c.re • v + c.im • (Complex.I • v) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [he, map_add, map_smul, map_smul, Kr_I R hR hRs]
  conv_rhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, Complex.coe_smul]
  simp only [Complex.coe_smul]

include hR hRs in
/-- `K` as a complex-linear map. -/
noncomputable def Kc : Z →ₗ[ℂ] Z where
  toFun := Kr R hR hRs
  map_add' := map_add _
  map_smul' c v := Kr_smul R hR hRs c v

include hR hRs in
/-- Auxiliary lemma `inner_Kc` for the fermionic Shale theorem. -/
lemma inner_Kc (u v : Z) : ⟪Kc R hR hRs u, v⟫_ℂ = ⟪u, Kc R hR hRs v⟫_ℂ := by
  apply Complex.ext
  · exact re_inner_Kr R hR hRs u v
  · have h1 : (⟪Kc R hR hRs u, v⟫_ℂ).im = -(⟪Kc R hR hRs u, Complex.I • v⟫_ℂ).re := by
      rw [re_inner_I_right, neg_neg]
    have h2 : (⟪u, Kc R hR hRs v⟫_ℂ).im = -(⟪u, Complex.I • Kc R hR hRs v⟫_ℂ).re := by
      rw [re_inner_I_right, neg_neg]
    rw [h1, h2, ← map_smul (Kc R hR hRs) Complex.I v]
    congr 1
    exact re_inner_Kr R hR hRs u (Complex.I • v)

include hR hRs in
/-- Auxiliary lemma `norm_Sinv` for the fermionic Shale theorem. -/
lemma norm_Sinv (w : Z) : ‖Sinv R hR hRs w‖ = ‖w‖ := by
  have := norm_R R hR (Sinv R hR hRs w)
  rw [R_Sinv R hR hRs] at this
  exact this.symm

include hR hRs in
/-- Auxiliary lemma `norm_Kr_le` for the fermionic Shale theorem. -/
lemma norm_Kr_le (v : Z) : ‖Kr R hR hRs v‖ ≤ ‖v‖ := by
  have hX : ‖Xr R hR hRs v‖ = ‖v‖ := by
    simp only [Xr, LinearMap.comp_apply, Jr_apply, norm_Sinv R hR hRs, norm_R R hR, norm_smul, Complex.norm_I, one_mul]
  have hY : ‖Yr R hR hRs v‖ = ‖v‖ := by
    simp only [Yr, LinearMap.comp_apply, Jr_apply, norm_Sinv R hR hRs, norm_R R hR, norm_smul, Complex.norm_I, one_mul]
  rw [Kr_apply]
  calc ‖(1 / 2 : ℝ) • v + (1 / 4 : ℝ) • (Xr R hR hRs v + Yr R hR hRs v)‖
      ≤ ‖(1 / 2 : ℝ) • v‖ + ‖(1 / 4 : ℝ) • (Xr R hR hRs v + Yr R hR hRs v)‖ := norm_add_le _ _
    _ ≤ (1 / 2) * ‖v‖ + (1 / 4) * (‖Xr R hR hRs v‖ + ‖Yr R hR hRs v‖) := by
        rw [norm_smul, norm_smul]
        simp only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
          abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        gcongr
        exact norm_add_le _ _
    _ = ‖v‖ := by rw [hX, hY]; ring

include hR hRs in
/-- `K` as a bounded complex-linear operator. -/
noncomputable def KL : Z →L[ℂ] Z :=
  LinearMap.mkContinuous (Kc R hR hRs) 1 (fun v => by rw [one_mul]; exact norm_Kr_le R hR hRs v)

include hR hRs in
/-- Auxiliary lemma `KL_apply` for the fermionic Shale theorem. -/
lemma KL_apply (v : Z) : KL R hR hRs v = Kr R hR hRs v := rfl

/-- The linear part `α v = (R v - i R (i v))/2`. -/
noncomputable def alphaPart (v : Z) : Z := (1 / 2 : ℂ) • (R v - Complex.I • R (Complex.I • v))

omit [CompleteSpace Z] in
/-- Auxiliary lemma `betaPart_I` for the fermionic Shale theorem. -/
lemma betaPart_I (v : Z) : betaPart R (Complex.I • v) = -(Complex.I • betaPart R v) := by
  simp only [betaPart, smul_smul, Complex.I_mul_I, neg_smul, one_smul, map_neg, smul_add, smul_neg]
  linear_combination (norm := (match_scalars <;> (ring_nf; try simp only [Complex.I_sq]; try ring)))

omit [CompleteSpace Z] in
/-- Auxiliary lemma `alphaPart_I` for the fermionic Shale theorem. -/
lemma alphaPart_I (v : Z) : alphaPart R (Complex.I • v) = Complex.I • alphaPart R v := by
  simp only [alphaPart, smul_smul, Complex.I_mul_I, neg_smul, one_smul, map_neg, smul_sub, smul_neg]
  linear_combination (norm := (match_scalars <;> (ring_nf; try simp only [Complex.I_sq]; try ring)))

include hR hRs in
/-- `Re⟪β u, β v⟫ = Re⟪u, K v⟫`. -/
lemma re_inner_beta_beta (u v : Z) : (⟪betaPart R u, betaPart R v⟫_ℂ).re = (⟪u, Kr R hR hRs v⟫_ℂ).re := by
  have c2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have key : ⟪betaPart R u, betaPart R v⟫_ℂ = (1 / 4 : ℂ) * (⟪R u, R v⟫_ℂ + ⟪R u, Complex.I • R (Complex.I • v)⟫_ℂ +
      ⟪Complex.I • R (Complex.I • u), R v⟫_ℂ + ⟪Complex.I • R (Complex.I • u), Complex.I • R (Complex.I • v)⟫_ℂ) := by
    simp only [betaPart, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, c2]
    ring
  have e1 : (⟪R u, Complex.I • R (Complex.I • v)⟫_ℂ).re = (⟪u, Xr R hR hRs v⟫_ℂ).re := by
    rw [re_inner_R_left R hR hRs]; rfl
  have e2 : (⟪Complex.I • R (Complex.I • u), R v⟫_ℂ).re = (⟪u, Yr R hR hRs v⟫_ℂ).re := by
    rw [re_inner_I_swap, re_inner_R_left R hR hRs, re_inner_I_swap]
    simp only [Yr, LinearMap.comp_apply, Jr_apply, neg_neg]
  have e3 : (⟪Complex.I • R (Complex.I • u), Complex.I • R (Complex.I • v)⟫_ℂ).re = (⟪u, v⟫_ℂ).re := by
    rw [re_inner_I_I, hR, re_inner_I_I]
  have rhs : (⟪u, Kr R hR hRs v⟫_ℂ).re = (1 / 2) * (⟪u, v⟫_ℂ).re +
      (1 / 4) * ((⟪u, Xr R hR hRs v⟫_ℂ).re + (⟪u, Yr R hR hRs v⟫_ℂ).re) := by
    rw [Kr_apply_c, inner_add_right, inner_smul_right, inner_smul_right, inner_add_right]
    simp only [Complex.mul_re, Complex.add_re, Complex.div_re, Complex.one_re, Complex.one_im]
    norm_num
  have lhs : (⟪betaPart R u, betaPart R v⟫_ℂ).re = (1 / 4) * ((⟪R u, R v⟫_ℂ).re + (⟪R u, Complex.I • R (Complex.I • v)⟫_ℂ).re +
      (⟪Complex.I • R (Complex.I • u), R v⟫_ℂ).re + (⟪Complex.I • R (Complex.I • u), Complex.I • R (Complex.I • v)⟫_ℂ).re) := by
    rw [key]
    simp only [Complex.mul_re, Complex.add_re, Complex.div_re, Complex.one_re, Complex.one_im]
    norm_num
  rw [lhs, rhs, hR, e1, e2, e3]
  ring

include hR hRs in
/-- **`⟪β u, β v⟫ = ⟪K v, u⟫`**. -/
lemma inner_beta_beta (u v : Z) : ⟪betaPart R u, betaPart R v⟫_ℂ = ⟪KL R hR hRs v, u⟫_ℂ := by
  apply Complex.ext
  · rw [re_inner_beta_beta R hR hRs, KL_apply, ← inner_conj_symm (𝕜 := ℂ) u, Complex.conj_re]
  · have h1 : (⟪betaPart R u, betaPart R v⟫_ℂ).im = -(⟪betaPart R u, Complex.I • betaPart R v⟫_ℂ).re := by
      rw [re_inner_I_right, neg_neg]
    have h2 : Complex.I • betaPart R v = -betaPart R (Complex.I • v) := by rw [betaPart_I, neg_neg]
    rw [h1, h2, inner_neg_right, Complex.neg_re, neg_neg, re_inner_beta_beta R hR hRs, ← KL_apply R hR hRs]
    rw [map_smul, re_inner_I_right, ← inner_conj_symm (KL R hR hRs v) u, Complex.conj_im]

include hR hRs in
/-- `Re⟪α u, β v⟫ = (Re⟪u, X v⟫ - Re⟪u, Y v⟫)/4`. -/
lemma re_inner_alpha_beta (u v : Z) : (⟪alphaPart R u, betaPart R v⟫_ℂ).re =
    (1 / 4) * ((⟪u, Xr R hR hRs v⟫_ℂ).re - (⟪u, Yr R hR hRs v⟫_ℂ).re) := by
  have c2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have key : ⟪alphaPart R u, betaPart R v⟫_ℂ = (1 / 4 : ℂ) * (⟪R u, R v⟫_ℂ + ⟪R u, Complex.I • R (Complex.I • v)⟫_ℂ -
      ⟪Complex.I • R (Complex.I • u), R v⟫_ℂ - ⟪Complex.I • R (Complex.I • u), Complex.I • R (Complex.I • v)⟫_ℂ) := by
    simp only [alphaPart, betaPart, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, inner_sub_left,
      c2]
    ring
  have e1 : (⟪R u, Complex.I • R (Complex.I • v)⟫_ℂ).re = (⟪u, Xr R hR hRs v⟫_ℂ).re := by
    rw [re_inner_R_left R hR hRs]; rfl
  have e2 : (⟪Complex.I • R (Complex.I • u), R v⟫_ℂ).re = (⟪u, Yr R hR hRs v⟫_ℂ).re := by
    rw [re_inner_I_swap, re_inner_R_left R hR hRs, re_inner_I_swap]
    simp only [Yr, LinearMap.comp_apply, Jr_apply, neg_neg]
  have e3 : (⟪Complex.I • R (Complex.I • u), Complex.I • R (Complex.I • v)⟫_ℂ).re = (⟪u, v⟫_ℂ).re := by
    rw [re_inner_I_I, hR, re_inner_I_I]
  have lhs : (⟪alphaPart R u, betaPart R v⟫_ℂ).re = (1 / 4) * ((⟪R u, R v⟫_ℂ).re +
      (⟪R u, Complex.I • R (Complex.I • v)⟫_ℂ).re - (⟪Complex.I • R (Complex.I • u), R v⟫_ℂ).re -
      (⟪Complex.I • R (Complex.I • u), Complex.I • R (Complex.I • v)⟫_ℂ).re) := by
    rw [key]
    simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.div_re, Complex.one_re, Complex.one_im]
    norm_num
  rw [lhs, hR, e1, e2, e3]
  ring

include hR hRs in
/-- `K` commutes with `X - Y`. -/
lemma Kr_Ar (w : Z) : Kr R hR hRs (Xr R hR hRs w - Yr R hR hRs w) =
    Xr R hR hRs (Kr R hR hRs w) - Yr R hR hRs (Kr R hR hRs w) := by
  have hXY := Xr_Yr R hR hRs
  have hYX := Yr_Xr R hR hRs
  simp only [Kr_apply, map_sub, map_add, map_smul, hXY, hYX]

include hR hRs in
/-- A real-level orthogonality: `Re⟪u, (X - Y) w⟫ = 0` for `K`-eigenvectors `u`, `w` with different eigenvalues. -/
lemma re_inner_Ar_eq_zero {u w : Z} {l m : ℝ} (hu : Kr R hR hRs u = l • u) (hw : Kr R hR hRs w = m • w)
    (hlm : l ≠ m) : (⟪u, Xr R hR hRs w - Yr R hR hRs w⟫_ℂ).re = 0 := by
  have h1 := re_inner_Kr R hR hRs u (Xr R hR hRs w - Yr R hR hRs w)
  rw [Kr_Ar R hR hRs, hu] at h1
  have h2 : Xr R hR hRs (Kr R hR hRs w) - Yr R hR hRs (Kr R hR hRs w) = m • (Xr R hR hRs w - Yr R hR hRs w) := by
    rw [hw]; simp [smul_sub]
  rw [h2] at h1
  have h3 : ∀ (r : ℝ) (a b : Z), (⟪r • a, b⟫_ℂ).re = r * (⟪a, b⟫_ℂ).re := fun r a b => by
    rw [← Complex.coe_smul, inner_smul_left]; simp
  have h4 : ∀ (r : ℝ) (a b : Z), (⟪a, r • b⟫_ℂ).re = r * (⟪a, b⟫_ℂ).re := fun r a b => by
    rw [← Complex.coe_smul, inner_smul_right]; simp
  rw [h3, h4] at h1
  have : (l - m) * (⟪u, Xr R hR hRs w - Yr R hR hRs w⟫_ℂ).re = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hlm)

include hR hRs in
/-- **Orthogonality of `α u` and `β v` for `K`-eigenvectors with different eigenvalues.** -/
theorem inner_alpha_beta_eq_zero {u v : Z} {l m : ℝ} (hu : KL R hR hRs u = (l : ℂ) • u)
    (hv : KL R hR hRs v = (m : ℂ) • v) (hlm : l ≠ m) : ⟪alphaPart R u, betaPart R v⟫_ℂ = 0 := by
  have hu' : Kr R hR hRs u = l • u := by rw [← KL_apply R hR hRs, hu, Complex.coe_smul]
  have hv' : Kr R hR hRs v = m • v := by rw [← KL_apply R hR hRs, hv, Complex.coe_smul]
  have hIv : Kr R hR hRs (Complex.I • v) = m • (Complex.I • v) := by
    rw [Kr_I R hR hRs, hv', smul_comm]
  have key : ∀ w, (⟪alphaPart R u, betaPart R w⟫_ℂ).re = (1 / 4) * (⟪u, Xr R hR hRs w - Yr R hR hRs w⟫_ℂ).re := fun w => by
    rw [re_inner_alpha_beta R hR hRs, inner_sub_right, Complex.sub_re]
  apply Complex.ext
  · rw [key, re_inner_Ar_eq_zero R hR hRs hu' hv' hlm]; simp
  · have h1 : (⟪alphaPart R u, betaPart R v⟫_ℂ).im = -(⟪alphaPart R u, Complex.I • betaPart R v⟫_ℂ).re := by
      rw [re_inner_I_right, neg_neg]
    have h2 : Complex.I • betaPart R v = -betaPart R (Complex.I • v) := by rw [betaPart_I, neg_neg]
    rw [h1, h2, inner_neg_right, Complex.neg_re, neg_neg, key, re_inner_Ar_eq_zero R hR hRs hu' hIv hlm]
    simp

end Lightlike.OperatorAlgebras.CARShale
