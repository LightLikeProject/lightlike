import Lightlike.Asymptotics.EPRL.Amplitude
import Lightlike.Spin4.CoherentTwoValent

/-!
# Gluing and stationarity of the coherent 15j integrand

For SU(2) boundary data, the integrand `F_n(X) = Π_e P_e(X)^{n_e}` of the coherent 15j integral
has modulus at most `1`, and its critical points are characterised by two geometric conditions,
gluing and closure (Barrett, Dowdall, Fairbairn, Gomes, Hellmann, J. Math. Phys. 50 (2009)
112504, arXiv:0902.1170, section 4; BDFGH below).

* `frameSrc` and `frameTgt` are the frames `X_a g_ab ε` and `X_b g_ba` of an edge `e = ab`, and
  `P_e` is the overlap of their first columns (`prop_eq_frame`).
* `|P_e| ≤ 1`, with equality exactly when the two frames have the same Bloch vector
  (`norm_prop_le`, `norm_prop_eq_one_iff`). Hence `|F_n| ≤ 1`, with equality exactly when every
  edge with a nonzero spin is glued (`norm_cohAmp_le`, `norm_cohAmp_eq_one_iff`): the points
  where the real part of the action is maximal (BDFGH, eq. (37)).
* `θ ↦ F_n(chart X θ)` is smooth (`contDiff_cohAmp_chart`). At a gluing point its partial
  derivative along `θ_{a,k}` is `F_n(X) (i/2) (Σ_e n_e ν_e)_k`, with `ν_e` the normal of the
  boundary data at the end `a` of `e` (`coordDeriv_cohAmp_chart_of_glued`). So the integrand is
  stationary there exactly when the boundary data close at the nodes `0, …, 3`
  (`stationary_iff_closure_free`). Closure there implies closure at the gauge-fixed node `4`
  (`closure_last_of_glued`): rotated by `X_a`, the five closure vectors add up to zero, because
  the two rotated normals of a glued edge are opposite. Hence stationarity at a gluing point is
  closure at every node (`stationary_iff_closure`).
* Trust checks: data glued at `X = 1` by construction give `F_n = 1` there
  (`cohAmp_twistData_one`), and the same data without the twist `ε` give `F_n = 0`
  (`cohAmp_untwisted_one`). A glued point that does not close is not stationary
  (`twistData_one_not_stationary`), and a closed triangle is (`triangle_stationary`).
-/

open Matrix Complex Finset

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4

/-- The matrix `ε` as an element of SU(2). -/
noncomputable def epsSU2 : SU2 :=
  ⟨epsMat, by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose]
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [epsMat, mul_apply, Fin.sum_univ_two]
    · simp [epsMat, det_fin_two_of]⟩

/-- Boundary data with every matrix in SU(2). -/
def IsSU2Data (g : BdryData) : Prop := ∀ e i, g e i ∈ specialUnitaryGroup (Fin 2) ℂ

/-- The frame `X_a g_ab ε` at the source of the edge `e = ab`: the first column is the spinor that
the propagator pairs at the node `a`. -/
noncomputable def frameSrc {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10) : SU2 :=
  X (edgeSrc e) * ⟨g e 0, hg e 0⟩ * epsSU2

/-- The frame `X_b g_ba` at the target of the edge `e = ab`. -/
noncomputable def frameTgt {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10) : SU2 :=
  X (edgeTgt e) * ⟨g e 1, hg e 1⟩

/-- The propagator is the overlap of the first columns of the two frames. -/
theorem prop_eq_frame {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10) :
    prop g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)) e =
      (((frameSrc hg X e : SU2) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (frameTgt hg X e : SU2)) 0 0 := by
  simp only [prop, frameSrc, frameTgt, epsSU2, Submonoid.coe_mul, conjTranspose_mul,
    Matrix.mul_assoc]

/-- **The propagator in terms of the normals**: `|P_e|² = (1 + ν(X_a g_ab ε) · ν(X_b g_ba))/2`. -/
theorem normSq_prop {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10) :
    Complex.normSq (prop g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)) e) =
      (1 + bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) ⬝ᵥ
        bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) / 2 := by
  rw [prop_eq_frame, normSq_overlap]

/-- **`|P_e| ≤ 1`** on SU(2) boundary data. -/
theorem norm_prop_le {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10) :
    ‖prop g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)) e‖ ≤ 1 := by
  have h := normSq_prop hg X e
  have hb := (bloch_dot_bounds (frameSrc hg X e) (frameTgt hg X e)).2
  rw [← sq_le_one_iff₀ (norm_nonneg _), ← Complex.normSq_eq_norm_sq, h]
  linarith

/-- **The gluing condition** (BDFGH, eq. (37)): `|P_e| = 1` if and only if the normals of the two
frames agree, `ν(X_a g_ab ε) = ν(X_b g_ba)`. -/
theorem norm_prop_eq_one_iff {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10) :
    ‖prop g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)) e‖ = 1 ↔
      bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
        bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h := normSq_prop hg X e
  set u := bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ)
  set v := bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)
  have hu : u ⬝ᵥ u = 1 := bloch_dot_self _
  have hv : v ⬝ᵥ v = 1 := bloch_dot_self _
  have key : (u - v) ⬝ᵥ (u - v) = 2 - 2 * (u ⬝ᵥ v) := by
    simp only [sub_dotProduct, dotProduct_sub, hu, hv, dotProduct_comm v u]
    ring
  constructor
  · intro h1
    have h2 : Complex.normSq (prop g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)) e) = 1 := by
      rw [Complex.normSq_eq_norm_sq, h1, one_pow]
    rw [h] at h2
    have h3 : (u - v) ⬝ᵥ (u - v) = 0 := by rw [key]; linarith
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h3)
  · intro huv
    have h2 : Complex.normSq (prop g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)) e) = 1 := by
      rw [h, ← huv, hu]; norm_num
    rw [Complex.normSq_eq_norm_sq] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

/-- **`|F_n| ≤ 1`** on SU(2) boundary data. -/
theorem norm_cohAmp_le (n : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) :
    ‖cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ ≤ 1 := by
  rw [cohAmp, norm_prod]
  exact prod_le_one₀ (fun _ _ => norm_nonneg _) fun e _ => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_prop_le hg X e)

/-- **`|F_n| = 1` exactly at the gluing solutions**: every edge with a nonzero spin satisfies the
gluing condition. -/
theorem norm_cohAmp_eq_one_iff (n : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g)
    (X : Fin 5 → SU2) :
    ‖cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 ↔
      ∀ e, n e ≠ 0 → bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
        bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp_rw [← norm_prop_eq_one_iff hg X]
  set p := fun e => ‖prop g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)) e‖
  have hp0 : ∀ e, 0 ≤ p e := fun e => norm_nonneg _
  have hp1 : ∀ e, p e ≤ 1 := fun e => norm_prop_le hg X e
  rw [cohAmp, norm_prod]
  simp only [norm_pow]
  change ∏ e, p e ^ n e = 1 ↔ ∀ e, n e ≠ 0 → p e = 1
  constructor
  · intro h e he
    by_contra hne
    have hlt : p e ^ n e < 1 := pow_lt_one₀ (hp0 e) (lt_of_le_of_ne (hp1 e) hne) he
    have hrest : ∏ e' ∈ univ.erase e, p e' ^ n e' ≤ 1 :=
      prod_le_one₀ (fun _ _ => pow_nonneg (hp0 _) _) fun _ _ => pow_le_one₀ (hp0 _) (hp1 _)
    rw [← mul_prod_erase univ _ (mem_univ e)] at h
    nlinarith [prod_nonneg fun e' (_ : e' ∈ univ.erase e) => pow_nonneg (hp0 e') (n e'),
      pow_nonneg (hp0 e) (n e)]
  · intro h
    refine prod_eq_one fun e _ => ?_
    by_cases he : n e = 0
    · rw [he, pow_zero]
    · rw [h e he, one_pow]

/-! ## Stationarity in the chart -/

section Stationarity

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open scoped ContDiff

/-- The Pauli matrices `σ₀ = [[0, 1], [1, 0]]`, `σ₁ = [[0, -i], [i, 0]]`, `σ₂ = [[1, 0], [0, -1]]`. -/
noncomputable def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -I; I, 0], !![1, 0; 0, -1]]

/-- The basis `(i/2) σ_k` of `su(2)` used by the chart. -/
noncomputable def su2Basis (k : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (I / 2) • pauli k

/-- `su2Gen θ = Σ_k θ_k (i/2) σ_k`. -/
lemma su2Gen_eq_sum (θ : Fin 3 → ℝ) : su2Gen θ = ∑ k, θ k • su2Basis k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Gen, su2Basis, pauli, Fin.sum_univ_three, Matrix.sum_apply] <;> ring

/-- On a coordinate vector, `su2Gen (t e_k) = t (i/2) σ_k`. -/
lemma su2Gen_single (k : Fin 3) (t : ℝ) : su2Gen (Pi.single k t) = t • su2Basis k := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [su2Gen, su2Basis, pauli] <;> ring

/-- `su2Gen 0 = 0`. -/
lemma su2Gen_zero : su2Gen 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [su2Gen]

/-- The basis of `su(2)` is anti-Hermitian. -/
lemma conjTranspose_su2Basis (k : Fin 3) : (su2Basis k)ᴴ = -su2Basis k := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [su2Basis, pauli, Complex.ext_iff] <;> norm_num

/-- **The normal as an expectation value**: `(gᴴ σ_k g)₀₀ = ν(g)_k`. -/
lemma conjTranspose_pauli_mul_apply (g : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 3) :
    (gᴴ * pauli k * g) 0 0 = (bloch g k : ℂ) := by
  fin_cases k <;> apply Complex.ext <;>
    simp [pauli, bloch, mul_apply, Fin.sum_univ_two, Complex.normSq_apply] <;> ring

/-- `ν(g ε) = −ν(g)` for `g ∈ SU(2)`. -/
lemma bloch_mul_epsMat {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ) :
    bloch (g * epsMat) = -bloch g := by
  have h11 : g 1 1 = star (g 0 0) := (Lightlike.SU2.su2_entries ⟨g, hg⟩).1
  have h01 : g 0 1 = -star (g 1 0) := (Lightlike.SU2.su2_entries ⟨g, hg⟩).2.1
  have e0 : (g * epsMat) 0 0 = -star (g 1 0) := by
    simp [epsMat, mul_apply, Fin.sum_univ_two, h01]
  have e1 : (g * epsMat) 1 0 = star (g 0 0) := by
    simp [epsMat, mul_apply, Fin.sum_univ_two, h11]
  ext k
  fin_cases k <;>
    simp [bloch, e0, e1, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

/-- The coordinate direction `θ_{a,k}` of the chart: the generator `(i/2) σ_k` at the node `a`. -/
def chartDir (a : Fin 4) (k : Fin 3) : Fin 12 → ℝ := Pi.single (finProdFinEquiv (a, k)) 1

/-- Along the direction `θ_{a,k}` the chart moves only the node `a`, by
`X_a ↦ X_a exp(t (i/2) σ_k)`. -/
lemma chart_smul_chartDir (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 4) (k : Fin 3) (t : ℝ)
    (b : Fin 5) :
    chart X (t • chartDir a k) b =
      if b = a.castSucc then X b * NormedSpace.exp (t • su2Basis k) else X b := by
  unfold chart
  by_cases hb : (b : ℕ) < 4
  · have hfun : (fun k' => (t • chartDir a k) (finProdFinEquiv ((⟨b, hb⟩ : Fin 4), k'))) =
        if b = a.castSucc then Pi.single k t else 0 := by
      ext k'
      split_ifs with hba
      · subst hba
        by_cases hk : k' = k
        · subst hk; simp [chartDir]
        · simp [chartDir, hk]
      · have hne : ((⟨b, hb⟩ : Fin 4), k') ≠ (a, k) := by
          intro h
          apply hba
          ext
          simpa using congrArg (fun p => (p.1 : ℕ)) h
        simp [chartDir, hne]
    simp only [hb, dite_true, hfun]
    split_ifs <;> simp [su2Gen_single, su2Gen_zero]
  · have hne : b ≠ a.castSucc := by
      rintro rfl; exact hb (by simp)
    simp [hb, hne]

/-- The edges of `K₅` have distinct ends. -/
lemma edgeSrc_ne_edgeTgt (e : Fin 10) : edgeSrc e ≠ edgeTgt e := by
  revert e; decide

/-! ### Smoothness of the integrand in the chart -/

/-- The conjugate transpose as a real-linear map. -/
noncomputable def conjTransposeRLin : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun M := Mᴴ
  map_add' := conjTranspose_add
  map_smul' c M := by simp [conjTranspose_smul]

/-- Each node of the chart is a smooth function of `θ`. -/
lemma contDiff_chart (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (b : Fin 5) :
    ContDiff ℝ ∞ fun θ : Fin 12 → ℝ => chart X θ b := by
  unfold chart
  by_cases hb : (b : ℕ) < 4
  · simp only [hb, dite_true]
    have hlin : ContDiff ℝ ∞ fun θ : Fin 12 → ℝ =>
        su2Gen fun k => θ (finProdFinEquiv ((⟨b, hb⟩ : Fin 4), k)) := by
      simp only [su2Gen_eq_sum]
      exact ContDiff.sum fun k _ => (contDiff_apply ℝ (fun _ : Fin 12 => ℝ) _).smul contDiff_const
    exact contDiff_const.mul (contDiff_iff_contDiffAt.mpr fun θ =>
      (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt.comp θ hlin.contDiffAt)
  · simp only [hb, dite_false]
    exact contDiff_const

/-- **The integrand is smooth in the chart**: `θ ↦ F_n(chart X θ)` is `C^∞`. -/
theorem contDiff_cohAmp_chart (n : Fin 10 → ℕ) (g : BdryData)
    (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) :
    ContDiff ℝ ∞ fun θ : Fin 12 → ℝ => cohAmp n g (chart X θ) := by
  let E : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
    (Matrix.entryLinearMap ℝ ℂ (0 : Fin 2) (0 : Fin 2)).toContinuousLinearMap
  let C : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    conjTransposeRLin.toContinuousLinearMap
  unfold cohAmp
  refine contDiff_prod fun e _ => ContDiff.pow ?_ _
  exact E.contDiff.comp (((contDiff_const.mul (C.contDiff.comp (contDiff_chart X (edgeSrc e)))).mul
    (contDiff_chart X (edgeTgt e))).mul contDiff_const)

/-- A partial derivative is the derivative along the coordinate line. -/
lemma coordDeriv_eq_of_hasDerivAt {m : ℕ} {f : (Fin m → ℝ) → ℂ} (hf : DifferentiableAt ℝ f 0)
    (l : Fin m) {d : ℂ} (hd : HasDerivAt (fun t : ℝ => f (t • Pi.single l 1)) d 0) :
    Lightlike.Oscillatory.coordDeriv f l 0 = d := by
  have hγ : HasDerivAt (fun t : ℝ => t • (Pi.single l 1 : Fin m → ℝ)) (Pi.single l 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l 1 : Fin m → ℝ)
  have hf' : HasFDerivAt f (fderiv ℝ f 0) ((0 : ℝ) • (Pi.single l 1 : Fin m → ℝ)) := by
    rw [zero_smul]; exact hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (0 : ℝ) hγ).unique hd

/-! ### The derivative of a propagator along a chart direction -/

/-- The derivative at `t = 0` of an entry of `L exp(tG) R`. -/
lemma hasDerivAt_entry_exp (L R G : Matrix (Fin 2) (Fin 2) ℂ) :
    HasDerivAt (fun t : ℝ => (L * NormedSpace.exp (t • G) * R) 0 0) ((L * G * R) 0 0) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) G 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have h2 := (h.const_mul L).mul_const R
  let E : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
    (Matrix.entryLinearMap ℝ ℂ (0 : Fin 2) (0 : Fin 2)).toContinuousLinearMap
  exact E.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2

/-- The derivative of `P_e` along `θ_{a,k}` when the edge `e` starts at `a`. -/
lemma hasDerivAt_prop_src (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 4)
    (k : Fin 3) {e : Fin 10} (hs : edgeSrc e = a.castSucc) :
    HasDerivAt (fun t : ℝ => prop g (chart X (t • chartDir a k)) e)
      (((g e 0 * epsMat)ᴴ * (su2Basis k)ᴴ * ((X (edgeSrc e))ᴴ * X (edgeTgt e) * g e 1)) 0 0) 0 := by
  have ht : edgeTgt e ≠ a.castSucc := hs ▸ (edgeSrc_ne_edgeTgt e).symm
  have hfun : (fun t : ℝ => prop g (chart X (t • chartDir a k)) e) = fun t : ℝ =>
      ((g e 0 * epsMat)ᴴ * NormedSpace.exp (t • (su2Basis k)ᴴ) *
        ((X (edgeSrc e))ᴴ * X (edgeTgt e) * g e 1)) 0 0 := by
    funext t
    simp only [prop, chart_smul_chartDir, hs, ht, ite_true, ite_false, conjTranspose_mul,
      ← Matrix.exp_conjTranspose, conjTranspose_smul, star_trivial, Matrix.mul_assoc]
  rw [hfun]
  exact hasDerivAt_entry_exp _ _ _

/-- The derivative of `P_e` along `θ_{a,k}` when the edge `e` ends at `a`. -/
lemma hasDerivAt_prop_tgt (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 4)
    (k : Fin 3) {e : Fin 10} (ht : edgeTgt e = a.castSucc) :
    HasDerivAt (fun t : ℝ => prop g (chart X (t • chartDir a k)) e)
      (((g e 0 * epsMat)ᴴ * (X (edgeSrc e))ᴴ * X (edgeTgt e) * su2Basis k * g e 1) 0 0) 0 := by
  have hs : edgeSrc e ≠ a.castSucc := ht ▸ edgeSrc_ne_edgeTgt e
  have hfun : (fun t : ℝ => prop g (chart X (t • chartDir a k)) e) = fun t : ℝ =>
      ((g e 0 * epsMat)ᴴ * (X (edgeSrc e))ᴴ * X (edgeTgt e) * NormedSpace.exp (t • su2Basis k) *
        g e 1) 0 0 := by
    funext t
    simp only [prop, chart_smul_chartDir, hs, ht, ite_true, ite_false, Matrix.mul_assoc]
  rw [hfun]
  exact hasDerivAt_entry_exp _ _ _

/-- The propagator of an edge away from the node `a` does not move along `θ_{a,k}`. -/
lemma hasDerivAt_prop_other (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 4)
    (k : Fin 3) {e : Fin 10} (hs : edgeSrc e ≠ a.castSucc) (ht : edgeTgt e ≠ a.castSucc) :
    HasDerivAt (fun t : ℝ => prop g (chart X (t • chartDir a k)) e) 0 0 := by
  have hfun : (fun t : ℝ => prop g (chart X (t • chartDir a k)) e) = fun _ => prop g X e := by
    funext t
    simp only [prop, chart_smul_chartDir, hs, ht, ite_false]
  rw [hfun]
  exact hasDerivAt_const _ _

/-! ### At a gluing point -/

/-- In SU(2), `|M₀₀| = 1` forces `M₁₀ = M₀₁ = 0`. -/
lemma su2_offDiag_eq_zero (M : SU2) (h : ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ = 1) :
    (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 ∧ (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
  obtain ⟨-, h01, hn⟩ := Lightlike.SU2.su2_entries M
  have h00 : Complex.normSq ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h, one_pow]
  have h10 : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [Complex.normSq_nonneg ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0)])
  exact ⟨h10, by rw [h01, h10, star_zero, neg_zero]⟩

/-- `U (Uᴴ Z) = Z` for `U ∈ SU(2)`. -/
lemma mul_conjTranspose_mul_cancel {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ specialUnitaryGroup (Fin 2) ℂ) (Z : Matrix (Fin 2) (Fin 2) ℂ) : U * (Uᴴ * Z) = Z := by
  rw [← Matrix.mul_assoc, ← star_eq_conjTranspose,
    mem_unitaryGroup_iff.mp (specialUnitaryGroup_le_unitaryGroup hU), Matrix.one_mul]

/-- The matrix `M = Aᴴ B` of the two frames of the edge `e`, whose `(0, 0)` entry is `P_e`. -/
lemma coe_frame_overlap {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10) :
    ((star (frameSrc hg X e) * frameTgt hg X e : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g e 0 * epsMat)ᴴ * (((X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
        X (edgeTgt e) * g e 1) := by
  change (((X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ) * g e 0 * epsMat))ᴴ *
      ((X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ) * g e 1) = _
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- The propagator is the `(0, 0)` entry of the frame overlap `Aᴴ B`. -/
lemma prop_eq_overlap {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10) :
    prop g (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) e =
      ((star (frameSrc hg X e) * frameTgt hg X e : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
  rw [coe_frame_overlap, prop]
  simp only [Matrix.mul_assoc]

/-- At a gluing point the frame overlap `M = Aᴴ B` is diagonal. -/
lemma overlap_offDiag_of_glued {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10)
    (hglue : bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) :
    ((star (frameSrc hg X e) * frameTgt hg X e : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 ∧
      ((star (frameSrc hg X e) * frameTgt hg X e : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 :=
  su2_offDiag_eq_zero _ (by rw [← prop_eq_overlap]; exact (norm_prop_eq_one_iff hg X e).mpr hglue)

/-- The derivative at the source node of a glued edge: `P_e (i/2) ν(g_ab)_k`. -/
lemma deriv_src_of_glued {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10)
    (k : Fin 3) (hglue : bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) :
    ((g e 0 * epsMat)ᴴ * (su2Basis k)ᴴ * (((X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
        X (edgeTgt e) * g e 1)) 0 0 =
      I / 2 * (bloch (g e 0) k : ℂ) * prop g (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) e := by
  have hh : (g e 0 * epsMat) ∈ specialUnitaryGroup (Fin 2) ℂ :=
    ((⟨g e 0, hg e 0⟩ : SU2) * epsSU2).2
  have key : (g e 0 * epsMat)ᴴ * (su2Basis k)ᴴ * (((X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
        X (edgeTgt e) * g e 1) =
      ((g e 0 * epsMat)ᴴ * (su2Basis k)ᴴ * (g e 0 * epsMat)) *
        ((star (frameSrc hg X e) * frameTgt hg X e : SU2) : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [coe_frame_overlap, Matrix.mul_assoc _ (g e 0 * epsMat), mul_conjTranspose_mul_cancel hh]
  rw [key, mul_apply, Fin.sum_univ_two, (overlap_offDiag_of_glued hg X e hglue).1, mul_zero,
    add_zero, ← prop_eq_overlap, conjTranspose_su2Basis, su2Basis, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_smul, Matrix.smul_mul, neg_apply, Matrix.smul_apply, conjTranspose_pauli_mul_apply,
    bloch_mul_epsMat (hg e 0), Pi.neg_apply, smul_eq_mul]
  push_cast
  ring

/-- The derivative at the target node of a glued edge: `P_e (i/2) ν(g_ba)_k`. -/
lemma deriv_tgt_of_glued {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10)
    (k : Fin 3) (hglue : bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) :
    ((g e 0 * epsMat)ᴴ * ((X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * X (edgeTgt e) *
        su2Basis k * g e 1) 0 0 =
      I / 2 * (bloch (g e 1) k : ℂ) * prop g (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) e := by
  have key : (g e 0 * epsMat)ᴴ * ((X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * X (edgeTgt e) *
        su2Basis k * g e 1 =
      ((star (frameSrc hg X e) * frameTgt hg X e : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((g e 1)ᴴ * su2Basis k * g e 1) := by
    rw [coe_frame_overlap]
    simp only [Matrix.mul_assoc, mul_conjTranspose_mul_cancel (hg e 1)]
  rw [key, mul_apply, Fin.sum_univ_two, (overlap_offDiag_of_glued hg X e hglue).2, zero_mul,
    add_zero, ← prop_eq_overlap, su2Basis, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
    conjTranspose_pauli_mul_apply, smul_eq_mul]
  ring

/-- The coefficient of the closure condition at the node `a` contributed by the edge `e`:
`ν(g_ab)` if `e = ab` starts at `a`, `ν(g_ba)` if it ends at `a`, and `0` otherwise. -/
noncomputable def nodeNormal (g : BdryData) (a : Fin 5) (e : Fin 10) : Fin 3 → ℝ :=
  if edgeSrc e = a then bloch (g e 0) else if edgeTgt e = a then bloch (g e 1) else 0

/-- The derivative of a glued propagator along `θ_{a,k}`: `P_e (i/2) ν_k`, with `ν` the normal of
the boundary data at the end `a` of `e`, independently of `X`. -/
lemma hasDerivAt_prop_of_glued {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (a : Fin 4)
    (k : Fin 3) (e : Fin 10) (hglue : bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) :
    HasDerivAt
      (fun t : ℝ => prop g (chart (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) (t • chartDir a k)) e)
      (I / 2 * (nodeNormal g a.castSucc e k : ℂ) *
        prop g (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) e) 0 := by
  by_cases hs : edgeSrc e = a.castSucc
  · refine (hasDerivAt_prop_src g _ a k hs).congr_deriv ?_
    rw [deriv_src_of_glued hg X e k hglue]
    simp [nodeNormal, hs]
  · by_cases ht : edgeTgt e = a.castSucc
    · refine (hasDerivAt_prop_tgt g _ a k ht).congr_deriv ?_
      rw [deriv_tgt_of_glued hg X e k hglue]
      simp [nodeNormal, hs, ht]
    · refine (hasDerivAt_prop_other g _ a k hs ht).congr_deriv ?_
      simp [nodeNormal, hs, ht]

/-! ### Stationarity is closure -/

/-- **The derivative of `F_n` along a chart direction at a gluing point**: if every edge with a
nonzero spin satisfies the gluing condition, the derivative of `t ↦ F_n(chart X (t θ_{a,k}))` at
`0` is `F_n(X) (i/2) (Σ_e n_e ν_e)_k`, with `ν_e` the normal of the boundary data at the end `a`
of `e`. -/
theorem hasDerivAt_cohAmp_line_of_glued (n : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g)
    (X : Fin 5 → SU2)
    (hglue : ∀ e, n e ≠ 0 → bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) (a : Fin 4) (k : Fin 3) :
    HasDerivAt
      (fun t : ℝ => cohAmp n g (chart (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) (t • chartDir a k)))
      (cohAmp n g (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) *
        (I / 2 * ((∑ e, (n e : ℝ) • nodeNormal g a.castSucc e) k : ℂ))) 0 := by
  set X' : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ := fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)
  have hc : chart X' ((0 : ℝ) • chartDir a k) = X' := funext fun b => by
    rw [chart_smul_chartDir, zero_smul, NormedSpace.exp_zero, Matrix.mul_one, ite_self]
  have hp0 : ∀ e, prop g (chart X' ((0 : ℝ) • chartDir a k)) e = prop g X' e := fun e => by
    rw [hc]
  have hd : ∀ e ∈ (univ : Finset (Fin 10)), HasDerivAt
      (fun t : ℝ => prop g (chart X' (t • chartDir a k)) e ^ n e)
      ((n e : ℂ) * (I / 2 * (nodeNormal g a.castSucc e k : ℂ)) * prop g X' e ^ n e) 0 := by
    intro e _
    by_cases hne : n e = 0
    · simp only [hne, pow_zero, Nat.cast_zero, zero_mul]
      exact hasDerivAt_const _ _
    · refine ((hasDerivAt_prop_of_glued hg X a k e (hglue e hne)).pow (n e)).congr_deriv ?_
      rw [hp0]
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
      rw [hm, Nat.succ_sub_one, pow_succ]
      push_cast
      ring
  refine (HasDerivAt.fun_finsetProd hd).congr_deriv ?_
  simp only [hp0, smul_eq_mul]
  have hF : ∀ e, (∏ j ∈ univ.erase e, prop g X' j ^ n j) *
      ((n e : ℂ) * (I / 2 * (nodeNormal g a.castSucc e k : ℂ)) * prop g X' e ^ n e) =
      cohAmp n g X' * ((n e : ℂ) * (I / 2 * (nodeNormal g a.castSucc e k : ℂ))) := by
    intro e
    rw [cohAmp, ← mul_prod_erase univ (fun j => prop g X' j ^ n j) (mem_univ e)]
    ring
  rw [Finset.sum_congr rfl fun e _ => hF e, ← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_natCast, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- The partial derivatives of `θ ↦ F_n(chart X θ)` at a gluing point. -/
theorem coordDeriv_cohAmp_chart_of_glued (n : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g)
    (X : Fin 5 → SU2)
    (hglue : ∀ e, n e ≠ 0 → bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) (a : Fin 4) (k : Fin 3) :
    Lightlike.Oscillatory.coordDeriv
        (fun θ => cohAmp n g (chart (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) θ))
        (finProdFinEquiv (a, k)) 0 =
      cohAmp n g (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) *
        (I / 2 * ((∑ e, (n e : ℝ) • nodeNormal g a.castSucc e) k : ℂ)) :=
  coordDeriv_eq_of_hasDerivAt ((contDiff_cohAmp_chart n g _).differentiable (by simp) 0) _
    (hasDerivAt_cohAmp_line_of_glued n hg X hglue a k)

/-- **Stationarity at a gluing point, free nodes**: at a point where every edge with a nonzero
spin is glued, all twelve partial derivatives of `θ ↦ F_n(chart X θ)` vanish at `θ = 0` if and
only if the boundary data close at the nodes `0, …, 3`, whose group elements the chart moves:
`Σ_e n_e ν_e = 0`, with `ν_e` the normal of the boundary data at the end `a` of `e`. -/
theorem stationary_iff_closure_free (n : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g)
    (X : Fin 5 → SU2)
    (hglue : ∀ e, n e ≠ 0 → bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) :
    (∀ l : Fin 12, Lightlike.Oscillatory.coordDeriv
        (fun θ => cohAmp n g (chart (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) θ)) l 0 = 0) ↔
      ∀ a : Fin 4, ∑ e, (n e : ℝ) • nodeNormal g a.castSucc e = 0 := by
  have hF : cohAmp n g (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0 := by
    intro h0
    have h1 := (norm_cohAmp_eq_one_iff n hg X).mpr hglue
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hI : (I / 2 : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  constructor
  · intro h a
    funext k
    have h1 := h (finProdFinEquiv (a, k))
    rw [coordDeriv_cohAmp_chart_of_glued n hg X hglue a k] at h1
    have h2 := ((mul_eq_zero.mp h1).resolve_left hF)
    have h3 := (mul_eq_zero.mp h2).resolve_left hI
    exact_mod_cast h3
  · intro h l
    obtain ⟨⟨a, k⟩, rfl⟩ := (finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12).surjective l
    rw [coordDeriv_cohAmp_chart_of_glued n hg X hglue a k, h a]
    simp

end Stationarity

/-- The Bloch vector of the source frame: `ν(X_a g_ab ε) = −ν(X_a g_ab)`. -/
lemma bloch_frameSrc {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (e : Fin 10) :
    bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      -bloch ((X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ) * g e 0) := by
  have h := bloch_mul_epsMat (X (edgeSrc e) * ⟨g e 0, hg e 0⟩).2
  simp only [Submonoid.coe_mul] at h
  simp only [frameSrc, epsSU2, Submonoid.coe_mul]
  exact h

/-! ## Closure at the gauge-fixed node -/

/-- Left multiplication by `X ∈ SU(2)` preserves the dot products of Bloch vectors:
`ν(X g) · ν(X h) = ν(g) · ν(h)`. -/
lemma bloch_mul_dot (X g h : SU2) :
    bloch ((X * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) ⬝ᵥ
        bloch ((X * h : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (g : Matrix (Fin 2) (Fin 2) ℂ) ⬝ᵥ bloch (h : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 := normSq_overlap (X * g) (X * h)
  have h2 := normSq_overlap g h
  have hu : ((X : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * X = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup X.2)
  have hc : ((X * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * ((X * h : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
      = (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * h := by
    simp only [Submonoid.coe_mul, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ, hu, Matrix.one_mul]
  rw [hc, h2] at h1
  linarith

/-- Left multiplication by `X ∈ SU(2)` preserves the length of every real combination of Bloch
vectors. -/
lemma bloch_mul_sum_dot {ι : Type*} (s : Finset ι) (c : ι → ℝ) (X : SU2) (u : ι → SU2) :
    (∑ i ∈ s, c i • bloch ((X * u i : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) ⬝ᵥ
        (∑ i ∈ s, c i • bloch ((X * u i : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) =
      (∑ i ∈ s, c i • bloch (u i : Matrix (Fin 2) (Fin 2) ℂ)) ⬝ᵥ
        (∑ i ∈ s, c i • bloch (u i : Matrix (Fin 2) (Fin 2) ℂ)) := by
  simp only [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, bloch_mul_dot]

/-- The boundary element that the edge `e` carries at the node `a`: `g_e0` at its source,
`g_e1` otherwise. -/
noncomputable def nodeElt {g : BdryData} (hg : IsSU2Data g) (a : Fin 5) (e : Fin 10) : SU2 :=
  if edgeSrc e = a then ⟨g e 0, hg e 0⟩ else ⟨g e 1, hg e 1⟩

/-- The incidence of the node `a` and the edge `e`: `1` if `a` is an end of `e`, else `0`. -/
noncomputable def incid (a : Fin 5) (e : Fin 10) : ℝ :=
  if edgeSrc e = a ∨ edgeTgt e = a then 1 else 0

/-- The closure coefficient `ν_e` at the node `a` is the incidence times the Bloch vector of
the element that `e` carries there. -/
lemma nodeNormal_eq_incid {g : BdryData} (hg : IsSU2Data g) (a : Fin 5) (e : Fin 10) :
    nodeNormal g a e = incid a e • bloch (nodeElt hg a e : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold nodeNormal incid nodeElt
  by_cases hs : edgeSrc e = a
  · simp [hs]
  · by_cases ht : edgeTgt e = a <;> simp [hs, ht]

/-- **Closure at the gauge-fixed node.** On a gluing solution, closure at the nodes `0, …, 3`
implies closure at the node `4`: the closure vectors rotated by `X_a` add up to zero over the five
nodes, because the two rotated normals of a glued edge are opposite, and the rotation keeps the
length of each closure vector. -/
theorem closure_last_of_glued (n : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g)
    (X : Fin 5 → SU2)
    (hglue : ∀ e, n e ≠ 0 → bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ))
    (hcl : ∀ a : Fin 4, ∑ e, (n e : ℝ) • nodeNormal g a.castSucc e = 0) :
    ∑ e, (n e : ℝ) • nodeNormal g (Fin.last 4) e = 0 := by
  set w : Fin 5 → Fin 3 → ℝ := fun a =>
    ∑ e, ((n e : ℝ) * incid a e) • bloch ((X a * nodeElt hg a e : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
    with hw_def
  have hC : ∀ a, (∑ e, (n e : ℝ) • nodeNormal g a e) =
      ∑ e, ((n e : ℝ) * incid a e) • bloch (nodeElt hg a e : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro a
    simp_rw [nodeNormal_eq_incid hg, smul_smul]
  have hnorm : ∀ a, w a ⬝ᵥ w a =
      (∑ e, (n e : ℝ) • nodeNormal g a e) ⬝ᵥ (∑ e, (n e : ℝ) • nodeNormal g a e) := by
    intro a
    rw [hC]
    exact bloch_mul_sum_dot _ _ _ _
  have hsum : ∑ a, w a = 0 := by
    simp only [hw_def]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun e _ => ?_
    have hne := edgeSrc_ne_edgeTgt e
    rw [Finset.sum_eq_add (edgeSrc e) (edgeTgt e) hne
      (fun a _ ha => by simp [incid, Ne.symm ha.1, Ne.symm ha.2])
      (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
    by_cases hn : n e = 0
    · simp [hn]
    have hg' := hglue e hn
    rw [bloch_frameSrc] at hg'
    simp only [incid, nodeElt, true_or, or_true, ite_true, hne, ite_false, mul_one,
      Submonoid.coe_mul]
    rw [← smul_add]
    have : bloch ((X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ) * g e 1) =
        bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [frameTgt, Submonoid.coe_mul]
    rw [this, ← hg', add_neg_cancel, smul_zero]
  have hw0 : ∀ a : Fin 4, w a.castSucc = 0 := fun a => by
    have h := hnorm a.castSucc
    rw [hcl a, dotProduct_zero] at h
    exact dotProduct_self_eq_zero.mp h
  rw [Fin.sum_univ_castSucc] at hsum
  simp only [hw0, Finset.sum_const_zero, zero_add] at hsum
  have h := hnorm (Fin.last 4)
  rw [hsum, dotProduct_zero] at h
  exact dotProduct_self_eq_zero.mp h.symm

/-- **Stationarity at a gluing point is closure** (BDFGH, section 4): at a point where every edge
with a nonzero spin is glued, all twelve partial derivatives of `θ ↦ F_n(chart X θ)` vanish at
`θ = 0` if and only if the boundary data close at every node: `Σ_e n_e ν_e = 0` at each of the
five nodes, with `ν_e` the normal of the boundary data at the end of `e`. -/
theorem stationary_iff_closure (n : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g)
    (X : Fin 5 → SU2)
    (hglue : ∀ e, n e ≠ 0 → bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) :
    (∀ l : Fin 12, Lightlike.Oscillatory.coordDeriv
        (fun θ => cohAmp n g (chart (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) θ)) l 0 = 0) ↔
      ∀ a : Fin 5, ∑ e, (n e : ℝ) • nodeNormal g a e = 0 := by
  rw [stationary_iff_closure_free n hg X hglue]
  refine ⟨fun h a => ?_, fun h a => h _⟩
  induction a using Fin.lastCases with
  | last => exact closure_last_of_glued n hg X hglue h
  | cast a => exact h a

/-! ## Trust checks -/

section TrustChecks

/-- `ν(1) = e_z`. -/
lemma bloch_one : bloch (1 : Matrix (Fin 2) (Fin 2) ℂ) = ![0, 0, 1] := by
  ext k; fin_cases k <;> simp [bloch]

/-- `ν(ε) = −e_z`. -/
lemma bloch_epsMat : bloch epsMat = ![0, 0, -1] := by
  ext k; fin_cases k <;> simp [bloch, epsMat]

/-- Boundary data glued at `X = 1` by construction: `g_ab = h_e` and `g_ba = h_e ε` on every
edge `e = ab`, so that the two normals of each edge are antiparallel. -/
noncomputable def twistData (h : Fin 10 → SU2) : BdryData :=
  fun e => ![(h e : Matrix (Fin 2) (Fin 2) ℂ), (h e : Matrix (Fin 2) (Fin 2) ℂ) * epsMat]

/-- The twisted data are SU(2) data. -/
lemma isSU2Data_twistData (h : Fin 10 → SU2) : IsSU2Data (twistData h) := by
  intro e i
  fin_cases i
  · exact (h e).2
  · exact (h e * epsSU2).2

/-- **Known value**: the propagator of the twisted data at `X = 1` is `1`. -/
theorem prop_twistData_one (h : Fin 10 → SU2) (e : Fin 10) :
    prop (twistData h) (fun _ => ((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) e = 1 := by
  have hu : star ((h e : Matrix (Fin 2) (Fin 2) ℂ) * epsMat) *
      ((h e : Matrix (Fin 2) (Fin 2) ℂ) * epsMat) = 1 :=
    mem_unitaryGroup_iff'.mp (specialUnitaryGroup_le_unitaryGroup (h e * epsSU2).2)
  change (((((h e : Matrix (Fin 2) (Fin 2) ℂ) * epsMat))ᴴ * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * 1 *
    ((h e : Matrix (Fin 2) (Fin 2) ℂ) * epsMat) : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = 1
  rw [conjTranspose_one, Matrix.mul_one, Matrix.mul_one, ← star_eq_conjTranspose, hu,
    one_apply_eq]

/-- **Known value**: `F_n = 1` for the twisted data at `X = 1`, for all spins. -/
theorem cohAmp_twistData_one (n : Fin 10 → ℕ) (h : Fin 10 → SU2) :
    cohAmp n (twistData h) (fun _ => ((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  unfold cohAmp
  exact Finset.prod_eq_one fun e _ => by rw [prop_twistData_one, one_pow]

/-- The twisted data are glued at `X = 1` on every edge. -/
theorem twistData_glued (h : Fin 10 → SU2) (e : Fin 10) :
    bloch (frameSrc (isSU2Data_twistData h) (fun _ => 1) e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt (isSU2Data_twistData h) (fun _ => 1) e : Matrix (Fin 2) (Fin 2) ℂ) :=
  (norm_prop_eq_one_iff (isSU2Data_twistData h) (fun _ => 1) e).mp
    (by rw [prop_twistData_one, norm_one])

/-- **Wrong input**: without the twist `ε`, i.e. with parallel instead of antiparallel normals
`g_ba = g_ab`, the propagator at `X = 1` vanishes. -/
theorem prop_untwisted_one (h : Fin 10 → SU2) (e : Fin 10) :
    prop (fun e => ![(h e : Matrix (Fin 2) (Fin 2) ℂ), (h e : Matrix (Fin 2) (Fin 2) ℂ)])
      (fun _ => ((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) e = 0 := by
  have hu : star (h e : Matrix (Fin 2) (Fin 2) ℂ) * (h e : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    mem_unitaryGroup_iff'.mp (specialUnitaryGroup_le_unitaryGroup (h e).2)
  change (((((h e : Matrix (Fin 2) (Fin 2) ℂ) * epsMat))ᴴ * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * 1 *
    (h e : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = 0
  rw [conjTranspose_one, Matrix.mul_one, Matrix.mul_one, conjTranspose_mul, Matrix.mul_assoc,
    ← star_eq_conjTranspose (h e : Matrix (Fin 2) (Fin 2) ℂ), hu, Matrix.mul_one]
  simp [epsMat]

/-- **Wrong input**: without the twist, `F_n = 0` at `X = 1` as soon as one spin is nonzero. -/
theorem cohAmp_untwisted_one (n : Fin 10 → ℕ) (h : Fin 10 → SU2) {e : Fin 10} (he : n e ≠ 0) :
    cohAmp n (fun e => ![(h e : Matrix (Fin 2) (Fin 2) ℂ), (h e : Matrix (Fin 2) (Fin 2) ℂ)])
      (fun _ => ((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) = 0 :=
  Finset.prod_eq_zero (mem_univ e) (by rw [prop_untwisted_one, zero_pow he])

/-- The closure coefficients of the twisted data: `ν(h_e)` at the source, `−ν(h_e)` at the
target. -/
lemma nodeNormal_twistData (h : Fin 10 → SU2) (a : Fin 5) (e : Fin 10) :
    nodeNormal (twistData h) a e =
      if edgeSrc e = a then bloch (h e : Matrix (Fin 2) (Fin 2) ℂ)
      else if edgeTgt e = a then -bloch (h e : Matrix (Fin 2) (Fin 2) ℂ) else 0 := by
  have h1 : twistData h e 1 = (h e : Matrix (Fin 2) (Fin 2) ℂ) * epsMat := rfl
  have h0 : twistData h e 0 = (h e : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  rw [nodeNormal, h0, h1, bloch_mul_epsMat (h e).2]

/-- **Glued but not closed is not stationary**: for the twisted data with `h = 1` all normals
are `±e_z`, the four edges at the node `0` all leave it, and with all spins `1` the integrand is
not stationary at `X = 1` although `|F_n| = 1` there. -/
theorem twistData_one_not_stationary :
    ¬ ∀ l : Fin 12, Lightlike.Oscillatory.coordDeriv
        (fun θ => cohAmp (fun _ => 1) (twistData fun _ => 1)
          (chart (fun b => (((fun _ => 1 : Fin 5 → SU2) b : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) θ))
        l 0 = 0 := by
  rw [stationary_iff_closure _ (isSU2Data_twistData _) _ fun e _ => twistData_glued _ e]
  intro hcl
  have h2 := congrFun (hcl 0) 2
  simp only [nodeNormal_twistData, OneMemClass.coe_one, bloch_one] at h2
  simp [Fin.sum_univ_succ, edgeSrc, edgeTgt] at h2
  norm_num at h2

/-- The edge labels of the triangle `012`: `h = ε` on the edge `02`, `h = 1` elsewhere. -/
noncomputable def triangleTwist : Fin 10 → SU2 := fun e => if e = 1 then epsSU2 else 1

/-- The spins of the triangle `012`: `1` on the edges `01`, `02`, `12`, and `0` elsewhere. -/
def triangleSpins : Fin 10 → ℕ := ![1, 1, 0, 0, 1, 0, 0, 0, 0, 0]

/-- **Non-vacuity of stationarity**: the twisted triangle data close at every node, so the
integrand is stationary at `X = 1`, where `|F_n| = 1`. -/
theorem triangle_stationary :
    ∀ l : Fin 12, Lightlike.Oscillatory.coordDeriv
        (fun θ => cohAmp triangleSpins (twistData triangleTwist)
          (chart (fun b => (((fun _ => 1 : Fin 5 → SU2) b : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) θ))
        l 0 = 0 := by
  rw [stationary_iff_closure _ (isSU2Data_twistData _) _ fun e _ => twistData_glued _ e]
  have hb : ∀ e, bloch (triangleTwist e : Matrix (Fin 2) (Fin 2) ℂ) =
      if e = 1 then ![0, 0, -1] else ![0, 0, 1] := fun e => by
    unfold triangleTwist
    split_ifs
    · exact bloch_epsMat
    · exact bloch_one
  intro a
  funext k
  simp only [nodeNormal_twistData, hb]
  fin_cases a <;> fin_cases k <;>
    simp [Fin.sum_univ_succ, edgeSrc, edgeTgt, triangleSpins]

end TrustChecks

end Lightlike.Asymptotics.EPRL
