module

public import Lightlike.Lorentz.Radial

/-!
# The Cartan decomposition of SL(2,ℂ)

Every `g ∈ SL(2,ℂ)` factors as `g = u · a_r · v` with `u, v ∈ SU(2)` and
`a_r = diag(e^{r/2}, e^{-r/2})` (`exists_cartan`). The proof is the singular value
decomposition: the Hermitian matrix `g†g` is diagonalised by a unitary `U` (Mathlib's spectral
theorem `Matrix.IsHermitian.spectral_theorem`), its eigenvalues `λ₀, λ₁` are positive with
`λ₀ λ₁ = det(g†g) = 1`, and `W = g U diag(λ₀^{-1/2}, λ₁^{-1/2})` is unitary. A square root `c`
of `det U` fixes the determinants: `g = (c⁻¹W) · diag(√λ₀, √λ₁) · (c U†)` with both outer factors
in `SU(2)`.

The parameter `r` is the hyperbolic distance from the base point of `SL(2,ℂ)/SU(2) ≅ H³` to
`g · o`: `coshDist g = ‖g‖²_F / 2` is invariant under `SU(2)` on both sides
(`coshDist_SU2_mul_mul`), so `coshDist (u a_r v) = cosh r` (`coshDist_cartan`). In particular `|r|`
is determined by `g`.

## References

* A. W. Knapp, *Representation Theory of Semisimple Groups*, Princeton 1986, ch. V (the
  decomposition `G = KAK`).
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, Cambridge 1985, §7.3 (the singular value
  decomposition).
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz

local notation "M2" => Matrix (Fin 2) (Fin 2) ℂ

/-- The Cartan torus element `a_r = diag(e^{r/2}, e^{-r/2})`. -/
noncomputable def diagR (r : ℝ) : SL2C :=
  SL2C.diagSL (Real.exp (r / 2) : ℂ) (by exact_mod_cast (Real.exp_pos _).ne')

/-- The matrix of `a_r`. -/
lemma coe_diagR (r : ℝ) : ((diagR r : SL2C) : M2) =
    !![(Real.exp (r / 2) : ℂ), 0; 0, (Real.exp (-(r / 2)) : ℂ)] := by
  simp [diagR, SL2C.diagSL, Real.exp_neg]

/-- `coshDist g = tr(g†g) / 2`. -/
lemma coshDist_eq_trace (g : SL2C) :
    (coshDist g : ℂ) = Matrix.trace ((g : M2)ᴴ * (g : M2)) / 2 := by
  simp [coshDist, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Complex.conj_mul']
  ring

/-- `coshDist a_r = cosh r`. -/
lemma coshDist_diagR (r : ℝ) : coshDist (diagR r) = Real.cosh r := by
  simp only [coshDist, coe_diagR]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_zero]
  rw [Real.cosh_eq, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  ring_nf


/-- `u†u = 1` for `u ∈ SU(2)`. -/
lemma SU2_star_mul (u : Lightlike.SU2) : star (u : M2) * (u : M2) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp u.2).1

/-- `uu† = 1` for `u ∈ SU(2)`. -/
lemma SU2_mul_star (u : Lightlike.SU2) : (u : M2) * star (u : M2) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp u.2).1

/-- `tr((UGV)†(UGV)) = tr(G†G)` for unitary `U`, `V`. -/
lemma trace_star_mul_unitary (G U V : M2) (hU : star U * U = 1) (hV : V * star V = 1) :
    trace (star (U * G * V) * (U * G * V)) = trace (star G * G) := by
  calc trace (star (U * G * V) * (U * G * V))
        = trace (star V * (star G * (star U * U) * G * V)) := by
          simp only [star_mul, mul_assoc]
      _ = trace (star G * G * (V * star V)) := by
          rw [hU, mul_one, trace_mul_comm]; simp only [mul_assoc]
      _ = trace (star G * G) := by rw [hV, mul_one]

/-- `coshDist` is invariant under `SU(2)` on both sides. -/
lemma coshDist_SU2_mul_mul (u v : Lightlike.SU2) (g : SL2C) :
    coshDist (SL2C.ofSU2 u * g * SL2C.ofSU2 v) = coshDist g := by
  have h : ((coshDist (SL2C.ofSU2 u * g * SL2C.ofSU2 v) : ℝ) : ℂ) = coshDist g := by
    rw [coshDist_eq_trace, coshDist_eq_trace]
    simp only [Matrix.SpecialLinearGroup.coe_mul, SL2C.coe_ofSU2, ← Matrix.star_eq_conjTranspose]
    rw [trace_star_mul_unitary _ _ _ (SU2_star_mul u) (SU2_mul_star v)]
  exact_mod_cast h

/-- `coshDist (u a_r v) = cosh r`: `r` is the hyperbolic distance of `g · o` from `o`. -/
theorem coshDist_cartan (u v : Lightlike.SU2) (r : ℝ) :
    coshDist (SL2C.ofSU2 u * diagR r * SL2C.ofSU2 v) = Real.cosh r := by
  rw [coshDist_SU2_mul_mul, coshDist_diagR]


/-- A diagonal matrix with real entries is self-adjoint. -/
lemma star_diag_real (s : Fin 2 → ℝ) :
    star (diagonal (fun i => (s i : ℂ)) : M2) = diagonal (fun i => (s i : ℂ)) := by
  rw [Matrix.star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1; funext i; simp

/-- The matrix form of the Cartan decomposition: every `G` with `det G = 1` is
`W · diag(s₀, s₁) · V` with `W, V` special unitary, `s₀, s₁ > 0`, `s₀ s₁ = 1`. -/
lemma exists_cartan_matrix (G : M2) (hG : G.det = 1) :
    ∃ W V : M2, star W * W = 1 ∧ W.det = 1 ∧ star V * V = 1 ∧ V.det = 1 ∧
      ∃ s : Fin 2 → ℝ, (∀ i, 0 < s i) ∧ s 0 * s 1 = 1 ∧
        G = W * diagonal (fun i => (s i : ℂ)) * V := by
  have hA : (Gᴴ * G).IsHermitian := isHermitian_conjTranspose_mul_self G
  set U : M2 := (hA.eigenvectorUnitary : M2) with hUdef
  set l := hA.eigenvalues with hl
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : star G * G = U * diagonal (fun i => (l i : ℂ)) * star U := by
    rw [Matrix.star_eq_conjTranspose]
    exact hA.spectral_theorem
  have hnn : ∀ i, 0 ≤ l i := eigenvalues_conjTranspose_mul_self_nonneg G
  have hprod : l 0 * l 1 = 1 := by
    have h := hA.det_eq_prod_eigenvalues
    rw [det_mul, det_conjTranspose, hG, star_one, one_mul, Fin.prod_univ_two] at h
    have h2 : ((l 0 * l 1 : ℝ) : ℂ) = 1 := by push_cast; exact h.symm
    exact_mod_cast h2
  have hl0 : 0 < l 0 := lt_of_le_of_ne (hnn 0) (fun h => by rw [← h] at hprod; simp at hprod)
  have hl1 : 0 < l 1 := lt_of_le_of_ne (hnn 1) (fun h => by rw [← h] at hprod; simp at hprod)
  set s : Fin 2 → ℝ := fun i => Real.sqrt (l i) with hsdef
  have hs : ∀ i, 0 < s i := fun i => Real.sqrt_pos.mpr (by fin_cases i <;> assumption)
  have hss : ∀ i, s i * s i = l i := fun i => Real.mul_self_sqrt (hnn i)
  have hs01 : s 0 * s 1 = 1 := by
    simp only [hsdef]; rw [← Real.sqrt_mul (hnn 0), hprod, Real.sqrt_one]
  set Sg : M2 := diagonal (fun i => (s i : ℂ)) with hSg
  set Si : M2 := diagonal (fun i => ((s i)⁻¹ : ℝ)) with hSi
  have hSiSg : Si * Sg = 1 := by
    rw [hSi, hSg, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; push_cast; exact inv_mul_cancel₀ (by exact_mod_cast (hs i).ne')
  set W : M2 := G * U * Si with hW
  have hWW : star W * W = 1 := by
    have h1 : star W * W = star Si * (star U * (star G * G) * U) * Si := by
      simp only [hW, star_mul, mul_assoc]
    rw [h1, hspec, star_diag_real]
    have h2 : star U * (U * diagonal (fun i => (l i : ℂ)) * star U) * U =
        diagonal (fun i => (l i : ℂ)) := by
      calc star U * (U * diagonal (fun i => (l i : ℂ)) * star U) * U
          = (star U * U) * diagonal (fun i => (l i : ℂ)) * (star U * U) := by
            simp only [mul_assoc]
        _ = _ := by rw [hUU, one_mul, mul_one]
    rw [h2, hSi, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    have hsi : (s i : ℂ) ≠ 0 := by exact_mod_cast (hs i).ne'
    rw [← hss i]; push_cast; field_simp
  have hGfac : G = W * Sg * star U := by
    rw [hW, show G * U * Si * Sg * star U = G * (U * (Si * Sg) * star U) by
      simp only [mul_assoc], hSiSg, mul_one, hUU', mul_one]
  -- the determinant phase
  set δ := U.det with hδ
  have hδδ : star δ * δ = 1 := by
    have := congrArg Matrix.det hUU
    rwa [det_mul, Matrix.star_eq_conjTranspose, det_conjTranspose, det_one] at this
  have hdetSg : Sg.det = 1 := by
    rw [hSg, det_diagonal, Fin.prod_univ_two]; exact_mod_cast hs01
  have hdetW : W.det = δ := by
    have h := congrArg Matrix.det hGfac
    rw [hG, det_mul, det_mul, hdetSg, mul_one, Matrix.star_eq_conjTranspose,
      det_conjTranspose] at h
    calc W.det = W.det * (star δ * δ) := by rw [hδδ, mul_one]
      _ = (W.det * star δ) * δ := by ring
      _ = δ := by rw [← h, one_mul]
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq δ (n := 2) (by norm_num)
  have hnδ : ‖δ‖ = 1 := by
    have h : (‖δ‖ : ℂ) ^ 2 = 1 := by rw [← Complex.conj_mul']; exact hδδ
    have h' : ‖δ‖ ^ 2 = 1 := by exact_mod_cast h
    nlinarith [norm_nonneg δ]
  have hnc : ‖c‖ = 1 := by
    have h : ‖c‖ ^ 2 = 1 := by rw [← norm_pow, hc, hnδ]
    nlinarith [norm_nonneg c]
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hnc]; simp
  have hc0 : c ≠ 0 := fun h => by simp [h] at hnc
  have hδ0 : δ ≠ 0 := fun h => by simp [h] at hnδ
  refine ⟨c⁻¹ • W, c • star U, ?_, ?_, ?_, ?_, s, hs, hs01, ?_⟩
  · rw [star_smul, smul_mul_smul_comm, hWW, star_inv₀, ← mul_inv, hcc, inv_one, one_smul]
  · rw [det_smul, Fintype.card_fin, inv_pow, hc, hdetW, inv_mul_cancel₀ hδ0]
  · rw [star_smul, star_star, smul_mul_smul_comm, hcc, hUU', one_smul]
  · rw [det_smul, Fintype.card_fin, hc, Matrix.star_eq_conjTranspose, det_conjTranspose, ← hδ,
      mul_comm, hδδ]
  · rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hc0, one_smul,
      ← hGfac]


/-- An element of `SU(2)` from a special unitary matrix. -/
def SU2.mk' (W : M2) (hW : star W * W = 1) (hd : W.det = 1) : Lightlike.SU2 :=
  ⟨W, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff'.mpr hW, hd⟩⟩

/-- **Cartan decomposition** of `SL(2,ℂ)`: `g = u · a_r · v` with `u, v ∈ SU(2)`. -/
theorem exists_cartan (g : SL2C) : ∃ u v : Lightlike.SU2, ∃ r : ℝ,
    g = SL2C.ofSU2 u * diagR r * SL2C.ofSU2 v := by
  obtain ⟨W, V, hW, hdW, hV, hdV, s, hs, hs01, hfac⟩ := exists_cartan_matrix (g : M2) g.2
  refine ⟨SU2.mk' W hW hdW, SU2.mk' V hV hdV, 2 * Real.log (s 0), ?_⟩
  have hs1 : s 1 = (s 0)⁻¹ := eq_inv_of_mul_eq_one_right hs01
  have hD : ((diagR (2 * Real.log (s 0)) : SL2C) : M2) = diagonal (fun i => (s i : ℂ)) := by
    rw [coe_diagR, show 2 * Real.log (s 0) / 2 = Real.log (s 0) by ring, Real.exp_neg,
      Real.exp_log (hs 0), ← hs1]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, SL2C.coe_ofSU2, hD]
  exact congrFun (congrFun hfac i) j

end Lightlike.Lorentz
