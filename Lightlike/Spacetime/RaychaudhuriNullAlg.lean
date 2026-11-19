import Lightlike.Spacetime.RaychaudhuriShear

/-!
# The split over a screen projector, and the null screen (G1-009)

`trace_sq_split_proj`: for an idempotent `P = g⁻¹ h` of trace `m` and `B = B P`, `tr(B²) = (tr B)²/m + σ² - ω²`. For a null
`k`, an auxiliary null `N` with `g(k, N) = -1` and the screen metric `h = g + k♭ N♭ + N♭ k♭` of Kar and SenGupta
(gr-qc/0611123, Section D), `P = 1 + k N♭ + N k♭` is such a projector of trace `n - 2` (`nullScreen_proj_sq`,
`trace_nullScreen_proj`); for `M k = 0` and `k♭ M = 0` the projection `B̂ = P M P` keeps `tr M` and `tr M²`
(`trace_proj_conj`, `trace_proj_conj_sq`), and the null shear kills `k + N` (`nullShear_mulVec`).
-/

open Matrix

namespace Lightlike.Raychaudhuri

variable {n : ℕ}

/-- **The split for a screen projector**: if `P = g⁻¹ h` (`h` symmetric) is idempotent of trace `m ≠ 0` and `B = B P`,
then `tr(B²) = (tr B)²/m + |σ|² - |ω|²` with `σ = sym(gB) - (tr B/m) h` and `ω = antisym(gB)`. -/
theorem trace_sq_split_proj (G B h : Matrix (Fin n) (Fin n) ℝ) (hG : Gᵀ = G) (hGu : IsUnit G.det) (hh : hᵀ = h)
    {m : ℝ} (hm : m ≠ 0) (hP : (G⁻¹ * h) * (G⁻¹ * h) = G⁻¹ * h) (htr : trace (G⁻¹ * h) = m)
    (hBP : B * (G⁻¹ * h) = B) :
    trace (B * B) = (trace B) ^ 2 / m +
      normSqG G ((1 / 2 : ℝ) • (G * B + (G * B)ᵀ) - (trace B / m) • h) -
      normSqG G ((1 / 2 : ℝ) • (G * B - (G * B)ᵀ)) := by
  set Gi := G⁻¹ with hGi
  have hGiG : Gi * G = 1 := nonsing_inv_mul G hGu
  have hGiT : Giᵀ = Gi := by rw [hGi, transpose_nonsing_inv, hG]
  set L := G * B with hL
  set θ := trace B with hθ
  have tLL : trace (Gi * L * Gi * L) = trace (B * B) := by
    rw [hL, show Gi * (G * B) * Gi * (G * B) = (Gi * G) * B * (Gi * G) * B by simp only [Matrix.mul_assoc],
      hGiG, Matrix.one_mul, Matrix.mul_one]
  have tTT : trace (Gi * Lᵀ * Gi * Lᵀ) = trace (Gi * L * Gi * L) := by
    rw [← trace_transpose]
    simp only [transpose_mul, transpose_transpose, hGiT, Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have e1 : normSqG G ((1 / 2 : ℝ) • (L + Lᵀ)) - normSqG G ((1 / 2 : ℝ) • (L - Lᵀ)) = trace (B * B) := by
    unfold normSqG
    simp only [transpose_smul, transpose_add, transpose_sub, transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, trace_smul, trace_add, trace_sub, smul_eq_mul]
    rw [← tLL, ← tTT]
    ring
  set S := (1 / 2 : ℝ) • (L + Lᵀ) with hS
  have hSt : Sᵀ = S := by simp only [hS, transpose_smul, transpose_add, transpose_transpose, add_comm]
  -- the traces against `h`
  have t1 : trace (Gi * L * Gi * h) = θ := by
    rw [hL, show Gi * (G * B) * Gi * h = (Gi * G) * (B * (Gi * h)) by simp only [Matrix.mul_assoc], hGiG,
      Matrix.one_mul, hBP]
  have t2 : trace (Gi * Lᵀ * Gi * h) = θ := by
    rw [← trace_transpose]
    simp only [transpose_mul, transpose_transpose, hGiT, hh, hL, hG]
    rw [show h * (Gi * (G * B * Gi)) = h * ((Gi * G) * B * Gi) by simp only [Matrix.mul_assoc], hGiG,
      Matrix.one_mul, trace_mul_comm, Matrix.mul_assoc, hBP]
  have tSh : trace (Gi * S * Gi * h) = θ := by
    rw [hS]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, trace_smul, trace_add, t1, t2,
      smul_eq_mul]
    ring
  have thS : trace (Gi * h * Gi * S) = θ := by
    rw [show Gi * h * Gi * S = (Gi * h) * (Gi * S) by simp only [Matrix.mul_assoc], trace_mul_comm,
      show Gi * S * (Gi * h) = Gi * S * Gi * h by simp only [Matrix.mul_assoc], tSh]
  have thh : trace (Gi * h * Gi * h) = m := by
    rw [show Gi * h * Gi * h = (Gi * h) * (Gi * h) by simp only [Matrix.mul_assoc], hP, htr]
  have e2 : ∀ c : ℝ, normSqG G (S - c • h) = normSqG G S - 2 * c * θ + c ^ 2 * m := by
    intro c
    have hT : (S - c • h)ᵀ = S - c • h := by rw [transpose_sub, transpose_smul c h, hSt, hh]
    unfold normSqG
    rw [← hGi, hT, hSt]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, trace_sub, trace_smul, smul_eq_mul]
    rw [tSh, thS, thh]
    ring
  rw [e2, ← e1]
  field_simp
  ring

/-- The null screen metric `h = g + k♭ ⊗ N♭ + N♭ ⊗ k♭` (Kar–SenGupta, Section D). -/
def nullScreen (G : Matrix (Fin n) (Fin n) ℝ) (k N : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  G + vecMulVec (G *ᵥ k) (G *ᵥ N) + vecMulVec (G *ᵥ N) (G *ᵥ k)

section Null
variable {G : Matrix (Fin n) (Fin n) ℝ} {k N : Fin n → ℝ} (hG : Gᵀ = G) (hGu : IsUnit G.det)
  (hkk : k ⬝ᵥ (G *ᵥ k) = 0) (hNN : N ⬝ᵥ (G *ᵥ N) = 0) (hkN : k ⬝ᵥ (G *ᵥ N) = -1)
include hG hGu

omit hGu in
/-- `g` is symmetric: `p ⬝ g q = q ⬝ g p`. -/
theorem dot_G_comm (p q : Fin n → ℝ) : p ⬝ᵥ (G *ᵥ q) = q ⬝ᵥ (G *ᵥ p) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hG, dotProduct_comm]

omit hG in
/-- The projector onto the screen: `g⁻¹ h = 1 + k N♭ + N k♭`. -/
theorem inv_mul_nullScreen :
    G⁻¹ * nullScreen G k N = 1 + vecMulVec k (G *ᵥ N) + vecMulVec N (G *ᵥ k) := by
  have hGiG : G⁻¹ * G = 1 := nonsing_inv_mul G hGu
  unfold nullScreen
  rw [Matrix.mul_add, Matrix.mul_add, hGiG, mul_vecMulVec, mul_vecMulVec, mulVec_mulVec, mulVec_mulVec, hGiG,
    one_mulVec, one_mulVec]

include hkk hNN hkN

/-- `P = g⁻¹ h` is idempotent. -/
theorem nullScreen_proj_sq :
    (G⁻¹ * nullScreen G k N) * (G⁻¹ * nullScreen G k N) = G⁻¹ * nullScreen G k N := by
  rw [inv_mul_nullScreen hGu]
  have hNk : N ⬝ᵥ (G *ᵥ k) = -1 := by rw [dot_G_comm hG]; exact hkN
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, vecMulVec_mul_vecMulVec]
  rw [dotProduct_comm (G *ᵥ N) k, dotProduct_comm (G *ᵥ N) N, dotProduct_comm (G *ᵥ k) k,
    dotProduct_comm (G *ᵥ k) N, hkk, hNN, hkN, hNk]
  ext i j
  simp [vecMulVec_apply]

omit hkk hNN in
/-- `tr P = n - 2`. -/
theorem trace_nullScreen_proj : trace (G⁻¹ * nullScreen G k N) = n - 2 := by
  rw [inv_mul_nullScreen hGu, trace_add, trace_add, trace_one, trace_vecMulVec, trace_vecMulVec, hkN,
    show N ⬝ᵥ (G *ᵥ k) = -1 by rw [dot_G_comm hG]; exact hkN, Fintype.card_fin]
  ring

omit hG hkk hNN hkN in
/-- For `M k = 0`, `M P = M + (M N) k♭`. -/
theorem mul_nullScreen_proj {M : Matrix (Fin n) (Fin n) ℝ} (hMk : M *ᵥ k = 0) :
    M * (G⁻¹ * nullScreen G k N) = M + vecMulVec (M *ᵥ N) (G *ᵥ k) := by
  rw [inv_mul_nullScreen hGu, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, mul_vecMulVec, hMk]
  ext i j; simp [vecMulVec_apply]

/-- The projected derivative `B̂ = P M P` has the trace of `M`. -/
theorem trace_proj_conj {M : Matrix (Fin n) (Fin n) ℝ} (hMk : M *ᵥ k = 0) (hkM : (G *ᵥ k) ᵥ* M = 0) :
    trace ((G⁻¹ * nullScreen G k N) * M * (G⁻¹ * nullScreen G k N)) = trace M := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, nullScreen_proj_sq hG hGu hkk hNN hkN, trace_mul_comm,
    mul_nullScreen_proj hGu hMk, trace_add, trace_vecMulVec, dotProduct_comm, dotProduct_mulVec, hkM,
    zero_dotProduct, add_zero]

/-- `tr(B̂²) = tr(M²)`. -/
theorem trace_proj_conj_sq {M : Matrix (Fin n) (Fin n) ℝ} (hMk : M *ᵥ k = 0) (hkM : (G *ᵥ k) ᵥ* M = 0) :
    trace (((G⁻¹ * nullScreen G k N) * M * (G⁻¹ * nullScreen G k N)) *
      ((G⁻¹ * nullScreen G k N) * M * (G⁻¹ * nullScreen G k N))) = trace (M * M) := by
  set P := G⁻¹ * nullScreen G k N with hP
  have hPP : P * P = P := nullScreen_proj_sq hG hGu hkk hNN hkN
  have hMP : M * P = M + vecMulVec (M *ᵥ N) (G *ᵥ k) := mul_nullScreen_proj hGu hMk
  have e1 : trace (P * M * P * (P * M * P)) = trace ((M * P) * (M * P)) := by
    calc trace (P * M * P * (P * M * P)) = trace (P * M * (P * P) * M * P) := by simp only [Matrix.mul_assoc]
      _ = trace (P * (M * P * M * P)) := by rw [hPP]; simp only [Matrix.mul_assoc]
      _ = trace (M * P * M * (P * P)) := by rw [trace_mul_comm]; simp only [Matrix.mul_assoc]
      _ = trace ((M * P) * (M * P)) := by rw [hPP]; simp only [Matrix.mul_assoc]
  rw [e1, hMP]
  have h1 : (G *ᵥ k) ⬝ᵥ (M *ᵥ N) = 0 := by rw [dotProduct_mulVec, hkM, zero_dotProduct]
  simp only [Matrix.add_mul, Matrix.mul_add, trace_add, vecMulVec_mul, hkM, trace_vecMulVec]
  rw [mul_vecMulVec, trace_vecMulVec, vecMul_vecMulVec, h1]
  have h2 : (M *ᵥ (M *ᵥ N)) ⬝ᵥ (G *ᵥ k) = 0 := by rw [dotProduct_comm, dotProduct_mulVec, hkM, zero_dotProduct]
  rw [h2]
  simp

omit hG hGu hNN in
/-- `h k = 0`. -/
theorem nullScreen_mulVec_k : nullScreen G k N *ᵥ k = 0 := by
  unfold nullScreen
  rw [add_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, dotProduct_comm (G *ᵥ N) k, hkN,
    dotProduct_comm (G *ᵥ k) k, hkk]
  ext i; simp

omit hGu hkk in
/-- `h N = 0`. -/
theorem nullScreen_mulVec_N : nullScreen G k N *ᵥ N = 0 := by
  have hNk : N ⬝ᵥ (G *ᵥ k) = -1 := by rw [dot_G_comm hG]; exact hkN
  unfold nullScreen
  rw [add_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, dotProduct_comm (G *ᵥ N) N, hNN,
    dotProduct_comm (G *ᵥ k) N, hNk]
  ext i; simp

omit hGu hkk hNN hkN in
/-- `h` is symmetric. -/
theorem nullScreen_transpose : (nullScreen G k N)ᵀ = nullScreen G k N := by
  unfold nullScreen
  rw [transpose_add, transpose_add, hG, transpose_vecMulVec, transpose_vecMulVec, add_assoc, add_assoc,
    add_comm (vecMulVec (G *ᵥ k) (G *ᵥ N))]

/-- **The null shear is spatial**: `σ̂ (k + N) = 0` for `σ̂ = sym(g B̂) - c h`, `B̂ = P M P`, any `M`. -/
theorem nullShear_mulVec (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    ((1 / 2 : ℝ) • (G * ((G⁻¹ * nullScreen G k N) * M * (G⁻¹ * nullScreen G k N)) +
      (G * ((G⁻¹ * nullScreen G k N) * M * (G⁻¹ * nullScreen G k N)))ᵀ) - c • nullScreen G k N) *ᵥ (k + N) = 0 := by
  have hGGi : G * G⁻¹ = 1 := mul_nonsing_inv G hGu
  have hGiT : (G⁻¹)ᵀ = G⁻¹ := by rw [transpose_nonsing_inv, hG]
  have hh : nullScreen G k N *ᵥ (k + N) = 0 := by
    rw [mulVec_add, nullScreen_mulVec_k hkk hkN, nullScreen_mulVec_N hG hNN hkN, add_zero]
  have hP : (G⁻¹ * nullScreen G k N) *ᵥ (k + N) = 0 := by rw [← mulVec_mulVec, hh, mulVec_zero]
  have h1 : (G * ((G⁻¹ * nullScreen G k N) * M * (G⁻¹ * nullScreen G k N))) *ᵥ (k + N) = 0 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hP, mulVec_zero, mulVec_zero]
  have hv0 : (G *ᵥ (k + N)) ᵥ* (G⁻¹ * nullScreen G k N) = 0 := by
    rw [← vecMul_vecMul, show (G *ᵥ (k + N)) ᵥ* G⁻¹ = k + N by
        rw [← mulVec_transpose, hGiT, mulVec_mulVec, nonsing_inv_mul G hGu, one_mulVec],
      ← mulVec_transpose, nullScreen_transpose hG, hh]
  have h2 : (G * ((G⁻¹ * nullScreen G k N) * M * (G⁻¹ * nullScreen G k N)))ᵀ *ᵥ (k + N) = 0 := by
    rw [mulVec_transpose, ← vecMul_vecMul, show (k + N) ᵥ* G = G *ᵥ (k + N) by rw [← mulVec_transpose, hG],
      Matrix.mul_assoc (G⁻¹ * nullScreen G k N) M, ← vecMul_vecMul, hv0, zero_vecMul]
  rw [sub_mulVec, smul_mulVec, add_mulVec, h1, h2, smul_mulVec, hh]
  simp

end Null

end Lightlike.Raychaudhuri
