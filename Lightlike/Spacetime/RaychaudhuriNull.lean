import Lightlike.Spacetime.RaychaudhuriFocusing
import Lightlike.Spacetime.RaychaudhuriNullAlg

/-!
# Raychaudhuri's equation for a null geodesic congruence (G1-009)

Kar and SenGupta (gr-qc/0611123), Section D, eq. (17): for a null geodesic congruence `k` (`kᵃkₐ = 0`), with an auxiliary
null vector `N` (`kᵃNₐ = -1`) and the transverse metric `h_ab = g_ab + k_a N_b + k_b N_a`, the projected derivative
`B̂ = P (∇k) P` (`P = g⁻¹ h`) has expansion `Θ̂`, shear `σ̂` and rotation `ω̂` with
`dΘ̂/dλ + Θ̂²/2 + σ̂² - ω̂² = -R_ab kᵃ kᵇ` in dimension four, and focusing follows under the null convergence condition
`R_ab kᵃ kᵇ ≥ 0`. Here, in coordinates on an open `U ⊆ ℝⁿ`, for a smooth null geodesic field `k` on `U`:

* `raychaudhuri_null_equation`: `k(Θ) = -Θ²/(n-2) - σ̂² + ω̂² - R(k, k)`, with `Θ̂ = tr B̂ = Θ` the expansion;
* `raychaudhuri_null_focusing_at`, `raychaudhuri_null_focusing`: for a Lorentzian metric, `σ̂² ≥ 0`, and with `ω̂ = 0` and
  `R(k, k) ≥ 0`, `k(Θ) ≤ -Θ²/(n-2)`; along an integral curve on `[0, L)` with `Θ(γ(0)) < 0`, `L ≤ (n-2)/|Θ(γ(0))|`;
  a rotation-free field (`g ∇k` symmetric, e.g. hypersurface-orthogonal) has `ω̂ = 0` (`nullRotation_eq_zero`).
-/

open Filter Topology Set Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
  {v : (Fin n → ℝ) → Fin n → ℝ}

/-- **A field of constant norm is orthogonal to its derivative**: if `g(v, v)` is a constant `c` on `U`, then
`g(v, ∇_b v) = 0` on `U` (for `c = 0`, a null field). -/
theorem covD_orthogonal_of_const {c : ℝ} (hg : IsCoordMetric g U) (hv : ∀ a, ContDiffOn ℝ ∞ (fun y => v y a) U)
    (hnorm : ∀ y ∈ U, v y ⬝ᵥ (g y *ᵥ v y) = c) {x : Fin n → ℝ} (hx : x ∈ U) (b : Fin n) :
    ∑ a, (g x *ᵥ v x) a * covD g v a b x = 0 := by
  have dv := fun a => differentiableAt_of_contDiffOn (hv a) hg.isOpen hx
  have dg := fun a c => differentiableAt_of_contDiffOn (hg.smooth a c) hg.isOpen hx
  have hF : (fun y => ∑ a, ∑ c, v y a * g y a c * v y c) =ᶠ[𝓝 x] fun _ => c :=
    Filter.eventually_of_mem (hg.isOpen.mem_nhds hx) fun y hy => by
      rw [← hnorm y hy]; simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have h0 := pd_congr hF b
  have hc : pd b (fun _ : Fin n → ℝ => c) x = 0 := by simp [pd]
  have hm2 : ∀ a c, DifferentiableAt ℝ (fun y => v y a * g y a c) x := fun a c => (dv a).mul (dg a c)
  have hm : ∀ a c, DifferentiableAt ℝ (fun y => v y a * g y a c * v y c) x := fun a c => (hm2 a c).mul (dv c)
  have hpdF : pd b (fun y => ∑ a, ∑ c, v y a * g y a c * v y c) x =
      ∑ a, ∑ c, ((pd b (fun z => v z a) x * g x a c + v x a * (christoffelFirst g a b c x +
        christoffelFirst g c b a x)) * v x c + v x a * g x a c * pd b (fun z => v z c) x) := by
    rw [pd_sum (f := fun a y => ∑ c, v y a * g y a c * v y c) _
      (fun a _ => DifferentiableAt.fun_sum fun c _ => hm a c) b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pd_sum (f := fun c y => v y a * g y a c * v y c) _ (fun c _ => hm a c) b]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [pd_mul (hm2 a c) (dv c) b, pd_mul (dv a) (dg a c) b, hg.pd_eq_christoffelFirst hx b a c]
  rw [hc, hpdF] at h0
  have hs : ∀ a c, g x a c = g x c a := fun a c => by
    conv_rhs => rw [← hg.symm x hx]
    rfl
  -- the two halves
  set T1 := ∑ a, ∑ c, g x a c * v x c * pd b (fun z => v z a) x
  set T2 := ∑ a, ∑ c, v x a * christoffelFirst g a b c x * v x c
  have e1 : ∑ a, ∑ c, v x a * g x a c * pd b (fun z => v z c) x = T1 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hs]; ring
  have e2 : ∑ a, ∑ c, v x a * christoffelFirst g c b a x * v x c = T2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  have hpd : (∑ a, ∑ c, ((pd b (fun z => v z a) x * g x a c + v x a * (christoffelFirst g a b c x +
      christoffelFirst g c b a x)) * v x c + v x a * g x a c * pd b (fun z => v z c) x)) = 2 * T1 + 2 * T2 := by
    have : ∀ a c, ((pd b (fun z => v z a) x * g x a c + v x a * (christoffelFirst g a b c x +
        christoffelFirst g c b a x)) * v x c + v x a * g x a c * pd b (fun z => v z c) x) =
        g x a c * v x c * pd b (fun z => v z a) x + v x a * christoffelFirst g a b c x * v x c +
        v x a * christoffelFirst g c b a x * v x c + v x a * g x a c * pd b (fun z => v z c) x := fun a c => by ring
    simp only [this, Finset.sum_add_distrib, e1, e2]
    ring
  have h1 : ∑ a, (∑ c, g x a c * v x c) * pd b (fun z => v z a) x = T1 := by
    simp only [T1, Finset.sum_mul]
  have h2 : ∑ a, (∑ c, g x a c * v x c) * ∑ d, christoffel g a b d x * v x d = T2 := by
    have : T2 = ∑ c, ∑ d, ∑ a, g x a c * v x c * (christoffel g a b d x * v x d) := by
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      rw [← hg.lower_christoffel hx c b d, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by rw [hs a c]; ring
    rw [this]
    simp only [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
  have hT : ∑ a, (g x *ᵥ v x) a * covD g v a b x = T1 + T2 := by
    simp only [covD, mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
    rw [h1, h2]
  rw [hT]
  linarith [hpd, h0]


/-- The screen projector `P = g⁻¹ h` at `x` for the auxiliary null vector `N`. -/
def nullProj (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (x N : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (g x)⁻¹ * Raychaudhuri.nullScreen (g x) (v x) N

/-- The projected derivative `B̂ = P (∇v) P`. -/
def nullB (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (x N : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  nullProj g v x N * covDMat g v x * nullProj g v x N

/-- The null shear `σ̂ = sym(g B̂) - (Θ/(n-2)) h`. -/
def nullShear (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (x N : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (g x * nullB g v x N + (g x * nullB g v x N)ᵀ) -
    (expansion g v x / ((n : ℝ) - 2)) • Raychaudhuri.nullScreen (g x) (v x) N

/-- The null rotation `ω̂ = antisym(g B̂)`. -/
def nullRotation (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (x N : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (g x * nullB g v x N - (g x * nullB g v x N)ᵀ)

section
variable (hg : IsCoordMetric g U) (hv : ∀ a, ContDiffOn ℝ ∞ (fun y => v y a) U)
  (hgeo : ∀ y ∈ U, ∀ d, ∑ c, v y c * covD g v d c y = 0) (hnull : ∀ y ∈ U, v y ⬝ᵥ (g y *ᵥ v y) = 0)
include hg hv hgeo hnull

/-- `M k = 0` and `k♭ M = 0` for a null geodesic field. -/
theorem covDMat_null {x : Fin n → ℝ} (hx : x ∈ U) :
    covDMat g v x *ᵥ v x = 0 ∧ (g x *ᵥ v x) ᵥ* covDMat g v x = 0 := by
  constructor
  · funext d; simp only [Matrix.mulVec, dotProduct, covDMat, Matrix.of_apply, Pi.zero_apply]
    rw [← hgeo x hx d]; exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · funext b; simp only [vecMul, dotProduct, covDMat, Matrix.of_apply, Pi.zero_apply]
    exact covD_orthogonal_of_const hg hv hnull hx b

/-- **Raychaudhuri's equation for a null geodesic field in coordinates** (Kar–SenGupta (17), any dimension `n ≥ 3`):
for an auxiliary null `N` with `g(k, N) = -1` at `x`, `k(Θ) = -Θ²/(n-2) - σ̂² + ω̂² - R(k, k)`, with `Θ = tr B̂` the
expansion. -/
theorem raychaudhuri_null_equation {x : Fin n → ℝ} (hx : x ∈ U) {N : Fin n → ℝ} (hNN : N ⬝ᵥ (g x *ᵥ N) = 0)
    (hkN : v x ⬝ᵥ (g x *ᵥ N) = -1) (hn : 2 < n) :
    ∑ c, v x c * pd c (expansion g v) x =
      -(expansion g v x) ^ 2 / (n - 2) - Raychaudhuri.normSqG (g x) (nullShear g v x N) +
        Raychaudhuri.normSqG (g x) (nullRotation g v x N) - ∑ s, ∑ t, ricci g s t x * v x s * v x t := by
  have hG := hg.symm x hx
  have hGu := hg.isUnit_det x hx
  have hkk := hnull x hx
  obtain ⟨hMk, hkM⟩ := covDMat_null hg hv hgeo hnull hx
  have hm : (n : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hPP := Raychaudhuri.nullScreen_proj_sq hG hGu hkk hNN hkN
  have hBP : nullB g v x N * nullProj g v x N = nullB g v x N := by
    unfold nullB nullProj; rw [Matrix.mul_assoc _ _ ((g x)⁻¹ * _), hPP]
  have hsplit := Raychaudhuri.trace_sq_split_proj (g x) (nullB g v x N) (Raychaudhuri.nullScreen (g x) (v x) N) hG
    hGu (Raychaudhuri.nullScreen_transpose hG) hm hPP (Raychaudhuri.trace_nullScreen_proj hG hGu hkN) hBP
  have hB2 : Matrix.trace (nullB g v x N * nullB g v x N) = Matrix.trace (covDMat g v x * covDMat g v x) :=
    Raychaudhuri.trace_proj_conj_sq hG hGu hkk hNN hkN hMk hkM
  have hB1 : Matrix.trace (nullB g v x N) = expansion g v x := by
    unfold nullB nullProj
    rw [Raychaudhuri.trace_proj_conj hG hGu hkk hNN hkN hMk hkM]
    simp [Matrix.trace, covDMat, expansion]
  have hsq : Matrix.trace (covDMat g v x * covDMat g v x) = ∑ a, ∑ b, covD g v a b x * covD g v b a x := by
    simp [Matrix.trace, Matrix.mul_apply, covDMat]
  rw [raychaudhuri_coord hg hv hgeo hx, ← hsq, ← hB2, hsplit, hB1]
  unfold nullShear nullRotation
  ring

end

/-- **The null shear term is nonnegative** for a Lorentzian coordinate metric: `σ̂` is symmetric and kills the timelike
`u = (k + N)/√2`, whose orthogonal complement is spacelike. -/
theorem nullShear_normSq_nonneg (hgL : IsLorentzianCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) {N : Fin n → ℝ}
    (hkk : v x ⬝ᵥ (g x *ᵥ v x) = 0) (hNN : N ⬝ᵥ (g x *ᵥ N) = 0) (hkN : v x ⬝ᵥ (g x *ᵥ N) = -1) :
    0 ≤ Raychaudhuri.normSqG (g x) (nullShear g v x N) := by
  have hg := hgL.1
  have hG := hg.symm x hx
  have hGu := hg.isUnit_det x hx
  set u : Fin n → ℝ := (1 / Real.sqrt 2) • (v x + N) with hu
  have hNk : N ⬝ᵥ (g x *ᵥ v x) = -1 := by rw [Raychaudhuri.dot_G_comm hG]; exact hkN
  have hs : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have huu : u ⬝ᵥ (g x *ᵥ u) = -1 := by
    simp only [hu, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, mulVec_add, dotProduct_add,
      add_dotProduct, hkk, hNN, hkN, hNk]
    rw [show (1 / Real.sqrt 2) * ((1 / Real.sqrt 2) * (0 + -1) + (1 / Real.sqrt 2) * (-1 + 0)) =
      ((1 / Real.sqrt 2) * (1 / Real.sqrt 2)) * (-2) by ring, hs]
    norm_num
  have hsym : (nullShear g v x N)ᵀ = nullShear g v x N := by
    unfold nullShear
    rw [transpose_sub, transpose_smul, transpose_smul, transpose_add, transpose_transpose,
      Raychaudhuri.nullScreen_transpose hG, add_comm (g x * nullB g v x N)ᵀ]
  have hσu : nullShear g v x N *ᵥ u = 0 := by
    have := Raychaudhuri.nullShear_mulVec hG hGu hkk hNN hkN (covDMat g v x) (expansion g v x / ((n : ℝ) - 2))
    rw [hu, mulVec_smul]
    unfold nullShear nullB nullProj
    rw [this, smul_zero]
  exact Raychaudhuri.normSqG_nonneg (g x) _ u hG hGu hsym hσu
    (Raychaudhuri.spacelike_complement (g x) u hG huu (hgL.orthogonal_nonneg hx (by rw [huu]; norm_num)))

/-- A rotation-free field (`ω = 0`, `g ∇v` symmetric) has `ω̂ = 0`. -/
theorem nullRotation_eq_zero {x : Fin n → ℝ} (hG : (g x)ᵀ = g x) (hGu : IsUnit (g x).det) {N : Fin n → ℝ}
    (hω : rotation g v x = 0) : nullRotation g v x N = 0 := by
  set P := nullProj g v x N
  set M := covDMat g v x
  set h := Raychaudhuri.nullScreen (g x) (v x) N
  have hGGi : g x * (g x)⁻¹ = 1 := mul_nonsing_inv _ hGu
  have hGiT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by rw [transpose_nonsing_inv, hG]
  have hhT : hᵀ = h := Raychaudhuri.nullScreen_transpose hG
  have hL : (g x * M)ᵀ = g x * M := by
    unfold rotation at hω
    have h2 : (1 / 2 : ℝ) • (g x * covDMat g v x - (g x * covDMat g v x)ᵀ) = 0 := hω
    have h3 : g x * covDMat g v x - (g x * covDMat g v x)ᵀ = 0 := by
      have := congrArg (fun A => (2 : ℝ) • A) h2
      simpa [smul_smul] using this
    exact (sub_eq_zero.1 h3).symm
  have hMt : Mᵀ = g x * M * (g x)⁻¹ := by
    have : Mᵀ * g x = g x * M := by rw [← hG, ← transpose_mul, hG]; exact hL
    calc Mᵀ = Mᵀ * g x * (g x)⁻¹ := by rw [Matrix.mul_assoc, hGGi, Matrix.mul_one]
      _ = g x * M * (g x)⁻¹ := by rw [this]
  have hGP : g x * P = h := by
    simp only [P, nullProj, ← Matrix.mul_assoc, hGGi, Matrix.one_mul]; rfl
  have hsymB : (g x * nullB g v x N)ᵀ = g x * nullB g v x N := by
    unfold nullB
    rw [show g x * (P * M * P) = (g x * P) * M * P by simp only [Matrix.mul_assoc], hGP]
    simp only [transpose_mul, hhT, hMt, P, nullProj, transpose_nonsing_inv, hG]
    simp only [Matrix.mul_assoc]
    rw [show (g x)⁻¹ * (g x * (M * ((g x)⁻¹ * h))) = M * ((g x)⁻¹ * h) by
      rw [← Matrix.mul_assoc, nonsing_inv_mul _ hGu, Matrix.one_mul]]
    show hᵀ * (M * ((g x)⁻¹ * h)) = h * (M * ((g x)⁻¹ * h))
    rw [hhT]
  unfold nullRotation
  rw [hsymB, sub_self, smul_zero]

section
variable (hgL : IsLorentzianCoordMetric g U) (hv : ∀ a, ContDiffOn ℝ ∞ (fun y => v y a) U)
  (hgeo : ∀ y ∈ U, ∀ d, ∑ c, v y c * covD g v d c y = 0) (hnull : ∀ y ∈ U, v y ⬝ᵥ (g y *ᵥ v y) = 0)
include hgL hv hgeo hnull

/-- **Null focusing inequality** (Kar–SenGupta, after (17)): for a null geodesic field of a Lorentzian coordinate metric with
`R(k, k) ≥ 0` at `x` and an auxiliary null `N` (`g(k, N) = -1`) for which the screen rotation vanishes (`ω̂ = 0`):
`k(Θ) ≤ -Θ²/(n-2)`. A rotation-free field has `ω̂ = 0` for every `N` (`nullRotation_eq_zero`). -/
theorem raychaudhuri_null_focusing_at {x : Fin n → ℝ} (hx : x ∈ U) (hn : 2 < n)
    (hN : ∃ N : Fin n → ℝ, N ⬝ᵥ (g x *ᵥ N) = 0 ∧ v x ⬝ᵥ (g x *ᵥ N) = -1 ∧ nullRotation g v x N = 0)
    (hR : 0 ≤ ∑ s, ∑ t, ricci g s t x * v x s * v x t) :
    ∑ c, v x c * pd c (expansion g v) x ≤ -(expansion g v x) ^ 2 / (n - 2) := by
  obtain ⟨N, hNN, hkN, hω⟩ := hN
  rw [raychaudhuri_null_equation hgL.1 hv hgeo hnull hx hNN hkN hn, hω]
  have hσ := nullShear_normSq_nonneg hgL hx (hnull x hx) hNN hkN (v := v)
  have h0 : Raychaudhuri.normSqG (g x) 0 = 0 := by simp [Raychaudhuri.normSqG]
  rw [h0]
  linarith

/-- **Null geodesic focusing** (Kar–SenGupta, after (17): the null convergence condition `R_ab kᵃ kᵇ ≥ 0`): along an
integral curve `γ` on `[0, L)` in `U` of a null geodesic field of a Lorentzian coordinate metric (`n ≥ 3`), with
`R(k, k) ≥ 0` and an auxiliary null vector with `ω̂ = 0` along `γ`, that starts converging (`Θ(γ(0)) < 0`):
`L ≤ (n-2)/|Θ(γ(0))|`. -/
theorem raychaudhuri_null_focusing (hn : 2 < n) {γ : ℝ → Fin n → ℝ} {L : ℝ} (hγU : ∀ s ∈ Ico 0 L, γ s ∈ U)
    (hγ : ∀ s ∈ Ico 0 L, HasDerivAt γ (v (γ s)) s)
    (hN : ∀ s ∈ Ico 0 L, ∃ N : Fin n → ℝ, N ⬝ᵥ (g (γ s) *ᵥ N) = 0 ∧ v (γ s) ⬝ᵥ (g (γ s) *ᵥ N) = -1 ∧
      nullRotation g v (γ s) N = 0)
    (hR : ∀ s ∈ Ico 0 L, 0 ≤ ∑ a, ∑ b, ricci g a b (γ s) * v (γ s) a * v (γ s) b)
    (h0 : expansion g v (γ 0) < 0) : L ≤ (n - 2) / |expansion g v (γ 0)| := by
  have hm : (0 : ℝ) < n - 2 := by
    have : (2 : ℝ) < n := by exact_mod_cast hn
    linarith
  exact focusing_along hv hgL.1 hm hγU hγ
    (fun s hs => raychaudhuri_null_focusing_at hgL hv hgeo hnull (hγU s hs) hn (hN s hs) (hR s hs)) h0

end

end Lightlike
