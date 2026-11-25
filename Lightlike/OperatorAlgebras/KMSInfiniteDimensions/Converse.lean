import Lightlike.OperatorAlgebras.KMSInfiniteDimensions.StripUnique

/-!
# A diagonal KMS state is a Gibbs state: the weight relation

For a Hilbert basis `b`, real eigenvalues `ev` and weights `p : ι → ℂ`, the *diagonal functional*
`ω_p(A) = ∑ₙ pₙ ⟪bₙ, A bₙ⟫` generalises the Gibbs state of `GibbsKMS.lean` (`pₙ = e^{-βλₙ}/Z`).

* `diagState b p`: the diagonal functional;
* `rankOne b m n`: the matrix unit `|bₘ⟩⟨bₙ|`;
* `weights_of_isKMSState`: if `ω_p` satisfies the strip KMS condition `IsKMSState` at `β > 0` for the flow
  `τᵗ(A) = e^{itH} A e^{-itH}`, then `pₙ = pₘ e^{-β(λₙ - λₘ)}` for all `m n`.  Proof: for the matrix units
  `a = |bₘ⟩⟨bₙ|`, `B = |bₙ⟩⟨bₘ|` one has `ω_p(a τᵗ(B)) = pₘ e^{it(λₙ-λₘ)}` and `ω_p(τᵗ(B) a) = pₙ e^{it(λₙ-λₘ)}`;
  the KMS function `F` agrees on `ℝ` with the entire function `pₘ e^{iz(λₙ-λₘ)}`, hence on the whole strip
  (`eqOn_of_eqOn_real`), and one evaluates at `iβ`.

No summability of `p` is needed: on matrix units the series has one term.
-/

namespace Lightlike.Rows.G1_053

open Lightlike.OperatorAlgebras.GibbsKMS
open scoped InnerProductSpace

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The diagonal functional** `ω_p(A) = ∑ₙ pₙ ⟪bₙ, A bₙ⟫`. -/
noncomputable def diagState (b : HilbertBasis ι ℂ H) (p : ι → ℂ) (A : H →L[ℂ] H) : ℂ :=
  ∑' n, p n * ⟪b n, A (b n)⟫_ℂ

/-- **The matrix unit** `|bₘ⟩⟨bₙ|`: `x ↦ ⟪bₙ, x⟫ bₘ`. -/
noncomputable def rankOne (b : HilbertBasis ι ℂ H) (m n : ι) : H →L[ℂ] H :=
  (innerSL ℂ (b n)).smulRight (b m)

omit [CompleteSpace H] in
lemma rankOne_apply (b : HilbertBasis ι ℂ H) (m n : ι) (x : H) :
    rankOne b m n x = ⟪b n, x⟫_ℂ • b m := rfl

variable [DecidableEq ι]

omit [CompleteSpace H] in
lemma inner_basis_basis (b : HilbertBasis ι ℂ H) (i j : ι) :
    ⟪b i, b j⟫_ℂ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp b.orthonormal i j

omit [CompleteSpace H] [DecidableEq ι] in
lemma norm_basis (b : HilbertBasis ι ℂ H) (i : ι) : ‖b i‖ = 1 := b.orthonormal.1 i

omit [CompleteSpace H] in
lemma diagState_rankOne_mul (b : HilbertBasis ι ℂ H) (p : ι → ℂ) (m n : ι) (B : H →L[ℂ] H) :
    diagState b p (rankOne b m n * B) = p m * ⟪b n, B (b m)⟫_ℂ := by
  unfold diagState
  rw [tsum_eq_single m]
  · simp [rankOne_apply, inner_smul_right, norm_basis]
  · intro k hk
    have : ⟪b k, b m⟫_ℂ = 0 := by rw [inner_basis_basis]; simp [hk]
    simp [rankOne_apply, inner_smul_right, this]

omit [CompleteSpace H] in
lemma diagState_mul_rankOne (b : HilbertBasis ι ℂ H) (p : ι → ℂ) (m n : ι) (B : H →L[ℂ] H) :
    diagState b p (B * rankOne b m n) = p n * ⟪b n, B (b m)⟫_ℂ := by
  unfold diagState
  rw [tsum_eq_single n]
  · simp [rankOne_apply, norm_basis]
  · intro k hk
    have : ⟪b n, b k⟫_ℂ = 0 := by rw [inner_basis_basis]; simp [Ne.symm hk]
    simp [rankOne_apply, this]

/-- **The weight relation of a KMS diagonal state**: if `ω_p` is `(τ, β)`-KMS with `β > 0` for the flow
`τᵗ(A) = e^{itH} A e^{-itH}`, then `pₙ = pₘ e^{-β(λₙ - λₘ)}`. -/
theorem weights_of_isKMSState (b : HilbertBasis ι ℂ H) (ev : ι → ℝ) (p : ι → ℂ) {β : ℝ} (hβ : 0 < β)
    (h : IsKMSState (dyn b ev) (diagState b p) β) (m n : ι) :
    p n = p m * Complex.exp (-(β * (ev n - ev m))) := by
  obtain ⟨F, hFc, hFd, -, hF0, hFβ⟩ := h (rankOne b m n) (rankOne b n m)
  have hBm : ⟪b n, rankOne b n m (b m)⟫_ℂ = 1 := by
    simp [rankOne_apply, norm_basis]
  have hdyn : ∀ t : ℝ, ⟪b n, dyn b ev t (rankOne b n m) (b m)⟫_ℂ =
      Complex.exp (Complex.I * t * (ev n - ev m)) := by
    intro t
    rw [inner_dyn, hBm, mul_one]
  have hF : ∀ t : ℝ, F t = (fun z : ℂ => p m * Complex.exp (Complex.I * z * (ev n - ev m))) t := by
    intro t
    rw [hF0, diagState_rankOne_mul, hdyn]
  have hG : ∀ t : ℝ, F (t + Complex.I * β) = p n * Complex.exp (Complex.I * t * (ev n - ev m)) := by
    intro t
    rw [hFβ, diagState_mul_rankOne, hdyn]
  have hGc : Differentiable ℂ (fun z : ℂ => p m * Complex.exp (Complex.I * z * (ev n - ev m))) := by
    fun_prop
  have heq := eqOn_of_eqOn_real hβ hFc hGc.continuous.continuousOn hFd hGc.differentiableOn hF
    (x := ((0 : ℝ) : ℂ) + Complex.I * β) (by simp [strip, hβ.le])
  have h1 := hG 0
  simp only at heq
  rw [heq] at h1
  have h2 : Complex.I * (((0 : ℝ) : ℂ) + Complex.I * β) * ((ev n : ℂ) - ev m) =
      -((β : ℂ) * ((ev n : ℂ) - ev m)) := by
    push_cast; ring_nf; simp [Complex.I_sq]
  rw [h2] at h1
  simpa using h1.symm

end Lightlike.Rows.G1_053
