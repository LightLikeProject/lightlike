import Lightlike.OperatorAlgebras.CARShaleK
import Lightlike.OperatorAlgebras.CARShaleConj
import Lightlike.OperatorAlgebras.TraceClass.HilbertSchmidt
import Lightlike.OperatorAlgebras.Spectral.HilbertSchmidtCompact
import Lightlike.OperatorAlgebras.Spectral.Compact

/-!
# The Hilbert-Schmidt condition on the antilinear part is basis independent

For a Hilbert basis `c` of `Z`, `T = β ∘ C_c` is a bounded complex-linear operator with `‖T cᵢ‖ = ‖β cᵢ‖`. The basis
independence of the Hilbert-Schmidt square sum for linear operators (`TraceClass.HilbertSchmidt`) transfers to `β`.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.OperatorAlgebras.CARShale

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z] (R : Z →ₗ[ℝ] Z)
  (hR : ∀ w w', (⟪R w, R w'⟫_ℂ).re = (⟪w, w'⟫_ℂ).re)

/-- `β` is conjugate-linear. -/
lemma betaPart_smul (a : ℂ) (v : Z) : betaPart R (a • v) = conj a • betaPart R v := by
  have h2 : Complex.I • (a • v) = (Complex.I * a) • v := smul_smul _ _ _
  simp only [betaPart]
  rw [h2, R_smul R a v, R_smul R (Complex.I * a) v]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
  have hc : starRingEnd ℂ a = (a.re : ℂ) - a.im * Complex.I := by apply Complex.ext <;> simp
  rw [hc]
  simp only [Complex.coe_smul, smul_add, smul_smul]
  linear_combination (norm := (match_scalars <;> (simp only [Complex.coe_algebraMap]; push_cast; ring_nf; try simp only [Complex.I_sq]; try ring)))

include hR in
/-- `β` is bounded by `1`. -/
lemma norm_betaPart_le (v : Z) : ‖betaPart R v‖ ≤ ‖v‖ := by
  unfold betaPart
  rw [norm_smul]
  have h1 : ‖R v + Complex.I • R (Complex.I • v)‖ ≤ ‖v‖ + ‖v‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul, norm_R R hR, norm_R R hR, norm_smul, Complex.norm_I, one_mul]
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]; linarith

section Indep

variable {κ κ' : Type*} (c : HilbertBasis κ ℂ Z) (e : HilbertBasis κ' ℂ Z)

/-- The conjugate of a Hilbert basis in the conjugation of another. -/
noncomputable def conjBasis : HilbertBasis κ' ℂ Z :=
  HilbertBasis.mkOfOrthogonalEqBot (v := fun k => conjC c (e k))
    (by
      classical
      rw [orthonormal_iff_ite]
      intro i j
      rw [inner_conjC, orthonormal_iff_ite.1 e.orthonormal i j]
      split_ifs <;> simp)
    (by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have h : ∀ k, ⟪conjC c (e k), x⟫_ℂ = 0 := fun k =>
        (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span ⟨k, rfl⟩)
      have h2 : ∀ k, e.repr (conjC c x) k = 0 := fun k => by
        rw [HilbertBasis.repr_apply_apply]
        have := inner_conjC c (conjC c (e k)) x
        rw [conjC_conjC] at this
        rw [this, h k, map_zero]
      have h3 : e.repr (conjC c x) = 0 := by ext k; exact h2 k
      have h4 : conjC c x = 0 := by simpa using h3
      have h0 : conjC c 0 = 0 := by simpa using conjC_smul c 0 0
      rw [← conjC_conjC c x, h4, h0])

/-- Auxiliary lemma `conjBasis_apply` for the fermionic Shale theorem. -/
lemma conjBasis_apply (k : κ') : conjBasis c e k = conjC c (e k) := by
  simp [conjBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

end Indep

omit [CompleteSpace Z] in
/-- Auxiliary lemma `betaPart_add` for the fermionic Shale theorem. -/
lemma betaPart_add (u v : Z) : betaPart R (u + v) = betaPart R u + betaPart R v := by
  have h1 : Complex.I • (u + v) = Complex.I • u + Complex.I • v := smul_add _ _ _
  simp only [betaPart, h1, map_add, smul_add]
  module

section Conj

variable {κ : Type*} (c : HilbertBasis κ ℂ Z)

include hR in
/-- `β ∘ C_c` as a bounded complex-linear operator. -/
noncomputable def betaConj : Z →L[ℂ] Z :=
  LinearMap.mkContinuous
    { toFun := fun v => betaPart R (conjC c v)
      map_add' := fun u v => by rw [conjC_add, betaPart_add]
      map_smul' := fun a v => by
        rw [conjC_smul, betaPart_smul, Complex.conj_conj]
        rfl } 1
    (fun v => by
      show ‖betaPart R (conjC c v)‖ ≤ 1 * ‖v‖
      rw [one_mul]
      exact (norm_betaPart_le R hR _).trans (norm_conjC c v).le)

include hR in
/-- Auxiliary lemma `betaConj_apply` for the fermionic Shale theorem. -/
lemma betaConj_apply (v : Z) : betaConj R hR c v = betaPart R (conjC c v) := rfl

end Conj

include hR in
/-- **The Hilbert-Schmidt square sum of `β` is basis independent**: if `∑ ‖β cᵢ‖²` converges in one Hilbert basis `c` then
in any Hilbert basis `e` the sum `∑ ‖β eⱼ‖²` converges to the same value. -/
theorem hasSum_beta_sq {w w' : Set Z} (c : HilbertBasis w ℂ Z) (e : HilbertBasis w' ℂ Z)
    (hc : Summable fun i : w => ‖betaPart R (c i)‖ ^ 2) :
    HasSum (fun j : w' => ‖betaPart R (e j)‖ ^ 2) (∑' i : w, ‖betaPart R (c i)‖ ^ 2) := by
  have h1 : ∀ i : w, betaConj R hR c (c i) = betaPart R (c i) := fun i => by
    rw [betaConj_apply, conjC_basis]
  have hb : Summable fun i : w => ‖betaConj R hR c (c i)‖ ^ 2 := by
    simpa only [h1] using hc
  have := TraceClass.HilbertSchmidt.hasSum_norm_sq_apply_of_basis c (conjBasis c e) hb
  simp only [conjBasis_apply, betaConj_apply, conjC_conjC, h1] at this
  simpa only [h1] using this

variable (hRs : Function.Surjective R)

include hR hRs in
/-- `‖K v‖ ≤ ‖β v‖`. -/
lemma norm_KL_le_beta (v : Z) : ‖KL R hR hRs v‖ ≤ ‖betaPart R v‖ := by
  have h := inner_beta_beta R hR hRs (KL R hR hRs v) v
  have h2 : ‖KL R hR hRs v‖ ^ 2 ≤ ‖KL R hR hRs v‖ * ‖betaPart R v‖ := by
    have h3 : ⟪KL R hR hRs v, KL R hR hRs v⟫_ℂ = ⟪betaPart R (KL R hR hRs v), betaPart R v⟫_ℂ := h.symm
    have h4 := congrArg RCLike.re h3
    rw [inner_self_eq_norm_sq] at h4
    calc ‖KL R hR hRs v‖ ^ 2 = RCLike.re ⟪betaPart R (KL R hR hRs v), betaPart R v⟫_ℂ := by simpa using h4
      _ ≤ ‖⟪betaPart R (KL R hR hRs v), betaPart R v⟫_ℂ‖ := RCLike.re_le_norm _
      _ ≤ ‖betaPart R (KL R hR hRs v)‖ * ‖betaPart R v‖ := norm_inner_le_norm _ _
      _ ≤ ‖KL R hR hRs v‖ * ‖betaPart R v‖ := by
          gcongr; exact norm_betaPart_le R hR _
  by_cases h0 : ‖KL R hR hRs v‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hp : 0 < ‖KL R hR hRs v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

include hR hRs in
/-- **An eigenbasis of `K = β*β` for a Hilbert-Schmidt `β`**: a Hilbert basis `e` of eigenvectors, `K eₖ = μₖ eₖ`, with
`μₖ = ‖β eₖ‖²` summable. -/
theorem exists_eigenbasis (hHS : ∃ (w : Set Z) (c : HilbertBasis w ℂ Z), Summable fun i : w => ‖betaPart R (c i)‖ ^ 2) :
    ∃ (s : Set Z) (e : HilbertBasis s ℂ Z) (μ : s → ℝ) (h : ℝ), (∀ k, KL R hR hRs (e k) = (μ k : ℂ) • e k) ∧
      (∀ k, ‖betaPart R (e k)‖ ^ 2 = μ k) ∧ HasSum μ h := by
  obtain ⟨w, c, hc⟩ := hHS
  have hK : TraceClass.HilbertSchmidt.IsHilbertSchmidt (KL R hR hRs) := by
    refine ⟨w, c, ?_⟩
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hc
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_KL_le_beta R hR hRs _) 2
  have hcomp := CompactSpectral.isCompactOperator_of_isHilbertSchmidt hK
  have hsym : ((KL R hR hRs : Z →L[ℂ] Z) : Z →ₗ[ℂ] Z).IsSymmetric := fun u v => by
    show ⟪KL R hR hRs u, v⟫_ℂ = ⟪u, KL R hR hRs v⟫_ℂ
    exact inner_Kc R hR hRs u v
  obtain ⟨s, e, μ, he, hμ⟩ := CompactSpectral.exists_hilbertBasis_eigenvectors hcomp hsym
  have hnorm : ∀ k, ‖betaPart R (e k)‖ ^ 2 = μ k := fun k => by
    have h1 := inner_beta_beta R hR hRs (e k) (e k)
    rw [hμ k, inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      e.orthonormal.1 k] at h1
    have h2 : ((‖betaPart R (e k)‖ : ℂ)) ^ 2 = (μ k : ℂ) := by
      simpa using h1
    exact_mod_cast h2
  have hsum := hasSum_beta_sq R hR c e hc
  refine ⟨s, e, μ, ∑' i : w, ‖betaPart R (c i)‖ ^ 2, hμ, hnorm, ?_⟩
  simpa only [hnorm] using hsum

end Lightlike.OperatorAlgebras.CARShale
