import Lightlike.OperatorAlgebras.WeylAlgebra

/-!
# Tests for the CCR algebra

* `IsWeylSystem.mul_twist`: `W(φ) W(ψ) = e^{-iω(φ,ψ)} W(ψ) W(φ)` (Bär-Ginoux-Pfäffle, arXiv:0806.1036, Section 4.2,
  p. 117, the computation in the proof of Proposition 4.2.3 (2)), and `IsWeylSystem.mul_ne_mul`: so `W(φ)` and `W(ψ)` do
  not commute when `e^{-iω(φ,ψ)} ≠ 1`;
* `not_isSymplecticForm_zero`: the zero form on a nonzero space is not symplectic (a wrong input);
* `stdForm`, `isSymplecticForm_stdForm`: the standard form `ω((a, b), (c, d)) = ad - bc` on `ℝ²`;
* `ell2Basis`, `weylOp_ell2Basis_apply`: on `ℓ²(V)` with its standard basis, `weylOp` is the operator
  `(W(φ)F)(ψ) = e^{iω(φ,ψ)/2} F(φ + ψ)` of Example 4.2.2, p. 116;
* `ccrW_mul_ne`: in the CCR algebra of `(ℝ², ω)`, `W(e₁)` and `W(e₂)` do not commute.
-/

namespace Lightlike.OperatorAlgebras

section General

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
  {ω : LinearMap.BilinForm ℝ V} {W : V → A}

/-- **The Weyl relation in commutator form**: `W(φ) W(ψ) = e^{-iω(φ,ψ)} W(ψ) W(φ)`. -/
theorem IsWeylSystem.mul_twist (hω : IsSymplecticForm ω) (hW : IsWeylSystem ω W) (φ ψ : V) :
    W φ * W ψ = Complex.exp (-(Complex.I * ((ω φ ψ : ℝ) : ℂ))) • (W ψ * W φ) := by
  rw [hW.mul φ ψ, hW.mul ψ φ, add_comm ψ φ, smul_smul, ← Complex.exp_add, hω.antisymm ψ φ]
  have : -(Complex.I * ((ω φ ψ / 2 : ℝ) : ℂ)) =
      -(Complex.I * ((ω φ ψ : ℝ) : ℂ)) + -(Complex.I * ((-ω φ ψ / 2 : ℝ) : ℂ)) := by
    push_cast; ring
  rw [this]

/-- **Two Weyl elements with `e^{-iω(φ,ψ)} ≠ 1` do not commute**, in a nonzero algebra. -/
theorem IsWeylSystem.mul_ne_mul [Nontrivial A] (hω : IsSymplecticForm ω) (hW : IsWeylSystem ω W) (φ ψ : V)
    (h : Complex.exp (-(Complex.I * ((ω φ ψ : ℝ) : ℂ))) ≠ 1) : W φ * W ψ ≠ W ψ * W φ := by
  intro heq
  set c := Complex.exp (-(Complex.I * ((ω φ ψ : ℝ) : ℂ)))
  have hu : W φ * W ψ ∈ unitary A := mul_mem (hW.mem_unitary hω φ) (hW.mem_unitary hω ψ)
  have htw := hW.mul_twist hω φ ψ
  rw [← heq] at htw
  have hne : (1 - c) ≠ 0 := sub_ne_zero.mpr h.symm
  have h1 : (1 - c) • (W φ * W ψ) = 0 := by
    rw [sub_smul, one_smul, ← htw, sub_self]
  have h0 : W φ * W ψ = 0 := by
    have := congrArg (fun x => (1 - c)⁻¹ • x) h1
    simpa [smul_smul, inv_mul_cancel₀ hne] using this
  have := Unitary.star_mul_self_of_mem hu
  rw [h0, mul_zero] at this
  exact zero_ne_one this

/-- **The zero form on a nonzero space is not symplectic** (a wrong input: it is degenerate). -/
theorem not_isSymplecticForm_zero [Nontrivial V] : ¬ IsSymplecticForm (0 : LinearMap.BilinForm ℝ V) := by
  intro h
  obtain ⟨φ, hφ⟩ := exists_ne (0 : V)
  exact hφ (h.nondeg φ fun ψ => rfl)

end General

/-- The standard symplectic form `ω((a, b), (c, d)) = ad - bc` on `ℝ²`. -/
noncomputable def stdForm : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => x.1 * y.2 - x.2 * y.1)
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

lemma stdForm_apply (x y : ℝ × ℝ) : stdForm x y = x.1 * y.2 - x.2 * y.1 := rfl

/-- **The standard form on `ℝ²` is symplectic.** -/
theorem isSymplecticForm_stdForm : IsSymplecticForm stdForm where
  antisymm φ ψ := by rw [stdForm_apply, stdForm_apply]; ring
  nondeg φ h := by
    have h1 : φ.1 = 0 := by simpa [stdForm_apply] using h (0, 1)
    have h2 : φ.2 = 0 := by simpa [stdForm_apply] using h (1, 0)
    exact Prod.ext h1 h2

/-- The standard Hilbert basis of `ℓ²(V)`. -/
noncomputable def ell2Basis (V : Type*) : HilbertBasis V ℂ (lp (fun _ : V => ℂ) 2) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- **On `ℓ²(V)` with its standard basis, `weylOp` is the operator of Example 4.2.2**:
`(W(φ)F)(ψ) = e^{iω(φ,ψ)/2} F(φ + ψ)`. -/
theorem weylOp_ell2Basis_apply {V : Type*} [AddCommGroup V] [Module ℝ V] (ω : LinearMap.BilinForm ℝ V) (φ : V)
    (F : lp (fun _ : V => ℂ) 2) (ψ : V) :
    weylOp ω (ell2Basis V) φ F ψ = Complex.exp (Complex.I * ((ω φ ψ / 2 : ℝ) : ℂ)) * F (φ + ψ) := by
  have h := repr_weylOp (ω := ω) (ell2Basis V) φ F
  exact congrArg (fun G : lp (fun _ : V => ℂ) 2 => G ψ) h

/-- The CCR algebra of a nonempty index set is a nonzero algebra. -/
lemma nontrivial_ccrAlgebra {V : Type*} [AddCommGroup V] [Module ℝ V] (ω : LinearMap.BilinForm ℝ V)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (B : HilbertBasis V ℂ H) :
    Nontrivial (ccrAlgebra ω B) := by
  refine nontrivial_of_ne 1 0 fun h => ?_
  have h1 : ((1 : ccrAlgebra ω B) : H →L[ℂ] H) (B 0) = ((0 : ccrAlgebra ω B) : H →L[ℂ] H) (B 0) := by rw [h]
  simp only [OneMemClass.coe_one, ZeroMemClass.coe_zero, one_apply_eq_self,
    zero_apply] at h1
  exact B.orthonormal.ne_zero 0 h1

/-- **The CCR algebra of `(ℝ², ω)` is not commutative**: `W(e₁) W(e₂) ≠ W(e₂) W(e₁)`, since `ω(e₁, e₂) = 1` and
`e^{-i} ≠ 1`. -/
theorem ccrW_mul_ne :
    ccrW stdForm (ell2Basis (ℝ × ℝ)) (1, 0) * ccrW stdForm (ell2Basis (ℝ × ℝ)) (0, 1) ≠
      ccrW stdForm (ell2Basis (ℝ × ℝ)) (0, 1) * ccrW stdForm (ell2Basis (ℝ × ℝ)) (1, 0) := by
  have := nontrivial_ccrAlgebra stdForm (ell2Basis (ℝ × ℝ))
  refine (isWeylSystem_ccrW (ell2Basis (ℝ × ℝ)) isSymplecticForm_stdForm).mul_ne_mul isSymplecticForm_stdForm _ _ ?_
  rw [stdForm_apply]
  norm_num
  intro h
  have := Complex.exp_eq_one_iff.mp h
  obtain ⟨n, hn⟩ := this
  have him := congrArg Complex.im hn
  simp at him
  have hpi : (n : ℝ) * (2 * Real.pi) = -1 := by linarith
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn0
    nlinarith [Real.two_le_pi]
  · subst hn0; simp at hpi
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    nlinarith [Real.two_le_pi]

end Lightlike.OperatorAlgebras
