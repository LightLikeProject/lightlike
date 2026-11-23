import Lightlike.OperatorAlgebras.QuasiFreeState.Covariance
import Lightlike.OperatorAlgebras.GramUnitary
import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# The GNS representation of a quasi-free state

For a symplectic (antisymmetric) form `ω` and a covariance `η` the Gram kernel `qfKer ω η` is positive semidefinite
(`posSemidef_qfKer`). Its reproducing kernel Hilbert space `QFSpace ω η` (Mathlib: `RKHS.OfKernel`) carries the Weyl
unitaries `qfW φ`, `qfW φ (k_ψ) = exp(-i ω(φ, ψ)/2) k_{ψ+φ}`, obtained from the shift invariance of the kernel
(`qfKer_shift`) by `exists_unitary_of_gram_eq`; they satisfy the Weyl relations (`qfWeylSystem`) and the vacuum `k_0`
is cyclic with `⟨k_0, W(φ) k_0⟩ = exp(-¼ η(φ, φ))` (`inner_vac_qfW`). This is the GNS construction of the quasi-free
state (Bratteli-Robinson 2, Chapter 5; the construction mirrors `fockRepOf`).

The space is built from a `Fact (qfKerM ω η).PosSemidef` instance; `qfFact` produces it from a covariance.
-/

open scoped InnerProductSpace ComplexOrder ComplexConjugate Matrix

universe u

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Lightlike.OperatorAlgebras

variable {V : Type u} [AddCommGroup V] [Module ℝ V] (ω η : LinearMap.BilinForm ℝ V)

/-- The Gram kernel as a matrix with entries in `ℂ →L[ℂ] ℂ`, for Mathlib's reproducing kernel Hilbert spaces. -/
noncomputable def qfKerM : Matrix V V (ℂ →L[ℂ] ℂ) :=
  Matrix.of fun f g => qfKer ω η f g • ContinuousLinearMap.id ℂ ℂ

lemma qfKer_conj (hω : ∀ a b, ω a b = -ω b a) (f g : V) :
    qfKer ω η g f = (starRingEnd ℂ) (qfKer ω η f g) := by
  have h1 : η (f - g) (f - g) = η (g - f) (g - f) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  unfold qfKer
  simp only [Matrix.of_apply, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
  rw [h1, hω g f]
  push_cast
  ring_nf

theorem posSemidef_qfKerM (hω : ∀ a b, ω a b = -ω b a) (hη : IsCovariance ω η) :
    (qfKerM ω η).PosSemidef := by
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  refine ⟨?_, fun vv => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, qfKerM, Matrix.of_apply, star_smul]
    have hs : star (ContinuousLinearMap.id ℂ ℂ) = ContinuousLinearMap.id ℂ ℂ :=
      star_one (ℂ →L[ℂ] ℂ)
    simp only [hs, RCLike.star_def]
    rw [← qfKer_conj ω η hω j i]
  · have hq := (posSemidef_qfKer hω hη).2 vv
    have : (vv.sum fun x w => vv.sum fun x' w' => ⟪qfKerM ω η x' x w, w'⟫_ℂ) =
        vv.sum fun i a => vv.sum fun j b => star a * qfKer ω η i j * b := by
      refine Finsupp.sum_congr fun x _ => Finsupp.sum_congr fun x' _ => ?_
      simp only [qfKerM, Matrix.of_apply, smul_apply,
        ContinuousLinearMap.id_apply, RCLike.inner_apply, smul_eq_mul, map_mul, RCLike.star_def]
      rw [qfKer_conj ω η hω x x']
      simp only [starRingEnd_self_apply]
      ring
    rw [this]
    exact (Complex.nonneg_iff.1 hq).1

/-- The `Fact` instance for the reproducing kernel Hilbert space of a quasi-free state. -/
theorem qfFact (hω : ∀ a b, ω a b = -ω b a) (hη : IsCovariance ω η) : Fact (qfKerM ω η).PosSemidef :=
  ⟨posSemidef_qfKerM ω η hω hη⟩

section Space

variable [Fact (qfKerM ω η).PosSemidef]

/-- **The GNS space of the quasi-free state**: the reproducing kernel Hilbert space of `qfKerM`. -/
abbrev QFSpace : Type u := RKHS.OfKernel (qfKerM ω η)

/-- The kernel vector `k_φ`, `W(φ) Ω` in the GNS representation. -/
noncomputable def kq (f : V) : QFSpace ω η := RKHS.kerFun (QFSpace ω η) f (1 : ℂ)

lemma inner_kq (hω : ∀ a b, ω a b = -ω b a) (f g : V) : ⟪kq ω η f, kq ω η g⟫_ℂ = qfKer ω η f g := by
  have := RKHS.kernel_inner (QFSpace ω η) g f 1 1
  rw [RKHS.OfKernel.kernel_ofKernel] at this
  simp only [qfKerM, Matrix.of_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, RCLike.inner_apply, mul_one, one_mul] at this
  have h2 : ⟪kq ω η f, kq ω η g⟫_ℂ = (starRingEnd ℂ) (qfKer ω η g f) := by
    rw [kq, kq]; exact this.symm
  rw [h2, ← qfKer_conj ω η hω]

/-- The Weyl phase `exp(-i ω(g, f)/2)`. -/
noncomputable def qfPhase (g f : V) : ℂ := Complex.exp (-(Complex.I * ((ω g f / 2 : ℝ) : ℂ)))

lemma qfPhase_ne_zero (g f : V) : qfPhase ω g f ≠ 0 := Complex.exp_ne_zero _

lemma qfPhase_cocycle (f g x : V) :
    qfPhase ω g x * qfPhase ω f (x + g) =
      Complex.exp (-(Complex.I * ((ω f g / 2 : ℝ) : ℂ))) * qfPhase ω (f + g) x := by
  unfold qfPhase
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_add, LinearMap.add_apply]
  push_cast
  ring

omit [Fact (qfKerM ω η).PosSemidef] in
/-- **The Gram matrix is invariant under the Weyl shift.** -/
lemma qfKer_shift (hω : ∀ a b, ω a b = -ω b a) (g f f' : V) :
    (starRingEnd ℂ) (qfPhase ω g f) * qfPhase ω g f' * qfKer ω η (f + g) (f' + g) = qfKer ω η f f' := by
  have hgg : ω g g = 0 := by have := hω g g; linarith
  have hd : f' + g - (f + g) = f' - f := by abel
  have e : ω (f + g) (f' + g) = ω f f' + ω f g + ω g f' := by
    simp only [map_add, LinearMap.add_apply, hgg]; ring
  have h2 : ((ω g f : ℝ) : ℂ) = -((ω f g : ℝ) : ℂ) := by rw [hω g f]; push_cast; ring
  simp only [qfKer, Matrix.of_apply, qfPhase, hd, e]
  rw [← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  have key : Complex.exp (-(-Complex.I * ((ω g f / 2 : ℝ) : ℂ))) *
      Complex.exp (-(Complex.I * ((ω g f' / 2 : ℝ) : ℂ))) *
      Complex.exp (Complex.I * (((ω f f' + ω f g + ω g f') / 2 : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((ω f f' / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast at h2 ⊢
    linear_combination (Complex.I / 2) * h2
  rw [← key]
  ring

/-- The linear map `c ↦ ∑ c f • k_f` from finitely supported coefficients to the GNS space. -/
noncomputable def qfPhi : (V →₀ ℂ) →ₗ[ℂ] QFSpace ω η := Finsupp.linearCombination ℂ (kq ω η)

lemma qfPhi_single (f : V) : qfPhi ω η (Finsupp.single f 1) = kq ω η f := by
  simp [qfPhi]

/-- The kernel vectors span a dense subspace of the GNS space. -/
lemma dense_range_qfPhi :
    Dense ((LinearMap.range (qfPhi ω η) : Submodule ℂ (QFSpace ω η)) : Set (QFSpace ω η)) := by
  have hd := RKHS.kerFun_dense (QFSpace ω η)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  refine eq_top_iff.2 (hd ▸ Submodule.topologicalClosure_mono ?_)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, v, rfl⟩
  have : RKHS.kerFun (QFSpace ω η) x v = v • kq ω η x := by
    rw [kq, ← map_smul]; simp
  rw [this]
  exact Submodule.smul_mem _ _ ⟨Finsupp.single x 1, qfPhi_single ω η x⟩

/-- The Weyl shift on finitely supported coefficients: `e_f ↦ exp(-i ω(g, f)/2) e_{f+g}`. -/
noncomputable def qfTau (g : V) : (V →₀ ℂ) →ₗ[ℂ] (V →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun f => qfPhase ω g f • Finsupp.single (f + g) (1 : ℂ)

lemma qfTau_single (g f : V) :
    qfTau ω g (Finsupp.single f 1) = qfPhase ω g f • Finsupp.single (f + g) (1 : ℂ) := by
  simp [qfTau]

lemma qfPhi_tau_single (g f : V) :
    qfPhi ω η (qfTau ω g (Finsupp.single f 1)) = qfPhase ω g f • kq ω η (f + g) := by
  rw [qfTau_single, map_smul, qfPhi_single]

lemma dense_range_qfPhi_tau (g : V) :
    Dense ((LinearMap.range ((qfPhi ω η).comp (qfTau ω g)) : Submodule ℂ (QFSpace ω η)) :
      Set (QFSpace ω η)) := by
  refine (dense_range_qfPhi ω η).mono ?_
  have hsub : LinearMap.range (qfPhi ω η) ≤ LinearMap.range ((qfPhi ω η).comp (qfTau ω g)) := by
    have hr : LinearMap.range (qfPhi ω η) = Submodule.span ℂ (Set.range (kq ω η)) :=
      Finsupp.range_linearCombination _
    rw [hr, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    refine ⟨(qfPhase ω g (x - g))⁻¹ • Finsupp.single (x - g) (1 : ℂ), ?_⟩
    simp only [LinearMap.comp_apply, map_smul, qfTau_single, qfPhi_single, smul_smul, sub_add_cancel]
    rw [inv_mul_cancel₀ (qfPhase_ne_zero ω g _), one_smul]
  exact fun x hx => hsub hx

/-- **The Weyl unitary** `W g` of the GNS space: `W g k_f = exp(-i ω(g, f)/2) k_{f+g}`. -/
theorem exists_qfWeyl (hω : ∀ a b, ω a b = -ω b a) (g : V) :
    ∃ U : QFSpace ω η ≃ₗᵢ[ℂ] QFSpace ω η, ∀ c, U (qfPhi ω η c) = qfPhi ω η (qfTau ω g c) := by
  refine exists_unitary_of_gram_eq (Φ₁ := qfPhi ω η) (Φ₂ := (qfPhi ω η).comp (qfTau ω g)) ?_
    (dense_range_qfPhi ω η) (dense_range_qfPhi_tau ω η g)
  intro f f'
  simp only [LinearMap.comp_apply, qfPhi_single, qfPhi_tau_single, inner_smul_left,
    inner_smul_right, inner_kq ω η hω]
  rw [← qfKer_shift ω η hω g f f']
  ring

/-- The Weyl unitary of `g` (a choice). -/
noncomputable def qfW (hω : ∀ a b, ω a b = -ω b a) (g : V) : QFSpace ω η ≃ₗᵢ[ℂ] QFSpace ω η :=
  Classical.choose (exists_qfWeyl ω η hω g)

lemma qfW_phi (hω : ∀ a b, ω a b = -ω b a) (g : V) (c : V →₀ ℂ) :
    qfW ω η hω g (qfPhi ω η c) = qfPhi ω η (qfTau ω g c) :=
  Classical.choose_spec (exists_qfWeyl ω η hω g) c

lemma qfW_kq (hω : ∀ a b, ω a b = -ω b a) (g f : V) :
    qfW ω η hω g (kq ω η f) = qfPhase ω g f • kq ω η (f + g) := by
  rw [← qfPhi_single, qfW_phi, qfPhi_tau_single]

omit [Fact (qfKerM ω η).PosSemidef] in
lemma qfPhase_zero_left (f : V) : qfPhase ω 0 f = 1 := by simp [qfPhase]

omit [Fact (qfKerM ω η).PosSemidef] in
lemma qfPhase_zero_right (g : V) : qfPhase ω g 0 = 1 := by simp [qfPhase]

omit [Fact (qfKerM ω η).PosSemidef] in
lemma qfTau_zero : qfTau ω (0 : V) = LinearMap.id := by
  refine Finsupp.lhom_ext fun f a => ?_
  rw [← Finsupp.smul_single_one, map_smul, qfTau_single, qfPhase_zero_left]
  simp

omit [Fact (qfKerM ω η).PosSemidef] in
lemma qfTau_comp (f g : V) :
    (qfTau ω f).comp (qfTau ω g) =
      Complex.exp (-(Complex.I * ((ω f g / 2 : ℝ) : ℂ))) • qfTau ω (f + g) := by
  refine Finsupp.lhom_ext fun x a => ?_
  rw [← Finsupp.smul_single_one]
  simp only [LinearMap.comp_apply, map_smul, qfTau_single, LinearMap.smul_apply]
  simp only [smul_smul]
  rw [qfPhase_cocycle ω f g x, show x + (f + g) = x + g + f by abel]

lemma qfW_zero (hω : ∀ a b, ω a b = -ω b a) :
    qfW ω η hω (0 : V) = LinearIsometryEquiv.refl ℂ (QFSpace ω η) := by
  refine LinearIsometryEquiv.ext fun ψ => ?_
  have hc1 : Continuous fun x : QFSpace ω η => qfW ω η hω (0 : V) x := (qfW ω η hω 0).continuous
  have := Continuous.ext_on (dense_range_qfPhi ω η) hc1 continuous_id (fun x hx => by
    obtain ⟨c, rfl⟩ := hx
    simp only [qfW_phi, qfTau_zero, LinearMap.id_apply, id_eq])
  exact congrFun this ψ

lemma qfW_weyl (hω : ∀ a b, ω a b = -ω b a) (f g : V) (ψ : QFSpace ω η) :
    qfW ω η hω f (qfW ω η hω g ψ) =
      Complex.exp (-(Complex.I * ((ω f g / 2 : ℝ) : ℂ))) • qfW ω η hω (f + g) ψ := by
  have hc1 : Continuous fun x : QFSpace ω η => qfW ω η hω f (qfW ω η hω g x) :=
    (qfW ω η hω f).continuous.comp (qfW ω η hω g).continuous
  have hc2 : Continuous fun x : QFSpace ω η =>
      Complex.exp (-(Complex.I * ((ω f g / 2 : ℝ) : ℂ))) • qfW ω η hω (f + g) x :=
    (qfW ω η hω (f + g)).continuous.const_smul
      (Complex.exp (-(Complex.I * ((ω f g / 2 : ℝ) : ℂ))))
  have := Continuous.ext_on (dense_range_qfPhi ω η) hc1 hc2 (fun x hx => by
    obtain ⟨c, rfl⟩ := hx
    have h1 : qfTau ω f (qfTau ω g c) =
        Complex.exp (-(Complex.I * ((ω f g / 2 : ℝ) : ℂ))) • qfTau ω (f + g) c := by
      have := congrArg (fun L => L c) (qfTau_comp ω f g)
      simpa using this
    simp only [qfW_phi, map_smul, h1])
  exact congrFun this ψ

/-- The vacuum vector `Ω = k_0` of the GNS representation. -/
noncomputable def qfVac : QFSpace ω η := kq ω η 0

lemma qfW_vac (hω : ∀ a b, ω a b = -ω b a) (f : V) : qfW ω η hω f (qfVac ω η) = kq ω η f := by
  rw [qfVac, qfW_kq, qfPhase_zero_right, one_smul, zero_add]

/-- **The vacuum expectation of the Weyl unitaries**: `⟨Ω, W(φ) Ω⟩ = exp(-¼ η(φ, φ))`. -/
theorem inner_vac_qfW (hω : ∀ a b, ω a b = -ω b a) (f : V) :
    ⟪qfVac ω η, qfW ω η hω f (qfVac ω η)⟫_ℂ = ((gaussVal η f : ℝ) : ℂ) := by
  rw [qfW_vac, qfVac, inner_kq ω η hω]
  simp [qfKer, gaussVal]

/-- **The Weyl unitaries of the GNS space form a Weyl system** of `(V, ω)` in the C*-algebra `B(K)`. -/
theorem qfWeylSystem (hω : ∀ a b, ω a b = -ω b a) :
    IsWeylSystem ω (fun φ : V => ((qfW ω η hω φ : QFSpace ω η ≃ₗᵢ[ℂ] QFSpace ω η) :
      QFSpace ω η →L[ℂ] QFSpace ω η)) where
  map_zero := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [qfW_zero]
  map_neg φ := by
    rw [LinearIsometryEquiv.star_eq_symm]
    refine ContinuousLinearMap.ext fun x => ?_
    show qfW ω η hω (-φ) x = (qfW ω η hω φ).symm x
    symm
    rw [LinearIsometryEquiv.symm_apply_eq, qfW_weyl, add_neg_cancel, qfW_zero]
    have h1 : ω φ (-φ) = 0 := by
      rw [map_neg]
      have := hω φ φ
      linarith
    simp [h1]
  mul φ ψ := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [qfW_weyl]

/-- **Cyclicity**: the vectors `W(φ) Ω = k_φ` span a dense subspace of the GNS space. -/
theorem qfVac_cyclic (hω : ∀ a b, ω a b = -ω b a) :
    Dense ((Submodule.span ℂ (Set.range fun φ : V => qfW ω η hω φ (qfVac ω η)) :
      Submodule ℂ (QFSpace ω η)) : Set (QFSpace ω η)) := by
  have hr : LinearMap.range (qfPhi ω η) = Submodule.span ℂ (Set.range (kq ω η)) :=
    Finsupp.range_linearCombination _
  simpa [qfW_vac, ← hr] using dense_range_qfPhi ω η

end Space

end Lightlike.OperatorAlgebras.QuasiFreeState
