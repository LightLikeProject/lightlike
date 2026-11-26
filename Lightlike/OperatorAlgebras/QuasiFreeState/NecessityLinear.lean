import Lightlike.OperatorAlgebras.QuasiFreeState.ComplexStructure

/-!
# Necessity of the complex structure: the linear-algebra half

A covariance `η` of a symplectic space `(V, ω)` (finite-dimensional, `ω` nondegenerate) is positive definite, and the
operator `T = η⁻¹ ω` (`η(T x, y) = ω(x, y)`) is `η`-skew with `η`-norm `≤ 1` (that is the covariance inequality). If
`T² = -1` then `T` is a compatible complex structure (`compatible_of_sq`). Otherwise a spectral vector of `-T²` with
eigenvalue `λ² < 1` gives a nonzero functional `ρ = η(u, ·)` and `ε = 1 - λ²` such that `η - ε ρ²` is still a covariance
(`exists_sub_covariance`): the quasi-free state of `η` is then a Gaussian mixture of translates of a quasi-free state, the
other half of the necessity proof.
-/

open scoped InnerProductSpace

universe u

namespace Lightlike.OperatorAlgebras.QuasiFreeState

variable {V : Type u} [AddCommGroup V] [Module ℝ V] {ω η : LinearMap.BilinForm ℝ V}

/-- **A covariance of a nondegenerate `ω` is positive definite.** -/
lemma IsCovariance.pos_def (hη : IsCovariance ω η) (hnd : ∀ x, (∀ y, ω x y = 0) → x = 0) {x : V} (hx : x ≠ 0) :
    0 < η x x := by
  rcases (hη.nonneg x).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    apply hnd
    intro y
    have := hη.sq_le x y
    rw [← h, zero_mul] at this
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg _))

end Lightlike.OperatorAlgebras.QuasiFreeState

namespace Lightlike.OperatorAlgebras.QuasiFreeState

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- `η` is a positive definite symmetric bilinear form. -/
class IsPosDefForm (η : LinearMap.BilinForm ℝ V) : Prop where
  symm : ∀ x y, η x y = η y x
  pos : ∀ x, x ≠ 0 → 0 < η x x

/-- The vector space `V` with the inner product `η`. -/
def WithEta (_η : LinearMap.BilinForm ℝ V) : Type u := V

namespace WithEta

variable {η : LinearMap.BilinForm ℝ V}

/-- The additive group of `V`. -/
instance : AddCommGroup (WithEta η) := inferInstanceAs (AddCommGroup V)
/-- The real vector space structure of `V`. -/
instance : Module ℝ (WithEta η) := inferInstanceAs (Module ℝ V)

/-- `WithEta η` is finite-dimensional. -/
instance [FiniteDimensional ℝ V] : FiniteDimensional ℝ (WithEta η) := inferInstanceAs (FiniteDimensional ℝ V)

/-- Wrap an element of `V`. -/
def mk (x : V) : WithEta η := x

/-- Unwrap. -/
def unmk (x : WithEta η) : V := x

variable [IsPosDefForm η]

/-- The inner product core of `η`. -/
def core : InnerProductSpace.Core ℝ (WithEta η) where
  inner x y := η (unmk x) (unmk y)
  conj_inner_symm x y := by
    show (starRingEnd ℝ) (η (unmk y) (unmk x)) = η (unmk x) (unmk y)
    simp [IsPosDefForm.symm (η := η) (unmk y) (unmk x)]
  re_inner_nonneg x := by
    show 0 ≤ η (unmk x) (unmk x)
    by_cases h : unmk x = 0
    · rw [h]; simp
    · exact (IsPosDefForm.pos (η := η) (unmk x) h).le
  add_left x y z := by
    show η (unmk (x + y)) (unmk z) = η (unmk x) (unmk z) + η (unmk y) (unmk z)
    have h : ∀ x' y' z' : V, η (x' + y') z' = η x' z' + η y' z' := fun x' y' z' => by simp
    exact h x y z
  smul_left x y r := by
    show η (unmk (r • x)) (unmk y) = (starRingEnd ℝ) r * η (unmk x) (unmk y)
    have h : ∀ x' y' : V, η (r • x') y' = r * η x' y' := fun x' y' => by simp
    exact h x y
  definite x hx := by
    by_contra h
    exact absurd hx (IsPosDefForm.pos (η := η) (unmk x) h).ne'

/-- The norm of `η`. -/
noncomputable instance : NormedAddCommGroup (WithEta η) := (core (η := η)).toNormedAddCommGroup

/-- The inner product `η`. -/
noncomputable instance : InnerProductSpace ℝ (WithEta η) := InnerProductSpace.ofCore (core (η := η)).toCore

/-- The inner product is `η`. -/
lemma inner_eq (x y : WithEta η) : ⟪x, y⟫_ℝ = η x y := rfl

end WithEta

section Riesz

variable [FiniteDimensional ℝ V] {ω η : LinearMap.BilinForm ℝ V} [IsPosDefForm η]

/-- The `η`-Riesz operator of `ω`: `⟪T x, y⟫ = ω x y`. -/
lemma exists_riesz (ω : LinearMap.BilinForm ℝ V) :
    ∃ T : WithEta η →ₗ[ℝ] WithEta η, ∀ x y : WithEta η, ⟪T x, y⟫_ℝ = ω (WithEta.unmk x) (WithEta.unmk y) := by
  let L : WithEta η →ₗ[ℝ] (WithEta η →L[ℝ] ℝ) :=
    { toFun := fun x => LinearMap.toContinuousLinearMap (ω (WithEta.unmk x))
      map_add' := fun x y => by
        ext z
        have h1 : ∀ a b c : V, ω (a + b) c = ω a c + ω b c := fun a b c => by simp
        exact h1 x y z
      map_smul' := fun r x => by
        ext z
        have h2 : ∀ a c : V, ω (r • a) c = r * ω a c := fun a c => by simp
        exact h2 x z }
  refine ⟨((InnerProductSpace.toDual ℝ (WithEta η)).symm.toLinearEquiv.toLinearMap).comp
    (L.restrictScalars ℝ), fun x y => ?_⟩
  show ⟪(InnerProductSpace.toDual ℝ (WithEta η)).symm (L x), y⟫_ℝ = _
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

end Riesz


section Operator

variable [FiniteDimensional ℝ V] {ω η : LinearMap.BilinForm ℝ V} [IsPosDefForm η]
  {T : WithEta η →ₗ[ℝ] WithEta η}

/-- `T` is `η`-skew. -/
lemma riesz_skew (hω : ∀ a b, ω a b = -ω b a)
    (hT : ∀ x y : WithEta η, ⟪T x, y⟫_ℝ = ω (WithEta.unmk x) (WithEta.unmk y)) (x y : WithEta η) :
    ⟪T x, y⟫_ℝ = -⟪x, T y⟫_ℝ := by
  rw [← real_inner_comm x (T y), hT x y, hT y x, hω (WithEta.unmk x) (WithEta.unmk y)]

/-- **The covariance inequality is `‖T a‖ ≤ ‖a‖`.** -/
lemma riesz_norm_le (hη : IsCovariance ω η)
    (hT : ∀ x y : WithEta η, ⟪T x, y⟫_ℝ = ω (WithEta.unmk x) (WithEta.unmk y)) (a : WithEta η) :
    ⟪T a, T a⟫_ℝ ≤ ⟪a, a⟫_ℝ := by
  have h1 := hη.sq_le (WithEta.unmk a) (WithEta.unmk (T a))
  have h2 : ω (WithEta.unmk a) (WithEta.unmk (T a)) = ⟪T a, T a⟫_ℝ := (hT a (T a)).symm
  rw [h2] at h1
  have h3 : η (WithEta.unmk (T a)) (WithEta.unmk (T a)) = ⟪T a, T a⟫_ℝ := rfl
  have h4 : η (WithEta.unmk a) (WithEta.unmk a) = ⟪a, a⟫_ℝ := rfl
  rw [h3, h4] at h1
  have h5 : 0 ≤ ⟪T a, T a⟫_ℝ := real_inner_self_nonneg
  rcases h5.lt_or_eq with h | h
  · nlinarith
  · rw [← h]; exact real_inner_self_nonneg


/-- **`T² = -1` gives a compatible complex structure.** -/
noncomputable def compatibleOfSq (hω : ∀ a b, ω a b = -ω b a) (hη : IsCovariance ω η)
    (hT : ∀ x y : WithEta η, ⟪T x, y⟫_ℝ = ω (WithEta.unmk x) (WithEta.unmk y))
    (hsq : ∀ x, T (T x) = -x) : CompatibleComplexStructure ω η where
  J := T
  J_sq := hsq
  symm := hη.symm
  eta_J x y := by
    have h : ⟪T (WithEta.mk x : WithEta η), T (WithEta.mk y : WithEta η)⟫_ℝ =
        ⟪(WithEta.mk x : WithEta η), (WithEta.mk y : WithEta η)⟫_ℝ := by
      rw [riesz_skew hω hT _ (T (WithEta.mk y)), hsq]
      simp
    exact h
  eta_pos x hx := IsPosDefForm.pos (η := η) x hx
  omega_eq x y := by
    have h : ω x y = -⟪(WithEta.mk x : WithEta η), T (WithEta.mk y : WithEta η)⟫_ℝ := by
      rw [← riesz_skew hω hT (WithEta.mk x) (WithEta.mk y), hT]
      rfl
    exact h

/-- If `T² ≠ -1` there is a unit vector `u` with `T² u = -μ u`, `0 < μ < 1`. -/
lemma exists_eigen (hω : ∀ a b, ω a b = -ω b a) (hη : IsCovariance ω η)
    (hnd : ∀ x, (∀ y, ω x y = 0) → x = 0)
    (hT : ∀ x y : WithEta η, ⟪T x, y⟫_ℝ = ω (WithEta.unmk x) (WithEta.unmk y))
    (hne : ¬ ∀ x, T (T x) = -x) :
    ∃ u : WithEta η, ⟪u, u⟫_ℝ = 1 ∧ ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ T (T u) = (-μ) • u := by
  let S : WithEta η →ₗ[ℝ] WithEta η := -(T ∘ₗ T)
  have hS : S.IsSymmetric := fun x y => by
    show ⟪-(T (T x)), y⟫_ℝ = ⟪x, -(T (T y))⟫_ℝ
    rw [inner_neg_left, inner_neg_right, riesz_skew hω hT (T x) y, riesz_skew hω hT x (T y)]
    simp [riesz_skew hω hT]
  let b := hS.eigenvectorBasis rfl
  have hb : ∀ i, S (b i) = (hS.eigenvalues rfl i : ℝ) • b i := fun i => hS.apply_eigenvectorBasis rfl i
  have hex : ∃ i, hS.eigenvalues rfl i ≠ 1 := by
    by_contra hall
    push_neg at hall
    apply hne
    have hSid : S = LinearMap.id := by
      apply b.toBasis.ext
      intro i
      simp [hb, hall i]
    intro x
    have := LinearMap.congr_fun hSid x
    simp only [S, LinearMap.neg_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at this
    simpa using congrArg Neg.neg this
  obtain ⟨i, hi⟩ := hex
  set μ := hS.eigenvalues rfl i with hμ
  have hu1 : ⟪b i, b i⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]; norm_num
  have hSu : S (b i) = μ • b i := hb i
  have hTT : T (T (b i)) = (-μ) • b i := by
    have : -(T (T (b i))) = μ • b i := hSu
    rw [neg_smul, ← this, neg_neg]
  have hinner : ⟪T (b i), T (b i)⟫_ℝ = μ := by
    have h1 : ⟪T (b i), T (b i)⟫_ℝ = ⟪S (b i), b i⟫_ℝ := by
      show _ = ⟪-(T (T (b i))), b i⟫_ℝ
      rw [inner_neg_left, riesz_skew hω hT (T (b i)) (b i)]; simp
    rw [h1, hSu, inner_smul_left, hu1]; simp
  have hle : μ ≤ 1 := by
    have := riesz_norm_le hη hT (b i)
    rw [hinner, hu1] at this; exact this
  have hge : 0 ≤ μ := by
    rw [← hinner]; exact real_inner_self_nonneg
  have hpos : 0 < μ := by
    rcases hge.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : T (b i) = 0 := by
        have : ⟪T (b i), T (b i)⟫_ℝ = 0 := by rw [hinner, ← h]
        exact inner_self_eq_zero.1 this
      have hz : ∀ y, ω (WithEta.unmk (b i)) y = 0 := fun y => by
        have := hT (b i) (WithEta.mk y)
        rw [h0, inner_zero_left] at this
        exact this.symm
      have := hnd _ hz
      have h2 : (b i) = 0 := this
      rw [h2, inner_zero_left] at hu1
      norm_num at hu1
  exact ⟨b i, hu1, μ, hpos, lt_of_le_of_ne hle hi, hTT⟩


/-- **The key inequality**: for a unit vector `u` with `T² u = -μ u`, `0 < μ < 1`, the covariance inequality survives the
subtraction of `(1 - μ) ⟪u, ·⟫²`. -/
lemma two_term_ineq {d c A B Na Nb : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hNa : 0 ≤ Na) (hNb : 0 ≤ Nb)
    (hd : d ^ 2 ≤ A * B) (hc : c ^ 2 ≤ Na * Nb) : (d + c) ^ 2 ≤ (A + Na) * (B + Nb) := by
  have h1 : (d * c) ^ 2 ≤ (A * Nb) * (B * Na) := by
    have : (d * c) ^ 2 = d ^ 2 * c ^ 2 := by ring
    rw [this]
    calc d ^ 2 * c ^ 2 ≤ (A * B) * (Na * Nb) := by
          apply mul_le_mul hd hc (sq_nonneg _) (by positivity)
      _ = (A * Nb) * (B * Na) := by ring
  have h2 : 2 * (d * c) ≤ A * Nb + B * Na := by
    have h3 : (2 * (d * c)) ^ 2 ≤ (A * Nb + B * Na) ^ 2 := by
      nlinarith [sq_nonneg (A * Nb - B * Na)]
    exact (abs_le_of_sq_le_sq' h3 (by positivity)).2
  nlinarith

lemma key_ineq (hω : ∀ a b, ω a b = -ω b a) (hη : IsCovariance ω η)
    (hT : ∀ x y : WithEta η, ⟪T x, y⟫_ℝ = ω (WithEta.unmk x) (WithEta.unmk y))
    {u : WithEta η} (hu1 : ⟪u, u⟫_ℝ = 1) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hTT : T (T u) = (-μ) • u)
    (a b : WithEta η) :
    ω (WithEta.unmk a) (WithEta.unmk b) ^ 2 ≤
      (⟪a, a⟫_ℝ - (1 - μ) * ⟪u, a⟫_ℝ ^ 2) * (⟪b, b⟫_ℝ - (1 - μ) * ⟪u, b⟫_ℝ ^ 2) := by
  set l := Real.sqrt μ with hl
  have hl0 : 0 < l := Real.sqrt_pos.2 hμ0
  have hll : l * l = μ := Real.mul_self_sqrt hμ0.le
  have hTu : ⟪T u, T u⟫_ℝ = μ := by
    rw [riesz_skew hω hT u (T u), hTT, inner_smul_right, hu1]; simp
  have huTu : ⟪u, T u⟫_ℝ = 0 := by
    have h1 := riesz_skew hω hT u u
    rw [real_inner_comm u (T u)] at h1
    linarith
  obtain ⟨v, hv⟩ : ∃ v : WithEta η, v = l⁻¹ • T u := ⟨_, rfl⟩
  have hvv : ⟪v, v⟫_ℝ = 1 := by
    rw [hv, inner_smul_left, inner_smul_right, hTu]
    simp only [conj_trivial]
    field_simp
    nlinarith [hll]
  have huv : ⟪u, v⟫_ℝ = 0 := by rw [hv, inner_smul_right, huTu]; simp
  have hTu' : T u = l • v := by rw [hv, smul_smul, mul_inv_cancel₀ hl0.ne', one_smul]
  have hTv : T v = (-l) • u := by
    rw [hv, map_smul, hTT, smul_smul]
    congr 1
    field_simp
    nlinarith [hll]
  -- the orthogonal decomposition
  have hperp : ∀ x : WithEta η, ⟪u, x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v⟫_ℝ = 0 ∧
      ⟪v, x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v⟫_ℝ = 0 := fun x => by
    refine ⟨?_, ?_⟩
    · rw [inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right, hu1, huv]; ring
    · rw [inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right, hvv, real_inner_comm u v, huv]; ring
  have hperpT : ∀ x : WithEta η, ⟪T (x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v), u⟫_ℝ = 0 ∧
      ⟪T (x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v), v⟫_ℝ = 0 := fun x => by
    obtain ⟨h1, h2⟩ := hperp x
    refine ⟨?_, ?_⟩
    · rw [riesz_skew hω hT, hTu', inner_smul_right, real_inner_comm, h2]; ring
    · rw [riesz_skew hω hT, hTv, inner_smul_right, real_inner_comm, h1]; ring
  have hTa : ∀ x : WithEta η, T x = (⟪u, x⟫_ℝ * l) • v - (⟪v, x⟫_ℝ * l) • u +
      T (x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v) := fun x => by
    have : x = ⟪u, x⟫_ℝ • u + ⟪v, x⟫_ℝ • v + (x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v) := by abel
    conv_lhs => rw [this]
    rw [map_add, map_add, map_smul, map_smul, hTu', hTv]
    module
  have hdec : ∀ x : WithEta η, x = ⟪u, x⟫_ℝ • u + ⟪v, x⟫_ℝ • v + (x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v) := fun x => by
    abel
  have hnorm : ∀ x : WithEta η, ⟪x, x⟫_ℝ = ⟪u, x⟫_ℝ ^ 2 + ⟪v, x⟫_ℝ ^ 2 +
      ⟪x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v, x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v⟫_ℝ := fun x => by
    obtain ⟨h1, h2⟩ := hperp x
    set p := x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v with hp
    have hx : x = ⟪u, x⟫_ℝ • u + ⟪v, x⟫_ℝ • v + p := hdec x
    have e1 : ⟪x, x⟫_ℝ = ⟪⟪u, x⟫_ℝ • u + ⟪v, x⟫_ℝ • v + p, x⟫_ℝ := by rw [← hx]
    rw [e1, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left]
    simp only [conj_trivial]
    have e2 : ⟪p, x⟫_ℝ = ⟪p, p⟫_ℝ := by
      conv_lhs => rw [hx]
      rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, real_inner_comm u p,
        real_inner_comm v p, h1, h2]
      ring
    rw [e2]
    ring
  have hom : ∀ x y : WithEta η, ω (WithEta.unmk x) (WithEta.unmk y) =
      l * (⟪u, x⟫_ℝ * ⟪v, y⟫_ℝ - ⟪v, x⟫_ℝ * ⟪u, y⟫_ℝ) +
        ⟪T (x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v), y - ⟪u, y⟫_ℝ • u - ⟪v, y⟫_ℝ • v⟫_ℝ := fun x y => by
    rw [← hT, hTa x, inner_add_left, inner_sub_left, inner_smul_left, inner_smul_left]
    simp only [conj_trivial]
    obtain ⟨h1, h2⟩ := hperpT x
    have e : ⟪T (x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v), y⟫_ℝ =
        ⟪T (x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v), y - ⟪u, y⟫_ℝ • u - ⟪v, y⟫_ℝ • v⟫_ℝ := by
      conv_lhs => rw [hdec y]
      rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, h1, h2]
      ring
    rw [e]
    ring
  have hc : ∀ x y : WithEta η, ⟪T (x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v), y - ⟪u, y⟫_ℝ • u - ⟪v, y⟫_ℝ • v⟫_ℝ ^ 2 ≤
      ⟪x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v, x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v⟫_ℝ *
        ⟪y - ⟪u, y⟫_ℝ • u - ⟪v, y⟫_ℝ • v, y - ⟪u, y⟫_ℝ • u - ⟪v, y⟫_ℝ • v⟫_ℝ := fun x y => by
    set px := x - ⟪u, x⟫_ℝ • u - ⟪v, x⟫_ℝ • v
    set py := y - ⟪u, y⟫_ℝ • u - ⟪v, y⟫_ℝ • v
    have h1 := real_inner_mul_inner_self_le (T px) py
    have h2 := riesz_norm_le hη hT px
    have h3 : 0 ≤ ⟪py, py⟫_ℝ := real_inner_self_nonneg
    have h4 := mul_le_mul_of_nonneg_right h2 h3
    nlinarith [sq_nonneg ⟪T px, py⟫_ℝ]
  rw [hom a b]
  have hNa : 0 ≤ ⟪a - ⟪u, a⟫_ℝ • u - ⟪v, a⟫_ℝ • v, a - ⟪u, a⟫_ℝ • u - ⟪v, a⟫_ℝ • v⟫_ℝ := real_inner_self_nonneg
  have hNb : 0 ≤ ⟪b - ⟪u, b⟫_ℝ • u - ⟪v, b⟫_ℝ • v, b - ⟪u, b⟫_ℝ • u - ⟪v, b⟫_ℝ • v⟫_ℝ := real_inner_self_nonneg
  have hmain := two_term_ineq (d := l * (⟪u, a⟫_ℝ * ⟪v, b⟫_ℝ - ⟪v, a⟫_ℝ * ⟪u, b⟫_ℝ))
    (c := ⟪T (a - ⟪u, a⟫_ℝ • u - ⟪v, a⟫_ℝ • v), b - ⟪u, b⟫_ℝ • u - ⟪v, b⟫_ℝ • v⟫_ℝ)
    (A := μ * ⟪u, a⟫_ℝ ^ 2 + ⟪v, a⟫_ℝ ^ 2) (B := μ * ⟪u, b⟫_ℝ ^ 2 + ⟪v, b⟫_ℝ ^ 2)
    (Na := ⟪a - ⟪u, a⟫_ℝ • u - ⟪v, a⟫_ℝ • v, a - ⟪u, a⟫_ℝ • u - ⟪v, a⟫_ℝ • v⟫_ℝ)
    (Nb := ⟪b - ⟪u, b⟫_ℝ • u - ⟪v, b⟫_ℝ • v, b - ⟪u, b⟫_ℝ • u - ⟪v, b⟫_ℝ • v⟫_ℝ)
    (by positivity) (by positivity) hNa hNb
    (by
      have := sq_nonneg (l * ⟪u, a⟫_ℝ * (l * ⟪u, b⟫_ℝ) + ⟪v, a⟫_ℝ * ⟪v, b⟫_ℝ)
      rw [← hll]
      nlinarith [this])
    (hc a b)
  have ea := hnorm a
  have eb := hnorm b
  rw [ea, eb]
  nlinarith [hmain]

end Operator


section Main

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {ω η : LinearMap.BilinForm ℝ V}

/-- The rank-one symmetric form `ρ ⊗ ρ` of a linear functional. -/
def outerForm (ρ : V →ₗ[ℝ] ℝ) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y => ρ x * ρ y) (fun x x' y => by simp [add_mul])
    (fun c x y => by simp [mul_assoc]) (fun x y y' => by simp [mul_add])
    (fun c x y => by simp [mul_left_comm])

lemma outerForm_apply (ρ : V →ₗ[ℝ] ℝ) (x y : V) : outerForm ρ x y = ρ x * ρ y := rfl

/-- **The linear-algebra half of the necessity**: a covariance of a nondegenerate `ω` with no compatible complex
structure stays a covariance after the subtraction of `ε ρ ⊗ ρ`, for a nonzero functional `ρ` and some `ε > 0`. -/
theorem exists_sub_covariance (hω : ∀ a b, ω a b = -ω b a) (hnd : ∀ x, (∀ y, ω x y = 0) → x = 0)
    (hη : IsCovariance ω η) (hno : IsEmpty (CompatibleComplexStructure ω η)) :
    ∃ (ρ : V →ₗ[ℝ] ℝ) (ε : ℝ), ρ ≠ 0 ∧ 0 < ε ∧ IsCovariance ω (η - ε • outerForm ρ) := by
  haveI : IsPosDefForm η := ⟨hη.symm, fun x hx => hη.pos_def hnd hx⟩
  obtain ⟨T, hT⟩ := exists_riesz (η := η) ω
  by_cases hsq : ∀ x, T (T x) = -x
  · exact (hno.false (compatibleOfSq hω hη hT hsq)).elim
  · obtain ⟨u, hu1, μ, hμ0, hμ1, hTT⟩ := exists_eigen hω hη hnd hT hsq
    let ρ : V →ₗ[ℝ] ℝ :=
      { toFun := fun y => ⟪u, (WithEta.mk y : WithEta η)⟫_ℝ
        map_add' := fun y z => by
          have h : ∀ y z : V, ⟪u, (WithEta.mk (y + z) : WithEta η)⟫_ℝ =
              ⟪u, (WithEta.mk y : WithEta η)⟫_ℝ + ⟪u, (WithEta.mk z : WithEta η)⟫_ℝ := fun y z => inner_add_right _ _ _
          exact h y z
        map_smul' := fun c y => by
          have h : ∀ (c : ℝ) (y : V), ⟪u, (WithEta.mk (c • y) : WithEta η)⟫_ℝ =
              c * ⟪u, (WithEta.mk y : WithEta η)⟫_ℝ := fun c y => inner_smul_right _ _ _
          exact h c y }
    have hρ : ∀ x : WithEta η, ρ (WithEta.unmk x) = ⟪u, x⟫_ℝ := fun x => rfl
    refine ⟨ρ, 1 - μ, ?_, by linarith, ?_⟩
    · intro h0
      have : ρ (WithEta.unmk u) = 0 := by rw [h0]; rfl
      rw [hρ, hu1] at this
      exact one_ne_zero this
    · have hsub : ∀ a : WithEta η, (η - (1 - μ) • outerForm ρ) (WithEta.unmk a) (WithEta.unmk a) =
          ⟪a, a⟫_ℝ - (1 - μ) * ⟪u, a⟫_ℝ ^ 2 := fun a => by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, outerForm_apply, smul_eq_mul]
        have e : ⟪a, a⟫_ℝ = η (WithEta.unmk a) (WithEta.unmk a) := rfl
        rw [hρ, e]; ring
      refine ⟨fun a b => ?_, fun a => ?_, fun a b => ?_⟩
      · simp [hη.symm a b, mul_comm, outerForm_apply]
      · have h := hsub (WithEta.mk a)
        rw [show WithEta.unmk (WithEta.mk a : WithEta η) = a from rfl] at h
        rw [h]
        have hcs := real_inner_mul_inner_self_le u (WithEta.mk a : WithEta η)
        rw [hu1] at hcs
        have h2 : ⟪u, (WithEta.mk a : WithEta η)⟫_ℝ ^ 2 ≤ ⟪(WithEta.mk a : WithEta η), (WithEta.mk a : WithEta η)⟫_ℝ := by
          have : ⟪(WithEta.mk a : WithEta η), u⟫_ℝ = ⟪u, (WithEta.mk a : WithEta η)⟫_ℝ := real_inner_comm _ _
          nlinarith
        nlinarith [sq_nonneg ⟪u, (WithEta.mk a : WithEta η)⟫_ℝ]
      · have h := key_ineq hω hη hT hu1 hμ0 hμ1 hTT (WithEta.mk a) (WithEta.mk b)
        have ha := hsub (WithEta.mk a)
        have hb := hsub (WithEta.mk b)
        rw [show WithEta.unmk (WithEta.mk a : WithEta η) = a from rfl] at ha h
        rw [show WithEta.unmk (WithEta.mk b : WithEta η) = b from rfl] at hb h
        rw [ha, hb]
        exact h

end Main

end Lightlike.OperatorAlgebras.QuasiFreeState
