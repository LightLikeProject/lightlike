import Lightlike.ODE.GlobalLipschitz
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Parallel transport and the holonomy of a connection along a path

A connection in a local trivialisation over the chart `ℝ³` is given by its matrix-valued components
`A_a(x) ∈ Mat(n, ℂ)` (`MatConn`). Along a path `e`, the parallel transport is the solution of
`d/dt U(t) = −A_a(e(t)) ė^a(t) U(t)`, `U(t₁) = 1` (Ashtekar–Lewandowski, arXiv:gr-qc/0404018, eq. (4.35), p. 33); it
exists on every interval and is unique (`exists_transport`, `transport_unique`), and the holonomy along the edge
`e|[t₁, t₂]` is `A(e) = U(t₂)` (eq. (4.36)). The transport has the flow property
`U(u, s) = U(u, t) U(t, s)` (`transport_trans`).

Paths are `C¹` on `ℝ`; Ashtekar–Lewandowski use piecewise analytic edges and note that "these assumptions can be relaxed
and one can work with just smooth structures" (footnote 17, p. 33).
-/

open Matrix Set
open scoped ContDiff NNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ}

/-- A connection in a local trivialisation over the chart `ℝ³`: the matrix-valued components `A_a(x)`. -/
abbrev MatConn (n : ℕ) := (Fin 3 → ℝ) → Fin 3 → Matrix (Fin n) (Fin n) ℂ

/-- The coefficient `A_a(e(t)) ė^a(t)` of the parallel transport equation along a path `e`. -/
def transportCoeff (A : MatConn n) (e : ℝ → Fin 3 → ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ a, ((deriv e t a : ℝ) : ℂ) • A (e t) a

/-- A continuous connection (entrywise) along a `C¹` path has a continuous transport coefficient. -/
lemma continuous_transportCoeff {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {e : ℝ → Fin 3 → ℝ}
    (he : ContDiff ℝ 1 e) : Continuous (transportCoeff A e) := by
  have hd : Continuous (deriv e) := he.continuous_deriv le_rfl
  unfold transportCoeff
  refine continuous_finsetSum _ fun a _ => ?_
  exact (Complex.continuous_ofReal.comp ((continuous_apply a).comp hd)).smul ((hA a).comp he.continuous)

/-- The right-hand side `U ↦ −M U` of a linear matrix equation is Lipschitz with constant `‖M‖`. -/
lemma lipschitzWith_neg_mul (M : Matrix (Fin n) (Fin n) ℂ) :
    LipschitzWith ‖M‖₊ (fun U : Matrix (Fin n) (Fin n) ℂ => -(M * U)) := by
  refine LipschitzWith.of_dist_le_mul fun U V => ?_
  rw [dist_eq_norm, dist_eq_norm, show -(M * U) - -(M * V) = -(M * (U - V)) by noncomm_ring, norm_neg, coe_nnnorm]
  exact norm_mul_le M (U - V)


/-! ### The transport equation `U' = −M(t) U` for a coefficient continuous on `[s, t]` -/

/-- **Existence** for the linear equation `U' = −M(t) U`, `U s = U₀`, with `M` continuous on `[s, t]`. -/
theorem exists_transportM {M : ℝ → Matrix (Fin n) (Fin n) ℂ} {s t : ℝ} (hM : ContinuousOn M (Icc s t))
    (hst : s ≤ t) (U₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : ℝ → Matrix (Fin n) (Fin n) ℂ, U s = U₀ ∧
      ∀ τ ∈ Icc s t, HasDerivWithinAt U (-(M τ * U τ)) (Icc s t) τ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hM
  have hc : ∀ U : Matrix (Fin n) (Fin n) ℂ, ContinuousOn (fun τ => -(M τ * U)) (Icc s t) := fun U =>
    (hM.mul continuousOn_const).neg
  refine Lightlike.ODE.exists_solution_Icc_of_lipschitz (f := fun τ U => -(M τ * U))
    (K := C.toNNReal) hst (fun τ hτ => ?_) hc U₀
  refine (lipschitzWith_neg_mul _).weaken ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact (hC τ hτ).trans (Real.le_coe_toNNReal C)

/-- **Uniqueness** for `U' = −M(t) U` on `[s, t]`, `M` continuous on `[s, t]`. -/
theorem transportM_unique {M : ℝ → Matrix (Fin n) (Fin n) ℂ} {s t : ℝ} (hM : ContinuousOn M (Icc s t))
    {U V : ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hU : ∀ τ ∈ Icc s t, HasDerivWithinAt U (-(M τ * U τ)) (Icc s t) τ)
    (hV : ∀ τ ∈ Icc s t, HasDerivWithinAt V (-(M τ * V τ)) (Icc s t) τ) (h0 : U s = V s) :
    EqOn U V (Icc s t) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hM
  refine Lightlike.ODE.eqOn_of_lipschitz (f := fun τ U => -(M τ * U))
    (K := C.toNNReal) (fun τ hτ => ?_) hU hV h0
  refine (lipschitzWith_neg_mul _).weaken ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact (hC τ hτ).trans (Real.le_coe_toNNReal C)

open Classical in
/-- The solution `U(t, s)` of `U' = −M U`, `U(s, s) = 1` at `t`, for `M` continuous on `[s, t]`; `1` otherwise. -/
def transportM (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (s t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  if h : ContinuousOn M (Icc s t) ∧ s ≤ t then Classical.choose (exists_transportM h.1 h.2 1) t else 1

/-- Every solution from `1` on `[s, t]` is `transportM`. -/
theorem transportM_eq {M : ℝ → Matrix (Fin n) (Fin n) ℂ} {s t : ℝ} (hM : ContinuousOn M (Icc s t))
    {U : ℝ → Matrix (Fin n) (Fin n) ℂ} (hU : ∀ τ ∈ Icc s t, HasDerivWithinAt U (-(M τ * U τ)) (Icc s t) τ)
    (h0 : U s = 1) : ∀ τ ∈ Icc s t, transportM M s τ = U τ := by
  intro τ hτ
  have hsub : Icc s τ ⊆ Icc s t := Icc_subset_Icc_right hτ.2
  have h : ContinuousOn M (Icc s τ) ∧ s ≤ τ := ⟨hM.mono hsub, hτ.1⟩
  have hspec := Classical.choose_spec (exists_transportM h.1 h.2 1)
  rw [transportM, dite_eq_left h]
  exact transportM_unique h.1 hspec.2 (fun σ hσ => (hU σ (hsub hσ)).mono hsub) (hspec.1.trans h0.symm)
    ⟨hτ.1, le_rfl⟩

/-- `transportM M s ·` solves the equation on `[s, t]`, with value `1` at `s`. -/
theorem hasDerivWithinAt_transportM {M : ℝ → Matrix (Fin n) (Fin n) ℂ} {s t : ℝ} (hM : ContinuousOn M (Icc s t))
    (hst : s ≤ t) :
    transportM M s s = 1 ∧ ∀ τ ∈ Icc s t,
      HasDerivWithinAt (transportM M s) (-(M τ * transportM M s τ)) (Icc s t) τ := by
  obtain ⟨U, hU0, hU⟩ := exists_transportM hM hst 1
  have heq := transportM_eq hM hU hU0
  refine ⟨(heq s ⟨le_rfl, hst⟩).trans hU0, fun τ hτ => ?_⟩
  rw [heq τ hτ]
  exact (hU τ hτ).congr (fun σ hσ => heq σ hσ) (heq τ hτ)

/-- **The flow property**: `U(u, s) = U(u, t) U(t, s)` for `s ≤ t ≤ u`. -/
theorem transportM_trans {M : ℝ → Matrix (Fin n) (Fin n) ℂ} {s t u : ℝ} (hM : ContinuousOn M (Icc s u))
    (hst : s ≤ t) (htu : t ≤ u) : transportM M s u = transportM M t u * transportM M s t := by
  have hsub : Icc t u ⊆ Icc s u := Icc_subset_Icc_left hst
  obtain ⟨h1, h2⟩ := hasDerivWithinAt_transportM hM (hst.trans htu)
  obtain ⟨k1, k2⟩ := hasDerivWithinAt_transportM (hM.mono hsub) htu
  have hW : ∀ τ ∈ Icc t u, HasDerivWithinAt (fun σ => transportM M t σ * transportM M s t)
      (-(M τ * (transportM M t τ * transportM M s t))) (Icc t u) τ := fun τ hτ => by
    have := (k2 τ hτ).mul_const (transportM M s t)
    rwa [neg_mul, Matrix.mul_assoc] at this
  exact transportM_unique (hM.mono hsub) (fun τ hτ => (h2 τ (hsub hτ)).mono hsub) hW
    (by rw [k1, Matrix.one_mul]) ⟨htu, le_rfl⟩

/-! ### Along a path -/

/-- **Existence of the parallel transport** (Ashtekar–Lewandowski (4.35)): for a continuous connection and a `C¹`
path, on every interval `[s, t]` and for every initial value `U₀` there is `U` with `U s = U₀` and
`U' = −A_a(e) ė^a U`. -/
theorem exists_transport {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {e : ℝ → Fin 3 → ℝ}
    (he : ContDiff ℝ 1 e) {s t : ℝ} (hst : s ≤ t) (U₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : ℝ → Matrix (Fin n) (Fin n) ℂ, U s = U₀ ∧
      ∀ τ ∈ Icc s t, HasDerivWithinAt U (-(transportCoeff A e τ * U τ)) (Icc s t) τ :=
  exists_transportM (continuous_transportCoeff hA he).continuousOn hst U₀

/-- **Uniqueness of the parallel transport**: two solutions of `U' = −A_a(e) ė^a U` on `[s, t]` with the same value
at `s` agree on `[s, t]`. -/
theorem transport_unique {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {e : ℝ → Fin 3 → ℝ}
    (he : ContDiff ℝ 1 e) {s t : ℝ} {U V : ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hU : ∀ τ ∈ Icc s t, HasDerivWithinAt U (-(transportCoeff A e τ * U τ)) (Icc s t) τ)
    (hV : ∀ τ ∈ Icc s t, HasDerivWithinAt V (-(transportCoeff A e τ * V τ)) (Icc s t) τ) (h0 : U s = V s) :
    EqOn U V (Icc s t) :=
  transportM_unique (continuous_transportCoeff hA he).continuousOn hU hV h0

/-- The **parallel transport** `U(t, s)` along `e` from `e(s)` to `e(t)`, for `s ≤ t` (Ashtekar–Lewandowski (4.35)):
`transportM` of the coefficient `A_a(e(t)) ė^a(t)`. -/
def transport (A : MatConn n) (e : ℝ → Fin 3 → ℝ) (s t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  transportM (transportCoeff A e) s t

/-- Every solution from `1` on `[s, t]` is the parallel transport. -/
theorem transport_eq {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {e : ℝ → Fin 3 → ℝ}
    (he : ContDiff ℝ 1 e) {s t : ℝ} {U : ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hU : ∀ τ ∈ Icc s t, HasDerivWithinAt U (-(transportCoeff A e τ * U τ)) (Icc s t) τ) (h0 : U s = 1) :
    ∀ τ ∈ Icc s t, transport A e s τ = U τ :=
  transportM_eq (continuous_transportCoeff hA he).continuousOn hU h0

/-- The parallel transport from `e(s)` solves the transport equation, with `U(s, s) = 1`. -/
theorem hasDerivWithinAt_transport {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {e : ℝ → Fin 3 → ℝ}
    (he : ContDiff ℝ 1 e) {s t : ℝ} (hst : s ≤ t) :
    transport A e s s = 1 ∧ ∀ τ ∈ Icc s t,
      HasDerivWithinAt (transport A e s) (-(transportCoeff A e τ * transport A e s τ)) (Icc s t) τ :=
  hasDerivWithinAt_transportM (continuous_transportCoeff hA he).continuousOn hst

/-- **The flow property** of the parallel transport: `U(u, s) = U(u, t) U(t, s)` for `s ≤ t ≤ u`. -/
theorem transport_trans {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {e : ℝ → Fin 3 → ℝ}
    (he : ContDiff ℝ 1 e) {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u) :
    transport A e s u = transport A e t u * transport A e s t :=
  transportM_trans (continuous_transportCoeff hA he).continuousOn hst htu

/-- The **holonomy** `A(e) = U(t₂, t₁)` of the connection along the edge `e|[t₁, t₂]` (Ashtekar–Lewandowski (4.36)). -/
def holonomy (A : MatConn n) (e : ℝ → Fin 3 → ℝ) (t₁ t₂ : ℝ) : Matrix (Fin n) (Fin n) ℂ := transport A e t₁ t₂


/-- `Icc s t` is a neighbourhood of `τ ∈ [s, t)` within `[τ, ∞)`. -/
lemma Icc_mem_nhdsWithin_Ici_of_mem {s t τ : ℝ} (hτ : τ ∈ Ico s t) : Icc s t ∈ nhdsWithin τ (Ici τ) :=
  Filter.mem_of_superset (Icc_mem_nhdsGE hτ.2) (Icc_subset_Icc_left hτ.1)

/-- A path in a normed space whose derivative within `[s, t]` vanishes is constant on `[s, t]`. -/
lemma eq_of_hasDerivWithinAt_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F} {s t : ℝ}
    (hf : ∀ τ ∈ Icc s t, HasDerivWithinAt f 0 (Icc s t) τ) : ∀ τ ∈ Icc s t, f τ = f s :=
  constant_of_has_deriv_right_zero (fun τ hτ => (hf τ hτ).continuousWithinAt)
    (fun τ hτ => (hf τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsWithin_Ici_of_mem hτ))

/-- The transport coefficient of an anti-Hermitian connection is anti-Hermitian. -/
lemma transportCoeff_conjTranspose {A : MatConn n} (hAH : ∀ x a, (A x a)ᴴ = -A x a) (e : ℝ → Fin 3 → ℝ) (τ : ℝ) :
    (transportCoeff A e τ)ᴴ = -transportCoeff A e τ := by
  simp only [transportCoeff, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hAH, Complex.star_def,
    Complex.conj_ofReal, smul_neg, Finset.sum_neg_distrib]

/-- The conjugate transpose, as a continuous `ℝ`-linear map. -/
def conjTransposeCLM : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Mᴴ
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun r M => by
        ext i j
        simp [Matrix.conjTranspose_apply, Matrix.smul_apply] }

/-- **Unitarity**: for `M` anti-Hermitian on `[s, t]`, `U(t, s)ᴴ U(t, s) = 1`. -/
theorem transportM_conjTranspose_mul_self {M : ℝ → Matrix (Fin n) (Fin n) ℂ} {s t : ℝ}
    (hM : ContinuousOn M (Icc s t)) (hMH : ∀ τ ∈ Icc s t, (M τ)ᴴ = -M τ) (hst : s ≤ t) :
    (transportM M s t)ᴴ * transportM M s t = 1 := by
  obtain ⟨h1, h2⟩ := hasDerivWithinAt_transportM hM hst
  have hD : ∀ τ ∈ Icc s t, HasDerivWithinAt (fun σ => (transportM M s σ)ᴴ * transportM M s σ) 0 (Icc s t) τ := by
    intro τ hτ
    have hS : HasDerivWithinAt (fun σ => (transportM M s σ)ᴴ) ((-(M τ * transportM M s τ))ᴴ) (Icc s t) τ :=
      (conjTransposeCLM (n := n)).hasFDerivAt.comp_hasDerivWithinAt τ (h2 τ hτ)
    refine (hS.fun_mul (h2 τ hτ)).congr_deriv ?_
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hMH τ hτ]
    noncomm_ring
  have := eq_of_hasDerivWithinAt_zero hD t ⟨hst, le_rfl⟩
  rw [this, h1, Matrix.conjTranspose_one, Matrix.one_mul]

/-- **The holonomy of a `u(n)` connection is unitary**: for anti-Hermitian `A_a`, `U(t, s)ᴴ U(t, s) = 1`. -/
theorem transport_conjTranspose_mul_self {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a)
    (hAH : ∀ x a, (A x a)ᴴ = -A x a) {e : ℝ → Fin 3 → ℝ} (he : ContDiff ℝ 1 e) {s t : ℝ} (hst : s ≤ t) :
    (transport A e s t)ᴴ * transport A e s t = 1 :=
  transportM_conjTranspose_mul_self (continuous_transportCoeff hA he).continuousOn
    (fun τ _ => transportCoeff_conjTranspose hAH e τ) hst

/-- The trace of the transport coefficient of a traceless connection vanishes. -/
lemma trace_transportCoeff {A : MatConn n} (htr : ∀ x a, (A x a).trace = 0) (e : ℝ → Fin 3 → ℝ) (τ : ℝ) :
    (transportCoeff A e τ).trace = 0 := by
  simp only [transportCoeff, Matrix.trace_sum, Matrix.trace_smul, htr, smul_zero, Finset.sum_const_zero]

/-- The entries of a matrix, as continuous `ℝ`-linear maps. -/
def entryCLM (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- **Determinant one in dimension two**: for `M` traceless on `[s, t]`, `det U(t, s) = 1` (Liouville's formula
`(det U)' = −tr M det U`). -/
theorem transportM_det_two {M : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {s t : ℝ} (hM : ContinuousOn M (Icc s t))
    (htr : ∀ τ ∈ Icc s t, (M τ).trace = 0) (hst : s ≤ t) : (transportM M s t).det = 1 := by
  obtain ⟨h1, h2⟩ := hasDerivWithinAt_transportM hM hst
  have hent : ∀ i j, ∀ τ ∈ Icc s t, HasDerivWithinAt (fun σ => transportM M s σ i j)
      ((-(M τ * transportM M s τ)) i j) (Icc s t) τ :=
    fun i j τ hτ => (entryCLM i j).hasFDerivAt.comp_hasDerivWithinAt τ (h2 τ hτ)
  have hD : ∀ τ ∈ Icc s t, HasDerivWithinAt (fun σ => (transportM M s σ).det) 0 (Icc s t) τ := by
    intro τ hτ
    have h := ((hent 0 0 τ hτ).fun_mul (hent 1 1 τ hτ)).sub ((hent 0 1 τ hτ).fun_mul (hent 1 0 τ hτ))
    have hdet : (fun σ => (transportM M s σ).det) = fun σ => transportM M s σ 0 0 * transportM M s σ 1 1 -
        transportM M s σ 0 1 * transportM M s σ 1 0 := funext fun σ => Matrix.det_fin_two _
    rw [hdet]
    convert h using 1
    have htrτ := htr τ hτ
    rw [Matrix.trace_fin_two] at htrτ
    simp only [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (transportM M s τ 0 0 * transportM M s τ 1 1 -
      transportM M s τ 0 1 * transportM M s τ 1 0) * htrτ
  have := eq_of_hasDerivWithinAt_zero hD t ⟨hst, le_rfl⟩
  rw [this, h1, Matrix.det_one]

/-- **The holonomy of a traceless connection in two dimensions has determinant one**: for `tr A_a = 0`,
`det U(t, s) = 1`. -/
theorem transport_det_two {A : MatConn 2} (hA : ∀ a, Continuous fun x => A x a) (htr : ∀ x a, (A x a).trace = 0)
    {e : ℝ → Fin 3 → ℝ} (he : ContDiff ℝ 1 e) {s t : ℝ} (hst : s ≤ t) : (transport A e s t).det = 1 :=
  transportM_det_two (continuous_transportCoeff hA he).continuousOn (fun τ _ => trace_transportCoeff htr e τ) hst

/-- **An `su(2)` coefficient gives a transport in `SU(2)`.** -/
theorem transportM_mem_specialUnitaryGroup {M : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {s t : ℝ}
    (hM : ContinuousOn M (Icc s t)) (hMH : ∀ τ ∈ Icc s t, (M τ)ᴴ = -M τ) (htr : ∀ τ ∈ Icc s t, (M τ).trace = 0)
    (hst : s ≤ t) : transportM M s t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 ?_, transportM_det_two hM htr hst⟩
  rw [Matrix.star_eq_conjTranspose]
  exact transportM_conjTranspose_mul_self hM hMH hst

/-- **The holonomy of an `su(2)` connection lies in `SU(2)`** (Ashtekar–Lewandowski (4.36): `A(e) ∈ G`). -/
theorem holonomy_mem_specialUnitaryGroup {A : MatConn 2} (hA : ∀ a, Continuous fun x => A x a)
    (hAH : ∀ x a, (A x a)ᴴ = -A x a) (htr : ∀ x a, (A x a).trace = 0) {e : ℝ → Fin 3 → ℝ} (he : ContDiff ℝ 1 e)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) : holonomy A e t₁ t₂ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  transportM_mem_specialUnitaryGroup (continuous_transportCoeff hA he).continuousOn
    (fun τ _ => transportCoeff_conjTranspose hAH e τ) (fun τ _ => trace_transportCoeff htr e τ) h

/-- The constant `u(1)` connection `A₀ = i`, `A₁ = A₂ = 0` (for the trust check). -/
def u1Conn : MatConn 1 := fun _ a => if a = 0 then Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ) else 0

/-- **Trust check: the holonomy is not trivial.** Along the straight path `e(t) = t e₀`, the holonomy of the constant
`u(1)` connection `A₀ = i` over `[0, π]` is `exp(−iπ) = −1`. -/
theorem holonomy_u1Conn : holonomy u1Conn (fun t => t • Pi.single 0 1) 0 Real.pi = -1 := by
  have hA : ∀ a, Continuous fun x => u1Conn x a := fun a => continuous_const
  have he : ContDiff ℝ 1 (fun t : ℝ => t • (Pi.single 0 1 : Fin 3 → ℝ)) := contDiff_id.smul contDiff_const
  have hde : ∀ t, deriv (fun t : ℝ => t • (Pi.single 0 1 : Fin 3 → ℝ)) t = Pi.single 0 1 := fun t => by
    simpa using ((hasDerivAt_id t).smul_const (Pi.single 0 1 : Fin 3 → ℝ)).deriv
  have hM : ∀ τ, transportCoeff u1Conn (fun t => t • Pi.single 0 1) τ = Complex.I • 1 := fun τ => by
    simp [transportCoeff, hde, u1Conn, Pi.single_apply]
  set U : ℝ → Matrix (Fin 1) (Fin 1) ℂ := fun t => Complex.exp (-(Complex.I * t)) • 1 with hU
  have hsol : ∀ τ ∈ Icc 0 Real.pi, HasDerivWithinAt U
      (-(transportCoeff u1Conn (fun t => t • Pi.single 0 1) τ * U τ)) (Icc 0 Real.pi) τ := by
    intro τ _
    have hc : HasDerivAt (fun t : ℝ => Complex.exp (-(Complex.I * t)))
        (Complex.exp (-(Complex.I * τ)) * (-(Complex.I * 1))) τ :=
      (((hasDerivAt_id τ).ofReal_comp).const_mul Complex.I).neg.cexp
    refine (hc.smul_const (1 : Matrix (Fin 1) (Fin 1) ℂ)).hasDerivWithinAt.congr_deriv ?_
    rw [hM, hU]
    ext i j
    fin_cases i; fin_cases j
    simp
  rw [holonomy, transport_eq hA he hsol (by simp [hU]) Real.pi ⟨Real.pi_pos.le, le_rfl⟩, hU]
  simp only
  rw [show -(Complex.I * (Real.pi : ℂ)) = -(Real.pi * Complex.I) by ring, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

end Lightlike.Canonical
