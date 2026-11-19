import Lightlike.Spacetime.Hypersurface
import Lightlike.Spacetime.EnergyConditionsField

/-!
# The Hamiltonian and momentum constraints (G1-014)

For a level-set hypersurface with unit normal `n` (`g(n, n) = ε`) and tangent fields `E_a` forming at `x₀` an orthonormal basis
of the tangent hyperplane (`g(E_a, E_b) = η_a δ_ab`), the contractions of the Gauss and Codazzi relations give the constraints

* `hamiltonian_constraint`: `2 G(n, n) = -ε Σ_{ab} η_a η_b g(R^D(E_b, E_a) E_a, E_b) + K² - K_ab K^ab`,
* `momentum_constraint`: `G(n, E_c) = Σ_a η_a ((D_{E_a} K)(E_c, E_a) - (D_{E_c} K)(E_a, E_a))`,

with `K = Σ_a η_a K(E_a, E_a)` and `K_ab K^ab = Σ_{ab} η_a η_b K(E_a, E_b)²` (Gourgoulhon, gr-qc/0703035, eqs. (2.92) and
(2.101) contracted). The traces are taken in the orthonormal basis `(n, E_a)` of the tangent space, which needs the curvature
to be linear in each slot (`curvatureAt_add_left`, …, from the components in a trivialization).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E] in
/-- The components are homogeneous on the chart domain. -/
theorem hv_smul (x₀ : M) {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) (r : ℝ) (u : TangentSpace 𝓘(ℝ, E) z) :
    hv x₀ z (r • u) = r • hv x₀ z u :=
  ((tTriv (E := E) x₀).linear ℝ hz).map_smul _ _

section Linear

variable (cov : Connection 𝓘(ℝ, E) M) [LocallySmoothConnection cov]


/-- The curvature is linear in each of its three slots. -/
theorem curvatureAt_linear (x : M) :
    (∀ a a' b c : TangentSpace 𝓘(ℝ, E) x, cov.curvatureAt x (a + a') b c = cov.curvatureAt x a b c + cov.curvatureAt x a' b c) ∧
    (∀ (r : ℝ) (a b c : TangentSpace 𝓘(ℝ, E) x), cov.curvatureAt x (r • a) b c = r • cov.curvatureAt x a b c) ∧
    (∀ a b b' c : TangentSpace 𝓘(ℝ, E) x, cov.curvatureAt x a (b + b') c = cov.curvatureAt x a b c + cov.curvatureAt x a b' c) ∧
    (∀ (r : ℝ) (a b c : TangentSpace 𝓘(ℝ, E) x), cov.curvatureAt x a (r • b) c = r • cov.curvatureAt x a b c) ∧
    (∀ a b c c' : TangentSpace 𝓘(ℝ, E) x, cov.curvatureAt x a b (c + c') = cov.curvatureAt x a b c + cov.curvatureAt x a b c') ∧
    (∀ (r : ℝ) (a b c : TangentSpace 𝓘(ℝ, E) x), cov.curvatureAt x a b (r • c) = r • cov.curvatureAt x a b c) := by
  have hx : x ∈ (tTriv (E := E) x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have inj : ∀ u v : TangentSpace 𝓘(ℝ, E) x, hv x x u = hv x x v → u = v := fun u v h =>
    (symmL_hv x hx u).symm.trans ((congrArg ((tTriv (E := E) x).symmL ℝ x) h).trans (symmL_hv x hx v))
  have hR := fun a b c => hv_curvatureAt' cov x hx a b c
  refine ⟨fun a a' b c => inj _ _ ?_, fun r a b c => inj _ _ ?_, fun a b b' c => inj _ _ ?_,
    fun r a b c => inj _ _ ?_, fun a b c c' => inj _ _ ?_, fun r a b c => inj _ _ ?_⟩ <;>
  simp only [hR, hv_add x hx, hv_smul x hx] <;> unfold Rhat <;>
  simp only [map_add, map_smul, add_apply, smul_apply, smul_add, smul_sub] <;> abel

end Linear

section Frame

variable (cov : Connection 𝓘(ℝ, E) M) [LocallySmoothConnection cov] (g : NondegMetric 𝓘(ℝ, E) M)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E] in
/-- The metric is a nondegenerate bilinear form at each point. -/
theorem nondegMetric_bilin_nondegenerate (x : M) : (g.g x).toBilinForm.Nondegenerate :=
  ⟨fun v hv => g.nondegenerate x v hv, fun w hw => g.nondegenerate x w fun v => (g.symm x w v).trans (hw v)⟩

/-- The curvature `v ↦ R(v, Y) Z` as a linear map. -/
def curvL (x : M) (Y Z : TangentSpace 𝓘(ℝ, E) x) : TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x where
  toFun v := cov.curvatureAt x v Y Z
  map_add' a a' := (curvatureAt_linear cov x).1 a a' Y Z
  map_smul' r a := (curvatureAt_linear cov x).2.1 r a Y Z

/-- The Ricci tensor is the trace of `v ↦ R(v, Y) Z`. -/
theorem ricciAt_eq_trace_curvL (x : M) (Y Z : TangentSpace 𝓘(ℝ, E) x) :
    cov.ricciAt x Y Z = LinearMap.trace ℝ _ (curvL cov x Y Z) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (tb (E := E) x)]
  unfold Connection.ricciAt
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, curvL, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E] in
/-- Coordinates in an orthonormal basis: `f.coord i w = sᵢ g(w, fᵢ)`. -/
theorem coord_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι] (x : M)
    (f : Module.Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) (s : ι → ℝ) (hs : ∀ i, s i * s i = 1)
    (hf : ∀ i j, g.g x (f i) (f j) = if i = j then s i else 0) (w : TangentSpace 𝓘(ℝ, E) x) (i : ι) :
    f.coord i w = s i * g.g x w (f i) := by
  have hw : g.g x w (f i) = f.coord i w * s i := by
    conv_lhs => rw [← f.sum_repr w]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul, hf]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  rw [hw, mul_comm (f.coord i w), ← mul_assoc, hs, one_mul]

/-- **The Ricci tensor in an orthonormal basis**: `Ric(Y, Z) = Σᵢ sᵢ g(R(fᵢ, Y) Z, fᵢ)`. -/
theorem ricciAt_frame {ι : Type*} [Fintype ι] [DecidableEq ι] (x : M)
    (f : Module.Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) (s : ι → ℝ) (hs : ∀ i, s i * s i = 1)
    (hf : ∀ i j, g.g x (f i) (f j) = if i = j then s i else 0) (Y Z : TangentSpace 𝓘(ℝ, E) x) :
    cov.ricciAt x Y Z = ∑ i, s i * g.g x (cov.curvatureAt x (f i) Y Z) (f i) := by
  rw [ricciAt_eq_trace_curvL, LinearMap.trace_eq_matrix_trace ℝ f]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := coord_orthonormal g x f s hs hf (curvL cov x Y Z (f i)) i
  simpa [Module.Basis.coord_apply, curvL] using this

theorem ricciAt_bilinear (x : M) :
    (∀ Y Y' Z : TangentSpace 𝓘(ℝ, E) x, cov.ricciAt x (Y + Y') Z = cov.ricciAt x Y Z + cov.ricciAt x Y' Z) ∧
    (∀ (r : ℝ) (Y Z : TangentSpace 𝓘(ℝ, E) x), cov.ricciAt x (r • Y) Z = r * cov.ricciAt x Y Z) ∧
    (∀ Y Z Z' : TangentSpace 𝓘(ℝ, E) x, cov.ricciAt x Y (Z + Z') = cov.ricciAt x Y Z + cov.ricciAt x Y Z') ∧
    (∀ (r : ℝ) (Y Z : TangentSpace 𝓘(ℝ, E) x), cov.ricciAt x Y (r • Z) = r * cov.ricciAt x Y Z) := by
  have hl := curvatureAt_linear cov x
  refine ⟨fun Y Y' Z => ?_, fun r Y Z => ?_, fun Y Z Z' => ?_, fun r Y Z => ?_⟩ <;>
    simp only [ricciAt_eq_trace_curvL]
  · rw [← map_add]; congr 1; ext v; exact hl.2.2.1 v Y Y' Z
  · rw [← smul_eq_mul, ← map_smul]; congr 1; ext v; exact hl.2.2.2.1 r v Y Z
  · rw [← map_add]; congr 1; ext v; exact hl.2.2.2.2.1 v Y Z Z'
  · rw [← smul_eq_mul, ← map_smul]; congr 1; ext v; exact hl.2.2.2.2.2 r v Y Z

/-- The Ricci tensor at `x` as a continuous bilinear form. -/
def ricciCLM (x : M) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    LinearMap.mk₂ ℝ (cov.ricciAt x) (ricciAt_bilinear cov x).1 (ricciAt_bilinear cov x).2.1
      (ricciAt_bilinear cov x).2.2.1 (ricciAt_bilinear cov x).2.2.2)

theorem ricciCLM_apply (x : M) (Y Z : TangentSpace 𝓘(ℝ, E) x) : ricciCLM cov x Y Z = cov.ricciAt x Y Z := rfl

/-- The scalar curvature is the `g`-trace of the Ricci tensor. -/
theorem scalarCurvatureAt_eq_traceG (hT : cov.torsion = 0) (hC : cov.IsMetricCompatible g) (x : M) :
    cov.scalarCurvatureAt g x = traceG (g.g x) (ricciCLM cov x) (nondegMetric_bilin_nondegenerate g x) := by
  rw [traceG_eq_gram _ _ _ (tb (E := E) x)]
  unfold Connection.scalarCurvatureAt
  simp only [ricciCLM_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ricciAt_symm_proved cov g hT hC]
  rfl

/-- **The scalar curvature in an orthonormal basis**: `S = Σᵢ sᵢ Ric(fᵢ, fᵢ)`. -/
theorem scalarCurvatureAt_frame (hT : cov.torsion = 0) (hC : cov.IsMetricCompatible g) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x : M) (f : Module.Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) (s : ι → ℝ) (hs : ∀ i, s i * s i = 1)
    (hf : ∀ i j, g.g x (f i) (f j) = if i = j then s i else 0) :
    cov.scalarCurvatureAt g x = ∑ i, s i * cov.ricciAt x (f i) (f i) := by
  rw [scalarCurvatureAt_eq_traceG cov g hT hC, traceG_eq_gram _ _ _ f]
  have hG : (Matrix.of fun i j => g.g x (f i) (f j)) = Matrix.diagonal s := by
    ext i j; simp [hf, Matrix.diagonal_apply]
  have hinv : (Matrix.diagonal s)⁻¹ = Matrix.diagonal s := by
    rw [Matrix.inv_eq_left_inv]
    rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; exact hs i
  rw [hG, hinv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp [ricciCLM_apply]

end Frame

/-- An orthonormal family (nonzero norms) is linearly independent. -/
theorem linearIndependent_of_orthonormal {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : V →L[ℝ] V →L[ℝ] ℝ) (v : ι → V) (s : ι → ℝ) (hs : ∀ i, s i ≠ 0)
    (hv : ∀ i j, B (v i) (v j) = if i = j then s i else 0) : LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (fun w => B w (v i)) hc
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul, hv,
    map_zero, zero_apply] at h
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at h
  simp only [ite_true] at h
  exact (mul_eq_zero.1 h).resolve_right (hs i)

section Constraints

variable [T2Space M] (cov : Connection 𝓘(ℝ, E) M) [LocallySmoothConnection cov]
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
  {g : NondegMetric 𝓘(ℝ, E) M} {φ : M → ℝ} {n : Π y : M, TangentSpace 𝓘(ℝ, E) y} {ε : ℝ} {x₀ : M}

open Hypersurface

/-- The orthonormal basis `(n, E_a)` of the tangent space at `x₀`. -/
def frameVec (n : Π y : M, TangentSpace 𝓘(ℝ, E) y) {d : ℕ} (Ef : Fin d → Π y : M, TangentSpace 𝓘(ℝ, E) y) (x₀ : M) :
    Fin (d + 1) → TangentSpace 𝓘(ℝ, E) x₀ :=
  Fin.cons (n x₀) fun a => Ef a x₀

theorem frameVec_orth (hn : IsUnitNormal g φ n ε x₀) {d : ℕ} {Ef : Fin d → Π y : M, TangentSpace 𝓘(ℝ, E) y}
    {η : Fin d → ℝ} (hEt : ∀ a, IsTangentNear φ (Ef a) x₀)
    (horth : ∀ a b, g.g x₀ (Ef a x₀) (Ef b x₀) = if a = b then η a else 0) (i j : Fin (d + 1)) :
    g.g x₀ (frameVec n Ef x₀ i) (frameVec n Ef x₀ j) = if i = j then (Fin.cons ε η : Fin (d + 1) → ℝ) i else 0 := by
  have hnn : g.g x₀ (n x₀) (n x₀) = ε := hn.norm.self_of_nhds
  have hnE : ∀ a, g.g x₀ (n x₀) (Ef a x₀) = 0 := fun a => ((hEt a).ortho hn).self_of_nhds
  have hEn : ∀ a, g.g x₀ (Ef a x₀) (n x₀) = 0 := fun a => (g.symm _ _ _).trans (hnE a)
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · simp [frameVec, hnn]
  · simp [frameVec, hnE, (Fin.succ_ne_zero b).symm]
  · simp [frameVec, hEn, Fin.succ_ne_zero a]
  · simp [frameVec, horth, Fin.succ_inj]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E) 2 M] [T2Space M] in
/-- `v = -v` forces `v = 0` in a tangent space. -/
theorem tangent_eq_zero_of_eq_neg {x : M} {v : TangentSpace 𝓘(ℝ, E) x} (h : v = -v) : v = 0 := by
  have h2 : (2 : ℝ) • v = 0 := by rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel v
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- The orthonormal basis `(n, E_a)` and its signs `(ε, η)`, from `d + 1 = dim`. -/
theorem exists_frame (hn : IsUnitNormal g φ n ε x₀) {d : ℕ} (hd : d + 1 = Module.finrank ℝ E)
    {Ef : Fin d → Π y : M, TangentSpace 𝓘(ℝ, E) y} {η : Fin d → ℝ} (hη : ∀ a, η a * η a = 1)
    (hEt : ∀ a, IsTangentNear φ (Ef a) x₀) (horth : ∀ a b, g.g x₀ (Ef a x₀) (Ef b x₀) = if a = b then η a else 0) :
    ∃ f : Module.Basis (Fin (d + 1)) ℝ (TangentSpace 𝓘(ℝ, E) x₀), (∀ i, f i = frameVec n Ef x₀ i) ∧
      (∀ i, (Fin.cons ε η : Fin (d + 1) → ℝ) i * (Fin.cons ε η : Fin (d + 1) → ℝ) i = 1) ∧
      ∀ i j, g.g x₀ (f i) (f j) = if i = j then (Fin.cons ε η : Fin (d + 1) → ℝ) i else 0 := by
  have hε2 : ε * ε = 1 := by rcases hn.eps with h | h <;> simp [h]
  have hs : ∀ i, (Fin.cons ε η : Fin (d + 1) → ℝ) i * (Fin.cons ε η : Fin (d + 1) → ℝ) i = 1 :=
    fun i => Fin.cases (by simpa using hε2) (fun a => by simpa using hη a) i
  have hs0 : ∀ i, (Fin.cons ε η : Fin (d + 1) → ℝ) i ≠ 0 := fun i h0 => by
    have := hs i; rw [h0] at this; simp at this
  have horthF := frameVec_orth hn hEt horth
  have hli := linearIndependent_of_orthonormal (g.g x₀) (frameVec n Ef x₀) _ hs0 horthF
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp only [Fintype.card_fin, hd]; rfl), fun i => ?_, hs, fun i j => ?_⟩
  · simp
  · simp only [coe_basisOfLinearIndependentOfCardEqFinrank]; exact horthF i j

/-- **The Hamiltonian constraint**: `2 G(n, n) = -ε R^D + K² - K_ab K^ab`, the traces in the orthonormal basis `(n, E_a)`. -/
theorem hamiltonian_constraint (h : cov.IsLeviCivita g) (hn : IsUnitNormal g φ n ε x₀) {d : ℕ}
    (hd : d + 1 = Module.finrank ℝ E) {Ef : Fin d → Π y : M, TangentSpace 𝓘(ℝ, E) y} {η : Fin d → ℝ}
    (hη : ∀ a, η a * η a = 1) (hEs : ∀ a, SmoothNear (Ef a) x₀) (hEt : ∀ a, IsTangentNear φ (Ef a) x₀)
    (horth : ∀ a b, g.g x₀ (Ef a x₀) (Ef b x₀) = if a = b then η a else 0) :
    2 * cov.einsteinField g x₀ (n x₀) (n x₀) =
      -ε * ∑ a, ∑ b, η a * η b * g.g x₀ (gaussCurv cov g n ε (Ef b) (Ef a) (Ef a) x₀) (Ef b x₀) +
        ((∑ a, η a * secondFF cov g n x₀ (Ef a x₀) (Ef a x₀)) ^ 2 -
          ∑ a, ∑ b, η a * η b * (secondFF cov g n x₀ (Ef a x₀) (Ef b x₀) * secondFF cov g n x₀ (Ef b x₀) (Ef a x₀))) := by
  obtain ⟨f, hfv, hs, hf⟩ := exists_frame hn hd hη hEt horth
  have hε2 : ε * ε = 1 := by rcases hn.eps with h | h <;> simp [h]
  have hR := ricciAt_frame cov g x₀ f _ hs hf
  have hS := scalarCurvatureAt_frame cov g h.1 h.2 x₀ f _ hs hf
  have hf0 : f 0 = n x₀ := by rw [hfv]; rfl
  have hfs : ∀ a, f a.succ = Ef a x₀ := fun a => by rw [hfv]; rfl
  have hnn0 : ∀ Z, cov.curvatureAt x₀ (n x₀) (n x₀) Z = 0 := fun Z => by
    exact tangent_eq_zero_of_eq_neg (curvatureAt_antisymm_left cov x₀ (n x₀) (n x₀) Z)
  set A : Fin d → ℝ := fun a => g.g x₀ (cov.curvatureAt x₀ (Ef a x₀) (n x₀) (n x₀)) (Ef a x₀)
  set C : Fin d → Fin d → ℝ := fun a b => g.g x₀ (cov.curvatureAt x₀ (Ef b x₀) (Ef a x₀) (Ef a x₀)) (Ef b x₀)
  set Kk : Fin d → Fin d → ℝ := fun a b => secondFF cov g n x₀ (Ef a x₀) (Ef b x₀)
  have hRnn : cov.ricciAt x₀ (n x₀) (n x₀) = ∑ a, η a * A a := by
    rw [hR, Fin.sum_univ_succ, hf0, hnn0]
    simp only [map_zero, zero_apply, mul_zero, zero_add, hfs, Fin.cons_succ, A]
  have hRaa : ∀ a, cov.ricciAt x₀ (Ef a x₀) (Ef a x₀) = ε * A a + ∑ b, η b * C a b := by
    intro a
    rw [hR, Fin.sum_univ_succ, hf0]
    simp only [hfs, Fin.cons_succ, Fin.cons_zero, C]
    congr 1
    have := riemannLowerAt_pair_symm cov g h.1 h.2 x₀ (n x₀) (Ef a x₀) (Ef a x₀) (n x₀)
    unfold Connection.riemannLowerAt at this
    rw [this]
  have hSS : cov.scalarCurvatureAt g x₀ = ε * cov.ricciAt x₀ (n x₀) (n x₀) + ∑ a, η a * cov.ricciAt x₀ (Ef a x₀) (Ef a x₀) := by
    rw [hS, Fin.sum_univ_succ, hf0]
    simp only [hfs, Fin.cons_succ, Fin.cons_zero]
  have hgnn : g.g x₀ (n x₀) (n x₀) = ε := hn.norm.self_of_nhds
  have hG : ∀ a b, C a b = g.g x₀ (gaussCurv cov g n ε (Ef b) (Ef a) (Ef a) x₀) (Ef b x₀) -
      ε * (Kk a a * Kk b b - Kk b a * Kk a b) := fun a b =>
    gauss_relation cov h.2 hn (hEs b) (hEs a) (hEs a) (hEt b) (hEt a) (hEt a) (hEt b)
  have hsum1 : ∑ a, η a * cov.ricciAt x₀ (Ef a x₀) (Ef a x₀) = ε * ∑ a, η a * A a + ∑ a, ∑ b, η a * η b * C a b := by
    simp only [hRaa, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => by ring
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have e1 : (∑ a, η a * Kk a a) ^ 2 = ∑ a, ∑ b, η a * η b * (Kk a a * Kk b b) := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hsum2 : ∑ a, ∑ b, η a * η b * C a b =
      ∑ a, ∑ b, η a * η b * g.g x₀ (gaussCurv cov g n ε (Ef b) (Ef a) (Ef a) x₀) (Ef b x₀) -
        ε * ((∑ a, η a * Kk a a) ^ 2 - ∑ a, ∑ b, η a * η b * (Kk a b * Kk b a)) := by
    rw [e1]
    calc ∑ a, ∑ b, η a * η b * C a b
        = ∑ a, ∑ b, (η a * η b * g.g x₀ (gaussCurv cov g n ε (Ef b) (Ef a) (Ef a) x₀) (Ef b x₀) -
            ε * (η a * η b * (Kk a a * Kk b b)) + ε * (η a * η b * (Kk a b * Kk b a))) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hG]; ring
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
          ring
  unfold Connection.einsteinField
  rw [hSS, hRnn, hsum1, hgnn, hsum2]
  linear_combination (-(2 * ∑ a, η a * A a - (∑ a, η a * Kk a a) ^ 2 +
    ∑ a, ∑ b, η a * η b * (Kk a b * Kk b a))) * hε2

/-- **The momentum constraint**: `G(n, E_c) = Σ_a η_a ((D_{E_a} K)(E_c, E_a) - (D_{E_c} K)(E_a, E_a))`. -/
theorem momentum_constraint (h : cov.IsLeviCivita g) (hn : IsUnitNormal g φ n ε x₀) {d : ℕ}
    (hd : d + 1 = Module.finrank ℝ E) {Ef : Fin d → Π y : M, TangentSpace 𝓘(ℝ, E) y} {η : Fin d → ℝ}
    (hη : ∀ a, η a * η a = 1) (hEs : ∀ a, SmoothNear (Ef a) x₀) (hEt : ∀ a, IsTangentNear φ (Ef a) x₀)
    (horth : ∀ a b, g.g x₀ (Ef a x₀) (Ef b x₀) = if a = b then η a else 0) (c : Fin d) :
    cov.einsteinField g x₀ (n x₀) (Ef c x₀) =
      ∑ a, η a * (covK cov g n ε (Ef a) (Ef c) (Ef a) x₀ - covK cov g n ε (Ef c) (Ef a) (Ef a) x₀) := by
  obtain ⟨f, hfv, hs, hf⟩ := exists_frame hn hd hη hEt horth
  have hR := ricciAt_frame cov g x₀ f _ hs hf
  have hf0 : f 0 = n x₀ := by rw [hfv]; rfl
  have hfs : ∀ a, f a.succ = Ef a x₀ := fun a => by rw [hfv]; rfl
  have hnn0 : ∀ Z, cov.curvatureAt x₀ (n x₀) (n x₀) Z = 0 := fun Z => by
    exact tangent_eq_zero_of_eq_neg (curvatureAt_antisymm_left cov x₀ (n x₀) (n x₀) Z)
  have hnE : g.g x₀ (n x₀) (Ef c x₀) = 0 := ((hEt c).ortho hn).self_of_nhds
  unfold Connection.einsteinField
  rw [hnE, mul_zero, sub_zero, hR, Fin.sum_univ_succ, hf0, hnn0]
  simp only [map_zero, zero_apply, mul_zero, zero_add, hfs, Fin.cons_succ]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hp := riemannLowerAt_pair_symm cov g h.1 h.2 x₀ (Ef a x₀) (n x₀) (Ef c x₀) (Ef a x₀)
  unfold Connection.riemannLowerAt at hp
  rw [hp, codazzi_relation cov h hn (hEs c) (hEs a) (hEs a) (hEt c) (hEt a) (hEt a)]
  ring

end Constraints

end Lightlike
