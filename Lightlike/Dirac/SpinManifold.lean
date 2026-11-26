import Mathlib
import Lightlike.Dirac.SpinStructure
import Lightlike.Dirac.SpinConnection
import Lightlike.Dirac.RicciIdentity
import Lightlike.Spacetime.LeviCivita
import Lightlike.Dirac.SpinLiftDeriv

/-!
# The Dirac operator and the rough Laplacian on a manifold with a spin structure

For a spin structure `S` (atlas form, `SpinStructure`) of a metric `g` on `M` and a Clifford module
`ρ` on `V`, a *spinor field* is a family of local representations `ψ i : M → V`, one per frame,
related on overlaps by the spin lifts, `ψ i x = ρ (lift i j x) (ψ j x)`.  In the frame `i` the
spin connection has the coefficients of the Levi-Civita connection in that frame,
`ω x a b c = g(∇_{Fₐ} F_b, F_c)`, and

* `∇ₐ φ = ∂_{Fₐ} φ + ¼ ∑ ωₐ,ₖₗ γₖγₗ φ`,
* `D φ = ∑ₐ γₐ ∇ₐ φ`,
* `∇*∇ φ = -∑ₐ (∇ₐ∇ₐ φ - ∑ₖ ωₐ,ₐₖ ∇ₖ φ)`.

These are the manifold counterparts of `Lightlike.Dirac.nablaF`, `diracF` and `hessF`, which
treat a frame on `ℝⁿ`.  Only the atlas form of a spin structure is used; its equivalence with the
principal `Spin(n)`-bundle definition is not proved.

The operators are independent of the frame: `nablaV_lift`, `dirac_lift` and
`roughLaplacian_lift` show that they commute with the change of frame `ρ(lift i j)`, so
`SpinorField.dirac` and `SpinorField.roughLaplacian` are the Dirac operator and the rough
Laplacian on spinor fields.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter II, §4 (the Dirac operator), no
  equation number is claimed.
-/

open Bundle Manifold CliffordAlgebra Filter
open scoped Manifold ContDiff Matrix Topology

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- A **spinor field** for the spin structure `S` and the Clifford module `ρ`: local
representations `ψ i : M → V`, one per frame, with `ψ i x = ρ (lift i j x) (ψ j x)` on overlaps. -/
structure SpinorField {g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M} {ι : Type*}
    (S : SpinStructure g ι) (ρ : CliffordRep n V) where
  /-- The representation of the spinor field in the frame `i`. -/
  rep : ι → M → V
  transform : ∀ i j x, x ∈ S.dom i → x ∈ S.dom j → rep i x = ρ (S.lift i j x) (rep j x)

section Operators

variable {g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M} {ι : Type*} (S : SpinStructure g ι)

/-- The coefficients of the Levi-Civita connection in the frame `i` along a tangent vector `v` at
`x`: `ω_v b c = g(∇_v F_b, F_c)`, so that `∇_v F_b = ∑ₖ ω_v bk F_k` in an orthonormal frame. -/
noncomputable def SpinStructure.connFormV (i : ι) (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun b c => g.g x (leviCivita g (S.frame i b) x v) (S.frame i c x)

/-- The coefficients of the Levi-Civita connection in the frame `i` at `x`:
`ω x a b c = g(∇_{Fₐ} F_b, F_c)`, so that `∇_{Fₐ} F_b = ∑ₖ ωₐ,bk F_k` in an orthonormal frame. -/
noncomputable def SpinStructure.connForm (i : ι) (x : M) (a : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  S.connFormV i x (S.frame i a x)

variable (ρ : CliffordRep n V)

/-- The spinor covariant derivative along a tangent vector `v` at `x`, for a local representation
`φ : M → V` in the frame `i`: `∇_v φ = d_v φ + ¼ ∑ ω_v,kl γₖγₗ φ`. -/
noncomputable def SpinStructure.nablaV (i : ι) (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
    (φ : M → V) : V :=
  mvfderiv 𝓘(ℝ, Fin n → ℝ) φ x v + spinForm ρ (S.connFormV i x v) (φ x)

/-- The spinor covariant derivative along the frame vector `Fₐ`:
`∇ₐ φ = ∂_{Fₐ} φ + ¼ ∑ ωₐ,ₖₗ γₖγₗ φ`, for a local representation `φ : M → V` in the frame `i`. -/
noncomputable def SpinStructure.nabla (i : ι) (a : Fin n) (φ : M → V) (x : M) : V :=
  S.nablaV ρ i x (S.frame i a x) φ

/-- The **Dirac operator** in the frame `i`: `D φ = ∑ₐ γₐ ∇ₐ φ`. -/
noncomputable def SpinStructure.dirac (i : ι) (φ : M → V) (x : M) : V :=
  ∑ a, gam ρ a (S.nabla ρ i a φ x)

/-- The **rough Laplacian** `∇*∇` in the frame `i`:
`∇*∇ φ = -∑ₐ (∇ₐ∇ₐ φ - ∑ₖ ωₐ,ₐₖ ∇ₖ φ)`. -/
noncomputable def SpinStructure.roughLaplacian (i : ι) (φ : M → V) (x : M) : V :=
  -∑ a, (S.nabla ρ i a (fun y => S.nabla ρ i a φ y) x -
    ∑ k, S.connForm i x a a k • S.nabla ρ i k φ x)

end Operators

/-! ### Frame independence -/

section Independence

variable {g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M} {ι : Type*} (S : SpinStructure g ι)

/-- A covariant derivative commutes with finite sums of differentiable sections. -/
lemma cov_sum (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) {σ : Fin n → Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    {x : M} (h : ∀ b, SecDiffAt (σ b) x) :
    cov (∑ b, σ b) x = ∑ b, cov (σ b) x := by
  classical
  have key : ∀ s : Finset (Fin n), cov (∑ b ∈ s, σ b) x = ∑ b ∈ s, cov (σ b) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [CovariantDerivative.zero]
    | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      have hs : SecDiffAt (∑ b ∈ s, σ b) x := by
        have := MDifferentiableAt.sum_section (s := s) (t := σ) (x₀ := x) fun b _ => h b
        simpa [Finset.sum_fn] using this
      rw [cov.isCovariantDerivativeOn.add (h a) hs, ih]
  exact key Finset.univ

/-- The inverse frame change at a point of the overlap: `F_i a = ∑_c R_ca F_j c`. -/
lemma SpinStructure.frame_inv {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j) (a : Fin n) :
    S.frame i a x = ∑ c, S.rmat i j x c a • S.frame j c x := by
  have hc : ∀ c, S.frame j c x = ∑ b, S.rmat i j x c b • S.frame i b x := fun c => by
    rw [S.frame_change i j x hi hj c, S.rot_eq_rmat hi hj]
  simp only [hc, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hRR := S.transpose_mul_rmat hi hj
  have hδ : ∀ b, ∑ c, S.rmat i j x c a * S.rmat i j x c b = if a = b then 1 else 0 := by
    intro b
    have := congrFun (congrFun hRR a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  simp only [← Finset.sum_smul, hδ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- **Change of frame of the connection coefficients.**  On the overlap of the frames `i`, `j`,
with `R = rmat i j x` and `Ṙ = d_v R`: `ω^j_v = R ω^i_v Rᵀ + Ṙ Rᵀ`. -/
theorem SpinStructure.connFormV_change {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    S.connFormV j x v = S.rmat i j x * S.connFormV i x v * (S.rmat i j x)ᵀ +
      S.rmatD i j x v * (S.rmat i j x)ᵀ := by
  have hopen : IsOpen (S.dom i ∩ S.dom j) := (S.dom_open i).inter (S.dom_open j)
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ S.dom i ∧ y ∈ S.dom j := hopen.mem_nhds ⟨hi, hj⟩
  set σ : Fin n → Fin n → Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y :=
    fun a b => (S.rmatE i j a b) • S.frame i b
  have hσ : ∀ a b, SecDiffAt (σ a b) x := fun a b =>
    (S.mdiffAt_rmat hi hj a b).smul_section (S.mdiffAt_frame b hi)
  have hcov : ∀ a, leviCivita g (S.frame j a) x = ∑ b, leviCivita g (σ a b) x := by
    intro a
    rw [← cov_sum (leviCivita g) (hσ a)]
    refine (leviCivita g).isCovariantDerivativeOn.congr_of_eventuallyEq (S.mdiffAt_frame a hj) ?_
      Filter.univ_mem ?_
    · have := MDifferentiableAt.sum_section (s := Finset.univ) (t := σ a) (x₀ := x)
        fun b _ => hσ a b
      simpa [Finset.sum_fn] using this
    · filter_upwards [hnear] with y hy
      rw [S.frame_change i j y hy.1 hy.2 a, S.rot_eq_rmat hy.1 hy.2]
      simp [σ, Finset.sum_apply]
  have hleib : ∀ a b, leviCivita g (σ a b) x v =
      S.rmat i j x a b • leviCivita g (S.frame i b) x v +
        mvfderiv 𝓘(ℝ, Fin n → ℝ) (S.rmatE i j a b) x v • S.frame i b x := by
    intro a b
    rw [(leviCivita g).isCovariantDerivativeOn.leibniz (S.mdiffAt_frame b hi)
      (S.mdiffAt_rmat hi hj a b)]
    simp [mvfderiv]
  have hjc : ∀ c, S.frame j c x = ∑ d, S.rmat i j x c d • S.frame i d x := fun c => by
    rw [S.frame_change i j x hi hj c, S.rot_eq_rmat hi hj]
  ext a c
  simp only [SpinStructure.connFormV, hcov, ContinuousLinearMap.coe_sum', Finset.sum_apply, hleib,
    hjc, map_sum, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, S.frame_orthonormal i _ _ x hi, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_mul, Finset.mul_sum, SpinStructure.rmatD_apply]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  · refine Finset.sum_congr rfl fun b _ => ?_
    ring

variable (ρ : CliffordRep n V)

/-- Locality: `∇_v φ` at `x` depends only on `φ` near `x`. -/
lemma SpinStructure.nablaV_congr (i : ι) {x : M} (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
    {φ₁ φ₂ : M → V} (h : φ₁ =ᶠ[𝓝 x] φ₂) : S.nablaV ρ i x v φ₁ = S.nablaV ρ i x v φ₂ := by
  simp only [SpinStructure.nablaV, mvfderiv_congr_nhds' h, h.eq_of_nhds]

/-- `∇_v` is linear in the direction `v`. -/
lemma SpinStructure.nablaV_sum (i : ι) {x : M} (c : Fin n → ℝ)
    (v : Fin n → TangentSpace 𝓘(ℝ, Fin n → ℝ) x) (φ : M → V) :
    S.nablaV ρ i x (∑ k, c k • v k) φ = ∑ k, c k • S.nablaV ρ i x (v k) φ := by
  have hω : S.connFormV i x (∑ k, c k • v k) = ∑ k, c k • S.connFormV i x (v k) := by
    ext b d
    simp [SpinStructure.connFormV, map_sum, map_smul, Matrix.sum_apply]
  simp only [SpinStructure.nablaV, map_sum, map_smul, hω, spinForm_sum, spinForm_smul,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_add, Finset.sum_add_distrib]

/-- **Frame independence of the spin connection.**  On the overlap of the frames `i` and `j`, for
`φ` differentiable at `x`: `∇^i_v (ρ(lift) φ) = ρ(lift) (∇^j_v φ)`.  The local representations of
a spinor field in the two frames are related by `ρ(lift i j)`, so the covariant derivative is
well defined on spinor fields. -/
theorem SpinStructure.nablaV_lift {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) {φ : M → V} (hφ : FunDiffAt (n := n) φ x) :
    S.nablaV ρ i x v (fun y => ρ (S.lift i j y) (φ y)) =
      ρ (S.lift i j x) (S.nablaV ρ j x v φ) := by
  set R := S.rmat i j x
  set Rd : Matrix (Fin n) (Fin n) ℝ := S.rmatD i j x v
  set s := S.lift i j x
  have hs : s ∈ spinGroup (Qneg n) := (S.isLift i j x hi hj).1
  have hRR : Rᵀ * R = 1 := S.transpose_mul_rmat hi hj
  have hRR' : R * Rᵀ = 1 := S.rmat_mul_transpose hi hj
  have hlM : FunDiffAt (n := n) (fun y => ρ (S.lift i j y)) x := by
    letI := clNormedRing n
    letI := clNormedAlgebra n
    have hlsM := (S.contMDiffAt_lift hi hj).mdifferentiableAt (by simp)
    exact (LinearMap.toContinuousLinearMap ρ.toLinearMap).mdifferentiableAt.comp x hlsM
  -- conjugation of a spin bivector by the lift
  have hconjρ : ∀ A : Matrix (Fin n) (Fin n) ℝ,
      ρ s * spinForm ρ A = spinForm ρ (Rᵀ * A * R) * ρ s := by
    intro A
    have hc : s * clSpinForm A * star s = clSpinForm (Rᵀ * A * R) :=
      conj_clSpinForm hs (S.lift_conj hi hj) A
    have hss : star s * s = 1 := spinGroup.star_mul_self_of_mem hs
    have : s * clSpinForm A = clSpinForm (Rᵀ * A * R) * s := by
      rw [← hc, mul_assoc, hss, mul_one]
    have := congrArg ρ this
    simpa [map_mul, map_clSpinForm] using this
  have hω := S.connFormV_change hi hj v
  have hsum : Rᵀ * (R * S.connFormV i x v * Rᵀ + Rd * Rᵀ) * R = S.connFormV i x v + Rᵀ * Rd := by
    simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hRR, Matrix.mul_one]
  unfold SpinStructure.nablaV
  rw [mvfderiv_clm_apply _ _ x hlM hφ v, S.mvfderiv_rho_lift ρ hi hj v, hω, map_add]
  change spinForm ρ (Rᵀ * Rd) (ρ s (φ x)) + ρ s (mvfderiv 𝓘(ℝ, Fin n → ℝ) φ x v) +
      spinForm ρ (S.connFormV i x v) (ρ s (φ x)) =
    ρ s (mvfderiv 𝓘(ℝ, Fin n → ℝ) φ x v) + ρ s (spinForm ρ _ (φ x))
  have h2 := congrArg (fun L => L (φ x)) (hconjρ (R * S.connFormV i x v * Rᵀ + Rd * Rᵀ))
  simp only [mul_apply_eq_comp] at h2
  rw [h2, hsum, spinForm_add]
  simp only [ContinuousLinearMap.add_apply]
  abel

/-- **Frame independence of the Dirac operator.**  On the overlap of the frames `i` and `j`, for
`φ` differentiable at `x`: `D^i (ρ(lift) φ) = ρ(lift) (D^j φ)`. -/
theorem SpinStructure.dirac_lift {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    {φ : M → V} (hφ : FunDiffAt (n := n) φ x) :
    S.dirac ρ i (fun y => ρ (S.lift i j y) (φ y)) x = ρ (S.lift i j x) (S.dirac ρ j φ x) := by
  set R := S.rmat i j x
  set s := S.lift i j x
  have hs : s ∈ spinGroup (Qneg n) := (S.isLift i j x hi hj).1
  have hRR : Rᵀ * R = 1 := S.transpose_mul_rmat hi hj
  have hRR' : R * Rᵀ = 1 := S.rmat_mul_transpose hi hj
  -- `γₐ ρ(s) = ρ(s) ∑_d R_da γ_d`
  have hγ : ∀ a (w : V), gam ρ a (ρ s w) = ρ s (∑ d, R d a • gam ρ d w) := by
    intro a w
    have hss : s * star s = 1 := spinGroup.mul_star_self_of_mem hs
    have hc := star_conj_cgen hs hRR (S.lift_conj hi hj) a
    have : cgen a * s = s * ∑ d, R d a • cgen d := by
      rw [← hc, ← mul_assoc, ← mul_assoc, hss, one_mul]
    have := congrArg (fun c => ρ c w) this
    simpa [map_mul, map_sum, map_smul, gam, cgen] using this
  have hδ : ∀ c d, ∑ a, R c a * R d a = if c = d then 1 else 0 := by
    intro c d
    have := congrFun (congrFun hRR' c) d
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  unfold SpinStructure.dirac SpinStructure.nabla
  simp only [S.nablaV_lift ρ hi hj _ hφ]
  change ∑ a, gam ρ a (ρ s (S.nablaV ρ j x (S.frame i a x) φ)) =
    ρ s (∑ a, gam ρ a (S.nablaV ρ j x (S.frame j a x) φ))
  simp only [hγ]
  rw [← map_sum]
  congr 1
  simp only [S.frame_inv hi hj, S.nablaV_sum ρ j, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  -- `∑ₐ ∑_d R_da (R_ca γ_d ∇_c)`
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [Finset.sum_eq_single c]
  · rw [show ∑ a, R c a * R c a = 1 by simpa using hδ c c, one_smul]
  · intro d _ hdc
    rw [show ∑ a, R c a * R d a = 0 by simpa [Ne.symm hdc] using hδ c d, zero_smul]
  · simp

/-- The connection coefficients are linear in the direction. -/
lemma SpinStructure.connFormV_sum (i : ι) {x : M} (c : Fin n → ℝ)
    (v : Fin n → TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    S.connFormV i x (∑ k, c k • v k) = ∑ k, c k • S.connFormV i x (v k) := by
  ext b d
  simp [SpinStructure.connFormV, map_sum, map_smul, Matrix.sum_apply]

/-- A finite sum of differentiable functions is differentiable. -/
lemma mdiffAt_finsum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Fin n → M → F}
    {x : M} (h : ∀ b, FunDiffAt (n := n) (f b) x) : FunDiffAt (n := n) (fun y => ∑ b, f b y) x := by
  classical
  have key : ∀ s : Finset (Fin n), FunDiffAt (n := n) (fun y => ∑ b ∈ s, f b y) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using mdifferentiableAt_const
    | insert a s has ih =>
      simp only [Finset.sum_insert has]
      exact (h a).add ih
  exact key Finset.univ

/-- The trace identity behind the frame independence of `∇*∇`: with `D a = d_{F_i a} R`,
`∑ₐ (D a)_{ca} - ∑ₐ ∑ₖ ω^i_{aak} R_{ck} = -∑ₑ ω^j_{eec}`. -/
lemma SpinStructure.trace_change {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    (c : Fin n) :
    ∑ a, mvfderiv 𝓘(ℝ, Fin n → ℝ) (S.rmatE i j c a) x (S.frame i a x) -
      ∑ a, ∑ k, S.connForm i x a a k * S.rmat i j x c k = -∑ e, S.connForm j x e e c := by
  set R := S.rmat i j x
  set D : Fin n → Matrix (Fin n) (Fin n) ℝ := fun a => S.rmatD i j x (S.frame i a x)
  have hRR : Rᵀ * R = 1 := S.transpose_mul_rmat hi hj
  have hRR' : R * Rᵀ = 1 := S.rmat_mul_transpose hi hj
  have hδ : ∀ a b, ∑ e, R e a * R e b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hRR a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hδ' : ∀ a b, ∑ e, R a e * R b e = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hRR' a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hskew : ∀ a p q, (Rᵀ * D a) p q = -(Rᵀ * D a) q p := fun a =>
    S.rmat_deriv_skew hi hj (S.frame i a x)
  have hFj : ∀ e, S.frame j e x = ∑ a, R e a • S.frame i a x := fun e => by
    rw [S.frame_change i j x hi hj e, S.rot_eq_rmat hi hj]
  have hD : ∀ e, S.rmatD i j x (S.frame j e x) = ∑ a, R e a • D a := by
    intro e
    ext p q
    simp [hFj e, map_sum, map_smul, D, Matrix.sum_apply]
  have hω : ∀ e, S.connForm j x e = R * (∑ a, R e a • S.connForm i x a) * Rᵀ +
      (∑ a, R e a • D a) * Rᵀ := by
    intro e
    unfold SpinStructure.connForm
    rw [S.connFormV_change hi hj, hD e, hFj e, S.connFormV_sum]
  -- the first part of `∑ₑ ω^j_eec`
  have hA : ∑ e, (R * (∑ a, R e a • S.connForm i x a) * Rᵀ) e c =
      ∑ a, ∑ k, S.connForm i x a a k * R c k := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    -- ∑ e ∑ k ∑ b ∑ a R e b * (R e a * ω a b k) * R c k
    calc ∑ e, ∑ k, ∑ b, ∑ a, R e b * (R e a * S.connForm i x a b k) * R c k
        = ∑ k, ∑ b, ∑ a, (∑ e, R e b * R e a) * S.connForm i x a b k * R c k := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun e _ => ?_
          ring
      _ = ∑ a, ∑ k, S.connForm i x a a k * R c k := by
          simp only [hδ, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
          rw [Finset.sum_comm]
  -- the second part
  have hB : ∑ e, ((∑ a, R e a • D a) * Rᵀ) e c = -∑ a, D a c a := by
    have h1 : ∀ a, ∑ e, R e a * ∑ b, D a e b * R c b = -D a c a := by
      intro a
      have h2 : ∑ e, R e a * ∑ b, D a e b * R c b = ∑ b, (Rᵀ * D a) a b * R c b := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
        ring
      rw [h2]
      simp only [hskew a a, neg_mul, Finset.sum_neg_distrib, Matrix.mul_apply, Matrix.transpose_apply,
        Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum, mul_comm (D a _ a)]
      simp only [← mul_assoc, ← Finset.sum_mul]
      rw [Finset.sum_eq_single c]
      · rw [show ∑ b, R c b * R c b = 1 by simpa using hδ' c c, one_mul]
      · intro e _ hec
        rw [show ∑ b, R e b * R c b = 0 by simpa [hec] using hδ' e c, zero_mul]
      · simp
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [← Finset.sum_neg_distrib]
    simp only [← h1, Finset.mul_sum]
    calc _ = ∑ e, ∑ a, ∑ k, R e a * D a e k * R c k :=
          Finset.sum_congr rfl fun e _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ =>
            Finset.sum_congr rfl fun k _ => ?_
          ring
  have : ∑ e, S.connForm j x e e c = ∑ a, ∑ k, S.connForm i x a a k * R c k - ∑ a, D a c a := by
    simp only [hω, Matrix.add_apply, Finset.sum_add_distrib, hA, hB, sub_eq_add_neg]
  rw [this]
  simp [D]

/-- **Frame independence of the rough Laplacian.**  On the overlap of the frames `i` and `j`, for
`φ` differentiable near `x` whose covariant derivatives `∇^j_c φ` are differentiable at `x`:
`(∇*∇)^i (ρ(lift) φ) = ρ(lift) ((∇*∇)^j φ)`. -/
theorem SpinStructure.roughLaplacian_lift {i j : ι} {x : M} (hi : x ∈ S.dom i)
    (hj : x ∈ S.dom j) {φ : M → V} (hφ : ∀ᶠ y in 𝓝 x, FunDiffAt (n := n) φ y)
    (hnf : ∀ c, FunDiffAt (n := n) (fun y => S.nabla ρ j c φ y) x) :
    S.roughLaplacian ρ i (fun y => ρ (S.lift i j y) (φ y)) x =
      ρ (S.lift i j x) (S.roughLaplacian ρ j φ x) := by
  set R := S.rmat i j x
  set L := S.lift i j x
  have hnear : ∀ᶠ y in 𝓝 x, (y ∈ S.dom i ∧ y ∈ S.dom j) ∧ FunDiffAt (n := n) φ y :=
    (show ∀ᶠ y in 𝓝 x, y ∈ S.dom i ∧ y ∈ S.dom j from
      ((S.dom_open i).inter (S.dom_open j)).mem_nhds ⟨hi, hj⟩).and hφ
  set χ : Fin n → M → V := fun a y => ∑ c, (S.rmatE i j c a) y • S.nabla ρ j c φ y
  have hpt : ∀ y, y ∈ S.dom i → y ∈ S.dom j → FunDiffAt (n := n) φ y → ∀ a,
      S.nabla ρ i a (fun z => ρ (S.lift i j z) (φ z)) y = ρ (S.lift i j y) (χ a y) := by
    intro y hyi hyj hyφ a
    unfold SpinStructure.nabla
    rw [S.nablaV_lift ρ hyi hyj _ hyφ, S.frame_inv hyi hyj a, S.nablaV_sum ρ j]
    rfl
  have hΨ : ∀ a, (fun y => S.nabla ρ i a (fun z => ρ (S.lift i j z) (φ z)) y) =ᶠ[𝓝 x]
      fun y => ρ (S.lift i j y) (χ a y) := by
    intro a
    filter_upwards [hnear] with y hy
    exact hpt y hy.1.1 hy.1.2 hy.2 a
  have hφx : FunDiffAt (n := n) φ x := hφ.self_of_nhds
  have hχ : ∀ a, FunDiffAt (n := n) (χ a) x := fun a =>
    mdiffAt_finsum fun c => (S.mdiffAt_rmat hi hj c a).smul (hnf c)
  -- the second derivatives
  have hsecond : ∀ a, S.nabla ρ i a (fun y => S.nabla ρ i a (fun z => ρ (S.lift i j z) (φ z)) y) x =
      ρ L (∑ c, mvfderiv 𝓘(ℝ, Fin n → ℝ) (S.rmatE i j c a) x (S.frame i a x) •
          S.nabla ρ j c φ x +
        ∑ c, ∑ d, (R c a * R d a) • S.nabla ρ j d (fun y => S.nabla ρ j c φ y) x) := by
    intro a
    have e1 : S.nabla ρ i a (fun y => S.nabla ρ i a (fun z => ρ (S.lift i j z) (φ z)) y) x =
        ρ L (S.nablaV ρ j x (S.frame i a x) (χ a)) := by
      change S.nablaV ρ i x (S.frame i a x)
          (fun y => S.nabla ρ i a (fun z => ρ (S.lift i j z) (φ z)) y) = _
      rw [S.nablaV_congr ρ i _ (hΨ a), S.nablaV_lift ρ hi hj _ (hχ a)]
    rw [e1]
    congr 1
    -- `∇_u χ = ∑_c (d_u R_ca) ∇_c φ + R_ca ∇_u ∇_c φ`
    have hd : mvfderiv 𝓘(ℝ, Fin n → ℝ) (χ a) x (S.frame i a x) =
        ∑ c, (mvfderiv 𝓘(ℝ, Fin n → ℝ) (S.rmatE i j c a) x (S.frame i a x) •
          S.nabla ρ j c φ x + R c a • mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => S.nabla ρ j c φ y) x
            (S.frame i a x)) := by
      have hm : ∀ c, FunDiffAt (n := n) (fun y => (S.rmatE i j c a) y • S.nabla ρ j c φ y) x := fun c =>
        (S.mdiffAt_rmat hi hj c a).smul (hnf c)
      rw [show χ a = fun y => ∑ c, (S.rmatE i j c a) y • S.nabla ρ j c φ y from rfl,
        mvfderiv_finsum hm]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [show (fun y => (S.rmatE i j c a) y • S.nabla ρ j c φ y) =
        (S.rmatE i j c a) • (fun y => S.nabla ρ j c φ y) from rfl,
        mvfderiv_smul (S.mdiffAt_rmat hi hj c a) (hnf c)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [add_comm]
      rfl
    have hu : ∀ c, S.nablaV ρ j x (S.frame i a x) (fun y => S.nabla ρ j c φ y) =
        ∑ d, R d a • S.nabla ρ j d (fun y => S.nabla ρ j c φ y) x := by
      intro c
      rw [S.frame_inv hi hj a, S.nablaV_sum ρ j]
      rfl
    unfold SpinStructure.nablaV
    rw [hd]
    have hχx : χ a x = ∑ c, R c a • S.nabla ρ j c φ x := rfl
    rw [hχx, map_sum]
    simp only [map_smul, Finset.sum_add_distrib]
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← smul_add]
    have := hu c
    unfold SpinStructure.nablaV at this
    rw [this, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_smul, mul_comm]
  -- the first derivatives in frame `i`
  have hfirst : ∀ k, S.nabla ρ i k (fun z => ρ (S.lift i j z) (φ z)) x =
      ρ L (∑ c, R c k • S.nabla ρ j c φ x) := fun k => hpt x hi hj hφx k
  have hδ : ∀ c d, ∑ a, R c a * R d a = if c = d then 1 else 0 := by
    intro c d
    have := congrFun (congrFun (S.rmat_mul_transpose hi hj) c) d
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have htr := S.trace_change hi hj
  unfold SpinStructure.roughLaplacian
  simp only [hsecond, hfirst, ← map_smul, ← map_sum, ← map_sub, ← map_neg]
  congr 1
  -- an identity in `V`
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, neg_sub]
  have hdd : ∑ a, ∑ c, ∑ d, (R c a * R d a) • S.nabla ρ j d (fun y => S.nabla ρ j c φ y) x =
      ∑ c, S.nabla ρ j c (fun y => S.nabla ρ j c φ y) x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hδ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hlin : ∑ a, ∑ c, mvfderiv 𝓘(ℝ, Fin n → ℝ) (S.rmatE i j c a) x (S.frame i a x) •
        S.nabla ρ j c φ x - ∑ a, ∑ k, S.connForm i x a a k • ∑ c, R c k • S.nabla ρ j c φ x =
      -∑ c, ∑ k, S.connForm j x c c k • S.nabla ρ j k φ x := by
    have e1 : ∑ a, ∑ k, S.connForm i x a a k • ∑ c, R c k • S.nabla ρ j c φ x =
        ∑ c, (∑ a, ∑ k, S.connForm i x a a k * R c k) • S.nabla ρ j c φ x := by
      simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
      calc _ = ∑ a, ∑ c, ∑ k, (S.connForm i x a a k * R c k) • S.nabla ρ j c φ x :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    have e2 : ∑ a, ∑ c, mvfderiv 𝓘(ℝ, Fin n → ℝ) (S.rmatE i j c a) x (S.frame i a x) •
        S.nabla ρ j c φ x = ∑ c, (∑ a, mvfderiv 𝓘(ℝ, Fin n → ℝ) (S.rmatE i j c a) x
          (S.frame i a x)) • S.nabla ρ j c φ x := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    have e3 : ∑ c, ∑ k, S.connForm j x c c k • S.nabla ρ j k φ x =
        ∑ k, (∑ c, S.connForm j x c c k) • S.nabla ρ j k φ x := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    rw [e1, e2, e3, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← sub_smul, htr c, neg_smul]
  rw [hdd]
  linear_combination (norm := module) -hlin

end Independence

/-! ### The Dirac operator on spinor fields -/

section Field

variable {g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M} {ι : Type*} {S : SpinStructure g ι}
  {ρ : CliffordRep n V}

/-- The local representations of a spinor field in two frames agree up to `ρ(lift)` near every
point of the overlap. -/
lemma SpinorField.rep_eventuallyEq (ψ : SpinorField S ρ) {i j : ι} {x : M} (hi : x ∈ S.dom i)
    (hj : x ∈ S.dom j) :
    ψ.rep i =ᶠ[𝓝 x] fun y => ρ (S.lift i j y) (ψ.rep j y) := by
  filter_upwards [((S.dom_open i).inter (S.dom_open j)).mem_nhds ⟨hi, hj⟩] with y hy
  exact ψ.transform i j y hy.1 hy.2

/-- **The Dirac operator on spinor fields.**  For a spinor field whose local representations are
differentiable on their frame domains, the frame-wise Dirac operators `S.dirac ρ i (ψ.rep i)` form
again a spinor field: they transform with `ρ(lift)` (`SpinStructure.dirac_lift`). -/
noncomputable def SpinorField.dirac (ψ : SpinorField S ρ)
    (hψ : ∀ i x, x ∈ S.dom i → FunDiffAt (n := n) (ψ.rep i) x) : SpinorField S ρ where
  rep i := S.dirac ρ i (ψ.rep i)
  transform i j x hi hj := by
    have h := ψ.rep_eventuallyEq hi hj
    have : S.dirac ρ i (ψ.rep i) x = S.dirac ρ i (fun y => ρ (S.lift i j y) (ψ.rep j y)) x := by
      unfold SpinStructure.dirac SpinStructure.nabla
      simp only [S.nablaV_congr ρ i _ h]
    rw [this, S.dirac_lift ρ hi hj (hψ j x hj)]

/-- **The rough Laplacian on spinor fields.**  For a spinor field whose local representations are
differentiable on their frame domains and have differentiable covariant derivatives there, the
frame-wise rough Laplacians form again a spinor field (`SpinStructure.roughLaplacian_lift`). -/
noncomputable def SpinorField.roughLaplacian (ψ : SpinorField S ρ)
    (hψ : ∀ i x, x ∈ S.dom i → FunDiffAt (n := n) (ψ.rep i) x)
    (hψ' : ∀ i c x, x ∈ S.dom i → FunDiffAt (n := n) (fun y => S.nabla ρ i c (ψ.rep i) y) x) :
    SpinorField S ρ where
  rep i := S.roughLaplacian ρ i (ψ.rep i)
  transform i j x hi hj := by
    have h := ψ.rep_eventuallyEq hi hj
    have hφ : ∀ᶠ y in 𝓝 x, FunDiffAt (n := n) (ψ.rep j) y := by
      filter_upwards [(S.dom_open j).mem_nhds hj] with y hy
      exact hψ j y hy
    -- `∇^i ψ_i = ∇^i (ρ(lift) ψ_j)` near `x`, so the second derivatives agree at `x`
    have h1 : ∀ a, (fun y => S.nabla ρ i a (ψ.rep i) y) =ᶠ[𝓝 x]
        fun y => S.nabla ρ i a (fun z => ρ (S.lift i j z) (ψ.rep j z)) y := by
      intro a
      filter_upwards [((S.dom_open i).inter (S.dom_open j)).mem_nhds ⟨hi, hj⟩] with y hy
      unfold SpinStructure.nabla
      exact S.nablaV_congr ρ i _ (ψ.rep_eventuallyEq hy.1 hy.2)
    have : S.roughLaplacian ρ i (ψ.rep i) x =
        S.roughLaplacian ρ i (fun y => ρ (S.lift i j y) (ψ.rep j y)) x := by
      unfold SpinStructure.roughLaplacian
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      have e1 : S.nabla ρ i a (fun y => S.nabla ρ i a (ψ.rep i) y) x =
          S.nabla ρ i a (fun y => S.nabla ρ i a (fun z => ρ (S.lift i j z) (ψ.rep j z)) y) x := by
        unfold SpinStructure.nabla
        exact S.nablaV_congr ρ i _ (h1 a)
      have e2 : ∀ k, S.nabla ρ i k (ψ.rep i) x =
          S.nabla ρ i k (fun z => ρ (S.lift i j z) (ψ.rep j z)) x := fun k => by
        unfold SpinStructure.nabla
        exact S.nablaV_congr ρ i _ h
      simp only [e1, e2]
    rw [this, S.roughLaplacian_lift ρ hi hj hφ fun c => hψ' j c x hj]

end Field

/-! ### Trust check: the flat case -/

/-- **Flat trust check.**  For the Euclidean metric on `ℝⁿ` and its standard global frame the
connection coefficients vanish, so `∇` is the plain derivative and `D` is the flat Dirac
operator.  The wrong value `connForm ≠ 0` would show a mistake in the definition of `connForm`. -/
theorem euclideanSpinStructure_connForm (x : Fin n → ℝ) (a : Fin n) :
    (euclideanSpinStructure n).connForm () x a = 0 := by
  funext b c
  have hX := (euclideanSpinStructure n).mdiffAt_frame (i := ()) a (y := x) trivial
  have hY := (euclideanSpinStructure n).mdiffAt_frame (i := ()) b (y := x) trivial
  have hZ := (euclideanSpinStructure n).mdiffAt_frame (i := ()) c (y := x) trivial
  unfold SpinStructure.connForm SpinStructure.connFormV
  rw [g_leviCivita _ hX hY hZ]
  have hc : ∀ p q : Fin n, gpair (euclideanMetric n) ((euclideanSpinStructure n).frame () p)
      ((euclideanSpinStructure n).frame () q) = fun _ => if p = q then (1 : ℝ) else 0 := by
    intro p q
    funext y
    exact (euclideanSpinStructure n).frame_orthonormal () p q y trivial
  have hb : ∀ p q : Fin n, VectorField.mlieBracket 𝓘(ℝ, Fin n → ℝ) ((euclideanSpinStructure n).frame () p)
      ((euclideanSpinStructure n).frame () q) x = 0 := by
    intro p q
    rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin]
    change VectorField.lieBracketWithin ℝ (fun _ : Fin n → ℝ => (Pi.single p 1 : Fin n → ℝ))
      (fun _ => (Pi.single q 1 : Fin n → ℝ)) Set.univ x = 0
    simp [VectorField.lieBracketWithin_univ, VectorField.lieBracket]
  unfold koszul
  simp only [hc, mvfderiv_const, hb, map_zero, zero_apply, sub_zero, add_zero,
    zero_div, Matrix.zero_apply]

end Lightlike.Dirac
