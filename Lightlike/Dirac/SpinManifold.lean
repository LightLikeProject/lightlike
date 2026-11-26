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

The operators are independent of the frame: `nablaV_lift` and `dirac_lift` show that they
commute with the change of frame `ρ(lift i j)`, so `SpinorField.dirac` is the Dirac operator on
spinor fields.

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
    {x : M} (h : ∀ b, MDiffAt (T% (σ b)) x) :
    cov (∑ b, σ b) x = ∑ b, cov (σ b) x := by
  classical
  have key : ∀ s : Finset (Fin n), cov (∑ b ∈ s, σ b) x = ∑ b ∈ s, cov (σ b) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [CovariantDerivative.zero]
    | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      have hs : MDiffAt (T% (∑ b ∈ s, σ b)) x := by
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
      (fun a b => mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => S.rmat i j y a b) x v) * (S.rmat i j x)ᵀ := by
  have hopen : IsOpen (S.dom i ∩ S.dom j) := (S.dom_open i).inter (S.dom_open j)
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ S.dom i ∧ y ∈ S.dom j := hopen.mem_nhds ⟨hi, hj⟩
  set σ : Fin n → Fin n → Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y :=
    fun a b => (fun z => S.rmat i j z a b) • S.frame i b
  have hσ : ∀ a b, MDiffAt (T% (σ a b)) x := fun a b =>
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
        mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => S.rmat i j y a b) x v • S.frame i b x := by
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
    Finset.mem_univ, ite_true, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
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
    simp [SpinStructure.connFormV, map_sum, map_smul, Finset.sum_apply]
  simp only [SpinStructure.nablaV, map_sum, map_smul, hω, spinForm_sum, spinForm_smul,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_add, Finset.sum_add_distrib]

/-- **Frame independence of the spin connection.**  On the overlap of the frames `i` and `j`, for
`φ` differentiable at `x`: `∇^i_v (ρ(lift) φ) = ρ(lift) (∇^j_v φ)`.  The local representations of
a spinor field in the two frames are related by `ρ(lift i j)`, so the covariant derivative is
well defined on spinor fields. -/
theorem SpinStructure.nablaV_lift {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) {φ : M → V} (hφ : MDiffAt φ x) :
    S.nablaV ρ i x v (fun y => ρ (S.lift i j y) (φ y)) =
      ρ (S.lift i j x) (S.nablaV ρ j x v φ) := by
  set R := S.rmat i j x
  set Rd : Matrix (Fin n) (Fin n) ℝ :=
    fun a b => mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => S.rmat i j y a b) x v
  set s := S.lift i j x
  have hs : s ∈ spinGroup (Qneg n) := (S.isLift i j x hi hj).1
  have hRR : Rᵀ * R = 1 := S.transpose_mul_rmat hi hj
  have hRR' : R * Rᵀ = 1 := S.rmat_mul_transpose hi hj
  have hlM : MDiffAt (fun y => ρ (S.lift i j y)) x := by
    letI := clNormedRing n
    letI := clNormedAlgebra n
    have hlsM := (S.contMDiffAt_lift hi hj).mdifferentiableAt (by simp)
    exact (LinearMap.toContinuousLinearMap ρ.toLinearMap).mdifferentiableAt.comp x hlsM
  -- conjugation of a spin bivector by the lift
  have hconjρ : ∀ A : Matrix (Fin n) (Fin n) ℝ,
      ρ s * spinForm ρ A = spinForm ρ (Rᵀ * A * R) * ρ s := by
    intro A
    have hc := conj_clSpinForm hs (S.lift_conj hi hj) A
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
  simp only [ContinuousLinearMap.mul_apply_eq_comp, ContinuousLinearMap.comp_apply] at h2
  rw [h2, hsum, spinForm_add]
  simp only [ContinuousLinearMap.add_apply]
  abel

/-- **Frame independence of the Dirac operator.**  On the overlap of the frames `i` and `j`, for
`φ` differentiable at `x`: `D^i (ρ(lift) φ) = ρ(lift) (D^j φ)`. -/
theorem SpinStructure.dirac_lift {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    {φ : M → V} (hφ : MDiffAt φ x) :
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
  simp only [S.nablaV_lift ρ hi hj _ hφ, hγ]
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
    (hψ : ∀ i x, x ∈ S.dom i → MDiffAt (ψ.rep i) x) : SpinorField S ρ where
  rep i := S.dirac ρ i (ψ.rep i)
  transform i j x hi hj := by
    have h := ψ.rep_eventuallyEq hi hj
    have : S.dirac ρ i (ψ.rep i) x = S.dirac ρ i (fun y => ρ (S.lift i j y) (ψ.rep j y)) x := by
      unfold SpinStructure.dirac SpinStructure.nabla
      simp only [S.nablaV_congr ρ i _ h]
    rw [this, S.dirac_lift ρ hi hj (hψ j x hj)]

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
