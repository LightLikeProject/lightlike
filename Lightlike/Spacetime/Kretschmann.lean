import Lightlike.Spacetime.ChartChange
import Lightlike.Spacetime.RicciContinuous
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Kretschmann scalar

`K = R_{abcd} R^{abcd}` of a coordinate metric (`kretschmann`), the simplest curvature invariant that does not
vanish for vacuum solutions. With the matrices `(R_{cd})^a_b = R^a_{bcd}` (`riemMat`),

`K = Σ_{c d c' d'} g^{cc'} g^{dd'} tr (g R_{cd} g⁻¹ R_{c'd'}ᵀ)`,

written as `tr ((g⁻¹ ⊗ g⁻¹)ᵀ T)` for the matrix `T_{(c,d),(c',d')} = tr (g R_{cd} g⁻¹ R_{c'd'}ᵀ)` on pairs of
indices (`kretMat`).

* `kretschmann_pullback`: `K` is chart-independent, `K'(y) = K(φ y)` for a chart change `φ`, from the tensor law
  of the Riemann tensor (`riemann_pullback`).
* `continuousOn_kretschmann`: `K` is continuous on the domain of a coordinate metric.

So a curvature invariant that is unbounded along a sequence of points cannot stay bounded in any other chart:
the sequence leaves every compact subset of the domain of every chart of an extension.
-/

open Matrix Finset
open scoped ContDiff Kronecker

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The Riemann tensor as a matrix in its first two indices: `(R_{cd})^a_b = R^a_{bcd}`. -/
def riemMat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (c d : Fin n) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun a b => riemann g a b c d x

/-- The matrix `T_{(c,d),(c',d')} = tr (g R_{cd} g⁻¹ R_{c'd'}ᵀ) = R_{abcd} R^{ab}{}_{c'd'}` on pairs of indices. -/
def kretMat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  fun p q => trace (g x * riemMat g p.1 p.2 x * (g x)⁻¹ * (riemMat g q.1 q.2 x)ᵀ)

/-- **The Kretschmann scalar** `K = R_{abcd} R^{abcd} = Σ g^{cc'} g^{dd'} tr (g R_{cd} g⁻¹ R_{c'd'}ᵀ)`. -/
def kretschmann (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  trace (((g x)⁻¹ ⊗ₖ (g x)⁻¹)ᵀ * kretMat g x)

/-- The Kretschmann scalar as a sum over index pairs. -/
lemma kretschmann_eq_sum (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    kretschmann g x = ∑ q : Fin n × Fin n, ∑ p : Fin n × Fin n,
      ((g x)⁻¹ p.1 q.1 * (g x)⁻¹ p.2 q.2) * kretMat g x p q := by
  simp only [kretschmann, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, transpose_apply,
    kroneckerMap_apply]

/-- **The Kretschmann scalar of a metric that is diagonal at `x`**:
`K = Σ_{c,d} g^{cc} g^{dd} Σ_{a,b} g_{aa} g^{bb} (R^a_{bcd})²`. -/
lemma kretschmann_diagonal (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) {D Di : Fin n → ℝ}
    (hD : g x = diagonal D) (hDi : (g x)⁻¹ = diagonal Di) :
    kretschmann g x = ∑ q : Fin n × Fin n, Di q.1 * Di q.2 *
      ∑ a, ∑ b, D a * Di b * riemann g a b q.1 q.2 x ^ 2 := by
  have hT : ∀ p q : Fin n × Fin n, kretMat g x p q =
      ∑ a, ∑ b, D a * riemann g a b p.1 p.2 x * Di b * riemann g a b q.1 q.2 x := by
    intro p q
    have hX : g x * riemMat g p.1 p.2 x * (g x)⁻¹ =
        Matrix.of fun a b => D a * riemann g a b p.1 p.2 x * Di b := by
      ext a b
      rw [hDi, hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
      rfl
    simp only [kretMat, hX, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, transpose_apply,
      Matrix.of_apply, riemMat]
  rw [kretschmann_eq_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_eq_single q]
  · rw [hDi, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hT]
    congr 1
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · intro p _ hp
    rw [hDi]
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hp (Prod.ext h1 h2)
      rw [Matrix.diagonal_apply_ne _ h2, mul_zero, zero_mul]
    · rw [Matrix.diagonal_apply_ne _ h1, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ q) h

section Pullback

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U V : Set (Fin n → ℝ)}
  {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-- The tensor law of the Riemann tensor in matrix form: `R'_{cd} = J⁻¹ (Σ_{κλ} J^κ_c J^λ_d R_{κλ}) J`. -/
lemma riemMat_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) {y : Fin n → ℝ}
    (hy : y ∈ V) (c d : Fin n) :
    riemMat (pullback g φ) c d y =
      (jac φ y)⁻¹ * (∑ q : Fin n × Fin n, (jac φ y q.1 c * jac φ y q.2 d) • riemMat g q.1 q.2 (φ y)) *
        jac φ y := by
  set J := jac φ y with hJdef
  have hJJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ (hφ.isUnit_det y hy)
  have h1 : J * riemMat (pullback g φ) c d y =
      (∑ q : Fin n × Fin n, (J q.1 c * J q.2 d) • riemMat g q.1 q.2 (φ y)) * J := by
    ext m b
    rw [Matrix.mul_apply]
    simp only [riemMat]
    rw [riemann_pullback hg hφ hy m b c d]
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
      Finset.sum_mul, riemMat]
    exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun κ _ =>
      Finset.sum_congr rfl fun l _ => by ring
  calc riemMat (pullback g φ) c d y = (J⁻¹ * J) * riemMat (pullback g φ) c d y := by
        rw [hJJ, Matrix.one_mul]
    _ = J⁻¹ * (J * riemMat (pullback g φ) c d y) := Matrix.mul_assoc _ _ _
    _ = _ := by rw [h1, Matrix.mul_assoc]

/-- A conjugation identity for the trace form `tr (G A G⁻¹ Bᵀ)`. -/
lemma trace_conj_form (J G A B : Matrix (Fin n) (Fin n) ℝ) (hJ : IsUnit J.det) :
    trace (Jᵀ * G * J * (J⁻¹ * A * J) * (Jᵀ * G * J)⁻¹ * (J⁻¹ * B * J)ᵀ) =
      trace (G * A * G⁻¹ * Bᵀ) := by
  have e1 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  have hJt : IsUnit Jᵀ.det := by rwa [Matrix.det_transpose]
  have e3 : Jᵀ⁻¹ * Jᵀ = 1 := Matrix.nonsing_inv_mul _ hJt
  have h1 : Jᵀ * G * J * (J⁻¹ * A * J) * (Jᵀ * G * J)⁻¹ * (J⁻¹ * B * J)ᵀ =
      Jᵀ * (G * ((J * J⁻¹) * (A * ((J * J⁻¹) * (G⁻¹ * ((Jᵀ⁻¹ * Jᵀ) * (Bᵀ * J⁻¹ᵀ))))))) := by
    simp only [Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [h1, e1, e3]
  simp only [Matrix.one_mul]
  rw [Matrix.trace_mul_comm, Matrix.transpose_nonsing_inv]
  have h2 : G * (A * (G⁻¹ * (Bᵀ * Jᵀ⁻¹))) * Jᵀ = G * A * G⁻¹ * Bᵀ := by
    simp only [Matrix.mul_assoc]
    rw [e3, Matrix.mul_one]
  rw [h2]

/-- The matrix `T` transforms by the Kronecker square of the Jacobian: `T' = (J ⊗ J)ᵀ T (J ⊗ J)`. -/
lemma kretMat_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) {y : Fin n → ℝ}
    (hy : y ∈ V) :
    kretMat (pullback g φ) y = (jac φ y ⊗ₖ jac φ y)ᵀ * kretMat g (φ y) * (jac φ y ⊗ₖ jac φ y) := by
  set J := jac φ y with hJdef
  have hJ : IsUnit J.det := hφ.isUnit_det y hy
  ext p q
  simp only [kretMat]
  rw [riemMat_pullback hg hφ hy, riemMat_pullback hg hφ hy, pullback_eq_mul, ← hJdef,
    trace_conj_form J (g (φ y)) _ _ hJ]
  simp only [Matrix.mul_apply, transpose_apply, kroneckerMap_apply, kretMat, Finset.mul_sum, Finset.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, Matrix.transpose_sum,
    Matrix.transpose_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun q1 _ => Finset.sum_congr rfl fun q2 _ => by ring

/-- **The Kretschmann scalar is chart-independent**: `K'(y) = K(φ y)`. -/
theorem kretschmann_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) {y : Fin n → ℝ}
    (hy : y ∈ V) : kretschmann (pullback g φ) y = kretschmann g (φ y) := by
  set J := jac φ y with hJdef
  have hJ : IsUnit J.det := hφ.isUnit_det y hy
  have e1 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  have hJt : IsUnit Jᵀ.det := by rwa [Matrix.det_transpose]
  have e3 : Jᵀ⁻¹ * Jᵀ = 1 := Matrix.nonsing_inv_mul _ hJt
  -- `J g'⁻¹ Jᵀ = g⁻¹`
  have hH : J * (pullback g φ y)⁻¹ * Jᵀ = (g (φ y))⁻¹ := by
    rw [pullback_eq_mul, ← hJdef]
    have : J * (Jᵀ * g (φ y) * J)⁻¹ * Jᵀ = (J * J⁻¹) * ((g (φ y))⁻¹ * (Jᵀ⁻¹ * Jᵀ)) := by
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]
    rw [this, e1, e3, Matrix.one_mul, Matrix.mul_one]
  have hK : (J ⊗ₖ J) * ((pullback g φ y)⁻¹ ⊗ₖ (pullback g φ y)⁻¹) * (J ⊗ₖ J)ᵀ =
      (g (φ y))⁻¹ ⊗ₖ (g (φ y))⁻¹ := by
    have ht : (J ⊗ₖ J)ᵀ = Jᵀ ⊗ₖ Jᵀ := by
      ext ⟨a, b⟩ ⟨c, d⟩; rfl
    rw [ht, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hH]
  unfold kretschmann
  rw [kretMat_pullback hg hφ hy, ← hJdef, ← hK]
  -- `tr (H'ᵀ (Ĵᵀ T Ĵ)) = tr ((Ĵ H' Ĵᵀ)ᵀ T)`
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end Pullback

/-- **The Kretschmann scalar of a coordinate metric is continuous on its domain.** -/
theorem continuousOn_kretschmann {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : IsCoordMetric g U) : ContinuousOn (kretschmann g) U := by
  have hG : ∀ i j, ContinuousOn (fun x => g x i j) U := fun i j => (hg.smooth i j).continuousOn
  have hGi : ∀ i j, ContinuousOn (fun x => (g x)⁻¹ i j) U := fun i j =>
    (contDiffOn_inv_entry hg.smooth (fun y hy => (hg.isUnit_det y hy).ne_zero) i j).continuousOn
  have hR : ∀ a b c d, ContinuousOn (fun x => riemMat g c d x a b) U := fun a b c d =>
    continuousOn_riemann hg a b c d
  have hT : ∀ p q, ContinuousOn (fun x => kretMat g x p q) U := by
    intro p q
    simp only [kretMat, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, transpose_apply]
    refine continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ => ?_
    refine ContinuousOn.mul ?_ (hR _ _ _ _)
    refine continuousOn_finsetSum _ fun e _ => ContinuousOn.mul ?_ (hGi _ _)
    exact continuousOn_finsetSum _ fun f _ => (hG _ _).mul (hR _ _ _ _)
  have h : kretschmann g = fun x => ∑ q : Fin n × Fin n, ∑ p : Fin n × Fin n,
      ((g x)⁻¹ p.1 q.1 * (g x)⁻¹ p.2 q.2) * kretMat g x p q := funext (kretschmann_eq_sum g)
  rw [h]
  exact continuousOn_finsetSum _ fun q _ => continuousOn_finsetSum _ fun p _ =>
    ((hGi _ _).mul (hGi _ _)).mul (hT p q)

end Lightlike
