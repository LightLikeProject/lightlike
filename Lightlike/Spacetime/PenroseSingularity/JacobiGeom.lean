import Lightlike.Spacetime.PenroseSingularity.JacobiCompat
import Lightlike.Spacetime.PenroseSingularity.JacobiDecomp
import Lightlike.Spacetime.PenroseSingularity.JacobiRiccati
import Lightlike.Spacetime.ConjugatePoints.Jacobi

/-!
# The Gram matrix of a family of Jacobi fields (G1-012, step D3b)

For `m` Jacobi fields `J i` with covariant derivatives `P i` along a geodesic `γ` (`IsJacobiOn`), the
matrices `Q = g(J_i, J_j)`, `C = g(P_i, J_j)` and the tidal matrix `ρ = g(R(J_i, w)w, J_j)` satisfy
`Q' = C + Cᵀ` and `C' = -ρ + Π`, `Π = g(P_i, P_j)`.
-/

open Set Filter Topology Matrix

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- `covDAlong` of a field with `W' = P - Γ(w, W)` is `P`. -/
theorem covDAlong_of_deriv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w W P : Fin n → ℝ) :
    (fun a => covDAlong g x w W (P - Lightlike.Geodesic.gammaApply g x w W) a) = P := by
  funext a
  simp [covDAlong, Lightlike.Geodesic.gammaApply]

/-- `covDAlong` of `P` with `P' = -Γ(w, P) - R(J, w)w` is `-R(J, w)w`. -/
theorem covDAlong_of_deriv' (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w J P : Fin n → ℝ) :
    (fun a => covDAlong g x w P (-Lightlike.Geodesic.gammaApply g x w P -
        Lightlike.Geodesic.riemannApply g x w J) a) = -Lightlike.Geodesic.riemannApply g x w J := by
  funext a
  simp [covDAlong, Lightlike.Geodesic.gammaApply]
  ring

theorem gpairAt_neg_left (x : Fin n → ℝ) (u v : Fin n → ℝ) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) :
    gpairAt g x (-u) v = -gpairAt g x u v := by
  simp [gpairAt, Finset.sum_neg_distrib]

theorem gpairAt_symm (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (u v : Fin n → ℝ) :
    gpairAt g x u v = gpairAt g x v u := by
  unfold gpairAt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : g x b a = g x a b := by
    have := congrFun (congrFun (hg.symm x hx) a) b
    simpa [Matrix.transpose_apply] using this
  rw [this]; ring

/-- The matrix `Q(t) = g(J_i, J_j)`. -/
def gramQ (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (γ : ℝ → Fin n → ℝ) (J : Fin m → ℝ → Fin n → ℝ)
    (t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => gpairAt g (γ t) (J i t) (J j t)

/-- The matrix `C(t) = g(P_i, J_j)`. -/
def gramC (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (γ : ℝ → Fin n → ℝ) (J P : Fin m → ℝ → Fin n → ℝ)
    (t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => gpairAt g (γ t) (P i t) (J j t)

/-- The matrix `Π(t) = g(P_i, P_j)`. -/
def gramP (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (γ : ℝ → Fin n → ℝ) (P : Fin m → ℝ → Fin n → ℝ)
    (t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => gpairAt g (γ t) (P i t) (P j t)

/-- The tidal matrix `ρ(t) = g(R(J_i, w)w, J_j)`. -/
def gramRho (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (γ w : ℝ → Fin n → ℝ)
    (J : Fin m → ℝ → Fin n → ℝ) (t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => gpairAt g (γ t) (Lightlike.Geodesic.riemannApply g (γ t) (w t) (J i t)) (J j t)

/-- **The derivative laws of the Gram matrices of Jacobi fields.** -/
theorem jacobi_gram_derivs (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ}
    {J P : Fin m → ℝ → Fin n → ℝ} {I : Set ℝ}
    (hJ : ∀ i, Lightlike.Geodesic.IsJacobiOn g γ w (J i) (P i) I) (hγU : ∀ t ∈ I, γ t ∈ U)
    {t : ℝ} (ht : t ∈ I) :
    (∀ i j, HasDerivAt (fun s => gramQ g γ J s i j)
      ((gramC g γ J P t + (gramC g γ J P t)ᵀ) i j) t) ∧
    (∀ i j, HasDerivAt (fun s => gramC g γ J P s i j)
      ((-(gramRho g γ w J t) + gramP g γ P t) i j) t) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  all_goals have hγ : HasDerivAt γ (w t) t := (hJ i).geodesic.pos t ht
  · have h := hasDerivAt_gpair hg hγ (hγU t ht) ((hJ i).deriv_field t ht) ((hJ j).deriv_field t ht)
    rw [covDAlong_of_deriv, covDAlong_of_deriv] at h
    refine h.congr_deriv ?_
    simp only [gramC, Matrix.add_apply, Matrix.of_apply, Matrix.transpose_apply]
    rw [gpairAt_symm hg (hγU t ht) (J i t) (P j t)]
  · have h := hasDerivAt_gpair hg hγ (hγU t ht) ((hJ i).deriv_cov t ht) ((hJ j).deriv_field t ht)
    rw [covDAlong_of_deriv', covDAlong_of_deriv] at h
    refine h.congr_deriv ?_
    simp only [gramP, gramRho, Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply]
    rw [gpairAt_neg_left]

theorem gpairAt_eq_toBilin (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u v : Fin n → ℝ) :
    gpairAt g x u v = Matrix.toBilin' (g x) u v := by
  rw [Matrix.toBilin'_apply']
  simp only [gpairAt, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **`Π = C Q⁻¹ Cᵀ`** for the Gram matrices of fields orthogonal to a null vector. -/
theorem gramP_eq (hg : Lightlike.IsCoordMetric g U) (hnm : n = m + 2) {x : Fin n → ℝ} (hx : x ∈ U)
    {w : Fin n → ℝ} (hww : gpairAt g x w w = 0) (hw0 : w ≠ 0) {J P : Fin m → Fin n → ℝ}
    (hwJ : ∀ i, gpairAt g x w (J i) = 0) (hwP : ∀ i, gpairAt g x w (P i) = 0)
    (hQ : (Matrix.of fun i j => gpairAt g x (J i) (J j)).det ≠ 0) :
    (Matrix.of fun i j => gpairAt g x (P i) (P j)) =
      (Matrix.of fun i k => gpairAt g x (P i) (J k)) * (Matrix.of fun i j => gpairAt g x (J i) (J j))⁻¹ *
        (Matrix.of fun i k => gpairAt g x (P i) (J k))ᵀ := by
  have hsymm : ∀ u v, Matrix.toBilin' (g x) u v = Matrix.toBilin' (g x) v u := fun u v => by
    rw [← gpairAt_eq_toBilin, ← gpairAt_eq_toBilin]; exact gpairAt_symm hg hx u v
  have hnd : (Matrix.toBilin' (g x)).Nondegenerate :=
    (Matrix.nondegenerate_toBilin'_iff).2
      (Matrix.nondegenerate_of_det_ne_zero (hg.isUnit_det x hx).ne_zero)
  have hdim : Module.finrank ℝ (Fin n → ℝ) = m + 2 := by simp [hnm]
  have := gram_P_eq (Matrix.toBilin' (g x)) hsymm hnd hdim J w (by rw [← gpairAt_eq_toBilin]; exact hww) hw0
    (fun i => by rw [← gpairAt_eq_toBilin]; exact hwJ i) (by simpa [gpairAt_eq_toBilin] using hQ) P
    (fun i => by rw [← gpairAt_eq_toBilin]; exact hwP i)
  simpa [gpairAt_eq_toBilin] using this

/-- `g(R(J, w)w, K) = Σ R_{bσμν} K^b w^σ J^μ w^ν`. -/
theorem gpair_riemannApply (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (w J K : Fin n → ℝ) :
    gpairAt g x (Lightlike.Geodesic.riemannApply g x w J) K =
      ∑ b, ∑ σ, ∑ μ, ∑ ν, Lightlike.riemannLower g b σ μ ν x * K b * w σ * J μ * w ν := by
  have hsymm : ∀ a b, g x a b = g x b a := fun a b => by
    have := congrFun (congrFun (hg.symm x hx) a) b
    simpa [Matrix.transpose_apply] using this.symm
  unfold gpairAt Lightlike.Geodesic.riemannApply Lightlike.riemannLower
  simp only [Finset.mul_sum, Finset.sum_mul]
  -- put the sum over `a` (resp. `l`) innermost on both sides
  have e1 : ∀ b, ∑ a, ∑ σ, ∑ μ, ∑ ν, g x a b * (Lightlike.riemann g a σ μ ν x * w σ * J μ * w ν) * K b =
      ∑ σ, ∑ μ, ∑ ν, ∑ a, g x a b * (Lightlike.riemann g a σ μ ν x * w σ * J μ * w ν) * K b := by
    intro b
    calc ∑ a, ∑ σ, ∑ μ, ∑ ν, g x a b * (Lightlike.riemann g a σ μ ν x * w σ * J μ * w ν) * K b
        = ∑ σ, ∑ a, ∑ μ, ∑ ν, g x a b * (Lightlike.riemann g a σ μ ν x * w σ * J μ * w ν) * K b :=
          Finset.sum_comm
      _ = ∑ σ, ∑ μ, ∑ a, ∑ ν, g x a b * (Lightlike.riemann g a σ μ ν x * w σ * J μ * w ν) * K b :=
          Finset.sum_congr rfl fun σ _ => Finset.sum_comm
      _ = ∑ σ, ∑ μ, ∑ ν, ∑ a, g x a b * (Lightlike.riemann g a σ μ ν x * w σ * J μ * w ν) * K b :=
          Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun μ _ => Finset.sum_comm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [e1 b]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun a _ => ?_
  rw [hsymm a b]; ring

/-- Quadruple sums can be permuted pairwise. -/
theorem sum4_pair_swap (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ b, ∑ σ, ∑ μ, ∑ ν, f b σ μ ν = ∑ μ, ∑ ν, ∑ b, ∑ σ, f b σ μ ν := by
  have h1 : ∑ b, ∑ σ, ∑ μ, ∑ ν, f b σ μ ν =
      ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, f p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type' (f := fun b σ => ∑ μ, ∑ ν, f b σ μ ν)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Fintype.sum_prod_type' (f := fun μ ν => f p.1 p.2 μ ν)]
  have h2 : ∑ μ, ∑ ν, ∑ b, ∑ σ, f b σ μ ν =
      ∑ q : Fin n × Fin n, ∑ p : Fin n × Fin n, f p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type' (f := fun μ ν => ∑ b, ∑ σ, f b σ μ ν)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Fintype.sum_prod_type' (f := fun b σ => f b σ q.1 q.2)]
  rw [h1, h2]
  exact Finset.sum_comm

/-- **The tidal matrix is symmetric** (pair symmetry of the Riemann tensor). -/
theorem gpair_riemannApply_symm (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (w J K : Fin n → ℝ) :
    gpairAt g x (Lightlike.Geodesic.riemannApply g x w J) K =
      gpairAt g x (Lightlike.Geodesic.riemannApply g x w K) J := by
  rw [gpair_riemannApply hg hx, gpair_riemannApply hg hx, sum4_pair_swap]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [hg.riemannLower_pair_symm hx b σ μ ν]
  ring

/-- **The Wronskian `C - Cᵀ` is constant**: `C` stays symmetric if it starts symmetric. -/
theorem gramC_symm (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ}
    {J P : Fin m → ℝ → Fin n → ℝ} {I : Set ℝ}
    (hJ : ∀ i, Lightlike.Geodesic.IsJacobiOn g γ w (J i) (P i) I) (hγU : ∀ t ∈ I, γ t ∈ U)
    {T : ℝ} (hT : Ico 0 T ⊆ I) (h0 : (gramC g γ J P 0)ᵀ = gramC g γ J P 0) :
    ∀ t ∈ Ico 0 T, (gramC g γ J P t)ᵀ = gramC g γ J P t := by
  intro t ht
  ext i j
  -- the function `s ↦ C_ij - C_ji` has zero derivative
  have hderiv : ∀ s ∈ Ico 0 t, HasDerivWithinAt (fun s => gramC g γ J P s i j - gramC g γ J P s j i) 0
      (Ici s) s := by
    intro s hs
    have hsI : s ∈ I := hT ⟨hs.1, lt_of_lt_of_le hs.2 ht.2.le⟩
    obtain ⟨-, hC⟩ := jacobi_gram_derivs hg hJ hγU hsI
    have h1 := hC i j
    have h2 := hC j i
    refine ((h1.sub h2).congr_deriv ?_).hasDerivWithinAt
    simp only [Matrix.add_apply, Matrix.neg_apply, gramRho, gramP, Matrix.of_apply]
    rw [gpair_riemannApply_symm hg (hγU s hsI) (w s) (J i s) (J j s),
      gpairAt_symm hg (hγU s hsI) (P i s) (P j s)]
    ring
  have hcont : ContinuousOn (fun s => gramC g γ J P s i j - gramC g γ J P s j i) (Icc 0 t) := by
    intro s hs
    have hsI : s ∈ I := hT ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    obtain ⟨-, hC⟩ := jacobi_gram_derivs hg hJ hγU hsI
    exact ((hC i j).sub (hC j i)).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont hderiv t ⟨ht.1, le_rfl⟩
  have h00 := congrFun (congrFun h0 i) j
  simp only [Matrix.transpose_apply] at h00 ⊢
  linarith

end Lightlike.Penrose
