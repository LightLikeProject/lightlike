import Lightlike.Spacetime.PenroseSingularity.JacobiGeom
import Lightlike.Spacetime.NullFrameExpansion

/-!
# The screen trace of the tidal matrix is the Ricci curvature (G1-012, step D3b)

For `m` screen vectors `J i ⊥ w` (`w` null) with invertible Gram matrix `Q`, in a space of dimension
`m + 2`, `tr (Q⁻¹ ρ) = Ric(w, w)` for the tidal matrix `ρ_ij = g(R(J_i, w)w, J_j)`.
-/

open Module Matrix Set

noncomputable section

namespace Lightlike.Penrose

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {m : ℕ}

/-- **A null vector dual to `w` and orthogonal to the screen.** -/
theorem exists_null_dual (B : LinearMap.BilinForm ℝ V) (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (J : Fin m → V) (w : V) (hww : B w w = 0) (hw0 : w ≠ 0)
    (hwJ : ∀ i, B w (J i) = 0) (hQ : (Matrix.of fun i j => B (J i) (J j)).det ≠ 0) :
    ∃ N : V, B N N = 0 ∧ B w N = -1 ∧ ∀ i, B (J i) N = 0 := by
  set Q : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => B (J i) (J j) with hQdef
  have hu : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ
  have hQi : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hu
  -- a vector with `B w y ≠ 0`
  obtain ⟨y, hy⟩ : ∃ y, B w y ≠ 0 := by
    by_contra hcon
    have hall : ∀ v, B w v = 0 := fun v => by
      by_contra hne; exact hcon ⟨v, hne⟩
    exact hw0 (hnd.1 w hall)
  set w₁ : V := (-(B w y)⁻¹) • y with hw₁
  have hw₁w : B w w₁ = -1 := by
    simp [hw₁, map_smul, hy]
  -- orthogonalise against the screen
  set w₂ : V := w₁ - ∑ k, ∑ l, (Q⁻¹ k l * B w₁ (J k)) • J l with hw₂
  have hBw₂ : ∀ v, B v w₂ = B v w₁ - ∑ k, ∑ l, (Q⁻¹ k l * B w₁ (J k)) * B v (J l) := by
    intro v
    simp only [hw₂, map_sub, map_sum, map_smul, smul_eq_mul]
  have hw₂J : ∀ j, B (J j) w₂ = 0 := by
    intro j
    rw [hBw₂, hsymm (J j) w₁]
    have : ∑ k, ∑ l, (Q⁻¹ k l * B w₁ (J k)) * B (J j) (J l) = B w₁ (J j) := by
      have h1 : ∀ k, ∑ l, (Q⁻¹ k l * B w₁ (J k)) * B (J j) (J l) = B w₁ (J k) * (if k = j then 1 else 0) := by
        intro k
        have := congrFun (congrFun hQi k) j
        simp only [Matrix.mul_apply, Matrix.one_apply] at this
        calc ∑ l, (Q⁻¹ k l * B w₁ (J k)) * B (J j) (J l)
            = B w₁ (J k) * ∑ l, Q⁻¹ k l * Q l j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun l _ => ?_
              have : Q l j = B (J j) (J l) := by simp [hQdef, hsymm (J l) (J j)]
              rw [this]; ring
          _ = _ := by rw [this]
      simp only [h1]
      simp
    rw [this]; ring
  have hw₂w : B w w₂ = -1 := by
    rw [hBw₂, hw₁w]
    simp [hwJ]
  have hw₂w' : B w₂ w = -1 := by rw [hsymm]; exact hw₂w
  refine ⟨w₂ + (B w₂ w₂ / 2) • w, ?_, ?_, ?_⟩
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hww, hw₂w', hw₂w]
    ring
  · simp only [map_add, map_smul, smul_eq_mul, hww, hw₂w]
    ring
  · intro i
    simp only [map_add, map_smul, smul_eq_mul]
    rw [hw₂J i, hsymm (J i) w, hwJ i]
    ring

open scoped MatrixOrder in
/-- **A screen orthonormal frame**: `e i = Σ_k (X⁻¹)_{ki} J_k` with `X = √Q`. -/
theorem exists_screen_frame (B : LinearMap.BilinForm ℝ V) (hsymm : ∀ x y, B x y = B y x)
    (J : Fin m → V) {Q : Matrix (Fin m) (Fin m) ℝ} (hQdef : Q = Matrix.of fun i j => B (J i) (J j))
    (hQ : Q.PosDef) :
    ∃ Xi : Matrix (Fin m) (Fin m) ℝ,
      (Xi * Xiᵀ = Q⁻¹) ∧
      ∀ i j, B (∑ k, Xi k i • J k) (∑ l, Xi l j • J l) = if i = j then 1 else 0 := by
  have hQs : Q.PosSemidef := hQ.posSemidef
  set X : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt Q with hX
  have hXX : X * X = Q := by
    have := CFC.sqrt_mul_sqrt_self Q hQs.nonneg
    simpa [hX] using this
  have hXh : Xᵀ = X := by
    have := (CFC.sqrt_nonneg Q).posSemidef.isHermitian
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hdetX : X.det ≠ 0 := by
    have h1 : X.det * X.det = Q.det := by rw [← Matrix.det_mul, hXX]
    have h2 : Q.det ≠ 0 := hQ.det_pos.ne'
    intro h0; rw [h0] at h1; simp at h1; exact h2 h1.symm
  have hXu : IsUnit X.det := isUnit_iff_ne_zero.2 hdetX
  have hXi : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv _ hXu
  have hiX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul _ hXu
  have hXiT : (X⁻¹)ᵀ = X⁻¹ := by rw [Matrix.transpose_nonsing_inv, hXh]
  refine ⟨X⁻¹, ?_, ?_⟩
  · rw [hXiT, ← Matrix.mul_inv_rev, hXX]
  · intro i j
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have : ∑ x, X⁻¹ x j * ∑ x_1, X⁻¹ x_1 i * B (J x_1) (J x) = (X⁻¹ᵀ * Q * X⁻¹) i j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hQdef, Matrix.of_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_comm]
    rw [this, hXiT, ← hXX]
    have h1 : X⁻¹ * (X * X) * X⁻¹ = 1 := by
      calc X⁻¹ * (X * X) * X⁻¹ = (X⁻¹ * X) * (X * X⁻¹) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hiX, hXi, Matrix.one_mul]
    rw [h1, Matrix.one_apply]

open scoped MatrixOrder in
/-- **The trace of a tidal-type map is the screen trace.** -/
theorem trace_eq_screen (B : LinearMap.BilinForm ℝ V) (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (hdim : finrank ℝ V = m + 2) (J : Fin m → V) (w : V)
    (hww : B w w = 0) (hw0 : w ≠ 0) (hwJ : ∀ i, B w (J i) = 0)
    {Q : Matrix (Fin m) (Fin m) ℝ} (hQdef : Q = Matrix.of fun i j => B (J i) (J j)) (hQ : Q.PosDef)
    (A : V →ₗ[ℝ] V) (hAw : A w = 0) (hAw' : ∀ u, B (A u) w = 0)
    (hAs : ∀ k l, B (A (J k)) (J l) = B (A (J l)) (J k)) :
    LinearMap.trace ℝ V A = Matrix.trace (Q⁻¹ * Matrix.of fun k l => B (A (J k)) (J l)) := by
  have hQ0 : (Matrix.of fun i j => B (J i) (J j)).det ≠ 0 := by
    rw [← hQdef]; exact hQ.det_pos.ne'
  obtain ⟨N, hNN, hwN, hJN⟩ := exists_null_dual B hsymm hnd J w hww hw0 hwJ hQ0
  obtain ⟨Xi, hXi, hortho⟩ := exists_screen_frame B hsymm J hQdef hQ
  set e : Fin m → V := fun i => ∑ k, Xi k i • J k with he
  have heV : ∀ i, B (e i) w = 0 := fun i => by
    simp only [he, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hsymm (J k) w, hwJ k]; ring
  have heN : ∀ i, B (e i) N = 0 := fun i => by
    simp only [he, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hJN k]; ring
  let F : NullFrame B m :=
    { e := e, V := w, N := N, he := hortho, hV := hww, hN := hNN, hVN := hwN, heV := heV, heN := heN }
  have htr := NullFrame.trace_eq (E := V) (B := B) (m := m)
    (fun u hu => hnd.1 u hu) hsymm hdim F A
  rw [htr]
  simp only [F, hAw, map_zero, LinearMap.zero_apply, zero_sub, sub_zero, hsymm (A N) w, hAw' N]
  have h0 : B w (A N) = 0 := by rw [hsymm]; exact hAw' N
  rw [h0, sub_zero]
  have hsum : ∀ x, B (A (e x)) (e x) = ∑ k, ∑ l, Xi k x * Xi l x * B (A (J l)) (J k) := by
    intro x
    simp only [he, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp only [hsum]
  have hQi' : ∀ k l, Q⁻¹ k l = ∑ x, Xi k x * Xi l x := fun k l => by
    rw [← hXi]; simp [Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  calc ∑ x, ∑ k, ∑ l, Xi k x * Xi l x * B (A (J l)) (J k)
      = ∑ k, ∑ x, ∑ l, Xi k x * Xi l x * B (A (J l)) (J k) := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ x, Xi k x * Xi l x * B (A (J l)) (J k) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, Q⁻¹ k l * B (A (J l)) (J k) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [hQi', Finset.sum_mul]

/-- A sum of an antisymmetric array against `w ⊗ w` vanishes. -/
theorem sum_antisymm_zero {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ a b, f a b = -f b a)
    (w : Fin n → ℝ) : ∑ a, ∑ b, f a b * w a * w b = 0 := by
  have h : ∑ a, ∑ b, f a b * w a * w b = -∑ a, ∑ b, f a b * w a * w b := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hf a b]; ring
  linarith

section Chart

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

open scoped MatrixOrder in
/-- **`tr (Q⁻¹ ρ) = Ric(w, w)`**: the screen trace of the tidal matrix of fields orthogonal to a null
vector `w` is the Ricci curvature of `w`. -/
theorem trace_gram_rho (hg : Lightlike.IsCoordMetric g U) (hnm : n = m + 2) {x : Fin n → ℝ}
    (hx : x ∈ U) {w : Fin n → ℝ} (hww : gpairAt g x w w = 0) (hw0 : w ≠ 0)
    {J : Fin m → Fin n → ℝ} (hwJ : ∀ i, gpairAt g x w (J i) = 0)
    (hpd : (Matrix.of fun i j => gpairAt g x (J i) (J j)).PosDef) :
    Matrix.trace ((Matrix.of fun i j => gpairAt g x (J i) (J j))⁻¹ *
        Matrix.of fun i j => gpairAt g x (Lightlike.Geodesic.riemannApply g x w (J i)) (J j)) =
      ∑ σ, ∑ ν, Lightlike.ricci g σ ν x * w σ * w ν := by
  classical
  set B : LinearMap.BilinForm ℝ (Fin n → ℝ) := Matrix.toBilin' (g x) with hB
  have hsymm : ∀ u v, B u v = B v u := fun u v => by
    rw [hB, ← gpairAt_eq_toBilin, ← gpairAt_eq_toBilin]; exact gpairAt_symm hg hx u v
  have hnd : B.Nondegenerate :=
    (Matrix.nondegenerate_toBilin'_iff).2
      (Matrix.nondegenerate_of_det_ne_zero (hg.isUnit_det x hx).ne_zero)
  have hdim : Module.finrank ℝ (Fin n → ℝ) = m + 2 := by simp [hnm]
  set Tm : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun ρ μ => ∑ σ, ∑ ν, Lightlike.riemann g ρ σ μ ν x * w σ * w ν with hTm
  set A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.toLin' Tm with hA
  have hAu : ∀ u, A u = Lightlike.Geodesic.riemannApply g x w u := by
    intro u
    funext ρ
    simp only [hA, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, hTm, Matrix.of_apply,
      Lightlike.Geodesic.riemannApply]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun ν _ => ?_
    ring
  have hBA : ∀ u v, B (A u) v = gpairAt g x (Lightlike.Geodesic.riemannApply g x w u) v := fun u v => by
    rw [hAu, hB, ← gpairAt_eq_toBilin]
  have hQdef : (Matrix.of fun i j => gpairAt g x (J i) (J j)) = Matrix.of fun i j => B (J i) (J j) := by
    ext i j; simp [hB, gpairAt_eq_toBilin]
  have hAw : A w = 0 := by
    rw [hAu]
    funext ρ
    simp only [Lightlike.Geodesic.riemannApply, Pi.zero_apply]
    refine Finset.sum_eq_zero fun σ _ => ?_
    have := sum_antisymm_zero (fun μ ν => Lightlike.riemann g ρ σ μ ν x)
      (fun a b => Lightlike.riemann_antisymm_last g ρ σ a b x) w
    calc ∑ μ, ∑ ν, Lightlike.riemann g ρ σ μ ν x * w σ * w μ * w ν
        = w σ * ∑ μ, ∑ ν, Lightlike.riemann g ρ σ μ ν x * w μ * w ν := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ν _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have hAw' : ∀ u, B (A u) w = 0 := by
    intro u
    rw [hBA, gpair_riemannApply hg hx, sum4_pair_swap]
    refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => ?_
    have := sum_antisymm_zero (fun b σ => Lightlike.riemannLower g b σ μ ν x)
      (fun a b => hg.riemannLower_antisymm_first hx a b μ ν) w
    calc ∑ b, ∑ σ, Lightlike.riemannLower g b σ μ ν x * w b * w σ * u μ * w ν
        = (u μ * w ν) * ∑ b, ∑ σ, Lightlike.riemannLower g b σ μ ν x * w b * w σ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have hAs : ∀ k l, B (A (J k)) (J l) = B (A (J l)) (J k) := fun k l => by
    rw [hBA, hBA]; exact gpair_riemannApply_symm hg hx w (J k) (J l)
  have hmain := trace_eq_screen B hsymm hnd hdim J w (by rw [hB, ← gpairAt_eq_toBilin]; exact hww) hw0
    (fun i => by rw [hB, ← gpairAt_eq_toBilin]; exact hwJ i)
    (Q := Matrix.of fun i j => gpairAt g x (J i) (J j)) hQdef hpd A hAw hAw' hAs
  have hrho : (Matrix.of fun k l => B (A (J k)) (J l)) =
      Matrix.of fun i j => gpairAt g x (Lightlike.Geodesic.riemannApply g x w (J i)) (J j) := by
    ext k l; simp [hBA]
  rw [hrho] at hmain
  rw [← hmain, hA, Matrix.trace_toLin'_eq]
  simp only [Matrix.trace, Matrix.diag, hTm, Matrix.of_apply, Lightlike.ricci]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]

open scoped MatrixOrder in
/-- **Focusing of a family of Jacobi fields along a null geodesic, in a chart.**

`m = n - 2` Jacobi fields `J i` (with covariant derivatives `P i`) along a null geodesic `γ` (velocity
`w`) on `[0, T)`, orthogonal to `w`, with positive definite Gram matrix `Q` and symmetric `C = g(P, J)`
at `0`; if `Ric(w, w) ≥ 0` and `θ(0) = tr (Q⁻¹ Cᵀ)(0) < 0` then `T ≤ m / |θ(0)|`. -/
theorem jacobi_focusing_chart (hg : Lightlike.IsCoordMetric g U) (hnm : n = m + 2) (hm : 0 < m)
    {γ w : ℝ → Fin n → ℝ} {J P : Fin m → ℝ → Fin n → ℝ} {I : Set ℝ} {T : ℝ}
    (hJ : ∀ i, Lightlike.Geodesic.IsJacobiOn g γ w (J i) (P i) I) (hγU : ∀ t ∈ I, γ t ∈ U)
    (hT : Ico 0 T ⊆ I)
    (hww : ∀ t ∈ Ico 0 T, gpairAt g (γ t) (w t) (w t) = 0) (hw0 : ∀ t ∈ Ico 0 T, w t ≠ 0)
    (hwJ : ∀ t ∈ Ico 0 T, ∀ i, gpairAt g (γ t) (w t) (J i t) = 0)
    (hwP : ∀ t ∈ Ico 0 T, ∀ i, gpairAt g (γ t) (w t) (P i t) = 0)
    (hpd : ∀ t ∈ Ico 0 T, (gramQ g γ J t).PosDef)
    (hC0 : (gramC g γ J P 0)ᵀ = gramC g γ J P 0)
    (hric : ∀ t ∈ Ico 0 T, 0 ≤ ∑ σ, ∑ ν, Lightlike.ricci g σ ν (γ t) * w t σ * w t ν)
    (h0 : Matrix.trace ((gramQ g γ J 0)⁻¹ * (gramC g γ J P 0)ᵀ) < 0) :
    T ≤ m / |Matrix.trace ((gramQ g γ J 0)⁻¹ * (gramC g γ J P 0)ᵀ)| := by
  have hI : ∀ t ∈ Ico 0 T, t ∈ I := fun t ht => hT ht
  have hCs := gramC_symm hg hJ hγU hT hC0
  refine gram_focusing hm (Q := gramQ g γ J) (C := gramC g γ J P) (ρ := gramRho g γ w J)
    (fun t ht i j => (jacobi_gram_derivs hg hJ hγU (hI t ht)).1 i j) ?_ hpd hCs ?_ ?_ h0
  · intro t ht i j
    have h := (jacobi_gram_derivs hg hJ hγU (hI t ht)).2 i j
    have hdet : (gramQ g γ J t).det ≠ 0 := (hpd t ht).det_pos.ne'
    have hP := gramP_eq hg hnm (hγU t (hI t ht)) (hww t ht) (hw0 t ht) (hwJ t ht) (hwP t ht) hdet
    have hP' : gramP g γ P t = gramC g γ J P t * (gramQ g γ J t)⁻¹ * (gramC g γ J P t)ᵀ := hP
    rw [hP'] at h
    exact h
  · intro t ht
    ext i j
    simp only [gramRho, Matrix.transpose_apply, Matrix.of_apply]
    exact gpair_riemannApply_symm hg (hγU t (hI t ht)) (w t) (J j t) (J i t)
  · intro t ht
    rw [show (gramQ g γ J t)⁻¹ * gramRho g γ w J t = _ from rfl]
    have := trace_gram_rho hg hnm (hγU t (hI t ht)) (hww t ht) (hw0 t ht) (hwJ t ht) (hpd t ht)
    rw [show gramQ g γ J t = Matrix.of fun i j => gpairAt g (γ t) (J i t) (J j t) from rfl,
      show gramRho g γ w J t = Matrix.of fun i j => gpairAt g (γ t)
        (Lightlike.Geodesic.riemannApply g (γ t) (w t) (J i t)) (J j t) from rfl, this]
    exact hric t ht

end Chart

end Lightlike.Penrose
