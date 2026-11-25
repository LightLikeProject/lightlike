import Lightlike.Spacetime.PenroseSingularity.JacobiGram

/-!
# The Riccati equation for a Gram matrix with a Jacobi-type derivative law (G1-012, step D3b)

For matrix functions `Q` (Gram), `C` (`g(P_i, J_j)`) and `ρ` (tidal), with `Q' = C + Cᵀ` and
`C' = -ρ + C Q⁻¹ Cᵀ`, the matrix `B = Q⁻¹ Cᵀ` satisfies `B' = -B² - Q⁻¹ρ`, so `θ = tr B` has
`θ' = -tr (Q⁻¹ ρ) - tr B²`.
-/

open Set Matrix Filter Topology

noncomputable section

namespace Lightlike.Penrose

variable {m : ℕ}

theorem differentiableAt_det_of_entries {M : ℝ → Matrix (Fin m) (Fin m) ℝ} {t : ℝ}
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) :
    DifferentiableAt ℝ (fun s => (M s).det) t := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine DifferentiableAt.const_mul ?_ _
  exact DifferentiableAt.fun_finset_prod fun i _ => hM (σ i) i

theorem differentiableAt_inv_entry {M : ℝ → Matrix (Fin m) (Fin m) ℝ} {t : ℝ}
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) (hdet : (M t).det ≠ 0) (a b : Fin m) :
    DifferentiableAt ℝ (fun s => (M s)⁻¹ a b) t := by
  have hadj : ∀ i j, DifferentiableAt ℝ (fun s => (M s).adjugate i j) t := by
    intro i j
    simp only [Matrix.adjugate_apply]
    refine differentiableAt_det_of_entries (M := fun s => (M s).updateRow j (Pi.single i 1)) ?_
    intro k l
    simp only [Matrix.updateRow_apply]
    by_cases h : k = j
    · simp [h]
    · simpa [h] using hM k l
  have hd := differentiableAt_det_of_entries hM
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  exact (hd.inv hdet).mul (hadj a b)

/-- **Derivative of an inverse matrix function**, given the derivative of the matrix. -/
theorem hasDerivAt_inv_of_hasDerivAt {Y : ℝ → Matrix (Fin m) (Fin m) ℝ} {Y1 : Matrix (Fin m) (Fin m) ℝ}
    {t : ℝ} (hY : ∀ i j, HasDerivAt (fun s => Y s i j) (Y1 i j) t) (hdet : (Y t).det ≠ 0) (i j : Fin m) :
    HasDerivAt (fun s => (Y s)⁻¹ i j) ((-((Y t)⁻¹ * Y1 * (Y t)⁻¹)) i j) t := by
  have hZd : ∀ a b, HasDerivAt (fun s => (Y s)⁻¹ a b) (deriv (fun s => (Y s)⁻¹ a b) t) t := fun a b =>
    (differentiableAt_inv_entry (fun i j => (hY i j).differentiableAt) hdet a b).hasDerivAt
  set Z' : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun a b => deriv (fun s => (Y s)⁻¹ a b) t with hZ'
  have hdetc : ContinuousAt (fun s => (Y s).det) t :=
    (differentiableAt_det_of_entries (fun i j => (hY i j).differentiableAt)).continuousAt
  have hnear : ∀ᶠ s in 𝓝 t, (Y s).det ≠ 0 := hdetc.eventually_ne hdet
  have hprod : ∀ a b, HasDerivAt (fun s => ∑ k, Y s a k * (Y s)⁻¹ k b)
      (∑ k, (Y1 a k * (Y t)⁻¹ k b + Y t a k * Z' k b)) t := fun a b =>
    HasDerivAt.fun_sum fun k _ => (hY a k).mul (hZd k b)
  have hconst : ∀ a b, HasDerivAt (fun s => ∑ k, Y s a k * (Y s)⁻¹ k b) 0 t := by
    intro a b
    refine (hasDerivAt_const t (if a = b then (1 : ℝ) else 0)).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with s hs
    have := congrFun (congrFun (Matrix.mul_nonsing_inv (Y s) (isUnit_iff_ne_zero.2 hs)) a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hmat : Y1 * (Y t)⁻¹ + Y t * Z' = 0 := by
    ext a b
    have := (hprod a b).unique (hconst a b)
    simpa [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using this
  have hZ : (Y t)⁻¹ * Y t = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
  have hZ'eq : Z' = -((Y t)⁻¹ * Y1 * (Y t)⁻¹) := by
    have h1 : Y t * Z' = -(Y1 * (Y t)⁻¹) := eq_neg_of_add_eq_zero_right hmat
    calc Z' = ((Y t)⁻¹ * Y t) * Z' := by rw [hZ, one_mul]
      _ = (Y t)⁻¹ * (Y t * Z') := by rw [Matrix.mul_assoc]
      _ = -((Y t)⁻¹ * Y1 * (Y t)⁻¹) := by rw [h1]; simp [Matrix.mul_assoc]
  have := hZd i j
  rw [show deriv (fun s => (Y s)⁻¹ i j) t = (-((Y t)⁻¹ * Y1 * (Y t)⁻¹)) i j from by
    rw [← hZ'eq]; rfl] at this
  exact this

variable {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {A' B' : Matrix (Fin m) (Fin m) ℝ} {t : ℝ}

theorem hasDerivAt_matrix_mul (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i j : Fin m) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hA i k).mul (hB k j)
  simp only [Matrix.mul_apply, Matrix.add_apply]
  refine this.congr_deriv ?_
  rw [← Finset.sum_add_distrib]

theorem hasDerivAt_matrix_transpose (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (i j : Fin m) :
    HasDerivAt (fun s => (A s)ᵀ i j) (A'ᵀ i j) t := by
  simpa using hA j i

theorem hasDerivAt_matrix_trace (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) :
    HasDerivAt (fun s => trace (A s)) (trace A') t := by
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hA i i
  simpa [trace, diag] using this

/-- **The Riccati equation for the expansion of a Gram matrix.** -/
theorem hasDerivAt_gram_expansion {Q C ρ : ℝ → Matrix (Fin m) (Fin m) ℝ} {t : ℝ}
    (hQ : ∀ i j, HasDerivAt (fun s => Q s i j) ((C t + (C t)ᵀ) i j) t)
    (hC : ∀ i j, HasDerivAt (fun s => C s i j) ((-(ρ t) + C t * (Q t)⁻¹ * (C t)ᵀ) i j) t)
    (hdet : (Q t).det ≠ 0) (hQs : (Q t)ᵀ = Q t) (hρs : (ρ t)ᵀ = ρ t) :
    HasDerivAt (fun s => trace ((Q s)⁻¹ * (C s)ᵀ))
      (-(trace ((Q t)⁻¹ * ρ t)) - trace (((Q t)⁻¹ * (C t)ᵀ) * ((Q t)⁻¹ * (C t)ᵀ))) t := by
  have hinv := hasDerivAt_inv_of_hasDerivAt hQ hdet
  have hCt := hasDerivAt_matrix_transpose hC
  have hprod := hasDerivAt_matrix_mul hinv hCt
  have htr := hasDerivAt_matrix_trace hprod
  refine htr.congr_deriv ?_
  have hQi : ((Q t)⁻¹)ᵀ = (Q t)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hQs]
  have hCt' : ((-(ρ t) + C t * (Q t)⁻¹ * (C t)ᵀ))ᵀ = -(ρ t) + C t * (Q t)⁻¹ * (C t)ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_neg, hρs, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hQi, Matrix.mul_assoc]
  simp only [hCt']
  -- expand the trace
  have e1 : trace (-((Q t)⁻¹ * (C t + (C t)ᵀ) * (Q t)⁻¹) * (C t)ᵀ + (Q t)⁻¹ * (-(ρ t) + C t * (Q t)⁻¹ * (C t)ᵀ)) =
      -(trace ((Q t)⁻¹ * (C t) * (Q t)⁻¹ * (C t)ᵀ)) - trace ((Q t)⁻¹ * (C t)ᵀ * (Q t)⁻¹ * (C t)ᵀ) -
        trace ((Q t)⁻¹ * ρ t) + trace ((Q t)⁻¹ * (C t) * (Q t)⁻¹ * (C t)ᵀ) := by
    simp only [Matrix.neg_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, trace_add, trace_neg,
      Matrix.mul_assoc]
    ring
  rw [e1]
  simp only [Matrix.mul_assoc]
  ring

/-- **Focusing for a Gram matrix.** On `[0, T)`, `Q` positive definite, `C` symmetric (Wronskian), the
derivative laws `Q' = C + Cᵀ`, `C' = -ρ + C Q⁻¹ Cᵀ`, `ρ` symmetric with `tr (Q⁻¹ ρ) ≥ 0`, and
`θ(0) = tr (Q⁻¹ Cᵀ)(0) < 0` give `T ≤ m / |θ(0)|`. -/
theorem gram_focusing (hm : 0 < m) {T : ℝ} {Q C ρ : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (hQd : ∀ t ∈ Ico 0 T, ∀ i j, HasDerivAt (fun s => Q s i j) ((C t + (C t)ᵀ) i j) t)
    (hCd : ∀ t ∈ Ico 0 T, ∀ i j,
      HasDerivAt (fun s => C s i j) ((-(ρ t) + C t * (Q t)⁻¹ * (C t)ᵀ) i j) t)
    (hpd : ∀ t ∈ Ico 0 T, (Q t).PosDef) (hCs : ∀ t ∈ Ico 0 T, (C t)ᵀ = C t)
    (hρs : ∀ t ∈ Ico 0 T, (ρ t)ᵀ = ρ t) (hρ : ∀ t ∈ Ico 0 T, 0 ≤ trace ((Q t)⁻¹ * ρ t))
    (h0 : trace ((Q 0)⁻¹ * (C 0)ᵀ) < 0) : T ≤ m / |trace ((Q 0)⁻¹ * (C 0)ᵀ)| := by
  refine Lightlike.focusing (Θ := fun s => trace ((Q s)⁻¹ * (C s)ᵀ))
    (Θ' := fun t => -(trace ((Q t)⁻¹ * ρ t)) - trace (((Q t)⁻¹ * (C t)ᵀ) * ((Q t)⁻¹ * (C t)ᵀ)))
    (by exact_mod_cast hm) ?_ ?_ h0
  · intro t ht
    have hQs : (Q t)ᵀ = Q t := by
      have := (hpd t ht).isHermitian.eq
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
    exact hasDerivAt_gram_expansion (hQd t ht) (hCd t ht) (hpd t ht).det_pos.ne' hQs (hρs t ht)
  · intro t ht
    have hQs : (Q t)ᵀ = Q t := by
      have := (hpd t ht).isHermitian.eq
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
    have hu : IsUnit (Q t).det := isUnit_iff_ne_zero.2 (hpd t ht).det_pos.ne'
    have hQB : (Q t * ((Q t)⁻¹ * (C t)ᵀ))ᵀ = Q t * ((Q t)⁻¹ * (C t)ᵀ) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.transpose_transpose,
        hCs t ht]
    have h2 := trace_sq_ge_of_gram hm (hpd t ht) hQB
    have h3 := hρ t ht
    rw [neg_div]
    linarith

end Lightlike.Penrose
