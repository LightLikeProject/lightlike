import Lightlike.OperatorAlgebras.VacuumProjection

/-!
# Shale's criterion, sufficiency

`T-OP2-P7` (`Tasks/OP/T_OP2_P7.lean`): a Bogoliubov transformation `T` whose antilinear part is Hilbert-Schmidt is
implemented in every Fock representation (`shale_sufficiency_of_hilbertSchmidt`).

Proof, without a polar decomposition. In the representation `f ↦ W (T f)` (`Bogoliubov.twist`) let `P_s` be the
vacuum projection (`vacAvg`) of the modes `bₖ`, `k ∈ s`, for a finite set `s` of indices of a Hilbert basis `b`.

* `‖P_s Ω‖² = ⟪Ω, P_s Ω⟫ = (2π)⁻ⁿ ∫ exp (-(‖f_x‖² + ‖T f_x‖²)/4) dx = det ((1 + A_s)/2)^(-1/2)`, and
  `det M ≤ exp (tr M - 2n)` gives `det ((1 + A_s)/2) ≤ exp (2 ∑_{k ∈ s} ‖β bₖ‖²)`. So
  `‖P_s Ω‖² ≥ exp (-∑ₖ ‖β bₖ‖²) > 0` for all `s`: this is where the Hilbert-Schmidt hypothesis enters.
* The ranges of the `P_s` decrease, so `P_s Ω` converges to a nonzero vector `Ω'` fixed by all `P_s`
  (`exists_fixed_of_decreasing_projections`).
* Hence `⟪Ω', W (T f) Ω'⟫ = exp (-‖f‖²/4) ‖Ω'‖²` for `f` in the span of the basis, and for all `f` by the norm
  continuity of the Weyl unitaries of a Fock representation (`FockRep.continuous_W`).
* So `f ↦ W (T f)` with the vacuum `Ω'/‖Ω'‖` is a Fock representation (cyclic by irreducibility), and the
  unitary of the uniqueness theorem (`fockUnitary_spec`) implements `T`.
-/

open scoped InnerProductSpace
open MeasureTheory Complex Matrix

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `det M ≤ exp (tr M - n)` for a positive definite real matrix. -/
lemma det_le_exp_trace_sub_card {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hM : M.PosDef) : M.det ≤ Real.exp (M.trace - Fintype.card ι) := by
  have hH := hM.isHermitian
  have hdet : M.det = ∏ i, hH.eigenvalues i := by
    have := hH.det_eq_prod_eigenvalues
    simpa using this
  have htr : M.trace = ∑ i, hH.eigenvalues i := by
    have := hH.trace_eq_sum_eigenvalues
    simpa using this
  have hsum : ∑ i, hH.eigenvalues i - (Fintype.card ι : ℝ) = ∑ i, (hH.eigenvalues i - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [hdet, htr, hsum, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun i _ => (hM.eigenvalues_pos i).le) fun i _ => by
    linarith [Real.add_one_le_exp (hH.eigenvalues i - 1)]

/-! ### Finite sets of modes of a family -/

/-- The mode vector of a finite subfamily with the coordinates of a coefficient function. -/
lemma modeVec_restrict {ι : Type*} (v : ι → h) (s : Finset ι) (z : ι → ℂ) :
    modeVec (fun k : s => v k) (Sum.elim (fun k : s => (z k).re) fun k : s => (z k).im) =
      ∑ k ∈ s, z k • v k := by
  unfold modeVec
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_coe_sort s fun k => z k • v k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, Complex.re_add_im]

/-- Every mode vector of a finite subfamily is a combination over the finite set. -/
lemma exists_modeVec_eq_sum {ι : Type*} [DecidableEq ι] (v : ι → h) (s : Finset ι) (a : s ⊕ s → ℝ) :
    ∃ z : ι → ℂ, (∀ k, k ∉ s → z k = 0) ∧ modeVec (fun k : s => v k) a = ∑ k ∈ s, z k • v k := by
  refine ⟨fun k => if hk : k ∈ s then (a (Sum.inl ⟨k, hk⟩) : ℂ) + I * (a (Sum.inr ⟨k, hk⟩) : ℂ) else 0,
    fun k hk => by simp [hk], ?_⟩
  unfold modeVec
  rw [← Finset.sum_coe_sort s fun k => (if hk : k ∈ s then
    (a (Sum.inl ⟨k, hk⟩) : ℂ) + I * (a (Sum.inr ⟨k, hk⟩) : ℂ) else 0) • v k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dif_pos k.2]

/-- The mode vectors of a finite subfamily are mode vectors of every larger finite subfamily. -/
lemma exists_modeVec_eq_of_subset {ι : Type*} [DecidableEq ι] (v : ι → h) {s t : Finset ι} (hst : s ⊆ t)
    (a : s ⊕ s → ℝ) : ∃ a' : t ⊕ t → ℝ, modeVec (fun k : s => v k) a = modeVec (fun k : t => v k) a' := by
  obtain ⟨z, hz, hsum⟩ := exists_modeVec_eq_sum v s a
  refine ⟨Sum.elim (fun k : t => (z k).re) fun k : t => (z k).im, ?_⟩
  rw [hsum, modeVec_restrict]
  exact Finset.sum_subset hst fun k _ hk => by rw [hz k hk, zero_smul]

/-! ### The vacuum projections of the twisted representation -/

/-- The twisted representation of a Fock representation is strongly continuous. -/
lemma FockRep.continuous_twist_W (R : FockRep h K) (T : Bogoliubov h) (ψ : K) :
    Continuous fun f : h => (T.twist R.toCCRRep).W f ψ :=
  (R.continuous_W ψ).comp T.toEquiv.continuous

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `‖P Ω‖² = det ((1 + A)/2)^(-1/2)` for the vacuum projection `P` of the modes `e` in the twisted
representation. -/
lemma norm_sq_vacAvg_twist_Ω (R : FockRep h K) (T : Bogoliubov h) {e : m → h} (he : Orthonormal ℂ e) :
    ‖vacAvg (T.twist R.toCCRRep) e R.Ω‖ ^ 2 = (Real.sqrt (halfCov T e).det)⁻¹ := by
  have hc := R.continuous_twist_W T
  have h1 := inner_self_eq_norm_sq (𝕜 := ℂ) (vacAvg (T.twist R.toCCRRep) e R.Ω)
  rw [inner_vacAvg_vacAvg _ hc he, inner_vacAvg _ hc he] at h1
  have hI : ∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) *
      ⟪R.Ω, (T.twist R.toCCRRep).W (modeVec e x) R.Ω⟫_ℂ =
      ((gaussZ m / Real.sqrt (halfCov T e).det : ℝ) : ℂ) := by
    rw [← integral_gaussE_mul_gaussE_map T he, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Bogoliubov.twist_W]
    rw [inner_Ω_W_Ω]
    exact (Complex.ofReal_mul _ _).symm
  have hZ : (gaussZ m : ℂ) ≠ 0 := by exact_mod_cast (gaussZ_pos (m := m)).ne'
  have h2 : ((gaussZ m : ℂ))⁻¹ * ((gaussZ m / Real.sqrt (halfCov T e).det : ℝ) : ℂ) =
      (((Real.sqrt (halfCov T e).det)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_inv, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hZ, one_mul]
  rw [hI, h2] at h1
  rw [← h1]
  exact Complex.ofReal_re _

/-- The lower bound: `exp (-∑ₖ ‖β eₖ‖²) ≤ ‖P Ω‖²`. -/
lemma exp_neg_le_norm_sq_vacAvg_twist_Ω (R : FockRep h K) (T : Bogoliubov h) {e : m → h}
    (he : Orthonormal ℂ e) :
    Real.exp (-∑ k, ‖T.betaPart (e k)‖ ^ 2) ≤ ‖vacAvg (T.twist R.toCCRRep) e R.Ω‖ ^ 2 := by
  rw [norm_sq_vacAvg_twist_Ω R T he]
  set H := ∑ k, ‖T.betaPart (e k)‖ ^ 2 with hH
  have hdetpos : 0 < (halfCov T e).det := (halfCov_posDef T e).det_pos
  have hbeta : ∀ k, ‖T.toEquiv (e k)‖ ^ 2 + ‖T.toEquiv (I • e k)‖ ^ 2 - 2 = 4 * ‖T.betaPart (e k)‖ ^ 2 := by
    intro k
    rw [T.norm_beta_sq_eq, he.1 k]
    ring
  have hdet : (halfCov T e).det ≤ Real.exp H ^ 2 := by
    have h1 := det_le_exp_trace_sub_card _ (halfCov_posDef T e)
    rw [halfCov_trace] at h1
    simp only [hbeta] at h1
    rw [← Finset.mul_sum, ← hH] at h1
    have h2 : Real.exp H ^ 2 = Real.exp (4 * H / 2) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [h2]
    exact h1
  have hsqrt : Real.sqrt (halfCov T e).det ≤ Real.exp H := by
    have := Real.sqrt_le_sqrt hdet
    rwa [Real.sqrt_sq (Real.exp_pos H).le] at this
  rw [Real.exp_neg]
  exact inv_anti₀ (Real.sqrt_pos.2 hdetpos) hsqrt

/-- **Shale's criterion, sufficiency**: a Bogoliubov transformation with a Hilbert-Schmidt antilinear part is
implemented in every Fock representation. -/
theorem shale_sufficiency_of_hilbertSchmidt [CompleteSpace h] (R : FockRep h K) (T : Bogoliubov h)
    (hβ : IsHilbertSchmidt T.betaPart) : Implements R.toCCRRep T := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ h
  have hsum := hβ _ b
  set H := ∑' i, ‖T.betaPart (b i)‖ ^ 2 with hH
  have hc := R.continuous_twist_W T
  have he : ∀ s : Finset w, Orthonormal ℂ fun k : s => b k := fun s =>
    b.orthonormal.comp _ Subtype.val_injective
  -- the limit of the vacuum projections of the vacuum
  have hlow : ∀ s : Finset w,
      Real.exp (-H) ≤ ‖vacAvg (T.twist R.toCCRRep) (fun k : s => b k) R.Ω‖ ^ 2 := by
    intro s
    refine le_trans ?_ (exp_neg_le_norm_sq_vacAvg_twist_Ω R T (he s))
    rw [Real.exp_le_exp, neg_le_neg_iff, Finset.sum_coe_sort s fun i => ‖T.betaPart (b i)‖ ^ 2]
    exact hsum.sum_le_tsum s fun i _ => sq_nonneg _
  obtain ⟨Ω', hΩ'c, hΩ'fix⟩ := exists_fixed_of_decreasing_projections
    (fun s : Finset w => vacAvg (T.twist R.toCCRRep) (fun k : s => b k))
    (fun s => vacAvg_symm _ hc (he s)) (fun s => vacAvg_idem _ hc (he s))
    (fun s => vacAvg_sub _ hc (he s)) (fun s => norm_vacAvg_le _ hc (he s))
    (fun s t hst ψ hψ => vacAvg_eq_of_subfamily _ hc (he s) (he t)
      (exists_modeVec_eq_of_subset (fun i => b i) hst) hψ)
    R.Ω (Real.exp (-H)) hlow
  have hΩ'pos : 0 < ‖Ω'‖ := by
    have h1 : 0 < ‖Ω'‖ ^ 2 := lt_of_lt_of_le (Real.exp_pos _) hΩ'c
    by_contra h0
    have h2 : ‖Ω'‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
    rw [h2] at h1
    norm_num at h1
  have hΩ'ne : Ω' ≠ 0 := norm_pos_iff.1 hΩ'pos
  -- the vacuum expectation of `Ω'` in the twisted representation
  have hall : ∀ f : h, ⟪Ω', R.W (T.toEquiv f) Ω'⟫_ℂ = (gaussE f : ℂ) * ⟪Ω', Ω'⟫_ℂ := by
    have hd : Dense ((Submodule.span ℂ (Set.range b) : Submodule ℂ h) : Set h) :=
      Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span
    have hc1 : Continuous fun f : h => ⟪Ω', R.W (T.toEquiv f) Ω'⟫_ℂ := continuous_const.inner (hc Ω')
    have hc2 : Continuous fun f : h => (gaussE f : ℂ) * ⟪Ω', Ω'⟫_ℂ :=
      (Complex.continuous_ofReal.comp continuous_gaussE).mul continuous_const
    have := Continuous.ext_on hd hc1 hc2 (fun f hf => by
      obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
      have h1 : (c.sum fun i a => a • b i) = modeVec (fun k : c.support => b k)
          (Sum.elim (fun k : c.support => (c k).re) fun k : c.support => (c k).im) :=
        (modeVec_restrict (fun i => b i) c.support c).symm
      rw [h1]
      exact inner_W_of_vacAvg_eq _ hc (he c.support) (hΩ'fix c.support) _)
    exact fun f => congrFun this f
  have hN : ⟪Ω', Ω'⟫_ℂ = ((‖Ω'‖ ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; exact inner_self_eq_norm_sq (𝕜 := ℂ) Ω'
    · rw [Complex.ofReal_im]; exact inner_self_im (𝕜 := ℂ) Ω'
  -- the Fock representation `f ↦ W (T f)` with the vacuum `Ω' / ‖Ω'‖`
  have hn0 : ((‖Ω'‖⁻¹ : ℝ) : ℂ) • Ω' ≠ 0 :=
    smul_ne_zero (by exact_mod_cast (inv_pos.2 hΩ'pos).ne') hΩ'ne
  let S : FockRep h K :=
    { toCCRRep := T.twist R.toCCRRep
      Ω := ((‖Ω'‖⁻¹ : ℝ) : ℂ) • Ω'
      norm_Ω := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hΩ'pos).le,
          inv_mul_cancel₀ hΩ'pos.ne']
      cyclic := by
        have h1 := fockRep_cyclic R hn0
        have h2 : (Set.range fun f => (T.twist R.toCCRRep).W f (((‖Ω'‖⁻¹ : ℝ) : ℂ) • Ω')) =
            Set.range fun g => R.W g (((‖Ω'‖⁻¹ : ℝ) : ℂ) • Ω') :=
          T.toEquiv.surjective.range_comp fun g => R.W g (((‖Ω'‖⁻¹ : ℝ) : ℂ) • Ω')
        rw [h2]
        exact h1
      vacuum_expectation := by
        intro f
        show ⟪((‖Ω'‖⁻¹ : ℝ) : ℂ) • Ω', R.W (T.toEquiv f) (((‖Ω'‖⁻¹ : ℝ) : ℂ) • Ω')⟫_ℂ =
          Complex.exp (-(‖f‖ ^ 2 / 4 : ℝ))
        rw [map_smul, inner_smul_left, inner_smul_right, hall f, hN, conj_ofReal, gaussE,
          Complex.ofReal_exp, Complex.ofReal_neg]
        have hreal : ‖Ω'‖⁻¹ * (‖Ω'‖⁻¹ * ‖Ω'‖ ^ 2) = 1 := by
          have := hΩ'pos.ne'
          field_simp
        have hk : ((‖Ω'‖⁻¹ : ℝ) : ℂ) * (((‖Ω'‖⁻¹ : ℝ) : ℂ) * ((‖Ω'‖ ^ 2 : ℝ) : ℂ)) = 1 := by
          exact_mod_cast hreal
        linear_combination (Complex.exp (-(‖f‖ ^ 2 / 4 : ℝ))) * hk }
  exact ⟨fockUnitary R S, fun f ψ => (fockUnitary_spec R S).2 f ψ⟩

/-- **Shale's criterion**: a Bogoliubov transformation is implemented in a Fock representation if and only if
its antilinear part is Hilbert-Schmidt. -/
theorem shale_criterion [CompleteSpace h] (R : FockRep h K) (T : Bogoliubov h) :
    Implements R.toCCRRep T ↔ IsHilbertSchmidt T.betaPart :=
  ⟨shale_necessity_of_implements R T, shale_sufficiency_of_hilbertSchmidt R T⟩

end Lightlike.OperatorAlgebras
