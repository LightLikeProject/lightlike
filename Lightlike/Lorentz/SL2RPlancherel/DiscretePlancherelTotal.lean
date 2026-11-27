module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteOrthDifferent

/-!
# The discrete series part of the Plancherel formula of `SL(2,ℝ)`

The normalised matrix coefficients `u^{n,±}_{jl}` of all holomorphic (`+`) and antiholomorphic (`-`) discrete series
`D_n^±`, `n ≥ 2`, form an orthonormal system of `L²(SL(2,ℝ))` (`discFam_orthonormal`): inside one series by
Schur orthogonality, for `n ≠ n'` by `inner_uLp_uLp_ne` and for `+` against `-` by `inner_uLp_uLpBar`. For
`f ∈ L²(SL(2,ℝ))` the squared norm of the projection onto the closed span `discreteAll` is the sum over all
series of the squared norms of the projections onto the isotypic subspaces
(`norm_sq_starProjection_discreteAll`), each of which is `d_n` times the Hilbert–Schmidt norm of `D_n^±(f)`
(`norm_sq_starProjection_discrete_eq`), and is at most `‖f‖²` (`norm_sq_starProjection_discreteAll_le`).
-/

@[expose] public section

open MeasureTheory Set Complex Real Filter Topology UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- Closed subspaces of `L²(SL(2,ℝ))` have an orthogonal projection. -/
instance closure_hasOrthogonalProjection (S : Submodule ℂ (Lp ℂ 2 (haarR : Measure SL2R))) :
    S.topologicalClosure.HasOrthogonalProjection := by
  have : CompleteSpace S.topologicalClosure := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- **The norm of the projection onto the closed span of an orthonormal system** is the `ℓ²`-norm of the
inner products. -/
theorem norm_sq_starProjection_span {ι : Type*} (v : ι → Lp ℂ 2 (haarR : Measure SL2R))
    (hv : Orthonormal ℂ v) (f : Lp ℂ 2 (haarR : Measure SL2R)) :
    ‖(Submodule.span ℂ (Set.range v)).topologicalClosure.starProjection f‖ ^ 2 = ∑' i, ‖⟪v i, f⟫_ℂ‖ ^ 2 := by
  classical
  set M := (Submodule.span ℂ (Set.range v)).topologicalClosure with hM
  have hcomplete : CompleteSpace M := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hmem : ∀ i, v i ∈ M := fun i => Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  set w : ι → M := fun i => ⟨v i, hmem i⟩ with hw
  have hon : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite] at hv ⊢
    intro i i'
    have h := hv i i'
    simpa [hw, Submodule.coe_inner] using h
  have hsp : (Submodule.span ℂ (Set.range w))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal] at hx
    have h0 : ∀ i, ⟪v i, (x : Lp ℂ 2 (haarR : Measure SL2R))⟫_ℂ = 0 := fun i => by
      have := hx (w i) (Submodule.subset_span ⟨i, rfl⟩)
      simpa [hw, Submodule.coe_inner] using this
    have hx2 : ⟪(x : Lp ℂ 2 (haarR : Measure SL2R)), (x : Lp ℂ 2 (haarR : Measure SL2R))⟫_ℂ = 0 := by
      have hxM : (x : Lp ℂ 2 (haarR : Measure SL2R)) ∈ M := x.2
      have horth : M ≤ (ℂ ∙ (x : Lp ℂ 2 (haarR : Measure SL2R)))ᗮ := by
        refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
        rw [← inner_conj_symm, h0 i]; simp
      have := horth hxM
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
      exact this
    exact Subtype.ext (inner_self_eq_zero.1 hx2)
  let b : HilbertBasis ι ℂ M := HilbertBasis.mkOfOrthogonalEqBot hon hsp
  have hb : ∀ i, b i = w i := fun i => congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hon hsp) i
  set g : M := ⟨M.starProjection f, Submodule.starProjection_apply_mem M f⟩ with hg
  have hpar := b.hasSum_inner_mul_inner g g
  have hterm : ∀ i, ⟪g, b i⟫_ℂ * ⟪b i, g⟫_ℂ = ((‖⟪v i, f⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have hin : ⟪b i, g⟫_ℂ = ⟪v i, f⟫_ℂ := by
      rw [hb i]
      show ⟪v i, M.starProjection f⟫_ℂ = _
      have h1 := Submodule.starProjection_inner_eq_zero (K := M) f (v i) (hmem i)
      rw [inner_sub_left] at h1
      have h2 : ⟪f, v i⟫_ℂ = ⟪M.starProjection f, v i⟫_ℂ := sub_eq_zero.1 h1
      rw [← inner_conj_symm (v i) (M.starProjection f), ← h2, inner_conj_symm]
    have : ⟪g, b i⟫_ℂ = (starRingEnd ℂ) ⟪b i, g⟫_ℂ := by
      simp only [Submodule.coe_inner]; exact (inner_conj_symm _ _).symm
    rw [this, hin, Complex.conj_mul']
    push_cast; ring
  have hnorm : ⟪g, g⟫_ℂ = ((‖M.starProjection f‖ ^ 2 : ℝ) : ℂ) := by
    have h0 : ⟪g, g⟫_ℂ = ⟪M.starProjection f, M.starProjection f⟫_ℂ := rfl
    rw [h0, inner_self_eq_norm_sq_to_K]
    norm_cast
  simp only [hterm, hnorm] at hpar
  have hpar' : HasSum (fun i : ι => ‖⟪v i, f⟫_ℂ‖ ^ 2) (‖M.starProjection f‖ ^ 2) := by
    exact_mod_cast hpar
  exact hpar'.tsum_eq.symm

lemma inner_uLpBar_uLpBar {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n') (p p' : ℕ × ℕ) :
    ⟪uLpBar hn p, uLpBar hn' p'⟫_ℂ = (starRingEnd ℂ) ⟪uLp hn p, uLp hn' p'⟫_ℂ := by
  have hae : ∀ᵐ g ∂haarR, ⟪(uLpBar hn p : SL2R → ℂ) g, (uLpBar hn' p' : SL2R → ℂ) g⟫_ℂ =
      (starRingEnd ℂ) ⟪(uLp hn p : SL2R → ℂ) g, (uLp hn' p' : SL2R → ℂ) g⟫_ℂ := by
    filter_upwards [(memLp_uFun hn p).coeFn_toLp, (memLp_uFun hn' p').coeFn_toLp,
      ((memLp_uFun hn p).star).coeFn_toLp, ((memLp_uFun hn' p').star).coeFn_toLp] with g h1 h2 h3 h4
    simp only [uLp, uLpBar]
    rw [h1, h2, h3, h4]
    simp [RCLike.inner_apply]
  rw [L2.inner_def, L2.inner_def, integral_congr_ae hae, integral_conj]

/-- **The coefficients of `D_n⁻` are an orthonormal system.** -/
theorem uLpBar_orthonormal {n : ℕ} (hn : 2 ≤ n) : Orthonormal ℂ (uLpBar hn) := by
  rw [orthonormal_iff_ite]
  intro p p'
  rw [inner_uLpBar_uLpBar, (orthonormal_iff_ite.1 (uLp_orthonormal hn)) p p']
  split_ifs <;> simp

/-- The coefficient `u^{m+2,+}_p`. -/
def uPlus (m : ℕ) (p : ℕ × ℕ) : Lp ℂ 2 (haarR : Measure SL2R) := uLp (show 2 ≤ m + 2 by omega) p

/-- The coefficient `u^{m+2,-}_p`. -/
def uMinus (m : ℕ) (p : ℕ × ℕ) : Lp ℂ 2 (haarR : Measure SL2R) := uLpBar (show 2 ≤ m + 2 by omega) p

/-- **The family of all normalised coefficients of the discrete series**, indexed by the sign, the series number
`m + 2` and the pair of `K`-weights. -/
def discFam : Bool × ℕ × (ℕ × ℕ) → Lp ℂ 2 (haarR : Measure SL2R)
  | (true, m, p) => uPlus m p
  | (false, m, p) => uMinus m p

/-- **The coefficients of all holomorphic and antiholomorphic discrete series are orthonormal.** -/
theorem discFam_orthonormal : Orthonormal ℂ discFam := by
  rw [orthonormal_iff_ite]
  rintro ⟨σ, m, p⟩ ⟨σ', m', p'⟩
  have hm : 2 ≤ m + 2 := by omega
  have hm' : 2 ≤ m' + 2 := by omega
  cases σ <;> cases σ'
  · -- minus, minus
    simp only [discFam, uMinus]
    rw [inner_uLpBar_uLpBar]
    by_cases hmm : m = m'
    · subst hmm
      rw [(orthonormal_iff_ite.1 (uLp_orthonormal hm)) p p']
      by_cases hp : p = p' <;> simp [hp]
    · rw [inner_uLp_uLp_ne hm hm' (by omega) p p']
      simp [hmm]
  · -- minus, plus
    simp only [discFam, uMinus, uPlus]
    rw [← inner_conj_symm, inner_uLp_uLpBar hm' hm p' p]
    simp
  · -- plus, minus
    simp only [discFam, uMinus, uPlus]
    rw [inner_uLp_uLpBar hm hm' p p']
    simp
  · -- plus, plus
    simp only [discFam, uPlus]
    by_cases hmm : m = m'
    · subst hmm
      rw [(orthonormal_iff_ite.1 (uLp_orthonormal hm)) p p']
      by_cases hp : p = p' <;> simp [hp]
    · rw [inner_uLp_uLp_ne hm hm' (by omega) p p']
      simp [hmm]

/-- **The isotypic subspace of `D_n⁻`**. -/
def discreteSpaceBar {n : ℕ} (hn : 2 ≤ n) : Submodule ℂ (Lp ℂ 2 (haarR : Measure SL2R)) :=
  (Submodule.span ℂ (Set.range (uLpBar hn))).topologicalClosure

/-- **The discrete part** of `L²(SL(2,ℝ))`: the closed span of all matrix coefficients of the discrete series. -/
def discreteAll : Submodule ℂ (Lp ℂ 2 (haarR : Measure SL2R)) :=
  (Submodule.span ℂ (Set.range discFam)).topologicalClosure

instance discreteAll_hasOrthogonalProjection : discreteAll.HasOrthogonalProjection := by
  have : CompleteSpace discreteAll := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

instance discreteSpaceBar_hasOrthogonalProjection {n : ℕ} (hn : 2 ≤ n) :
    (discreteSpaceBar hn).HasOrthogonalProjection := by
  have : CompleteSpace (discreteSpaceBar hn) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- **The projection onto the isotypic subspace of `D_n⁻`**: `‖P_n⁻ f‖² = Σ_{j,l} |⟨u⁻_{jl}, f⟩|²`. -/
theorem norm_sq_starProjection_discreteBar {n : ℕ} (hn : 2 ≤ n) (f : Lp ℂ 2 (haarR : Measure SL2R)) :
    ‖(discreteSpaceBar hn).starProjection f‖ ^ 2 = ∑' p : ℕ × ℕ, ‖⟪uLpBar hn p, f⟫_ℂ‖ ^ 2 :=
  norm_sq_starProjection_span (uLpBar hn) (uLpBar_orthonormal hn) f

/-- **Bessel's inequality for the discrete part**: the squared norm of the projection of `f` onto the discrete part
is at most `‖f‖²`. -/
theorem norm_sq_starProjection_discreteAll_le (f : Lp ℂ 2 (haarR : Measure SL2R)) :
    ‖discreteAll.starProjection f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have := Submodule.norm_starProjection_apply_le discreteAll f
  nlinarith [norm_nonneg (discreteAll.starProjection f), norm_nonneg f]

/-- **The discrete part of the Plancherel formula**: the squared norm of the projection of `f` onto the discrete part
is the sum over all holomorphic and antiholomorphic discrete series of the squared norms of the projections onto their
isotypic subspaces. -/
theorem norm_sq_starProjection_discreteAll (f : Lp ℂ 2 (haarR : Measure SL2R)) :
    ‖discreteAll.starProjection f‖ ^ 2 =
      ∑' m : ℕ, (‖(discreteSpace (show 2 ≤ m + 2 by omega)).starProjection f‖ ^ 2 +
        ‖(discreteSpaceBar (show 2 ≤ m + 2 by omega)).starProjection f‖ ^ 2) := by
  change ‖(Submodule.span ℂ (Set.range discFam)).topologicalClosure.starProjection f‖ ^ 2 = _
  rw [norm_sq_starProjection_span discFam discFam_orthonormal f]
  set F : Bool × ℕ × (ℕ × ℕ) → ℝ := fun i => ‖⟪discFam i, f⟫_ℂ‖ ^ 2 with hF
  have hsum : Summable F := discFam_orthonormal.inner_products_summable f
  have hP : ∀ m : ℕ, ‖(discreteSpace (show 2 ≤ m + 2 by omega)).starProjection f‖ ^ 2 =
      ∑' p : ℕ × ℕ, F (true, m, p) := fun m => norm_sq_starProjection_discrete _ f
  have hM : ∀ m : ℕ, ‖(discreteSpaceBar (show 2 ≤ m + 2 by omega)).starProjection f‖ ^ 2 =
      ∑' p : ℕ × ℕ, F (false, m, p) := fun m => norm_sq_starProjection_discreteBar _ f
  simp_rw [hP, hM]
  have hs1 : Summable fun c : ℕ × (ℕ × ℕ) => F (true, c) := hsum.prod_factor true
  have hs0 : Summable fun c : ℕ × (ℕ × ℕ) => F (false, c) := hsum.prod_factor false
  have hA : Summable fun m : ℕ => ∑' p : ℕ × ℕ, F (true, m, p) := hs1.prod
  have hB : Summable fun m : ℕ => ∑' p : ℕ × ℕ, F (false, m, p) := hs0.prod
  rw [hsum.tsum_prod' (fun b => hsum.prod_factor b), tsum_bool, hs0.tsum_prod' (fun m => hs0.prod_factor m),
    hs1.tsum_prod' (fun m => hs1.prod_factor m), add_comm, ← hA.tsum_add hB]

end Lightlike.Lorentz.SL2RPlancherel
