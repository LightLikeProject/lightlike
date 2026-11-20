import Lightlike.OperatorAlgebras.GaussAvg
import Lightlike.OperatorAlgebras.FockExists
import Lightlike.OperatorAlgebras.FockIrreducible
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The Stone-von Neumann theorem for finitely many degrees of freedom

J. Dereziński, arXiv:math-ph/0511030 (read), Theorem 4 and Corollary 1, p. 12 (statements); M. Faulhuber, *Time-Frequency
Analysis*, arXiv:2204.01596 (read), §7.3.1, pp. 90-94, Theorems 7.32 and 7.35 (von Neumann's proof). For a representation
`R` of the Weyl relations of a finite-dimensional `h` on a Hilbert space `K`:

* `vnProj R = (2π)^{-d} ∫ e^{-‖z‖²/4} W z dz` is an orthogonal projection with `P₀ W f P₀ = e^{-‖f‖²/4} P₀` (`vnProj_W_vnProj`),
  nonzero on a nonzero space; a unit vector `g` of its range has the Fock vacuum expectation (`inner_W_of_vnProj`);
* `exists_fockRep_of_irreducible`, `stone_von_neumann_irreducible`: an irreducible representation on a nonzero space is a Fock
  representation, unitarily equivalent to `fockRepOf h` (Theorem 7.32, Corollary 1);
* `stone_von_neumann`: `K` is the Hilbert sum of the closed invariant subspaces `orbitSpan R gᵢ` over an orthonormal basis
  `(gᵢ)` of `ran P₀`, each carrying a Fock representation (Theorem 7.35; Theorem 4 with `L²(X) ⊗ K` as this Hilbert sum);
* `isIrreducible_iff_finrank_vnRange`: on a nonzero space the representation is irreducible iff `ran P₀` (the multiplicity
  space `K` of Theorem 4) is one-dimensional.

Representation: the symplectic space is the finite-dimensional complex inner product space `h` with `σ = Im⟪·,·⟫`, and the
reference representation is the repository's Fock representation `fockRepOf h` (the Schrödinger representation of the
sources, unitarily equivalent to it by the Bargmann transform, is not used).
-/

namespace Lightlike.OperatorAlgebras

open MeasureTheory GaussianFourier
open scoped InnerProductSpace

attribute [local instance] InnerProductSpace.complexToReal

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [FiniteDimensional ℂ h]
  [MeasurableSpace h] [BorelSpace h]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma vnConst_ne_zero : vnConst h ≠ 0 := by
  rw [vnConst, Ne, Complex.cpow_eq_zero_iff]
  push Not
  intro h0
  simp at h0

/-- **von Neumann's projection** `P₀ = (2π)^{-d} ∫ e^{-‖z‖²/4} W z dz`. -/
noncomputable def vnProj (R : CCRRep h K) (y : K) : K := (vnConst h)⁻¹ • gaussAvg R y

lemma vnProj_smul (R : CCRRep h K) (c : ℂ) (y : K) : vnProj R (c • y) = c • vnProj R y := by
  rw [vnProj, vnProj, gaussAvg_smul, smul_comm]

lemma vnProj_W_vnProj (R : CCRRep h K) (f : h) (y : K) :
    vnProj R (R.W f (vnProj R y)) = (gaussW f : ℂ) • vnProj R y := by
  simp only [vnProj, map_smul, gaussAvg_smul, gaussAvg_W_gaussAvg, smul_smul]
  congr 1
  field_simp [vnConst_ne_zero]

lemma vnProj_idem (R : CCRRep h K) (y : K) : vnProj R (vnProj R y) = vnProj R y := by
  have := vnProj_W_vnProj R 0 y
  rwa [R.W_zero_apply, show gaussW (0 : h) = 1 by simp [gaussW], Complex.ofReal_one, one_smul] at this

lemma vnConst_eq_ofReal : ∃ c : ℝ, vnConst h = c := by
  refine ⟨(2 * Real.pi) ^ ((Module.finrank ℝ h : ℝ) / 2), ?_⟩
  rw [vnConst, Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 1
  ring

lemma inner_vnProj_left (R : CCRRep h K) (x y : K) : ⟪vnProj R x, y⟫_ℂ = ⟪x, vnProj R y⟫_ℂ := by
  obtain ⟨c, hc⟩ := vnConst_eq_ofReal (h := h)
  rw [vnProj, vnProj, inner_smul_left, inner_smul_right, inner_gaussAvg_left, hc, map_inv₀, Complex.conj_ofReal]

/-- **The vacuum expectation**: a unit vector `g` in the range of `P₀` has `⟪g, W f g⟫ = e^{-‖f‖²/4}`
(Faulhuber, eq. (7.15)). -/
theorem inner_W_of_vnProj (R : CCRRep h K) {g : K} (hg : vnProj R g = g) (h1 : ‖g‖ = 1) (f : h) :
    ⟪g, R.W f g⟫_ℂ = Complex.exp (-(‖f‖ ^ 2 / 4 : ℝ)) := by
  calc ⟪g, R.W f g⟫_ℂ = ⟪vnProj R g, R.W f (vnProj R g)⟫_ℂ := by rw [hg]
    _ = ⟪g, vnProj R (R.W f (vnProj R g))⟫_ℂ := inner_vnProj_left R _ _
    _ = (gaussW f : ℂ) * ⟪g, g⟫_ℂ := by rw [vnProj_W_vnProj, hg, inner_smul_right]
    _ = Complex.exp (-(‖f‖ ^ 2 / 4 : ℝ)) := by
        rw [inner_self_eq_norm_sq_to_K, h1, gaussW]
        push_cast
        ring_nf

/-- A unit vector in the range of `P₀` exists on a nonzero space. -/
theorem exists_unit_vnProj [Nontrivial K] (R : CCRRep h K) : ∃ g : K, vnProj R g = g ∧ ‖g‖ = 1 := by
  obtain ⟨y, hy⟩ := exists_gaussAvg_ne_zero R
  have hy' : vnProj R y ≠ 0 := by
    rw [vnProj]; exact smul_ne_zero (inv_ne_zero vnConst_ne_zero) hy
  refine ⟨(‖vnProj R y‖⁻¹ : ℂ) • vnProj R y, ?_, ?_⟩
  · rw [vnProj_smul, vnProj_idem]
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy')]

/-- **Irreducibility** of a representation of the Weyl relations (Dereziński, p. 10). -/
def CCRRep.IsIrreducible (R : CCRRep h K) : Prop :=
  ∀ W : Submodule ℂ K, IsClosed (W : Set K) → (∀ f, ∀ w ∈ W, R.W f w ∈ W) → W = ⊥ ∨ W = ⊤

/-- The closed span of the vectors `W f g` is invariant. -/
lemma invariant_span_W (R : CCRRep h K) (g : K) (f : h) :
    ∀ w ∈ (Submodule.span ℂ (Set.range fun f' => R.W f' g)).topologicalClosure,
      R.W f w ∈ (Submodule.span ℂ (Set.range fun f' => R.W f' g)).topologicalClosure := by
  set S := Submodule.span ℂ (Set.range fun f' => R.W f' g)
  have hS : ∀ w ∈ S, R.W f w ∈ S := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => R.W f w ∈ S) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨f', rfl⟩
      rw [R.weyl]
      exact S.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    · simp
    · intro u v _ _ hu hv; rw [map_add]; exact S.add_mem hu hv
    · intro c u _ hu; rw [map_smul]; exact S.smul_mem c hu
  intro w hw
  have hc : Continuous (R.W f) := (R.W f).continuous
  have := map_mem_closure hc hw (fun u hu => hS u hu)
  exact this

/-- **The Stone-von Neumann theorem, irreducible case** (Dereziński, Theorem 4 and Corollary 1, p. 12; Faulhuber,
Theorem 7.32): an irreducible representation of the Weyl relations of a finite-dimensional `h` on a nonzero Hilbert
space is a Fock representation, hence unitarily equivalent to every Fock representation. -/
theorem exists_fockRep_of_irreducible [Nontrivial K] (R : CCRRep h K) (hR : R.IsIrreducible) :
    ∃ S : FockRep h K, S.toCCRRep = R := by
  obtain ⟨g, hg, h1⟩ := exists_unit_vnProj R
  set S := Submodule.span ℂ (Set.range fun f' => R.W f' g)
  have hgS : g ∈ S.topologicalClosure :=
    S.le_topologicalClosure (Submodule.subset_span ⟨0, R.W_zero_apply g⟩)
  have htop : S.topologicalClosure = ⊤ := by
    rcases hR _ S.isClosed_topologicalClosure (invariant_span_W R g) with hb | ht
    · exfalso
      have : g = 0 := by rw [hb] at hgS; exact (Submodule.mem_bot ℂ).mp hgS
      rw [this, norm_zero] at h1
      exact zero_ne_one h1
    · exact ht
  exact ⟨{ R with Ω := g, norm_Ω := h1, cyclic := htop, vacuum_expectation := inner_W_of_vnProj R hg h1 }, rfl⟩

/-- **Corollary**: an irreducible representation is unitarily equivalent to the Fock representation `fockRepOf h`. -/
theorem stone_von_neumann_irreducible [Nontrivial K] (R : CCRRep h K) (hR : R.IsIrreducible) :
    ∃ U : K ≃ₗᵢ[ℂ] FockSpace h, ∀ f ψ, U (R.W f ψ) = fockW f (U ψ) := by
  obtain ⟨S, rfl⟩ := exists_fockRep_of_irreducible R hR
  exact ⟨fockUnitary S (fockRepOf h), (fockUnitary_spec S (fockRepOf h)).2⟩

open scoped InnerProductSpace

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The restriction of a Weyl unitary to an invariant subspace. -/
noncomputable def CCRRep.restrictW (R : CCRRep h K) (M : Submodule ℂ K) (hM : ∀ f, ∀ w ∈ M, R.W f w ∈ M) (f : h) :
    M ≃ₗᵢ[ℂ] M where
  toFun w := ⟨R.W f w, hM f w w.2⟩
  invFun w := ⟨R.W (-f) w, hM (-f) w w.2⟩
  map_add' u v := by ext; simp
  map_smul' c v := by ext; simp
  left_inv w := by ext; simp [R.W_neg_W]
  right_inv w := by ext; simp [R.W_W_neg]
  norm_map' w := by simp

lemma CCRRep.restrictW_apply (R : CCRRep h K) (M : Submodule ℂ K) (hM : ∀ f, ∀ w ∈ M, R.W f w ∈ M) (f : h) (w : M) :
    (R.restrictW M hM f w : K) = R.W f w := rfl

/-- **The subrepresentation** on an invariant subspace. -/
noncomputable def CCRRep.restrict (R : CCRRep h K) (M : Submodule ℂ K) (hM : ∀ f, ∀ w ∈ M, R.W f w ∈ M) :
    CCRRep h M where
  W := R.restrictW M hM
  W_zero := by ext w; simp [CCRRep.restrictW_apply, R.W_zero_apply]
  weyl f g ψ := by ext; simp [CCRRep.restrictW_apply, R.weyl]
  continuous_line f ψ := by
    refine Continuous.subtype_mk ?_ _
    exact R.continuous_line f ψ

open MeasureTheory
open scoped InnerProductSpace

attribute [local instance] InnerProductSpace.complexToReal

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [FiniteDimensional ℂ h]
  [MeasurableSpace h] [BorelSpace h]
universe uK
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `⟪g, W u g'⟫ = e^{-‖u‖²/4} ⟪g, g'⟫` for `g, g'` in the range of `P₀`. -/
lemma inner_W_of_vnProj_pair (R : CCRRep h K) {g g' : K} (hg : vnProj R g = g) (hg' : vnProj R g' = g') (u : h) :
    ⟪g, R.W u g'⟫_ℂ = (gaussW u : ℂ) * ⟪g, g'⟫_ℂ := by
  calc ⟪g, R.W u g'⟫_ℂ = ⟪vnProj R g, R.W u (vnProj R g')⟫_ℂ := by rw [hg, hg']
    _ = ⟪g, vnProj R (R.W u (vnProj R g'))⟫_ℂ := inner_vnProj_left R _ _
    _ = (gaussW u : ℂ) * ⟪g, g'⟫_ℂ := by rw [vnProj_W_vnProj, hg', inner_smul_right]

/-- The Weyl orbits of orthogonal vectors in the range of `P₀` are orthogonal. -/
lemma inner_W_W_eq_zero (R : CCRRep h K) {g g' : K} (hg : vnProj R g = g) (hg' : vnProj R g' = g')
    (h0 : ⟪g, g'⟫_ℂ = 0) (f f' : h) : ⟪R.W f g, R.W f' g'⟫_ℂ = 0 := by
  rw [← LinearIsometryEquiv.inner_map_map (R.W (-f)), R.W_neg_W, R.weyl, inner_smul_right,
    inner_W_of_vnProj_pair R hg hg', h0, mul_zero, mul_zero]

/-- The closed span of a Weyl orbit. -/
noncomputable def orbitSpan (R : CCRRep h K) (g : K) : Submodule ℂ K :=
  (Submodule.span ℂ (Set.range fun f => R.W f g)).topologicalClosure

lemma orbitSpan_le_orthogonal (R : CCRRep h K) {g g' : K} (hg : vnProj R g = g) (hg' : vnProj R g' = g')
    (h0 : ⟪g, g'⟫_ℂ = 0) : orbitSpan R g' ≤ (orbitSpan R g)ᗮ := by
  have h1 : Submodule.span ℂ (Set.range fun f => R.W f g') ≤ (Submodule.span ℂ (Set.range fun f => R.W f g))ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨f', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction (p := fun u _ => ⟪u, R.W f' g'⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨f, rfl⟩; exact inner_W_W_eq_zero R hg hg' h0 f f'
    · simp
    · intro a b _ _ ha hb; rw [inner_add_left, ha, hb, add_zero]
    · intro c a _ ha; rw [inner_smul_left, ha, mul_zero]
  have h2 : (Submodule.span ℂ (Set.range fun f => R.W f g))ᗮ = (orbitSpan R g)ᗮ := by
    rw [orbitSpan, Submodule.orthogonal_closure]
  rw [orbitSpan, ← h2]
  exact Submodule.topologicalClosure_minimal _ h1 (Submodule.isClosed_orthogonal _)

/-- The fixed vectors of `P₀`. -/
noncomputable def vnRange (R : CCRRep h K) : Submodule ℂ K where
  carrier := {g | vnProj R g = g}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [vnProj, gaussAvg_add, smul_add, ← vnProj, ← vnProj, ha, hb]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    have := vnProj_smul R 0 0
    simpa using this
  smul_mem' c g hg := by
    simp only [Set.mem_ofPred_eq] at *
    rw [vnProj_smul, hg]

lemma isClosed_vnRange (R : CCRRep h K) : IsClosed (vnRange R : Set K) := by
  have hc : Continuous (vnProj R) := by
    have : vnProj R = fun y => (vnConst h)⁻¹ • gaussAvgCLM R y := rfl
    rw [this]; exact continuous_const.smul (gaussAvgCLM R).continuous
  exact isClosed_eq hc continuous_id

/-- The Gaussian average of a subrepresentation is the restriction of the Gaussian average. -/
lemma coe_gaussAvg_restrict (R : CCRRep h K) (M : Submodule ℂ K) (hM : ∀ f, ∀ w ∈ M, R.W f w ∈ M)
    [CompleteSpace M] (w : M) : ((gaussAvg (R.restrict M hM) w : M) : K) = gaussAvg R w := by
  rw [gaussAvg, gaussAvg, ← M.subtypeL_apply, ← ContinuousLinearMap.integral_comp_comm _
    (integrable_gaussW_smul_W (R.restrict M hM) w)]
  rfl

/-- **A closed invariant subspace orthogonal to the range of `P₀` is zero.** -/
theorem eq_bot_of_orthogonal_vnRange (R : CCRRep h K) (M : Submodule ℂ K) (hM : ∀ f, ∀ w ∈ M, R.W f w ∈ M)
    (hMc : IsClosed (M : Set K)) (horth : ∀ g ∈ vnRange R, ∀ m ∈ M, ⟪g, m⟫_ℂ = 0) : M = ⊥ := by
  by_contra hne
  have : CompleteSpace M := hMc.completeSpace_coe
  have : Nontrivial M := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨w, hw⟩ := exists_gaussAvg_ne_zero (R.restrict M hM)
  set y : K := vnProj R w with hy
  have hyM : y ∈ M := by
    rw [hy, vnProj, ← coe_gaussAvg_restrict R M hM w]
    exact M.smul_mem _ (gaussAvg (R.restrict M hM) w).2
  have hyR : y ∈ vnRange R := vnProj_idem R w
  have h0 : y = 0 := inner_self_eq_zero.mp (horth y hyR y hyM)
  apply hw
  have : ((gaussAvg (R.restrict M hM) w : M) : K) = 0 := by
    rw [coe_gaussAvg_restrict R M hM w]
    have := congrArg (fun v => vnConst h • v) h0
    simpa [hy, vnProj, smul_smul, mul_inv_cancel₀ vnConst_ne_zero] using this
  exact Subtype.ext this

lemma orbitSpan_invariant (R : CCRRep h K) (g : K) : ∀ f, ∀ w ∈ orbitSpan R g, R.W f w ∈ orbitSpan R g :=
  fun f => invariant_span_W R g f

lemma isClosed_orbitSpan (R : CCRRep h K) (g : K) : IsClosed (orbitSpan R g : Set K) :=
  Submodule.isClosed_topologicalClosure _

lemma mem_orbitSpan_self (R : CCRRep h K) (g : K) : g ∈ orbitSpan R g :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨0, R.W_zero_apply g⟩)

/-- The Fock representation on the orbit of a unit vector of the range of `P₀`. -/
theorem exists_fockRep_orbitSpan (R : CCRRep h K) {g : K} (hg : vnProj R g = g) (h1 : ‖g‖ = 1) :
    ∃ S : FockRep h (orbitSpan R g),
      S.toCCRRep = R.restrict (orbitSpan R g) (orbitSpan_invariant R g) ∧ (S.Ω : K) = g := by
  set M := orbitSpan R g
  set Rm := R.restrict M (orbitSpan_invariant R g)
  let Ω : M := ⟨g, mem_orbitSpan_self R g⟩
  have hcyc : (Submodule.span ℂ (Set.range fun f => Rm.W f Ω)).topologicalClosure = ⊤ := by
    set S' := Submodule.span ℂ (Set.range fun f => Rm.W f Ω) with hS'
    have hT : Submodule.span ℂ (Set.range fun f => R.W f g) ≤ S'.topologicalClosure.map M.subtype := by
      rw [Submodule.span_le]
      rintro _ ⟨f, rfl⟩
      exact ⟨Rm.W f Ω, S'.le_topologicalClosure (Submodule.subset_span ⟨f, rfl⟩), rfl⟩
    have hTc : IsClosed ((S'.topologicalClosure.map M.subtype : Submodule ℂ K) : Set K) := by
      rw [Submodule.map_coe]
      exact (isClosed_orbitSpan R g).isClosedEmbedding_subtypeVal.isClosedMap _ S'.isClosed_topologicalClosure
    have hle : M ≤ S'.topologicalClosure.map M.subtype := Submodule.topologicalClosure_minimal _ hT hTc
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hle x.2)
    have : y = x := Subtype.ext hyx
    rwa [← this]
  refine ⟨⟨Rm, Ω, ?_, hcyc, fun f => ?_⟩, rfl, rfl⟩
  · exact h1
  rw [Submodule.coe_inner]
  exact inner_W_of_vnProj R hg h1 f

/-- **The Stone-von Neumann theorem** (Dereziński, Theorem 4, p. 12; Faulhuber, Theorems 7.32 and 7.35): a representation
of the Weyl relations of a finite-dimensional `h` on a Hilbert space `K` is the Hilbert sum of closed invariant subspaces,
on each of which it is a Fock representation (hence unitarily equivalent to `fockRepOf h`). -/
theorem stone_von_neumann (R : CCRRep h K) :
    ∃ (ι : Type uK) (g : ι → K), (∀ i, vnProj R (g i) = g i ∧ ‖g i‖ = 1) ∧
      IsHilbertSum ℂ (fun i => orbitSpan R (g i)) (fun i => (orbitSpan R (g i)).subtypeₗᵢ) ∧
      ∀ i, ∃ S : FockRep h (orbitSpan R (g i)),
        S.toCCRRep = R.restrict (orbitSpan R (g i)) (orbitSpan_invariant R (g i)) := by
  have : CompleteSpace (vnRange R) := (isClosed_vnRange R).completeSpace_coe
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ (vnRange R)
  refine ⟨w, fun i => (b i : K), fun i => ⟨(b i).2, by
    show ‖((b i : vnRange R) : K)‖ = 1
    simpa using b.orthonormal.1 i⟩, ?_, ?_⟩
  · have : ∀ i, CompleteSpace (orbitSpan R (b i : K)) := fun i => (isClosed_orbitSpan R _).completeSpace_coe
    refine IsHilbertSum.mkInternal _ ?_ ?_
    · intro i j hij v w'
      have hle := orbitSpan_le_orthogonal R (g := (b i : K)) (g' := (b j : K)) (b i).2 (b j).2
        (by rw [← Submodule.coe_inner]; exact b.orthonormal.2 hij)
      exact (Submodule.mem_orthogonal _ _).mp (hle w'.2) v v.2
    · set S := (⨆ i, orbitSpan R (b i : K)).topologicalClosure with hSdef
      have hSc : IsClosed (S : Set K) := Submodule.isClosed_topologicalClosure _
      have : CompleteSpace S := hSc.completeSpace_coe
      have hsup : ∀ f, ∀ v ∈ ⨆ i, orbitSpan R (b i : K), R.W f v ∈ ⨆ i, orbitSpan R (b i : K) := by
        intro f v hv
        refine Submodule.iSup_induction _ (motive := fun v => R.W f v ∈ ⨆ i, orbitSpan R (b i : K)) hv
          (fun i x hx => Submodule.mem_iSup_of_mem i (orbitSpan_invariant R _ f x hx)) (by simp)
          (fun x y hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
      have hSinv : ∀ f, ∀ v ∈ S, R.W f v ∈ S := fun f v hv =>
        map_mem_closure (R.W f).continuous hv (fun u hu => hsup f u hu)
      have hperp : ∀ f, ∀ m ∈ Sᗮ, R.W f m ∈ Sᗮ := by
        intro f m hm
        rw [Submodule.mem_orthogonal] at hm ⊢
        intro u hu
        rw [← LinearIsometryEquiv.inner_map_map (R.W (-f)), R.W_neg_W]
        exact hm _ (hSinv (-f) u hu)
      have hmaps : Set.MapsTo (Subtype.val : vnRange R → K)
          ((Submodule.span ℂ (Set.range b) : Submodule ℂ (vnRange R)) : Set (vnRange R)) (S : Set K) := by
        intro u hu
        refine Submodule.span_induction (p := fun (u : vnRange R) _ => (u : K) ∈ S) ?_ ?_ ?_ ?_ hu
        · rintro _ ⟨i, rfl⟩
          exact Submodule.le_topologicalClosure _ (Submodule.mem_iSup_of_mem i (mem_orbitSpan_self R _))
        · simp
        · intro x y _ _ hx hy; exact S.add_mem hx hy
        · intro c x _ hx; exact S.smul_mem c hx
      have hrange : ∀ g ∈ vnRange R, g ∈ S := by
        intro g hg
        have hcl : (⟨g, hg⟩ : vnRange R) ∈
            closure ((Submodule.span ℂ (Set.range b) : Submodule ℂ (vnRange R)) : Set (vnRange R)) := by
          rw [← Submodule.topologicalClosure_coe, b.dense_span]; trivial
        have hmap := map_mem_closure continuous_subtype_val hcl hmaps
        rwa [hSc.closure_eq] at hmap
      have hbot := eq_bot_of_orthogonal_vnRange R Sᗮ hperp (Submodule.isClosed_orthogonal _)
        (fun g hg m hm => (Submodule.mem_orthogonal _ _).mp hm g (hrange g hg))
      rw [Submodule.orthogonal_eq_bot_iff] at hbot
      rw [hbot]
  · intro i
    obtain ⟨S, hS, -⟩ := exists_fockRep_orbitSpan R (b i).2 (by rw [Submodule.norm_coe, b.orthonormal.1 i])
    exact ⟨S, hS⟩

open MeasureTheory
open scoped InnerProductSpace

attribute [local instance] InnerProductSpace.complexToReal

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [FiniteDimensional ℂ h]
  [MeasurableSpace h] [BorelSpace h]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The orthogonal complement of a closed invariant subspace is invariant. -/
lemma orthogonal_invariant (R : CCRRep h K) {M : Submodule ℂ K} (hM : ∀ f, ∀ w ∈ M, R.W f w ∈ M) :
    ∀ f, ∀ m ∈ Mᗮ, R.W f m ∈ Mᗮ := by
  intro f m hm
  rw [Submodule.mem_orthogonal] at hm ⊢
  intro u hu
  rw [← LinearIsometryEquiv.inner_map_map (R.W (-f)), R.W_neg_W]
  exact hm _ (hM (-f) u hu)

/-- If `ran P₀` is spanned by the unit vector `g`, the orbit of `g` is everything. -/
lemma orbitSpan_eq_top (R : CCRRep h K) {g : K} (hgR : ∀ g' ∈ vnRange R, g' ∈ Submodule.span ℂ {g}) :
    orbitSpan R g = ⊤ := by
  have : CompleteSpace (orbitSpan R g) := (isClosed_orbitSpan R g).completeSpace_coe
  have hbot := eq_bot_of_orthogonal_vnRange R (orbitSpan R g)ᗮ (orthogonal_invariant R (orbitSpan_invariant R g))
    (Submodule.isClosed_orthogonal _) (fun g' hg' m hm => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hgR g' hg')
      rw [inner_smul_left, (Submodule.mem_orthogonal _ _).mp hm g (mem_orbitSpan_self R g), mul_zero])
  rwa [Submodule.orthogonal_eq_bot_iff] at hbot

/-- **Dereziński, Theorem 4, p. 12: the representation is irreducible iff the multiplicity space is `ℂ`** (here:
`ran P₀` is one-dimensional). -/
theorem isIrreducible_iff_finrank_vnRange [Nontrivial K] (R : CCRRep h K) :
    R.IsIrreducible ↔ Module.finrank ℂ (vnRange R) = 1 := by
  obtain ⟨g, hg, h1⟩ := exists_unit_vnProj R
  have hg0 : g ≠ 0 := by rintro rfl; simp at h1
  have hgR : g ∈ vnRange R := hg
  constructor
  · intro hR
    have htop : orbitSpan R g = ⊤ := by
      rcases hR _ (isClosed_orbitSpan R g) (orbitSpan_invariant R g) with hb | ht
      · exact absurd ((Submodule.mem_bot ℂ).mp (hb ▸ mem_orbitSpan_self R g)) hg0
      · exact ht
    -- every vector of `ran P₀` is a multiple of `g`
    have hspan : ∀ g' ∈ vnRange R, g' ∈ Submodule.span ℂ {g} := by
      intro g' hg'
      set d := g' - (⟪g, g'⟫_ℂ) • g with hd
      have hdR : d ∈ vnRange R := (vnRange R).sub_mem hg' ((vnRange R).smul_mem _ hgR)
      have hdg : ⟪g, d⟫_ℂ = 0 := by
        rw [hd, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, h1]; simp
      have hle := orbitSpan_le_orthogonal R hg hdR hdg
      rw [htop] at hle
      have hd0 : d = 0 := by
        have : d ∈ (⊤ : Submodule ℂ K)ᗮ := hle (mem_orbitSpan_self R d)
        rwa [Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at this
      have : g' = (⟪g, g'⟫_ℂ) • g := by rw [← sub_eq_zero, ← hd, hd0]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g)
    have : vnRange R = Submodule.span ℂ {g} :=
      le_antisymm hspan ((Submodule.span_singleton_le_iff_mem g _).mpr hgR)
    rw [this]
    exact finrank_span_singleton hg0
  · intro hfin W hWc hW
    have hspan : ∀ g' ∈ vnRange R, g' ∈ Submodule.span ℂ {g} := by
      intro g' hg'
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨g, hgR⟩ : vnRange R) (by simpa using hg0)).mp hfin
        ⟨g', hg'⟩
      have : g' = c • g := by simpa using (congrArg Subtype.val hc).symm
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g)
    have htop := orbitSpan_eq_top R hspan
    obtain ⟨S, hS, hSΩ⟩ := exists_fockRep_orbitSpan R hg h1
    by_cases hb : W = ⊥
    · exact Or.inl hb
    right
    obtain ⟨ψ, hψW, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    -- the orbit of `ψ` is dense: the representation on `orbitSpan R g = K` is a Fock representation
    have hψM : ψ ∈ orbitSpan R g := htop ▸ Submodule.mem_top
    set ψ' : orbitSpan R g := ⟨ψ, hψM⟩ with hψ'
    have hψ'0 : ψ' ≠ 0 := fun h0 => hψ0 (congrArg Subtype.val h0)
    have : CompleteSpace (orbitSpan R g) := (isClosed_orbitSpan R g).completeSpace_coe
    have hcyc := fockRep_cyclic S hψ'0
    have hWorb : orbitSpan R ψ ≤ W := Submodule.topologicalClosure_minimal _
      (Submodule.span_le.mpr (by rintro _ ⟨f, rfl⟩; exact hW f ψ hψW)) hWc
    rw [eq_top_iff]
    intro x _
    apply hWorb
    have hxM : x ∈ orbitSpan R g := htop ▸ Submodule.mem_top
    have hcl : (⟨x, hxM⟩ : orbitSpan R g) ∈
        closure ((Submodule.span ℂ (Set.range fun f => S.W f ψ') : Submodule ℂ (orbitSpan R g)) :
          Set (orbitSpan R g)) := by
      rw [← Submodule.topologicalClosure_coe, hcyc]; trivial
    have hmaps : Set.MapsTo (Subtype.val : orbitSpan R g → K)
        ((Submodule.span ℂ (Set.range fun f => S.W f ψ') : Submodule ℂ (orbitSpan R g)) : Set (orbitSpan R g))
        ((Submodule.span ℂ (Set.range fun f => R.W f ψ) : Submodule ℂ K) : Set K) := by
      intro u hu
      refine Submodule.span_induction
        (p := fun (u : orbitSpan R g) _ => (u : K) ∈ Submodule.span ℂ (Set.range fun f => R.W f ψ)) ?_ ?_ ?_ ?_ hu
      · rintro _ ⟨f, rfl⟩
        rw [show ((S.W f ψ' : orbitSpan R g) : K) = R.W f ψ by rw [hS]; rfl]
        exact Submodule.subset_span ⟨f, rfl⟩
      · simp
      · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
      · intro c a _ ha; exact Submodule.smul_mem _ c ha
    exact map_mem_closure continuous_subtype_val hcl hmaps

end Lightlike.OperatorAlgebras
