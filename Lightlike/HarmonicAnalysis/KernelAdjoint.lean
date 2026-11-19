import Lightlike.HarmonicAnalysis.KernelOperator

/-!
# The adjoint of a kernel operator

`k ↦ T_k` is a bounded linear map `kerOpL` from `C(G × G, ℂ)`, and `(T_k)* = T_{k†}`. For pure tensors this
is the adjoint of a rank-one operator; the span of the pure tensors is dense in `C(G × G, ℂ)`
(Stone–Weierstrass), and both sides are continuous in `k`.

Supporting lemma for the Peter–Weyl theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

lemma kerCurry_add (k k' : C(G × G, ℂ)) (x : G) : kerCurry (k + k') x = kerCurry k x + kerCurry k' x := by
  ext y; simp [kerCurry_apply]

lemma kerCurry_smul (c : ℂ) (k : C(G × G, ℂ)) (x : G) :
    kerCurry (c • k) x = starRingEnd ℂ c • kerCurry k x := by
  ext y; simp [kerCurry_apply]

lemma norm_kerCurry_le (k : C(G × G, ℂ)) : ‖kerCurry k‖ ≤ ‖k‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun y => ?_
  simpa [kerCurry_apply] using (k.norm_coe_le_norm (x, y))

lemma kerOp_add (k k' : C(G × G, ℂ)) : kerOp μ (k + k') = kerOp μ k + kerOp μ k' := by
  ext ψ : 1
  rw [ContinuousLinearMap.add_apply]
  unfold kerOp
  simp only [ContinuousLinearMap.comp_apply]
  rw [← map_add]
  congr 1
  ext x
  simp [kerToC_apply, kerCurry_add, inner_add_left]

lemma kerOp_smul (c : ℂ) (k : C(G × G, ℂ)) : kerOp μ (c • k) = c • kerOp μ k := by
  ext ψ : 1
  rw [ContinuousLinearMap.smul_apply]
  unfold kerOp
  simp only [ContinuousLinearMap.comp_apply]
  rw [← map_smul]
  congr 1
  ext x
  simp [kerToC_apply, kerCurry_smul, inner_smul_left]

lemma norm_kerOp_le (k : C(G × G, ℂ)) :
    ‖kerOp μ k‖ ≤ (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖)) * ‖k‖ := by
  unfold kerOp
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖kerToC μ k‖ ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kerCurry k‖ :=
    LinearMap.mkContinuous_norm_le _ (by positivity) _
  calc ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kerToC μ k‖
      ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kerCurry k‖) := by
        gcongr
    _ ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖k‖) := by
        gcongr; exact norm_kerCurry_le k
    _ = _ := by ring

/-- `k ↦ T_k` as a bounded linear map. -/
def kerOpL : C(G × G, ℂ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  LinearMap.mkContinuous
    { toFun := kerOp μ, map_add' := kerOp_add μ, map_smul' := kerOp_smul μ }
    ((‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖)))
    (norm_kerOp_le μ)

lemma kerOpL_apply (k : C(G × G, ℂ)) : kerOpL μ k = kerOp μ k := rfl

/-- The pure tensor kernel `a ⊗ b`. -/
def tens (a b : C(G, ℂ)) : C(G × G, ℂ) := ⟨fun p => a p.1 * b p.2, by fun_prop⟩

lemma tens_apply (a b : C(G, ℂ)) (x y : G) : tens a b (x, y) = a x * b y := rfl

lemma kerDagger_tens (a b : C(G, ℂ)) : kerDagger (tens a b) = tens (star b) (star a) := by
  ext ⟨x, y⟩
  simp [kerDagger_apply, tens_apply, mul_comm]

lemma kerOp_tens (a b : C(G, ℂ)) (ψ : Lp ℂ 2 μ) :
    kerOp μ (tens a b) ψ =
      inner ℂ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (star b)) ψ • ContinuousMap.toLp (E := ℂ) 2 μ ℂ a :=
  kerOp_tensor μ a b ψ

/-- The adjoint of the rank-one operator of a pure tensor. -/
lemma adjoint_kerOp_tens (a b : C(G, ℂ)) :
    ContinuousLinearMap.adjoint (kerOp μ (tens a b)) = kerOp μ (tens (star b) (star a)) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro ψ χ
  rw [kerOp_tens, kerOp_tens, star_star, inner_smul_left, inner_smul_right]
  rw [← inner_conj_symm (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (star b)) χ]
  simp [mul_comm]

lemma kerDagger_add (k k' : C(G × G, ℂ)) : kerDagger (k + k') = kerDagger k + kerDagger k' := by
  ext ⟨x, y⟩; simp [kerDagger_apply]

lemma kerDagger_smul (c : ℂ) (k : C(G × G, ℂ)) : kerDagger (c • k) = starRingEnd ℂ c • kerDagger k := by
  ext ⟨x, y⟩; simp [kerDagger_apply]

lemma continuous_kerDagger : Continuous (kerDagger : C(G × G, ℂ) → C(G × G, ℂ)) := by
  let f : C(G × G, ℂ) →+ C(G × G, ℂ) :=
    { toFun := kerDagger
      map_zero' := by ext ⟨x, y⟩; simp [kerDagger_apply]
      map_add' := kerDagger_add }
  refine AddMonoidHomClass.continuous_of_bound f 1 fun k => ?_
  rw [one_mul]
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun p => ?_
  show ‖starRingEnd ℂ (k (p.2, p.1))‖ ≤ ‖k‖
  simpa using k.norm_coe_le_norm (p.2, p.1)

/-- The span of the pure tensors, as a star subalgebra of `C(G × G, ℂ)`. -/
def tensAlgebra : StarSubalgebra ℂ C(G × G, ℂ) where
  carrier := Submodule.span ℂ (Set.range fun p : C(G, ℂ) × C(G, ℂ) => tens p.1 p.2)
  mul_mem' := by
    intro a b ha hb
    have h1 : a * b ∈ Submodule.span ℂ (Set.range fun p : C(G, ℂ) × C(G, ℂ) => tens p.1 p.2) *
        Submodule.span ℂ (Set.range fun p : C(G, ℂ) × C(G, ℂ) => tens p.1 p.2) :=
      Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨⟨a1, b1⟩, rfl⟩, _, ⟨⟨a2, b2⟩, rfl⟩, rfl⟩
    exact ⟨(a1 * a2, b1 * b2), by ext ⟨x, y⟩; simp [tens_apply]; ring⟩
  one_mem' := Submodule.subset_span ⟨(1, 1), by ext ⟨x, y⟩; simp [tens_apply]⟩
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := fun c => by
    have : algebraMap ℂ C(G × G, ℂ) c = c • (1 : C(G × G, ℂ)) := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨(1, 1), by ext ⟨x, y⟩; simp [tens_apply]⟩)
  star_mem' := by
    intro a ha
    refine Submodule.span_induction
      (p := fun x _ => star x ∈ Submodule.span ℂ (Set.range fun p : C(G, ℂ) × C(G, ℂ) => tens p.1 p.2))
      ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨⟨a1, b1⟩, rfl⟩
      exact Submodule.subset_span ⟨(star a1, star b1), by ext ⟨x, y⟩; simp [tens_apply]⟩
    · simpa using Submodule.zero_mem _
    · intro x y _ _ hx hy
      simpa using Submodule.add_mem _ hx hy
    · intro c x _ hx
      simpa using Submodule.smul_mem _ (starRingEnd ℂ c) hx

/-- Continuous functions separate the points of a compact Hausdorff space. -/
lemma exists_continuousMap_ne {g h : G} (hgh : g ≠ h) : ∃ a : C(G, ℂ), a g ≠ a h := by
  obtain ⟨f, hf0, hf1, -⟩ := exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := g))
    (isClosed_singleton (x := h)) (Set.disjoint_singleton.2 hgh)
  refine ⟨(ContinuousMap.mk (fun r : ℝ => (r : ℂ)) Complex.continuous_ofReal).comp f, ?_⟩
  simp [hf0 rfl, hf1 rfl]

/-- The span of the pure tensors is dense in `C(G × G, ℂ)` (Stone–Weierstrass). -/
theorem dense_tensSpan :
    Dense (Submodule.span ℂ (Set.range fun p : C(G, ℂ) × C(G, ℂ) => tens p.1 p.2) : Set C(G × G, ℂ)) := by
  have hS : (tensAlgebra (G := G)).SeparatesPoints := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hne
    by_cases hx : x = x'
    · have hy : y ≠ y' := fun hy => hne (by rw [hx, hy])
      obtain ⟨b, hb⟩ := exists_continuousMap_ne hy
      refine ⟨tens 1 b, ⟨tens 1 b, Submodule.subset_span ⟨(1, b), rfl⟩, rfl⟩, ?_⟩
      simpa [tens_apply, hx] using hb
    · obtain ⟨a, ha⟩ := exists_continuousMap_ne hx
      refine ⟨tens a 1, ⟨tens a 1, Submodule.subset_span ⟨(a, 1), rfl⟩, rfl⟩, ?_⟩
      simpa [tens_apply] using ha
  have := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hS
  rw [dense_iff_closure_eq]
  have h3 := congrArg (fun A : StarSubalgebra ℂ C(G × G, ℂ) => (A : Set C(G × G, ℂ))) this
  have h4 : closure ((tensAlgebra (G := G) : StarSubalgebra ℂ C(G × G, ℂ)) : Set C(G × G, ℂ)) = Set.univ := by
    simpa [StarSubalgebra.topologicalClosure_coe] using h3
  exact h4

/-- **The adjoint of a kernel operator.** `(T_k)* = T_{k†}` with `k†(x, y) = conj k(y, x)`. -/
theorem adjoint_kerOp (k : C(G × G, ℂ)) :
    ContinuousLinearMap.adjoint (kerOp μ k) = kerOp μ (kerDagger k) := by
  let Z : Set C(G × G, ℂ) := {k | ContinuousLinearMap.adjoint (kerOpL μ k) = kerOpL μ (kerDagger k)}
  have hZc : IsClosed Z :=
    isClosed_eq ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Lp ℂ 2 μ) (F := Lp ℂ 2 μ)).continuous.comp
      (kerOpL μ).continuous) ((kerOpL μ).continuous.comp continuous_kerDagger)
  have hspan : (Submodule.span ℂ (Set.range fun p : C(G, ℂ) × C(G, ℂ) => tens p.1 p.2) : Set C(G × G, ℂ)) ⊆ Z := by
    intro k hk
    refine Submodule.span_induction (p := fun x _ => x ∈ Z) ?_ ?_ ?_ ?_ hk
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      show ContinuousLinearMap.adjoint (kerOpL μ (tens a b)) = kerOpL μ (kerDagger (tens a b))
      rw [kerOpL_apply, kerOpL_apply, kerDagger_tens]
      exact adjoint_kerOp_tens μ a b
    · show ContinuousLinearMap.adjoint (kerOpL μ 0) = kerOpL μ (kerDagger 0)
      have : kerDagger (0 : C(G × G, ℂ)) = 0 := by ext ⟨x, y⟩; simp [kerDagger_apply]
      simp [this]
    · intro x y _ _ hx hy
      show ContinuousLinearMap.adjoint (kerOpL μ (x + y)) = kerOpL μ (kerDagger (x + y))
      rw [map_add, map_add, kerDagger_add, map_add]
      exact congrArg₂ (· + ·) hx hy
    · intro c x _ hx
      show ContinuousLinearMap.adjoint (kerOpL μ (c • x)) = kerOpL μ (kerDagger (c • x))
      rw [kerDagger_smul, map_smul (kerOpL μ), map_smul (kerOpL μ), LinearIsometryEquiv.map_smulₛₗ, hx]
  have hall : k ∈ Z := by
    have : k ∈ closure (Submodule.span ℂ (Set.range fun p : C(G, ℂ) × C(G, ℂ) => tens p.1 p.2) : Set C(G × G, ℂ)) := by
      rw [dense_tensSpan.closure_eq]; trivial
    exact closure_minimal hspan hZc this
  exact hall

end

end Lightlike.HarmonicAnalysis
