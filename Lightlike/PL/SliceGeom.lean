import Lightlike.PL.CellGeom
import Lightlike.PL.Convex

/-!
# Geometric realisation of the cells of a slicing

The cells of a slicing of a geometric complex `K` by affine functionals `H` form a
`CellStructure`: the open part of a cell `(σ, s)` is the set of points of `σ°` where each `H i`
has sign `s i`, and its closed part is the set of points of the closed simplex of `σ` where each
`H i` has sign `0` or `s i`.

## Main results

* `exists_exit_time`: the first time a ray leaves a region cut out by finitely many affine
  inequalities.
-/

open Finset

namespace Lightlike.PL

/-- **The first exit time of a ray.** Finitely many affine functions `t ↦ a i + t * b i`, positive
at `0` and at `1`, and an upper bound `t₁ ≥ 1`: there is a time `T ∈ [1, t₁]` at which all are
nonnegative and which is either `t₁` or a zero of one of them. -/
lemma exists_exit_time {ι : Type*} [DecidableEq ι] (I : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ I, 0 < a i) (hab : ∀ i ∈ I, 0 < a i + b i) {t₁ : ℝ} (h1 : 1 ≤ t₁) :
    ∃ T : ℝ, 1 ≤ T ∧ T ≤ t₁ ∧ (∀ i ∈ I, 0 ≤ a i + T * b i) ∧
      (T = t₁ ∨ ∃ i ∈ I, a i + T * b i = 0) := by
  induction I using Finset.induction_on with
  | empty => exact ⟨t₁, h1, le_rfl, by simp, .inl rfl⟩
  | insert j I hj ih =>
    obtain ⟨T, hT1, hTt, hI, hcase⟩ := ih (fun i hi => ha i (mem_insert_of_mem hi))
      (fun i hi => hab i (mem_insert_of_mem hi))
    have haj := ha j (mem_insert_self j I)
    have habj := hab j (mem_insert_self j I)
    by_cases hnn : 0 ≤ a j + T * b j
    · refine ⟨T, hT1, hTt, fun i hi => ?_, ?_⟩
      · rcases mem_insert.1 hi with rfl | hi
        · exact hnn
        · exact hI i hi
      · rcases hcase with h | ⟨i, hi, h⟩
        · exact .inl h
        · exact .inr ⟨i, mem_insert_of_mem hi, h⟩
    · replace hnn := lt_of_not_ge hnn
      have hbj : b j < 0 := by
        by_contra h
        replace h := le_of_not_gt h
        nlinarith
      set T' := a j / -b j with hT'
      have hmul : T' * -b j = a j := by
        rw [hT']; exact div_mul_cancel₀ _ (neg_ne_zero.2 hbj.ne)
      have hT'1 : 1 < T' := by nlinarith
      have hT'T : T' < T := by nlinarith
      have hz : a j + T' * b j = 0 := by nlinarith
      refine ⟨T', hT'1.le, hT'T.le.trans hTt, fun i hi => ?_, .inr ⟨j, mem_insert_self j I, hz⟩⟩
      rcases mem_insert.1 hi with rfl | hi
      · exact hz.ge
      · have h1 := hab i (mem_insert_of_mem hi)
        have h2 := hI i hi
        by_contra hneg
        replace hneg := lt_of_not_ge hneg
        have hTpos : 0 < T - 1 := by linarith
        nlinarith [mul_nonneg (sub_nonneg.2 hT'T.le) h1.le, mul_nonneg (sub_nonneg.2 hT'1.le) h2,
          mul_pos hTpos (neg_pos.2 hneg)]


/-! ## Signs -/

/-- A nonzero sign times a number of that sign is positive. -/
lemma sign_mul_pos {s : SignType} {r : ℝ} (h : SignType.sign r = s) (hs : s ≠ 0) :
    0 < (s : ℝ) * r := by
  subst h
  rcases lt_trichotomy r 0 with hr | hr | hr
  · simp [sign_neg hr]; linarith
  · simp [hr] at hs
  · simp [sign_pos hr, hr]

/-- If a nonzero sign times a number is nonnegative, the number has sign `0` or that sign. -/
lemma sign_of_mul_nonneg {s : SignType} {r : ℝ} (hs : s ≠ 0) (h : 0 ≤ (s : ℝ) * r) :
    SignType.sign r = 0 ∨ SignType.sign r = s := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · right
    rw [sign_neg hr]
    cases s <;> simp_all <;> linarith
  · left; simp [hr]
  · right
    rw [sign_pos hr]
    cases s <;> simp_all <;> linarith

/-- Signs `0` or `s` are preserved by convex combinations. -/
lemma closedSign_combo {s : SignType} {r₁ r₂ a : ℝ} (h₁ : SignType.sign r₁ = 0 ∨ SignType.sign r₁ = s)
    (h₂ : SignType.sign r₂ = 0 ∨ SignType.sign r₂ = s) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    SignType.sign (a * r₁ + (1 - a) * r₂) = 0 ∨ SignType.sign (a * r₁ + (1 - a) * r₂) = s := by
  have hb : 0 ≤ 1 - a := by linarith
  by_cases hs : s = 0
  · subst hs
    left
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp_all
  · refine sign_of_mul_nonneg hs ?_
    have e₁ : 0 ≤ (s : ℝ) * r₁ := by
      rcases h₁ with h | h
      · simp [sign_eq_zero_iff.1 h]
      · exact (sign_mul_pos h hs).le
    have e₂ : 0 ≤ (s : ℝ) * r₂ := by
      rcases h₂ with h | h
      · simp [sign_eq_zero_iff.1 h]
      · exact (sign_mul_pos h hs).le
    nlinarith [mul_nonneg ha0 e₁, mul_nonneg hb e₂]


/-! ## The cell structure -/

namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] {ι : Type*}

/-- The **closed part** of a cell `(σ, s)`: the points of the closed simplex of `σ` where each
`H i` has sign `0` or `s i`. -/
def sliceHull (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι) : Set E :=
  convexHull ℝ (c.1 : Set E) ∩
    {x | ∀ i, SignType.sign (H i x) = 0 ∨ SignType.sign (H i x) = (show Finset E × (ι → SignType) from c).2 i}

omit [DecidableEq E] in
/-- The closed part of a cell is convex. -/
lemma convex_sliceHull (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι) : Convex ℝ (sliceHull H c) := by
  refine (convex_convexHull ℝ _).inter ?_
  intro x hx y hy a b ha hb hab i
  have hb' : b = 1 - a := by linarith
  subst hb'
  show SignType.sign (H i (a • x + (1 - a) • y)) = 0 ∨ _
  rw [aff_combo]
  exact closedSign_combo (hx i) (hy i) ha (by linarith)

omit [DecidableEq E] in
/-- The open part of a cell lies in its closed part. -/
lemma cellSet_subset_sliceHull (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι) :
    cellSet (fun i => ⇑(H i)) c ⊆ sliceHull H c :=
  fun _ hx => ⟨openHull_subset_convexHull _ hx.1, fun i => .inr (hx.2 i)⟩

omit [DecidableEq E] in
/-- Closed parts increase with the cell order. -/
lemma sliceHull_mono (H : ι → E →ᵃ[ℝ] ℝ) {c' c : CellIdx E ι} (h : c' ≤ c) :
    sliceHull H c' ⊆ sliceHull H c := by
  intro x hx
  refine ⟨convexHull_mono (by exact_mod_cast h.1) hx.1, fun i => ?_⟩
  rcases hx.2 i with h0 | h0
  · exact .inl h0
  · rcases h.2 i with h1 | h1
    · left; rw [h0]; exact h1
    · right; rw [← h1]; exact h0

omit [DecidableEq E] in
/-- A point of the closed part of a cell lies in the open part of a smaller cell of `K`. -/
lemma exists_cell_of_mem_sliceHull {K : SComplex E} (H : ι → E →ᵃ[ℝ] ℝ) {c : CellIdx E ι}
    (hc : c.1 ∈ K) {z : E} (hz : z ∈ sliceHull H c) :
    ∃ c' : CellIdx E ι, c' ≤ c ∧ c'.1 ∈ K ∧ z ∈ cellSet (fun i => ⇑(H i)) c' := by
  obtain ⟨σ', hσ'K, hσ'σ, hzσ'⟩ := exists_face_openHull hc hz.1
  exact ⟨(σ', fun i => SignType.sign (H i z)), ⟨hσ'σ, hz.2⟩, hσ'K, hzσ', fun i => rfl⟩

variable [Fintype ι] [DecidableEq ι]

/-- **The cells of a slicing form a cell structure.** -/
noncomputable def sliceStructure (K : SComplex E) (hK : IsGeom K) (H : ι → E →ᵃ[ℝ] ℝ) :
    CellStructure E (CellIdx E ι) where
  cells := cells K (fun i => ⇑(H i))
  cell := cellSet (fun i => ⇑(H i))
  hull := sliceHull H
  pt c := Classical.epsilon fun x => x ∈ cellSet (fun i => ⇑(H i)) c
  pt_mem _ hc := Classical.epsilon_spec (p := fun x => x ∈ cellSet (fun i => ⇑(H i)) _)
    (mem_cells.1 hc).2
  nonempty _ hc := (mem_cells.1 hc).2
  convex_hull c _ := convex_sliceHull H c
  cell_subset_hull c _ := cellSet_subset_sliceHull H c
  hull_mono a _ b _ hba := sliceHull_mono H hba
  cell_inj a ha b hb x hxa hxb := by
    refine Prod.ext (hK.eq_of_mem_openHull (mem_cells.1 ha).1 (mem_cells.1 hb).1 hxa.1 hxb.1)
      (funext fun i => ?_)
    exact (hxa.2 i).symm.trans (hxb.2 i)
  combo_mem a ha p z hp hz l hl0 hl1 := by
    obtain ⟨c', hc', -, hzc'⟩ := exists_cell_of_mem_sliceHull H (mem_cells.1 ha).1 hz
    exact segment_mem_cell hc' hzc' hp hl0 hl1
  notMem_span a ha b hb hlt x hx hxs := by
    by_cases he : b.1 = a.1
    · obtain ⟨i, hi⟩ : ∃ i, b.2 i ≠ a.2 i := by
        by_contra hall
        push Not at hall
        exact hlt.ne (Prod.ext he (funext hall))
      have hb0 : b.2 i = 0 := (hlt.le.2 i).resolve_right hi
      have hzero : ∀ y ∈ sliceHull H b, H i y = 0 := by
        intro y hy
        rcases hy.2 i with h | h
        · exact sign_eq_zero_iff.1 h
        · rw [hb0] at h; exact sign_eq_zero_iff.1 h
      have himg : H i '' sliceHull H b ⊆ {0} := by
        rintro _ ⟨y, hy, rfl⟩; exact hzero y hy
      have hmem : H i x ∈ affineSpan ℝ ({0} : Set ℝ) := by
        have := AffineSubspace.map_span (H i) (sliceHull H b)
        have h2 : H i x ∈ (affineSpan ℝ (sliceHull H b)).map (H i) := ⟨x, hxs, rfl⟩
        rw [this] at h2
        exact affineSpan_mono ℝ himg h2
      rw [AffineSubspace.affineSpan_singleton] at hmem
      have hs0 : SignType.sign (H i x) = 0 := by
        have : H i x = 0 := by simpa using hmem
        rw [this]; simp
      rw [hx.2 i] at hs0
      exact hi (hb0.trans hs0.symm)
    · have hsp : affineSpan ℝ (sliceHull H b) ≤ affineSpan ℝ (b.1 : Set E) := by
        rw [← affineSpan_convexHull (b.1 : Set E)]
        exact affineSpan_mono ℝ fun y hy => hy.1
      exact notMem_affineSpan_of_mem_openHull (hK.indep _ (mem_cells.1 ha).1) hlt.le.1 he hx.1
        (hsp hxs)

/-- **Rays leave a cell through a smaller cell.** The ray from the chosen point of a cell through
another point of the cell meets a smaller cell of the slicing. -/
theorem sliceStructure_exit (K : SComplex E) (hK : IsGeom K) (H : ι → E →ᵃ[ℝ] ℝ) :
    ∀ c ∈ (sliceStructure K hK H).cells, ∀ x ∈ (sliceStructure K hK H).cell c,
      x ≠ (sliceStructure K hK H).pt c →
      ∃ t : ℝ, 1 ≤ t ∧ ∃ b ∈ (sliceStructure K hK H).cells, b < c ∧
        (sliceStructure K hK H).pt c + t • (x - (sliceStructure K hK H).pt c) ∈
          (sliceStructure K hK H).cell b := by
  intro c hc x hx hne
  have hp : (sliceStructure K hK H).pt c ∈ cellSet (fun i => ⇑(H i)) c :=
    (sliceStructure K hK H).pt_mem _ hc
  generalize (sliceStructure K hK H).pt c = p at hp hne ⊢
  have hcK := (mem_cells.1 hc).1
  obtain ⟨t₁, ht₁, hy₁, hn₁⟩ :=
    exists_exit (hK.indep c.1 hcK) hp.1 (openHull_subset_convexHull _ hx.1) hne
  have hyH : ∀ (i : ι) (t : ℝ), H i (p + t • (x - p)) = H i p + t * (H i x - H i p) := by
    intro i t
    have e : p + t • (x - p) = t • x + (1 - t) • p := by module
    rw [e, aff_combo]; ring
  classical
  let I := Finset.univ.filter fun i : ι => c.2 i ≠ 0
  let ε : ι → ℝ := fun i => ((c.2 i : SignType) : ℝ)
  have hε : ∀ i ∈ I, ε i ≠ 0 := fun i hi => by
    have := (mem_filter.1 hi).2
    intro h
    have h' : ((c.2 i : SignType) : ℝ) = 0 := h
    apply this
    generalize c.2 i = s at h' ⊢
    cases s <;> simp_all
  have ha : ∀ i ∈ I, 0 < ε i * H i p := fun i hi =>
    sign_mul_pos (hp.2 i) (mem_filter.1 hi).2
  have hab : ∀ i ∈ I, 0 < ε i * H i p + (ε i * H i x - ε i * H i p) := fun i hi => by
    have := sign_mul_pos (hx.2 i) (mem_filter.1 hi).2
    linarith
  obtain ⟨T, hT1, hTt, hTnn, hcase⟩ :=
    exists_exit_time I (fun i => ε i * H i p) (fun i => ε i * H i x - ε i * H i p) ha hab ht₁
  have hT0 : 0 < T := by linarith
  have hyhull : p + T • (x - p) ∈ sliceHull H c := by
    refine ⟨?_, fun i => ?_⟩
    · have hpc : p ∈ convexHull ℝ (c.1 : Set E) := openHull_subset_convexHull _ hp.1
      have hmem := (convex_convexHull ℝ (c.1 : Set E)).add_smul_sub_mem hpc hy₁
        (t := T / t₁) ⟨div_nonneg hT0.le (by linarith), (div_le_one (by linarith)).2 hTt⟩
      convert hmem using 2
      rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ (by linarith : t₁ ≠ 0)]
    · by_cases hci : c.2 i = 0
      · left
        have h1 : H i p = 0 := sign_eq_zero_iff.1 ((hp.2 i).trans hci)
        have h2 : H i x = 0 := sign_eq_zero_iff.1 ((hx.2 i).trans hci)
        rw [hyH, h1, h2]; simp
      · have hiI : i ∈ I := mem_filter.2 ⟨mem_univ _, hci⟩
        have := hTnn i hiI
        refine sign_of_mul_nonneg hci ?_
        rw [hyH]
        change 0 ≤ ε i * H i p + T * (ε i * H i x - ε i * H i p) at this
        change 0 ≤ ε i * (H i p + T * (H i x - H i p))
        linarith
  have hynot : p + T • (x - p) ∉ cellSet (fun i => ⇑(H i)) c := by
    intro hy
    rcases hcase with rfl | ⟨i, hiI, hz⟩
    · exact hn₁ hy.1
    · have h0 : H i (p + T • (x - p)) = 0 := by
        rw [hyH]
        have : ε i * (H i p + T * (H i x - H i p)) = 0 := by
          change ε i * H i p + T * (ε i * H i x - ε i * H i p) = 0 at hz
          linarith
        exact (mul_eq_zero.1 this).resolve_left (hε i hiI)
      have := hy.2 i
      change SignType.sign (H i (p + T • (x - p))) = c.2 i at this
      rw [h0] at this
      exact (mem_filter.1 hiI).2 (by simpa using this.symm)
  obtain ⟨c', hc'le, hc'K, hyc'⟩ := exists_cell_of_mem_sliceHull H hcK hyhull
  refine ⟨T, hT1, c', mem_cells.2 ⟨hc'K, ⟨_, hyc'⟩⟩, lt_of_le_of_ne hc'le ?_, hyc'⟩
  rintro rfl
  exact hynot hyc'

/-- **The chain complex of the cells of a slicing is geometric.** -/
theorem isGeom_slice_chainComplex (K : SComplex E) (hK : IsGeom K) (H : ι → E →ᵃ[ℝ] ℝ) :
    IsGeom (sliceStructure K hK H).chainComplex :=
  (sliceStructure K hK H).isGeom_chainComplex

/-- Every point of a cell of a slicing lies in a simplex of the chain complex, spanned by the
chosen points of a chain of cells below it. -/
theorem exists_chain_of_mem_sliceCell (K : SComplex E) (hK : IsGeom K) (H : ι → E →ᵃ[ℝ] ℝ)
    {c : CellIdx E ι} (hc : c ∈ cells K (fun i => ⇑(H i))) {x : E}
    (hx : x ∈ cellSet (fun i => ⇑(H i)) c) :
    ∃ C, (sliceStructure K hK H).IsCellChain C ∧ (∀ p ∈ C, p ≤ c) ∧
      x ∈ convexHull ℝ (↑(C.image (sliceStructure K hK H).pt) : Set E) := by
  obtain ⟨C, h1, h2, h3⟩ :=
    (sliceStructure K hK H).exists_chain_of_mem_cell (sliceStructure_exit K hK H) _ c hc rfl x hx
  exact ⟨C, h1, h2, by convert h3⟩

end SComplex

end Lightlike.PL
