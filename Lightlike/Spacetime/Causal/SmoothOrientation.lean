import Lightlike.Spacetime.Causal.ConeConvex
import Lightlike.Spacetime.Causal.TimeOrientation

/-!
# A continuous time orientation can be replaced by a smooth one

The time orientation of a Lorentzian manifold is given as a continuous timelike vector field. Around
every point the field that is constant in a trivialization of the tangent bundle and equals `X`
at the point is smooth and future timelike (for `g` and `X`) on a neighbourhood. A smooth partition
of unity glues these local fields: at each point the result is a finite convex combination of
vectors of the future timelike cone, which is convex (`IsLorentzianForm.convex_futureTimelike`), so
it is future timelike (`exists_smooth_field`). The manifold is Hausdorff, second countable and
modelled on a finite-dimensional space.

## References

* R. M. Wald, *General Relativity*, University of Chicago Press (1984), Section 8.1 (time
  orientation).
* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Section 6.2.

The comparison with the sources at a location is pending.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n}

/-- The metric evaluated on two continuous sections of the tangent bundle is continuous. -/
lemma continuousAt_metric_apply {s t : ∀ q : M, TangentSpace I q} {q₀ : M}
    (hs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 0 (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q (s q)) q₀)
    (ht : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 0 (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q (t q)) q₀) :
    ContinuousAt (fun q ↦ g.g q (s q) (t q)) q₀ := by
  have hg : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) q (g.g q)) q₀ :=
    (g.contMDiff q₀).of_le (by norm_num)
  have := ContMDiffAt.clm_bundle_apply₂ (E₃ := Bundle.Trivial M ℝ) (F₃ := ℝ) (b := id) hg hs ht
  simp only [contMDiffAt_totalSpace] at this
  exact this.2.continuousAt

variable (I M) in
/-- The trivialization of the tangent bundle around `p` (the one of the chart at `p`). -/
abbrev tTriv (p : M) : Trivialization E (Bundle.TotalSpace.proj : Bundle.TotalSpace E (fun x : M ↦ TangentSpace I x) → M) :=
  trivializationAt E (fun x : M ↦ TangentSpace I x) p

/-- The vector field that is constant `ξ` in the trivialization of the tangent bundle around `p`
(defined everywhere, meaningful on its base set). -/
def localField (p : M) (ξ : E) (q : M) : TangentSpace I q := (tTriv I M p).symm q ξ

/-- The constant coordinates of `localField`. -/
lemma localField_coord (p : M) (ξ : E) {q : M} (hq : q ∈ (tTriv I M p).baseSet) :
    (tTriv I M p ⟨q, localField (I := I) p ξ q⟩).2 = ξ := by
  have := (tTriv I M p).apply_mk_symm hq ξ
  exact congrArg Prod.snd this

/-- `localField` is smooth on the base set of its trivialization. -/
lemma localField_contMDiffOn (p : M) (ξ : E) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q (localField (I := I) p ξ q))
      (tTriv I M p).baseSet := by
  rw [Trivialization.contMDiffOn_section_iff (tTriv I M p) (tTriv I M p).open_baseSet subset_rfl]
  exact contMDiffOn_const.congr fun q hq ↦ localField_coord p ξ hq

section Cover

variable (T : TimeOrientation g)

/-- The future timelike cone at `q` for the orientation `T`: `g(v, v) < 0` and `g(v, X) < 0`. -/
def futureCone (q : M) : Set (TangentSpace I q) := {v | g.g q v v < 0 ∧ g.g q v (T.X q) < 0}

/-- The chart-constant extension of the vector `X p` of the time orientation. -/
def fieldAt (p : M) : ∀ q : M, TangentSpace I q :=
  localField (I := I) p ((tTriv I M p ⟨p, T.X p⟩).2)

/-- The chart-constant extension of `X p` takes the value `X p` at `p`. -/
lemma fieldAt_self (p : M) : fieldAt T p p = T.X p := by
  have hp : p ∈ (tTriv I M p).baseSet := mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p
  exact (tTriv I M p).symm_apply_apply_mk hp (T.X p)

/-- The open set where the chart-constant field `fieldAt T p` is future timelike. -/
def coverSet (p : M) : Set M :=
  {q | q ∈ (tTriv I M p).baseSet ∧ fieldAt T p q ∈ futureCone T q}

/-- The sets `coverSet T p` are open. -/
lemma isOpen_coverSet (p : M) : IsOpen (coverSet T p) := by
  rw [isOpen_iff_mem_nhds]
  rintro q₀ ⟨hq₀, h1, h2⟩
  have hb : (tTriv I M p).baseSet ∈ 𝓝 q₀ := (tTriv I M p).open_baseSet.mem_nhds hq₀
  have hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 0
      (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q (fieldAt T p q)) q₀ :=
    ((localField_contMDiffOn (I := I) p _).contMDiffAt hb).of_le (by norm_num)
  have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 0
      (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q (T.X q)) q₀ := T.contMDiff q₀
  have c1 := continuousAt_metric_apply (g := g) hY hY
  have c2 := continuousAt_metric_apply (g := g) hY hX
  filter_upwards [hb, c1.eventually (gt_mem_nhds h1), c2.eventually (gt_mem_nhds h2)] with q hq e1 e2
  exact ⟨hq, e1, e2⟩

/-- `p` lies in `coverSet T p`. -/
lemma mem_coverSet_self (p : M) : p ∈ coverSet T p := by
  have hp : p ∈ (tTriv I M p).baseSet := mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p
  refine ⟨hp, ?_⟩
  rw [fieldAt_self]
  exact ⟨T.timelike p, T.timelike p⟩

/-- The coordinates of `fieldAt T p` in the trivialization around `x₀` are the constant
coordinates of `X p` in the trivialization around `p`, transported by the coordinate change. -/
lemma fieldAt_coord (p q : M) (hq : q ∈ (tTriv I M p).baseSet) (x₀ : M)
    (hq' : q ∈ (tTriv I M x₀).baseSet) :
    ((tTriv I M x₀) ⟨q, fieldAt T p q⟩).2 =
      (tTriv I M p).coordChangeL ℝ (tTriv I M x₀) q ((tTriv I M p ⟨p, T.X p⟩).2) := by
  rw [Trivialization.coordChangeL_apply _ _ ⟨hq, hq'⟩]
  rfl

end Cover

/-- **A continuous time orientation can be replaced by a smooth one**: there is a smooth vector
field `X'` that is future-directed timelike for `T` at every point (`g(X', X') < 0` and
`g(X', X) < 0`). The field is a locally finite convex combination, by a smooth partition of unity,
of chart-constant fields that are timelike future around their base points; the future timelike cone
of a Lorentzian form is convex (`IsLorentzianForm.convex_futureTimelike`). -/
theorem exists_smooth_field [T2Space M] [SecondCountableTopology M] [FiniteDimensional ℝ E]
    (T : TimeOrientation g) :
    ∃ X' : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) x (X' x)) ∧
      ∀ x, g.g x (X' x) (X' x) < 0 ∧ g.g x (X' x) (T.X x) < 0 := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate I (isClosed_univ (X := M))
    (coverSet T) (isOpen_coverSet T) (fun p _ ↦ mem_iUnion.2 ⟨p, mem_coverSet_self T p⟩)
  have hsub : ∀ i q, f i q ≠ 0 → q ∈ coverSet T i := fun i q hq =>
    hf i (subset_tsupport _ (Function.mem_support.2 hq))
  refine ⟨fun q ↦ ∑ᶠ i, f i q • fieldAt T i q, ?_, ?_⟩
  · intro x₀
    rw [contMDiffAt_section]
    have hb₀ : x₀ ∈ (tTriv I M x₀).baseSet :=
      mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) x₀
    have hRHS : ContMDiffAt I 𝓘(ℝ, E) ∞
        (fun q ↦ ∑ᶠ i, f i q • ((tTriv I M x₀) ⟨q, fieldAt T i q⟩).2) x₀ := by
      refine f.contMDiffAt_finsum (g := fun i q ↦ ((tTriv I M x₀) ⟨q, fieldAt T i q⟩).2)
        (fun i hi ↦ ?_)
      have hbi : x₀ ∈ (tTriv I M i).baseSet := (hf i hi).1
      have hopen : IsOpen ((tTriv I M i).baseSet ∩ (tTriv I M x₀).baseSet) :=
        (tTriv I M i).open_baseSet.inter (tTriv I M x₀).open_baseSet
      have hcc := (contMDiffOn_coordChangeL (IB := I) (n := ∞) (tTriv I M i) (tTriv I M x₀)).clm_apply
        (contMDiffOn_const (c := (tTriv I M i ⟨i, T.X i⟩).2))
      refine (hcc.contMDiffAt (hopen.mem_nhds ⟨hbi, hb₀⟩)).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds ⟨hbi, hb₀⟩] with q hq
      exact fieldAt_coord T i q hq.1 x₀ hq.2
    refine hRHS.congr_of_eventuallyEq ?_
    filter_upwards [(tTriv I M x₀).open_baseSet.mem_nhds hb₀] with q hq
    have key : ∀ v : TangentSpace I q, ((tTriv I M x₀) ⟨q, v⟩).2 =
        (tTriv I M x₀).continuousLinearEquivAt ℝ q hq v := fun v ↦
      (congrFun ((tTriv I M x₀).continuousLinearEquivAt_apply ℝ q hq) v).symm
    have hfin : (Function.support fun i ↦ f i q • fieldAt T i q).Finite :=
      (f.locallyFinite.point_finite q).subset fun i hi ↦
        Function.mem_support.2 fun h0 ↦ hi (by simp [h0])
    simp only [key]
    rw [map_finsum ((tTriv I M x₀).continuousLinearEquivAt ℝ q hq) hfin]
    simp
  · intro q
    have hmem := ((g.lorentzian q).convex_futureTimelike (T.timelike q)).finsum_mem
      (w := fun i ↦ f i q) (z := fun i ↦ fieldAt T i q) (fun i ↦ f.nonneg i q)
      (f.sum_eq_one (mem_univ q)) (fun i hi ↦ (hsub i q hi).2)
    exact hmem

end Lightlike.Causal
