import Lightlike.SpinFoam.Move15Global

/-!
# Chains of Pachner moves for the gauge-fixed Ooguri state sum

The gauge-fixed state sum at finite cutoff is invariant under each of the five 4D Pachner moves
(`amplitudeGF_move33_gauge`, `amplitudeGF_move24_gauge`, `amplitudeGF_move42_gauge`,
`Move15.amplitudeGF_move15_gauge`, `Move15.amplitudeGF_move51_gauge`). Each of those theorems has
cutoff conditions that make the cutoffs on the faces inside the move non-binding, and carries the
gauge set along. This file puts them into one relation, as the 3D file `Lightlike/PonzanoRegge/GaugeFixed.lean`
does for the 2-3 and 1-4 moves.

Limits: finite cutoff only. The cutoffs must be re-chosen by `recut` between moves, and the
cutoff conditions are sufficient, not necessary. Nothing here says that the state sum is
independent of the gauge set.

## Main results

* `GFStep4`: one step between triples `(complex, gauge set, cutoffs)`: a 3-3, 2-4 or 1-5 move with
  the hypotheses of the matching theorem, or a change of the cutoffs on faces that are not summed.
  The 4-2 and 5-1 moves are the steps read backwards.
* `GFStep4.isGauge`: a step takes a gauge set to a gauge set.
* `amplitudeGF_eqvGen4`: the gauge-fixed amplitude is constant along every chain of steps.
* `amplitudeGF_congr_cut`: the sum reads the cutoff only on the faces that are summed.
* `amplitudeGF_tendsto_one_of_forces`: for a gauge set that forces every triangle, the state sum
  at the constant cutoff `L` is `1` for every `L`, so it converges as the cutoff is removed.

## References

* `freidel-louapre-2003`, Section IV.B: gauge fixing by a maximal tree. The gauge rule `IsGauge` is
  this library's 4D analogue, not their construction.
-/

open Finset Lightlike.FourD Complex4

namespace Lightlike.SpinFoam

variable {V : Type*} [LinearOrder V]

/-- `amplitudeGF` reads the cutoff only on the summed faces. -/
theorem amplitudeGF_congr_cut (K : Complex4 V) (T : Finset (Finset V)) {cut cut' : Finset V → ℕ}
    (h : ∀ f ∈ colFaces K \ T, cut f = cut' f) : amplitudeGF K T cut = amplitudeGF K T cut' := by
  unfold amplitudeGF
  have : (colFaces K \ T).pi (fun f => range (cut f + 1)) =
      (colFaces K \ T).pi (fun f => range (cut' f + 1)) := by
    ext σ
    simp only [mem_pi]
    exact forall₂_congr fun f hf => by rw [h f hf]
  rw [this]

/-- One step between gauge-fixed, cut-off Ooguri state sums `(complex, gauge set, cutoffs)`: a 3-3,
2-4 or 1-5 move (the hypotheses are those of `amplitudeGF_move33_gauge`,
`amplitudeGF_move24_gauge` and `Move15.amplitudeGF_move15_gauge`; the gauge set is carried along),
or a change of the cutoffs on faces that are not summed. -/
inductive GFStep4 : Complex4 V × Finset (Finset V) × (Finset V → ℕ) →
    Complex4 V × Finset (Finset V) × (Finset V → ℕ) → Prop
  | move33 {K : Complex4 V} {σ τ : Finset V} (h : K.IsMove σ τ) (hσ : #σ = 3)
      {T : Finset (Finset V)} (hg : IsGauge K T) (hσT : σ ∉ T) {cut : Finset V → ℕ}
      (hAσ : ∀ b ∈ τ, ∑ f ∈ ((insert b σ).powersetCard 3).erase σ, cut f ≤ cut σ)
      (htσ : ∀ b ∈ τ,
        cut σ + ∑ f ∈ ((insert b σ).powersetCard 3).erase σ, cut f ≤ cut (insert b σ))
      (hAτ : ∀ a ∈ σ, ∑ f ∈ ((insert a τ).powersetCard 3).erase τ, cut f ≤ cut τ)
      (htτ : ∀ a ∈ σ,
        cut τ + ∑ f ∈ ((insert a τ).powersetCard 3).erase τ, cut f ≤ cut (insert a τ)) :
      GFStep4 (K, T, cut) (K.move h, T, cut)
  | move24 {K : Complex4 V} {σ τ : Finset V} (h : K.IsMove σ τ) (hσ : #σ = 4)
      {T : Finset (Finset V)} (hg : IsGauge K T) {cut : Finset V → ℕ}
      (hA : ∑ f ∈ σ.powersetCard 3, cut f ≤ cut σ)
      (hc3 : ∑ f ∈ outerTri σ τ, cut f ≤ cut (insert (σ.orderEmbOfFin hσ 3) τ))
      (hc2 : cut (insert (σ.orderEmbOfFin hσ 3) τ) + ∑ f ∈ outerTri σ τ, cut f ≤
        cut (insert (σ.orderEmbOfFin hσ 2) τ))
      (hc1 : cut (insert (σ.orderEmbOfFin hσ 3) τ) + ∑ f ∈ outerTri σ τ, cut f ≤
        cut (insert (σ.orderEmbOfFin hσ 1) τ))
      (hte : ∀ x ∈ σ, ∀ y ∈ σ, x ≠ y →
        cut (insert (σ.orderEmbOfFin hσ 1) τ) + cut (insert (σ.orderEmbOfFin hσ 2) τ) +
          cut (insert (σ.orderEmbOfFin hσ 3) τ) + ∑ f ∈ outerTri σ τ, cut f ≤
          cut (insert x (insert y τ))) :
      GFStep4 (K, T, cut) (K.move h, insert (insert (σ.orderEmbOfFin hσ 0) τ) T, cut)
  | move15 {K : Complex4 V} {σ τ : Finset V} (h : K.IsMove σ τ) (hσ : #σ = 5) {v : V}
      (hτ : τ = {v}) {T : Finset (Finset V)} (hg : IsGauge K T) {cut : Finset V → ℕ}
      (hcut : Move15.Cut15 cut (Move15.triV (σ.orderEmbOfFin hσ) v)
        (Move15.teV (σ.orderEmbOfFin hσ) v) (Move15.otV (σ.orderEmbOfFin hσ))) :
      GFStep4 (K, T, cut) (K.move h, Move15.gaugeTri (σ.orderEmbOfFin hσ) v ∪ T, cut)
  | recut {K : Complex4 V} {T : Finset (Finset V)} {cut cut' : Finset V → ℕ}
      (h : ∀ f ∈ colFaces K \ T, cut f = cut' f) : GFStep4 (K, T, cut) (K, T, cut')

/-- **A step takes a gauge set to a gauge set.** -/
theorem GFStep4.isGauge {x y : Complex4 V × Finset (Finset V) × (Finset V → ℕ)}
    (hs : GFStep4 x y) (hx : IsGauge x.1 x.2.1) : IsGauge y.1 y.2.1 := by
  cases hs with
  | move33 h hσ hg hσT hAσ htσ hAτ htτ =>
    exact (amplitudeGF_move33_gauge _ h hσ hg hσT _ hAσ htσ hAτ htτ).1
  | move24 h hσ hg hA hc3 hc2 hc1 hte =>
    exact (amplitudeGF_move24_gauge _ h hσ _ hg _ hA hc3 hc2 hc1 hte).1
  | move15 h hσ hτ hg hcut => exact (Move15.amplitudeGF_move15_gauge _ h hσ hτ _ hg _ hcut).1
  | recut _ => exact hx

/-- **The gauge-fixed Ooguri amplitude is constant along every chain of 3-3, 2-4, 4-2, 1-5 and 5-1
moves** (the equivalence closure of `GFStep4`). At finite cutoff; the cutoffs between two moves are
related by `recut`, which may change them on faces that are not summed only. -/
theorem amplitudeGF_eqvGen4 {x y : Complex4 V × Finset (Finset V) × (Finset V → ℕ)}
    (hxy : Relation.EqvGen GFStep4 x y) :
    amplitudeGF x.1 x.2.1 x.2.2 = amplitudeGF y.1 y.2.1 y.2.2 := by
  induction hxy with
  | rel x y hs =>
    cases hs with
    | move33 h hσ hg hσT hAσ htσ hAτ htτ =>
      exact (amplitudeGF_move33_gauge _ h hσ hg hσT _ hAσ htσ hAτ htτ).2.symm
    | move24 h hσ hg hA hc3 hc2 hc1 hte =>
      exact (amplitudeGF_move24_gauge _ h hσ _ hg _ hA hc3 hc2 hc1 hte).2.symm
    | move15 h hσ hτ hg hcut => exact (Move15.amplitudeGF_move15_gauge _ h hσ hτ _ hg _ hcut).2.symm
    | recut h => exact amplitudeGF_congr_cut _ _ h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A forcing gauge set makes the cutoff removable.** If `T` forces every triangle of `K`, the
state sum at the constant cutoff `L` is `1` for every `L` (`amplitudeGF_eq_one_of_forces`), so it
converges to `1` as the cutoff is removed. Only for gauge sets that force every triangle; no
statement for other gauge sets or for the state sum without gauge fixing. -/
theorem amplitudeGF_tendsto_one_of_forces {K : Complex4 V} {T : Finset (Finset V)}
    (h : Forces K K.tris T) :
    Filter.Tendsto (fun L : ℕ => amplitudeGF K T (fun _ => L)) Filter.atTop (nhds 1) := by
  have : (fun L : ℕ => amplitudeGF K T (fun _ => L)) = fun _ => 1 :=
    funext fun L => amplitudeGF_eq_one_of_forces h _
  rw [this]
  exact tendsto_const_nhds

end Lightlike.SpinFoam
