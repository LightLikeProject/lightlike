import Lightlike.SpinFoam.Vertex
import Lightlike.FourD.Pachner
import Lightlike.PonzanoRegge.GaugeFixed
import Lightlike.Recoupling.Span

/-!
# The Ooguri state sum

The 4-dimensional SU(2) BF model of Ooguri (*Mod. Phys. Lett. A* 7 (1992) 2799; Baez,
*Spin foam models*, *Class. Quantum Grav.* 15 (1998) 1827, §3) on a 4-complex `K`: a spin on every
triangle, an intertwiner (a virtual spin in the canonical basis) on every tetrahedron, the vertex
amplitude `vertexAmp` (a 15j symbol) for every 4-simplex, and the dimension `2j + 1` of every
triangle. In doubled units the weight of a colouring `col` is

`weight K col = Π_{f triangle} (col f + 1) · Π_{s 4-simplex} vertexAmp s col`.

The tetrahedra carry no weight because the canonical intertwiners are orthonormal
(`Lightlike.Recoupling.sum_fourJ_mul_fourJ`). The vertex amplitude does not depend on an orientation
(`vertexContr_neg`), so neither does the state sum: it is defined on every `Complex4`.

A closed 4-manifold gives a divergent sum, as in three dimensions (Ponzano–Regge). As there
(`Lightlike.PR.amplitudeGF`) the state sum is regularised by a **cutoff** on every colourable face
(triangles and tetrahedra) and a **gauge set** `T` of faces whose colour is fixed to `0`:

* `amplitudeGF K T cut`: the sum over the colours `≤ cut f` of the faces `f ∉ T`, with colour `0`
  on `T`;
* `amplitude K L`: no gauge set, spins `≤ L/2` on the triangles and virtual spins `≤ L` on the
  tetrahedra (the range of the virtual spin of four spins `≤ L/2`).

## Main results

* `simpW_congr`, `weight_congr`: the amplitude of a 4-simplex depends only on the colours of its
  own triangles and tetrahedra.
* `amplitude_zero`: with cutoff `0` the state sum is `1` on every complex.
* `ampP_tet_zero`, `weight_tet_zero`: **forcing**. In a colouring of nonzero weight, a
  tetrahedron with three triangles of spin `0` has its fourth triangle and its virtual spin at `0`.
  `Forces` iterates this, and `amplitudeGF_eq_one_of_forces` gives state sum `1` for every cutoff
  when the gauge set forces every triangle.
* `amplitudeGF_eq_of_vanish`: enlarging the gauge set by faces on which every colouring of nonzero
  weight already vanishes leaves the state sum unchanged.
* `IsGauge`: **the gauge rule**. `T` is a set of triangles such that the vertices, the edges and
  `T` form a collapsible 2-complex (`Collapsible`). `IsGauge.card_eq`: `#T = E − V + 1`.
  `IsGauge.move33`: the rule survives a 3-3 move that does not remove a triangle of `T`; the
  gauge-fixed invariance is `amplitudeGF_move33_gauge` (`Move33.lean`).

The gauge rule is this library's proposal for the 4-dimensional analogue of the maximal tree. Its
size `E − V + 1` is the second Betti number of the dual 2-complex of a triangulated 4-sphere,
which Bonzom and Smerlak identify as the degree of divergence; on a closed orientable 4-manifold
`M` that Betti number is `E − V + 1 + b₂(M) − b₃(M)`. On the boundary of the 5-simplex a set of
ten triangles is collapsible together with the edges exactly when it forces all triangles (all
184756 sets checked numerically), and the state sum is then `1` for every cutoff.

## References

- H. Ooguri, *Topological lattice models in four dimensions*, Mod. Phys. Lett. A 7, 2799 (1992),
  arXiv:hep-th/9205090: the state sum.
- J. C. Baez, *Spin foam models*, Class. Quantum Grav. 15, 1827 (1998), arXiv:gr-qc/9709052:
  spin foams, 2-complexes with faces labelled by representations and edges by intertwining
  operators.
- J. C. Baez, *An introduction to spin foam models of BF theory and quantum gravity*,
  Lect. Notes Phys. 543, 25 (2000), arXiv:gr-qc/9905087: spin foam models of BF theory.
- L. Freidel, D. Louapre, *Diffeomorphisms and spin foam models*, Nucl. Phys. B 662, 279 (2003),
  arXiv:gr-qc/0212001: the gauge fixing of the divergences, worked out for the Ponzano–Regge
  model, with a maximal tree of fixed spins.
- V. Bonzom, M. Smerlak, *Bubble divergences from cellular cohomology*, Lett. Math. Phys. 93, 295
  (2010), arXiv:1004.5196: the divergence degree of the BF spin foam models from the cellular
  cohomology of the 2-complex.
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam

variable {V : Type*} [LinearOrder V]

/-- The amplitude of a vertex set: `vertexAmp` for a 4-simplex, `0` (junk) otherwise. -/
noncomputable def simpW (col : Finset V → ℕ) (s : Finset V) : ℝ :=
  if h : #s = 5 then vertexAmp s h col else 0

/-- **The Ooguri weight** of a coloured 4-complex:
`Π_{triangles} (col f + 1) · Π_{4-simplices} vertexAmp s col` (doubled units). -/
noncomputable def weight (K : Complex4 V) (col : Finset V → ℕ) : ℝ :=
  (∏ f ∈ K.tris, ((col f : ℝ) + 1)) * ∏ s ∈ K.simps, simpW col s

/-- The faces that carry a colour: triangles (spins) and tetrahedra (virtual spins). -/
def colFaces (K : Complex4 V) : Finset (Finset V) := K.tris ∪ K.tets

/-- **The Ooguri state sum** with face-wise cutoffs and a gauge set: the sum of `weight` over the
colourings with colour `≤ cut f` on every colourable face `f ∉ T` and colour `0` on `T`. -/
noncomputable def amplitudeGF (K : Complex4 V) (T : Finset (Finset V)) (cut : Finset V → ℕ) : ℝ :=
  ∑ c ∈ (colFaces K \ T).pi (fun f => range (cut f + 1)), weight K (Lightlike.PR.extS (colFaces K \ T) c)

/-- **The Ooguri state sum** with spins `≤ L/2` on the triangles and virtual spins `≤ L` on the
tetrahedra (doubled units), without gauge fixing. -/
noncomputable def amplitude (K : Complex4 V) (L : ℕ) : ℝ :=
  amplitudeGF K ∅ (fun f => if #f = 4 then 2 * L else L)

/-! ## Locality -/

/-- The vertex amplitude depends only on the colours of the triangles and tetrahedra of `s`. -/
theorem simpW_congr {col col' : Finset V → ℕ} {s : Finset V}
    (h : ∀ f ⊆ s, (#f = 3 ∨ #f = 4) → col f = col' f) : simpW col s = simpW col' s := by
  unfold simpW
  split_ifs with hs
  · unfold vertexAmp
    congr 1
    · funext p q
      apply h _ ((erase_subset _ _).trans (erase_subset _ _))
      by_cases hpq : p = q
      · subst hpq
        right
        rw [erase_eq_of_notMem (notMem_erase _ _), card_erase_of_mem (s.orderEmbOfFin_mem hs p),
          hs]
      · left
        have hne : s.orderEmbOfFin hs q ≠ s.orderEmbOfFin hs p :=
          fun he => hpq ((s.orderEmbOfFin hs).injective he).symm
        rw [card_erase_of_mem (mem_erase.mpr ⟨hne, s.orderEmbOfFin_mem hs q⟩),
          card_erase_of_mem (s.orderEmbOfFin_mem hs p), hs]
    · funext i
      apply h _ (erase_subset _ _)
      right
      rw [card_erase_of_mem (s.orderEmbOfFin_mem hs i), hs]
  · rfl

/-- The weight depends only on the colours of the triangles and tetrahedra of `K`. -/
theorem weight_congr (K : Complex4 V) {col col' : Finset V → ℕ}
    (h : ∀ f ∈ colFaces K, col f = col' f) : weight K col = weight K col' := by
  unfold weight
  congr 1
  · refine prod_congr rfl fun f hf => ?_
    rw [h f (mem_union_left _ hf)]
  · refine prod_congr rfl fun s hs => simpW_congr fun f hfs hf => h f ?_
    rcases hf with hf | hf
    · exact mem_union_left _ (Complex4.mem_faces.mpr ⟨s, hs, hfs, hf⟩)
    · exact mem_union_right _ (Complex4.mem_faces.mpr ⟨s, hs, hfs, hf⟩)

/-- The zero colouring has weight `1` on every complex: every vertex amplitude is `1`
(`vertexAmp_zero`). -/
theorem weight_zero (K : Complex4 V) : weight K (fun _ => 0) = 1 := by
  unfold weight simpW
  simp only [Nat.cast_zero, zero_add, prod_const_one, one_mul]
  refine prod_eq_one fun s hs => ?_
  rw [dite_eq_left (K.card_eq s hs)]
  simp [vertexAmp, ampP, Lightlike.Recoupling.fifteenJSimplex_zero]

/-- **Value check.** With cutoff `0` every colour is `0`, every vertex amplitude is `1`
(`vertexAmp_zero`), and the state sum is `1`, on every complex. -/
theorem amplitude_zero (K : Complex4 V) : amplitude K 0 = 1 := by
  unfold amplitude amplitudeGF
  rw [sdiff_empty]
  simp only [mul_zero, ite_self, zero_add, range_one]
  have hpi : (colFaces K).pi (fun _ => ({0} : Finset ℕ)) = {fun _ _ => 0} := by
    ext c
    simp only [mem_pi, mem_singleton]
    constructor
    · intro hc; funext f hf; exact hc f hf
    · rintro rfl f _; rfl
  rw [hpi, sum_singleton]
  have h0 : Lightlike.PR.extS (colFaces K) (fun _ _ => 0) = fun _ => 0 := by
    funext f; simp [Lightlike.PR.extS]
  rw [h0, weight_zero]

/-! ## Forcing

At a tetrahedron of a 4-simplex with nonzero amplitude, three triangles of spin `0` force the
fourth triangle and the virtual spin to `0`: the two triads `(x, y, k)`, `(k, z, w)` of the
intertwiner leave no room for anything else. -/

section Forcing

open Lightlike.Recoupling Lightlike.Pentagon

/-- **Support of the vertex amplitude.** A nonzero vertex amplitude has admissible triads at all
five intertwiners, listed by the position of the tetrahedron (`0, 2, 4, 1, 3`, the pentagram order
of `fifteenJSimplex`). -/
theorem tri_of_ampP_ne_zero {J : Fin 5 → Fin 5 → ℕ} {K : Fin 5 → ℕ} (h : ampP J K ≠ 0) :
    (Tri (J 0 2) (J 0 4) (K 0) ∧ Tri (K 0) (J 0 1) (J 0 3)) ∧
    (Tri (J 2 4) (J 1 2) (K 2) ∧ Tri (K 2) (J 2 3) (J 0 2)) ∧
    (Tri (J 1 4) (J 3 4) (K 4) ∧ Tri (K 4) (J 0 4) (J 2 4)) ∧
    (Tri (J 1 3) (J 0 1) (K 1) ∧ Tri (K 1) (J 1 2) (J 1 4)) ∧
    (Tri (J 0 3) (J 2 3) (K 3) ∧ Tri (K 3) (J 3 4) (J 1 3)) := by
  have h15 : fifteenJSimplex (J 0 2) (J 0 4) (J 0 1) (J 0 3) (J 2 4) (J 1 2) (J 2 3) (J 1 4)
      (J 3 4) (J 1 3) (K 0) (K 2) (K 4) (K 1) (K 3) ≠ 0 :=
    fun h0 => h (by unfold ampP; rw [h0, mul_zero])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> by_contra hn <;> apply h15 <;> unfold fifteenJSimplex <;>
    simp only [fourJ_eq_zero_of_not_adm hn, zero_mul, mul_zero, sum_const_zero]

/-- Two admissible triads `(x, y, k)` and `(k, z, w)` in which at most one of `x, y, z, w` is
nonzero have all five spins `0`. -/
lemma tri_tri_eq_zero {x y z w k : ℕ} (h₁ : Tri x y k) (h₂ : Tri k z w)
    (hxy : x = 0 ∨ y = 0) (hxz : x = 0 ∨ z = 0) (hxw : x = 0 ∨ w = 0) (hyz : y = 0 ∨ z = 0)
    (hyw : y = 0 ∨ w = 0) (hzw : z = 0 ∨ w = 0) : x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 ∧ k = 0 := by
  obtain ⟨-, h₁⟩ := h₁
  obtain ⟨-, h₂⟩ := h₂
  omega

/-- **Forcing at one tetrahedron.** If the vertex amplitude is nonzero, the spins are symmetric,
and at most one triangle of the tetrahedron at position `i` (the spins `J i q`, `q ≠ i`) is
nonzero, then all four triangles of that tetrahedron and its virtual spin `K i` are `0`. -/
theorem ampP_tet_zero {J : Fin 5 → Fin 5 → ℕ} {K : Fin 5 → ℕ} (h : ampP J K ≠ 0)
    (hJ : ∀ p q, J p q = J q p) (i : Fin 5)
    (hz : ∀ q r, q ≠ i → r ≠ i → q ≠ r → J i q = 0 ∨ J i r = 0) :
    (∀ q, q ≠ i → J i q = 0) ∧ K i = 0 := by
  obtain ⟨⟨a0, b0⟩, ⟨a2, b2⟩, ⟨a4, b4⟩, ⟨a1, b1⟩, ⟨a3, b3⟩⟩ := tri_of_ampP_ne_zero h
  fin_cases i
  · obtain ⟨h2, h4, h1, h3, hk⟩ := tri_tri_eq_zero a0 b0 (hz 2 4 (by decide) (by decide) (by decide))
      (hz 2 1 (by decide) (by decide) (by decide)) (hz 2 3 (by decide) (by decide) (by decide))
      (hz 4 1 (by decide) (by decide) (by decide)) (hz 4 3 (by decide) (by decide) (by decide))
      (hz 1 3 (by decide) (by decide) (by decide))
    refine ⟨fun q hq => ?_, hk⟩
    fin_cases q <;> first | exact (hq rfl).elim | assumption
  · rw [hJ 0 1] at a1
    obtain ⟨h3, h0, h2, h4, hk⟩ := tri_tri_eq_zero a1 b1 (hz 3 0 (by decide) (by decide) (by decide))
      (hz 3 2 (by decide) (by decide) (by decide)) (hz 3 4 (by decide) (by decide) (by decide))
      (hz 0 2 (by decide) (by decide) (by decide)) (hz 0 4 (by decide) (by decide) (by decide))
      (hz 2 4 (by decide) (by decide) (by decide))
    refine ⟨fun q hq => ?_, hk⟩
    fin_cases q <;> first | exact (hq rfl).elim | assumption
  · rw [hJ 1 2] at a2
    rw [hJ 0 2] at b2
    obtain ⟨h4, h1, h3, h0, hk⟩ := tri_tri_eq_zero a2 b2 (hz 4 1 (by decide) (by decide) (by decide))
      (hz 4 3 (by decide) (by decide) (by decide)) (hz 4 0 (by decide) (by decide) (by decide))
      (hz 1 3 (by decide) (by decide) (by decide)) (hz 1 0 (by decide) (by decide) (by decide))
      (hz 3 0 (by decide) (by decide) (by decide))
    refine ⟨fun q hq => ?_, hk⟩
    fin_cases q <;> first | exact (hq rfl).elim | assumption
  · rw [hJ 0 3, hJ 2 3] at a3
    rw [hJ 1 3] at b3
    obtain ⟨h0, h2, h4, h1, hk⟩ := tri_tri_eq_zero a3 b3 (hz 0 2 (by decide) (by decide) (by decide))
      (hz 0 4 (by decide) (by decide) (by decide)) (hz 0 1 (by decide) (by decide) (by decide))
      (hz 2 4 (by decide) (by decide) (by decide)) (hz 2 1 (by decide) (by decide) (by decide))
      (hz 4 1 (by decide) (by decide) (by decide))
    refine ⟨fun q hq => ?_, hk⟩
    fin_cases q <;> first | exact (hq rfl).elim | assumption
  · rw [hJ 1 4, hJ 3 4] at a4
    rw [hJ 0 4, hJ 2 4] at b4
    obtain ⟨h1, h3, h0, h2, hk⟩ := tri_tri_eq_zero a4 b4 (hz 1 3 (by decide) (by decide) (by decide))
      (hz 1 0 (by decide) (by decide) (by decide)) (hz 1 2 (by decide) (by decide) (by decide))
      (hz 3 0 (by decide) (by decide) (by decide)) (hz 3 2 (by decide) (by decide) (by decide))
      (hz 0 2 (by decide) (by decide) (by decide))
    refine ⟨fun q hq => ?_, hk⟩
    fin_cases q <;> first | exact (hq rfl).elim | assumption

end Forcing


/-- A subset `f ⊆ t` with one element fewer is `t` with one element erased. -/
lemma exists_eq_erase {f t : Finset V} (hft : f ⊆ t) (h : #f + 1 = #t) :
    ∃ w ∈ t, f = t.erase w := by
  obtain ⟨w, hw, rfl⟩ := exists_eq_insert_iff.mpr ⟨hft, h⟩
  exact ⟨w, mem_insert_self w f, (erase_insert hw).symm⟩

/-- **Forcing at a tetrahedron of a 4-simplex.** If the amplitude of the 4-simplex `s` is nonzero
and every triangle of a tetrahedron `t ⊆ s` other than `f` has colour `0`, then `f` and `t` have
colour `0` too. -/
theorem simpW_tet_zero {col : Finset V → ℕ} {s t f : Finset V} (hW : simpW col s ≠ 0)
    (hts : t ⊆ s) (ht : #t = 4) (hft : f ⊆ t) (hf : #f = 3)
    (h0 : ∀ g ⊆ t, #g = 3 → g ≠ f → col g = 0) : col f = 0 ∧ col t = 0 := by
  unfold simpW at hW
  split_ifs at hW with hs
  · set e := s.orderEmbOfFin hs
    have hrange : ∀ v ∈ s, ∃ i, e i = v := fun v hv => by
      have : v ∈ Set.range e := by rw [range_orderEmbOfFin]; exact hv
      exact this
    obtain ⟨v, hv, rfl⟩ := exists_eq_erase hts (by rw [ht, hs])
    obtain ⟨i, rfl⟩ := hrange v hv
    obtain ⟨w, hw, rfl⟩ := exists_eq_erase hft (by rw [hf, ht])
    obtain ⟨q, rfl⟩ := hrange w (mem_of_mem_erase hw)
    have hqi : q ≠ i := fun hqi => by rw [hqi] at hw; exact notMem_erase _ _ hw
    have hmem : ∀ r, r ≠ i → e r ∈ s.erase (e i) := fun r hr =>
      mem_erase.mpr ⟨fun he => hr (e.injective he), s.orderEmbOfFin_mem hs r⟩
    have hcard : ∀ r, r ≠ i → #((s.erase (e i)).erase (e r)) = 3 := fun r hr => by
      rw [card_erase_of_mem (hmem r hr), ht]
    have hne : ∀ r, r ≠ i → r ≠ q →
        (s.erase (e i)).erase (e r) ≠ (s.erase (e i)).erase (e q) := fun r hr hrq he => by
      have : e r ∉ (s.erase (e i)).erase (e q) := by rw [← he]; exact notMem_erase _ _
      exact hrq (e.injective (by
        by_contra hc; exact this (mem_erase.mpr ⟨hc, hmem r hr⟩)))
    have := ampP_tet_zero hW (fun p r => by simp only [erase_right_comm]) i
      fun r r' hr hr' hrr' => by
        by_cases hrq : r = q
        · subst hrq
          exact Or.inr (h0 _ (erase_subset _ _) (hcard r' hr') (hne r' hr' (Ne.symm hrr')))
        · exact Or.inl (h0 _ (erase_subset _ _) (hcard r hr) (hne r hr hrq))
    exact ⟨this.1 q hqi, this.2⟩
  · exact absurd rfl hW

/-- A colouring of nonzero weight has a nonzero amplitude at every 4-simplex. -/
lemma simpW_ne_zero_of_weight {K : Complex4 V} {col : Finset V → ℕ} (h : weight K col ≠ 0)
    {s : Finset V} (hs : s ∈ K.simps) : simpW col s ≠ 0 :=
  prod_ne_zero_iff.mp (right_ne_zero_of_mul h) s hs

/-- **Forcing at a tetrahedron of a complex.** For a colouring of nonzero weight, if every triangle
of a tetrahedron `t` of `K` other than `f` has colour `0`, then `f` and `t` have colour `0`. -/
theorem weight_tet_zero {K : Complex4 V} {col : Finset V → ℕ} (hW : weight K col ≠ 0)
    {t f : Finset V} (ht : t ∈ K.tets) (hf : f ∈ t.powersetCard 3)
    (h0 : ∀ g ∈ t.powersetCard 3, g ≠ f → col g = 0) : col f = 0 ∧ col t = 0 := by
  obtain ⟨s, hs, hts, ht4⟩ := Complex4.mem_faces.mp ht
  rw [mem_powersetCard] at hf
  exact simpW_tet_zero (simpW_ne_zero_of_weight hW hs) hts ht4 hf.1 hf.2
    fun g hg hg3 hgf => h0 g (mem_powersetCard.mpr ⟨hg, hg3⟩) hgf

/-- For a colouring of nonzero weight, a tetrahedron of `K` whose four triangles have colour `0`
has virtual spin `0`. -/
theorem weight_tet_zero_of_tris {K : Complex4 V} {col : Finset V → ℕ} (hW : weight K col ≠ 0)
    {t : Finset V} (ht : t ∈ K.tets) (h0 : ∀ g ∈ t.powersetCard 3, col g = 0) : col t = 0 := by
  obtain ⟨f, hf⟩ : (t.powersetCard 3).Nonempty :=
    powersetCard_nonempty.mpr (by rw [Complex4.card_of_mem_faces ht]; omega)
  exact (weight_tet_zero hW ht hf fun g hg _ => h0 g hg).2

/-- **Forcing.** `Forces K U T`: starting from the faces of `T`, repeatedly adding the fourth
triangle of a tetrahedron of `K` whose other three triangles are already in the set reaches every
face of `U`. Every colouring of nonzero weight that vanishes on `T` then vanishes on `U`
(`Forces.sound`). It is the 4-dimensional analogue of `Lightlike.PR.ForcesAll`. -/
inductive Forces (K : Complex4 V) (U : Finset (Finset V)) : Finset (Finset V) → Prop
  /-- Every face of `U` is already in the set. -/
  | done {T : Finset (Finset V)} (h : U ⊆ T) : Forces K U T
  /-- The tetrahedron `t` forces its triangle `f`. -/
  | step {T : Finset (Finset V)} (t f : Finset V) (ht : t ∈ K.tets) (hf : f ∈ t.powersetCard 3)
      (hT : ∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ T) (h : Forces K U (insert f T)) : Forces K U T

/-- **Soundness of forcing.** A colouring of nonzero weight that vanishes on `T` vanishes on every
face that `T` forces. -/
theorem Forces.sound {K : Complex4 V} {U T : Finset (Finset V)} (h : Forces K U T)
    {col : Finset V → ℕ} (hW : weight K col ≠ 0) : (∀ f ∈ T, col f = 0) → ∀ f ∈ U, col f = 0 := by
  induction h with
  | done h => exact fun hT f hf => hT f (h hf)
  | step t f ht hf hT' _ ih =>
    intro hT
    have hf0 := (weight_tet_zero hW ht hf fun g hg hgf => hT g (hT' g hg hgf)).1
    exact ih fun g hg => by
      rcases mem_insert.mp hg with rfl | hg
      · exact hf0
      · exact hT g hg

/-- A list of forcing steps `(t, f)`, checked one after the other: a decision procedure whose
success proves `Forces` (`forces_of_forcesBy`). -/
def forcesBy (K : Complex4 V) (U : Finset (Finset V)) :
    List (Finset V × Finset V) → Finset (Finset V) → Bool
  | [], T => decide (U ⊆ T)
  | (t, f) :: l, T => decide (t ∈ K.tets ∧ f ∈ t.powersetCard 3 ∧
      ∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ T) && forcesBy K U l (insert f T)

/-- A successful `forcesBy` check proves `Forces`. -/
theorem forces_of_forcesBy {K : Complex4 V} {U : Finset (Finset V)}
    {l : List (Finset V × Finset V)} {T : Finset (Finset V)} (h : forcesBy K U l T = true) :
    Forces K U T := by
  induction l generalizing T with
  | nil => exact .done (of_decide_eq_true h)
  | cons p l ih =>
    obtain ⟨t, f⟩ := p
    simp only [forcesBy, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .step t f h.1.1 h.1.2.1 h.1.2.2 (ih h.2)

/-! ## Changing the gauge set -/

/-- The colourings summed in `amplitudeGF K T cut`, as functions on all faces: colour `≤ cut f` on
the colourable faces outside `T`, `0` elsewhere. -/
lemma mem_image_extS [DecidableEq (Finset V → ℕ)] {S : Finset (Finset V)} {cut : Finset V → ℕ}
    {col : Finset V → ℕ} :
    col ∈ (S.pi fun f => range (cut f + 1)).image (Lightlike.PR.extS S) ↔
      (∀ f ∈ S, col f ≤ cut f) ∧ ∀ f ∉ S, col f = 0 := by
  rw [mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun f hf => ?_, fun f hf => Lightlike.PR.extS_of_not_mem hf⟩
    have := mem_range.mp (mem_pi.mp hc f hf)
    unfold Lightlike.PR.extS
    rw [dite_eq_left hf]
    exact Nat.le_of_lt_succ this
  · rintro ⟨h1, h2⟩
    refine ⟨fun f _ => col f, mem_pi.mpr fun f hf => mem_range.mpr (Nat.lt_succ_of_le (h1 f hf)),
      funext fun f => ?_⟩
    unfold Lightlike.PR.extS
    by_cases hf : f ∈ S
    · rw [dite_eq_left hf]
    · rw [dite_eq_right hf, h2 f hf]

/-- `amplitudeGF` as a sum over colourings of all faces. -/
lemma amplitudeGF_eq_sum_image [DecidableEq (Finset V → ℕ)] (K : Complex4 V)
    (T : Finset (Finset V)) (cut : Finset V → ℕ) :
    amplitudeGF K T cut = ∑ col ∈ ((colFaces K \ T).pi fun f => range (cut f + 1)).image
      (Lightlike.PR.extS (colFaces K \ T)), weight K col := by
  unfold amplitudeGF
  rw [sum_image]
  intro c _ c' _ he
  funext f hf
  have := congrFun he f
  unfold Lightlike.PR.extS at this
  rwa [dite_eq_left hf, dite_eq_left hf] at this

/-- **Changing the gauge set.** If every colouring of nonzero weight that vanishes on `T` also
vanishes on `T' ⊇ T`, then fixing `T'` instead of `T` leaves the state sum unchanged, for all
cutoffs. -/
theorem amplitudeGF_eq_of_vanish (K : Complex4 V) {T T' : Finset (Finset V)} (hTT' : T ⊆ T')
    (h : ∀ col, weight K col ≠ 0 → (∀ f ∈ T, col f = 0) → ∀ f ∈ T', col f = 0)
    (cut : Finset V → ℕ) : amplitudeGF K T' cut = amplitudeGF K T cut := by
  classical
  rw [amplitudeGF_eq_sum_image, amplitudeGF_eq_sum_image]
  have hsub : colFaces K \ T' ⊆ colFaces K \ T := sdiff_subset_sdiff subset_rfl hTT'
  apply sum_subset
  · intro col hcol
    rw [mem_image_extS] at hcol ⊢
    refine ⟨fun f hf => ?_, fun f hf => hcol.2 f fun hf' => hf (hsub hf')⟩
    by_cases hf' : f ∈ colFaces K \ T'
    · exact hcol.1 f hf'
    · rw [hcol.2 f hf']; omega
  · intro col hcol hcol'
    by_contra hw
    apply hcol'
    rw [mem_image_extS] at hcol ⊢
    have hT : ∀ f ∈ T, col f = 0 := fun f hf => hcol.2 f fun h' => (mem_sdiff.mp h').2 hf
    refine ⟨fun f hf => hcol.1 f (hsub hf), fun f hf => ?_⟩
    by_cases hc : f ∈ colFaces K
    · exact h col hw hT f (by by_contra h'; exact hf (mem_sdiff.mpr ⟨hc, h'⟩))
    · exact hcol.2 f fun h' => hc (mem_sdiff.mp h').1

/-- With every colourable face fixed, the state sum is the weight `1` of the zero colouring. -/
theorem amplitudeGF_union_colFaces (K : Complex4 V) (T : Finset (Finset V))
    (cut : Finset V → ℕ) : amplitudeGF K (T ∪ colFaces K) cut = 1 := by
  classical
  rw [amplitudeGF_eq_sum_image, sdiff_eq_empty_iff_subset.mpr subset_union_right]
  have : ((∅ : Finset (Finset V)).pi fun f => range (cut f + 1)).image (Lightlike.PR.extS ∅) =
      {fun _ => 0} := by
    ext col
    rw [mem_image_extS, mem_singleton]
    constructor
    · rintro ⟨-, h⟩; funext f; exact h f (notMem_empty f)
    · rintro rfl; exact ⟨fun f hf => absurd hf (notMem_empty f), fun _ _ => rfl⟩
  rw [this, sum_singleton, weight_zero]

/-- **A forcing gauge set gives `1`.** If the gauge set `T` forces every triangle of `K`, only the
zero colouring has nonzero weight, and the state sum is `1` for all cutoffs. -/
theorem amplitudeGF_eq_one_of_forces {K : Complex4 V} {T : Finset (Finset V)}
    (h : Forces K K.tris T) (cut : Finset V → ℕ) : amplitudeGF K T cut = 1 := by
  rw [← amplitudeGF_eq_of_vanish K subset_union_left _ cut, amplitudeGF_union_colFaces]
  intro col hW hT f hf
  rcases mem_union.mp hf with hf | hf
  · exact hT f hf
  have htri := h.sound hW hT
  rcases mem_union.mp hf with hf | hf
  · exact htri f hf
  · refine weight_tet_zero_of_tris hW hf fun g hg => htri g ?_
    obtain ⟨s, hs, hts, -⟩ := Complex4.mem_faces.mp hf
    rw [mem_powersetCard] at hg
    exact Complex4.mem_faces.mpr ⟨s, hs, hg.1.trans hts, hg.2⟩

/-! ## The gauge rule

The 4-dimensional analogue of Freidel–Louapre's maximal tree: a set `T` of triangles, fixed at spin
`0`, such that the vertices, the edges and the triangles of `T` form a collapsible 2-complex. A
maximal tree in three dimensions is exactly a set of edges that together with the vertices
collapses to a point. -/

/-- **Collapsible** sets of faces: `X` reduces to a single vertex `{v}` by elementary collapses,
each removing a free face `σ` together with the unique face `τ ⊋ σ` of `X` that contains it, one
dimension higher. -/
inductive Collapsible : Finset (Finset V) → Prop
  /-- A single vertex. -/
  | point (v : V) : Collapsible {{v}}
  /-- An elementary collapse of the free face `σ ⊂ τ`. -/
  | collapse {X : Finset (Finset V)} (σ τ : Finset V) (hσ : σ ∈ X) (hτ : τ ∈ X) (hστ : σ ⊆ τ)
      (hcard : #τ = #σ + 1) (hfree : ∀ ρ ∈ X, σ ⊆ ρ → ρ = σ ∨ ρ = τ)
      (h : Collapsible ((X.erase τ).erase σ)) : Collapsible X

/-- A list of elementary collapses `(σ, τ)` ending at the vertex `v`, checked one after the other:
a decision procedure whose success proves `Collapsible` (`collapsible_of_collapsesBy`). -/
def collapsesBy (v : V) : List (Finset V × Finset V) → Finset (Finset V) → Bool
  | [], X => decide (X = {{v}})
  | (σ, τ) :: l, X => decide (σ ∈ X ∧ τ ∈ X ∧ σ ⊆ τ ∧ #τ = #σ + 1 ∧
      ∀ ρ ∈ X, σ ⊆ ρ → ρ = σ ∨ ρ = τ) && collapsesBy v l ((X.erase τ).erase σ)

/-- A successful `collapsesBy` check proves `Collapsible`. -/
theorem collapsible_of_collapsesBy {v : V} {l : List (Finset V × Finset V)}
    {X : Finset (Finset V)} (h : collapsesBy v l X = true) : Collapsible X := by
  induction l generalizing X with
  | nil => rw [of_decide_eq_true h]; exact .point v
  | cons p l ih =>
    obtain ⟨σ, τ⟩ := p
    simp only [collapsesBy, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .collapse σ τ h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2 (ih h.2)

/-- The Euler characteristic of a set of faces: `Σ_f (-1)^dim f`. -/
def eulerChar (X : Finset (Finset V)) : ℤ := ∑ f ∈ X, (-1) ^ (#f + 1)

/-- An elementary collapse removes two faces of adjacent dimensions, so a collapsible set has Euler
characteristic `1`. -/
theorem Collapsible.euler_eq {X : Finset (Finset V)} (h : Collapsible X) : eulerChar X = 1 := by
  induction h with
  | point v => simp [eulerChar]
  | collapse σ τ hσ hτ _ hcard _ _ ih =>
    have hne : σ ≠ τ := fun he => by rw [he] at hcard; omega
    unfold eulerChar at ih ⊢
    rw [← add_sum_erase _ _ hτ, ← add_sum_erase _ _ (mem_erase.mpr ⟨hne, hσ⟩), ih, hcard,
      pow_succ]
    ring

/-- The faces of the gauge rule: the vertices and edges of `K` and the triangles of `T`. -/
def gaugeCx (K : Complex4 V) (T : Finset (Finset V)) : Finset (Finset V) :=
  K.faces 0 ∪ K.faces 1 ∪ T

/-- **The gauge rule**, the 4-dimensional analogue of Freidel–Louapre's maximal tree: `T` is a set
of triangles of `K` such that the vertices, the edges and the triangles of `T` form a collapsible
2-complex. -/
def IsGauge (K : Complex4 V) (T : Finset (Finset V)) : Prop :=
  T ⊆ K.tris ∧ Collapsible (gaugeCx K T)

/-- **Size of a gauge set**: `#T = #edges − #vertices + 1`, from the Euler characteristic of the
collapsible complex `gaugeCx K T`. -/
theorem IsGauge.card_eq {K : Complex4 V} {T : Finset (Finset V)} (h : IsGauge K T) :
    (#T : ℤ) = #K.edges - #K.verts + 1 := by
  have he := h.2.euler_eq
  have c0 : ∀ f ∈ K.faces 0, #f = 1 := fun f hf => Complex4.card_of_mem_faces hf
  have c1 : ∀ f ∈ K.faces 1, #f = 2 := fun f hf => Complex4.card_of_mem_faces hf
  have c2 : ∀ f ∈ T, #f = 3 := fun f hf => Complex4.card_of_mem_faces (h.1 hf)
  have d01 : Disjoint (K.faces 0) (K.faces 1) :=
    disjoint_left.mpr fun f h0 h1 => by have := c0 f h0; have := c1 f h1; omega
  have d2 : Disjoint (K.faces 0 ∪ K.faces 1) T :=
    disjoint_left.mpr fun f h01 h2 => by
      have := c2 f h2
      rcases mem_union.mp h01 with h0 | h1
      · have := c0 f h0; omega
      · have := c1 f h1; omega
  have s0 : ∑ f ∈ K.faces 0, (-1 : ℤ) ^ (#f + 1) = #(K.faces 0) := by
    rw [sum_congr rfl (g := fun _ => (1 : ℤ)) fun f hf => by rw [c0 f hf]; norm_num]; simp
  have s1 : ∑ f ∈ K.faces 1, (-1 : ℤ) ^ (#f + 1) = -#(K.faces 1) := by
    rw [sum_congr rfl (g := fun _ => (-1 : ℤ)) fun f hf => by rw [c1 f hf]; norm_num]; simp
  have s2 : ∑ f ∈ T, (-1 : ℤ) ^ (#f + 1) = #T := by
    rw [sum_congr rfl (g := fun _ => (1 : ℤ)) fun f hf => by rw [c2 f hf]; norm_num]; simp
  unfold eulerChar gaugeCx at he
  rw [sum_union d2, sum_union d01, s0, s1, s2] at he
  rw [← Complex4.card_faces_zero]
  linarith

/-! ### The gauge rule under the 3-3 move -/

/-- A face of `K` is a nonempty face of a 4-simplex of the right size. -/
lemma mem_faces_iff_allFaces {K : Complex4 V} {k : ℕ} {f : Finset V} :
    f ∈ K.faces k ↔ f ∈ K.allFaces ∧ #f = k + 1 := by
  rw [Complex4.mem_faces, Complex4.mem_allFaces]
  constructor
  · rintro ⟨s, hs, hfs, hf⟩
    exact ⟨⟨card_pos.mp (by omega), s, hs, hfs⟩, hf⟩
  · rintro ⟨⟨-, s, hs, hfs⟩, hf⟩
    exact ⟨s, hs, hfs, hf⟩

/-- A face of `K` that does not contain `σ` survives the move `σ → τ`. -/
lemma mem_faces_move {K : Complex4 V} {σ τ : Finset V} (h : K.IsMove σ τ) {k : ℕ}
    {f : Finset V} (hf : f ∈ K.faces k) (hσ : ¬σ ⊆ f) : f ∈ (K.move h).faces k := by
  rw [mem_faces_iff_allFaces] at hf ⊢
  have : f ∈ (K.move h).allFaces.filter (¬τ ⊆ ·) := by
    rw [Complex4.filter_allFaces_move]; exact mem_filter.mpr ⟨hf.1, hσ⟩
  exact ⟨(mem_filter.mp this).1, hf.2⟩

/-- A face of the moved complex that does not contain `τ` is a face of `K`. -/
lemma mem_faces_of_mem_move {K : Complex4 V} {σ τ : Finset V} (h : K.IsMove σ τ) {k : ℕ}
    {f : Finset V} (hf : f ∈ (K.move h).faces k) (hτ : ¬τ ⊆ f) : f ∈ K.faces k := by
  rw [mem_faces_iff_allFaces] at hf ⊢
  have : f ∈ (K.move h).allFaces.filter (¬τ ⊆ ·) := mem_filter.mpr ⟨hf.1, hτ⟩
  rw [Complex4.filter_allFaces_move] at this
  exact ⟨(mem_filter.mp this).1, hf.2⟩

/-- A move `σ → τ` does not change the faces with fewer vertices than `σ` and `τ`. -/
lemma faces_move_of_lt {K : Complex4 V} {σ τ : Finset V} (h : K.IsMove σ τ) {k : ℕ}
    (hσ : k + 1 < #σ) (hτ : k + 1 < #τ) : (K.move h).faces k = K.faces k := by
  ext f
  constructor
  · intro hf
    exact mem_faces_of_mem_move h hf fun hs => by
      have := card_le_card hs; rw [Complex4.card_of_mem_faces hf] at this; omega
  · intro hf
    exact mem_faces_move h hf fun hs => by
      have := card_le_card hs; rw [Complex4.card_of_mem_faces hf] at this; omega

/-- **The gauge rule survives the 3-3 move.** A 3-3 move leaves the vertices and edges unchanged,
so a gauge set of `K` that does not contain the triangle `σ` removed by the move is a gauge set of
the new complex. -/
theorem IsGauge.move33 {K : Complex4 V} {σ τ : Finset V} (h : K.IsMove σ τ) (hσ : #σ = 3)
    {T : Finset (Finset V)} (hg : IsGauge K T) (hσT : σ ∉ T) : IsGauge (K.move h) T := by
  have hτ : #τ = 3 := by have := h.card; omega
  refine ⟨fun f hf => mem_faces_move h (hg.1 hf) fun hs => hσT ?_, ?_⟩
  · rwa [eq_of_subset_of_card_le hs (by rw [Complex4.card_of_mem_faces (hg.1 hf), hσ])]
  · unfold gaugeCx
    rw [faces_move_of_lt h (by omega) (by omega), faces_move_of_lt h (by omega) (by omega)]
    exact hg.2

end Lightlike.SpinFoam
