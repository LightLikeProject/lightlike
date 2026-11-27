import Lightlike.SpinFoam.EPRLStateSum.BoneCollapse

/-!
# The Ooguri weight of the bone colouring of every edge of `∂Δ⁵`

The bone colouring of the edge `{u, w}` of `∂Δ⁵` has doubled spin `1` on the four triangles through the edge and the virtual
spin `boneLf` on the tetrahedra. Seen from one 4-simplex that contains the edge, at the positions `a < b` of `u`, `w` among the
five sorted vertices, it is the colouring `patJ a b`, `patK a b`: spin `½` on the three triangles among the other three positions
and the virtual spin `patK` on the tetrahedra through the edge. The vertex amplitude `ampP` of these ten patterns is `±1/√2`, with
the sign `-1` exactly when `b - a ≥ 3` (`ampP_pat`).
-/

open Finset Lightlike.FourD Lightlike.FourD.Tests Lightlike.SpinFoam Lightlike.Recoupling PhyslibAlpha.Sl2

namespace Lightlike.SpinFoam.EPRLStateSum.Trust

/-- The virtual spin of the bone colouring on the tetrahedron opposite the position `c`, when the edge sits at the positions
`a < b` of a 4-simplex: `1` if `c ∉ {a, b}` and the number of positions strictly between `a` and `b`, other than `c`, is not `1`. -/
def patK (a b : Fin 5) (c : Fin 5) : ℕ :=
  if c ≠ a ∧ c ≠ b ∧ (if a < c ∧ c < b then (b : ℕ) - a - 2 else (b : ℕ) - a - 1) ≠ 1 then 1 else 0

/-- Spin `½` on the triangles among the three positions other than `a, b` (off the diagonal), the virtual spin `patK` on the
diagonal (as `simplexJ`). -/
def patJ (a b : Fin 5) (p q : Fin 5) : ℕ :=
  if p = q then patK a b p else if p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b then 1 else 0

/-- **The intertwiner `(½, 0, 0, ½; ½)`** with zero projections on its spin-`0` legs. -/
lemma fourJ_h00h (m m' : ℤ) :
    fourJ 1 0 0 1 1 m 0 0 m' =
      if m = 1 ∧ m' = -1 then -1 / Real.sqrt 2 else if m = -1 ∧ m' = 1 then 1 / Real.sqrt 2
      else 0 := by
  unfold fourJ
  have hI : Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  have hc1 : ∀ μ : ℤ, threeJ 1 0 1 m 0 μ = threeJ 0 1 1 0 μ m :=
    fun μ => (threeJ_cycle 1 1 0 μ m 0).trans (threeJ_cycle 0 1 1 0 μ m)
  have hc : ∀ μ : ℤ, threeJ 1 0 1 (-μ) 0 m' = threeJ 0 1 1 0 m' (-μ) :=
    fun μ => (threeJ_cycle 1 1 0 m' (-μ) 0).trans (threeJ_cycle 0 1 1 0 m' (-μ))
  simp only [hI, hc1, hc, Recoupling.Tests.threeJ_0hh_table,
    sum_insert (show (-1 : ℤ) ∉ ({0, 1} : Finset ℤ) by decide),
    sum_insert (show (0 : ℤ) ∉ ({1} : Finset ℤ) by decide), sum_singleton]
  norm_num
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  split_ifs <;> first | omega | (simp only [mul_zero, add_zero, zero_add]; done) |
    (field_simp; done) | (field_simp; nlinarith [h2])

lemma icc_one : Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide

lemma sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

set_option linter.unusedSimpArgs false in
/-- The evaluation of `ampP` on a bone pattern: unfold `ampP` and the 15j symbol, replace the intertwiners by their tables. -/
local macro "pat_eval" : tactic => `(tactic| (
  unfold ampP
  simp [patJ, patK]
  unfold fifteenJSimplex
  simp only [Nat.cast_zero, neg_zero, Icc_self, sum_singleton, fourJ_zero, neg_zero]
  simp only [Recoupling.Tests.fourJ_hh00, Recoupling.Tests.fourJ_00hh, fourJ_h00h, fourJ_h0h0, fourJ_0h0h,
    Recoupling.Tests.fourJ_0hh0, Recoupling.Tests.threeJ_0hh_table, edgeSign]
  simp only [icc_one, sum_insert (show (-1 : ℤ) ∉ ({0, 1} : Finset ℤ) by decide),
    sum_insert (show (0 : ℤ) ∉ ({1} : Finset ℤ) by decide), sum_singleton]
  norm_num
  field_simp
  nlinarith [sqrt2_mul_self]))

theorem ampP_pat_01 : ampP (patJ 0 1) (patK 0 1) = 1 / Real.sqrt 2 := by pat_eval
theorem ampP_pat_02 : ampP (patJ 0 2) (patK 0 2) = 1 / Real.sqrt 2 := by pat_eval
theorem ampP_pat_03 : ampP (patJ 0 3) (patK 0 3) = -1 / Real.sqrt 2 := by pat_eval
theorem ampP_pat_04 : ampP (patJ 0 4) (patK 0 4) = -1 / Real.sqrt 2 := by pat_eval
theorem ampP_pat_12 : ampP (patJ 1 2) (patK 1 2) = 1 / Real.sqrt 2 := by pat_eval
theorem ampP_pat_13 : ampP (patJ 1 3) (patK 1 3) = 1 / Real.sqrt 2 := by pat_eval
theorem ampP_pat_14 : ampP (patJ 1 4) (patK 1 4) = -1 / Real.sqrt 2 := by pat_eval
theorem ampP_pat_23 : ampP (patJ 2 3) (patK 2 3) = 1 / Real.sqrt 2 := by pat_eval
theorem ampP_pat_24 : ampP (patJ 2 4) (patK 2 4) = 1 / Real.sqrt 2 := by pat_eval
theorem ampP_pat_34 : ampP (patJ 3 4) (patK 3 4) = 1 / Real.sqrt 2 := by pat_eval


lemma pat_cases : ∀ a b : Fin 5, a < b →
    (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 3) ∨
      (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 3) ∨ (a = 2 ∧ b = 4) ∨ (a = 3 ∧ b = 4) := by
  decide +kernel

/-- **The vertex amplitude of the ten position patterns**: `±1/√2`, with the sign `-1` exactly when `b - a ≥ 3`. -/
theorem ampP_pat (a b : Fin 5) (hab : a < b) :
    ampP (patJ a b) (patK a b) = (if 3 ≤ (b : ℕ) - a then -1 else 1) / Real.sqrt 2 := by
  rcases pat_cases a b hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [ampP_pat_01]; norm_num
  · rw [ampP_pat_02]; norm_num
  · rw [ampP_pat_03]; norm_num
  · rw [ampP_pat_04]; norm_num
  · rw [ampP_pat_12]; norm_num
  · rw [ampP_pat_13]; norm_num
  · rw [ampP_pat_14]; norm_num
  · rw [ampP_pat_23]; norm_num
  · rw [ampP_pat_24]; norm_num
  · rw [ampP_pat_34]; norm_num

/-- The bone colouring of an edge is `patJ`, `patK` seen from the simplex `univ.erase p` at the positions `a < b` of the edge. -/
lemma boneFull_tri : ∀ (p : Fin 6) (a b : Fin 5), a < b → ∀ i j : Fin 5,
    boneFull (p.succAbove a) (p.succAbove b) (((univ.erase p).erase (p.succAbove i)).erase (p.succAbove j)) = patJ a b i j := by
  unfold boneFull boneB boneLf patJ patK; decide +kernel

lemma boneFull_tet : ∀ (p : Fin 6) (a b : Fin 5), a < b → ∀ i : Fin 5,
    boneFull (p.succAbove a) (p.succAbove b) ((univ.erase p).erase (p.succAbove i)) = patK a b i := by
  unfold boneFull boneB boneLf patK; decide +kernel

/-- The vertex amplitude of the simplex `univ.erase p` at the bone colouring of the edge at the positions `a < b`. -/
lemma simpW_bone_succAbove (p : Fin 6) (a b : Fin 5) (hab : a < b) :
    simpW (boneFull (p.succAbove a) (p.succAbove b)) (univ.erase p) = ampP (patJ a b) (patK a b) := by
  have hc : #(univ.erase p : Finset (Fin 6)) = 5 := by decide +revert
  unfold simpW
  rw [dite_eq_left hc, vertexAmp_eq_ampP]
  congr 1
  · funext i j
    unfold simplexJ
    rw [orderEmbOfFin_erase p hc, orderEmbOfFin_erase p hc, boneFull_tri p a b hab]
  · funext i
    rw [orderEmbOfFin_erase p hc, boneFull_tet p a b hab]

/-- A set not containing the edge has colour `0` in the bone colouring. -/
lemma boneFull_zero_of_not_sub {u w : Fin 6} {f : Finset (Fin 6)} (h : ¬ ({u, w} : Finset (Fin 6)) ⊆ f) :
    boneFull u w f = 0 := by
  unfold boneFull boneB boneLf
  split_ifs <;> simp_all

/-- A simplex that does not contain the edge carries the zero colouring: its vertex amplitude is `1`. -/
lemma simpW_bone_of_not_sub {u w : Fin 6} {s : Finset (Fin 6)} (hs : #s = 5) (h : ¬ ({u, w} : Finset (Fin 6)) ⊆ s) :
    simpW (boneFull u w) s = 1 := by
  have hz : ∀ f ⊆ s, boneFull u w f = 0 := fun f hf => boneFull_zero_of_not_sub fun h' => h (h'.trans hf)
  unfold simpW
  rw [dite_eq_left hs, vertexAmp_eq_ampP]
  have e1 : simplexJ s hs (boneFull u w) = fun _ _ => 0 := by
    funext p q
    exact hz _ ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
  have e2 : (fun i => boneFull u w (s.erase (s.orderEmbOfFin hs i))) = fun _ => 0 := by
    funext i
    exact hz _ (Finset.erase_subset _ _)
  rw [e1, e2]
  exact Lightlike.SpinFoam.ampP_zero


/-- The number of positions strictly between the edge `{u, w}` (`u < w`) in the simplex `univ.erase p`, plus one: `b - a`. -/
def gapB (u w p : Fin 6) : ℕ := (w.val - (if p < w then 1 else 0)) - (u.val - (if p < u then 1 else 0))

lemma succAbove_gap : ∀ (p : Fin 6) (a b : Fin 5), a < b → (b : ℕ) - a = gapB (p.succAbove a) (p.succAbove b) p := by
  unfold gapB; decide +kernel

/-- The sign `±1` of the vertex amplitude of the simplex `univ.erase p` at the bone colouring of `{u, w}`. -/
def sgnB (u w p : Fin 6) : ℤ := if p = u ∨ p = w then 1 else if 3 ≤ gapB u w p then -1 else 1

/-- **The vertex amplitude of every simplex at the bone colouring of every edge**: `sgnB / √2` for a simplex through the
edge, `1` for the two others. -/
theorem simpW_bone (u w p : Fin 6) (huw : u < w) :
    simpW (boneFull u w) (univ.erase p) =
      (sgnB u w p : ℝ) * (if p = u ∨ p = w then 1 else 1 / Real.sqrt 2) := by
  by_cases hp : p = u ∨ p = w
  · have hs : #(univ.erase p : Finset (Fin 6)) = 5 := by decide +revert
    have hn : ¬ ({u, w} : Finset (Fin 6)) ⊆ univ.erase p := by
      rcases hp with rfl | rfl <;> simp [Finset.insert_subset_iff]
    rw [simpW_bone_of_not_sub hs hn]
    simp [sgnB, hp]
  · rw [not_or] at hp
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq (x := u) (y := p) (Ne.symm hp.1)
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq (x := w) (y := p) (Ne.symm hp.2)
    subst ha hb
    have hab : a < b := (Fin.strictMono_succAbove p).lt_iff_lt.1 huw
    rw [simpW_bone_succAbove p a b hab, ampP_pat a b hab, succAbove_gap p a b hab]
    have hne : ¬ (p = p.succAbove a ∨ p = p.succAbove b) := by
      rw [not_or]; exact ⟨Ne.symm (Fin.succAbove_ne p a), Ne.symm (Fin.succAbove_ne p b)⟩
    simp only [sgnB, hne, ite_false]
    split_ifs <;> simp <;> ring

lemma tris_bone_card : ∀ u w : Fin 6, u < w →
    (sphere6.tris.filter (fun f => boneFull u w f = 1)).card = 4 := by
  unfold boneFull boneB boneLf; decide +kernel

/-- `2⁴` from the four triangles through the edge. -/
lemma prod_tris_bone (u w : Fin 6) (huw : u < w) : (∏ f ∈ sphere6.tris, ((boneFull u w f : ℝ) + 1)) = 16 := by
  have h01 : ∀ f ∈ sphere6.tris, boneFull u w f = 0 ∨ boneFull u w f = 1 := fun f hf => by
    unfold boneFull boneB boneLf; split_ifs <;> simp
  have h : ∀ f ∈ sphere6.tris, ((boneFull u w f : ℝ) + 1) = if boneFull u w f = 1 then 2 else 1 := by
    intro f hf
    rcases h01 f hf with h | h <;> simp [h]
    norm_num
  rw [Finset.prod_congr rfl h, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    tris_bone_card u w huw]
  norm_num

lemma simps_sphere6_eq : sphere6.simps = (univ : Finset (Fin 6)).image (fun p => univ.erase p) := by
  decide +kernel

lemma sgnB_prod : ∀ u w : Fin 6, u < w → ∏ p : Fin 6, sgnB u w p = 1 := by
  unfold sgnB gapB; decide +kernel

lemma card_off_edge : ∀ u w : Fin 6, u < w → (univ.filter fun p : Fin 6 => ¬ (p = u ∨ p = w)).card = 4 := by
  decide +kernel

/-- **The Ooguri weight of the bone colouring of every edge of `∂Δ⁵` is `4`**: `2⁴` from the four triangles through the edge,
`(1/√2)⁴` from the four vertices through it, and the signs `sgnB` of the four vertices multiply to `1`. -/
theorem weight_bone (u w : Fin 6) (huw : u < w) : weight sphere6 (boneFull u w) = 4 := by
  unfold weight
  rw [prod_tris_bone u w huw, simps_sphere6_eq, Finset.prod_image (fun p _ q _ h => erase_univ_inj p q h)]
  simp only [simpW_bone u w _ huw]
  rw [Finset.prod_mul_distrib, ← Int.cast_prod, sgnB_prod u w huw, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const]
  have hc : (univ.filter fun p : Fin 6 => ¬ (p = u ∨ p = w)).card = 4 := card_off_edge u w huw
  rw [hc]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h4 : (1 / Real.sqrt 2) ^ 4 = 1 / 4 := by
    have : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
    calc (1 / Real.sqrt 2) ^ 4 = ((1 / Real.sqrt 2) ^ 2) ^ 2 := by ring
      _ = 1 / 4 := by rw [this]; norm_num
  simp only [Int.cast_one, one_mul]
  rw [h4]
  norm_num


/-- **The EPRL state sum at `γ = 1` on `∂Δ⁵` with the bone cutoff of any edge `{u, w}` is `5`**: the zero colouring (weight
`1`) and the bone colouring (weight `4`), both with the sign `1` of the link orientations. For `{0, 1}` this is
`amplitudeI_sphere6_low_spin`. -/
theorem amplitudeI_sphere6_bone (u w : Fin 6) (huw : u < w) : amplitudeI 1 sphere6 (boneB u w) = 5 := by
  obtain ⟨e, he⟩ := exists_complex_incidence sphere6 sphere6_checks.2.2
  rw [amplitudeI_one_eq_signedSum sphere6 (boneB u w) e he,
    signedSum_bone u w huw e he (Lightlike.SpinFoam.weight sphere6)
      (fun col col' h => weight_congr sphere6 h)]
  rw [weight_zero, weight_bone u w huw]
  norm_num

/-- Relabelling the vertices by `σ` maps the bone cutoff of `{0, 1}` to the bone cutoff of `{σ 0, σ 1}`. -/
lemma boneB_relabel (σ : Equiv.Perm (Fin 6)) (f : Finset (Fin 6)) :
    boneB 0 1 (f.map σ.symm.toEmbedding) = boneB (σ 0) (σ 1) f := by
  have h : ({0, 1} : Finset (Fin 6)) ⊆ f.map σ.symm.toEmbedding ↔ ({σ 0, σ 1} : Finset (Fin 6)) ⊆ f := by
    have e : ({0, 1} : Finset (Fin 6)) = ({σ 0, σ 1} : Finset (Fin 6)).map σ.symm.toEmbedding := by
      simp [Finset.map_insert]
    rw [e, Finset.map_subset_map]
  unfold boneB
  rw [Finset.card_map]
  simp only [h]

/-- **The EPRL state sum at `γ = 1` on `∂Δ⁵` is the same for every reordering of the vertices (the trust check)**: the bone
cutoff of `{0, 1}` with the vertices relabelled by any permutation `σ` gives `5`, the value of the unrelabelled cutoff; the library's
earlier sign twist gave `5` or `-3`. -/
theorem amplitudeI_sphere6_relabel (σ : Equiv.Perm (Fin 6)) :
    amplitudeI 1 sphere6 (fun f => boneB 0 1 (f.map σ.symm.toEmbedding)) = 5 := by
  have h : (fun f : Finset (Fin 6) => boneB 0 1 (f.map σ.symm.toEmbedding)) = boneB (σ 0) (σ 1) := by
    funext f; exact boneB_relabel σ f
  rw [h]
  have hne : σ 0 ≠ σ 1 := fun h => by simpa using σ.injective h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact amplitudeI_sphere6_bone _ _ hlt
  · have hc : boneB (σ 0) (σ 1) = boneB (σ 1) (σ 0) := by
      funext f; unfold boneB; rw [Finset.pair_comm]
    rw [hc]
    exact amplitudeI_sphere6_bone _ _ hgt

end Lightlike.SpinFoam.EPRLStateSum.Trust
