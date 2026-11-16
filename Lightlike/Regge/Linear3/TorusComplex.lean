import Lightlike.Regge.Conv3.KuhnCore
import Lightlike.Regge.Complex
import Lightlike.Regge.Linear3.AngleSmooth
import Lightlike.Regge.Linear3.SecondOrder

/-!
# The periodic Kuhn complex of the grid `(ℤ/n)³`

The six Kuhn tetrahedra of every cube of the grid `(ℤ/n)³` (`n ≥ 3`) form a closed 3-complex
`torusComplex n`, a triangulated 3-torus. With the base lengths `len0` (the Euclidean length
`√(number of differing coordinates)` of a pair of neighbouring vertices) every tetrahedron is an
orthoscheme congruent to the Kuhn simplex `0, e₁, e₁ + e₂, e₁ + e₂ + e₃`. This file proves that the
complex is a valid instance of the hypotheses of `regge_second_order`:

* it is closed (`bdryTris_torus`): every triangle lies in two tetrahedra, the neighbour being found
  by a finite table (`neighbour`);
* the base lengths are non-degenerate (`lengthsNondeg_len0`);
* it is flat (`deficit_len0`): the dihedral angle of a tetrahedron at a hinge is the angle `hang h` of
  the orthoscheme (`dihedralAt_hinge`), and the angles at an edge `{z, z + w}` are the 36 pairs
  (tetrahedron, hinge) of the Kuhn star sorted by the direction `w`, which add up to `2π`
  (`angleSum_class`, from `Lightlike.Regge.Conv3.star_angle_sum`).

The tetrahedra of distinct (cube, permutation) pairs are distinct (`tetV_injective`), so the star of
an edge is counted correctly (`star_sum`).

## Main results

* `torusComplex`: the periodic Kuhn complex, `len0`: its base lengths.
* `bdryTris_torus`, `lengthsNondeg_len0`, `deficit_len0`: closed, non-degenerate, flat.
* `torus_second_order`: `regge_second_order` for this complex.

**Limits.** The base lengths of `len0` are Euclidean only on the edges of the complex (other vertex
pairs get the value `1` and do not enter the Regge action). The complex is the standard cubical Kuhn
triangulation; its mesh is `1/n` only after rescaling the lengths.
-/

open Real Finset
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3
open Lightlike.PR (Complex3)

/-- The vertices of the orthoscheme as natural numbers: `0, e₁, e₁ + e₂, e₁ + e₂ + e₃`. -/
def koff : Fin 4 → Fin 3 → ℕ := ![![0, 0, 0], ![1, 0, 0], ![1, 1, 0], ![1, 1, 1]]

theorem koff_le (a : Fin 4) (j : Fin 3) : koff a j ≤ 1 := by
  fin_cases a <;> fin_cases j <;> simp [koff]

theorem koff_cast (a : Fin 4) (j : Fin 3) : ((koff a j : ℕ) : ℝ) = kv a j := by
  fin_cases a <;> fin_cases j <;> simp [koff, kv]

variable (n : ℕ) [NeZero n]

/-- The vertex set of the periodic cubic grid. -/
abbrev TV := Fin 3 → ZMod n

/-- The offset of the corner `a` of the Kuhn tetrahedron `σ` in a cube. -/
def off (σ : Fin 6) (a : Fin 4) : TV n := fun i => (koff a (perms σ i) : ZMod n)

/-- The vertex set of the Kuhn tetrahedron `σ` of the cube with lower corner `c`. -/
def tetV (c : TV n) (σ : Fin 6) : Finset (TV n) := univ.image fun a : Fin 4 => c + off n σ a

theorem natCast_inj01 {x y : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (hn : 2 ≤ n) (h : (x : ZMod n) = y) :
    x = y := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  interval_cases x <;> interval_cases y
  · rfl
  · exact absurd (by simpa using h) (one_ne_zero (α := ZMod n)).symm
  · exact absurd (by simpa using h) (one_ne_zero (α := ZMod n))
  · rfl

/-- The four corners of a Kuhn tetrahedron are distinct points of the grid (`n ≥ 2`). -/
theorem off_injective (hn : 2 ≤ n) (σ : Fin 6) : Function.Injective (off n σ) := by
  intro a b h
  have hi : ∀ i, koff a (perms σ i) = koff b (perms σ i) := fun i =>
    natCast_inj01 n (koff_le _ _) (koff_le _ _) hn (congrFun h i)
  fin_cases σ <;> fin_cases a <;> fin_cases b <;> simp_all [perms, koff, Fin.forall_fin_succ]

/-- The periodic Kuhn complex of the grid `(ℤ/n)³`: the six Kuhn tetrahedra of every cube. -/
def torusComplex (hn : 2 ≤ n) : Complex3 (TV n) where
  tets := univ.image fun p : TV n × Fin 6 => tetV n p.1 p.2
  card_eq := by
    intro t ht
    simp only [mem_image, mem_univ, true_and] at ht
    obtain ⟨⟨c, σ⟩, rfl⟩ := ht
    unfold tetV
    rw [card_image_of_injective _ (fun a b h => off_injective n hn σ (add_left_cancel h))]
    simp


theorem two_ne_zero_zmod (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem coord_mem (c : TV n) (σ : Fin 6) (i : Fin 3) (v : TV n) (hv : v ∈ tetV n c σ) :
    v i = c i ∨ v i = c i + 1 := by
  simp only [tetV, mem_image, mem_univ, true_and] at hv
  obtain ⟨a, rfl⟩ := hv
  have h := koff_le a (perms σ i)
  simp only [Pi.add_apply, off]
  interval_cases hk : koff a (perms σ i) <;> simp

theorem coord_mem' (c : TV n) (σ : Fin 6) (i : Fin 3) :
    c i ∈ ((tetV n c σ).image fun v => v i) ∧ c i + 1 ∈ ((tetV n c σ).image fun v => v i) := by
  have h0 : ∃ a, koff a (perms σ i) = 0 := ⟨0, by fin_cases σ <;> fin_cases i <;> simp [koff, perms]⟩
  have h1 : ∃ a, koff a (perms σ i) = 1 := ⟨3, by fin_cases σ <;> fin_cases i <;> simp [koff, perms]⟩
  obtain ⟨a0, ha0⟩ := h0
  obtain ⟨a1, ha1⟩ := h1
  refine ⟨mem_image.2 ⟨c + off n σ a0, ?_, ?_⟩, mem_image.2 ⟨c + off n σ a1, ?_, ?_⟩⟩
  · simp only [tetV, mem_image, mem_univ, true_and]; exact ⟨a0, rfl⟩
  · simp [off, ha0]
  · simp only [tetV, mem_image, mem_univ, true_and]; exact ⟨a1, rfl⟩
  · simp [off, ha1]

theorem tetV_inj_base (hn : 3 ≤ n) {c c' : TV n} {σ σ' : Fin 6} (h : tetV n c σ = tetV n c' σ') :
    c = c' := by
  funext i
  have h1 := (coord_mem' n c σ i).1
  have h2 := (coord_mem' n c' σ' i).1
  rw [h] at h1
  rw [← h] at h2
  obtain ⟨v, hv, hvi⟩ := mem_image.1 h1
  obtain ⟨w, hw, hwi⟩ := mem_image.1 h2
  have a1 := coord_mem n c' σ' i v hv
  have a2 := coord_mem n c σ i w hw
  rw [hvi] at a1
  rw [hwi] at a2
  have h2ne := two_ne_zero_zmod n hn
  have h1ne : (1 : ZMod n) ≠ 0 := by
    haveI : Fact (1 < n) := ⟨by omega⟩
    exact one_ne_zero
  rcases a1 with a1 | a1
  · exact a1
  · rcases a2 with a2 | a2
    · exact a2.symm
    · exfalso
      apply h2ne
      linear_combination -a1 - a2


theorem perm_separate : ∀ σ σ' : Fin 6, σ ≠ σ' →
    ∃ a : Fin 4, ∀ b : Fin 4, ∃ i : Fin 3, koff a (perms σ i) ≠ koff b (perms σ' i) := by
  decide

theorem tetV_inj_perm (hn : 2 ≤ n) {c : TV n} {σ σ' : Fin 6} (h : tetV n c σ = tetV n c σ') :
    σ = σ' := by
  by_contra hne
  obtain ⟨a, ha⟩ := perm_separate σ σ' hne
  have hmem : c + off n σ a ∈ tetV n c σ' := by
    rw [← h]; simp only [tetV, mem_image, mem_univ, true_and]; exact ⟨a, rfl⟩
  simp only [tetV, mem_image, mem_univ, true_and] at hmem
  obtain ⟨b, hb⟩ := hmem
  have hb' := add_left_cancel hb
  obtain ⟨i, hi⟩ := ha b
  exact hi (natCast_inj01 n (koff_le _ _) (koff_le _ _) hn (congrFun hb' i).symm)

/-- Distinct pairs (cube, tetrahedron) give distinct tetrahedra. -/
theorem tetV_injective (hn : 3 ≤ n) : Function.Injective fun p : TV n × Fin 6 => tetV n p.1 p.2 := by
  rintro ⟨c, σ⟩ ⟨c', σ'⟩ h
  have hc := tetV_inj_base n hn h
  subst hc
  have := tetV_inj_perm n (by omega) h
  subst this
  rfl


/-- The number of coordinates in which two grid vertices differ. -/
def hdist (x y : TV n) : ℕ := (univ.filter fun i => x i ≠ y i).card

/-- The base lengths of the periodic Kuhn complex: the Euclidean length `√(number of differing
coordinates)` of a pair of neighbouring vertices (the vertices of an edge of the complex differ by
`0` or `1` in each coordinate). The value for a set that is not a pair of distinct vertices is `1`; it
does not enter the Regge action. -/
noncomputable def len0 (g : Finset (TV n)) : ℝ :=
  √(max 1 ((∑ x ∈ g, ∑ y ∈ g, (hdist n x y : ℝ)) / 2))

theorem len0_pos (g : Finset (TV n)) : 0 < len0 n g := by
  unfold len0
  exact Real.sqrt_pos.2 (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem len0_pair {x y : TV n} (hxy : x ≠ y) : len0 n {x, y} = √(hdist n x y) := by
  have hpos : 1 ≤ hdist n x y := by
    unfold hdist
    rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, filter_eq_empty_iff]
    push_neg
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    exact ⟨i, mem_univ _, hi⟩
  have hs : hdist n y x = hdist n x y := by
    unfold hdist; congr 1; ext i; simp [eq_comm]
  have hd : hdist n x x = 0 := by simp [hdist]
  have hd' : hdist n y y = 0 := by simp [hdist]
  unfold len0
  rw [sum_pair hxy, sum_pair hxy, sum_pair hxy]
  simp only [hd, hd', hs, Nat.cast_zero]
  rw [max_eq_right (by have : (1 : ℝ) ≤ hdist n x y := by exact_mod_cast hpos
                       linarith)]
  congr 1; ring


theorem koff_sq (a b : Fin 4) (j : Fin 3) :
    (if koff a j ≠ koff b j then (1 : ℝ) else 0) = (kv a j - kv b j) ^ 2 := by
  fin_cases a <;> fin_cases b <;> fin_cases j <;> simp [koff, kv]

/-- The squared length between two corners of a Kuhn tetrahedron is the Euclidean squared distance of
the corresponding vertices of the orthoscheme. -/
theorem hdist_corner (hn : 2 ≤ n) (c : TV n) (σ : Fin 6) (a b : Fin 4) :
    (hdist n (c + off n σ a) (c + off n σ b) : ℝ) =
      sqd (fun i => kv a (perms σ i)) (fun i => kv b (perms σ i)) := by
  have hne : ∀ i, (c + off n σ a) i ≠ (c + off n σ b) i ↔ koff a (perms σ i) ≠ koff b (perms σ i) := by
    intro i
    have e1 : (c + off n σ a) i = (c + off n σ b) i ↔ off n σ a i = off n σ b i := by
      simp [Pi.add_apply]
    rw [Ne, e1]
    unfold off
    exact not_congr ⟨fun h => natCast_inj01 n (koff_le _ _) (koff_le _ _) hn h, fun h => by rw [h]⟩
  have : hdist n (c + off n σ a) (c + off n σ b) =
      (univ.filter fun i : Fin 3 => koff a (perms σ i) ≠ koff b (perms σ i)).card := by
    unfold hdist; congr 1; exact filter_congr fun i _ => hne i
  rw [this, card_filter]
  push_cast
  rw [Fin.sum_univ_three]
  unfold sqd
  simp only [koff_sq]


theorem hinge_distinct : ∀ h : Fin 6, hP h ≠ hQ h ∧ hP h ≠ hR h ∧ hP h ≠ hS h ∧ hQ h ≠ hR h ∧
    hQ h ≠ hS h ∧ hR h ≠ hS h := by decide

theorem hinge_cover : ∀ h : Fin 6, ({hP h, hQ h, hR h, hS h} : Finset (Fin 4)) = univ := by decide

/-- The vertices of the Kuhn tetrahedron `(c, σ)`, in the labelling of the hinge `h`. -/
theorem tetV_eq_hinge (c : TV n) (σ h : Fin 6) :
    tetV n c σ = {c + off n σ (hP h), c + off n σ (hQ h), c + off n σ (hR h), c + off n σ (hS h)} := by
  unfold tetV
  rw [← hinge_cover h]
  simp [image_insert]

theorem hbase_nonneg (h : Fin 6) (j : Fin 6) : 0 ≤ hbase h j := by
  fin_cases h <;> fin_cases j <;> simp [hbase]

theorem hbase_pos' (h : Fin 6) (j : Fin 6) : 0 < hbase h j := by
  fin_cases h <;> fin_cases j <;> simp [hbase]

/-- The length of the segment between two distinct corners of a Kuhn tetrahedron. -/
theorem len0_corner (hn : 2 ≤ n) (c : TV n) (σ : Fin 6) {a b : Fin 4} (hab : a ≠ b) :
    len0 n {c + off n σ a, c + off n σ b} =
      √(sqd (fun i => kv a (perms σ i)) (fun i => kv b (perms σ i))) := by
  rw [len0_pair n (fun h => hab (off_injective n hn σ (add_left_cancel h))), hdist_corner n hn]

/-- The sum of squares of a permuted vertex pair of the orthoscheme is that of the unpermuted pair. -/
theorem sqd_perm (σ : Fin 6) (a b : Fin 4) :
    sqd (fun i => kv a (perms σ i)) (fun i => kv b (perms σ i)) = sqd (kv a) (kv b) := by
  fin_cases σ <;> simp [sqd, perms] <;> ring

/-- **The dihedral angle of a Kuhn tetrahedron at a hinge** of the periodic complex with the base
lengths is the angle `hang h` of the orthoscheme. -/
theorem dihedralAt_hinge (hn : 2 ≤ n) (c : TV n) (σ h : Fin 6) :
    dihedralAt (len0 n) (tetV n c σ) {c + off n σ (hP h), c + off n σ (hQ h)} = hang h := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hinge_distinct h
  have inj := fun {a b : Fin 4} (hab : a ≠ b) (e : c + off n σ a = c + off n σ b) =>
    hab (off_injective n hn σ (add_left_cancel e))
  rw [tetV_eq_hinge n c σ h, dihedralAt_eq _ (fun e => inj d1 e) (fun e => inj d2 e)
    (fun e => inj d3 e) (fun e => inj d4 e) (fun e => inj d5 e) (fun e => inj d6 e)
    (len0_pos n _).ne']
  rw [len0_corner n hn c σ d1, len0_corner n hn c σ d2, len0_corner n hn c σ d4,
    len0_corner n hn c σ d3, len0_corner n hn c σ d5, len0_corner n hn c σ d6]
  have hb := hbase_eq h
  have e0 : sqd (kv (hP h)) (kv (hQ h)) = hbase h 0 := by rw [hb]; rfl
  have e1 : sqd (kv (hP h)) (kv (hR h)) = hbase h 1 := by rw [hb]; rfl
  have e2 : sqd (kv (hQ h)) (kv (hR h)) = hbase h 2 := by rw [hb]; rfl
  have e3 : sqd (kv (hP h)) (kv (hS h)) = hbase h 3 := by rw [hb]; rfl
  have e4 : sqd (kv (hQ h)) (kv (hS h)) = hbase h 4 := by rw [hb]; rfl
  have e5 : sqd (kv (hR h)) (kv (hS h)) = hbase h 5 := by rw [hb]; rfl
  simp only [sqd_perm, e0, e1, e2, e3, e4, e5]
  rw [dihedral_sqrt_eq (hbase_pos' h 0) (hbase_nonneg h 1) (hbase_nonneg h 2) (hbase_nonneg h 3)
    (hbase_nonneg h 4) (hbase_nonneg h 5)]
  rw [← hang_eq h]
  rfl


/-- The edge of the tetrahedron `(c, σ)` that is the hinge `h`. -/
def hing (c : TV n) (σ h : Fin 6) : Finset (TV n) := {c + off n σ (hP h), c + off n σ (hQ h)}

theorem hinge_pairs : ∀ h h' : Fin 6, (hP h = hP h' ∧ hQ h = hQ h') ∨ (hP h = hQ h' ∧ hQ h = hP h') →
    h = h' := by decide

theorem hinge_cover_pairs : ∀ a b : Fin 4, a ≠ b → ∃ h : Fin 6,
    (hP h = a ∧ hQ h = b) ∨ (hP h = b ∧ hQ h = a) := by decide

theorem koff_mono : ∀ (h : Fin 6) (j : Fin 3), koff (hP h) j ≤ koff (hQ h) j := by decide

/-- A pair of vertices of a Kuhn tetrahedron is one of its six hinges. -/
theorem subset_tetV_iff (hn : 2 ≤ n) (c : TV n) (σ : Fin 6) {e : Finset (TV n)} (he : e.card = 2) :
    e ⊆ tetV n c σ ↔ ∃ h, e = hing n c σ h := by
  constructor
  · intro hs
    obtain ⟨u, v, huv, rfl⟩ := card_eq_two.1 he
    have hu : u ∈ tetV n c σ := hs (by simp)
    have hv : v ∈ tetV n c σ := hs (by simp)
    simp only [tetV, mem_image, mem_univ, true_and] at hu hv
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := hv
    have hab : a ≠ b := fun h => huv (by rw [h])
    obtain ⟨h, hh | hh⟩ := hinge_cover_pairs a b hab
    · exact ⟨h, by simp [hing, hh.1, hh.2]⟩
    · exact ⟨h, by simp [hing, hh.1, hh.2, pair_comm]⟩
  · rintro ⟨h, rfl⟩
    intro x hx
    simp only [hing, mem_insert, mem_singleton] at hx
    simp only [tetV, mem_image, mem_univ, true_and]
    rcases hx with rfl | rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩


/-- The sum over the star of an edge is a sum over the pairs (cube, tetrahedron) containing it. -/
theorem star_sum (hn : 3 ≤ n) (e : Finset (TV n)) (G : Finset (TV n) → ℝ) :
    ∑ t ∈ star (torusComplex n (by omega)) e, G t =
      ∑ p : TV n × Fin 6, if e ⊆ tetV n p.1 p.2 then G (tetV n p.1 p.2) else 0 := by
  have hstar : star (torusComplex n (by omega)) e =
      (univ.filter fun p : TV n × Fin 6 => e ⊆ tetV n p.1 p.2).image
        fun p => tetV n p.1 p.2 := by
    unfold star torusComplex
    rw [filter_image]
  rw [hstar, sum_image (fun x _ y _ h => tetV_injective n hn h), sum_filter]


theorem hing_inj (hn : 2 ≤ n) (c : TV n) (σ : Fin 6) {h h' : Fin 6}
    (e : hing n c σ h = hing n c σ h') : h = h' := by
  have inj := fun {a b : Fin 4} (e : c + off n σ a = c + off n σ b) =>
    off_injective n hn σ (add_left_cancel e)
  have h1 : c + off n σ (hP h) ∈ hing n c σ h' := by rw [← e]; simp [hing]
  have h2 : c + off n σ (hQ h) ∈ hing n c σ h' := by rw [← e]; simp [hing]
  simp only [hing, mem_insert, mem_singleton] at h1 h2
  apply hinge_pairs
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (by rw [inj h1, inj h2]) (hinge_distinct h).1
  · exact Or.inl ⟨inj h1, inj h2⟩
  · exact Or.inr ⟨inj h1, inj h2⟩
  · exact absurd (by rw [inj h1, inj h2]) (hinge_distinct h).1

/-- The sum of the dihedral angles at an edge of the periodic complex is a sum over the
pairs (cube, tetrahedron) and hinges that realise the edge. -/
theorem angleSum_eq (hn : 3 ≤ n) (e : Finset (TV n)) (he : e.card = 2) :
    angleSum (torusComplex n (by omega)) (len0 n) e =
      ∑ p : TV n × Fin 6, ∑ h : Fin 6, if e = hing n p.1 p.2 h then hang h else 0 := by
  unfold angleSum
  rw [star_sum n hn]
  refine sum_congr rfl fun p _ => ?_
  by_cases hs : e ⊆ tetV n p.1 p.2
  · obtain ⟨h0, rfl⟩ := (subset_tetV_iff n (by omega) p.1 p.2 he).1 hs
    rw [if_pos hs, show hing n p.1 p.2 h0 = {p.1 + off n p.2 (hP h0), p.1 + off n p.2 (hQ h0)} from rfl,
      dihedralAt_hinge n (by omega)]
    change hang h0 = _
    rw [← show hing n p.1 p.2 h0 = {p.1 + off n p.2 (hP h0), p.1 + off n p.2 (hQ h0)} from rfl]
    rw [sum_eq_single h0]
    · simp
    · intro h _ hh
      rw [if_neg]
      exact fun e' => hh (hing_inj n (by omega) p.1 p.2 e').symm
    · simp
  · rw [if_neg hs]
    symm
    refine sum_eq_zero fun h _ => ?_
    rw [if_neg]
    intro e'
    exact hs ((subset_tetV_iff n (by omega) p.1 p.2 he).2 ⟨h, e'⟩)


theorem natCast_inj2 {x y : ℕ} (hx : x ≤ 2) (hy : y ≤ 2) (hn : 3 ≤ n) (h : (x : ZMod n) = y) :
    x = y := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h

/-- The direction `w` as a vector of the grid. -/
def wv (w : Fin 3 → ℕ) : TV n := fun i => (w i : ZMod n)

/-- The condition that the hinge `h` of the tetrahedron `σ` has direction `w`. -/
def Cond (w : Fin 3 → ℕ) (σ h : Fin 6) : Prop :=
  ∀ i, koff (hQ h) (perms σ i) = koff (hP h) (perms σ i) + w i

instance (w : Fin 3 → ℕ) (σ h : Fin 6) : Decidable (Cond w σ h) := by unfold Cond; infer_instance

theorem wv_ne_zero (hn : 2 ≤ n) {w : Fin 3 → ℕ} (hw1 : ∀ i, w i ≤ 1) (hw0 : ∃ i, w i ≠ 0) :
    wv n w ≠ 0 := by
  obtain ⟨i, hi⟩ := hw0
  intro h
  have := congrFun h i
  simp only [wv, Pi.zero_apply] at this
  have h0 : ((w i : ℕ) : ZMod n) = ((0 : ℕ) : ZMod n) := by simpa using this
  exact hi (natCast_inj01 n (hw1 i) (by norm_num) hn h0)

/-- **The hinges of direction `w` at the edge `{z, z + w}`.** A hinge `h` of a tetrahedron `(c, σ)`
is the edge `{z, z + w}` exactly when the cube is `c = z - off σ (hP h)` and the hinge has direction `w`. -/
theorem hing_eq_iff (hn : 3 ≤ n) {w : Fin 3 → ℕ} (hw1 : ∀ i, w i ≤ 1) (hw0 : ∃ i, w i ≠ 0)
    (z c : TV n) (σ h : Fin 6) :
    ({z, z + wv n w} : Finset (TV n)) = hing n c σ h ↔ Cond w σ h ∧ c = z - off n σ (hP h) := by
  have hwne := wv_ne_zero n (by omega) hw1 hw0
  have hcast : ∀ i, ((koff (hQ h) (perms σ i) : ℕ) : ZMod n) =
      ((koff (hP h) (perms σ i) : ℕ) : ZMod n) + (w i : ZMod n) →
      koff (hQ h) (perms σ i) = koff (hP h) (perms σ i) + w i := fun i hi => by
    have := natCast_inj2 n (x := koff (hQ h) (perms σ i)) (y := koff (hP h) (perms σ i) + w i)
      (by have := koff_le (hQ h) (perms σ i); omega)
      (by have := koff_le (hP h) (perms σ i); have := hw1 i; omega) hn (by rw [hi]; push_cast; rfl)
    exact this
  constructor
  · intro e
    have h1 : z ∈ hing n c σ h := by rw [← e]; simp
    have h2 : z + wv n w ∈ hing n c σ h := by rw [← e]; simp
    simp only [hing, mem_insert, mem_singleton] at h1 h2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd (by rw [← h1] at h2; simpa using h2) hwne
      · refine ⟨fun i => hcast i ?_, by rw [h1]; abel⟩
        have := congrFun h2 i
        have h1i := congrFun h1 i
        simp only [Pi.add_apply, wv, off] at this h1i
        rw [h1i] at this
        linear_combination -this
    · exfalso
      rcases h2 with h2 | h2
      · obtain ⟨i, hi⟩ := hw0
        have hw : ∀ j, w j = 0 := by
          intro j
          have := congrFun h2 j
          have h1j := congrFun h1 j
          simp only [Pi.add_apply, wv, off] at this h1j
          rw [h1j] at this
          have hnat : koff (hP h) (perms σ j) = koff (hQ h) (perms σ j) + w j := by
            apply natCast_inj2 n (by have := koff_le (hP h) (perms σ j); omega)
              (by have := koff_le (hQ h) (perms σ j); have := hw1 j; omega) hn
            push_cast
            linear_combination -this
          have := koff_mono h (perms σ j)
          omega
        exact hi (hw i)
      · exact hwne (by rw [← h1] at h2; simpa using h2)
  · rintro ⟨hc, rfl⟩
    have hq : ∀ i, (off n σ (hQ h)) i = (off n σ (hP h)) i + (wv n w) i := by
      intro i
      simp only [off, wv]
      have := hc i
      rw [this]; push_cast; ring
    have : z - off n σ (hP h) + off n σ (hQ h) = z + wv n w := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [hq i]; ring
    simp only [hing, sub_add_cancel, this]


theorem cond_iff_real (w : Fin 3 → ℕ) (σ h : Fin 6) :
    Cond w σ h ↔ (kv (hQ h) (perms σ 0) - kv (hP h) (perms σ 0) = (w 0 : ℝ) ∧
      kv (hQ h) (perms σ 1) - kv (hP h) (perms σ 1) = (w 1 : ℝ) ∧
      kv (hQ h) (perms σ 2) - kv (hP h) (perms σ 2) = (w 2 : ℝ)) := by
  have key : ∀ i : Fin 3, koff (hQ h) (perms σ i) = koff (hP h) (perms σ i) + w i ↔
      kv (hQ h) (perms σ i) - kv (hP h) (perms σ i) = (w i : ℝ) := by
    intro i
    rw [← koff_cast, ← koff_cast]
    constructor
    · intro hh; rw [hh]; push_cast; ring
    · intro hh; exact_mod_cast (by linarith : ((koff (hQ h) (perms σ i) : ℕ) : ℝ) =
        (koff (hP h) (perms σ i) : ℕ) + (w i : ℕ))
  unfold Cond
  constructor
  · intro hc
    exact ⟨(key 0).1 (hc 0), (key 1).1 (hc 1), (key 2).1 (hc 2)⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact (key 0).2 h0
    · exact (key 1).2 h1
    · exact (key 2).2 h2

/-- **The angles at an edge `{z, z + w}` of the periodic complex add up to `2π`:** the periodic Kuhn
complex is flat, every deficit angle vanishes. -/
theorem angleSum_class (hn : 3 ≤ n) {w : Fin 3 → ℕ} (hw1 : ∀ i, w i ≤ 1) (hw0 : ∃ i, w i ≠ 0)
    (z : TV n) :
    angleSum (torusComplex n (by omega)) (len0 n) {z, z + wv n w} = 2 * π := by
  have hwne := wv_ne_zero n (by omega) hw1 hw0
  have hcard : ({z, z + wv n w} : Finset (TV n)).card = 2 := by
    rw [card_pair]; intro h; apply hwne; simpa using h
  rw [angleSum_eq n hn _ hcard, Fintype.sum_prod_type]
  simp only [hing_eq_iff n hn hw1 hw0]
  rw [sum_comm]
  have step : ∀ σ : Fin 6, ∑ c : TV n, ∑ h : Fin 6,
      (if Cond w σ h ∧ c = z - off n σ (hP h) then hang h else 0) =
      ∑ h : Fin 6, if Cond w σ h then hang h else 0 := by
    intro σ
    rw [sum_comm]
    refine sum_congr rfl fun h _ => ?_
    simp only [ite_and]
    by_cases hc : Cond w σ h
    · simp [hc]
    · simp [hc]
  simp only [step]
  have := star_angle_sum (w 0 : ℝ) (w 1) (w 2)
    (by rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hw1 0) with h | h <;> simp [h])
    (by rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hw1 1) with h | h <;> simp [h])
    (by rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hw1 2) with h | h <;> simp [h])
    (by
      obtain ⟨i, hi⟩ := hw0
      rintro ⟨h0, h1, h2⟩
      fin_cases i
      · exact hi (by exact_mod_cast h0)
      · exact hi (by exact_mod_cast h1)
      · exact hi (by exact_mod_cast h2))
  rw [← this]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun h _ => ?_
  simp only [← cond_iff_real]


theorem sqd_nonneg' (y z : Fin 3 → ℝ) : 0 ≤ sqd y z := by unfold sqd; positivity

theorem len0_sq (hn : 2 ≤ n) (c : TV n) (σ : Fin 6) {a b : Fin 4} (hab : a ≠ b) :
    len0 n {c + off n σ a, c + off n σ b} ^ 2 = sqd (kv a) (kv b) := by
  rw [len0_corner n hn c σ hab, Real.sq_sqrt (sqd_nonneg' _ _), sqd_perm]

/-- Heron's quantity in terms of the squares. -/
theorem heron_sqrt {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Lightlike.Regge.heron (√x) (√y) (√z) = 2 * (x * y + y * z + z * x) - (x ^ 2 + y ^ 2 + z ^ 2) := by
  unfold Lightlike.Regge.heron
  have e1 : √x ^ 4 = x ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hx]
  have e2 : √y ^ 4 = y ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hy]
  have e3 : √z ^ 4 = z ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hz]
  rw [e1, e2, e3, Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sq_sqrt hz]

theorem face_pos : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
    0 < 2 * (sqd (kv a) (kv b) * sqd (kv b) (kv c) + sqd (kv b) (kv c) * sqd (kv c) (kv a) +
      sqd (kv c) (kv a) * sqd (kv a) (kv b)) -
      (sqd (kv a) (kv b) ^ 2 + sqd (kv b) (kv c) ^ 2 + sqd (kv c) (kv a) ^ 2) := by
  intro a b c hab hac hbc
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all [sqd, kv] <;> norm_num


theorem mem_tetV (c : TV n) (σ : Fin 6) {x : TV n} (hx : x ∈ tetV n c σ) :
    ∃ a : Fin 4, x = c + off n σ a := by
  simp only [tetV, mem_image, mem_univ, true_and] at hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, rfl⟩

/-- **The base lengths of the periodic Kuhn complex are non-degenerate.** -/
theorem lengthsNondeg_len0 (hn : 3 ≤ n) : LengthsNondeg (torusComplex n (by omega)) (len0 n) := by
  intro t ht
  have ht' : t ∈ univ.image fun p : TV n × Fin 6 => tetV n p.1 p.2 := ht
  simp only [mem_image, mem_univ, true_and] at ht'
  obtain ⟨⟨c, σ⟩, rfl⟩ := ht'
  refine ⟨fun e _ => len0_pos n e, fun f hf => ?_, ?_⟩
  · obtain ⟨hfs, hf3⟩ := mem_powersetCard.1 hf
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.1 hf3
    obtain ⟨a, rfl⟩ := mem_tetV n c σ (hfs (by simp : x ∈ ({x, y, z} : Finset (TV n))))
    obtain ⟨b, rfl⟩ := mem_tetV n c σ (hfs (by simp : y ∈ ({_, y, z} : Finset (TV n))))
    obtain ⟨d, rfl⟩ := mem_tetV n c σ (hfs (by simp : z ∈ ({_, _, z} : Finset (TV n))))
    have hab : a ≠ b := fun h => hxy (by rw [h])
    have had : a ≠ d := fun h => hxz (by rw [h])
    have hbd : b ≠ d := fun h => hyz (by rw [h])
    rw [triH_eq _ hxy hxz hyz, len0_corner n (by omega) c σ hab, len0_corner n (by omega) c σ hbd,
      len0_corner n (by omega) c σ had.symm, sqd_perm, sqd_perm, sqd_perm,
      heron_sqrt (sqd_nonneg' _ _) (sqd_nonneg' _ _) (sqd_nonneg' _ _)]
    have := face_pos a b d hab had hbd
    exact this
  · have e := tetV_eq_hinge n c σ 0
    have d := hinge_distinct 0
    rw [e]
    have inj := fun {a b : Fin 4} (hab : a ≠ b) (e : c + off n σ a = c + off n σ b) =>
      hab (off_injective n (by omega) σ (add_left_cancel e))
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := d
    rw [tetV2_eq _ (fun e => inj d1 e) (fun e => inj d2 e) (fun e => inj d3 e) (fun e => inj d4 e)
      (fun e => inj d5 e) (fun e => inj d6 e)]
    rw [len0_corner n (by omega) c σ d1, len0_corner n (by omega) c σ d4,
      len0_corner n (by omega) c σ d2.symm, len0_corner n (by omega) c σ d6,
      len0_corner n (by omega) c σ d3, len0_corner n (by omega) c σ d5]
    unfold Lightlike.PR.vol2
    simp only [sqd_perm, Real.sq_sqrt (sqd_nonneg' _ _)]
    norm_num [sqd, kv, hP, hQ, hR, hS]


/-- Every edge of the periodic complex is `{z, z + w}` with `w ∈ {0,1}³` non-zero. -/
theorem edge_form (hn : 3 ≤ n) {e : Finset (TV n)} (he : e ∈ (torusComplex n (by omega)).edges) :
    ∃ (z : TV n) (w : Fin 3 → ℕ), (∀ i, w i ≤ 1) ∧ (∃ i, w i ≠ 0) ∧ e = {z, z + wv n w} := by
  obtain ⟨t, ht, hse, h2⟩ := Complex3.mem_edges.mp he
  have ht' : t ∈ univ.image fun p : TV n × Fin 6 => tetV n p.1 p.2 := ht
  simp only [mem_image, mem_univ, true_and] at ht'
  obtain ⟨⟨c, σ⟩, rfl⟩ := ht'
  obtain ⟨h, rfl⟩ := (subset_tetV_iff n (by omega) c σ h2).1 hse
  refine ⟨c + off n σ (hP h), fun i => koff (hQ h) (perms σ i) - koff (hP h) (perms σ i), ?_, ?_, ?_⟩
  · intro i
    show koff (hQ h) (perms σ i) - koff (hP h) (perms σ i) ≤ 1
    have := koff_le (hQ h) (perms σ i); omega
  · by_contra hcon
    push Not at hcon
    have hd := hinge_distinct h
    apply hd.1
    apply off_injective n (by omega) σ
    funext i
    have h1 := koff_mono h (perms σ i)
    have h2 := hcon i
    have : koff (hP h) (perms σ i) = koff (hQ h) (perms σ i) := by omega
    simp only [off, this]
  · have hq : c + off n σ (hQ h) =
        (c + off n σ (hP h)) + wv n (fun i => koff (hQ h) (perms σ i) - koff (hP h) (perms σ i)) := by
      funext i
      have h1 := koff_mono h (perms σ i)
      simp only [wv, Pi.add_apply, off]
      rw [Nat.cast_sub h1]
      ring
    simp only [hing]
    rw [← hq]

/-- **The periodic Kuhn complex of `(ℤ/n)³` with its base lengths is flat:** every deficit angle
vanishes (`n ≥ 3`). -/
theorem deficit_len0 (hn : 3 ≤ n) {e : Finset (TV n)} (he : e ∈ (torusComplex n (by omega)).edges) :
    deficit (torusComplex n (by omega)) (len0 n) e = 0 := by
  obtain ⟨z, w, hw1, hw0, rfl⟩ := edge_form n hn he
  rw [deficit, angleSum_class n hn hw1 hw0, sub_self]


/-- Across each face of a Kuhn tetrahedron there is another Kuhn tetrahedron: a different
permutation or a different cube (shifted by `s - 1` in each coordinate). -/
theorem neighbour : ∀ (σ : Fin 6) (a : Fin 4), ∃ (s : Fin 3 → Fin 3) (σ' : Fin 6),
    (σ' ≠ σ ∨ ∃ i, (s i : ℕ) ≠ 1) ∧ ∀ b : Fin 4, b ≠ a → ∃ b' : Fin 4, ∀ i : Fin 3,
      (koff b (perms σ i) : ℤ) = ((s i : ℕ) : ℤ) - 1 + koff b' (perms σ' i) := by
  decide

/-- A triangle of a Kuhn tetrahedron lies in another Kuhn tetrahedron. -/
theorem exists_other_tet (hn : 3 ≤ n) (c : TV n) (σ : Fin 6) {f : Finset (TV n)}
    (hfs : f ⊆ tetV n c σ) (h3 : f.card = 3) :
    ∃ (c' : TV n) (σ' : Fin 6), (c', σ') ≠ (c, σ) ∧ f ⊆ tetV n c' σ' := by
  have h4 : (tetV n c σ).card = 4 := by
    unfold tetV
    rw [card_image_of_injective _ (fun a b h => off_injective n (by omega) σ (add_left_cancel h))]
    simp
  have hd : (tetV n c σ \ f).card = 1 := by rw [card_sdiff_of_subset hfs, h4, h3]
  obtain ⟨v, hv⟩ := card_eq_one.1 hd
  have hvm : v ∈ tetV n c σ \ f := by rw [hv]; simp
  obtain ⟨hvt, hvf⟩ := mem_sdiff.1 hvm
  obtain ⟨a, rfl⟩ := mem_tetV n c σ hvt
  have hcorner : ∀ x ∈ f, ∃ b : Fin 4, b ≠ a ∧ x = c + off n σ b := by
    intro x hx
    obtain ⟨b, rfl⟩ := mem_tetV n c σ (hfs hx)
    exact ⟨b, fun hba => hvf (by rw [← hba]; exact hx), rfl⟩
  obtain ⟨s, σ', hne, hb⟩ := neighbour σ a
  refine ⟨c + fun i => (((s i : ℕ) : ZMod n) - 1), σ', ?_, ?_⟩
  · intro h
    rcases hne with hne | ⟨i, hi⟩
    · exact hne (congrArg Prod.snd h)
    · have hci := congrFun (congrArg Prod.fst h) i
      simp only [Pi.add_apply, add_eq_left] at hci
      have h1ne : (1 : ZMod n) ≠ 0 := by
        haveI : Fact (1 < n) := ⟨by omega⟩
        exact one_ne_zero
      have hs2 : (s i : ℕ) = 0 ∨ (s i : ℕ) = 2 := by have := (s i).2; omega
      rcases hs2 with h0 | h2
      · rw [h0] at hci
        apply h1ne
        simpa using hci
      · rw [h2] at hci
        apply h1ne
        push_cast at hci
        linear_combination hci
  · intro x hx
    obtain ⟨b, hba, rfl⟩ := hcorner x hx
    obtain ⟨b', hb'⟩ := hb b hba
    simp only [tetV, mem_image, mem_univ, true_and]
    refine ⟨b', ?_⟩
    funext i
    have := congrArg (fun z : ℤ => (z : ZMod n)) (hb' i)
    simp only [Pi.add_apply, off]
    push_cast at this
    rw [this]; ring

/-- **The periodic Kuhn complex is closed:** every triangle lies in at least two tetrahedra, so
there is no boundary triangle. -/
theorem bdryTris_torus (hn : 3 ≤ n) : bdryTris (torusComplex n (by omega)) = ∅ := by
  unfold bdryTris
  rw [filter_eq_empty_iff]
  intro f hf hcard
  obtain ⟨t, ht, hfs, h3⟩ := Complex3.mem_tris.1 hf
  have ht' : t ∈ univ.image fun p : TV n × Fin 6 => tetV n p.1 p.2 := ht
  simp only [mem_image, mem_univ, true_and] at ht'
  obtain ⟨⟨c, σ⟩, rfl⟩ := ht'
  obtain ⟨c', σ', hneq, hsub⟩ := exists_other_tet n hn c σ hfs h3
  have hmem1 : tetV n c σ ∈ star (torusComplex n (by omega)) f := by
    unfold star; rw [mem_filter]; exact ⟨ht, hfs⟩
  have hmem2 : tetV n c' σ' ∈ star (torusComplex n (by omega)) f := by
    unfold star; rw [mem_filter]
    exact ⟨mem_image.2 ⟨(c', σ'), mem_univ _, rfl⟩, hsub⟩
  have hdiff : tetV n c σ ≠ tetV n c' σ' := fun h => by
    have := @tetV_injective n _ hn (c, σ) (c', σ') h
    exact hneq this.symm
  have : 2 ≤ (star (torusComplex n (by omega)) f).card := by
    calc 2 = (({tetV n c σ, tetV n c' σ'} : Finset (Finset (TV n)))).card := (card_pair hdiff).symm
      _ ≤ _ := card_le_card (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption)
  omega


/-- **Non-vacuity of the second-order expansion.** The hypotheses of `regge_second_order` hold for
the periodic Kuhn complex of `(ℤ/n)³` (`n ≥ 3`) with its base lengths: it is closed, its lengths are
non-degenerate, and every deficit angle vanishes. Hence along every line of squared lengths its Regge
action is `ε²/2 · Σ_e (a_e / (2 ℓ_e)) δ_e'(0) + O(ε³)`. -/
theorem torus_second_order (hn : 3 ≤ n) (a : Finset (TV n) → ℝ) :
    ∃ M r : ℝ, 0 < r ∧ ∀ ε : ℝ, |ε| ≤ r →
      |reggeAction (torusComplex n (by omega)) (lenLine (len0 n) a ε) -
        ε ^ 2 / 2 * ∑ e ∈ (torusComplex n (by omega)).edges, a e / (2 * len0 n e) *
          deriv (fun ε => deficit (torusComplex n (by omega)) (lenLine (len0 n) a ε) e) 0| ≤
        M * |ε| ^ 3 :=
  regge_second_order (bdryTris_torus n hn) (len0_pos n) (lengthsNondeg_len0 n hn)
    (fun _ he => deficit_len0 n hn he) a

end Lightlike.Regge.Linear3
