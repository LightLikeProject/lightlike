import Mathlib

/-!
# The affine map between two triangles of the plane

Piece 1 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  For two affinely independent
triples `a b c` and `a' b' c'` of `ℝ × ℝ`, `triMap` is the affine map sending `a ↦ a'`, `b ↦ b'`,
`c ↦ c'`.  It is a bijection of the plane, with inverse `triMap a' b' c' a b c`, and it maps the
triangle `convexHull {a,b,c}` onto `convexHull {a',b',c'}`, each edge onto the matching edge.
-/

namespace Lightlike.PL.Schoenflies

/-- The planar cross product `u × v`. -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Twice the signed area of the triangle `a b c`. -/
def det3 (a b c : ℝ × ℝ) : ℝ := cross (b - a) (c - a)

/-- Barycentric coordinate of `x` along `b` in the triangle `a b c`. -/
noncomputable def tmB (a b c x : ℝ × ℝ) : ℝ := cross (x - a) (c - a) / det3 a b c

/-- Barycentric coordinate of `x` along `c` in the triangle `a b c`. -/
noncomputable def tmC (a b c x : ℝ × ℝ) : ℝ := cross (b - a) (x - a) / det3 a b c

/-- The affine map of the plane sending the triangle `a b c` to `a' b' c'` vertex by vertex
(meaningful when `det3 a b c ≠ 0`). -/
noncomputable def triMap (a b c a' b' c' x : ℝ × ℝ) : ℝ × ℝ :=
  a' + tmB a b c x • (b' - a') + tmC a b c x • (c' - a')

section
variable {a b c a' b' c' : ℝ × ℝ}

lemma tmB_a : tmB a b c a = 0 := by simp [tmB, cross]
lemma tmC_a : tmC a b c a = 0 := by simp [tmC, cross]
lemma tmB_b (h : det3 a b c ≠ 0) : tmB a b c b = 1 := by
  unfold tmB; rw [div_eq_one_iff_eq h]; simp [det3, cross]
lemma tmC_b : tmC a b c b = 0 := by
  unfold tmC; rw [div_eq_zero_iff]; left
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
lemma tmB_c : tmB a b c c = 0 := by
  unfold tmB; rw [div_eq_zero_iff]; left
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
lemma tmC_c (h : det3 a b c ≠ 0) : tmC a b c c = 1 := by
  unfold tmC; rw [div_eq_one_iff_eq h]; simp [det3, cross]

lemma triMap_a : triMap a b c a' b' c' a = a' := by
  simp [triMap, tmB_a, tmC_a]
lemma triMap_b (h : det3 a b c ≠ 0) : triMap a b c a' b' c' b = b' := by
  simp [triMap, tmB_b h, tmC_b]
lemma triMap_c (h : det3 a b c ≠ 0) : triMap a b c a' b' c' c = c' := by
  simp [triMap, tmB_c, tmC_c h]

lemma tmB_mul (h : det3 a b c ≠ 0) (x : ℝ × ℝ) : tmB a b c x * det3 a b c = cross (x - a) (c - a) := by
  unfold tmB; field_simp

lemma tmC_mul (h : det3 a b c ≠ 0) (x : ℝ × ℝ) : tmC a b c x * det3 a b c = cross (b - a) (x - a) := by
  unfold tmC; field_simp

/-- `x = a + tmB • (b - a) + tmC • (c - a)`: the barycentric coordinates reconstruct `x`. -/
lemma recon (h : det3 a b c ≠ 0) (x : ℝ × ℝ) :
    a + tmB a b c x • (b - a) + tmC a b c x • (c - a) = x := by
  have e1 := tmB_mul h x
  have e2 := tmC_mul h x
  ext
  · apply mul_right_cancel₀ h
    simp only [det3, cross, Prod.fst_sub, Prod.snd_sub] at e1 e2 ⊢
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sub]
    linear_combination (b.1 - a.1) * e1 + (c.1 - a.1) * e2
  · apply mul_right_cancel₀ h
    simp only [det3, cross, Prod.fst_sub, Prod.snd_sub] at e1 e2 ⊢
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_sub]
    linear_combination (b.2 - a.2) * e1 + (c.2 - a.2) * e2

/-- The barycentric coordinates of `a + s (b-a) + t (c-a)` are `s` and `t`. -/
lemma tmB_comb (h : det3 a b c ≠ 0) (s t : ℝ) :
    tmB a b c (a + s • (b - a) + t • (c - a)) = s := by
  unfold tmB; rw [div_eq_iff h]
  simp only [det3, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
  ring

lemma tmC_comb (h : det3 a b c ≠ 0) (s t : ℝ) :
    tmC a b c (a + s • (b - a) + t • (c - a)) = t := by
  unfold tmC; rw [div_eq_iff h]
  simp only [det3, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
  ring

/-- The map is affine: it commutes with every affine combination of two points. -/
lemma triMap_affine (x y : ℝ × ℝ) (t : ℝ) :
    triMap a b c a' b' c' (x + t • (y - x)) =
      triMap a b c a' b' c' x + t • (triMap a b c a' b' c' y - triMap a b c a' b' c' x) := by
  have h1 : tmB a b c (x + t • (y - x)) = tmB a b c x + t * (tmB a b c y - tmB a b c x) := by
    unfold tmB cross
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub]
    ring
  have h2 : tmC a b c (x + t • (y - x)) = tmC a b c x + t * (tmC a b c y - tmC a b c x) := by
    unfold tmC cross
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub]
    ring
  unfold triMap
  rw [h1, h2]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub] <;> ring

/-- `triMap a' b' c' a b c` undoes `triMap a b c a' b' c'`. -/
lemma triMap_left_inv (h : det3 a b c ≠ 0) (h' : det3 a' b' c' ≠ 0) (x : ℝ × ℝ) :
    triMap a' b' c' a b c (triMap a b c a' b' c' x) = x := by
  unfold triMap
  rw [tmB_comb h', tmC_comb h']
  exact recon h x

/-- The barycentric coordinates of `triMap x` in the target triangle are those of `x`. -/
lemma tmB_triMap (h' : det3 a' b' c' ≠ 0) (x : ℝ × ℝ) :
    tmB a' b' c' (triMap a b c a' b' c' x) = tmB a b c x := tmB_comb h' _ _

lemma tmC_triMap (h' : det3 a' b' c' ≠ 0) (x : ℝ × ℝ) :
    tmC a' b' c' (triMap a b c a' b' c' x) = tmC a b c x := tmC_comb h' _ _

/-- The closed triangle `convexHull {a,b,c}` is the set of points with barycentric coordinates
`tmB, tmC ≥ 0`, `tmB + tmC ≤ 1`. -/
lemma mem_hull_iff (h : det3 a b c ≠ 0) (x : ℝ × ℝ) :
    x ∈ convexHull ℝ {a, b, c} ↔ 0 ≤ tmB a b c x ∧ 0 ≤ tmC a b c x ∧
      tmB a b c x + tmC a b c x ≤ 1 := by
  constructor
  · intro hx
    have hconv : Convex ℝ {y : ℝ × ℝ | 0 ≤ tmB a b c y ∧ 0 ≤ tmC a b c y ∧
        tmB a b c y + tmC a b c y ≤ 1} := by
      intro y hy z hz s t hs ht hst
      have hs' : s = 1 - t := by linarith
      subst hs'
      have e : (1 - t) • y + t • z = y + t • (z - y) := by
        ext <;> simp <;> ring
      have h1 : tmB a b c (y + t • (z - y)) = tmB a b c y + t * (tmB a b c z - tmB a b c y) := by
        unfold tmB cross
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          Prod.fst_sub, Prod.snd_sub]
        ring
      have h2 : tmC a b c (y + t • (z - y)) = tmC a b c y + t * (tmC a b c z - tmC a b c y) := by
        unfold tmC cross
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          Prod.fst_sub, Prod.snd_sub]
        ring
      obtain ⟨hy1, hy2, hy3⟩ := hy
      obtain ⟨hz1, hz2, hz3⟩ := hz
      show 0 ≤ tmB a b c ((1 - t) • y + t • z) ∧ 0 ≤ tmC a b c ((1 - t) • y + t • z) ∧
        tmB a b c ((1 - t) • y + t • z) + tmC a b c ((1 - t) • y + t • z) ≤ 1
      rw [e, h1, h2]
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    have hsub : ({a, b, c} : Set (ℝ × ℝ)) ⊆ {y : ℝ × ℝ | 0 ≤ tmB a b c y ∧ 0 ≤ tmC a b c y ∧
        tmB a b c y + tmC a b c y ≤ 1} := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · simp [tmB_a, tmC_a]
      · simp [tmB_b h, tmC_b]
      · simp [tmB_c, tmC_c h]
    exact convexHull_min hsub hconv hx
  · rintro ⟨h1, h2, h3⟩
    rw [← recon h x]
    have hc := convex_convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))
    have ha : a ∈ convexHull ℝ {a, b, c} := subset_convexHull ℝ _ (by simp)
    have hb : b ∈ convexHull ℝ {a, b, c} := subset_convexHull ℝ _ (by simp)
    have hc' : c ∈ convexHull ℝ {a, b, c} := subset_convexHull ℝ _ (by simp)
    have key := hc.sum_mem (t := (Finset.univ : Finset (Fin 3)))
      (w := ![1 - tmB a b c x - tmC a b c x, tmB a b c x, tmC a b c x]) (z := ![a, b, c])
      (by intro i _; fin_cases i <;> simp <;> linarith)
      (by simp [Fin.sum_univ_three]; ring)
      (by intro i _; fin_cases i <;> simp [ha, hb, hc'])
    simp only [Fin.sum_univ_three] at key
    convert key using 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    ext <;> simp <;> ring

/-- The triangle `a b c` goes onto the triangle `a' b' c'`. -/
lemma triMap_mapsTo (h : det3 a b c ≠ 0) (h' : det3 a' b' c' ≠ 0) :
    Set.MapsTo (triMap a b c a' b' c' ) (convexHull ℝ {a, b, c}) (convexHull ℝ {a', b', c'}) := by
  intro x hx
  rw [mem_hull_iff h] at hx
  rw [mem_hull_iff h', tmB_triMap h', tmC_triMap h']
  exact hx

/-- The triangle map is a bijection of triangles. -/
lemma triMap_bijOn (h : det3 a b c ≠ 0) (h' : det3 a' b' c' ≠ 0) :
    Set.BijOn (triMap a b c a' b' c') (convexHull ℝ {a, b, c}) (convexHull ℝ {a', b', c'}) := by
  refine ⟨triMap_mapsTo h h', ?_, ?_⟩
  · intro x _ y _ hxy
    have := congrArg (triMap a' b' c' a b c) hxy
    rwa [triMap_left_inv h h', triMap_left_inv h h'] at this
  · intro y hy
    refine ⟨triMap a' b' c' a b c y, triMap_mapsTo h' h hy, ?_⟩
    exact triMap_left_inv h' h y

end

end Lightlike.PL.Schoenflies
