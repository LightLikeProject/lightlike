import Lightlike.Asymptotics.EPRL.ReggeState

/-!
# The outward normals of a 4-simplex

For a nondegenerate 4-simplex `σ` in `ℝ⁴`, with outward unit normals `N_a = outNormal σ a` to the
tetrahedra opposite the vertices `a` and heights `h_a`:

* any four of the five normals are linearly independent, hence any three
  (`linearIndependent_outNormal_compl`, `linearIndependent_outNormal_three`);
* the normals close: `Σ_a h_a⁻¹ N_a = 0` (`sum_outNormal_div_height`). This is the Minkowski
  closure `Σ_a V_a N_a = 0` of the tetrahedra, since their volumes are `V_a = 4 V / h_a`;
* two distinct normals are not parallel, `|⟨N_a, N_b⟩| < 1` (`abs_inner_outNormal_lt_one`);
* for the link `e = ab`, the area `A_e` of the triangle shared by the tetrahedra opposite `a` and
  `b` satisfies `2 A_e h_b = √(1 - ⟨N_a, N_b⟩²) V_a` and `2 A_e h_a = √(1 - ⟨N_a, N_b⟩²) V_b`, with
  `V_a = nodeVol σ a` six times the volume of the tetrahedron opposite `a`
  (`triArea_mul_height_tgt`, `triArea_mul_height_src`).

Areas and volumes are computed with the triple cross product `a × b × c` of `ℝ⁴` (`cross3`),
whose length is the Gram determinant of `a, b, c` (`inner_cross3_self`).
-/

open Finset
open scoped RealInnerProductSpace

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Regge4

variable (σ : Simplex4)

/-! ## The outward normals of a 4-simplex -/

/-- The normal `N_a` is orthogonal to every edge of the tetrahedron opposite `a`. -/
lemma inner_outNormal_vsub {a j k : Fin 5} (hj : j ≠ a) (hk : k ≠ a) :
    ⟪outNormal σ a, σ.points j -ᵥ σ.points k⟫ = 0 := by
  have h1 : ⟪σ.points j -ᵥ σ.altitudeFoot a, σ.points a -ᵥ σ.altitudeFoot a⟫ = 0 :=
    σ.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (Ne.symm hj)
  have h2 : ⟪σ.points k -ᵥ σ.altitudeFoot a, σ.points a -ᵥ σ.altitudeFoot a⟫ = 0 :=
    σ.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (Ne.symm hk)
  rw [real_inner_comm] at h1 h2
  have e : σ.points j -ᵥ σ.points k =
      (σ.points j -ᵥ σ.altitudeFoot a) - (σ.points k -ᵥ σ.altitudeFoot a) :=
    (vsub_sub_vsub_cancel_right _ _ _).symm
  have e2 : σ.altitudeFoot a -ᵥ σ.points a = -(σ.points a -ᵥ σ.altitudeFoot a) :=
    (neg_vsub_eq_vsub_rev _ _).symm
  rw [outNormal, real_inner_smul_left, e, e2, inner_neg_left, inner_sub_right, h1, h2]
  simp

/-- The normal `N_a` points from `σ_a` to the opposite face: `⟨N_a, σ_k - σ_a⟩ = h_a`. -/
lemma inner_outNormal_vsub_self {a k : Fin 5} (hk : k ≠ a) :
    ⟪outNormal σ a, σ.points k -ᵥ σ.points a⟫ = σ.height a := by
  have h := σ.inner_vsub_vsub_altitudeFoot_eq_height_sq (Ne.symm hk)
  have hpos := σ.height_pos a
  have e2 : σ.altitudeFoot a -ᵥ σ.points a = -(σ.points a -ᵥ σ.altitudeFoot a) :=
    (neg_vsub_eq_vsub_rev _ _).symm
  have e3 : σ.points k -ᵥ σ.points a = -(σ.points a -ᵥ σ.points k) :=
    (neg_vsub_eq_vsub_rev _ _).symm
  rw [outNormal, real_inner_smul_left, e2, e3, inner_neg_left, inner_neg_right, neg_neg,
    real_inner_comm, h]
  field_simp

/-- The normals are unit vectors. -/
lemma norm_outNormal (a : Fin 5) : ‖outNormal σ a‖ = 1 := by
  rw [outNormal, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (σ.height_pos a),
    ← dist_eq_norm_vsub']
  exact inv_mul_cancel₀ (σ.height_pos a).ne'

/-- `⟨N_a, N_a⟩ = 1`. -/
lemma inner_outNormal_self (a : Fin 5) : ⟪outNormal σ a, outNormal σ a⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_outNormal, one_pow]

/-- **Any four of the five normals are linearly independent.** -/
theorem linearIndependent_outNormal_compl (k : Fin 5) :
    LinearIndependent ℝ (fun a : {a : Fin 5 // a ≠ k} => outNormal σ a) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (fun v => ⟪v, σ.points i -ᵥ σ.points k⟫) hc
  simp only [sum_inner, real_inner_smul_left, inner_zero_left] at h
  rw [Finset.sum_eq_single i] at h
  · have e3 : σ.points i -ᵥ σ.points k = -(σ.points k -ᵥ σ.points i) :=
      (neg_vsub_eq_vsub_rev _ _).symm
    rw [e3, inner_neg_right, inner_outNormal_vsub_self σ i.2.symm] at h
    have := σ.height_pos i
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · linarith
  · intro b _ hb
    rw [inner_outNormal_vsub σ (fun h => hb (Subtype.ext h.symm)) b.2.symm, mul_zero]
  · simp

/-- **Any three of the five normals are linearly independent.** -/
theorem linearIndependent_outNormal_three {a b c : Fin 5} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : LinearIndependent ℝ ![outNormal σ a, outNormal σ b, outNormal σ c] := by
  obtain ⟨k, hka, hkb, hkc⟩ : ∃ k : Fin 5, k ≠ a ∧ k ≠ b ∧ k ≠ c := by
    revert a b c; decide
  have h := linearIndependent_outNormal_compl σ k
  have hinj : Function.Injective
      (![⟨a, hka.symm⟩, ⟨b, hkb.symm⟩, ⟨c, hkc.symm⟩] : Fin 3 → {x : Fin 5 // x ≠ k}) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff, eq_comm]
  convert h.comp _ hinj using 1
  ext i : 1
  fin_cases i <;> rfl

/-- **The normals weighted by the inverse heights add up to zero**: `Σ_a N_a / h_a = 0`. -/
theorem sum_outNormal_div_height : ∑ a, (σ.height a)⁻¹ • outNormal σ a = 0 := by
  set v := ∑ a, (σ.height a)⁻¹ • outNormal σ a
  have hpair : ∀ j k : Fin 5, ⟪v, σ.points j -ᵥ σ.points k⟫ = 0 := by
    intro j k
    by_cases hjk : j = k
    · subst hjk; simp
    simp only [v, sum_inner, real_inner_smul_left]
    rw [Finset.sum_eq_add_of_mem j k (mem_univ _) (mem_univ _) hjk]
    · have e3 : σ.points j -ᵥ σ.points k = -(σ.points k -ᵥ σ.points j) :=
        (neg_vsub_eq_vsub_rev _ _).symm
      rw [e3, inner_neg_right, inner_outNormal_vsub_self σ (Ne.symm hjk), ← e3,
        inner_outNormal_vsub_self σ hjk]
      have := (σ.height_pos j).ne'
      have := (σ.height_pos k).ne'
      field_simp
      ring
    · intro m _ hm
      rw [inner_outNormal_vsub σ (fun h => hm.1 h.symm) (fun h => hm.2 h.symm), mul_zero]
  -- the edge vectors span `ℝ⁴`
  have htop : vectorSpan ℝ (Set.range σ.points) = ⊤ := by
    have h := σ.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
    rw [← direction_affineSpan, h, AffineSubspace.direction_top]
  rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_range_self 0)] at htop
  have hle : Submodule.span ℝ ((· -ᵥ σ.points 0) '' Set.range σ.points) ≤ (ℝ ∙ v)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hpair j 0
  rw [htop] at hle
  have hv : v ∈ (ℝ ∙ v)ᗮ := hle Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hv
  exact inner_self_eq_zero.mp hv


/-! ## The triple cross product in `ℝ⁴` -/

/-- The **triple cross product** of `a, b, c ∈ ℝ⁴`: the vector with
`⟨a × b × c, d⟩ = det(a, b, c, d)` for the matrix with rows `a, b, c, d`. -/
noncomputable def cross3 (a b c : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2
    ![-a 1 * b 2 * c 3 + a 1 * b 3 * c 2 + a 2 * b 1 * c 3 - a 2 * b 3 * c 1 - a 3 * b 1 * c 2 +
        a 3 * b 2 * c 1,
      a 0 * b 2 * c 3 - a 0 * b 3 * c 2 - a 2 * b 0 * c 3 + a 2 * b 3 * c 0 + a 3 * b 0 * c 2 -
        a 3 * b 2 * c 0,
      -a 0 * b 1 * c 3 + a 0 * b 3 * c 1 + a 1 * b 0 * c 3 - a 1 * b 3 * c 0 - a 3 * b 0 * c 1 +
        a 3 * b 1 * c 0,
      a 0 * b 1 * c 2 - a 0 * b 2 * c 1 - a 1 * b 0 * c 2 + a 1 * b 2 * c 0 + a 2 * b 0 * c 1 -
        a 2 * b 1 * c 0]

/-- `a × b × c` is orthogonal to `a`. -/
lemma inner_cross3_left (a b c : EuclideanSpace ℝ (Fin 4)) : ⟪cross3 a b c, a⟫ = 0 := by
  simp [cross3, PiLp.inner_apply, Fin.sum_univ_four]; ring

/-- `a × b × c` is orthogonal to `b`. -/
lemma inner_cross3_mid (a b c : EuclideanSpace ℝ (Fin 4)) : ⟪cross3 a b c, b⟫ = 0 := by
  simp [cross3, PiLp.inner_apply, Fin.sum_univ_four]; ring

/-- `a × b × c` is orthogonal to `c`. -/
lemma inner_cross3_right (a b c : EuclideanSpace ℝ (Fin 4)) : ⟪cross3 a b c, c⟫ = 0 := by
  simp [cross3, PiLp.inner_apply, Fin.sum_univ_four]; ring

/-- The inner product on `ℝ⁴` in coordinates. -/
lemma inner_eq_coords (x y : EuclideanSpace ℝ (Fin 4)) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial]; ring

/-- `|a × b × c|²` is the Gram determinant of `a, b, c`. -/
lemma inner_cross3_self (a b c : EuclideanSpace ℝ (Fin 4)) :
    ⟪cross3 a b c, cross3 a b c⟫ =
      ⟪a, a⟫ * (⟪b, b⟫ * ⟪c, c⟫ - ⟪b, c⟫ ^ 2) - ⟪a, b⟫ * (⟪a, b⟫ * ⟪c, c⟫ - ⟪b, c⟫ * ⟪a, c⟫) +
        ⟪a, c⟫ * (⟪a, b⟫ * ⟪b, c⟫ - ⟪b, b⟫ * ⟪a, c⟫) := by
  simp only [inner_eq_coords]; simp [cross3]; ring

/-- The expansion of `|z|² (a × b × c)` along `z`. -/
lemma inner_self_smul_cross3 (a b c z : EuclideanSpace ℝ (Fin 4)) :
    ⟪z, z⟫ • cross3 a b c = ⟪cross3 a b c, z⟫ • z + ⟪z, a⟫ • cross3 z b c + ⟪z, b⟫ • cross3 a z c +
      ⟪z, c⟫ • cross3 a b z := by
  simp only [inner_eq_coords]
  ext k; fin_cases k <;> simp [cross3] <;> ring

/-- A vector orthogonal to `a, b, c` is parallel to `a × b × c`. -/
lemma cross3_parallel {a b c z : EuclideanSpace ℝ (Fin 4)} (ha : ⟪z, a⟫ = 0) (hb : ⟪z, b⟫ = 0)
    (hc : ⟪z, c⟫ = 0) : ⟪z, z⟫ • cross3 a b c = ⟪cross3 a b c, z⟫ • z := by
  rw [inner_self_smul_cross3, ha, hb, hc]; simp

/-- The oriented volume `det(n, p₁ - p₀, p₂ - p₀, p₃ - p₀)` of four points against a normal. -/
noncomputable def affDet (n p0 p1 p2 p3 : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  ⟪cross3 n (p1 - p0) (p2 - p0), p3 - p0⟫

/-- Swapping the first two points changes `affDet` only by a sign. -/
lemma abs_affDet_swap01 (n p0 p1 p2 p3 : EuclideanSpace ℝ (Fin 4)) :
    |affDet n p1 p0 p2 p3| = |affDet n p0 p1 p2 p3| := by
  rw [← abs_neg]; congr 1
  simp [affDet, cross3, PiLp.inner_apply, Fin.sum_univ_four]; ring

/-- Swapping the second and third points changes `affDet` only by a sign. -/
lemma abs_affDet_swap12 (n p0 p1 p2 p3 : EuclideanSpace ℝ (Fin 4)) :
    |affDet n p0 p2 p1 p3| = |affDet n p0 p1 p2 p3| := by
  rw [← abs_neg]; congr 1
  simp [affDet, cross3, PiLp.inner_apply, Fin.sum_univ_four]; ring

/-- Swapping the last two points changes `affDet` only by a sign. -/
lemma abs_affDet_swap23 (n p0 p1 p2 p3 : EuclideanSpace ℝ (Fin 4)) :
    |affDet n p0 p1 p3 p2| = |affDet n p0 p1 p2 p3| := by
  rw [← abs_neg]; congr 1
  simp [affDet, cross3, PiLp.inner_apply, Fin.sum_univ_four]; ring

/-- The vertices of the tetrahedron opposite `a`, in increasing order. -/
def nodeTet : Fin 5 → Fin 4 → Fin 5 :=
  ![![1, 2, 3, 4], ![0, 2, 3, 4], ![0, 1, 3, 4], ![0, 1, 2, 4], ![0, 1, 2, 3]]

/-- Six times the volume of the tetrahedron opposite `a`, as `|det(N_a, edges)|`. -/
noncomputable def nodeVol (a : Fin 5) : ℝ :=
  |affDet (outNormal σ a) (σ.points (nodeTet a 0)) (σ.points (nodeTet a 1))
    (σ.points (nodeTet a 2)) (σ.points (nodeTet a 3))|

/-- `nodeVol` at the source of `e`, with the vertices listed as the triangle of `e` and then the
target. -/
lemma nodeVol_src (e : Fin 10) :
    |affDet (outNormal σ (edgeSrc e)) (σ.points (edgeTri e 0)) (σ.points (edgeTri e 1))
      (σ.points (edgeTri e 2)) (σ.points (edgeTgt e))| = nodeVol σ (edgeSrc e) := by
  fin_cases e <;>
    simp only [nodeVol, nodeTet, edgeTri, edgeSrc, edgeTgt, Fin.isValue, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] <;>
    simp only [abs_affDet_swap01, abs_affDet_swap12, abs_affDet_swap23]

/-- `nodeVol` at the target of `e`, with the vertices listed as the triangle of `e` and then the
source. -/
lemma nodeVol_tgt (e : Fin 10) :
    |affDet (outNormal σ (edgeTgt e)) (σ.points (edgeTri e 0)) (σ.points (edgeTri e 1))
      (σ.points (edgeTri e 2)) (σ.points (edgeSrc e))| = nodeVol σ (edgeTgt e) := by
  fin_cases e <;>
    simp only [nodeVol, nodeTet, edgeTri, edgeSrc, edgeTgt, Fin.isValue, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] <;>
    simp only [abs_affDet_swap01, abs_affDet_swap12, abs_affDet_swap23]


/-! ## Areas, heights and the normals -/

/-- Two distinct normals are not parallel: `|⟨N_a, N_b⟩| < 1`. -/
lemma abs_inner_outNormal_lt_one {a b : Fin 5} (h : a ≠ b) :
    |⟪outNormal σ a, outNormal σ b⟫| < 1 := by
  have h1 := σ.abs_inner_vsub_altitudeFoot_div_lt_one h
  have ha := (σ.height_pos a).ne'
  have hb := (σ.height_pos b).ne'
  convert h1 using 2
  rw [outNormal, outNormal, real_inner_smul_left, real_inner_smul_right,
    ← neg_vsub_eq_vsub_rev (σ.points a) (σ.altitudeFoot a),
    ← neg_vsub_eq_vsub_rev (σ.points b) (σ.altitudeFoot b), inner_neg_left, inner_neg_right,
    neg_neg]
  field_simp

/-- For distinct nodes, `1 - ⟨N_a, N_b⟩² > 0`. -/
lemma one_sub_inner_outNormal_sq_pos {a b : Fin 5} (h : a ≠ b) :
    0 < 1 - ⟪outNormal σ a, outNormal σ b⟫ ^ 2 := by
  have h1 := abs_inner_outNormal_lt_one σ h
  have h2 : ⟪outNormal σ a, outNormal σ b⟫ ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg ⟪outNormal σ a, outNormal σ b⟫]
  linarith

/-- `⟨N_a, σ_j - σ_k⟩ = 0` for two vertices `j, k` of the tetrahedron opposite `a`. -/
lemma inner_outNormal_sub {a j k : Fin 5} (hj : j ≠ a) (hk : k ≠ a) :
    ⟪outNormal σ a, σ.points j - σ.points k⟫ = 0 := inner_outNormal_vsub σ hj hk

/-- **The area–height relation.** For the triangle `ijk` shared by the tetrahedra opposite `x` and
`y`, `(1 - ⟨N_x, N_y⟩²) det(N_x, σ_j - σ_i, σ_k - σ_i, σ_y - σ_i)² = |W|² h_y²` with
`W = N_x × (σ_j - σ_i) × (σ_k - σ_i)`. -/
lemma affDet_sq_mul {x y i j k : Fin 5} (hxy : x ≠ y) (hix : i ≠ x) (hjx : j ≠ x) (hkx : k ≠ x)
    (hiy : i ≠ y) (hjy : j ≠ y) (hky : k ≠ y) :
    (1 - ⟪outNormal σ x, outNormal σ y⟫ ^ 2) *
        affDet (outNormal σ x) (σ.points i) (σ.points j) (σ.points k) (σ.points y) ^ 2 =
      ⟪cross3 (outNormal σ x) (σ.points j - σ.points i) (σ.points k - σ.points i),
          cross3 (outNormal σ x) (σ.points j - σ.points i) (σ.points k - σ.points i)⟫ *
        σ.height y ^ 2 := by
  set n := outNormal σ x
  set m := outNormal σ y
  set W := cross3 n (σ.points j - σ.points i) (σ.points k - σ.points i)
  set z := m - ⟪n, m⟫ • n
  have hnn : ⟪n, n⟫ = 1 := inner_outNormal_self σ x
  have hmm : ⟪m, m⟫ = 1 := inner_outNormal_self σ y
  have hza : ⟪z, n⟫ = 0 := by
    simp only [z, inner_sub_left, real_inner_smul_left, hnn, real_inner_comm n m]; ring
  have hzb : ⟪z, σ.points j - σ.points i⟫ = 0 := by
    simp only [z, inner_sub_left, real_inner_smul_left, n, m, inner_outNormal_sub σ hjx hix,
      inner_outNormal_sub σ hjy hiy]; ring
  have hzc : ⟪z, σ.points k - σ.points i⟫ = 0 := by
    simp only [z, inner_sub_left, real_inner_smul_left, n, m, inner_outNormal_sub σ hkx hix,
      inner_outNormal_sub σ hky hiy]; ring
  have hzz : ⟪z, z⟫ = 1 - ⟪n, m⟫ ^ 2 := by
    simp only [z, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hnn, hmm, real_inner_comm n m]; ring
  have hyi : ⟪m, σ.points y - σ.points i⟫ = -σ.height y := by
    have h := inner_outNormal_vsub_self σ hiy
    rw [← neg_sub, inner_neg_right]
    rw [vsub_eq_sub] at h
    rw [h]
  have hzd : ⟪z, σ.points y - σ.points i⟫ = -σ.height y := by
    simp only [z, inner_sub_left, real_inner_smul_left, n, m, inner_outNormal_sub σ hxy.symm hix]
    rw [hyi]; ring
  have hpar := cross3_parallel hza hzb hzc
  have h1 := congrArg (fun v => ⟪v, σ.points y - σ.points i⟫) hpar
  have h2 := congrArg (fun v => ⟪v, W⟫) hpar
  simp only [real_inner_smul_left, hzd] at h1 h2
  rw [real_inner_comm z W] at h2
  have hpos : 0 < ⟪z, z⟫ := by rw [hzz]; exact one_sub_inner_outNormal_sq_pos σ hxy
  rw [← hzz]
  apply mul_left_cancel₀ hpos.ne'
  simp only [affDet]
  rw [show ⟪z, z⟫ * (⟪z, z⟫ * ⟪W, σ.points y - σ.points i⟫ ^ 2) =
    (⟪z, z⟫ * ⟪W, σ.points y - σ.points i⟫) ^ 2 by ring, h1]
  rw [show ⟪z, z⟫ * (⟪W, W⟫ * σ.height y ^ 2) = (⟪z, z⟫ * ⟪W, W⟫) * σ.height y ^ 2 by ring, h2]
  have hC : cross3 n (σ.points j - σ.points i) (σ.points k - σ.points i) = W := rfl
  rw [hC, real_inner_comm z W]
  ring

/-- `|W|²` for `W = N_x × (σ_j - σ_i) × (σ_k - σ_i)` is the Gram determinant of the two edges. -/
lemma inner_cross3_outNormal {x i j k : Fin 5} (hix : i ≠ x) (hjx : j ≠ x) (hkx : k ≠ x) :
    ⟪cross3 (outNormal σ x) (σ.points j - σ.points i) (σ.points k - σ.points i),
        cross3 (outNormal σ x) (σ.points j - σ.points i) (σ.points k - σ.points i)⟫ =
      ⟪σ.points j - σ.points i, σ.points j - σ.points i⟫ *
          ⟪σ.points k - σ.points i, σ.points k - σ.points i⟫ -
        ⟪σ.points j - σ.points i, σ.points k - σ.points i⟫ ^ 2 := by
  rw [inner_cross3_self, inner_outNormal_self, inner_outNormal_sub σ hjx hix,
    inner_outNormal_sub σ hkx hix]
  ring

/-- The distinctness facts of an edge and its triangle. -/
lemma edge_distinct (e : Fin 10) :
    edgeTri e 0 ≠ edgeTri e 1 ∧ edgeTri e 0 ≠ edgeTri e 2 ∧ edgeTri e 1 ≠ edgeTri e 2 ∧
      edgeTri e 0 ≠ edgeSrc e ∧ edgeTri e 1 ≠ edgeSrc e ∧ edgeTri e 2 ≠ edgeSrc e ∧
      edgeTri e 0 ≠ edgeTgt e ∧ edgeTri e 1 ≠ edgeTgt e ∧ edgeTri e 2 ≠ edgeTgt e ∧
      edgeSrc e ≠ edgeTgt e := by
  revert e; decide

/-- `2 A_e` is the length of `W`. -/
lemma two_triArea (e : Fin 10) {x : Fin 5} (hx : x = edgeSrc e ∨ x = edgeTgt e) :
    2 * triArea σ e = √⟪cross3 (outNormal σ x) (σ.points (edgeTri e 1) - σ.points (edgeTri e 0))
        (σ.points (edgeTri e 2) - σ.points (edgeTri e 0)),
      cross3 (outNormal σ x) (σ.points (edgeTri e 1) - σ.points (edgeTri e 0))
        (σ.points (edgeTri e 2) - σ.points (edgeTri e 0))⟫ := by
  obtain ⟨h01, h02, h12, h0s, h1s, h2s, h0t, h1t, h2t, -⟩ := edge_distinct e
  have hℓ : ∀ a b, a ≠ b → simplexLength σ {a, b} = dist (σ.points a) (σ.points b) :=
    fun a b h => simplexLength_pair σ h
  rw [triArea, edgeTriSet, area4_eq _ h01 h02 h12, gram2_eq_inner σ.points hℓ]
  rcases hx with rfl | rfl
  · rw [inner_cross3_outNormal σ h0s h1s h2s]; ring
  · rw [inner_cross3_outNormal σ h0t h1t h2t]; ring

/-- **Area, height and volume** at the source of `e = ab`:
`2 A_e h_b = √(1 - ⟨N_a, N_b⟩²) V_a`, with `V_a = nodeVol σ a`. -/
theorem triArea_mul_height_tgt (e : Fin 10) :
    2 * triArea σ e * σ.height (edgeTgt e) =
      √(1 - ⟪outNormal σ (edgeSrc e), outNormal σ (edgeTgt e)⟫ ^ 2) * nodeVol σ (edgeSrc e) := by
  obtain ⟨-, -, -, h0s, h1s, h2s, h0t, h1t, h2t, hst⟩ := edge_distinct e
  rw [two_triArea σ e (Or.inl rfl), ← nodeVol_src, ← Real.sqrt_sq (σ.height_pos _).le,
    ← Real.sqrt_mul (real_inner_self_nonneg), ← affDet_sq_mul σ hst h0s h1s h2s h0t h1t h2t,
    Real.sqrt_mul (one_sub_inner_outNormal_sq_pos σ hst).le, Real.sqrt_sq_eq_abs]

/-- **Area, height and volume** at the target of `e = ab`:
`2 A_e h_a = √(1 - ⟨N_a, N_b⟩²) V_b`. -/
theorem triArea_mul_height_src (e : Fin 10) :
    2 * triArea σ e * σ.height (edgeSrc e) =
      √(1 - ⟪outNormal σ (edgeSrc e), outNormal σ (edgeTgt e)⟫ ^ 2) * nodeVol σ (edgeTgt e) := by
  obtain ⟨-, -, -, h0s, h1s, h2s, h0t, h1t, h2t, hst⟩ := edge_distinct e
  rw [two_triArea σ e (Or.inr rfl), ← nodeVol_tgt, ← Real.sqrt_sq (σ.height_pos _).le,
    ← Real.sqrt_mul (real_inner_self_nonneg),
    ← affDet_sq_mul σ hst.symm h0t h1t h2t h0s h1s h2s, real_inner_comm,
    Real.sqrt_mul (one_sub_inner_outNormal_sq_pos σ hst).le, Real.sqrt_sq_eq_abs]

end Lightlike.Asymptotics.EPRL
