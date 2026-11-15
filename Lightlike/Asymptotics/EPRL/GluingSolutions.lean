import Lightlike.Asymptotics.EPRL.Gluing
import Lightlike.Spin4.SO4

/-!
# Solutions of the gluing equations

For SU(2) boundary data `g`, a point `X ∈ SU(2)⁵` glues the edge `e = ab` when the frames
`X_a g_ab ε` and `X_b g_ba` have the same Bloch vector; at such points, and only there, the
integrand of the coherent 15j integral has modulus `1` (`norm_cohAmp_eq_one_iff`). This file
solves the gluing equations of all ten edges, given two solutions: if `1` and `Q` glue every
edge, and the matrices `Q₄, Q_a, Q_b` are real linearly independent for distinct `a, b ≠ 4`, then
`X` glues every edge exactly when `X_a = ±X₄` for every `a`, or `X_a = ±X₄ Q₄† Q_a` for every `a`
(`glued_iff_two_classes`). This is the uniqueness argument for the critical points in Barrett,
Dowdall, Fairbairn, Gomes, Hellmann, J. Math. Phys. 50 (2009) 112504, arXiv:0902.1170, section 4.

* SU(2) is the group of unit quaternions (`Lightlike.Spin4.toMat`), and the Bloch vector of `toMat f`
  is the rotated `i`, `rotI f = f i f̄` (`bloch_toMat_eq_iff_rotI`). So gluing of `e = ab` reads
  `p_a k_e p̄_a = p_b k'_e p̄_b` for lifts `p_a` of `X_a` and pure quaternions `k_e, k'_e`
  (`glued_iff_rotI`, `glued_iff_quat`).
* If `p` and `q` both glue `e`, then `p̄_a p_b` and `q̄_a q_b` commute with the same nonzero pure
  quaternion, so `p̄_a p_b = x + y q̄_a q_b` with real `x, y` (`comm_span`, `rel_of_glued`).
* The relations for all pairs `a < b` and the independence of `q₄, q_a, q_b` force
  `p_a = ±p₄` for every `a` or `p_a = ±p₄ q̄₄ q_a` for every `a`; conversely both families glue
  (`quat_two_classes`, `quat_glue_iff`). The independence enters through the independence of
  `1, u, v, u v` for independent `1, u, v` (`indep_mul`).
-/

open Quaternion

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 (bloch)
open scoped Matrix

/-! ## Quaternion algebra -/

/-- Real independence of `1, u, v` in coordinates. -/
lemma indep3_iff {u v : ℍ} :
    LinearIndependent ℝ ![1, u, v] ↔
      ∀ a b c : ℝ, (a : ℍ) + b • u + c • v = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h a b c habc
    have := h ![a, b, c] (by
      simpa [Fin.sum_univ_three, ← Quaternion.coe_mul_eq_smul] using habc)
    exact ⟨this 0, this 1, this 2⟩
  · intro h w hw
    have hw' : ((w 0 : ℝ) : ℍ) + w 1 • u + w 2 • v = 0 := by
      simpa [Fin.sum_univ_three, ← Quaternion.coe_mul_eq_smul] using hw
    obtain ⟨h0, h1, h2⟩ := h _ _ _ hw'
    intro i; fin_cases i <;> assumption

/-- The key identity behind `indep_mul`: left multiplication by `star (c₃ u + c₂)` turns
`c₀ + c₁ u + c₂ v + c₃ u v` into a combination of `1`, `u` and `v` in which `v` has the
coefficient `|c₃ u + c₂|²`. -/
lemma star_mul_comb (u v : ℍ) (c0 c1 c2 c3 : ℝ) :
    star (c3 • u + (c2 : ℍ)) * ((c0 : ℍ) + c1 • u + c2 • v + c3 • (u * v)) =
      ((c3 * c0 * (2 * u.re) + c3 * c1 * normSq u + c2 * c0 : ℝ) : ℍ) + (c2 * c1 - c3 * c0) • u +
        normSq (c3 • u + (c2 : ℍ)) • v := by
  ext <;> simp [normSq_def', sq] <;> ring

/-- If `1, u, v` are real independent quaternions, so are `1, u, v, u v`. -/
lemma indep_mul {u v : ℍ} (h : LinearIndependent ℝ ![1, u, v]) {c0 c1 c2 c3 : ℝ}
    (hc : (c0 : ℍ) + c1 • u + c2 • v + c3 • (u * v) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  have h3 := indep3_iff.mp h
  have hk := star_mul_comb u v c0 c1 c2 c3
  rw [hc, mul_zero] at hk
  obtain ⟨-, -, hn⟩ := h3 _ _ _ hk.symm
  have hs : c3 • u + (c2 : ℍ) = 0 := normSq_eq_zero.mp hn
  obtain ⟨hc2, hc3, -⟩ := h3 c2 c3 0 (by rw [zero_smul, add_zero, add_comm]; exact hs)
  subst hc2 hc3
  obtain ⟨hc0, hc1, -⟩ := h3 c0 c1 0 (by simpa using hc)
  exact ⟨hc0, hc1, rfl, rfl⟩

/-- Replacing `u` by `star u` keeps `1, u, v` independent. -/
lemma indep3_star {u v : ℍ} (h : LinearIndependent ℝ ![1, u, v]) :
    LinearIndependent ℝ ![1, star u, v] := by
  rw [indep3_iff] at h ⊢
  intro a b c habc
  have hu : star u = ((2 * u.re : ℝ) : ℍ) - u := by
    rw [eq_sub_iff_add_eq, add_comm, Quaternion.self_add_star']
  rw [hu] at habc
  obtain ⟨h0, h1, h2⟩ := h (a + b * (2 * u.re)) (-b) c (by
    rw [← habc]; ext <;> simp; ring)
  refine ⟨?_, neg_eq_zero.mp h1, h2⟩
  have hb : b = 0 := neg_eq_zero.mp h1
  subst hb; simpa using h0

/-- A unit quaternion: `|p|² = 1` gives `p p̄ = 1`. -/
lemma mul_star_of_normSq {p : ℍ} (hp : normSq p = 1) : p * star p = 1 := by
  rw [Quaternion.self_mul_star, hp, Quaternion.coe_one]

/-- A unit quaternion: `|p|² = 1` gives `p̄ p = 1`. -/
lemma star_mul_of_normSq {p : ℍ} (hp : normSq p = 1) : star p * p = 1 := by
  rw [Quaternion.star_mul_self, hp, Quaternion.coe_one]

/-- **The commutant of a pure quaternion.** If `k` is pure and `w` commutes with `k`, then
`|k|² w = |k|² Re w + (w · k) k`. -/
lemma comm_pure {k w : ℍ} (hk : k.re = 0) (hw : w * k = k * w) :
    normSq k • w = ((normSq k * w.re : ℝ) : ℍ) +
      (w.imI * k.imI + w.imJ * k.imJ + w.imK * k.imK) • k := by
  have hI := congrArg QuaternionAlgebra.imI hw
  have hJ := congrArg QuaternionAlgebra.imJ hw
  have hK := congrArg QuaternionAlgebra.imK hw
  simp only [Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] at hI hJ hK
  rw [normSq_def']
  ext
  · simp only [Quaternion.re_smul, smul_eq_mul, Quaternion.re_add, Quaternion.re_coe]
    linear_combination (-(w.imI * k.imI + w.imJ * k.imJ + w.imK * k.imK)) * hk
  · simp only [Quaternion.imI_smul, smul_eq_mul, Quaternion.imI_add, Quaternion.imI_coe]
    linear_combination (k.imJ / 2) * hK - (k.imK / 2) * hJ + (k.re * w.imI) * hk
  · simp only [Quaternion.imJ_smul, smul_eq_mul, Quaternion.imJ_add, Quaternion.imJ_coe]
    linear_combination (-k.imI / 2) * hK + (k.imK / 2) * hI + (k.re * w.imJ) * hk
  · simp only [Quaternion.imK_smul, smul_eq_mul, Quaternion.imK_add, Quaternion.imK_coe]
    linear_combination (k.imI / 2) * hJ - (k.imJ / 2) * hI + (k.re * w.imK) * hk

/-- Two quaternions that commute with the same nonzero pure quaternion `k` lie in a common
plane `span(1, k)`: if `v` is not real, `w = x + y v` with `x, y` real. -/
lemma comm_span {k w v : ℍ} (hk : k.re = 0) (hk0 : k ≠ 0) (hw : w * k = k * w)
    (hv : v * k = k * v) (hvr : ∀ r : ℝ, v ≠ r) : ∃ x y : ℝ, w = x + y • v := by
  have hN : normSq k ≠ 0 := normSq_ne_zero.mpr hk0
  have Fw := comm_pure hk hw
  have Fv := comm_pure hk hv
  set tw := w.imI * k.imI + w.imJ * k.imJ + w.imK * k.imK
  set tv := v.imI * k.imI + v.imJ * k.imJ + v.imK * k.imK
  have htv : tv ≠ 0 := by
    intro h0
    apply hvr v.re
    rw [h0, zero_smul, add_zero] at Fv
    have := congrArg (fun z => (normSq k)⁻¹ • z) Fv
    simp only [smul_smul, inv_mul_cancel₀ hN, one_smul] at this
    conv_lhs => rw [this]
    rw [Quaternion.smul_coe, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  have key : ∀ x y z : ℝ, normSq k * x = tw * z → normSq k * y = tv * z → x = tw / tv * y := by
    intro x y z h1 h2
    rw [div_mul_eq_mul_div, eq_div_iff htv]
    apply mul_left_cancel₀ hN
    linear_combination tv * h1 - tw * h2
  refine ⟨w.re - tw / tv * v.re, tw / tv, ?_⟩
  have cI := congrArg QuaternionAlgebra.imI Fw
  have cJ := congrArg QuaternionAlgebra.imJ Fw
  have cK := congrArg QuaternionAlgebra.imK Fw
  have dI := congrArg QuaternionAlgebra.imI Fv
  have dJ := congrArg QuaternionAlgebra.imJ Fv
  have dK := congrArg QuaternionAlgebra.imK Fv
  simp only [Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul, smul_eq_mul,
    Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add, Quaternion.imI_coe,
    Quaternion.imJ_coe, Quaternion.imK_coe, zero_add] at cI cJ cK dI dJ dK
  ext
  · simp only [Quaternion.re_add, Quaternion.re_coe, Quaternion.re_smul, smul_eq_mul]; ring
  · simp only [Quaternion.imI_add, Quaternion.imI_coe, Quaternion.imI_smul, smul_eq_mul, zero_add]
    exact key _ _ _ cI dI
  · simp only [Quaternion.imJ_add, Quaternion.imJ_coe, Quaternion.imJ_smul, smul_eq_mul, zero_add]
    exact key _ _ _ cJ dJ
  · simp only [Quaternion.imK_add, Quaternion.imK_coe, Quaternion.imK_smul, smul_eq_mul, zero_add]
    exact key _ _ _ cK dK

/-! ## The two classes of solutions -/

/-- `p̄ (p x) = x` for a unit quaternion `p`. -/
lemma star_mul_cancel {p : ℍ} (hp : normSq p = 1) (x : ℍ) : star p * (p * x) = x := by
  rw [← mul_assoc, star_mul_of_normSq hp, one_mul]

/-- `p (p̄ x) = x` for a unit quaternion `p`. -/
lemma mul_star_cancel {p : ℍ} (hp : normSq p = 1) (x : ℍ) : p * (star p * x) = x := by
  rw [← mul_assoc, mul_star_of_normSq hp, one_mul]

/-- Each pair `a < b` of nodes is an edge of `K₅`. -/
lemma exists_edge {a b : Fin 5} (h : a < b) : ∃ e, edgeSrc e = a ∧ edgeTgt e = b := by
  revert a b; decide

/-- The coefficients of a product relation: if `1, u, v` are independent and
`(x_a + y_a u)(x_b + y_b v) = x + y u v`, then `y_a x_b = 0` and `x_a y_b = 0`. -/
lemma rel_coeffs {u v : ℍ} (h : LinearIndependent ℝ ![1, u, v]) {xa ya xb yb x y : ℝ}
    (E : ((xa : ℍ) + ya • u) * ((xb : ℍ) + yb • v) = (x : ℍ) + y • (u * v)) :
    ya * xb = 0 ∧ xa * yb = 0 := by
  have hc :
      ((xa * xb - x : ℝ) : ℍ) + (ya * xb) • u + (xa * yb) • v + (ya * yb - y) • (u * v) = 0 := by
    rw [← sub_eq_zero.mpr E]
    ext <;> simp <;> ring
  obtain ⟨-, h1, h2, -⟩ := indep_mul h hc
  exact ⟨h1, h2⟩

/-- Left multiplication by `q̄₄` maps independent `q₄, q_a, q_b` to independent
`1, q̄₄ q_a, q̄₄ q_b`. -/
lemma indep_normalize {q4 qa qb : ℍ} (hq4 : normSq q4 = 1)
    (h : LinearIndependent ℝ ![q4, qa, qb]) :
    LinearIndependent ℝ ![1, star q4 * qa, star q4 * qb] := by
  rw [indep3_iff]
  intro x y z hxyz
  have h' := congrArg (q4 * ·) hxyz
  simp only [mul_add, mul_zero, mul_smul_comm, Quaternion.mul_coe_eq_smul,
    mul_star_cancel hq4] at h'
  have := Fintype.linearIndependent_iff.mp h ![x, y, z] (by simpa [Fin.sum_univ_three] using h')
  exact ⟨this 0, this 1, this 2⟩

/-- A real number with square `1` is `1` or `-1`. -/
lemma sq_eq_one_cases {t : ℝ} (h : t ^ 2 = 1) : t = 1 ∨ t = -1 := by
  have : (t - 1) * (t + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **The two classes, in quaternions.** Let `p, q : Fin 5 → ℍ` be unit quaternions, with
`q₄, q_a, q_b` real independent for distinct `a, b ≠ 4`. If for every pair `a < b`,
`p̄_a p_b = x + y q̄_a q_b` with real `x, y`, then either `p_a = ±p₄` for every `a`, or
`p_a = ±p₄ q̄₄ q_a` for every `a`. -/
theorem quat_two_classes (p q : Fin 5 → ℍ) (hp : ∀ a, normSq (p a) = 1)
    (hq : ∀ a, normSq (q a) = 1)
    (hind : ∀ a b : Fin 5, a ≠ b → a ≠ 4 → b ≠ 4 → LinearIndependent ℝ ![q 4, q a, q b])
    (hrel : ∀ a b : Fin 5, a < b →
      ∃ x y : ℝ, star (p a) * p b = (x : ℍ) + y • (star (q a) * q b)) :
    (∀ a, p a = p 4 ∨ p a = -p 4) ∨
      (∀ a, p a = p 4 * star (q 4) * q a ∨ p a = -(p 4 * star (q 4) * q a)) := by
  set n : Fin 4 → ℍ := fun a => star (q 4) * q a.castSucc with hn_def
  have hne : ∀ a : Fin 4, a.castSucc ≠ (4 : Fin 5) := fun a => (Fin.castSucc_lt_last a).ne
  have hcs : ∀ {a b : Fin 4}, a ≠ b → a.castSucc ≠ b.castSucc := fun h => by
    simpa [Fin.castSucc_inj] using h
  -- the relations to the node 4, starred
  have H4 : ∀ a : Fin 4, ∃ x y : ℝ, star (p 4) * p a.castSucc = (x : ℍ) + y • n a := by
    intro a
    obtain ⟨x, y, h⟩ := hrel a.castSucc 4 (Fin.castSucc_lt_last a)
    refine ⟨x, y, ?_⟩
    have := congrArg star h
    simpa [star_mul, Quaternion.star_coe, hn_def] using this
  choose X Y hXY using H4
  have hnn : ∀ a, normSq (n a) = 1 := fun a => by
    simp [hn_def, Quaternion.normSq_star, hq]
  have hz : ∀ a : Fin 4, normSq ((X a : ℍ) + Y a • n a) = 1 := fun a => by
    rw [← hXY a, map_mul, Quaternion.normSq_star, hp, hp, one_mul]
  -- the cross relations kill the mixed coefficients
  have hmix : ∀ a b : Fin 4, a < b → Y a * X b = 0 ∧ X a * Y b = 0 := by
    intro a b hab
    obtain ⟨x, y, h⟩ := hrel a.castSucc b.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hab)
    have hli := indep3_star (indep_normalize (hq 4)
      (hind _ _ (hcs hab.ne) (hne a) (hne b)))
    refine rel_coeffs hli (x := x) (y := y) ?_
    have e1 : star (p a.castSucc) * p b.castSucc =
        star (star (p 4) * p a.castSucc) * (star (p 4) * p b.castSucc) := by
      rw [star_mul, star_star, mul_assoc, mul_star_cancel (hp 4)]
    have e2 : star (q a.castSucc) * q b.castSucc = star (n a) * n b := by
      simp only [hn_def, star_mul, star_star, mul_assoc, mul_star_cancel (hq 4)]
    rw [e1, hXY a, hXY b, e2] at h
    simpa [star_add, Quaternion.star_smul, Quaternion.star_coe, hn_def] using h
  have hXYz : ∀ a b : Fin 4, a ≠ b → X a * Y b = 0 := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact (hmix a b h).2
    · rw [mul_comm]; exact (hmix b a h).1
  -- reconstruct `p a` from `z_a = p̄₄ p_a`
  have hrec : ∀ a : Fin 4, p a.castSucc = p 4 * ((X a : ℍ) + Y a • n a) := fun a => by
    rw [← hXY a, mul_star_cancel (hp 4)]
  by_cases hY : ∃ a : Fin 4, Y a ≠ 0
  · obtain ⟨a0, ha0⟩ := hY
    have hX : ∀ b, b ≠ a0 → X b = 0 := fun b hb => by
      have := hXYz b a0 hb
      exact (mul_eq_zero.mp this).resolve_right ha0
    have hY1 : ∀ b, b ≠ a0 → Y b ^ 2 = 1 := fun b hb => by
      have := hz b
      rwa [hX b hb, Quaternion.coe_zero, zero_add, Quaternion.normSq_smul, hnn, mul_one] at this
    obtain ⟨b0, hb0⟩ : ∃ b0 : Fin 4, b0 ≠ a0 := ⟨if a0 = 0 then 1 else 0, by
      split_ifs with h0
      · rw [h0]; decide
      · exact fun h => h0 h.symm⟩
    have hXa0 : X a0 = 0 := by
      have h1 := hXYz a0 b0 (Ne.symm hb0)
      have h2 : Y b0 ≠ 0 := by intro h; have := hY1 b0 hb0; rw [h] at this; norm_num at this
      exact (mul_eq_zero.mp h1).resolve_right h2
    have hX0 : ∀ b, X b = 0 := fun b => by
      by_cases hb : b = a0
      · rw [hb]; exact hXa0
      · exact hX b hb
    have hY1' : ∀ b, Y b ^ 2 = 1 := fun b => by
      have := hz b
      rwa [hX0 b, Quaternion.coe_zero, zero_add, Quaternion.normSq_smul, hnn, mul_one] at this
    right
    intro a
    induction a using Fin.lastCases with
    | last =>
      left
      rw [show Fin.last 4 = (4 : Fin 5) from rfl, mul_assoc, star_mul_of_normSq (hq 4), mul_one]
    | cast c =>
      rw [hrec c, hX0 c, Quaternion.coe_zero, zero_add]
      rcases sq_eq_one_cases (hY1' c) with h | h
      · left; rw [h, one_smul, hn_def, mul_assoc]
      · right; rw [h, neg_one_smul, mul_neg, hn_def, mul_assoc]
  · simp only [not_exists, not_not] at hY
    have hX1 : ∀ b, X b ^ 2 = 1 := fun b => by
      have := hz b
      rwa [hY b, zero_smul, add_zero, Quaternion.normSq_coe] at this
    left
    intro a
    induction a using Fin.lastCases with
    | last => left; rfl
    | cast c =>
      rw [hrec c, hY c, zero_smul, add_zero]
      rcases sq_eq_one_cases (hX1 c) with h | h
      · left; rw [h, Quaternion.coe_one, mul_one]
      · right; rw [h, Quaternion.coe_neg, Quaternion.coe_one, mul_neg, mul_one]

/-- On a glued edge, `p̄_a p_b` commutes with the edge quaternion `k`. -/
lemma comm_of_glued {k pa pb : ℍ} (hpa : normSq pa = 1) (hpb : normSq pb = 1)
    (h : pa * k * star pa = pb * k * star pb) : star pa * pb * k = k * (star pa * pb) := by
  have h' := congrArg (fun z => star pa * (z * pb)) h
  simp only [mul_assoc, star_mul_cancel hpa, star_mul_of_normSq hpb, mul_one] at h'
  simp only [mul_assoc]
  exact h'.symm

/-- **The bridge to the reference solution.** If `p` and the reference `q` both glue an edge
whose quaternion `k` is pure and nonzero, and `q̄_a q_b` is not real, then
`p̄_a p_b = x + y q̄_a q_b` with real `x, y`. -/
lemma rel_of_glued {k pa pb qa qb : ℍ} (hk : k.re = 0) (hk0 : k ≠ 0)
    (hpa : normSq pa = 1) (hpb : normSq pb = 1) (hqa : normSq qa = 1) (hqb : normSq qb = 1)
    (hp : pa * k * star pa = pb * k * star pb) (hq : qa * k * star qa = qb * k * star qb)
    (hvr : ∀ r : ℝ, star qa * qb ≠ r) :
    ∃ x y : ℝ, star pa * pb = (x : ℍ) + y • (star qa * qb) :=
  comm_span hk hk0 (comm_of_glued hpa hpb hp) (comm_of_glued hqa hqb hq) hvr

/-- Independent unit quaternions: `q̄_a q_b` is not real for distinct `a, b`. -/
lemma not_real_of_indep (q : Fin 5 → ℍ) (hq : ∀ a, normSq (q a) = 1)
    (hind : ∀ a b : Fin 5, a ≠ b → a ≠ 4 → b ≠ 4 → LinearIndependent ℝ ![q 4, q a, q b])
    {a b : Fin 5} (hab : a ≠ b) (r : ℝ) : star (q a) * q b ≠ r := by
  intro h
  have hb : q b = r • q a := by
    rw [← mul_star_cancel (hq a) (q b), h, Quaternion.mul_coe_eq_smul]
  -- a relation `r q_a - q_b = 0` inside an independent triple
  have key : ∀ c d : Fin 5, c ≠ d → c ≠ 4 → d ≠ 4 →
      ∀ s t u : ℝ, s • q 4 + t • q c + u • q d = 0 → s = 0 ∧ t = 0 ∧ u = 0 := by
    intro c d hcd hc hd s t u h0
    have := Fintype.linearIndependent_iff.mp (hind c d hcd hc hd) ![s, t, u]
      (by simpa [Fin.sum_univ_three] using h0)
    exact ⟨this 0, this 1, this 2⟩
  by_cases ha4 : a = 4
  · subst ha4
    obtain ⟨c, hc4, hcb⟩ : ∃ c : Fin 5, c ≠ 4 ∧ c ≠ b := by
      by_cases hb0 : b = 0
      · exact ⟨1, by decide, by rw [hb0]; decide⟩
      · exact ⟨0, by decide, Ne.symm hb0⟩
    have := key b c (Ne.symm hcb) (Ne.symm hab) hc4 r (-1) 0 (by rw [hb]; simp)
    norm_num at this
  by_cases hb4 : b = 4
  · subst hb4
    obtain ⟨c, hc4, hca⟩ : ∃ c : Fin 5, c ≠ 4 ∧ c ≠ a := by
      by_cases ha0 : a = 0
      · exact ⟨1, by decide, by rw [ha0]; decide⟩
      · exact ⟨0, by decide, Ne.symm ha0⟩
    have := key a c (Ne.symm hca) ha4 hc4 (-1) r 0 (by rw [hb]; simp)
    norm_num at this
  have := key a b hab ha4 hb4 0 r (-1) (by rw [hb]; simp)
  norm_num at this

/-- **Gluing solutions, in quaternions.** Let every edge carry a pure nonzero quaternion `k_e`,
and let the unit quaternions `q` glue every edge (`q_a k_e q̄_a = q_b k_e q̄_b` for `e = ab`), with
`q₄, q_a, q_b` independent. Then unit quaternions `p` glue every edge exactly when `p_a = ±p₄` for
every `a`, or `p_a = ±p₄ q̄₄ q_a` for every `a`. -/
theorem quat_glue_iff (k : Fin 10 → ℍ) (hk : ∀ e, (k e).re = 0) (hk0 : ∀ e, k e ≠ 0)
    (q : Fin 5 → ℍ) (hq : ∀ a, normSq (q a) = 1)
    (hQ : ∀ e, q (edgeSrc e) * k e * star (q (edgeSrc e)) =
      q (edgeTgt e) * k e * star (q (edgeTgt e)))
    (hind : ∀ a b : Fin 5, a ≠ b → a ≠ 4 → b ≠ 4 → LinearIndependent ℝ ![q 4, q a, q b])
    (p : Fin 5 → ℍ) (hp : ∀ a, normSq (p a) = 1) :
    (∀ e, p (edgeSrc e) * k e * star (p (edgeSrc e)) =
        p (edgeTgt e) * k e * star (p (edgeTgt e))) ↔
      (∀ a, p a = p 4 ∨ p a = -p 4) ∨
        (∀ a, p a = p 4 * star (q 4) * q a ∨ p a = -(p 4 * star (q 4) * q a)) := by
  constructor
  · intro hP
    refine quat_two_classes p q hp hq hind fun a b hab => ?_
    obtain ⟨e, rfl, rfl⟩ := exists_edge hab
    exact rel_of_glued (hk e) (hk0 e) (hp _) (hp _) (hq _) (hq _) (hP e) (hQ e)
      (not_real_of_indep q hq hind hab.ne)
  · rintro (h | h) e
    · have hc : ∀ a, p a * k e * star (p a) = p 4 * k e * star (p 4) := fun a => by
        rcases h a with h' | h'
        · rw [h']
        · rw [h']; simp [star_neg]
      rw [hc (edgeSrc e), hc (edgeTgt e)]
    · have hc : ∀ a, p a * k e * star (p a) =
          p 4 * star (q 4) * (q a * k e * star (q a)) * q 4 * star (p 4) := fun a => by
        rcases h a with h' | h' <;> rw [h'] <;> simp [star_neg, star_mul, mul_assoc]
      rw [hc (edgeSrc e), hc (edgeTgt e), hQ e]


/-! ## SU(2) frames as unit quaternions -/

/-- The quaternion `i`; `toMat i = diag(i, -i)`. -/
def quatI : ℍ := ⟨0, 1, 0, 0⟩

/-- The quaternion `-j`; `toMat (-j) = ε`. -/
def quatEps : ℍ := ⟨0, 0, -1, 0⟩

/-- The quaternion `ε = -j` is the matrix `epsMat`. -/
lemma toMat_quatEps : Lightlike.Spin4.toMat quatEps = epsMat := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [quatEps, Lightlike.Spin4.toMat_apply, Lightlike.Spin4.quatMat, epsMat]

/-- `i` is a unit quaternion. -/
lemma normSq_quatI : normSq quatI = 1 := by simp [quatI, normSq_def']

/-- `ε` is a unit quaternion. -/
lemma normSq_quatEps : normSq quatEps = 1 := by simp [quatEps, normSq_def']

/-- **The Bloch vector as a rotated `i`.** `f i f̄ = ν₂ i + ν₁ j + ν₀ k` for the Bloch vector `ν` of
`toMat f`. -/
lemma mul_quatI_mul_star (f : ℍ) :
    f * quatI * star f =
      ⟨0, bloch (Lightlike.Spin4.toMat f) 2, bloch (Lightlike.Spin4.toMat f) 1, bloch (Lightlike.Spin4.toMat f) 0⟩ := by
  ext <;> simp [quatI, Lightlike.Spin4.bloch, Lightlike.Spin4.toMat_apply, Lightlike.Spin4.quatMat,
    Complex.normSq_apply] <;> ring

/-- Two frames have the same Bloch vector exactly when they rotate `i` to the same quaternion. -/
lemma bloch_toMat_eq_iff (f g : ℍ) :
    bloch (Lightlike.Spin4.toMat f) = bloch (Lightlike.Spin4.toMat g) ↔
      f * quatI * star f = g * quatI * star g := by
  rw [mul_quatI_mul_star, mul_quatI_mul_star]
  constructor
  · intro h; rw [h]
  · intro h
    have h1 := congrArg QuaternionAlgebra.imI h
    have h2 := congrArg QuaternionAlgebra.imJ h
    have h3 := congrArg QuaternionAlgebra.imK h
    ext k; fin_cases k
    · exact h3
    · exact h2
    · exact h1

/-- The **rotated `i`** of a quaternion: `rotI f = f i f̄`. For a unit quaternion `f` it is
`ν₂ i + ν₁ j + ν₀ k` with `ν` the Bloch vector of `toMat f`. -/
def rotI (f : ℍ) : ℍ := f * quatI * star f

/-- Left multiplication by `p` conjugates the rotated `i` by `p`. -/
lemma rotI_mul (p f : ℍ) : rotI (p * f) = p * rotI f * star p := by
  simp only [rotI, star_mul, mul_assoc]

/-- The rotated `i` of `ε = -j` is `-i`. -/
lemma rotI_quatEps : rotI quatEps = -quatI := by
  ext <;> simp [rotI, quatEps, quatI]

/-- Right multiplication by `ε` reverses the rotated `i`. -/
lemma rotI_mul_quatEps (f : ℍ) : rotI (f * quatEps) = -rotI f := by
  rw [rotI_mul, rotI_quatEps, mul_neg, neg_mul, rotI]

/-- Two frames have the same Bloch vector exactly when they have the same rotated `i`. -/
lemma bloch_toMat_eq_iff_rotI (f g : ℍ) :
    bloch (Lightlike.Spin4.toMat f) = bloch (Lightlike.Spin4.toMat g) ↔ rotI f = rotI g :=
  bloch_toMat_eq_iff f g

/-- **Gluing in quaternions, with any lifts.** Let `p_a` lift `X_a` and `G e i` lift `g e i`.
The edge `e = ab` is glued at `X` exactly when `p_a rotI(G_ab ε) p̄_a = p_b rotI(G_ba) p̄_b`. -/
lemma glued_iff_rotI {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (p : Fin 5 → ℍ)
    (hp : ∀ a, Lightlike.Spin4.toMat (p a) = (X a : Matrix (Fin 2) (Fin 2) ℂ)) (G : Fin 10 → Fin 2 → ℍ)
    (hG : ∀ e i, Lightlike.Spin4.toMat (G e i) = g e i) (e : Fin 10) :
    bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
        bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ) ↔
      p (edgeSrc e) * rotI (G e 0 * quatEps) * star (p (edgeSrc e)) =
        p (edgeTgt e) * rotI (G e 1) * star (p (edgeTgt e)) := by
  have hs : (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      Lightlike.Spin4.toMat (p (edgeSrc e) * G e 0 * quatEps) := by
    rw [map_mul, map_mul, hp, hG, toMat_quatEps]; rfl
  have ht : (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      Lightlike.Spin4.toMat (p (edgeTgt e) * G e 1) := by
    rw [map_mul, hp, hG]; rfl
  rw [hs, ht, bloch_toMat_eq_iff_rotI, mul_assoc, rotI_mul (p (edgeSrc e)),
    rotI_mul (p (edgeTgt e))]

/-- A unit quaternion lifting an element of SU(2). -/
noncomputable def quatLift (g : SU2) : ℍ := ((Lightlike.Spin4.exists_toMat_eq g).choose : ℍ)

/-- The quaternion `quatLift g` lifts `g`. -/
lemma toMat_quatLift (g : SU2) :
    Lightlike.Spin4.toMat (quatLift g) = (g : Matrix (Fin 2) (Fin 2) ℂ) :=
  (Lightlike.Spin4.exists_toMat_eq g).choose_spec

/-- The quaternion `quatLift g` is a unit quaternion. -/
lemma normSq_quatLift (g : SU2) : normSq (quatLift g) = 1 := by
  have h := Unitary.star_mul_self_of_mem (Lightlike.Spin4.exists_toMat_eq g).choose.2
  rw [Quaternion.star_mul_self] at h
  exact Quaternion.coe_injective (h.trans Quaternion.coe_one.symm)

/-- The rotated `i` of the edge `e` at its source, for SU(2) boundary data. -/
noncomputable def edgeQuat {g : BdryData} (hg : IsSU2Data g) (e : Fin 10) : ℍ :=
  quatLift ⟨g e 0, hg e 0⟩ * quatEps * quatI * star (quatLift ⟨g e 0, hg e 0⟩ * quatEps)

/-- The rotated `i` of the edge `e` at its target. -/
noncomputable def edgeQuat' {g : BdryData} (hg : IsSU2Data g) (e : Fin 10) : ℍ :=
  quatLift ⟨g e 1, hg e 1⟩ * quatI * star (quatLift ⟨g e 1, hg e 1⟩)

/-- **Gluing in quaternions.** With unit quaternions `p_a` lifting `X_a`, the edge `e = ab` is
glued at `X` exactly when `p_a k_e p̄_a = p_b k'_e p̄_b`. -/
lemma glued_iff_quat {g : BdryData} (hg : IsSU2Data g) (X : Fin 5 → SU2) (p : Fin 5 → ℍ)
    (hp : ∀ a, Lightlike.Spin4.toMat (p a) = (X a : Matrix (Fin 2) (Fin 2) ℂ)) (e : Fin 10) :
    bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
        bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ) ↔
      p (edgeSrc e) * edgeQuat hg e * star (p (edgeSrc e)) =
        p (edgeTgt e) * edgeQuat' hg e * star (p (edgeTgt e)) := by
  have hs : (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      Lightlike.Spin4.toMat (p (edgeSrc e) * quatLift ⟨g e 0, hg e 0⟩ * quatEps) := by
    rw [map_mul, map_mul, hp, toMat_quatLift, toMat_quatEps]; rfl
  have ht : (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
      Lightlike.Spin4.toMat (p (edgeTgt e) * quatLift ⟨g e 1, hg e 1⟩) := by
    rw [map_mul, hp, toMat_quatLift]; rfl
  rw [hs, ht, bloch_toMat_eq_iff]
  simp only [edgeQuat, edgeQuat', star_mul, mul_assoc]

/-- A conjugate `f i f̄` of `i` is pure. -/
lemma re_mul_quatI_mul_star (f : ℍ) : (f * quatI * star f).re = 0 := by
  rw [mul_quatI_mul_star]

/-- A conjugate `f i f̄` of `i` by a unit quaternion is nonzero. -/
lemma mul_quatI_mul_star_ne_zero {f : ℍ} (hf : normSq f = 1) : f * quatI * star f ≠ 0 := by
  rw [← normSq_ne_zero, map_mul, map_mul, Quaternion.normSq_star, hf, normSq_quatI]; norm_num

/-- The product `quatLift g ε` is a unit quaternion. -/
lemma normSq_lift_eps (g : SU2) : normSq (quatLift g * quatEps) = 1 := by
  rw [map_mul, normSq_quatLift, normSq_quatEps, one_mul]

/-- **The gluing solutions of SU(2) boundary data with two reference solutions.** Let the data
`g` be glued at `X = 1` and at `X = Q` on every edge, with `Q₄, Q_a, Q_b` real independent for
distinct `a, b ≠ 4`. Then `X` glues every edge exactly when `X_a = ±X₄` for every `a`, or
`X_a = ±X₄ Q₄† Q_a` for every `a`. -/
theorem glued_iff_two_classes {g : BdryData} (hg : IsSU2Data g) (Q : Fin 5 → SU2)
    (h1 : ∀ e, bloch (frameSrc hg 1 e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg 1 e : Matrix (Fin 2) (Fin 2) ℂ))
    (hQ : ∀ e, bloch (frameSrc hg Q e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt hg Q e : Matrix (Fin 2) (Fin 2) ℂ))
    (hind : ∀ a b : Fin 5, a ≠ b → a ≠ 4 → b ≠ 4 →
      LinearIndependent ℝ ![(Q 4 : Matrix (Fin 2) (Fin 2) ℂ), Q a, Q b])
    (X : Fin 5 → SU2) :
    (∀ e, bloch (frameSrc hg X e : Matrix (Fin 2) (Fin 2) ℂ) =
        bloch (frameTgt hg X e : Matrix (Fin 2) (Fin 2) ℂ)) ↔
      (∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = X 4 ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) = -(X 4 : Matrix (Fin 2) (Fin 2) ℂ)) ∨
        (∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) =
            (X 4 : Matrix (Fin 2) (Fin 2) ℂ) * (Q 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Q a ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) =
            -((X 4 : Matrix (Fin 2) (Fin 2) ℂ) * (Q 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Q a)) := by
  set p : Fin 5 → ℍ := fun a => quatLift (X a)
  set q : Fin 5 → ℍ := fun a => quatLift (Q a)
  have hp : ∀ a, Lightlike.Spin4.toMat (p a) = (X a : Matrix (Fin 2) (Fin 2) ℂ) := fun a =>
    toMat_quatLift _
  have hq : ∀ a, Lightlike.Spin4.toMat (q a) = (Q a : Matrix (Fin 2) (Fin 2) ℂ) := fun a =>
    toMat_quatLift _
  have h1q : ∀ a, Lightlike.Spin4.toMat ((fun _ => (1 : ℍ)) a) =
      ((1 : Fin 5 → SU2) a : Matrix (Fin 2) (Fin 2) ℂ) := fun a => by simp
  -- the reference solution `1` identifies the two edge quaternions
  have hk : ∀ e, edgeQuat hg e = edgeQuat' hg e := fun e => by
    have := (glued_iff_quat hg 1 _ h1q e).mp (h1 e)
    simpa using this
  simp only [glued_iff_quat hg X p hp, glued_iff_quat hg Q q hq, ← hk] at hQ ⊢
  have hind' : ∀ a b : Fin 5, a ≠ b → a ≠ 4 → b ≠ 4 → LinearIndependent ℝ ![q 4, q a, q b] := by
    intro a b hab ha hb
    refine LinearIndependent.of_comp Lightlike.Spin4.toMat.toLinearMap ?_
    convert hind a b hab ha hb using 1
    ext i : 1; fin_cases i <;> simp [hq]
  have e1 : ∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = X 4 ↔ p a = p 4 := fun a => by
    rw [← hp a, ← hp 4]; exact Lightlike.Spin4.toMat_injective.eq_iff
  have e2 : ∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = -(X 4 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      p a = -p 4 := fun a => by
    rw [← hp a, ← hp 4, ← map_neg]; exact Lightlike.Spin4.toMat_injective.eq_iff
  have e3 : ∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) =
      (X 4 : Matrix (Fin 2) (Fin 2) ℂ) * (Q 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Q a ↔
      p a = p 4 * star (q 4) * q a := fun a => by
    rw [← hp a, ← hp 4, ← hq 4, ← hq a, ← Lightlike.Spin4.toMat_star, ← map_mul, ← map_mul]
    exact Lightlike.Spin4.toMat_injective.eq_iff
  have e4 : ∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) =
      -((X 4 : Matrix (Fin 2) (Fin 2) ℂ) * (Q 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * Q a) ↔
      p a = -(p 4 * star (q 4) * q a) := fun a => by
    rw [← hp a, ← hp 4, ← hq 4, ← hq a, ← Lightlike.Spin4.toMat_star, ← map_mul, ← map_mul, ← map_neg]
    exact Lightlike.Spin4.toMat_injective.eq_iff
  simp only [e1, e2, e3, e4]
  exact quat_glue_iff (edgeQuat hg) (fun e => re_mul_quatI_mul_star _)
    (fun e => mul_quatI_mul_star_ne_zero (normSq_lift_eps _)) q (fun a => normSq_quatLift _) hQ
    hind' p (fun a => normSq_quatLift _)

end Lightlike.Asymptotics.EPRL
