import Lightlike.Regge.Lorentzian.Schlaefli
import Lightlike.Regge.D4.ReggeEquations

/-!
# The Lorentzian Regge equations

The Lorentzian Regge action `S = Σ_{interior} A_t ε_t + Σ_{boundary} A_t (π Z_t − Σ θ)`
(`Lightlike/Regge/Lorentzian/Complex.lean`, ADP eq. 3.1) depends on the signed squared edge lengths `L`
through the areas `A_t = √|triHL| / 4`, through the causal types `Z_t` and through Sorkin's complex
dihedral angles. Along a line of lengths `L + τ v` with no null triangle the causal types are
locally constant, and by the Lorentzian Schläfli identity (`Lightlike/Regge/Lorentzian/Schlaefli.lean`) the
variation of the angles drops out 4-simplex by 4-simplex. Only the areas vary:

  `dS = Σ_{interior} dA_t ε_t + Σ_{boundary} dA_t (π Z_t − Σ θ)`.

In terms of the squared lengths this is the Lorentzian Regge equation (Sorkin 1975; ADP eq. 3.2):
for every interior edge `e`, `∂S/∂L_e = Σ_{t ∋ e} (∂A_t/∂L_e) ε_t`, with
`∂A_t/∂L_e = ± (L_f + L_g − L_e) / (4 √|triHL|)` for the other two edges `f, g` of `t`, the sign
being that of `triHL` (`+` at spacelike, `−` at timelike triangles). The equation is complex; at a
regular light-cone structure the imaginary parts of the deficits vanish. Flat Minkowski space is a
solution (`Lightlike/Regge/Lorentzian/FlatSolution.lean`).

As in the Euclidean case (`Lightlike/Regge/D4/ReggeEquations.lean`) the action is varied in every direction
of the edge data, here the signed squared lengths, which are the natural variables of Lorentzian
Regge calculus: they change sign across the light cone, the lengths do not.

## Main results

* `LorLengthsNondeg4 K L`: no null triangle and no null tetrahedron, and every 4-simplex
  Lorentzian (`gram4L < 0`), in every labelling.
* `triSign L t`: the sign of `triHL L t`.
* `lorAreaPartial L t e`: the partial derivative `∂A_t/∂L_e`; `lorAreaDeriv L v t`: the
  derivative of `A_t` along `L + τ v`.
* `lorReggePartial K L e = Σ_{t ∋ e} ∂A_t/∂L_e · (ε_t or π Z_t − Σ θ)`.

* `lorReggeAction_eq_sum_simps`: the action regrouped 4-simplex by 4-simplex.
* `hasDerivAt_lorArea`: the derivative of the area at a non-null triangle, for both causal types.
* `hasDerivAt_lorSimpSum4`: one 4-simplex's contribution varies only through its areas (Schläfli).
* `hasDerivAt_lorReggeAction`, `hasDerivAt_lorReggeAction_grad` (**the Lorentzian Regge
  equations**): the derivative of the action along every line of squared lengths, as a sum over
  triangles and as `Σ_e v_e ∂S/∂L_e`.
* `lorReggeAction_stationary_iff`: with the boundary lengths fixed, the action is stationary
  exactly when `Σ_{t ∋ e} (∂A_t/∂L_e) ε_t = 0` at every interior edge.
-/

open Real Finset Filter Topology

namespace Lightlike.ReggeLor

open Lightlike.FourD (Complex4)
open Lightlike.FourD.Complex4 (mem_faces mem_star card_of_mem_faces)
open Lightlike.Regge (hasDerivAt_line)
open Lightlike.Regge4 (lineL lineL_zero exists_label4 exists_label5 mem_tris_of_subset mem_tets_of_subset
  bdryEdges4 intEdges4 intTris4 bdryTris4 disjoint_intTris4_bdryTris4 intTris4_union_bdryTris4
  filter_bdryTris4_eq_empty)

variable {V : Type*} [DecidableEq V]

/-! ## The action, 4-simplex by 4-simplex -/

/-- Exchanging the sum over triangles with the sum over 4-simplices, for complex values: the pairs
(triangle, 4-simplex containing it) are the pairs (4-simplex, one of its ten triangles). -/
theorem sum_tris_star_complex (K : Complex4 V) (F : Finset V → Finset V → ℂ) :
    ∑ t ∈ K.tris, ∑ σ ∈ K.star t, F t σ = ∑ σ ∈ K.simps, ∑ t ∈ σ.powersetCard 3, F t σ := by
  apply sum_comm'
  intro t σ
  simp only [mem_star, mem_powersetCard]
  constructor
  · rintro ⟨ht, hσ, hs⟩
    exact ⟨⟨hs, card_of_mem_faces ht⟩, hσ⟩
  · rintro ⟨⟨hs, h3⟩, hσ⟩
    exact ⟨mem_faces.mpr ⟨σ, hσ, hs, h3⟩, hσ, hs⟩

/-- **The Lorentzian curvature sum, 4-simplex by 4-simplex.** For any real weights `w` on
triangles, `Σ_{int} w_t ε_t + Σ_{bdry} w_t (π Z_t − Σ θ)` is
`2π Σ_{int} w_t Z_t + π Σ_{bdry} w_t Z_t − Σ_σ Σ_{t ⊂ σ} w_t θ_σ(t)`. -/
theorem sum_lorCurvature_eq (K : Complex4 V) (L w : Finset V → ℝ) :
    ∑ t ∈ intTris4 K, (w t : ℂ) * lorDeficit K L t +
        ∑ t ∈ bdryTris4 K, (w t : ℂ) * lorBdryAngle K L t =
      ∑ t ∈ intTris4 K, 2 * π * ((w t : ℂ) * causalZ L t) +
        ∑ t ∈ bdryTris4 K, π * ((w t : ℂ) * causalZ L t) -
        ∑ σ ∈ K.simps, ∑ t ∈ σ.powersetCard 3, (w t : ℂ) * lorDihedralAt L σ t := by
  have hsplit : ∑ t ∈ intTris4 K, (w t : ℂ) * lorAngleSum K L t +
      ∑ t ∈ bdryTris4 K, (w t : ℂ) * lorAngleSum K L t =
        ∑ t ∈ K.tris, (w t : ℂ) * lorAngleSum K L t := by
    rw [← sum_union (disjoint_intTris4_bdryTris4 K), intTris4_union_bdryTris4]
  have hswap : ∑ t ∈ K.tris, (w t : ℂ) * lorAngleSum K L t =
      ∑ σ ∈ K.simps, ∑ t ∈ σ.powersetCard 3, (w t : ℂ) * lorDihedralAt L σ t := by
    simp only [lorAngleSum, mul_sum]
    exact sum_tris_star_complex K fun t σ => (w t : ℂ) * lorDihedralAt L σ t
  have e1 : ∀ t, (w t : ℂ) * (2 * π * causalZ L t) = 2 * π * ((w t : ℂ) * causalZ L t) :=
    fun t => by ring
  have e2 : ∀ t, (w t : ℂ) * (π * causalZ L t) = π * ((w t : ℂ) * causalZ L t) :=
    fun t => by ring
  simp only [lorDeficit, lorBdryAngle, mul_sub, sum_sub_distrib, e1, e2]
  rw [← hswap, ← hsplit]
  ring

/-- The Lorentzian Regge action rewritten 4-simplex by 4-simplex. -/
theorem lorReggeAction_eq_sum_simps (K : Complex4 V) (L : Finset V → ℝ) :
    lorReggeAction K L = ∑ t ∈ intTris4 K, 2 * π * ((lorArea L t : ℂ) * causalZ L t) +
      ∑ t ∈ bdryTris4 K, π * ((lorArea L t : ℂ) * causalZ L t) -
      ∑ σ ∈ K.simps, ∑ t ∈ σ.powersetCard 3, (lorArea L t : ℂ) * lorDihedralAt L σ t :=
  sum_lorCurvature_eq K L (lorArea L)

/-! ## Non-degenerate signed squared lengths -/

/-- **Non-degenerate Lorentzian lengths** on `K`: no triangle and no tetrahedron is null, and
every 4-simplex is Lorentzian (`gram4L < 0`), in every labelling of its vertices. -/
structure LorLengthsNondeg4 (K : Complex4 V) (L : Finset V → ℝ) : Prop where
  /-- No null triangles. -/
  tri : ∀ t ∈ K.tris, triHL L t ≠ 0
  /-- No null tetrahedra. -/
  tet : ∀ p q r s : V, ({p, q, r, s} : Finset V) ∈ K.tets → gram3L L p q r s ≠ 0
  /-- Lorentzian 4-simplices. -/
  simp4 : ∀ p q r s u : V, ({p, q, r, s, u} : Finset V) ∈ K.simps → gram4L L p q r s u < 0

/-- `gram2L ≠ 0` for the triangles of `K`. -/
theorem LorLengthsNondeg4.gram2L_ne {K : Complex4 V} {L : Finset V → ℝ}
    (hK : LorLengthsNondeg4 K L) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ({a, b, c} : Finset V) ∈ K.tris) : gram2L L a b c ≠ 0 := by
  have := hK.tri _ ht
  rw [triHL_eq L hab hac hbc] at this
  exact right_ne_zero_of_mul this

/-- **One condition for all labellings**: non-degenerate Lorentzian lengths make every 4-simplex
non-degenerate and Lorentzian (`LorNondeg4`) in every labelling. -/
theorem LorLengthsNondeg4.lorNondeg4 {K : Complex4 V} {L : Finset V → ℝ}
    (hK : LorLengthsNondeg4 K L) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s) (hru : r ≠ u)
    (hsu : s ≠ u) (hσ : ({p, q, r, s, u} : Finset V) ∈ K.simps) : LorNondeg4 L p q r s u := by
  have T : ∀ {a b c : V}, a ∈ ({p, q, r, s, u} : Finset V) → b ∈ ({p, q, r, s, u} : Finset V) →
      c ∈ ({p, q, r, s, u} : Finset V) → a ≠ b → a ≠ c → b ≠ c → gram2L L a b c ≠ 0 :=
    fun ha hb hc hab hac hbc => hK.gram2L_ne hab hac hbc
      (mem_tris_of_subset hσ hab hac hbc (by simp [insert_subset_iff, ha, hb, hc]))
  have F : ∀ {a b c d : V}, a ∈ ({p, q, r, s, u} : Finset V) → b ∈ ({p, q, r, s, u} : Finset V) →
      c ∈ ({p, q, r, s, u} : Finset V) → d ∈ ({p, q, r, s, u} : Finset V) → a ≠ b → a ≠ c →
      a ≠ d → b ≠ c → b ≠ d → c ≠ d → gram3L L a b c d ≠ 0 :=
    fun ha hb hc hd hab hac had hbc hbd hcd => hK.tet _ _ _ _
      (mem_tets_of_subset hσ hab hac had hbc hbd hcd
        (by simp [insert_subset_iff, ha, hb, hc, hd]))
  exact ⟨T (by simp) (by simp) (by simp) hpq hpr hqr, T (by simp) (by simp) (by simp) hpq hps hqs,
    T (by simp) (by simp) (by simp) hpq hpu hqu, T (by simp) (by simp) (by simp) hpr hps hrs,
    T (by simp) (by simp) (by simp) hpr hpu hru, T (by simp) (by simp) (by simp) hps hpu hsu,
    T (by simp) (by simp) (by simp) hqr hqs hrs, T (by simp) (by simp) (by simp) hqr hqu hru,
    T (by simp) (by simp) (by simp) hqs hqu hsu, T (by simp) (by simp) (by simp) hrs hru hsu,
    F (by simp) (by simp) (by simp) (by simp) hpq hpr hps hqr hqs hrs,
    F (by simp) (by simp) (by simp) (by simp) hpq hpr hpu hqr hqu hru,
    F (by simp) (by simp) (by simp) (by simp) hpq hps hpu hqs hqu hsu,
    F (by simp) (by simp) (by simp) (by simp) hpr hps hpu hrs hru hsu,
    F (by simp) (by simp) (by simp) (by simp) hqr hqs hqu hrs hru hsu, hK.simp4 _ _ _ _ _ hσ⟩

/-! ## Areas along a line of squared lengths -/

omit [DecidableEq V] in
/-- The derivative of `triHL` along `L + τ v` at `τ = 0`: `2 (Σ L_e)(Σ v_e) − 2 Σ 2 L_e v_e`, sums
over the three edges. -/
theorem hasDerivAt_triHL (L v : Finset V → ℝ) (t : Finset V) :
    HasDerivAt (fun τ => triHL (lineL L v τ) t)
      (2 * (∑ e ∈ t.powersetCard 2, L e) * (∑ e ∈ t.powersetCard 2, v e) -
        2 * ∑ e ∈ t.powersetCard 2, 2 * L e * v e) 0 := by
  have h1 : HasDerivAt (fun τ => ∑ e ∈ t.powersetCard 2, (L e + τ * v e))
      (∑ e ∈ t.powersetCard 2, v e) 0 :=
    HasDerivAt.fun_sum fun e _ => hasDerivAt_line (L e) (v e)
  have h2 : HasDerivAt (fun τ => ∑ e ∈ t.powersetCard 2, (L e + τ * v e) ^ 2)
      (∑ e ∈ t.powersetCard 2, 2 * L e * v e) 0 := by
    refine (HasDerivAt.fun_sum fun e _ => (hasDerivAt_line (L e) (v e)).pow 2).congr_deriv ?_
    refine sum_congr rfl fun e _ => ?_
    simp
  have := (h1.pow 2).sub (h2.const_mul 2)
  simp only [triHL, lineL]
  convert this using 1
  simp

/-- The sign of `triHL L t`: `1` at a spacelike triangle, `−1` otherwise. -/
noncomputable def triSign (L : Finset V → ℝ) (t : Finset V) : ℝ :=
  if 0 < triHL L t then 1 else -1

/-- The partial derivative `∂A_t/∂L_e = ± (Σ_{f ⊂ t} L_f − 2 L_e) / (4 √|triHL|)` of the area of
the triangle `t` with respect to the signed squared length of its edge `e`, with the sign of
`triHL`; for the other two edges `f, g` of `t` this is `± (L_f + L_g − L_e) / (16 A_t)`. -/
noncomputable def lorAreaPartial (L : Finset V → ℝ) (t e : Finset V) : ℝ :=
  triSign L t * (∑ f ∈ t.powersetCard 2, L f - 2 * L e) / (4 * √|triHL L t|)

/-- The derivative of the area of `t` along `L + τ v`: `dA_t = Σ_{e ⊂ t} v_e ∂A_t/∂L_e`. -/
noncomputable def lorAreaDeriv (L v : Finset V → ℝ) (t : Finset V) : ℝ :=
  ∑ e ∈ t.powersetCard 2, v e * lorAreaPartial L t e

omit [DecidableEq V] in
/-- **The areas vary as `lorAreaDeriv`** along a line of squared lengths, at every non-null
triangle (spacelike or timelike). -/
theorem hasDerivAt_lorArea (L v : Finset V → ℝ) {t : Finset V} (h : triHL L t ≠ 0) :
    HasDerivAt (fun τ => lorArea (lineL L v τ) t) (lorAreaDeriv L v t) 0 := by
  have hH := hasDerivAt_triHL L v t
  have h0 : triHL (lineL L v 0) t = triHL L t := by rw [lineL_zero]
  have hAbs : HasDerivAt (fun τ => |triHL (lineL L v τ) t|)
      (triSign L t * (2 * (∑ e ∈ t.powersetCard 2, L e) * (∑ e ∈ t.powersetCard 2, v e) -
        2 * ∑ e ∈ t.powersetCard 2, 2 * L e * v e)) 0 := by
    rcases lt_or_gt_of_ne h with hn | hp
    · have hs : triSign L t = -1 := by simp [triSign, lt_asymm hn]
      rw [hs]
      exact (hasDerivAt_abs_neg (by rw [h0]; exact hn)).comp 0 hH
    · have hs : triSign L t = 1 := by simp [triSign, hp]
      rw [hs]
      exact (hasDerivAt_abs_pos (by rw [h0]; exact hp)).comp 0 hH
  have hS := (hAbs.sqrt (by simpa using h)).div_const 4
  refine hS.congr_deriv ?_
  simp only [lineL_zero]
  have hD : √|triHL L t| ≠ 0 := (Real.sqrt_pos.mpr (abs_pos.mpr h)).ne'
  have e1 : ∑ e ∈ t.powersetCard 2, 2 * L e * v e = 2 * ∑ e ∈ t.powersetCard 2, L e * v e := by
    rw [mul_sum]
    exact sum_congr rfl fun e _ => by ring
  have e2 : lorAreaDeriv L v t = triSign L t / (4 * √|triHL L t|) *
      ∑ e ∈ t.powersetCard 2, (v e * ∑ f ∈ t.powersetCard 2, L f - 2 * (L e * v e)) := by
    rw [lorAreaDeriv, mul_sum]
    exact sum_congr rfl fun e _ => by rw [lorAreaPartial]; ring
  have e3 : ∑ e ∈ t.powersetCard 2, (v e * ∑ f ∈ t.powersetCard 2, L f - 2 * (L e * v e)) =
      (∑ e ∈ t.powersetCard 2, L e) * (∑ e ∈ t.powersetCard 2, v e) -
        2 * ∑ e ∈ t.powersetCard 2, L e * v e := by
    rw [sum_sub_distrib, ← sum_mul, ← mul_sum]
    ring
  rw [e1, e2, e3]
  field_simp

omit [DecidableEq V] in
/-- Along a line of squared lengths the causal type of a non-null triangle is locally constant. -/
theorem eventually_causalZ (L v : Finset V → ℝ) {t : Finset V} (h : triHL L t ≠ 0) :
    ∀ᶠ τ in 𝓝 0, causalZ (lineL L v τ) t = causalZ L t := by
  have hc : ContinuousAt (fun τ => triHL (lineL L v τ) t) 0 :=
    (hasDerivAt_triHL L v t).continuousAt
  have h0 : triHL (lineL L v 0) t = triHL L t := by rw [lineL_zero]
  rcases lt_or_gt_of_ne h with hn | hp
  · have hn' : triHL (lineL L v 0) t < 0 := by rw [h0]; exact hn
    filter_upwards [hc.eventually (gt_mem_nhds hn')] with τ hτ
    have hτ' : triHL (lineL L v τ) t < 0 := hτ
    simp only [causalZ, lt_asymm hτ', lt_asymm hn, ↓reduceIte]
  · have hp' : 0 < triHL (lineL L v 0) t := by rw [h0]; exact hp
    filter_upwards [hc.eventually (lt_mem_nhds hp')] with τ hτ
    have hτ' : 0 < triHL (lineL L v τ) t := hτ
    simp only [causalZ, hτ', hp, ↓reduceIte]

omit [DecidableEq V] in
/-- Along a line of squared lengths, `A_t Z_t` has the derivative `dA_t Z_t` at a non-null
triangle. -/
theorem hasDerivAt_area_causalZ (L v : Finset V → ℝ) {t : Finset V} (h : triHL L t ≠ 0) :
    HasDerivAt (fun τ => (lorArea (lineL L v τ) t : ℂ) * causalZ (lineL L v τ) t)
      ((lorAreaDeriv L v t : ℂ) * causalZ L t) 0 := by
  refine ((hasDerivAt_lorArea L v h).ofReal_comp.mul_const (causalZ L t)).congr_of_eventuallyEq ?_
  filter_upwards [eventually_causalZ L v h] with τ hτ
  rw [hτ]

/-! ## One 4-simplex -/

/-- The Lorentzian dihedral angles of a 4-simplex of `K` are differentiable along every line of
squared lengths. -/
theorem LorLengthsNondeg4.hasDerivAt_lorDihedralAt {K : Complex4 V} {L : Finset V → ℝ}
    (hK : LorLengthsNondeg4 K L) (v : Finset V → ℝ) {σ : Finset V} (hσ : σ ∈ K.simps)
    {t : Finset V} (ht : t ∈ σ.powersetCard 3) :
    HasDerivAt (fun τ => lorDihedralAt (lineL L v τ) σ t)
      (deriv (fun τ => lorDihedralAt (lineL L v τ) σ t) 0) 0 := by
  obtain ⟨hts, ht3⟩ := mem_powersetCard.mp ht
  obtain ⟨a, b, c, x, y, hab, hac, hax, hay, hbc, hbx, hby, hcx, hcy, hxy, rfl, rfl⟩ :=
    exists_label4 (K.card_eq σ hσ) ht3 hts
  have hfun : (fun τ => lorDihedralAt (lineL L v τ) {a, b, c, x, y} {a, b, c}) =
      fun τ => lorDihedral4 (lineL L v τ) a b c x y :=
    funext fun τ => lorDihedralAt_eq _ hab hac hax hay hbc hbx hby hcx hcy hxy
  have hnd := hK.lorNondeg4 hab hac hax hay hbc hbx hby hcx hcy hxy hσ
  rw [hfun]
  exact (hasDerivAt_lorDihedral4_line L v a b c x y hnd.f_u hnd.f_s hnd.t₁ hnd.g4).differentiableAt
    |>.hasDerivAt

/-- **One Lorentzian 4-simplex's contribution to the variation** (Schläfli): along a direction
`v`, the derivative of `Σ_{t ⊂ σ} A_t θ_σ(t)` is `Σ_{t ⊂ σ} dA_t θ_σ(t)`; the variation of the
complex angles cancels. -/
theorem hasDerivAt_lorSimpSum4 {K : Complex4 V} {L : Finset V → ℝ} (hK : LorLengthsNondeg4 K L)
    (v : Finset V → ℝ) {σ : Finset V} (hσ : σ ∈ K.simps) :
    HasDerivAt (fun τ => ∑ t ∈ σ.powersetCard 3,
        (lorArea (lineL L v τ) t : ℂ) * lorDihedralAt (lineL L v τ) σ t)
      (∑ t ∈ σ.powersetCard 3, (lorAreaDeriv L v t : ℂ) * lorDihedralAt L σ t) 0 := by
  have hA : ∀ t ∈ σ.powersetCard 3, HasDerivAt (fun τ => (lorArea (lineL L v τ) t : ℂ))
      (lorAreaDeriv L v t : ℂ) 0 := fun t ht => by
    obtain ⟨hts, ht3⟩ := mem_powersetCard.mp ht
    exact (hasDerivAt_lorArea L v (hK.tri t (mem_faces.mpr ⟨σ, hσ, hts, ht3⟩))).ofReal_comp
  have hθ : ∀ t ∈ σ.powersetCard 3, HasDerivAt (fun τ => lorDihedralAt (lineL L v τ) σ t)
      (deriv (fun τ => lorDihedralAt (lineL L v τ) σ t) 0) 0 :=
    fun t ht => hK.hasDerivAt_lorDihedralAt v hσ ht
  have hprod := HasDerivAt.fun_sum fun t ht => (hA t ht).mul (hθ t ht)
  -- Schläfli: the angle variation, weighted by the areas at `L`, vanishes
  obtain ⟨p, q, r, s, u, hpq, hpr, hps, hpu, hqr, hqs, hqu, hrs, hru, hsu, rfl⟩ :=
    exists_label5 (K.card_eq σ hσ)
  have hS := lorSchlaefli4_finset L v hpq hpr hps hpu hqr hqs hqu hrs hru hsu
    (hK.lorNondeg4 hpq hpr hps hpu hqr hqs hqu hrs hru hsu hσ)
  have hS' := HasDerivAt.fun_sum fun t ht => (hθ t ht).const_mul (lorArea L t : ℂ)
  have hzero := hS'.unique hS
  refine hprod.congr_deriv ?_
  simp only [lineL_zero, sum_add_distrib, hzero, add_zero]

/-! ## The Lorentzian Regge equations -/

/-- **The Lorentzian Regge equations.** For non-degenerate Lorentzian squared lengths `L` on `K`
and any direction `v` of change of the squared lengths, the derivative of the Lorentzian Regge
action along `L + τ v` at `τ = 0` is `Σ_{interior} dA_t ε_t + Σ_{boundary} dA_t (π Z_t − Σ θ)`:
only the areas vary. -/
theorem hasDerivAt_lorReggeAction {K : Complex4 V} {L : Finset V → ℝ}
    (hK : LorLengthsNondeg4 K L) (v : Finset V → ℝ) :
    HasDerivAt (fun τ => lorReggeAction K (lineL L v τ))
      (∑ t ∈ intTris4 K, (lorAreaDeriv L v t : ℂ) * lorDeficit K L t +
        ∑ t ∈ bdryTris4 K, (lorAreaDeriv L v t : ℂ) * lorBdryAngle K L t) 0 := by
  have hA : ∀ t ∈ K.tris,
      HasDerivAt (fun τ => (lorArea (lineL L v τ) t : ℂ) * causalZ (lineL L v τ) t)
        ((lorAreaDeriv L v t : ℂ) * causalZ L t) 0 :=
    fun t ht => hasDerivAt_area_causalZ L v (hK.tri t ht)
  have hint : HasDerivAt (fun τ => ∑ t ∈ intTris4 K,
        2 * π * ((lorArea (lineL L v τ) t : ℂ) * causalZ (lineL L v τ) t))
      (∑ t ∈ intTris4 K, 2 * π * ((lorAreaDeriv L v t : ℂ) * causalZ L t)) 0 :=
    HasDerivAt.fun_sum fun t ht => (hA t (mem_filter.mp ht).1).const_mul (2 * π : ℂ)
  have hbd : HasDerivAt (fun τ => ∑ t ∈ bdryTris4 K,
        π * ((lorArea (lineL L v τ) t : ℂ) * causalZ (lineL L v τ) t))
      (∑ t ∈ bdryTris4 K, π * ((lorAreaDeriv L v t : ℂ) * causalZ L t)) 0 :=
    HasDerivAt.fun_sum fun t ht => (hA t (mem_filter.mp ht).1).const_mul (π : ℂ)
  have hsimps := HasDerivAt.fun_sum (u := K.simps) fun σ hσ => hasDerivAt_lorSimpSum4 hK v hσ
  rw [sum_lorCurvature_eq]
  convert (hint.add hbd).sub hsimps using 1
  funext τ
  rw [lorReggeAction_eq_sum_simps]
  simp only [Pi.sub_apply, Pi.add_apply]

/-- The partial derivative of the Lorentzian Regge action with respect to the squared length of
the edge `e`: `∂S/∂L_e = Σ_{t ∋ e} (∂A_t/∂L_e) ε_t` over interior triangles plus the same with
`π Z_t − Σ θ` over boundary triangles. -/
noncomputable def lorReggePartial (K : Complex4 V) (L : Finset V → ℝ) (e : Finset V) : ℂ :=
  ∑ t ∈ (intTris4 K).filter (e ⊆ ·), (lorAreaPartial L t e : ℂ) * lorDeficit K L t +
    ∑ t ∈ (bdryTris4 K).filter (e ⊆ ·), (lorAreaPartial L t e : ℂ) * lorBdryAngle K L t

/-- Exchanging the sum over triangles of a set `T ⊆ K.tris` with the sum over edges, for complex
values. -/
theorem sum_tris_edges_complex {K : Complex4 V} {T : Finset (Finset V)} (hT : T ⊆ K.tris)
    (F : Finset V → Finset V → ℂ) :
    ∑ t ∈ T, ∑ e ∈ t.powersetCard 2, F t e = ∑ e ∈ K.edges, ∑ t ∈ T.filter (e ⊆ ·), F t e := by
  apply sum_comm'
  intro t e
  simp only [mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨ht, hs, h2⟩
    obtain ⟨σ, hσ, htσ, -⟩ := mem_faces.mp (hT ht)
    exact ⟨⟨ht, hs⟩, mem_faces.mpr ⟨σ, hσ, hs.trans htσ, h2⟩⟩
  · rintro ⟨⟨ht, hs⟩, he⟩
    exact ⟨ht, hs, card_of_mem_faces he⟩

/-- **The Lorentzian Regge equations, edge by edge.** Along every direction `v` the derivative of
the Lorentzian Regge action is `Σ_e v_e ∂S/∂L_e`. -/
theorem hasDerivAt_lorReggeAction_grad {K : Complex4 V} {L : Finset V → ℝ}
    (hK : LorLengthsNondeg4 K L) (v : Finset V → ℝ) :
    HasDerivAt (fun τ => lorReggeAction K (lineL L v τ))
      (∑ e ∈ K.edges, (v e : ℂ) * lorReggePartial K L e) 0 := by
  refine (hasDerivAt_lorReggeAction hK v).congr_deriv ?_
  have hi : intTris4 K ⊆ K.tris := filter_subset _ _
  have hb : bdryTris4 K ⊆ K.tris := filter_subset _ _
  simp only [lorAreaDeriv, Complex.ofReal_sum, Complex.ofReal_mul, sum_mul]
  rw [sum_tris_edges_complex hi, sum_tris_edges_complex hb, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  simp only [lorReggePartial, mul_add, mul_sum]
  congr 1 <;> exact sum_congr rfl fun t _ => by ring

/-- **The Lorentzian discrete Einstein equations.** For non-degenerate Lorentzian squared lengths,
the Lorentzian Regge action is stationary under every variation that keeps the boundary lengths
fixed exactly when `∂S/∂L_e = Σ_{t ∋ e} (∂A_t/∂L_e) ε_t` vanishes at every interior edge. -/
theorem lorReggeAction_stationary_iff {K : Complex4 V} {L : Finset V → ℝ}
    (hK : LorLengthsNondeg4 K L) :
    (∀ v : Finset V → ℝ, (∀ e ∈ bdryEdges4 K, v e = 0) →
      HasDerivAt (fun τ => lorReggeAction K (lineL L v τ)) 0 0) ↔
    ∀ e ∈ intEdges4 K,
      ∑ t ∈ (intTris4 K).filter (e ⊆ ·), (lorAreaPartial L t e : ℂ) * lorDeficit K L t = 0 := by
  have hpart : ∀ e ∈ intEdges4 K, lorReggePartial K L e =
      ∑ t ∈ (intTris4 K).filter (e ⊆ ·), (lorAreaPartial L t e : ℂ) * lorDeficit K L t :=
    fun e he => by rw [lorReggePartial, filter_bdryTris4_eq_empty he, sum_empty, add_zero]
  constructor
  · intro h e he
    have hv : ∀ f ∈ bdryEdges4 K, (fun g => if g = e then (1 : ℝ) else 0) f = 0 := by
      intro f hf
      have : f ≠ e := fun hfe => (mem_filter.mp he).2 (hfe ▸ (mem_filter.mp hf).2)
      simp [this]
    have h1 := (hasDerivAt_lorReggeAction_grad hK fun g => if g = e then (1 : ℝ) else 0).unique
      (h _ hv)
    rw [sum_eq_single e (fun f _ hfe => by simp [hfe]) (fun hn => absurd (mem_filter.mp he).1 hn),
      ite_eq_left rfl, Complex.ofReal_one, one_mul] at h1
    rw [← hpart e he]
    exact h1
  · intro h v hv
    refine (hasDerivAt_lorReggeAction_grad hK v).congr_deriv ?_
    refine sum_eq_zero fun e he => ?_
    by_cases hb : ∃ t ∈ bdryTris4 K, e ⊆ t
    · rw [hv e (mem_filter.mpr ⟨he, hb⟩), Complex.ofReal_zero, zero_mul]
    · have he' : e ∈ intEdges4 K := mem_filter.mpr ⟨he, hb⟩
      rw [hpart e he', h e he', mul_zero]

end Lightlike.ReggeLor
