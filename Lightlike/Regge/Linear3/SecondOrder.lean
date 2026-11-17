import Lightlike.Regge.Linear3.AngleSmooth
import Lightlike.Regge.Linear3.Taylor
import Lightlike.Regge.Gradient

/-!
# The second-order expansion of the Regge action at a flat closed 3-complex

Let `K` be a closed 3-complex (no boundary triangles) with non-degenerate edge lengths `ℓ₀` at which
every deficit angle `δ_e` vanishes (a flat triangulation), and let the squared lengths vary along a
line, `ℓ² = ℓ₀² + ε a` (`lenLine`). Then the Regge action `S = Σ_e ℓ_e δ_e` is
`S = ε²/2 · Σ_e ℓ_e'(0) δ_e'(0) + O(ε³)` with `ℓ_e'(0) = a_e / (2 ℓ₀_e)`
(`regge_second_order`). The first-order term vanishes because `δ_e(0) = 0`, and the second-order term
comes from Regge's equations, `dS = Σ_e δ_e dℓ_e` (Schläfli's identity, `hasFDerivAt_reggeAction`),
differentiated once more; the remainder is controlled by the `C³` smoothness of the dihedral
angles (`AngleSmooth.lean`) and a one-variable Taylor bound (`taylor2_cubic`).

This is the fixed-mesh second-order coefficient of Christiansen, *On the linearization of Regge
calculus*, Numer. Math. 119 (2011), Proposition 3.2, eq. (75) and its consequence (81)
`R(ε) = ε²/2 Σ_e θ_e'(0) ℓ_e'(0) + O(ε³)`.

## Main results

* `exists_label_edge`: a tetrahedron containing an edge is `{p, q, r, s}` with the edge `{p, q}`.
* `contDiffAt_deficit`: deficit angles are `C³` along the line.
* `eventually_lengthsNondeg`: non-degeneracy persists for small `ε`.
* `hasDerivAt_reggeAction_line`: `d/dε S = Σ_e ℓ_e' δ_e` near `0`.
* `regge_second_order`: the expansion.

**Limits.** A fixed (arbitrary) closed complex; the line is in squared lengths with `ℓ₀` positive on
every vertex pair (values off the edges of `K` do not enter and only normalise the statement).
The identification of `Σ_e ℓ_e' δ_e'` with the quadratic form `⟨curl^t curl u', u'⟩` of the paper (its
Theorem 3.3), and the limit as the mesh tends to zero, are not claimed here.
-/

open Real Filter Topology Finset
namespace Lightlike.Regge.Linear3
open Lightlike.Regge
open Lightlike.PR (Complex3)

variable {V : Type*} [DecidableEq V]

/-- A tetrahedron containing an edge is `{p, q, r, s}` with the edge `{p, q}`. -/
theorem exists_label_edge {t e : Finset V} (ht : t.card = 4) (he : e.card = 2) (hs : e ⊆ t) :
    ∃ p q r s, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧ t = {p, q, r, s} ∧ e = {p, q} := by
  obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp he
  have hd : (t \ {p, q}).card = 2 := by rw [card_sdiff_of_subset hs, ht, he]
  obtain ⟨r, s, hrs, hrs'⟩ := card_eq_two.mp hd
  have hr : r ∈ t \ {p, q} := by simp [hrs']
  have hs' : s ∈ t \ {p, q} := by simp [hrs']
  obtain ⟨hrt, hrn⟩ := mem_sdiff.1 hr
  obtain ⟨hst, hsn⟩ := mem_sdiff.1 hs'
  simp only [mem_insert, mem_singleton, not_or] at hrn hsn
  refine ⟨p, q, r, s, hpq, fun h => hrn.1 h.symm, fun h => hsn.1 h.symm,
    fun h => hrn.2 h.symm, fun h => hsn.2 h.symm, hrs, ?_, rfl⟩
  ext x
  constructor
  · intro hx
    by_cases hx' : x ∈ ({p, q} : Finset V)
    · simp only [mem_insert, mem_singleton] at hx' ⊢; tauto
    · have : x ∈ t \ {p, q} := mem_sdiff.2 ⟨hx, hx'⟩
      rw [hrs'] at this
      simp only [mem_insert, mem_singleton] at this ⊢; tauto
  · intro hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hs (by simp)
    · exact hs (by simp)
    · exact hrt
    · exact hst


/-- The dihedral angle of a tetrahedron of the star of an edge is `C³` along the line. -/
theorem contDiffAt_dihedralAt_star {K : Complex3 V} {ℓ₀ : Finset V → ℝ} (hK : LengthsNondeg K ℓ₀)
    (a : Finset V → ℝ) {e t : Finset V} (he : e ∈ K.edges) (ht : t ∈ star K e) :
    ContDiffAt ℝ 3 (fun ε => dihedralAt (lenLine ℓ₀ a ε) t e) 0 := by
  obtain ⟨htK, hse⟩ := mem_filter.1 ht
  obtain ⟨t', ht', hs', h2⟩ := Complex3.mem_edges.mp he
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl, rfl⟩ :=
    exists_label_edge (K.card_eq t htK) h2 hse
  exact contDiffAt_dihedralAt hK a hpq hpr hps hqr hqs hrs htK

/-- **The deficit angle of an edge is `C³` along the line of squared lengths.** -/
theorem contDiffAt_deficit {K : Complex3 V} {ℓ₀ : Finset V → ℝ} (hK : LengthsNondeg K ℓ₀)
    (a : Finset V → ℝ) {e : Finset V} (he : e ∈ K.edges) :
    ContDiffAt ℝ 3 (fun ε => deficit K (lenLine ℓ₀ a ε) e) 0 := by
  unfold deficit angleSum
  exact contDiffAt_const.sub (ContDiffAt.sum fun t ht => contDiffAt_dihedralAt_star hK a he ht)

omit [DecidableEq V] in
/-- The length of an edge is `C³` along the line, at positive length. -/
theorem contDiffAt_lenLine {ℓ₀ : Finset V → ℝ} (a : Finset V → ℝ) {e : Finset V} (he : 0 < ℓ₀ e) :
    ContDiffAt ℝ 3 (fun ε => lenLine ℓ₀ a ε e) 0 := by
  unfold lenLine sqLine
  have h : (0 : ℝ) < ℓ₀ e ^ 2 + 0 * a e := by simpa using pow_pos he 2
  exact (Real.contDiffAt_sqrt h.ne').comp 0 (by fun_prop : ContDiff ℝ 3 fun ε : ℝ => ℓ₀ e ^ 2 + ε * a e).contDiffAt |>.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)


omit [DecidableEq V] in
/-- The length assignment of the line is continuous in `ε`. -/
theorem continuous_lenLine (ℓ₀ a : Finset V → ℝ) (g : Finset V) :
    Continuous (fun ε => lenLine ℓ₀ a ε g) := by
  unfold lenLine sqLine
  fun_prop

omit [DecidableEq V] in
/-- At `ε = 0` the line is the base length assignment where it is positive. -/
theorem lenLine_zero {ℓ₀ : Finset V → ℝ} (a : Finset V → ℝ) {g : Finset V} (hg : 0 < ℓ₀ g) :
    lenLine ℓ₀ a 0 g = ℓ₀ g := by
  simp [lenLine, sqLine, Real.sqrt_sq hg.le]

/-- **Non-degeneracy persists along the line.** -/
theorem eventually_lengthsNondeg {K : Complex3 V} {ℓ₀ : Finset V → ℝ} (hK : LengthsNondeg K ℓ₀)
    (a : Finset V → ℝ) : ∀ᶠ ε in 𝓝 (0 : ℝ), LengthsNondeg K (lenLine ℓ₀ a ε) := by
  unfold LengthsNondeg
  rw [eventually_all_finset]
  intro t ht
  obtain ⟨h1, h2, h3⟩ := hK t ht
  have hc := fun g => continuous_lenLine ℓ₀ a g
  have hp : ∀ x y : V, x ≠ y → ({x, y} : Finset V) ∈ t.powersetCard 2 → lenLine ℓ₀ a 0 {x, y} = ℓ₀ {x, y} :=
    fun x y _ hxy => lenLine_zero a (h1 _ hxy)
  refine eventually_and.2 ⟨?_, eventually_and.2 ⟨?_, ?_⟩⟩
  · rw [eventually_all_finset]
    intro g hg
    exact (hc g).continuousAt.eventually (lt_mem_nhds (by
      show 0 < lenLine ℓ₀ a 0 g
      rw [lenLine_zero a (h1 g hg)]; exact h1 g hg))
  · rw [eventually_all_finset]
    intro f hf
    have hcf : Continuous (fun ε => triH (lenLine ℓ₀ a ε) f) := by
      unfold triH
      fun_prop
    refine hcf.continuousAt.eventually (lt_mem_nhds ?_)
    obtain ⟨hft, hf3⟩ := mem_powersetCard.mp hf
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hf3
    have e : ∀ u v : V, u ∈ ({x, y, z} : Finset V) → v ∈ ({x, y, z} : Finset V) → u ≠ v →
        lenLine ℓ₀ a 0 {u, v} = ℓ₀ {u, v} := fun u v hu hv huv =>
      lenLine_zero a (h1 _ (mem_powersetCard.mpr ⟨by
        intro w hw; simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl <;> [exact hft hu; exact hft hv], card_pair huv⟩))
    show 0 < triH (lenLine ℓ₀ a 0) {x, y, z}
    rw [triH_eq _ hxy hxz hyz, e x y (by simp) (by simp) hxy, e y z (by simp) (by simp) hyz,
      e z x (by simp) (by simp) hxz.symm, ← triH_eq _ hxy hxz hyz]
    exact h2 _ hf
  · have hct : Continuous (fun ε => tetV2 (lenLine ℓ₀ a ε) t) := by
      unfold tetV2
      fun_prop
    refine hct.continuousAt.eventually (lt_mem_nhds ?_)
    obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ := exists_label (K := K) ht
    have e : ∀ u v : V, u ∈ ({p, q, r, s} : Finset V) → v ∈ ({p, q, r, s} : Finset V) → u ≠ v →
        lenLine ℓ₀ a 0 {u, v} = ℓ₀ {u, v} := fun u v hu hv huv =>
      lenLine_zero a (h1 _ (mem_powersetCard.mpr ⟨by
        intro w hw; simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption, card_pair huv⟩))
    show 0 < tetV2 (lenLine ℓ₀ a 0) {p, q, r, s}
    rw [tetV2_eq _ hpq hpr hps hqr hqs hrs, e p q (by simp) (by simp) hpq,
      e q r (by simp) (by simp) hqr, e r p (by simp) (by simp) hpr.symm,
      e r s (by simp) (by simp) hrs, e p s (by simp) (by simp) hps, e q s (by simp) (by simp) hqs,
      ← tetV2_eq _ hpq hpr hps hqr hqs hrs]
    exact h3


section Derivative

variable [Fintype V]

/-- The derivative `a / (2 ℓ)` of the length along the line, as an assignment. -/
noncomputable def lenLine' (ℓ₀ a : Finset V → ℝ) (ε : ℝ) (f : Finset V) : ℝ :=
  a f / (2 * lenLine ℓ₀ a ε f)

/-- Where all squared lengths are positive the line of lengths is differentiable, with derivative
`lenLine'`. -/
theorem hasDerivAt_lenLine {ℓ₀ a : Finset V → ℝ} {ε : ℝ} (h : ∀ g, 0 < sqLine ℓ₀ a ε g) :
    HasDerivAt (lenLine ℓ₀ a) (lenLine' ℓ₀ a ε) ε := by
  rw [hasDerivAt_pi]
  intro g
  have h1 : HasDerivAt (fun ε => sqLine ℓ₀ a ε g) (a g) ε := by
    unfold sqLine
    simpa using ((hasDerivAt_id ε).mul_const (a g)).const_add (ℓ₀ g ^ 2)
  have h2 : HasDerivAt (fun ε => √(sqLine ℓ₀ a ε g)) (a g / (2 * √(sqLine ℓ₀ a ε g))) ε :=
    h1.sqrt (h g).ne'
  exact h2

/-- **The derivative of the Regge action along the line** at non-degenerate lengths: `Σ_e ℓ_e' δ_e`
for a closed complex. -/
theorem hasDerivAt_reggeAction_line {K : Complex3 V} {ℓ₀ a : Finset V → ℝ} {ε : ℝ}
    (hclosed : bdryTris K = ∅) (hpos : ∀ g, 0 < sqLine ℓ₀ a ε g)
    (hK : LengthsNondeg K (lenLine ℓ₀ a ε)) :
    HasDerivAt (fun ε => reggeAction K (lenLine ℓ₀ a ε))
      (∑ e ∈ K.edges, lenLine' ℓ₀ a ε e * deficit K (lenLine ℓ₀ a ε) e) ε := by
  have h1 := (hasFDerivAt_reggeAction hK).comp_hasDerivAt ε (hasDerivAt_lenLine hpos)
  refine h1.congr_deriv ?_
  rw [reggeGradient_apply, intEdges_of_bdryTris_eq_empty hclosed]
  simp [bdryEdges, hclosed]

/-- The base lengths are those of the line at `ε = 0`. -/
theorem lenLine_zero_eq {ℓ₀ : Finset V → ℝ} (hpos : ∀ g, 0 < ℓ₀ g) (a : Finset V → ℝ) :
    lenLine ℓ₀ a 0 = ℓ₀ := funext fun g => lenLine_zero a (hpos g)

/-- **The second-order expansion of the Regge action at a flat closed complex.** Let `K` be a closed
3-complex with non-degenerate lengths `ℓ₀` at which every deficit angle vanishes, and let the squared
lengths vary along `ℓ₀² + ε a`. Then the Regge action is
`ε² / 2 · Σ_e (a_e / (2 ℓ₀_e)) δ_e'(0) + O(ε³)`, where `δ_e'(0)` is the derivative of the deficit
angle of `e` along the line (Christiansen 2011, eq. (81)). -/
theorem regge_second_order {K : Complex3 V} {ℓ₀ : Finset V → ℝ} (hclosed : bdryTris K = ∅)
    (hpos : ∀ g, 0 < ℓ₀ g) (hK : LengthsNondeg K ℓ₀)
    (hflat : ∀ e ∈ K.edges, deficit K ℓ₀ e = 0) (a : Finset V → ℝ) :
    ∃ M r : ℝ, 0 < r ∧ ∀ ε : ℝ, |ε| ≤ r →
      |reggeAction K (lenLine ℓ₀ a ε) -
        ε ^ 2 / 2 * ∑ e ∈ K.edges, a e / (2 * ℓ₀ e) *
          deriv (fun ε => deficit K (lenLine ℓ₀ a ε) e) 0| ≤ M * |ε| ^ 3 := by
  set f : ℝ → ℝ := fun ε => reggeAction K (lenLine ℓ₀ a ε) with hf
  set g : ℝ → ℝ := fun ε => ∑ e ∈ K.edges, lenLine' ℓ₀ a ε e * deficit K (lenLine ℓ₀ a ε) e with hg
  have hmem : ∀ e ∈ K.edges, 0 < ℓ₀ e := fun e _ => hpos e
  -- smoothness
  have hfs : ContDiffAt ℝ 3 f 0 := by
    have : f = fun ε => ∑ e ∈ K.edges, lenLine ℓ₀ a ε e * deficit K (lenLine ℓ₀ a ε) e := by
      funext ε; exact reggeAction_of_bdryTris_eq_empty hclosed _
    rw [this]
    exact ContDiffAt.sum fun e he => (contDiffAt_lenLine a (hpos e)).mul (contDiffAt_deficit hK a he)
  have hδ0 : ∀ e ∈ K.edges, deficit K (lenLine ℓ₀ a 0) e = 0 := fun e he => by
    rw [lenLine_zero_eq hpos]; exact hflat e he
  have hf0 : f 0 = 0 := by
    simp only [hf]
    rw [reggeAction_of_bdryTris_eq_empty hclosed]
    exact sum_eq_zero fun e he => by rw [hδ0 e he, mul_zero]
  -- derivative of `f` near `0`
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ g, 0 < sqLine ℓ₀ a ε g := by
    rw [eventually_all]
    intro g
    have hc : Continuous (fun ε : ℝ => sqLine ℓ₀ a ε g) := by unfold sqLine; fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa [sqLine] using pow_pos (hpos g) 2))
  have hfg : ∀ᶠ ε in 𝓝 (0 : ℝ), HasDerivAt f (g ε) ε := by
    filter_upwards [hev, eventually_lengthsNondeg hK a] with ε h1 h2
    exact hasDerivAt_reggeAction_line hclosed h1 h2
  have hdf : deriv f =ᶠ[𝓝 0] g := hfg.mono fun ε h => h.deriv
  have h1 : deriv f 0 = 0 := by
    rw [hdf.eq_of_nhds]
    simp only [hg]
    exact sum_eq_zero fun e he => by rw [hδ0 e he, mul_zero]
  -- derivative of `g` at `0`
  have hd2 : deriv (deriv f) 0 = deriv g 0 := hdf.deriv_eq
  have hlen : ∀ e ∈ K.edges, DifferentiableAt ℝ (fun ε => lenLine ℓ₀ a ε e) 0 := fun e _ =>
    ((contDiffAt_lenLine a (hpos e)).differentiableAt (by norm_num))
  have hdel : ∀ e ∈ K.edges, DifferentiableAt ℝ (fun ε => deficit K (lenLine ℓ₀ a ε) e) 0 := fun e he =>
    (contDiffAt_deficit hK a he).differentiableAt (by norm_num)
  have hl0 : ∀ e : Finset V, lenLine ℓ₀ a 0 e ≠ 0 := fun e => by rw [lenLine_zero_eq hpos]; exact (hpos e).ne'
  have hprod : ∀ e ∈ K.edges, HasDerivAt (fun ε => lenLine' ℓ₀ a ε e * deficit K (lenLine ℓ₀ a ε) e)
      (a e / (2 * ℓ₀ e) * deriv (fun ε => deficit K (lenLine ℓ₀ a ε) e) 0 +
        deriv (fun ε => lenLine' ℓ₀ a ε e) 0 * deficit K (lenLine ℓ₀ a 0) e) 0 := by
    intro e he
    have hq : DifferentiableAt ℝ (fun ε => lenLine' ℓ₀ a ε e) 0 := by
      unfold lenLine'
      exact (differentiableAt_const _).div ((differentiableAt_const _).mul (hlen e he)) (by simpa using hl0 e)
    have := (hq.hasDerivAt.mul (hdel e he).hasDerivAt)
    convert this using 1
    simp [lenLine', lenLine_zero_eq hpos]
    ring
  have hdg : deriv g 0 = ∑ e ∈ K.edges, a e / (2 * ℓ₀ e) * deriv (fun ε => deficit K (lenLine ℓ₀ a ε) e) 0 := by
    have := HasDerivAt.sum (u := K.edges) (A := fun e ε => lenLine' ℓ₀ a ε e * deficit K (lenLine ℓ₀ a ε) e) hprod
    have h2 := this.deriv
    simp only [hg]
    rw [show (fun ε => ∑ e ∈ K.edges, lenLine' ℓ₀ a ε e * deficit K (lenLine ℓ₀ a ε) e) =
      ∑ e ∈ K.edges, fun ε => lenLine' ℓ₀ a ε e * deficit K (lenLine ℓ₀ a ε) e from by
        funext ε; simp]
    rw [h2]
    exact sum_congr rfl fun e he => by rw [hδ0 e he, mul_zero, add_zero]
  obtain ⟨M, r, hr, hb⟩ := taylor2_cubic hfs hf0 h1
  refine ⟨M, r, hr, fun ε hε => ?_⟩
  have := hb ε hε
  rw [hd2, hdg] at this
  convert this using 3
  ring

end Derivative

end Lightlike.Regge.Linear3
