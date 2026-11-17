import Lightlike.Regge.Linear3.AngleSmooth
import Lightlike.Regge.Linear3.TorusBridge
import Lightlike.Regge.Conv3.DihedralTaylor

/-!
# Derivatives of dihedral angles and deficit angles along a line of squared lengths

Along the line of squared lengths `ℓ₀² + ε a`, the dihedral angle of a tetrahedron at one of its edges has, at
`ε = 0`, the derivative `Dh (L₀, a)`, the first variation of the angle at the base squared lengths `L₀`
(`hasDerivAt_dihedralAt_line`, from `Conv3.hasDerivAt_Dsq`). For the periodic Kuhn complex the deficit angle of
the edge `(z, k)` has derivative minus the sum over the incidences of the class `k` of these
(`hasDerivAt_deficit_edgeOf`). The first variation is invariant under a joint scaling of the squared
lengths and of the variation, `Dh (c L, c δ) = Dh (L, δ)` (`Dh_scale`), because the angle is scale invariant.

## Main results

* `Dh_scale`: joint scaling invariance of the first variation of the dihedral angle.
* `hasDerivAt_dihedralAt_line`, `hasDerivAt_dihedral_inc`: the derivative of one angle.
* `hasDerivAt_deficit_edgeOf`: the derivative of the deficit angle of an edge of the periodic complex.

**Limits.** At `ε = 0` only; non-degenerate base lengths.
-/

open Real Filter Topology
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3

theorem Pp_smul {c : ℝ} (hc : 0 < c) (a b d : ℝ) (ha : 0 < a) : Pp (c * a) (c * b) (c * d) = c * Pp a b d := by
  unfold Pp; field_simp

theorem Nn_smul {c : ℝ} (hc : 0 < c) (a b d e f g : ℝ) (ha : 0 < a) :
    Nn (c * a) (c * b) (c * d) (c * e) (c * f) (c * g) = c * Nn a b d e f g := by
  unfold Nn; field_simp

theorem cosSq_smul {c : ℝ} (hc : 0 < c) (a b d e f g : ℝ) (ha : 0 < a) :
    cosSq (c * a) (c * b) (c * d) (c * e) (c * f) (c * g) = cosSq a b d e f g := by
  unfold cosSq
  rw [Nn_smul hc _ _ _ _ _ _ ha, Pp_smul hc _ _ _ ha, Pp_smul hc _ _ _ ha]
  have : c * Pp a b d * (c * Pp a e f) = c ^ 2 * (Pp a b d * Pp a e f) := by ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  by_cases h0 : √(Pp a b d * Pp a e f) = 0
  · simp [h0]
  · field_simp

theorem Dsq_smul {c : ℝ} (hc : 0 < c) (L : Fin 6 → ℝ) (ha : 0 < L 0) : Dsq (c • L) = Dsq L := by
  unfold Dsq dihSq
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [cosSq_smul hc _ _ _ _ _ _ ha]

theorem Valid_smul {c : ℝ} (hc : 0 < c) {L : Fin 6 → ℝ} (hL : Valid L) : Valid (c • L) := by
  obtain ⟨ha, h1, h2, h3⟩ := hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; positivity
  · simp only [Pi.smul_apply, smul_eq_mul]; rw [Pp_smul hc _ _ _ ha]; positivity
  · simp only [Pi.smul_apply, smul_eq_mul]; rw [Pp_smul hc _ _ _ ha]; positivity
  · simp only [Pi.smul_apply, smul_eq_mul]; rw [cosSq_smul hc _ _ _ _ _ _ ha]; exact h3

/-- **The first variation of the dihedral angle is invariant under a joint scaling** of the squared
lengths and of the variation: `Dh (c L, c δ) = Dh (L, δ)`. -/
theorem Dh_scale {c : ℝ} (hc : 0 < c) {L : Fin 6 → ℝ} (hL : Valid L) (δ : Fin 6 → ℝ) :
    Dh (c • L, c • δ) = Dh (L, δ) := by
  have h1 := hasDerivAt_Dsq (c • δ) (Valid_smul hc hL)
  have h2 := hasDerivAt_Dsq δ hL
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, 0 < (L + ε • δ) 0 := by
    have hc : Continuous fun ε : ℝ => (L + ε • δ) 0 := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hL.1))
  have h3 : HasDerivAt (fun ε : ℝ => Dsq (L + ε • δ)) (Dh (c • L, c • δ)) 0 := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hev] with ε hε
    have : c • L + ε • c • δ = c • (L + ε • δ) := by
      funext i; simp [smul_eq_mul]; ring
    rw [this, Dsq_smul hc _ hε]
  exact h3.unique h2


open Finset in
/-- **The derivative of a dihedral angle along a line of squared lengths** at `ε = 0` is the first
variation `Dh` at the base squared lengths in the direction `a`. -/
theorem hasDerivAt_dihedralAt_line {V : Type*} [DecidableEq V] {K : Lightlike.PR.Complex3 V}
    {ℓ₀ : Finset V → ℝ} (hK : LengthsNondeg K ℓ₀) (a : Finset V → ℝ) {p q r s : V} (hpq : p ≠ q)
    (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (ht : ({p, q, r, s} : Finset V) ∈ K.tets) :
    HasDerivAt (fun ε => dihedralAt (lenLine ℓ₀ a ε) {p, q, r, s} {p, q})
      (Dh (![ℓ₀ {p, q} ^ 2, ℓ₀ {p, r} ^ 2, ℓ₀ {q, r} ^ 2, ℓ₀ {p, s} ^ 2, ℓ₀ {q, s} ^ 2, ℓ₀ {r, s} ^ 2],
        ![a {p, q}, a {p, r}, a {q, r}, a {p, s}, a {q, s}, a {r, s}])) 0 := by
  have hnd := hK.tetNondeg hpq hpr hps hqr hqs hrs ht
  have hpos : ∀ x y : V, x ≠ y → x ∈ ({p, q, r, s} : Finset V) → y ∈ ({p, q, r, s} : Finset V) →
      0 < ℓ₀ {x, y} := fun x y hxy hx hy =>
    (hK _ ht).1 _ (mem_powersetCard.mpr ⟨by simp [insert_subset_iff, hx, hy], card_pair hxy⟩)
  have hv : Valid ![ℓ₀ {p, q} ^ 2, ℓ₀ {p, r} ^ 2, ℓ₀ {q, r} ^ 2, ℓ₀ {p, s} ^ 2, ℓ₀ {q, s} ^ 2,
      ℓ₀ {r, s} ^ 2] := valid_of_tetNondeg (by
      have := hnd
      simp only [labLen, pair_comm r p] at this
      simpa using this)
  have h1 := hasDerivAt_Dsq (L := ![ℓ₀ {p, q} ^ 2, ℓ₀ {p, r} ^ 2, ℓ₀ {q, r} ^ 2, ℓ₀ {p, s} ^ 2,
    ℓ₀ {q, s} ^ 2, ℓ₀ {r, s} ^ 2]) ![a {p, q}, a {p, r}, a {q, r}, a {p, s}, a {q, s}, a {r, s}] hv
  refine h1.congr_of_eventuallyEq ?_
  have hev : ∀ x y : V, x ≠ y → x ∈ ({p, q, r, s} : Finset V) → y ∈ ({p, q, r, s} : Finset V) →
      ∀ᶠ ε : ℝ in 𝓝 0, 0 < sqLine ℓ₀ a ε {x, y} := fun x y hxy hx hy => by
    have hc : Continuous (fun ε : ℝ => sqLine ℓ₀ a ε {x, y}) := by unfold sqLine; fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa [sqLine] using pow_pos (hpos x y hxy hx hy) 2))
  filter_upwards [hev p q hpq (by simp) (by simp), hev p r hpr (by simp) (by simp),
    hev q r hqr (by simp) (by simp), hev p s hps (by simp) (by simp),
    hev q s hqs (by simp) (by simp), hev r s hrs (by simp) (by simp)] with ε h1 h2 h3 h4 h5 h6
  have hne : lenLine ℓ₀ a ε {p, q} ≠ 0 := (Real.sqrt_pos.2 h1).ne'
  rw [dihedralAt_eq _ hpq hpr hps hqr hqs hrs hne]
  simp only [lenLine]
  rw [dihedral_sqrt_eq h1 h2.le h3.le h4.le h5.le h6.le]
  congr 1
  funext i
  fin_cases i <;> simp [sqLine]


section Torus

variable (n : ℕ) [NeZero n]

/-- The six edge values `(pq, pr, qr, ps, qs, rs)` of the incidence `(σ, h)` of the cell `c`. -/
def incV (f : Finset (TV n) → ℝ) (c : TV n) (σ h : Fin 6) : Fin 6 → ℝ :=
  ![f {c + off n σ (hP h), c + off n σ (hQ h)}, f {c + off n σ (hP h), c + off n σ (hR h)},
    f {c + off n σ (hQ h), c + off n σ (hR h)}, f {c + off n σ (hP h), c + off n σ (hS h)},
    f {c + off n σ (hQ h), c + off n σ (hS h)}, f {c + off n σ (hR h), c + off n σ (hS h)}]

/-- **The derivative of the dihedral angle of an incidence along a line of squared lengths.** -/
theorem hasDerivAt_dihedral_inc (hn : 3 ≤ n) {ℓ₀ : Finset (TV n) → ℝ}
    (hK : LengthsNondeg (torusComplex n (by omega)) ℓ₀) (a : Finset (TV n) → ℝ) (c : TV n) (σ h : Fin 6) :
    HasDerivAt (fun ε => dihedralAt (lenLine ℓ₀ a ε) (tetV n c σ) (hing n c σ h))
      (Dh (incV n (fun e => ℓ₀ e ^ 2) c σ h, incV n a c σ h)) 0 := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hinge_distinct h
  have inj := fun {x y : Fin 4} (hxy : x ≠ y) (e : c + off n σ x = c + off n σ y) =>
    hxy (off_injective n (by omega) σ (add_left_cancel e))
  have ht : tetV n c σ ∈ (torusComplex n (by omega)).tets :=
    Finset.mem_image.2 ⟨(c, σ), Finset.mem_univ _, rfl⟩
  have := hasDerivAt_dihedralAt_line hK a (fun e => inj d1 e) (fun e => inj d2 e) (fun e => inj d3 e)
    (fun e => inj d4 e) (fun e => inj d5 e) (fun e => inj d6 e) (by rw [← tetV_eq_hinge n c σ h]; exact ht)
  rw [tetV_eq_hinge n c σ h]
  exact this

/-- **The derivative of the deficit angle of the edge `(z, k)` along a line of squared lengths.** -/
theorem hasDerivAt_deficit_edgeOf (hn : 3 ≤ n) {ℓ₀ : Finset (TV n) → ℝ}
    (hK : LengthsNondeg (torusComplex n (by omega)) ℓ₀) (a : Finset (TV n) → ℝ) (z : TV n) (k : Fin 7) :
    HasDerivAt (fun ε => deficit (torusComplex n (by omega)) (lenLine ℓ₀ a ε) (edgeOf n z k))
      (-∑ σ : Fin 6, ∑ h : Fin 6, if Cond (dirsN k) σ h then
        Dh (incV n (fun e => ℓ₀ e ^ 2) (z - off n σ (hP h)) σ h, incV n a (z - off n σ (hP h)) σ h) else 0) 0 := by
  have hfun : (fun ε => deficit (torusComplex n (by omega)) (lenLine ℓ₀ a ε) (edgeOf n z k)) =
      fun ε => 2 * π - ∑ σ : Fin 6, ∑ h : Fin 6, if Cond (dirsN k) σ h then
        dihedralAt (lenLine ℓ₀ a ε) (tetV n (z - off n σ (hP h)) σ) (hing n (z - off n σ (hP h)) σ h) else 0 := by
    funext ε
    rw [deficit, angleSum_edgeOf n hn]
  rw [hfun]
  have hs : HasDerivAt (fun ε => ∑ σ : Fin 6, ∑ h : Fin 6, if Cond (dirsN k) σ h then
        dihedralAt (lenLine ℓ₀ a ε) (tetV n (z - off n σ (hP h)) σ) (hing n (z - off n σ (hP h)) σ h) else 0)
      (∑ σ : Fin 6, ∑ h : Fin 6, if Cond (dirsN k) σ h then
        Dh (incV n (fun e => ℓ₀ e ^ 2) (z - off n σ (hP h)) σ h, incV n a (z - off n σ (hP h)) σ h) else 0) 0 := by
    refine HasDerivAt.fun_sum fun σ _ => HasDerivAt.fun_sum fun h _ => ?_
    by_cases hc : Cond (dirsN k) σ h
    · simp only [hc, ite_true]
      exact hasDerivAt_dihedral_inc n hn hK a _ σ h
    · simp [hc]; exact hasDerivAt_const _ _
  have := (hasDerivAt_const (0 : ℝ) (2 * π)).sub hs
  rw [zero_sub] at this
  exact this

end Torus

end Lightlike.Regge.Linear3
