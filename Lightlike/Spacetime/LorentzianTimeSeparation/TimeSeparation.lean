import Lightlike.Spacetime.LorentzianTimeSeparation.LorentzLength
import Lightlike.Spacetime.Causal.ChainCurve

/-!
# Time separation (row G1-007)

The Lorentzian length (`Causal.lorentzLength`) does not change when the parameter of a curve is translated
(`Causal.lorentzLength_shift`); this is the step that lets two curves be glued end to end, for the reverse triangle
inequality of the time separation `d(p, q)`.

* `Causal.velocity_shift`: the velocity of `t ↦ γ (t + k)` is the velocity of `γ` at `t + k`;
* `Causal.lorentzLength_shift`: `L(t ↦ γ (t + k)) on [a - k, b - k] = L(γ) on [a, b]`;
* `Causal.lorentzLength_congr`: the length depends only on the values of the curve on `[a, b]`;
* `Causal.timeSep T p q`: the time separation `d(p, q)`, the supremum of the Lorentzian lengths of the
  future-directed timelike curves (`IsFutureTimelikeCurve`) from `p` to `q`, in `ℝ≥0∞` (`0` if there is none);
  `lorentzLength_le_timeSep`: the length of a curve is at most `d` of its endpoints;
* `Causal.timeSep_add_le`: the **reverse triangle inequality** `d(p, q) + d(q, r) ≤ d(p, r)` when there are timelike
  curves from `p` to `q` and from `q` to `r` (glue the second, translated, to the first).

Differences from the textbook `d`: the supremum is over `IsFutureTimelikeCurve` (a timelike velocity with a margin on
compact subintervals, `Lightlike/Spacetime/Causal/CausalCurve.lean`), not over piecewise `C¹` curves, and `d(p, q) = 0` (not `-∞` or
undefined) when `q ∉ I⁺(p)`. The value `+∞` is possible (no global hyperbolicity assumed).

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Section 6.2 (the length of a timelike curve is unchanged by reparametrisation); comparison with
  the page pending (not read).
-/

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} (g : LorentzianMetric I M n)

omit [IsManifold I ∞ M] in
/-- The velocity of a translated curve: where `γ` is differentiable within `[a, b]` at `t + k`, the curve
`s ↦ γ (s + k)` has the same velocity at `t` within `[a - k, b - k]`. -/
theorem velocity_shift {γ : ℝ → M} {a b k t : ℝ} (hab : a < b) (ht : t ∈ Icc (a - k) (b - k))
    (hd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Icc a b) (t + k)) :
    velocity I (fun s => γ (s + k)) (Icc (a - k) (b - k)) t = velocity I γ (Icc a b) (t + k) := by
  have hmem : ∀ s, s ∈ Icc (a - k) (b - k) → s + k ∈ Icc a b := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (a - k) (b - k)) t :=
    (uniqueDiffOn_Icc (by linarith) t ht).uniqueMDiffWithinAt
  have hτ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + k) (Icc (a - k) (b - k)) t := by
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    exact differentiableWithinAt_id.add_const k
  have hmaps : Icc (a - k) (b - k) ⊆ (fun s : ℝ => s + k) ⁻¹' Icc a b := fun s hs => hmem s hs
  have hc := mfderivWithin_comp t hd hτ hmaps hu
  have hd1 : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + k) (Icc (a - k) (b - k)) t 1 = 1 := by
    rw [mfderivWithin_eq_fderivWithin]
    have : HasFDerivWithinAt (fun s : ℝ => s + k) (ContinuousLinearMap.id ℝ ℝ)
        (Icc (a - k) (b - k)) t := (hasFDerivWithinAt_id t _).add_const k
    rw [this.fderivWithin (uniqueDiffOn_Icc (by linarith) t ht)]
    rfl
  unfold velocity
  rw [show (fun s => γ (s + k)) = γ ∘ (fun s : ℝ => s + k) from rfl, hc]
  exact congrArg (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) (t + k)) hd1

/-- **The Lorentzian length is invariant under translation of the parameter.** -/
theorem lorentzLength_shift {P : ∀ x : M, TangentSpace I x → Prop} {γ : ℝ → M} {a b : ℝ}
    (h : IsCurveWith (I := I) P γ (Icc a b)) (hab : a < b) (k : ℝ) :
    lorentzLength g (fun s => γ (s + k)) (a - k) (b - k) = lorentzLength g γ a b := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) k
  have hemb : MeasurableEmbedding (fun s : ℝ => s + k) := (Homeomorph.addRight k).measurableEmbedding
  have h1 : ∫⁻ t in (fun s : ℝ => s + k) ⁻¹' Icc a b, lorentzSpeed g γ (Icc a b) (t + k) =
      ∫⁻ t in Icc a b, lorentzSpeed g γ (Icc a b) t :=
    hmp.setLIntegral_comp_preimage_emb hemb (lorentzSpeed g γ (Icc a b)) (Icc a b)
  rw [show (fun s : ℝ => s + k) ⁻¹' Icc a b = Icc (a - k) (b - k) from by
    ext s; simp only [mem_preimage, mem_Icc]; constructor <;> intro hs <;> constructor <;> linarith [hs.1, hs.2]] at h1
  unfold lorentzLength
  rw [← h1]
  have h2 := (measurePreserving_add_right volume k).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Icc).1 h.ae_velocity)
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae h2] with t ht h3
  obtain ⟨hd, -⟩ := h3 (show t + k ∈ Icc a b from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  unfold lorentzSpeed
  rw [velocity_shift hab ht hd]

/-- The Lorentzian length depends only on the values of the curve on `[a, b]`. -/
theorem lorentzLength_congr {γ γ' : ℝ → M} {a b : ℝ} (_hab : a < b) (h : EqOn γ γ' (Icc a b)) :
    lorentzLength g γ a b = lorentzLength g γ' a b := by
  unfold lorentzLength
  refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  have hv : (velocity I γ' (Icc a b) t : E) = (velocity I γ (Icc a b) t : E) := by
    have e := mfderivWithin_congr (I := 𝓘(ℝ, ℝ)) (I' := I) (s := Icc a b) (x := t) (f₁ := γ') (f := γ)
      (fun y hy => (h hy).symm) (h ht).symm
    unfold velocity
    rw [e]
    rfl
  have hp : γ t = γ' t := h ht
  have key : ∀ x y : M, x = y → ∀ v : E, g.g x v v = g.g y v v := fun x y hxy v => by subst hxy; rfl
  have hs : g.g (γ t) (velocity I γ (Icc a b) t) (velocity I γ (Icc a b) t) =
      g.g (γ' t) (velocity I γ' (Icc a b) t) (velocity I γ' (Icc a b) t) := by
    have h1 := key (γ t) (γ' t) hp (velocity I γ (Icc a b) t)
    refine h1.trans ?_
    have h2 : (velocity I γ (Icc a b) t : E) = (velocity I γ' (Icc a b) t : E) := hv.symm
    exact congrArg (fun v : E => g.g (γ' t) v v) h2
  unfold lorentzSpeed
  rw [hs]

variable {g} (T : TimeOrientation g)

/-- The **time separation** (Lorentzian distance) `d(p, q)`: the supremum of the Lorentzian lengths of the
future-directed timelike curves from `p` to `q`, in `ℝ≥0∞`; the supremum of the empty set is `0`, so `d(p, q) = 0`
when there is no such curve. -/
def timeSep (p q : M) : ℝ≥0∞ :=
  sSup {x | ∃ (γ : ℝ → M) (a b : ℝ), a < b ∧ IsFutureTimelikeCurve T γ (Icc a b) ∧ γ a = p ∧ γ b = q ∧
    lorentzLength g γ a b = x}

/-- The length of a future-directed timelike curve from `p` to `q` is at most `d(p, q)`. -/
theorem lorentzLength_le_timeSep {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (h : IsFutureTimelikeCurve T γ (Icc a b)) :
    lorentzLength g γ a b ≤ timeSep T (γ a) (γ b) :=
  le_sSup ⟨γ, a, b, hab, h, rfl, rfl, rfl⟩

/-- **Reverse triangle inequality**: if there are future-directed timelike curves from `p` to `q` and from `q` to `r`,
then `d(p, q) + d(q, r) ≤ d(p, r)`. (Without the curves the left side can be positive while `d(p, r) = 0`: the
supremum over no curve is `0`.) -/
theorem timeSep_add_le {p q r : M}
    (hpq : ∃ (γ : ℝ → M) (a b : ℝ), a < b ∧ IsFutureTimelikeCurve T γ (Icc a b) ∧ γ a = p ∧ γ b = q)
    (hqr : ∃ (γ : ℝ → M) (a b : ℝ), a < b ∧ IsFutureTimelikeCurve T γ (Icc a b) ∧ γ a = q ∧ γ b = r) :
    timeSep T p q + timeSep T q r ≤ timeSep T p r := by
  unfold timeSep
  obtain ⟨γ₀, a₀, b₀, hab₀, h₀, hp₀, hq₀⟩ := hpq
  obtain ⟨γ₀', c₀, d₀, hcd₀, h₀', hq₀', hr₀⟩ := hqr
  have : Nonempty ↑{x | ∃ (γ : ℝ → M) (a b : ℝ), a < b ∧ IsFutureTimelikeCurve T γ (Icc a b) ∧ γ a = p ∧
      γ b = q ∧ lorentzLength g γ a b = x} := ⟨⟨_, γ₀, a₀, b₀, hab₀, h₀, hp₀, hq₀, rfl⟩⟩
  have : Nonempty ↑{x | ∃ (γ : ℝ → M) (a b : ℝ), a < b ∧ IsFutureTimelikeCurve T γ (Icc a b) ∧ γ a = q ∧
      γ b = r ∧ lorentzLength g γ a b = x} := ⟨⟨_, γ₀', c₀, d₀, hcd₀, h₀', hq₀', hr₀, rfl⟩⟩
  rw [sSup_eq_iSup', sSup_eq_iSup', ENNReal.iSup_add]
  refine iSup_le fun x => ?_
  rw [ENNReal.add_iSup]
  refine iSup_le fun y => ?_
  obtain ⟨x, γ₁, a, b, hab, h₁, hp, hq, hx⟩ := x
  obtain ⟨y, γ₂, c, d, hcd, h₂, hq', hr, hy⟩ := y
  have hbe : b < b + (d - c) := by linarith
  have h₃ := IsFutureTimelikeCurve.shift T h₂ hcd (c - b)
  rw [show c - (c - b) = b by ring, show d - (c - b) = b + (d - c) by ring] at h₃
  have hj : γ₁ b = (fun t => γ₂ (t + (c - b))) b := by
    simp only [add_sub_cancel]; rw [hq, hq']
  have hG := IsFutureTimelikeCurve.glue T h₁ h₃ hab hbe hj
  set G : ℝ → M := fun t => if t ≤ b then γ₁ t else γ₂ (t + (c - b)) with hGdef
  have hlen : lorentzLength g G a (b + (d - c)) = x + y := by
    rw [lorentzLength_add g hG.1 hab.le hbe.le]
    have e1 : lorentzLength g G a b = lorentzLength g γ₁ a b :=
      lorentzLength_congr g hab fun t ht => by simp [hGdef, ht.2]
    have e2 : lorentzLength g G b (b + (d - c)) = lorentzLength g (fun t => γ₂ (t + (c - b))) b (b + (d - c)) :=
      lorentzLength_congr g hbe fun t ht => by
        by_cases htb : t ≤ b
        · have : t = b := le_antisymm htb ht.1
          subst this
          simp [hGdef, hj]
        · simp [hGdef, htb]
    have e3 : lorentzLength g (fun t => γ₂ (t + (c - b))) b (b + (d - c)) = lorentzLength g γ₂ c d := by
      have := lorentzLength_shift g h₂.1 hcd (c - b)
      rwa [show c - (c - b) = b by ring, show d - (c - b) = b + (d - c) by ring] at this
    rw [e1, e2, e3, hx, hy]
  rw [← hlen]
  have := lorentzLength_le_timeSep T (γ := G) (a := a) (b := b + (d - c)) (by linarith) hG
  have hGa : G a = p := by simp [hGdef, hab.le, hp]
  have hGb : G (b + (d - c)) = r := by
    have : ¬ (b + (d - c) ≤ b) := by linarith
    simp only [hGdef, this, ↓reduceIte]
    rw [show b + (d - c) + (c - b) = d by ring]
    exact hr
  rw [hGa, hGb] at this
  exact this

end Causal

end Lightlike
