import Lightlike.Spacetime.Causal.CurveOps
import Lightlike.Spacetime.Causal.Ladder

/-!
# Basic properties of the chronological and causal futures

The inclusion `I⁺(x) ⊆ J⁺(x)`, the reflexivity `x ∈ J⁺(x)`, the transitivity of `J⁺` and of `I⁺`,
and that causality implies chronology. These are the first statements of the causal theory of a
time-oriented Lorentzian manifold; the proofs glue and restrict locally Lipschitz curves
(`Lightlike/Spacetime/Causal/CurveOps.lean`).

## Main statements

* `Causal.chron_subset_causal`: `I⁺(x) ⊆ J⁺(x)`.
* `Causal.self_mem_causalFuture`: `x ∈ J⁺(x)`.
* `Causal.causal_trans`, `Causal.chron_trans`: transitivity.
* `Causal.chronological_of_causal`: causality implies chronology.

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Chapter 6 (causal structure); the comparison of each statement with the book at its
  location is pending (the book has not been read at a location).
* R. Penrose, *Techniques of Differential Topology in Relativity*, SIAM (1972), Chapter 2.
-/

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- A future-directed timelike vector is future-directed causal: it is nonzero because
`g(v, v) < 0`. -/
theorem TimeOrientation.isFutureCausal_of_isFutureTimelike {x : M} {v : TangentSpace I x}
    (h : T.IsFutureTimelike v) : T.IsFutureCausal v := by
  refine ⟨?_, h.1.le, h.2⟩
  rintro rfl
  exact absurd h.1 (by simp)

omit [IsManifold I ∞ M] in
/-- A curve whose velocity satisfies `P` almost everywhere satisfies every weaker condition `Q`. -/
theorem IsCurveWith.mono_velocity {P Q : ∀ x : M, TangentSpace I x → Prop} {γ : ℝ → M} {s : Set ℝ}
    (h : IsCurveWith (I := I) P γ s) (hPQ : ∀ x v, P x v → Q x v) : IsCurveWith (I := I) Q γ s :=
  ⟨h.ordConnected, h.lipschitz, h.ae_velocity.mono fun _ ht => ⟨ht.1, hPQ _ _ ht.2⟩⟩

/-- A future-directed timelike curve is a future-directed causal curve. -/
theorem isFutureCausalCurve_of_isFutureTimelikeCurve {γ : ℝ → M} {s : Set ℝ}
    (h : IsFutureTimelikeCurve T γ s) : IsFutureCausalCurve T γ s :=
  IsCurveWith.mono_velocity h fun _ _ hv => T.isFutureCausal_of_isFutureTimelike hv

/-- **Timelike futures are causal futures: `I⁺(x) ⊆ J⁺(x)`.** (Hawking–Ellis, Chapter 6; the
comparison with the book at its location is pending.) -/
theorem chron_subset_causal (x : M) : chronFuture T x ⊆ causalFuture T x := by
  rintro y ⟨γ, a, b, hab, h, h1, h2⟩
  exact ⟨γ, a, b, hab.le, isFutureCausalCurve_of_isFutureTimelikeCurve T h, h1, h2⟩

omit [IsManifold I ∞ M] in
/-- A constant curve on a degenerate interval satisfies any velocity condition: the interval is a
null set. -/
theorem isCurveWith_const (P : ∀ x : M, TangentSpace I x → Prop) (x : M) (a : ℝ) :
    IsCurveWith (I := I) P (fun _ => x) (Icc a a) := by
  refine ⟨ordConnected_Icc, ?_, ?_⟩
  · intro t _
    refine ⟨0, univ, univ_mem, fun _ _ => mem_extChartAt_source x, ?_⟩
    exact (LipschitzWith.const _).lipschitzOnWith
  · have : (volume : Measure ℝ).restrict (Icc a a) = 0 :=
      Measure.restrict_eq_zero.2 (by simp)
    rw [this, ae_zero]
    exact eventually_bot

/-- **A point is in its own causal future: `x ∈ J⁺(x)`.** (Hawking–Ellis, Chapter 6; the
comparison with the book at its location is pending.) -/
theorem self_mem_causalFuture (x : M) : x ∈ causalFuture T x :=
  ⟨fun _ => x, 0, 0, le_rfl, isCurveWith_const _ x 0, rfl, rfl⟩

omit [IsManifold I ∞ M] in
/-- **Concatenation** of two curves with velocity in `P`, both on nondegenerate intervals, the first
ending where the second starts: one curve from the start of the first to the end of the second. -/
theorem IsCurveWith.trans {P : ∀ x : M, TangentSpace I x → Prop} {γ₁ γ₂ : ℝ → M} {a b c d : ℝ}
    (h₁ : IsCurveWith (I := I) P γ₁ (Icc a b)) (h₂ : IsCurveWith (I := I) P γ₂ (Icc c d))
    (hab : a < b) (hcd : c < d) (hj : γ₁ b = γ₂ c) :
    ∃ (G : ℝ → M) (e : ℝ), a < e ∧ IsCurveWith (I := I) P G (Icc a e) ∧ G a = γ₁ a ∧
      G e = γ₂ d := by
  have h₃ := h₂.shift hcd (c - b)
  have e1 : c - (c - b) = b := by ring
  have e2 : d - (c - b) = b + (d - c) := by ring
  rw [e1, e2] at h₃
  have hbe : b < b + (d - c) := by linarith
  refine ⟨_, b + (d - c), hab.trans hbe, h₁.glue h₃ hab hbe (by simpa using hj), ?_, ?_⟩
  · simp [hab.le]
  · have : ¬ (b + (d - c) ≤ b) := by linarith
    simp only [this, ite_false]
    congr 1
    ring

/-- **The causal future is transitive: `y ∈ J⁺(x)` and `z ∈ J⁺(y)` give `z ∈ J⁺(x)`.**
(Hawking–Ellis, Chapter 6; the comparison with the book at its location is pending.) -/
theorem causal_trans {x y z : M} (hxy : y ∈ causalFuture T x) (hyz : z ∈ causalFuture T y) :
    z ∈ causalFuture T x := by
  obtain ⟨γ₁, a, b, hab, h₁, e1, e2⟩ := hxy
  obtain ⟨γ₂, c, d, hcd, h₂, e3, e4⟩ := hyz
  rcases hab.eq_or_lt with rfl | hab'
  · have : x = y := by rw [← e1, ← e2]
    subst this
    exact ⟨γ₂, c, d, hcd, h₂, e3, e4⟩
  rcases hcd.eq_or_lt with rfl | hcd'
  · have : y = z := by rw [← e3, ← e4]
    subst this
    exact ⟨γ₁, a, b, hab, h₁, e1, e2⟩
  obtain ⟨G, e, hae, hG, hG1, hG2⟩ := IsCurveWith.trans h₁ h₂ hab' hcd' (e2.trans e3.symm)
  exact ⟨G, a, e, hae.le, hG, hG1.trans e1, hG2.trans e4⟩

/-- **The chronological future is transitive: `y ∈ I⁺(x)` and `z ∈ I⁺(y)` give `z ∈ I⁺(x)`.**
(Hawking–Ellis, Chapter 6; the comparison with the book at its location is pending.) -/
theorem chron_trans {x y z : M} (hxy : y ∈ chronFuture T x) (hyz : z ∈ chronFuture T y) :
    z ∈ chronFuture T x := by
  obtain ⟨γ₁, a, b, hab, h₁, e1, e2⟩ := hxy
  obtain ⟨γ₂, c, d, hcd, h₂, e3, e4⟩ := hyz
  obtain ⟨G, e, hae, hG, hG1, hG2⟩ := IsCurveWith.trans h₁ h₂ hab hcd (e2.trans e3.symm)
  exact ⟨G, a, e, hae, hG, hG1.trans e1, hG2.trans e4⟩

/-- A future-directed timelike curve on `[a, b]`, `a < b`, is not constant: some value differs from
`x`, whatever `x` is. Its velocity is nonzero almost everywhere, and a constant curve has velocity
zero. -/
theorem exists_ne_of_isFutureTimelikeCurve {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (h : IsFutureTimelikeCurve T γ (Icc a b)) (x : M) : ∃ t ∈ Icc a b, γ t ≠ x := by
  by_contra hcon
  push Not at hcon
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc a b → False := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 h.ae_velocity] with t ht hmem
    obtain ⟨hd, hv⟩ := ht hmem
    have hv0 : velocity I γ (Icc a b) t = 0 := by
      unfold velocity
      rw [mfderivWithin_congr (f := fun _ : ℝ => x) (fun s hs => hcon s hs) (hcon t hmem)]
      have : mfderivWithin 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) (Icc a b) t = 0 := mfderivWithin_const
      rw [this]
      rfl
    rw [hv0] at hv
    exact absurd hv.1 (by simp)
  have h2 : volume (Icc a b) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h1] with t ht hmem using ht hmem
  rw [Real.volume_Icc] at h2
  simp at h2
  linarith

/-- **Causality implies chronology.** If `x ∈ I⁺(x)`, a timelike curve from `x` to `x` passes
through a point `y ≠ x`, and then `y ∈ J⁺(x)` and `x ∈ J⁺(y)` contradict causality. (Hawking–Ellis,
Chapter 6; the comparison with the book at its location is pending.) -/
theorem chronological_of_causal (h : IsCausal T) : IsChronological T := by
  intro x hx
  obtain ⟨γ, a, b, hab, hγ, e1, e2⟩ := hx
  obtain ⟨t, ht, hne⟩ := exists_ne_of_isFutureTimelikeCurve T hab hγ x
  have hta : a < t := lt_of_le_of_ne ht.1 (fun h' => hne (h' ▸ e1))
  have htb : t < b := lt_of_le_of_ne ht.2 (fun h' => hne (h' ▸ e2))
  have hc := isFutureCausalCurve_of_isFutureTimelikeCurve T hγ
  have hy : γ t ∈ causalFuture T x :=
    ⟨γ, a, t, hta.le, IsCurveWith.mono hc le_rfl htb.le hta, e1, rfl⟩
  have hx' : x ∈ causalFuture T (γ t) :=
    ⟨γ, t, b, htb.le, IsCurveWith.mono hc hta.le le_rfl htb, rfl, e2⟩
  exact hne (h x (γ t) hy hx').symm

end Causal

end Lightlike
