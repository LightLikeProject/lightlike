import Lightlike.PL.ArcTrim
import Lightlike.PL.K33

/-!
# No drawing of `K₃,₃` by continuous arcs

## Main results

* `ContDrawing`: a drawing of `K₃,₃` in the plane by continuous injective arcs.
* `no_K33`: there is none.
-/

open Set

namespace Lightlike.PL

/-- Two segments from the same centre to two different points of the sphere of radius `r` meet only
at the centre. -/
lemma segment_inter_sphere {c q q' y : ℝ × ℝ} {r : ℝ} (hr : 0 < r) (hq : dist q c = r)
    (hq' : dist q' c = r) (hne : q ≠ q') (h1 : y ∈ segment ℝ c q) (h2 : y ∈ segment ℝ c q') :
    y = c := by
  rw [segment_eq_image'] at h1 h2
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := h1
  obtain ⟨s', ⟨hs0', hs1'⟩, hs⟩ := h2
  have hn : s * r = s' * r := by
    have := congrArg (fun z => ‖z - c‖) hs
    simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0, Real.norm_of_nonneg hs0'] at this
    rw [← dist_eq_norm, ← dist_eq_norm, hq, hq'] at this
    exact this.symm
  have hss : s = s' := mul_right_cancel₀ hr.ne' hn
  subst hss
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]; simp
  · exfalso
    apply hne
    have : s • (q - c) = s • (q' - c) := by
      have := hs
      simpa using this.symm
    have := smul_right_injective _ h.ne' this
    simpa using this

/-- A **drawing of `K₃,₃` by continuous arcs**: six distinct points `u i`, `v j` and nine injective
continuous arcs `γ i j : [0, 1] → ℝ²` from `u i` to `v j` that meet only in common endpoints. -/
structure ContDrawing where
  /-- The three points of the first class. -/
  u : Fin 3 → ℝ × ℝ
  /-- The three points of the second class. -/
  v : Fin 3 → ℝ × ℝ
  /-- The arc from `u i` to `v j`, as a map on `[0, 1]`. -/
  γ : Fin 3 → Fin 3 → ℝ → ℝ × ℝ
  /-- Each arc is continuous. -/
  cont : ∀ i j, ContinuousOn (γ i j) (Icc 0 1)
  /-- Each arc is injective. -/
  inj : ∀ i j, InjOn (γ i j) (Icc 0 1)
  /-- Each arc starts at `u i`. -/
  start : ∀ i j, γ i j 0 = u i
  /-- Each arc ends at `v j`. -/
  stop : ∀ i j, γ i j 1 = v j
  /-- Two different arcs meet only in common endpoints. -/
  disj : ∀ i j i' j', (i, j) ≠ (i', j') →
    γ i j '' Icc 0 1 ∩ γ i' j' '' Icc 0 1 ⊆ {u i, v j} ∩ {u i', v j'}
  /-- The three points of the first class are distinct. -/
  inj_u : Function.Injective u
  /-- The three points of the second class are distinct. -/
  inj_v : Function.Injective v
  /-- The two classes are disjoint. -/
  uv_ne : ∀ i j, u i ≠ v j

namespace ContDrawing

variable (D : ContDrawing)

/-- The six points, indexed by the two classes. -/
def w : Fin 3 ⊕ Fin 3 → ℝ × ℝ := Sum.elim D.u D.v

lemma w_inj : Function.Injective D.w := by
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (D.inj_u h)
  · exact absurd h (D.uv_ne _ _)
  · exact absurd h.symm (D.uv_ne _ _)
  · exact congrArg Sum.inr (D.inj_v h)

/-- The ends of the edge `e`: the vertex `inl e.1` for `false`, `inr e.2` for `true`. -/
def ep (e : Fin 3 × Fin 3) : Bool → Fin 3 ⊕ Fin 3
  | false => Sum.inl e.1
  | true => Sum.inr e.2

/-- A vertex that is not an end of the edge `e` is not on the arc `e`. -/
lemma w_notMem {e : Fin 3 × Fin 3} {x : Fin 3 ⊕ Fin 3} (h : ∀ k, x ≠ ep e k) :
    D.w x ∉ D.γ e.1 e.2 '' Icc 0 1 := by
  intro hx
  rcases x with i | j
  · have h0 : D.w (Sum.inl i) ∈ D.γ i 0 '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, D.start i 0⟩
    have hne : (e.1, e.2) ≠ (i, 0) := fun h' => h false (by simp [ep]; exact (congrArg Prod.fst h').symm)
    have := D.disj _ _ _ _ hne ⟨hx, h0⟩
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at this
    rcases this.1 with h1 | h1
    · exact h false (by simp [ep]; exact D.inj_u h1)
    · exact D.uv_ne _ _ (by simpa [w] using h1)
  · have h0 : D.w (Sum.inr j) ∈ D.γ 0 j '' Icc 0 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, D.stop 0 j⟩
    have hne : (e.1, e.2) ≠ (0, j) := fun h' => h true (by simp [ep]; exact (congrArg Prod.snd h').symm)
    have := D.disj _ _ _ _ hne ⟨hx, h0⟩
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at this
    rcases this.1 with h1 | h1
    · exact D.uv_ne _ _ (by simpa [w] using h1.symm)
    · exact h true (by simp [ep]; exact D.inj_v h1)

end ContDrawing

end Lightlike.PL
