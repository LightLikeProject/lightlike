import Mathlib
import Lightlike.PL.ArcSet
import Lightlike.PL.LoopErase
import Lightlike.PL.Schoenflies.ChainHit
import Lightlike.PL.Schoenflies.JordanInnerULC

/-!
# Simple chains in the inside that follow an arc of a Jordan curve

Row G3-188 (PL5), step 4e of the pass-4 plan.  `exists_block_chain`: for `η > 0` and parameters `a ≤ b`, two
points `za`, `zb` of the open inner region `U`, close to `f(exp a)`, `f(exp b)`, are joined by a simple chain
in `U` all of whose points are within `η` of the arc `s ↦ f (exp s)`, `s ∈ [a, b]`.
-/

open Set Metric Lightlike.PL

namespace Lightlike.PL.Schoenflies

theorem exists_chain_of_joinedIn {S : Set (ℝ × ℝ)} (hS : IsOpen S) {x y : ℝ × ℝ} (h : JoinedIn S x y) :
    ∃ l : List (ℝ × ℝ), l.head? = some x ∧ l.getLast? = some y ∧ chainSet l ⊆ S := by
  have hx : x ∈ S := h.source_mem
  have hpc := isPathConnected_pathComponentIn hx
  obtain ⟨l, h1, h2, h3⟩ := exists_chain_in_open (hS.pathComponentIn x) hpc.isConnected.isPreconnected
    (mem_pathComponentIn_self hx) (show y ∈ pathComponentIn S x from h)
  exact ⟨l, h1, h2, h3.trans pathComponentIn_subset⟩

/-- Concatenation of chains between consecutive points. -/
theorem exists_chain_along (z : ℕ → ℝ × ℝ) (S : ℕ → Set (ℝ × ℝ))
    (h : ∀ i, ∃ l : List (ℝ × ℝ), l.head? = some (z i) ∧ l.getLast? = some (z (i + 1)) ∧ chainSet l ⊆ S i) :
    ∀ M : ℕ, ∃ l : List (ℝ × ℝ), l.head? = some (z 0) ∧ l.getLast? = some (z (M + 1)) ∧
      ∀ x ∈ chainSet l, ∃ i, i ≤ M ∧ x ∈ S i := by
  intro M
  induction M with
  | zero =>
    obtain ⟨l, h1, h2, h3⟩ := h 0
    exact ⟨l, h1, h2, fun x hx => ⟨0, le_rfl, h3 hx⟩⟩
  | succ M ih =>
    obtain ⟨l, h1, h2, h3⟩ := ih
    obtain ⟨l', g1, g2, g3⟩ := h (M + 1)
    obtain ⟨m, hm⟩ : ∃ m, l = m ++ [z (M + 1)] := by
      rcases List.eq_nil_or_concat l with rfl | ⟨m, y, rfl⟩
      · simp at h1
      · refine ⟨m, ?_⟩
        simp only [List.concat_eq_append] at h2 ⊢
        have : (m ++ [y]).getLast? = some y := by simp
        rw [this] at h2; rw [Option.some.inj h2]
    obtain ⟨r, hr⟩ : ∃ r, l' = z (M + 1) :: r := by
      cases l' with
      | nil => simp at g1
      | cons x r => simp at g1; subst g1; exact ⟨r, rfl⟩
    refine ⟨m ++ z (M + 1) :: r, ?_, ?_, ?_⟩
    · rw [hm] at h1
      cases m with
      | nil => simpa using h1
      | cons x t => simpa using h1
    · rw [List.getLast?_append_of_ne_nil _ (by simp), ← hr]; exact g2
    · intro x hx
      rw [chainSet_append] at hx
      rcases hx with hx | hx
      · rw [← hm] at hx
        obtain ⟨i, hi, hxi⟩ := h3 x hx
        exact ⟨i, by omega, hxi⟩
      · rw [← hr] at hx
        exact ⟨M + 1, le_rfl, g3 hx⟩

theorem exists_block_chain {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f)
    {U : Set (ℝ × ℝ)} (hUo : IsOpen U) (hUc : IsConnected U) (hcl : closure U = U ∪ range f)
    (hUJ : Disjoint U (range f)) {η : ℝ} (hη : 0 < η) {a b : ℝ} (hab : a ≤ b)
    :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {za zb : ℝ × ℝ}, za ∈ U → zb ∈ U → dist za (f (Circle.exp a)) < ρ →
      dist zb (f (Circle.exp b)) < ρ →
      ∃ l : List (ℝ × ℝ), IsSimpleChain l ∧ l.head? = some za ∧ l.getLast? = some zb ∧ chainSet l ⊆ U ∧
        ∀ x ∈ chainSet l, ∃ s ∈ Icc a b, dist x (f (Circle.exp s)) < η := by
  obtain ⟨δ, hδ, hulc⟩ := jordan_inner_ulc hc hi hUo hUc hcl hUJ (η / 2) (by positivity)
  set ρ : ℝ := min (δ / 3) (η / 4) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
  refine ⟨ρ, hρ0, fun {za zb} hza hzb hda hdb => ?_⟩
  -- uniform continuity of the curve on `[a, b]`
  have hg : ContinuousOn (fun s : ℝ => f (Circle.exp s)) (Icc a b) :=
    (hc.comp Circle.exp.continuous).continuousOn
  obtain ⟨w, hw, hwc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) ρ hρ0
  -- the subdivision
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (b - a) / (M + 1 : ℝ) < w := by
    obtain ⟨M, hM⟩ := exists_nat_gt ((b - a) / w)
    refine ⟨M, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hw).1 hM
    nlinarith [Nat.cast_nonneg (α := ℝ) M]
  set s : ℕ → ℝ := fun i => a + i * ((b - a) / (M + 1 : ℝ)) with hs
  have hs0 : s 0 = a := by simp [hs]
  have hstepnn : 0 ≤ (b - a) / (M + 1 : ℝ) := div_nonneg (by linarith) (by positivity)
  have hsM : s (M + 1) = b := by
    simp only [hs]; push_cast; field_simp; ring
  have hsmem : ∀ i, i ≤ M + 1 → s i ∈ Icc a b := by
    intro i hile
    refine ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hstepnn), ?_⟩
    have hle : (i : ℝ) ≤ M + 1 := by exact_mod_cast hile
    calc s i = a + i * ((b - a) / (M + 1 : ℝ)) := rfl
      _ ≤ a + (M + 1 : ℝ) * ((b - a) / (M + 1 : ℝ)) := by gcongr
      _ = b := by field_simp; ring
  -- points of `U` near the curve
  have hnear : ∀ i, ∃ z, z ∈ U ∧ dist z (f (Circle.exp (s i))) < ρ := by
    intro i
    have : f (Circle.exp (s i)) ∈ closure U := by rw [hcl]; exact Or.inr ⟨_, rfl⟩
    obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.1 this ρ hρ0
    exact ⟨z, hz, by rw [dist_comm]; exact hd⟩
  choose z0 hz0U hz0d using hnear
  set z : ℕ → ℝ × ℝ := fun i => if i = 0 then za else if i = M + 1 then zb else z0 i with hz
  have hzU : ∀ i, z i ∈ U := by
    intro i; simp only [hz]; split_ifs
    · exact hza
    · exact hzb
    · exact hz0U i
  have hzd : ∀ i, i ≤ M + 1 → dist (z i) (f (Circle.exp (s i))) < ρ := by
    intro i hi; simp only [hz]; split_ifs with h1 h2
    · subst h1; rw [hs0]; exact hda
    · subst h2; rw [hsM]; exact hdb
    · exact hz0d i
  -- the chains between consecutive points
  have hstep : ∀ i, i ≤ M → ∃ l : List (ℝ × ℝ), l.head? = some (z i) ∧ l.getLast? = some (z (i + 1)) ∧
      chainSet l ⊆ U ∩ ball (z i) (η / 2) := by
    intro i hi
    have hclose : dist (z i) (z (i + 1)) < δ := by
      have h1 := hzd i (by omega)
      have h2 := hzd (i + 1) (by omega)
      have h3 : dist (f (Circle.exp (s i))) (f (Circle.exp (s (i + 1)))) < ρ := by
        apply hwc _ (hsmem i (by omega)) _ (hsmem (i + 1) (by omega))
        rw [Real.dist_eq]
        simp only [hs]
        push_cast
        have : a + (i : ℝ) * ((b - a) / (M + 1 : ℝ)) - (a + ((i : ℝ) + 1) * ((b - a) / (M + 1 : ℝ))) =
          -((b - a) / (M + 1 : ℝ)) := by ring
        rw [this, abs_neg, abs_of_nonneg (by apply div_nonneg <;> linarith [Nat.cast_nonneg (α := ℝ) M])]
        exact hM
      have hρδ : ρ ≤ δ / 3 := min_le_left _ _
      calc dist (z i) (z (i + 1)) ≤ dist (z i) (f (Circle.exp (s i))) +
            dist (f (Circle.exp (s i))) (z (i + 1)) := dist_triangle _ _ _
        _ ≤ dist (z i) (f (Circle.exp (s i))) + (dist (f (Circle.exp (s i))) (f (Circle.exp (s (i + 1)))) +
            dist (f (Circle.exp (s (i + 1)))) (z (i + 1))) := by
          gcongr; exact dist_triangle _ _ _
        _ < δ := by rw [dist_comm (f (Circle.exp (s (i + 1)))) (z (i + 1))]; linarith
    exact exists_chain_of_joinedIn (hUo.inter isOpen_ball) (hulc _ (hzU i) _ (hzU (i + 1)) hclose)
  have hstep' : ∀ i, ∃ l : List (ℝ × ℝ), l.head? = some (z i) ∧ l.getLast? = some (z (i + 1)) ∧
      chainSet l ⊆ (if i ≤ M then U ∩ ball (z i) (η / 2) else univ) := by
    intro i
    by_cases hi : i ≤ M
    · obtain ⟨l, h1, h2, h3⟩ := hstep i hi
      exact ⟨l, h1, h2, by simpa [hi] using h3⟩
    · exact ⟨[z i, z (i + 1)], rfl, rfl, by simp [hi]⟩
  obtain ⟨l, h1, h2, h3⟩ := exists_chain_along z (fun i => if i ≤ M then U ∩ ball (z i) (η / 2) else univ) hstep' M
  obtain ⟨t, ht, ht1, ht2, ht3⟩ := exists_simple_sub l (z 0) (z (M + 1)) h1 h2
  refine ⟨t, ht, ?_, ?_, ?_, ?_⟩
  · simpa [hz] using ht1
  · simpa [hz] using ht2
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := h3 x (ht3 hx)
    simp only [hi, if_true] at hxi
    exact hxi.1
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := h3 x (ht3 hx)
    simp only [hi, if_true] at hxi
    refine ⟨s i, hsmem i (by omega), ?_⟩
    have h1 := mem_ball.1 hxi.2
    have h2 := hzd i (by omega)
    have hρη : ρ ≤ η / 4 := min_le_right _ _
    calc dist x (f (Circle.exp (s i))) ≤ dist x (z i) + dist (z i) (f (Circle.exp (s i))) := dist_triangle _ _ _
      _ < η := by linarith

end Lightlike.PL.Schoenflies
