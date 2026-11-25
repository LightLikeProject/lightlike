import Mathlib
import Lightlike.PL.ArcSet
import Lightlike.PL.Schoenflies.ChainCycle
import Lightlike.PL.Schoenflies.CircleLift

/-!
# A loop through a cycle of chains, with uniform timing

Row G3-188 (PL5), step 4e of the pass-4 plan.

* `exists_chain_param`: a simple chain from `a` to `b` is the image of `[0,1]` under a continuous
  map `γ` with `γ 0 = a`, `γ 1 = b`.
* `exists_block_glue`: continuous maps `γ j` of `[0,1]` with `γ j 1 = γ (j+1) 0` are glued on `k` equal blocks.
* `CycChains.exists_loop`: a trimmed cycle of `N` chains is traversed by a continuous `2π`-periodic map `G`
  that runs through the chain `T j` for `s ∈ [2π j/N, 2π (j+1)/N]`.
-/

open Set Lightlike.PL

namespace Lightlike.PL.Schoenflies

theorem exists_chain_param {c : List (ℝ × ℝ)} (hs : IsSimpleChain c) {a b : ℝ × ℝ} (h1 : c.head? = some a)
    (h2 : c.getLast? = some b) :
    ∃ γ : ℝ → ℝ × ℝ, Continuous γ ∧ γ 0 = a ∧ γ 1 = b ∧ γ '' Icc 0 1 = chainSet c := by
  rcases le_or_gt 2 c.length with hlen | hlen
  · obtain ⟨γ, hγc, -, h0, h1', himg⟩ := IsArc.chain hs h1 h2 hlen
    refine ⟨fun t => γ (Set.projIcc (0 : ℝ) 1 zero_le_one t), ?_, ?_, ?_, ?_⟩
    · exact hγc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        (fun t => (projIcc (0 : ℝ) 1 zero_le_one t).2)
    · simp [h0]
    · simp [h1']
    · rw [← himg]
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨_, (projIcc (0 : ℝ) 1 zero_le_one t).2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, ht, by simp [projIcc_of_mem _ ht]⟩
  · cases c with
    | nil => simp at h1
    | cons x t =>
      cases t with
      | nil =>
        simp only [List.head?_cons, Option.some.injEq] at h1
        simp only [List.getLast?_singleton, Option.some.injEq] at h2
        subst h1; subst h2
        refine ⟨fun _ => x, continuous_const, rfl, rfl, ?_⟩
        simp [chainSet]
      | cons y t' => simp at hlen

theorem exists_block_glue {X : Type*} [TopologicalSpace X] (γ : ℕ → ℝ → X) (hc : ∀ j, Continuous (γ j)) :
    ∀ m : ℕ, (∀ j, j + 1 < m + 1 → γ j 1 = γ (j + 1) 0) →
      ∃ F : ℝ → X, Continuous F ∧ ∀ j, j < m + 1 → ∀ τ ∈ Icc (0 : ℝ) 1,
        F ((j + τ) / ((m + 1 : ℕ) : ℝ)) = γ j τ := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨γ 0, hc 0, fun j hj τ hτ => ?_⟩
    obtain rfl : j = 0 := by omega
    simp
  | succ m ih =>
    intro hlink
    obtain ⟨F, hFc, hF⟩ := ih (fun j hj => hlink j (by omega))
    have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hm1 : (0 : ℝ) < (m + 1 + 1 : ℕ) := by positivity
    set k : ℝ := ((m + 1 : ℕ) : ℝ) with hk
    set k1 : ℝ := ((m + 1 + 1 : ℕ) : ℝ) with hk1
    have hk1k : k1 = k + 1 := by rw [hk1, hk]; push_cast; ring
    refine ⟨fun u => if u ≤ k / k1 then F (u * k1 / k) else γ (m + 1) (u * k1 - k), ?_, ?_⟩
    · refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
      · exact hFc.comp (by fun_prop)
      · exact (hc _).comp (by fun_prop)
      · intro u hu
        have e1 : u * k1 / k = 1 := by rw [hu]; field_simp
        have e2 : u * k1 - k = 0 := by rw [hu]; field_simp; ring
        rw [e1, e2]
        have := hF m (by omega) 1 ⟨zero_le_one, le_rfl⟩
        have e3 : ((m : ℝ) + 1) / k = 1 := by rw [hk]; push_cast; field_simp
        rw [e3] at this
        rw [this]
        exact hlink m (by omega)
    · intro j hj τ hτ
      by_cases hjm : j < m + 1
      · have hle : ((j : ℝ) + τ) / k1 ≤ k / k1 := by
          apply div_le_div_of_nonneg_right _ hm1.le
          have : (j : ℝ) + 1 ≤ k := by rw [hk]; exact_mod_cast hjm
          linarith [hτ.2]
        simp only [hle, ite_true]
        have : ((j : ℝ) + τ) / k1 * k1 / k = ((j : ℝ) + τ) / k := by field_simp
        rw [this]
        exact hF j hjm τ hτ
      · obtain rfl : j = m + 1 := by omega
        have hkk : ((m + 1 : ℕ) : ℝ) = k := hk.symm
        by_cases hτ0 : τ = 0
        · subst hτ0
          have hle : (((m + 1 : ℕ) : ℝ) + 0) / k1 ≤ k / k1 := by rw [hkk, add_zero]
          simp only [hle, ite_true]
          have e1 : (((m + 1 : ℕ) : ℝ) + 0) / k1 * k1 / k = 1 := by rw [hkk, add_zero]; field_simp
          rw [e1]
          have := hF m (by omega) 1 ⟨zero_le_one, le_rfl⟩
          have e3 : ((m : ℝ) + 1) / k = 1 := by rw [hk]; push_cast; field_simp
          rw [e3] at this
          rw [this]
          exact hlink m (by omega)
        · have hlt : ¬ (((m + 1 : ℕ) : ℝ) + τ) / k1 ≤ k / k1 := by
            rw [not_le, hkk]
            apply div_lt_div_of_pos_right _ hm1
            have : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτ0)
            linarith
          simp only [hlt, if_false]
          congr 1
          rw [hkk]; field_simp; ring

/-- **A loop through a trimmed cycle of chains, with uniform timing.** -/
theorem CycChains.exists_loop {N : ℕ} (hN : 1 ≤ N) {T : ℕ → List (ℝ × ℝ)} (hT : CycChains N T) :
    ∃ G : ℝ → ℝ × ℝ, Continuous G ∧ Function.Periodic G (2 * Real.pi) ∧
      (∀ j < N, ∀ s : ℝ, 2 * Real.pi * j / N ≤ s → s ≤ 2 * Real.pi * (j + 1) / N → G s ∈ chainSet (T j)) ∧
      range G = {x | ∃ j, j < N ∧ x ∈ chainSet (T j)} := by
  classical
  have hex : ∀ j : ℕ, ∃ γ : ℝ → ℝ × ℝ, Continuous γ ∧ (j < N → (T j).head? = some (γ 0) ∧
      (T j).getLast? = some (γ 1) ∧ γ '' Icc 0 1 = chainSet (T j)) := by
    intro j
    by_cases hj : j < N
    · obtain ⟨a, ha⟩ : ∃ a, (T j).head? = some a := by
        cases h : (T j).head? with
        | none => exact absurd h (hT.head j hj)
        | some a => exact ⟨a, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b, (T j).getLast? = some b := by
        cases h : (T j).getLast? with
        | none =>
          have : T j = [] := List.getLast?_eq_none_iff.1 h
          rw [this] at ha; simp at ha
        | some b => exact ⟨b, rfl⟩
      obtain ⟨γ, hγ, h0, h1, himg⟩ := exists_chain_param (hT.simple j hj) ha hb
      exact ⟨γ, hγ, fun _ => ⟨by rw [h0]; exact ha, by rw [h1]; exact hb, himg⟩⟩
    · exact ⟨fun _ => 0, continuous_const, fun h => absurd h hj⟩
  choose γ hγc hγs using hex
  have hlink : ∀ j, j + 1 < N → γ j 1 = γ (j + 1) 0 := by
    intro j hj
    have h1 := (hγs j (by omega)).2.1
    have h2 := (hγs (j + 1) hj).1
    rw [hT.link j hj, h2] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  obtain ⟨F, hFc, hF⟩ := exists_block_glue γ hγc m hlink
  have hclose : γ m 1 = γ 0 0 := by
    have h1 := (hγs m (by omega)).2.1
    have h2 := (hγs 0 (by omega)).1
    rw [show m = m + 1 - 1 by omega, hT.close] at h1
    rw [show m + 1 - 1 = m by omega] at h1
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  have hk : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hF0 : F 0 = γ 0 0 := by
    have := hF 0 (by omega) 0 ⟨le_rfl, zero_le_one⟩
    simpa using this
  have hF1 : F 1 = γ m 1 := by
    have := hF m (by omega) 1 ⟨zero_le_one, le_rfl⟩
    have e : ((m : ℝ) + 1) / ((m + 1 : ℕ) : ℝ) = 1 := by push_cast; field_simp
    rwa [e] at this
  set F' : ℝ → ℝ × ℝ := fun s => F (s / (2 * Real.pi)) with hF'
  have hpi : 0 < 2 * Real.pi := by positivity
  haveI : Fact (0 < 2 * Real.pi) := ⟨hpi⟩
  have hF'0 : F' 0 = F' (0 + 2 * Real.pi) := by
    simp only [hF', zero_add, zero_div, div_self hpi.ne']
    rw [hF0, hF1, hclose]
  have hF'c : Continuous F' := hFc.comp (by fun_prop)
  set G : ℝ → ℝ × ℝ := fun s => AddCircle.liftIco (2 * Real.pi) 0 F' (s : AddCircle (2 * Real.pi)) with hG
  have hGc : Continuous G :=
    (AddCircle.liftIco_continuous hF'0 hF'c.continuousOn).comp (AddCircle.continuous_mk' _)
  have hGper : Function.Periodic G (2 * Real.pi) := by
    intro s; simp only [hG]; rw [AddCircle.coe_add_period]
  have hGeq : ∀ s ∈ Icc 0 (2 * Real.pi), G s = F' s := by
    intro s hs
    rcases hs.2.eq_or_lt with h | h
    · rw [h]
      have : G (2 * Real.pi) = G 0 := by
        have := hGper 0; rw [zero_add] at this; exact this
      rw [this]
      simp only [hG]
      rw [AddCircle.liftIco_coe_apply (by simp [hpi])]
      simpa using hF'0
    · simp only [hG]
      exact AddCircle.liftIco_coe_apply (by simp [hs.1, h])
  have hblock : ∀ j < m + 1, ∀ s : ℝ, 2 * Real.pi * j / ((m + 1 : ℕ) : ℝ) ≤ s →
      s ≤ 2 * Real.pi * (j + 1) / ((m + 1 : ℕ) : ℝ) → G s ∈ chainSet (T j) := by
    intro j hj s hs1 hs2
    set τ : ℝ := ((m + 1 : ℕ) : ℝ) * s / (2 * Real.pi) - j with hτ
    have hτ1 : 0 ≤ τ := by
      rw [hτ, sub_nonneg, le_div_iff₀ hpi]
      rw [div_le_iff₀ hk] at hs1; linarith
    have hτ2 : τ ≤ 1 := by
      rw [hτ, sub_le_iff_le_add, div_le_iff₀ hpi]
      rw [le_div_iff₀ hk] at hs2; nlinarith
    have hs0 : s ∈ Icc 0 (2 * Real.pi) := by
      refine ⟨le_trans (by positivity) hs1, ?_⟩
      have : (j : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hj
      calc s ≤ 2 * Real.pi * (j + 1) / ((m + 1 : ℕ) : ℝ) := hs2
        _ ≤ 2 * Real.pi := by rw [div_le_iff₀ hk]; nlinarith [Real.pi_pos]
    rw [hGeq s hs0]
    have e : s / (2 * Real.pi) = ((j : ℝ) + τ) / ((m + 1 : ℕ) : ℝ) := by
      rw [hτ]; field_simp; ring
    simp only [hF']
    rw [e, hF j hj τ ⟨hτ1, hτ2⟩]
    rw [← (hγs j hj).2.2]
    exact ⟨τ, ⟨hτ1, hτ2⟩, rfl⟩
  refine ⟨G, hGc, hGper, hblock, ?_⟩
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    -- reduce to the fundamental interval
    set s' := toIcoMod Real.two_pi_pos 0 s with hs'
    have hmem : s' ∈ Ico 0 (0 + 2 * Real.pi) := toIcoMod_mem_Ico Real.two_pi_pos _ _
    have hGs : G s = G s' := by
      have : s' = s - toIcoDiv Real.two_pi_pos 0 s • (2 * Real.pi) := rfl
      rw [this, hGper.sub_zsmul_eq]
    rw [hGs]
    set j := Nat.floor (((m + 1 : ℕ) : ℝ) * s' / (2 * Real.pi)) with hj
    have hq0 : 0 ≤ ((m + 1 : ℕ) : ℝ) * s' / (2 * Real.pi) := by
      have := hmem.1; positivity
    have hq1 : ((m + 1 : ℕ) : ℝ) * s' / (2 * Real.pi) < ((m + 1 : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hpi]
      have := hmem.2; rw [zero_add] at this; nlinarith
    have hjN : j < m + 1 := by
      rw [hj, Nat.floor_lt hq0]; exact_mod_cast hq1
    have hj1 : (j : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * s' / (2 * Real.pi) := Nat.floor_le hq0
    have hj2 : ((m + 1 : ℕ) : ℝ) * s' / (2 * Real.pi) < j + 1 := Nat.lt_floor_add_one _
    refine ⟨j, hjN, hblock j hjN s' ?_ ?_⟩
    · rw [div_le_iff₀ hk]
      rw [le_div_iff₀ hpi] at hj1; nlinarith
    · rw [le_div_iff₀ hk]
      rw [div_lt_iff₀ hpi] at hj2; nlinarith
  · rintro ⟨j, hj, hx⟩
    rw [← (hγs j hj).2.2] at hx
    obtain ⟨τ, hτ, rfl⟩ := hx
    refine ⟨2 * Real.pi * (j + τ) / ((m + 1 : ℕ) : ℝ), ?_⟩
    have hs0 : 2 * Real.pi * (j + τ) / ((m + 1 : ℕ) : ℝ) ∈ Icc 0 (2 * Real.pi) := by
      refine ⟨by have := hτ.1; positivity, ?_⟩
      have : (j : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hj
      rw [div_le_iff₀ hk]; nlinarith [Real.pi_pos, hτ.2]
    rw [hGeq _ hs0]
    simp only [hF']
    have e : 2 * Real.pi * (j + τ) / ((m + 1 : ℕ) : ℝ) / (2 * Real.pi) = ((j : ℝ) + τ) / ((m + 1 : ℕ) : ℝ) := by
      field_simp
    rw [e, hF j hj τ hτ]

end Lightlike.PL.Schoenflies
