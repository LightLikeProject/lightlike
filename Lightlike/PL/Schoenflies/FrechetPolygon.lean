import Mathlib
import Lightlike.PL.Schoenflies.BlockChain
import Lightlike.PL.Schoenflies.ChainCycle
import Lightlike.PL.Schoenflies.CycPolygon
import Lightlike.PL.Schoenflies.BlockLoop
import Lightlike.PL.Schoenflies.MemInsideClose

/-!
# Polygons in the inside that follow a Jordan curve

Row G3-188 (PL5), step 4 of the pass-4 plan.  Preliminaries: separation of non-adjacent arcs of the curve.
-/

open Set Metric Lightlike.PL

namespace Lightlike.PL.Schoenflies

/-- Two disjoint compact sets are at positive distance. -/
lemma exists_pos_sep {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂) (hd : Disjoint K₁ K₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K₁, ∀ y ∈ K₂, δ ≤ dist x y := by
  by_cases hne : (K₁ ×ˢ K₂).Nonempty
  · obtain ⟨p, hp, hmin⟩ := (h₁.prod h₂).exists_isMinOn hne (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => dist p.1 p.2)
      (by fun_prop)
    refine ⟨dist p.1 p.2, ?_, fun x hx y hy => hmin (show (x, y) ∈ K₁ ×ˢ K₂ from ⟨hx, hy⟩)⟩
    rw [dist_pos]
    intro h
    exact Set.disjoint_left.1 hd hp.1 (h ▸ hp.2)
  · refine ⟨1, one_pos, fun x hx y hy => absurd ⟨(x, y), hx, hy⟩ hne⟩

/-- A real number in `[0, 2π)` lies in one of the `N` equal blocks. -/
lemma exists_block_of_mem {N : ℕ} (hN : 1 ≤ N) {s : ℝ} (hs : s ∈ Ico 0 (2 * Real.pi)) :
    ∃ j : ℕ, j < N ∧ 2 * Real.pi * j / N ≤ s ∧ s ≤ 2 * Real.pi * (j + 1) / N := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hk : (0 : ℝ) < N := by exact_mod_cast hN
  set j := Nat.floor ((N : ℝ) * s / (2 * Real.pi)) with hj
  have hq0 : 0 ≤ (N : ℝ) * s / (2 * Real.pi) := by have := hs.1; positivity
  have hq1 : (N : ℝ) * s / (2 * Real.pi) < N := by
    rw [div_lt_iff₀ hpi]; nlinarith [hs.2]
  have hjN : j < N := by rw [hj, Nat.floor_lt hq0]; exact_mod_cast hq1
  have hj1 : (j : ℝ) ≤ (N : ℝ) * s / (2 * Real.pi) := Nat.floor_le hq0
  have hj2 : (N : ℝ) * s / (2 * Real.pi) < j + 1 := Nat.lt_floor_add_one _
  refine ⟨j, hjN, ?_, ?_⟩
  · rw [div_le_iff₀ hk]; rw [le_div_iff₀ hpi] at hj1; nlinarith
  · rw [le_div_iff₀ hk]; rw [div_lt_iff₀ hpi] at hj2; nlinarith

/-- Non-adjacent arcs of the curve (parameter blocks `j` and `k`, `j + 2 ≤ k`, not the first and the last) are at
a positive distance, uniformly. -/
lemma exists_arc_sep {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f) {N : ℕ}
    (hN : 1 ≤ N) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j k : ℕ, j < N → k < N → j + 2 ≤ k → ¬ (j = 0 ∧ k = N - 1) →
      ∀ s ∈ Icc (2 * Real.pi * j / N) (2 * Real.pi * (j + 1) / N),
      ∀ s' ∈ Icc (2 * Real.pi * k / N) (2 * Real.pi * (k + 1) / N),
        ε ≤ dist (f (Circle.exp s)) (f (Circle.exp s')) := by
  classical
  have hpi : 0 < 2 * Real.pi := by positivity
  have hk : (0 : ℝ) < N := by exact_mod_cast hN
  set F : ℝ → ℝ × ℝ := fun s => f (Circle.exp s) with hF
  have hFc : Continuous F := hc.comp Circle.exp.continuous
  set I : ℕ → Set ℝ := fun j => Icc (2 * Real.pi * j / N) (2 * Real.pi * (j + 1) / N) with hI
  have hdisj : ∀ j k : ℕ, j < N → k < N → j + 2 ≤ k → ¬ (j = 0 ∧ k = N - 1) →
      Disjoint (F '' I j) (F '' I k) := by
    intro j k hj hkN hjk hne
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ ⟨s', hs', hss'⟩
    have h1 : Circle.exp s' = Circle.exp s := hi hss'
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.1 h1
    -- `s' = s + n * 2π`
    have hjk' : (j : ℝ) + 2 ≤ k := by exact_mod_cast hjk
    have hlt : s < s' := by
      have e1 : s ≤ 2 * Real.pi * (j + 1) / N := hs.2
      have e2 : 2 * Real.pi * k / N ≤ s' := hs'.1
      have e3 : 2 * Real.pi * (j + 1) / N < 2 * Real.pi * k / N := by
        apply div_lt_div_of_pos_right _ hk
        nlinarith
      linarith
    have hn1 : 1 ≤ n := by
      by_contra hn0
      push Not at hn0
      have : n ≤ 0 := by omega
      have : (n : ℝ) ≤ 0 := by exact_mod_cast this
      nlinarith
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hdiff : 2 * Real.pi ≤ s' - s := by rw [hn]; nlinarith
    have hup : s' - s ≤ 2 * Real.pi * ((k : ℝ) + 1 - j) / N := by
      have e1 : s ≥ 2 * Real.pi * j / N := hs.1
      have e2 : s' ≤ 2 * Real.pi * (k + 1) / N := hs'.2
      have : 2 * Real.pi * (k + 1) / N - 2 * Real.pi * j / N = 2 * Real.pi * ((k : ℝ) + 1 - j) / N := by ring
      linarith
    have hkj : (k : ℝ) + 1 - j ≤ N - 1 := by
      have : k + 1 - j ≤ N - 1 := by
        by_contra hcon
        push Not at hcon
        exact hne ⟨by omega, by omega⟩
      have h2 : j ≤ k + 1 := by omega
      have h3 : ((k + 1 - j : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub h2, Nat.cast_sub hN] at h3
      push_cast at h3
      linarith
    have : 2 * Real.pi * ((k : ℝ) + 1 - j) / N < 2 * Real.pi := by
      rw [div_lt_iff₀ hk]; nlinarith [hpi]
    linarith
  have hpair : ∀ p : ℕ × ℕ, ∃ δ : ℝ, 0 < δ ∧ (p.1 < N → p.2 < N → p.1 + 2 ≤ p.2 →
      ¬ (p.1 = 0 ∧ p.2 = N - 1) → ∀ x ∈ F '' I p.1, ∀ y ∈ F '' I p.2, δ ≤ dist x y) := by
    intro p
    by_cases h : p.1 < N ∧ p.2 < N ∧ p.1 + 2 ≤ p.2 ∧ ¬ (p.1 = 0 ∧ p.2 = N - 1)
    · obtain ⟨δ, hδ, hsep⟩ := exists_pos_sep ((isCompact_Icc).image hFc) ((isCompact_Icc).image hFc)
        (hdisj p.1 p.2 h.1 h.2.1 h.2.2.1 h.2.2.2)
      exact ⟨δ, hδ, fun _ _ _ _ => hsep⟩
    · exact ⟨1, one_pos, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩
  choose δ hδ hδs using hpair
  obtain ⟨p₀, -, hp₀⟩ := Finset.exists_min_image (Finset.range N ×ˢ Finset.range N) δ
    ⟨(0, 0), by simp [hN]; omega⟩
  refine ⟨δ p₀, hδ p₀, fun j k hj hkN hjk hne s hs s' hs' => ?_⟩
  have hmin : δ p₀ ≤ δ (j, k) := hp₀ (j, k) (by simp [hj, hkN])
  exact hmin.trans (hδs (j, k) hj hkN hjk hne _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩)

/-- **Polygons in the inside that follow a Jordan curve.** For every `ρ > 0` there is `N₀` such that for every
`N ≥ max N₀ 4` there is a simple polygon with carrier in the open inner region `U`, traversed by a continuous
`2π`-periodic loop `G` that stays within `ρ` of the curve at each parameter, and which encloses every point of
`U` at distance at least `2ρ` from the curve. -/
theorem exists_frechet_polygon {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f)
    {U : Set (ℝ × ℝ)} (hUo : IsOpen U) (hUc : IsConnected U) (hUb : Bornology.IsBounded U)
    (hcl : closure U = U ∪ range f) (hUJ : Disjoint U (range f)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 4 ≤ N → ∃ (a b : ℝ × ℝ) (m₁ m₂ : List (ℝ × ℝ)),
      (Polygon.ofList (a :: m₁ ++ b :: m₂)).IsSimple ∧
      (Polygon.ofList (a :: m₁ ++ b :: m₂)).carrier ⊆ U ∧
      ∃ G : ℝ → ℝ × ℝ, Continuous G ∧ Function.Periodic G (2 * Real.pi) ∧
        range G = (Polygon.ofList (a :: m₁ ++ b :: m₂)).carrier ∧
        (∀ s, dist (G s) (f (Circle.exp s)) < ρ) ∧
        (∀ z ∈ U, 2 * ρ ≤ infDist z (range f) → z ∈ (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside) := by
  classical
  have hpi : 0 < 2 * Real.pi := by positivity
  set F : ℝ → ℝ × ℝ := fun s => f (Circle.exp s) with hF
  have hFc : Continuous F := hc.comp Circle.exp.continuous
  have hFper : Function.Periodic F (2 * Real.pi) := fun s => by
    simp only [hF]; rw [Circle.periodic_exp s]
  obtain ⟨w, hw, hwc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hFc.continuousOn) (ρ / 2) (by positivity)
  refine ⟨Nat.ceil (2 * Real.pi / w) + 1, fun N hN₀ hN4 => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hk : (0 : ℝ) < N := by exact_mod_cast hN1
  have hmesh : 2 * Real.pi / N < w := by
    rw [div_lt_iff₀ hk]
    have h1 : 2 * Real.pi / w ≤ (Nat.ceil (2 * Real.pi / w) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (2 * Real.pi / w) : ℝ) + 1 ≤ N := by exact_mod_cast hN₀
    rw [div_le_iff₀ hw] at h1
    have h3 : w * ((Nat.ceil (2 * Real.pi / w) : ℝ) + 1) ≤ w * N := mul_le_mul_of_nonneg_left h2 hw.le
    nlinarith
  obtain ⟨ε, hε, hsep⟩ := exists_arc_sep hc hi hN1
  set η : ℝ := min (ρ / 2) (ε / 3) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  set t : ℕ → ℝ := fun j => 2 * Real.pi * j / N with ht
  have htmem : ∀ j, j ≤ N → t j ∈ Icc 0 (2 * Real.pi) := by
    intro j hj
    refine ⟨by simp only [ht]; positivity, ?_⟩
    simp only [ht]
    rw [div_le_iff₀ hk]
    have : (j : ℝ) ≤ N := by exact_mod_cast hj
    nlinarith
  have htN : t N = 2 * Real.pi := by simp only [ht]; field_simp
  -- the curve at the junctions and the chains
  have hblock : ∀ j : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ {za zb : ℝ × ℝ}, za ∈ U → zb ∈ U →
      dist za (f (Circle.exp (t j))) < r → dist zb (f (Circle.exp (t (j + 1)))) < r →
      ∃ l : List (ℝ × ℝ), IsSimpleChain l ∧ l.head? = some za ∧ l.getLast? = some zb ∧ chainSet l ⊆ U ∧
        ∀ x ∈ chainSet l, ∃ σ ∈ Icc (t j) (t (j + 1)), dist x (f (Circle.exp σ)) < η := by
    intro j
    exact exists_block_chain hc hi hUo hUc hcl hUJ hη0 (a := t j) (b := t (j + 1)) (by
      simp only [ht]; apply div_le_div_of_nonneg_right _ hk.le; push_cast; nlinarith [hpi])
  choose r hr0 hr using hblock
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image (Finset.range N) r ⟨0, by simp; omega⟩
  set r₀ : ℝ := r j₀ with hr₀
  have hr₀0 : 0 < r₀ := hr0 j₀
  have hnear : ∀ j : ℕ, ∃ z, z ∈ U ∧ dist z (f (Circle.exp (t j))) < r₀ := by
    intro j
    have : f (Circle.exp (t j)) ∈ closure U := by rw [hcl]; exact Or.inr ⟨_, rfl⟩
    obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.1 this r₀ hr₀0
    exact ⟨z, hz, by rw [dist_comm]; exact hd⟩
  choose z0 hz0U hz0d using hnear
  set z : ℕ → ℝ × ℝ := fun j => if j = N then z0 0 else z0 j with hz
  have hzU : ∀ j, z j ∈ U := by intro j; simp only [hz]; split_ifs <;> exact hz0U _
  have hzd : ∀ j, j ≤ N → dist (z j) (f (Circle.exp (t j))) < r₀ := by
    intro j hj
    simp only [hz]
    split_ifs with h
    · rw [h]
      have : Circle.exp (t N) = Circle.exp (t 0) := by
        rw [htN]; simp only [ht]; simp
      rw [this]; exact hz0d 0
    · exact hz0d j
  have hchain : ∀ j : ℕ, ∃ l : List (ℝ × ℝ), j < N → (IsSimpleChain l ∧ l.head? = some (z j) ∧
      l.getLast? = some (z (j + 1)) ∧ chainSet l ⊆ U ∧
      ∀ x ∈ chainSet l, ∃ σ ∈ Icc (t j) (t (j + 1)), dist x (f (Circle.exp σ)) < η) := by
    intro j
    by_cases hj : j < N
    · have hrj : r₀ ≤ r j := hj₀ j (by simp [hj])
      obtain ⟨l, h1, h2, h3, h4, h5⟩ := hr j (hzU j) (hzU (j + 1))
        (lt_of_lt_of_le (hzd j hj.le) hrj) (lt_of_lt_of_le (hzd (j + 1) hj) hrj)
      exact ⟨l, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨[], fun h => absurd h hj⟩
  choose S hS using hchain
  have hraw : RawChains N S := by
    refine ⟨fun j hj => (hS j hj).1, fun j hj => ?_, fun j hj => ?_, ?_, ?_⟩
    · rw [(hS j hj).2.1]; simp
    · rw [(hS j (by omega)).2.2.1, (hS (j + 1) hj).2.1]
    · rw [(hS (N - 1) (by omega)).2.2.1, (hS 0 (by omega)).2.1]
      have : N - 1 + 1 = N := by omega
      simp only [this, hz]
      simp
    · intro j k hjk hk hne
      rw [Set.disjoint_left]
      intro x hxj hxk
      obtain ⟨σ, hσ, hσd⟩ := (hS j (by omega)).2.2.2.2 x hxj
      obtain ⟨σ', hσ', hσd'⟩ := (hS k hk).2.2.2.2 x hxk
      have := hsep j k (by omega) hk hjk hne σ (by simp only [ht] at hσ; push_cast at hσ; exact hσ) σ'
        (by simp only [ht] at hσ'; push_cast at hσ'; exact hσ')
      have h3 : dist (f (Circle.exp σ)) (f (Circle.exp σ')) < ε := by
        calc dist (f (Circle.exp σ)) (f (Circle.exp σ')) ≤ dist (f (Circle.exp σ)) x + dist x (f (Circle.exp σ')) :=
              dist_triangle _ _ _
          _ < η + η := by rw [dist_comm (f (Circle.exp σ)) x]; exact add_lt_add hσd hσd'
          _ ≤ ε := by have := min_le_right (ρ / 2) (ε / 3); linarith
      linarith
  obtain ⟨T, hT, hTsub⟩ := exists_cyc_of_raw (by omega : 3 ≤ N) hraw
  obtain ⟨a, b, m₁, m₂, hsimple, hcar⟩ := hT.exists_polygon hN4
  obtain ⟨G, hGc, hGper, hGblock, hGrange⟩ := hT.exists_loop hN1
  have hcarU : (Polygon.ofList (a :: m₁ ++ b :: m₂)).carrier ⊆ U := by
    rw [hcar]
    rintro x ⟨j, hj, hx⟩
    exact (hS j hj).2.2.2.1 (hTsub j hj hx)
  have hrange : range G = (Polygon.ofList (a :: m₁ ++ b :: m₂)).carrier := by rw [hcar, hGrange]
  -- closeness
  have hclose0 : ∀ s ∈ Ico 0 (2 * Real.pi), dist (G s) (F s) < ρ := by
    intro s hs
    obtain ⟨j, hj, hj1, hj2⟩ := exists_block_of_mem hN1 hs
    have hGs : G s ∈ chainSet (T j) := hGblock j hj s hj1 hj2
    obtain ⟨σ, hσ, hσd⟩ := (hS j hj).2.2.2.2 _ (hTsub j hj hGs)
    have hσ2 : σ ∈ Icc 0 (2 * Real.pi) := by
      have h1 := htmem j hj.le
      have h2 := htmem (j + 1) hj
      exact ⟨le_trans h1.1 hσ.1, le_trans hσ.2 h2.2⟩
    have hs2 : s ∈ Icc 0 (2 * Real.pi) := ⟨hs.1, hs.2.le⟩
    have hdist : dist σ s < w := by
      rw [Real.dist_eq, abs_lt]
      have e1 : t (j + 1) - t j = 2 * Real.pi / N := by simp only [ht]; push_cast; field_simp; ring
      have e2 : t j ≤ s := hj1
      have e3 : s ≤ t (j + 1) := by simp only [ht]; push_cast; exact hj2
      constructor <;> linarith [hσ.1, hσ.2]
    have h3 := hwc σ hσ2 s hs2 hdist
    have h4 : dist (G s) (F s) ≤ dist (G s) (F σ) + dist (F σ) (F s) := dist_triangle _ _ _
    have h5 : η ≤ ρ / 2 := min_le_left _ _
    have hσd' : dist (G s) (F σ) < η := hσd
    linarith
  have hclose : ∀ s, dist (G s) (F s) < ρ := by
    intro s
    set s' := toIcoMod Real.two_pi_pos 0 s with hs'
    have hmem : s' ∈ Ico 0 (0 + 2 * Real.pi) := toIcoMod_mem_Ico Real.two_pi_pos _ _
    have hs'eq : s' = s - toIcoDiv Real.two_pi_pos 0 s • (2 * Real.pi) := rfl
    have e1 : G s' = G s := by rw [hs'eq, hGper.sub_zsmul_eq]
    have e2 : F s' = F s := by rw [hs'eq, hFper.sub_zsmul_eq]
    rw [← e1, ← e2]
    exact hclose0 s' (by simpa using hmem)
  refine ⟨a, b, m₁, m₂, hsimple, hcarU, G, hGc, hGper, hrange, hclose, ?_⟩
  -- the points of the inside far from the curve are enclosed
  intro z hzU' hz2
  obtain ⟨ψ, hψc, hψ⟩ := exists_circle_lift hGc hGper
  have hψrange : range ψ = (Polygon.ofList (a :: m₁ ++ b :: m₂)).carrier := by
    rw [← hrange]
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨s, rfl⟩ := Circle.exp_surjective u
      exact ⟨s, (hψ s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Circle.exp s, hψ s⟩
  have : NeZero (a :: m₁ ++ b :: m₂).length := ⟨by simp⟩
  refine mem_inside_of_close hc hi hUo hUb hcl hUJ hsimple hψc hψrange hzU' (fun u => ?_)
  obtain ⟨s, rfl⟩ := Circle.exp_surjective u
  rw [hψ s]
  have := hclose s
  simp only [hF] at this
  linarith

end Lightlike.PL.Schoenflies
