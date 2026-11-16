import Lightlike.PL.ArcApprox

/-!
# An arc seen from a connected set near it

The inverse of an injective continuous arc is uniformly continuous: points of the arc that are close
in the plane are close in the parameter (`exists_inverse_modulus`). With it, a connected compact set
that contains both ends of the arc and lies close to it is, at the scale of that modulus, close to
every point of the arc (`arc_density`). This is what makes a polygon obtained from an arc by
loop erasure still approximate the whole arc.

## Main results

* `exists_inverse_modulus`: the modulus of continuity of the inverse of an arc.
* `arc_density`: a connected compact set containing both ends of an arc and near it is near every
  point of the arc.
-/

open Set

namespace Lightlike.PL

/-- **An arc is covered, at the scale of its inverse modulus, by the parameters seen from a
connected set near it.** If a connected compact set `P` contains both ends of the arc `γ` and every
point of `P` is within `ε'` of the arc, then every parameter is within `θ` of a parameter whose
point is within `ε'` of `P`; here `δ` and `θ` are linked by the modulus of the inverse of `γ`, and
`2 ε' < δ`. -/
theorem arc_density {γ : ℝ → ℝ × ℝ} (hγ : ContinuousOn γ (Icc 0 1)) {θ δ ε' : ℝ} (hθ : 0 < θ)
    (hinv : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (γ s) (γ t) < δ → |s - t| < θ)
    (hε' : 2 * ε' < δ) {P : Set (ℝ × ℝ)} (hPc : IsCompact P) (hPp : IsPreconnected P)
    (h0 : γ 0 ∈ P) (h1 : γ 1 ∈ P) (hP : ∀ p ∈ P, ∃ τ ∈ Icc (0 : ℝ) 1, dist p (γ τ) ≤ ε') :
    ∀ τ ∈ Icc (0 : ℝ) 1, ∃ τ' ∈ Icc (0 : ℝ) 1, |τ - τ'| < θ ∧ ∃ p ∈ P, dist p (γ τ') ≤ ε' := by
  intro τ₀ hτ₀
  by_contra hcon
  push Not at hcon
  have hε0 : 0 ≤ ε' := by
    obtain ⟨τ, -, h'⟩ := hP _ h0
    exact le_trans dist_nonneg h'
  -- the two ends are far from `τ₀` in parameter
  have hlo : θ ≤ τ₀ := by
    by_contra h
    rw [not_le] at h
    have := hcon 0 ⟨le_rfl, zero_le_one⟩ (by rw [sub_zero, abs_of_nonneg hτ₀.1]; exact h) _ h0
    rw [dist_self] at this
    linarith
  have hhi : τ₀ + θ ≤ 1 := by
    by_contra h
    rw [not_le] at h
    have := hcon 1 ⟨zero_le_one, le_rfl⟩ (by rw [abs_of_nonpos (by linarith [hτ₀.2])]; linarith) _ h1
    rw [dist_self] at this
    linarith
  -- the points of `P` near the early and the late part of the arc
  set Kₗ : Set ((ℝ × ℝ) × ℝ) := (P ×ˢ Icc (0 : ℝ) (τ₀ - θ)) ∩ {q | dist q.1 (γ q.2) ≤ ε'} with hKₗ
  set Kᵣ : Set ((ℝ × ℝ) × ℝ) := (P ×ˢ Icc (τ₀ + θ) (1 : ℝ)) ∩ {q | dist q.1 (γ q.2) ≤ ε'} with hKᵣ
  have hcontd : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => dist q.1 (γ q.2))
      (P ×ˢ Icc (0 : ℝ) 1) := by
    exact (continuous_dist.comp_continuousOn
      (continuousOn_fst.prodMk (hγ.comp continuousOn_snd (fun q hq => hq.2))))
  have hKₗc : IsCompact Kₗ := by
    have hsub : P ×ˢ Icc (0 : ℝ) (τ₀ - θ) ⊆ P ×ˢ Icc (0 : ℝ) 1 :=
      prod_mono subset_rfl (Icc_subset_Icc le_rfl (by linarith [hτ₀.2]))
    refine (hPc.prod isCompact_Icc).of_isClosed_subset ?_ inter_subset_left
    exact ((hcontd.mono hsub).preimage_isClosed_of_isClosed (hPc.prod isCompact_Icc).isClosed
      isClosed_Iic)
  have hKᵣc : IsCompact Kᵣ := by
    have hsub : P ×ˢ Icc (τ₀ + θ) (1 : ℝ) ⊆ P ×ˢ Icc (0 : ℝ) 1 :=
      prod_mono subset_rfl (Icc_subset_Icc (by linarith [hτ₀.1]) le_rfl)
    refine (hPc.prod isCompact_Icc).of_isClosed_subset ?_ inter_subset_left
    exact ((hcontd.mono hsub).preimage_isClosed_of_isClosed (hPc.prod isCompact_Icc).isClosed
      isClosed_Iic)
  have hPl : IsClosed (Prod.fst '' Kₗ) := (hKₗc.image continuous_fst).isClosed
  have hPr : IsClosed (Prod.fst '' Kᵣ) := (hKᵣc.image continuous_fst).isClosed
  have hcover : P ⊆ Prod.fst '' Kₗ ∪ Prod.fst '' Kᵣ := by
    intro p hp
    obtain ⟨τ, hτ, hd⟩ := hP p hp
    rcases le_or_gt τ (τ₀ - θ) with h | h
    · exact Or.inl ⟨(p, τ), ⟨⟨hp, hτ.1, h⟩, hd⟩, rfl⟩
    · rcases le_or_gt (τ₀ + θ) τ with h' | h'
      · exact Or.inr ⟨(p, τ), ⟨⟨hp, h', hτ.2⟩, hd⟩, rfl⟩
      · exact absurd (hcon τ hτ (by rw [abs_lt]; constructor <;> linarith) p hp) (not_lt.2 hd)
  have hne₁ : (P ∩ Prod.fst '' Kₗ).Nonempty :=
    ⟨γ 0, h0, ⟨(γ 0, 0), ⟨⟨h0, le_rfl, by linarith⟩, by simpa using hε0⟩, rfl⟩⟩
  have hne₂ : (P ∩ Prod.fst '' Kᵣ).Nonempty :=
    ⟨γ 1, h1, ⟨(γ 1, 1), ⟨⟨h1, hhi, le_rfl⟩, by simpa using hε0⟩, rfl⟩⟩
  obtain ⟨p, hp, ⟨q₁, ⟨⟨-, hq₁⟩, hd₁⟩, hq₁p⟩, ⟨q₂, ⟨⟨-, hq₂⟩, hd₂⟩, hq₂p⟩⟩ :=
    isPreconnected_closed_iff.1 hPp _ _ hPl hPr hcover hne₁ hne₂
  subst hq₁p
  have hd₁' : dist q₁.1 (γ q₁.2) ≤ ε' := hd₁
  have hd₂' : dist q₂.1 (γ q₂.2) ≤ ε' := hd₂
  have hdd : dist (γ q₁.2) (γ q₂.2) < δ := by
    have h1' := dist_triangle_left (γ q₁.2) (γ q₂.2) q₁.1
    have h2' : dist q₁.1 (γ q₂.2) ≤ ε' := by rw [← hq₂p]; exact hd₂'
    linarith
  have := hinv q₁.2 ⟨hq₁.1, by linarith [hq₁.2, hτ₀.2]⟩ q₂.2 ⟨by linarith [hq₂.1, hτ₀.1], hq₂.2⟩ hdd
  rw [abs_lt] at this
  linarith [hq₁.2, hq₂.1]

/-- **The inverse of an arc is uniformly continuous**: points of an injective continuous arc that are
close in the plane are close in parameter. -/
theorem exists_inverse_modulus {γ : ℝ → ℝ × ℝ} (hγ : ContinuousOn γ (Icc 0 1))
    (hi : InjOn γ (Icc 0 1)) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (γ s) (γ t) < δ →
      |s - t| < θ := by
  set F : Set (ℝ × ℝ) := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {q | θ ≤ |q.1 - q.2|} with hF
  have hFc : IsCompact F := by
    refine (isCompact_Icc.prod isCompact_Icc).inter_right ?_
    exact isClosed_le continuous_const (by fun_prop)
  rcases F.eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun s hs t ht _ => ?_⟩
    by_contra h
    rw [not_lt] at h
    have : (s, t) ∈ F := ⟨⟨hs, ht⟩, h⟩
    rw [hE] at this
    exact this
  · have hcd : ContinuousOn (fun q : ℝ × ℝ => dist (γ q.1) (γ q.2)) F := by
      have hm : MapsTo (fun q : ℝ × ℝ => q) F (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := fun q hq => hq.1
      exact (continuous_dist.comp_continuousOn
        (((hγ.comp continuousOn_fst (fun q hq => hq.1.1)).prodMk
          (hγ.comp continuousOn_snd (fun q hq => hq.1.2)))))
    obtain ⟨q₀, hq₀, hmin⟩ := hFc.exists_isMinOn hne hcd
    have hpos : 0 < dist (γ q₀.1) (γ q₀.2) := by
      rw [dist_pos]
      intro h
      have := hi hq₀.1.1 hq₀.1.2 h
      have hq := hq₀.2
      simp only [mem_ofPred_eq, this, sub_self, abs_zero] at hq
      linarith
    refine ⟨_, hpos, fun s hs t ht hlt => ?_⟩
    by_contra h
    rw [not_lt] at h
    have := hmin (show (s, t) ∈ F from ⟨⟨hs, ht⟩, h⟩)
    simp only [mem_ofPred_eq] at this
    linarith

end Lightlike.PL
