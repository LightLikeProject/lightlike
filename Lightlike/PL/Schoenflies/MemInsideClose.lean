import Mathlib
import Lightlike.PL.Polygon
import Lightlike.PL.PolygonInside
import Lightlike.PL.Schoenflies.JordanIndex
import Lightlike.PL.Schoenflies.WindingCompare
import Lightlike.PL.Schoenflies.JordanInnerULC

/-!
# A point of the inside that a close polygon loop must enclose

Row G3-188 (PL5), step 3 of the pass-4 plan.  `mem_inside_of_close`: if a simple polygon is the image of a loop
`ψ` of the circle that stays closer to the Jordan curve `f` (at the same parameter, up to the factor `2`) than
the point `z` of the inner region `U` is to the curve, then `z` lies inside the polygon.  The winding number of
`ψ` about `z` equals that of `f` (`period_inc_eq_of_close`); the winding number of `f` about `z` is nonzero since
`z` is not joined to infinity (`jordan_index_zero_joined`); the winding number about a point of the outside
of the polygon is zero (`period_inc_zero_of_joined`).
-/

namespace Lightlike.PL.Schoenflies

open Set Metric Lightlike.PL Complex

private lemma norm_toC_le (q : ℝ × ℝ) : ‖Complex.equivRealProdCLM.symm q‖ ≤ 2 * ‖q‖ := by
  have h1 : ‖(Complex.equivRealProdCLM.symm q : ℂ)‖ ≤ |q.1| + |q.2| := by
    have := Complex.norm_le_abs_re_add_abs_im (Complex.equivRealProdCLM.symm q)
    simpa using this
  have h2 : |q.1| ≤ ‖q‖ := by simpa using norm_fst_le q
  have h3 : |q.2| ≤ ‖q‖ := by simpa using norm_snd_le q
  linarith

private lemma norm_le_toC (q : ℝ × ℝ) : ‖q‖ ≤ ‖Complex.equivRealProdCLM.symm q‖ := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · simpa using Complex.abs_re_le_norm (Complex.equivRealProdCLM.symm q)
  · simpa using Complex.abs_im_le_norm (Complex.equivRealProdCLM.symm q)

theorem mem_inside_of_close {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f)
    {U : Set (ℝ × ℝ)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hcl : closure U = U ∪ range f)
    (hUJ : Disjoint U (range f))
    {n : ℕ} [NeZero n] {p : Polygon n} (hs : p.IsSimple) {ψ : Circle → ℝ × ℝ} (hψ : Continuous ψ)
    (hr : range ψ = p.carrier) {z : ℝ × ℝ} (hz : z ∈ U)
    (h : ∀ t, 2 * dist (ψ t) (f t) < infDist z (range f)) : z ∈ p.inside := by
  set e := Complex.equivRealProdCLM with he
  set fC : Circle → ℂ := fun t => e.symm (f t) with hfC
  set ψC : Circle → ℂ := fun t => e.symm (ψ t) with hψC
  have hfCc : Continuous fC := e.symm.continuous.comp hc
  have hψCc : Continuous ψC := e.symm.continuous.comp hψ
  have hfCi : Function.Injective fC := fun a b hab => hi (e.symm.injective hab)
  have hzJ : z ∉ range f := fun hh => Set.disjoint_left.1 hUJ hz hh
  have hd0 : ∀ t, dist z (f t) ≥ infDist z (range f) := fun t => infDist_le_dist_of_mem ⟨t, rfl⟩
  have hdistnn : ∀ t, 0 ≤ dist (ψ t) (f t) := fun t => dist_nonneg
  -- `z` is not on the polygon
  have hzC : z ∉ p.carrier := by
    rw [← hr]
    rintro ⟨t, rfl⟩
    have h1 := h t
    have h2 := hd0 t
    rw [dist_comm (ψ t) (f t)] at h1 h2
    linarith [hdistnn t, dist_comm (ψ t) (f t)]
  by_contra hzin
  have hzout : z ∈ p.outside := by
    have : z ∈ p.carrierᶜ := hzC
    rw [Polygon.compl_carrier_eq] at this
    rcases this with h1 | h1
    · exact h1
    · exact absurd h1 hzin
  -- a far point of the outside
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ∀ t, ‖ψC t‖ ≤ ρ := by
    obtain ⟨ρ, hρ⟩ := (isCompact_range hψCc).isBounded.exists_norm_le
    exact ⟨ρ, fun t => hρ _ ⟨t, rfl⟩⟩
  obtain ⟨w, hwout, hw⟩ : ∃ w ∈ p.outside, ρ < ‖e.symm w‖ := by
    by_contra hcon
    push Not at hcon
    apply Polygon.not_isBounded_outside p
    rw [isBounded_iff_forall_norm_le]
    exact ⟨ρ, fun w hw => (norm_le_toC w).trans (hcon w hw)⟩
  -- the path to infinity in the complement of the polygon
  have hjoin : JoinedIn (range ψC)ᶜ (e.symm z) (e.symm w) := by
    have hpc : IsPathConnected p.outside :=
      ((Polygon.isOpen_outside p).isConnected_iff_isPathConnected.1
        ⟨⟨z, hzout⟩, Polygon.isPreconnected_outside hs⟩)
    have hj := (hpc.joinedIn z hzout w hwout).map e.symm.continuous.continuousOn
    refine hj.mono ?_
    rintro _ ⟨q, hq, rfl⟩ ⟨t, ht⟩
    have : ψ t = q := e.symm.injective ht
    exact hq.1 (hr ▸ ⟨t, this⟩)
  -- the two global logarithms
  have hzfC : e.symm z ∉ range fC := by
    rintro ⟨t, ht⟩; exact hzJ ⟨t, e.symm.injective ht⟩
  have hzψC : e.symm z ∉ range ψC := by
    rintro ⟨t, ht⟩; exact hzC (hr ▸ ⟨t, e.symm.injective ht⟩)
  obtain ⟨Ff, hFfc, hFf⟩ := Lightlike.PL.exists_global_log hfCc hzfC
  obtain ⟨Fψ, hFψc, hFψ⟩ := Lightlike.PL.exists_global_log hψCc hzψC
  have hclose : ∀ t, ‖ψC t - fC t‖ < ‖fC t - e.symm z‖ := by
    intro t
    have h1 : ψC t - fC t = e.symm (ψ t - f t) := by simp [hψC, hfC]
    have h2 : fC t - e.symm z = e.symm (f t - z) := by simp [hfC]
    rw [h1, h2]
    calc ‖e.symm (ψ t - f t)‖ ≤ 2 * ‖ψ t - f t‖ := norm_toC_le _
      _ = 2 * dist (ψ t) (f t) := by rw [dist_eq_norm]
      _ < infDist z (range f) := h t
      _ ≤ dist z (f t) := hd0 t
      _ = ‖f t - z‖ := by rw [dist_comm, dist_eq_norm]
      _ ≤ ‖e.symm (f t - z)‖ := norm_le_toC _
  have hinc := period_inc_eq_of_close hfCc hψCc hclose hFfc hFψc hFf hFψ
  have hψ0 := period_inc_zero_of_joined hψCc hjoin hρ hw hFψc hFψ
  have hf0 : Ff (2 * Real.pi) = Ff 0 := by
    have : Fψ (2 * Real.pi) - Fψ 0 = 0 := by rw [hψ0]; ring
    rw [hinc] at this
    linear_combination this
  -- so `z` is joined to infinity off the curve
  obtain ⟨M, hM⟩ := hUb.exists_norm_le
  obtain ⟨R', hR'norm, hR'⟩ := jordan_index_zero_joined hfCc hfCi hzfC hFfc hFf hf0 (2 * M)
  have hj2 : JoinedIn (range f)ᶜ z (e R') := by
    have hmap := hR'.map e.continuous.continuousOn
    rw [ContinuousLinearEquiv.apply_symm_apply] at hmap
    refine hmap.mono ?_
    rintro _ ⟨q, hq, rfl⟩ ⟨t, ht⟩
    exact hq ⟨t, by rw [hfC]; simp only []; rw [ht]; simp⟩
  obtain ⟨γ, hγ⟩ := hj2
  have hconn : IsPreconnected (range γ) := (isConnected_range γ.continuous).isPreconnected
  have hsub : range γ ⊆ U :=
    subset_inner_of_connected hUo hcl hconn
      (Set.disjoint_left.2 fun x ⟨t, ht⟩ hxJ => hγ t (ht ▸ hxJ)) (⟨0, γ.source⟩ : z ∈ range γ) hz
  have hRU : e R' ∈ U := by
    exact hsub ⟨1, γ.target⟩
  have h1 := hM _ hRU
  have h2 : ‖R'‖ ≤ 2 * ‖e R'‖ := by
    have := norm_toC_le (e R')
    rwa [ContinuousLinearEquiv.symm_apply_apply] at this
  linarith

end Lightlike.PL.Schoenflies
