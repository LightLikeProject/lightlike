import Lightlike.Spacetime.CausalLadder.LipschitzMono
import Lightlike.Spacetime.CausalLadder.ChartFTC

/-!
# Two comparison lemmas for Lipschitz functions

The real-analysis steps of the local causality theorem (`Lightlike.Geodesic.LocalCausality`).

* `le_of_ae_deriv_nonpos_of_neg`: a Lipschitz function that starts negative, and whose derivative
  is nonpositive almost everywhere where the function is negative, never exceeds its initial
  value.
* `nonpos_of_cone_inequality`: if `f ≤ C h²`, `h` increases from `0`, and almost everywhere
  `f' h ≤ f h'` where `f > 0` and `f' ≤ 0` where `f ≤ 0`, then `f ≤ 0` at the end. Here `f` is
  the squared geodesic distance from a point `p` along a causal curve from `p`, and `h` is a time
  function; the inequality `f' h ≤ f h'` comes from the Gauss lemma.

Supporting lemmas; no catalogue entry.
-/

open Set MeasureTheory Filter Topology

namespace Lightlike.Geodesic

/-- A Lipschitz function on `[s, b]` with `G s < 0` whose derivative is nonpositive at almost
every point where `G < 0` satisfies `G ≤ G s` on `[s, b]`. -/
theorem le_of_ae_deriv_nonpos_of_neg {G : ℝ → ℝ} {s b : ℝ} {K : NNReal}
    (hG : LipschitzOnWith K G (Icc s b)) (hs : G s < 0)
    (hd : ∀ᵐ t, t ∈ Ioo s b → DifferentiableAt ℝ G t ∧ (G t < 0 → deriv G t ≤ 0)) :
    ∀ t ∈ Icc s b, G t ≤ G s := by
  intro t ht
  have hsb : s ≤ b := ht.1.trans ht.2
  set S : Set ℝ := {u | G u ≤ G s} with hS
  have hclosed : IsClosed (S ∩ Icc s b) := by
    rw [inter_comm]
    exact hG.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub : Icc s b ⊆ S := by
    refine hclosed.Icc_subset_of_forall_mem_nhdsWithin (le_refl (G s)) ?_
    rintro x ⟨hxS, hx⟩
    have hx' : x ∈ Icc s b := ⟨hx.1, hx.2.le⟩
    have hneg : G x < 0 := lt_of_le_of_lt hxS hs
    have hcont : ContinuousWithinAt G (Icc s b) x := hG.continuousOn x hx'
    have hev : ∀ᶠ u in 𝓝[Icc s b] x, G u < 0 := hcont.eventually (Iio_mem_nhds hneg)
    obtain ⟨δ, hδ, hδG⟩ := Metric.mem_nhdsWithin_iff.1 hev
    have hmem : Ioo x (min (x + δ) b) ∈ 𝓝[>] x :=
      Ioo_mem_nhdsGT (lt_min (by linarith) hx.2)
    filter_upwards [hmem] with u hu
    have hub : u ≤ b := (hu.2.trans_le (min_le_right _ _)).le
    have hsubI : Icc x u ⊆ Icc s b := Icc_subset_Icc hx.1 hub
    have hnegI : ∀ z ∈ Icc x u, G z < 0 := by
      intro z hz
      refine hδG ⟨?_, hsubI hz⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      have := hu.2.trans_le (min_le_left _ _)
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have h0 : LipschitzOnWith 0 (fun _ : ℝ => (0 : ℝ)) (Icc x u) :=
      (LipschitzWith.const (0 : ℝ)).lipschitzOnWith
    have hcmp := Lightlike.Causal.sub_le_sub_of_ae_deriv_le (f := G) (h := fun _ => (0 : ℝ))
      hu.1.le (hG.mono hsubI) h0 (by
        filter_upwards [hd] with z hz hzI
        have hzI' : z ∈ Ioo s b := ⟨lt_of_le_of_lt hx.1 hzI.1, lt_of_lt_of_le hzI.2 hub⟩
        refine ⟨(hz hzI').1, differentiableAt_const _, ?_⟩
        rw [deriv_const]
        exact (hz hzI').2 (hnegI z (Ioo_subset_Icc_self hzI)))
    have hxS' : G x ≤ G s := hxS
    show G u ≤ G s
    linarith
  exact hsub ht

/-- **The cone inequality.** Let `f` and `h` be Lipschitz on `[a, b]`, with `h a = 0`, `h > 0` on
`(a, b]` and `f ≤ C h²`. If almost everywhere `h' ≥ 0`, `f' h ≤ f h'` where `f > 0`, and `f' ≤ 0`
where `f ≤ 0`, then `f b ≤ 0`. -/
theorem nonpos_of_cone_inequality {f h : ℝ → ℝ} {a b C : ℝ} {Kf Kh : NNReal} (hab : a < b)
    (hf : LipschitzOnWith Kf f (Icc a b)) (hh : LipschitzOnWith Kh h (Icc a b))
    (ha : h a = 0) (hpos : ∀ t ∈ Ioc a b, 0 < h t) (hC : 0 ≤ C)
    (hfC : ∀ t ∈ Icc a b, f t ≤ C * h t ^ 2)
    (hd : ∀ᵐ t, t ∈ Ioo a b → DifferentiableAt ℝ f t ∧ DifferentiableAt ℝ h t ∧
      0 ≤ deriv h t ∧ (0 < f t → deriv f t * h t ≤ f t * deriv h t) ∧
      (f t ≤ 0 → deriv f t ≤ 0)) : f b ≤ 0 := by
  by_contra hcon
  have hfb : 0 < f b := not_le.1 hcon
  have hb : b ∈ Ioc a b := ⟨hab, le_rfl⟩
  have hhb : 0 < h b := hpos b hb
  -- the comparison for every starting time and every slope
  have key : ∀ s ∈ Ioc a b, ∀ η : ℝ, 0 < η → f b < (C * h s + η) * h b := by
    intro s hs η hη
    have hhs : 0 < h s := hpos s hs
    set lam : ℝ := C * h s + η with hlam
    have hlam0 : 0 < lam := by positivity
    set G : ℝ → ℝ := fun t => f t - lam * h t with hGdef
    have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc_left hs.1.le
    set L : NNReal := ⟨lam, hlam0.le⟩ with hLdef
    have hL : (L : ℝ) = lam := rfl
    have hGL : LipschitzOnWith (Kf + L * Kh) G (Icc s b) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      have h1 := hf.dist_le_mul x (hsub hx) y (hsub hy)
      have h2 := hh.dist_le_mul x (hsub hx) y (hsub hy)
      simp only [Real.dist_eq] at h1 h2 ⊢
      have h3 : G x - G y = (f x - f y) - lam * (h x - h y) := by simp only [hGdef]; ring
      rw [h3, NNReal.coe_add, NNReal.coe_mul, hL]
      calc |(f x - f y) - lam * (h x - h y)| ≤ |f x - f y| + |lam * (h x - h y)| := abs_sub _ _
        _ = |f x - f y| + lam * |h x - h y| := by rw [abs_mul, abs_of_pos hlam0]
        _ ≤ Kf * |x - y| + lam * (Kh * |x - y|) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 hlam0.le)
        _ = ((Kf : ℝ) + lam * Kh) * |x - y| := by ring
    have hGs : G s < 0 := by
      have h1 := hfC s (Ioc_subset_Icc_self hs)
      have h2 : G s = f s - (C * h s + η) * h s := rfl
      nlinarith [mul_pos hη hhs]
    have hGd : ∀ᵐ t, t ∈ Ioo s b → DifferentiableAt ℝ G t ∧ (G t < 0 → deriv G t ≤ 0) := by
      filter_upwards [hd] with t ht htI
      have htI' : t ∈ Ioo a b := ⟨hs.1.trans htI.1, htI.2⟩
      obtain ⟨hdf, hdh, hh', h1, h2⟩ := ht htI'
      have hdG : HasDerivAt G (deriv f t - lam * deriv h t) t :=
        hdf.hasDerivAt.sub (hdh.hasDerivAt.const_mul lam)
      refine ⟨hdG.differentiableAt, fun hneg => ?_⟩
      rw [hdG.deriv]
      have hht : 0 < h t := hpos t ⟨htI'.1, htI'.2.le⟩
      have hlt : f t < lam * h t := by
        have : G t = f t - lam * h t := rfl
        linarith
      rcases lt_or_ge 0 (f t) with hft | hft
      · have h3 := h1 hft
        have h4 : deriv f t * h t ≤ lam * deriv h t * h t := by
          nlinarith [mul_nonneg (sub_nonneg.2 hlt.le) hh']
        have h5 := le_of_mul_le_mul_right h4 hht
        linarith
      · have h3 := h2 hft
        nlinarith [mul_nonneg hlam0.le hh']
    have hfin := le_of_ae_deriv_nonpos_of_neg hGL hGs hGd b ⟨hs.2, le_rfl⟩
    have : G b = f b - lam * h b := rfl
    linarith
  -- let the starting time tend to `a`
  set ε : ℝ := f b / (2 * h b) with hε
  have hε0 : 0 < ε := by positivity
  set δ : ℝ := ε / (C + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  set s : ℝ := a + min (b - a) (δ / (Kh + 1)) with hsdef
  have hm0 : 0 < min (b - a) (δ / ((Kh : ℝ) + 1)) :=
    lt_min (by linarith) (div_pos hδ0 (by positivity))
  have hs : s ∈ Ioc a b := ⟨by linarith, by linarith [min_le_left (b - a) (δ / ((Kh : ℝ) + 1))]⟩
  have hhs : h s ≤ δ := by
    have h1 := hh.dist_le_mul s (Ioc_subset_Icc_self hs) a ⟨le_rfl, hab.le⟩
    rw [Real.dist_eq, Real.dist_eq, ha, sub_zero] at h1
    have h2 : |s - a| ≤ δ / ((Kh : ℝ) + 1) := by
      rw [hsdef, add_sub_cancel_left, abs_of_pos hm0]
      exact min_le_right _ _
    have h3 : (Kh : ℝ) * (δ / ((Kh : ℝ) + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [Kh.coe_nonneg]
    calc h s ≤ |h s| := le_abs_self _
      _ ≤ Kh * |s - a| := h1
      _ ≤ Kh * (δ / ((Kh : ℝ) + 1)) := mul_le_mul_of_nonneg_left h2 Kh.coe_nonneg
      _ ≤ δ := h3
  have hCh : C * h s ≤ ε := by
    have h1 : C * h s ≤ C * δ := mul_le_mul_of_nonneg_left hhs hC
    have h2 : C * δ ≤ ε := by
      rw [hδ, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have h1 := key s hs ε hε0
  have h2 : (C * h s + ε) * h b ≤ (ε + ε) * h b :=
    mul_le_mul_of_nonneg_right (by linarith) hhb.le
  have h3 : (ε + ε) * h b = f b := by
    rw [hε]; field_simp; ring
  linarith

end Lightlike.Geodesic
