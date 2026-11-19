import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Lightlike.Spacetime.EHManifold.RegularDomainDivergence

/-!
# A boundary given by a defining function is locally a graph

Let `u` be a `C²` function near `x₀ ∈ ℝⁿ⁺¹` with `u(x₀) = 0` and `du(x₀) ≠ 0`. Then, for some coordinate
`i`, the set `{u ≥ 0}` is near `x₀` the region above or below the graph of a `C²` function `γ : ℝⁿ → ℝ` of
the other coordinates (`exists_graphRegion_of_defining_function`). The function `γ` is the implicit function
of `u` in the coordinate `x_i` (Mathlib's `ContDiffAt.implicitFunction`), cut off by a smooth bump function so
that it is defined and `C²` on all of `ℝⁿ`; the inequality `u ≥ 0` becomes `x_i ≥ γ(x')` because `u` is
strictly monotone in `x_i` near `x₀`.

`exists_graph_atlas_integral_divergence_of_defining_function`: the divergence theorem for a domain `D ⊆ ℝⁿ⁺¹`
that is near every point of its closure of the form `{u ≥ 0}` with `u ∈ C²` and `du ≠ 0` where `u = 0`.
A chart of type (iii) in the definition of a domain with regular boundary of Loomis–Sternberg gives such a
function: its last coordinate.

## References

* L. H. Loomis, S. Sternberg, *Advanced Calculus* (revised edition), chapter 10, section 6: Definition
  (domain with regular boundary), p. 419; Theorem 6.1, p. 421.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- Inserting `0` at the `i`-th place, as a continuous linear map. -/
def insZeroL (i : Fin (n + 1)) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    Fin.insertNth (α := fun _ => (Fin n → ℝ) →L[ℝ] ℝ) i 0 (fun k => ContinuousLinearMap.proj k) j

lemma insZeroL_apply_same (i : Fin (n + 1)) (y : Fin n → ℝ) : insZeroL i y i = 0 := by
  simp [insZeroL]

lemma insZeroL_apply_succAbove (i : Fin (n + 1)) (y : Fin n → ℝ) (k : Fin n) :
    insZeroL i y (i.succAbove k) = y k := by
  simp [insZeroL]

/-- A point is its projection plus its `i`-th coordinate times the `i`-th basis vector. -/
lemma eq_insZeroL_add (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    insZeroL i (i.removeNth x) + x i • (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) = x := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k, h⟩
  · rw [h, Pi.add_apply, insZeroL_apply_same]
    simp
  · rw [h, Pi.add_apply, insZeroL_apply_succAbove]
    simp [Fin.removeNth, Fin.succAbove_ne]

/-- The map `(y, s) ↦ (y, s)` from `ℝⁿ × ℝ` to `ℝⁿ⁺¹`, with `s` at the `i`-th place. -/
def insL (i : Fin (n + 1)) : ((Fin n → ℝ) × ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  (insZeroL i).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ) +
    (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).smulRight (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ)

lemma insL_apply (i : Fin (n + 1)) (p : (Fin n → ℝ) × ℝ) :
    insL i p = insZeroL i p.1 + p.2 • (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) := rfl

lemma insL_removeNth (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : insL i (i.removeNth x, x i) = x := by
  rw [insL_apply]
  exact eq_insZeroL_add i x

/-- A continuous linear map `ℝ → ℝ` that is multiplication by a nonzero number is invertible. -/
lemma isInvertible_of_apply_eq_mul (A : ℝ →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0) (hA : ∀ s, A s = s * c) :
    A.IsInvertible := by
  refine ⟨ContinuousLinearEquiv.equivOfInverse A (c⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_,
    ContinuousLinearMap.ext fun s => rfl⟩
  · intro s
    show c⁻¹ * A s = s
    rw [hA s, mul_comm s, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  · intro s
    show A (c⁻¹ * s) = s
    rw [hA, mul_comm _ s, mul_assoc, inv_mul_cancel₀ hc, mul_one]

/-- **The zero set of a function with positive `i`-th partial derivative is locally a graph**, and the
function is nonnegative exactly above it. -/
theorem exists_graph_of_pos (i : Fin (n + 1)) (u : (Fin (n + 1) → ℝ) → ℝ) (x₀ : Fin (n + 1) → ℝ)
    (hu : ContDiffAt ℝ 2 u x₀) (hu0 : u x₀ = 0) (hpos : 0 < pd i u x₀) :
    ∃ γ : (Fin n → ℝ) → ℝ, ContDiff ℝ 2 γ ∧ ∀ᶠ x in 𝓝 x₀,
      (0 ≤ u x ↔ γ (i.removeNth x) ≤ x i) ∧ (u x ≤ 0 ↔ x i ≤ γ (i.removeNth x)) := by
  have hJp : insL i (i.removeNth x₀, x₀ i) = x₀ := insL_removeNth i x₀
  have hud : DifferentiableAt ℝ u x₀ := hu.differentiableAt (by norm_num)
  have cdf : ContDiffAt ℝ 2 (fun p : (Fin n → ℝ) × ℝ => u (insL i p)) (i.removeNth x₀, x₀ i) := by
    have h1 : ContDiffAt ℝ 2 u (insL i (i.removeNth x₀, x₀ i)) := by
      rw [hJp]
      exact hu
    exact h1.comp _ (insL i).contDiff.contDiffAt
  have hfd : fderiv ℝ (fun p : (Fin n → ℝ) × ℝ => u (insL i p)) (i.removeNth x₀, x₀ i) =
      (fderiv ℝ u x₀).comp (insL i) := by
    have h1 : HasFDerivAt u (fderiv ℝ u x₀) (insL i (i.removeNth x₀, x₀ i)) := by
      rw [hJp]
      exact hud.hasFDerivAt
    exact (h1.comp _ (insL i).hasFDerivAt).fderiv
  have hA : ∀ s : ℝ, ((fderiv ℝ (fun p : (Fin n → ℝ) × ℝ => u (insL i p)) (i.removeNth x₀, x₀ i)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ)) s = s * pd i u x₀ := by
    intro s
    have h0 : insL i ((0 : Fin n → ℝ), s) = s • (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) := by
      rw [insL_apply]
      simp
    rw [hfd]
    show fderiv ℝ u x₀ (insL i ((0 : Fin n → ℝ), s)) = _
    rw [h0, map_smul, smul_eq_mul]
    rfl
  have if₂ := isInvertible_of_apply_eq_mul _ (pd i u x₀) hpos.ne' hA
  -- the implicit function
  obtain ⟨ψ, hψ0, hψeq, hψc⟩ : ∃ ψ : (Fin n → ℝ) → ℝ, ψ (i.removeNth x₀) = x₀ i ∧
      (∀ᶠ y in 𝓝 (i.removeNth x₀), u (insL i (y, ψ y)) = 0) ∧
      ContDiffAt ℝ 2 ψ (i.removeNth x₀) := by
    have pn : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
    refine ⟨cdf.implicitFunction pn if₂, cdf.implicitFunction_apply_self pn if₂, ?_,
      cdf.contDiffAt_implicitFunction pn if₂⟩
    refine (cdf.eventually_apply_implicitFunction pn if₂).mono fun y hy => ?_
    have h1 : u (insL i (i.removeNth x₀, x₀ i)) = 0 := by rw [hJp, hu0]
    exact hy.trans h1
  -- a product neighbourhood on which `u` is differentiable with positive `i`-th derivative
  have hcont : ContinuousAt (fun x => pd i u x) x₀ := by
    unfold pd
    exact (hu.fderiv_right (m := 1) (by norm_num)).continuousAt.clm_apply continuousAt_const
  have hdiffev : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ u x :=
    (hu.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hposev : ∀ᶠ x in 𝓝 x₀, 0 < pd i u x := hcont.eventually (lt_mem_nhds hpos)
  have ht : Tendsto (fun p : (Fin n → ℝ) × ℝ => insL i p) (𝓝 (i.removeNth x₀, x₀ i)) (𝓝 x₀) := by
    have h := (insL i).continuous.tendsto (i.removeNth x₀, x₀ i)
    rwa [hJp] at h
  have hP := ht.eventually (hdiffev.and hposev)
  rw [nhds_prod_eq] at hP
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.1 hP
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff_ball.1 hpb
  have hψball : ∀ᶠ y in 𝓝 (i.removeNth x₀), ψ y ∈ ball (x₀ i) δ := by
    have h : Tendsto ψ (𝓝 (i.removeNth x₀)) (𝓝 (x₀ i)) := by
      have h' := hψc.continuousAt.tendsto
      rwa [hψ0] at h'
    exact h.eventually (ball_mem_nhds _ hδ)
  have hY := ((hpa.and hψball).and hψeq).and (hψc.eventually (by simp))
  obtain ⟨R, hR, hRb⟩ := Metric.eventually_nhds_iff_ball.1 hY
  -- cut the implicit function off
  obtain ⟨b, hbi, hbo⟩ : ∃ b : ContDiffBump (i.removeNth x₀), b.rIn = R / 4 ∧ b.rOut = R / 2 :=
    ⟨⟨R / 4, R / 2, by linarith, by linarith⟩, rfl, rfl⟩
  refine ⟨fun y => b y * ψ y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ ball (i.removeNth x₀) R
    · exact b.contDiffAt.mul (hRb y hy).2
    · have hyt : y ∉ tsupport b := by
        rw [b.tsupport_eq]
        intro hmem
        exact hy (closedBall_subset_ball (by rw [hbo]; linarith) hmem)
      have hev : (fun z => b z * ψ z) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hyt] with z hz
        have hbz : b z = 0 := by
          by_contra hne
          exact hz (subset_tsupport _ hne)
        rw [hbz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hU : ∀ᶠ x : Fin (n + 1) → ℝ in 𝓝 x₀,
        Fin.removeNth (α := fun _ => ℝ) i x ∈ ball (Fin.removeNth (α := fun _ => ℝ) i x₀) (R / 4) ∧
          x i ∈ ball (x₀ i) δ := by
      have h1 : Tendsto (fun x : Fin (n + 1) → ℝ => i.removeNth x) (𝓝 x₀) (𝓝 (i.removeNth x₀)) :=
        (removeNthL i).continuous.tendsto x₀
      have h2 : Tendsto (fun x : Fin (n + 1) → ℝ => x i) (𝓝 x₀) (𝓝 (x₀ i)) :=
        (continuous_apply i).tendsto x₀
      exact (h1.eventually (ball_mem_nhds _ (by linarith))).and
        (h2.eventually (ball_mem_nhds _ hδ))
    filter_upwards [hU] with x hx
    obtain ⟨hy, hs⟩ := hx
    have hyR : i.removeNth x ∈ ball (i.removeNth x₀) R := ball_subset_ball (by linarith) hy
    obtain ⟨⟨⟨hpay, hψb⟩, hψz⟩, -⟩ := hRb _ hyR
    have hγ : b (i.removeNth x) * ψ (i.removeNth x) = ψ (i.removeNth x) := by
      rw [b.one_of_mem_closedBall (by rw [hbi]; exact ball_subset_closedBall hy), one_mul]
    -- `u` along the line through `x` in the `i`-th direction
    obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun s => u (insL i (i.removeNth x, s)) := ⟨_, rfl⟩
    have hder : ∀ s ∈ ball (x₀ i) δ, HasDerivAt h (pd i u (insL i (i.removeNth x, s))) s := by
      intro s hs'
      have hd := (hab hpay (hδb s hs')).1
      have hline : HasDerivAt (fun s : ℝ => insL i (i.removeNth x, s))
          (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) s := by
        have e : (fun s : ℝ => insL i (i.removeNth x, s)) = fun s =>
            insZeroL i (i.removeNth x) + s • (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) :=
          funext fun s => insL_apply i _
        rw [e]
        have h3 := ((hasDerivAt_id s).smul_const (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ)).const_add
          (insZeroL i (i.removeNth x))
        rw [one_smul] at h3
        exact h3
      rw [hh]
      exact hd.hasFDerivAt.comp_hasDerivAt s hline
    have hmono : StrictMonoOn h (ball (x₀ i) δ) := by
      refine strictMonoOn_of_deriv_pos (convex_ball _ _)
        (fun s hs' => (hder s hs').continuousAt.continuousWithinAt) fun s hs' => ?_
      rw [isOpen_ball.interior_eq] at hs'
      rw [(hder s hs').deriv]
      exact (hab hpay (hδb s hs')).2
    have hux : u x = h (x i) := by
      rw [hh]
      show u x = u (insL i (i.removeNth x, x i))
      rw [insL_removeNth]
    have hzero : h (ψ (i.removeNth x)) = 0 := by
      rw [hh]
      exact hψz
    have k1 := hmono.le_iff_le hψb hs
    have k2 := hmono.le_iff_le hs hψb
    rw [hzero] at k1 k2
    show (0 ≤ u x ↔ b (i.removeNth x) * ψ (i.removeNth x) ≤ x i) ∧
      (u x ≤ 0 ↔ x i ≤ b (i.removeNth x) * ψ (i.removeNth x))
    rw [hγ, hux]
    exact ⟨k1, k2⟩

/-- **A set given near `x₀` by `u ≥ 0`, with `u ∈ C²`, `u(x₀) = 0` and `du(x₀) ≠ 0`, is near `x₀` the
region above or below a `C²` graph.** -/
theorem exists_graphRegion_of_defining_function (D : Set (Fin (n + 1) → ℝ)) (x₀ : Fin (n + 1) → ℝ)
    (u : (Fin (n + 1) → ℝ) → ℝ) (hu : ContDiffAt ℝ 2 u x₀) (hu0 : u x₀ = 0)
    (hdu : fderiv ℝ u x₀ ≠ 0) (hD : ∀ᶠ x in 𝓝 x₀, (x ∈ D ↔ 0 ≤ u x)) :
    ∃ U ∈ 𝓝 x₀, ∃ (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)), ContDiff ℝ 2 γ ∧
      ∀ y ∈ U, (y ∈ D ↔ y ∈ graphRegion σ γ i) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), pd i u x₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hdu
    refine ContinuousLinearMap.ext fun v => ?_
    show fderiv ℝ u x₀ v = 0
    have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul]
    have hj : fderiv ℝ u x₀ (Pi.single j (1 : ℝ)) = 0 := hall j
    rw [hj, smul_zero]
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · -- negative derivative: use `-u`
    have hd := (hu.differentiableAt (by norm_num)).hasFDerivAt.neg.fderiv
    have hpd : pd i (fun x => -u x) x₀ = -pd i u x₀ := DFunLike.congr_fun hd _
    obtain ⟨γ, hγ, hev⟩ := exists_graph_of_pos i (fun x => -u x) x₀ hu.neg (by rw [hu0, neg_zero])
      (by rw [hpd]; linarith)
    exact ⟨{x | (x ∈ D ↔ 0 ≤ u x) ∧ (-u x ≤ 0 ↔ x i ≤ γ (i.removeNth x))},
      hD.and (hev.mono fun x h => h.2), SignType.neg, γ, i, hγ,
      fun y hy => hy.1.trans (neg_nonpos.symm.trans hy.2)⟩
  · obtain ⟨γ, hγ, hev⟩ := exists_graph_of_pos i u x₀ hu hu0 hpos
    exact ⟨{x | (x ∈ D ↔ 0 ≤ u x) ∧ (0 ≤ u x ↔ γ (i.removeNth x) ≤ x i)},
      hD.and (hev.mono fun x h => h.1), SignType.pos, γ, i, hγ, fun y hy => hy.1.trans hy.2⟩

/-- **The divergence theorem on a domain with regular boundary given by defining functions.** Near every
point of its closure, `D` is `{u ≥ 0}` for a `C²` function `u` with `du ≠ 0` where `u = 0`. -/
theorem exists_graph_atlas_integral_divergence_of_defining_function (D : Set (Fin (n + 1) → ℝ))
    (hD : MeasurableSet D) (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j))
    (hreg : ∀ x ∈ closure D, ∃ u : (Fin (n + 1) → ℝ) → ℝ, ContDiffAt ℝ 2 u x ∧
      (u x = 0 → fderiv ℝ u x ≠ 0) ∧ ∀ᶠ y in 𝓝 x, (y ∈ D ↔ 0 ≤ u y)) :
    ∃ (ι : Type) (_ : Fintype ι) (ρ : ι → (Fin (n + 1) → ℝ) → ℝ) (σ : ι → SignType)
      (γ : ι → (Fin n → ℝ) → ℝ) (i : ι → Fin (n + 1)),
      (∀ a, ContDiff ℝ ∞ (ρ a)) ∧ (∀ a y, 0 ≤ ρ a y) ∧ (∀ a, ContDiff ℝ 2 (γ a)) ∧
      (∀ a x, x ∈ tsupport (ρ a) → (x ∈ D ↔ x ∈ graphRegion (σ a) (γ a) (i a))) ∧
      (∀ y ∈ closure D, (∃ j, y ∈ tsupport (F j)) → ∑ a, ρ a y = 1) ∧
      ∫ x in D, ∑ j, pd j (F j) x =
        -∑ a, (σ a : ℝ) * graphFlux (γ a) (i a) (fun j y => ρ a y * F j y) := by
  refine exists_graph_atlas_integral_divergence D hD F hF hc fun x hx => ?_
  obtain ⟨u, hu, hdu, hDu⟩ := hreg x hx
  rcases lt_trichotomy (u x) 0 with hneg | hzero | hpos
  · -- impossible: no point of `D` near `x`
    exfalso
    have hev : ∀ᶠ y in 𝓝 x, y ∉ D := by
      filter_upwards [hDu, hu.continuousAt.eventually (gt_mem_nhds hneg)] with y hy1 hy2 hyD
      exact absurd (hy1.1 hyD) (not_le.2 hy2)
    obtain ⟨y, hyD, hyn⟩ := ((mem_closure_iff_frequently.1 hx).and_eventually hev).exists
    exact hyn hyD
  · exact exists_graphRegion_of_defining_function D x u hu hzero (hdu hzero) hDu
  · refine ⟨{y | (y ∈ D ↔ 0 ≤ u y) ∧ 0 < u y},
      hDu.and (hu.continuousAt.eventually (lt_mem_nhds hpos)), SignType.zero, fun _ => 0, 0,
      contDiff_const, fun y hy => ⟨fun _ => Set.mem_univ y, fun _ => hy.1.2 hy.2.le⟩⟩

end Lightlike
