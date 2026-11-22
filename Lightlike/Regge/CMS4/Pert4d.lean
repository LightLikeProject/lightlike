import Lightlike.Regge.CMS4.Pert4c

/-!
# The first-order coefficient of the class angle sum vanishes (dimension 4)

The moved star (vertices moved by the normal-coordinate change `Phi t`) is a Euclidean star with the
same combinatorics as the Gram star. Its class angle sum `F t` is in `2π ℤ` for small `t`
(`eventually_chain_int`), continuous, and `F 0 = 2π`; hence `F` is constant `2π` near `0` and its
derivative at `0`, which is `clsSum4 c (angC14 g m)`, vanishes.

## Main results

* `eventually_cls_int`: `F t ∈ 2π ℤ` for small `t`, in every admissible class.
* `hasDerivAt_clsAng`: `F` has derivative `clsSum4 c (angC14 g m)` at `0`.
* `first_order4`: **the `first_order` field of `JetStarCore4`**.
-/

open Lightlike Real Filter Topology
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3 Lightlike.Geodesic

variable (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)

/-- The class angle sum of the moved star. -/
noncomputable def clsAng (m : Fin 4 → ℝ) (c : Fin 4 → Fin 3) (t : ℝ) : ℝ :=
  clsSum4 c (fun σ h => incAng4 h (Qt g m σ h t))

/-- A certified quad class has an integral moved angle sum for small `t`. -/
theorem eventually_quad_int {m : Fin 4 → ℝ} (hG : (g m).PosDef) (hs : ∀ y, (g y)ᵀ = g y)
    (c : Fin 4 → Fin 3) (hq : quadCert c = true) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∃ k : ℤ, clsAng g m c t = 2 * π * k := by
  have hq' := hq
  simp only [quadCert, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq'
  obtain ⟨⟨⟨⟨⟨⟨hL, hlen⟩, hnd⟩, hcl⟩, hadj⟩, hLm⟩, hmL⟩ := hq'
  have key := eventually_chain_int g hG hs c 4 (by norm_num)
    (fun i => (chainOf c).getD i default) (fun i hi => chain_mem_quad c hq i hi)
    (fun i hi => by
      have := (hadj i (List.mem_range.2 hi)).2
      simpa only [adjB, decide_eq_true_eq] using this)
    (fun i hi => by
      have := (hadj i (List.mem_range.2 hi)).1
      simp only [posB, decide_eq_true_eq] at this
      exact this)
    hcl
  filter_upwards [key] with t ⟨k, hk⟩
  exact ⟨k, by unfold clsAng; rw [clsSum4_quad c hq]; exact hk⟩

/-- A certified hex class has an integral moved angle sum for small `t`. -/
theorem eventually_hex_int {m : Fin 4 → ℝ} (hG : (g m).PosDef) (hs : ∀ y, (g y)ᵀ = g y)
    (c : Fin 4 → Fin 3) (hq : hexCert c = true) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∃ k : ℤ, clsAng g m c t = 2 * π * k := by
  have hq' := hq
  simp only [hexCert, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hL, hlen⟩, hnd⟩, hcl⟩, hadj⟩, ha1⟩, ha2⟩, hLm⟩, hmL⟩ := hq'
  have key := eventually_chain_int g hG hs c 6 (by norm_num)
    (fun i => (chainOf c).getD i default) (fun i hi => chain_mem_hex c hq i hi)
    (fun i hi => by
      have := (hadj i (List.mem_range.2 hi)).2
      simpa only [adjB, decide_eq_true_eq] using this)
    (fun i hi => by
      have := (hadj i (List.mem_range.2 hi)).1
      simp only [posB, decide_eq_true_eq] at this
      exact this)
    hcl
  filter_upwards [key] with t ⟨k, hk⟩
  exact ⟨k, by unfold clsAng; rw [clsSum4_hex c hq]; exact hk⟩

/-- **The moved class angle sum is integral for small `t`** in every admissible class. -/
theorem eventually_cls_int {m : Fin 4 → ℝ} (hG : (g m).PosDef) (hs : ∀ y, (g y)ᵀ = g y)
    (c : Fin 4 → Fin 3) (hc : ClsOK c) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∃ k : ℤ, clsAng g m c t = 2 * π * k := by
  obtain ⟨n, hn, rfl⟩ := exists_clsOfNat c
  rcases cert_all ⟨n, hn⟩ (clsOKB_of_clsOK hc) with h | h
  · exact eventually_quad_int g hG hs _ h
  · exact eventually_hex_int g hG hs _ h

open Classical in
/-- The moved class angle sum has derivative `clsSum4 c (angC14 g m)` at `t = 0`. -/
theorem hasDerivAt_clsAng {m : Fin 4 → ℝ} (hG : (g m).PosDef) (hs : ∀ y, (g y)ᵀ = g y)
    (c : Fin 4 → Fin 3) :
    HasDerivAt (clsAng g m c) (clsSum4 c (angC14 g m)) 0 := by
  unfold clsAng clsSum4
  have hd : ∀ σ : Fin 24, ∀ h : Fin 10, HasDerivAt
      (fun t => if InClass4 c σ h then incAng4 h (Qt g m σ h t) else 0)
      (if InClass4 c σ h then angC14 g m σ h else 0) 0 := by
    intro σ h
    by_cases hh : InClass4 c σ h
    · simp only [hh, ↓reduceIte]
      exact hasDerivAt_angQt g hG hs σ h
    · simp only [hh, ↓reduceIte]
      exact hasDerivAt_const _ _
  exact HasDerivAt.fun_sum fun σ _ => HasDerivAt.fun_sum fun h _ => hd σ h

/-- At `t = 0` the moved class angle sum is `2π`. -/
theorem clsAng_zero {m : Fin 4 → ℝ} (hG : (g m).PosDef) (hs : ∀ y, (g y)ᵀ = g y)
    (c : Fin 4 → Fin 3) (hc : ClsOK c) : clsAng g m c 0 = 2 * π := by
  have hdet : IsUnit (g m).det := isUnit_iff_ne_zero.2 hG.det_pos.ne'
  have := angle_sum4 g hG c hc
  unfold clsAng
  simpa only [Qt_zero g hs m hdet] using this

/-- **The `first_order` field of `JetStarCore4` in dimension 4.** For a symmetric metric field with
`g m` positive definite, the first-order coefficients of the dihedral angles add up to zero in
every admissible class. -/
theorem first_order4 {m : Fin 4 → ℝ} (hG : (g m).PosDef) (hs : ∀ y, (g y)ᵀ = g y)
    (c : Fin 4 → Fin 3) (hc : ClsOK c) : clsSum4 c (angC14 g m) = 0 := by
  have hder := hasDerivAt_clsAng g hG hs c
  have hcont : ContinuousAt (clsAng g m c) 0 := hder.continuousAt
  have h0 := clsAng_zero g hG hs c hc
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), |clsAng g m c t - 2 * π| < π := by
    have := hcont.eventually (Metric.ball_mem_nhds (clsAng g m c 0) pi_pos)
    filter_upwards [this] with t ht
    rw [h0] at ht
    simpa [Metric.mem_ball, Real.dist_eq] using ht
  have heq : ∀ᶠ t in 𝓝 (0 : ℝ), clsAng g m c t = 2 * π := by
    filter_upwards [eventually_cls_int g hG hs c hc, hnear] with t ⟨k, hk⟩ hn
    rw [hk] at hn ⊢
    have h1 : |(k : ℝ) - 1| < 1 := by
      have : 2 * π * k - 2 * π = π * (2 * ((k : ℝ) - 1)) := by ring
      rw [this, abs_mul, abs_of_pos pi_pos] at hn
      have h2 : |2 * ((k : ℝ) - 1)| < 1 := by
        by_contra hcon
        have hcon := not_lt.1 hcon
        nlinarith [pi_pos]
      rw [abs_mul] at h2
      simp only [abs_two] at h2
      linarith
    have hk1 : k = 1 := by
      have a : ((k - 1 : ℤ) : ℝ) = (k : ℝ) - 1 := by push_cast; ring
      have : |k - 1| < 1 := by
        have := h1
        rw [← a] at this
        exact_mod_cast this
      have := abs_lt.1 this
      omega
    rw [hk1]
    simp
  have hc2 : HasDerivAt (fun _ : ℝ => 2 * π) (clsSum4 c (angC14 g m)) 0 :=
    hder.congr_of_eventuallyEq (heq.mono fun t ht => ht.symm)
  exact hc2.unique (hasDerivAt_const _ _)

end Lightlike.Regge4
