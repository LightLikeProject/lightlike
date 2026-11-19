import Lightlike.Spacetime.KillingOrbit
import Lightlike.Spacetime.SpaceFormKilling
import Lightlike.ODE.LocalFlow

/-!
# Homogeneous and isotropic Riemannian 3-metrics are locally the space forms (route (A) to G1-024)

A metric `G` near a point `p` of a Banach space `E` with a family of Killing fields `Y` indexed like the Killing algebra of the
space form of curvature `k` (`SpaceForm.Idx`: three translations, the rotations), whose brackets close with the structure
constants `SpaceForm.S k` and whose rotations vanish at `p` (isotropy at `p`), is, in the orbit chart
`η ↦ exp(∑ₘ ηₘ Yₘ)(p)`, a constant multiple of the space form `δ/(1 + k|x|²/4)²` in its own orbit chart
(`isometric_spaceForm`): this is the step of Carroll's argument around (8.1) (gr-qc/9712019, pp. 217-219) from homogeneous
and isotropic slices to the maximally symmetric 3-metrics (8.2)-(8.7), with the Killing algebra in place of the isometry
group.
-/

open Set Metric
open scoped NNReal

noncomputable section

namespace Lightlike

open SpaceForm

theorem spaceForm_fderiv_X (k : ℝ) (i : Idx) (x : Fin 3 → ℝ) :
    fderiv ℝ (SpaceForm.X k i) x = match i with | .inl m => dP k m x | .inr ab => dR ab.1 ab.2 := by
  rcases i with m | ⟨a, b⟩
  · exact (hasFDerivAt_P k m x).fderiv
  · exact (hasFDerivAt_R a b x).fderiv

theorem spaceForm_differentiableAt_X (k : ℝ) (i : Idx) (x : Fin 3 → ℝ) :
    DifferentiableAt ℝ (SpaceForm.X k i) x := by
  rcases i with m | ⟨a, b⟩
  · exact (hasFDerivAt_P k m x).differentiableAt
  · exact (hasFDerivAt_R a b x).differentiableAt

/-- The Killing fields of the space form are Killing in coordinates. -/
theorem spaceForm_killing (k : ℝ) (i : Idx) {x : Fin 3 → ℝ} (hx : ψ k x ≠ 0) (u w : Fin 3 → ℝ) :
    fderiv ℝ (metric k) x (SpaceForm.X k i x) u w + metric k x (fderiv ℝ (SpaceForm.X k i) x u) w +
      metric k x u (fderiv ℝ (SpaceForm.X k i) x w) = 0 := by
  rw [spaceForm_fderiv_X]
  rcases i with m | ⟨a, b⟩
  · exact killing_P k m hx u w
  · exact killing_R k a b hx u w

theorem spaceForm_metric_symm (k : ℝ) (x u w : Fin 3 → ℝ) : metric k x u w = metric k x w u := by
  simp only [metric_apply, mul_comm (u _)]

theorem spaceForm_gram_zero (k : ℝ) : gramAt (metric k) (SpaceForm.X k) 0 = gram0 := by
  funext i j
  rcases i with m | ⟨a, b⟩ <;> rcases j with n | ⟨c, d⟩ <;>
    simp [gramAt, metric_zero_apply, X_zero, gram0, Pi.single_apply, eq_comm]

/-- **Isotropy fixes the Gram matrix.** If the rotations vanish at `p`, are Killing there, and satisfy
`[R_ab, Pₘ] = δₘᵦ P_a - δₘₐ P_b` at `p`, then the Gram matrix of the family at `p` is `c` times that of the space form at
the origin, `c = G(p)(P₀, P₀)`. -/
theorem gram_of_isotropy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Y : Idx → E → E) (p : E)
    (hR0 : ∀ a b : Fin 3, Y (.inr (a, b)) p = 0)
    (hK : ∀ a b : Fin 3, ∀ u w : E, fderiv ℝ G p (Y (.inr (a, b)) p) u w + G p (fderiv ℝ (Y (.inr (a, b))) p u) w +
      G p u (fderiv ℝ (Y (.inr (a, b))) p w) = 0)
    (hbr : ∀ (a b m : Fin 3), VectorField.lieBracket ℝ (Y (.inr (a, b))) (Y (.inl m)) p =
      ∑ e, S k (.inr (a, b)) (.inl m) e • Y e p)
    (hsym : ∀ u w : E, G p u w = G p w u) :
    gramAt G Y p = G p (Y (.inl 0) p) (Y (.inl 0) p) • gram0 := by
  set Γ : Fin 3 → Fin 3 → ℝ := fun m n => G p (Y (.inl m) p) (Y (.inl n) p) with hΓ
  -- `D_ab Pₘ = δₘₐ P_b - δₘᵦ P_a` at `p`
  have hD : ∀ a b m, fderiv ℝ (Y (.inr (a, b))) p (Y (.inl m) p) =
      (if m = a then (1 : ℝ) else 0) • Y (.inl b) p - (if m = b then (1 : ℝ) else 0) • Y (.inl a) p := by
    intro a b m
    have h := hbr a b m
    rw [VectorField.lieBracket, hR0, map_zero, zero_sub] at h
    have hsum : ∑ e, S k (.inr (a, b)) (.inl m) e • Y e p =
        (if m = b then (1 : ℝ) else 0) • Y (.inl a) p - (if m = a then (1 : ℝ) else 0) • Y (.inl b) p := by
      simp only [S, sub_smul, Finset.sum_sub_distrib]
      congr 1 <;> split_ifs <;> simp [ind, ite_smul, Finset.sum_ite_eq']
    rw [hsum] at h
    rw [← neg_neg (fderiv ℝ (Y (.inr (a, b))) p (Y (.inl m) p)), h]
    abel
  -- the skewness relations
  have hskew : ∀ a b m n, (if m = a then Γ b n else 0) - (if m = b then Γ a n else 0) +
      ((if n = a then Γ m b else 0) - (if n = b then Γ m a else 0)) = 0 := by
    intro a b m n
    have h := hK a b (Y (.inl m) p) (Y (.inl n) p)
    rw [hR0, map_zero, zero_apply, zero_apply, zero_add, hD, hD] at h
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] at h
    simp only [hΓ]
    split_ifs at h ⊢ <;> linarith
  have hdiag : ∀ m n : Fin 3, Γ m n = if m = n then Γ 0 0 else 0 := by
    intro m n
    by_cases hmn : m = n
    · subst hmn
      simp only [ite_true]
      by_cases hm : m = 0
      · rw [hm]
      · have := hskew 0 m 0 m
        simp [hm, Ne.symm hm] at this
        linarith
    · simp only [hmn, ite_false]
      have := hskew m n m m
      simp [hmn] at this
      have hs : Γ n m = Γ m n := hsym _ _
      linarith
  funext i j
  rcases i with m | ⟨a, b⟩ <;> rcases j with n | ⟨c, d⟩
  · simp only [gramAt, Pi.smul_apply, smul_eq_mul, gram0]
    have := hdiag m n
    simp only [hΓ] at this
    rw [this]; split_ifs <;> simp
  · simp [gramAt, gram0, hR0]
  · simp [gramAt, gram0, hR0]
  · simp [gramAt, gram0, hR0]

section Orbit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ι : Type*} [Fintype ι]
  {Y : ι → E → E} {q₀ : (ι → ℝ) × E} {a r T : ℝ} {K : ℝ≥0} {Ψ : ℝ → (ι → ℝ) × E → (ι → ℝ) × E}

omit [CompleteSpace E] in
/-- The suspension flow from `(0, p)` is stationary. -/
theorem susp_flow_zero (h : ODE.IsFlowBox (suspField Y) q₀ a r T K Ψ) {p : E}
    (hq : ((0 : ι → ℝ), p) ∈ ball q₀ r) {t : ℝ} (ht : t ∈ Icc (-T) T) : Ψ t (0, p) = (0, p) := by
  have hd : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun s => Ψ s (0, p)) 0 (Icc (-T) T) s := by
    intro s hs
    have := (h.hasDerivAt _ hq s hs).hasDerivWithinAt (s := Icc (-T) T)
    have h1 := susp_flow_fst h hq hs
    simp only at h1
    have h0 : suspField Y (Ψ s (0, p)) = 0 := by
      simp only [suspField, h1, Pi.zero_apply, zero_smul, Finset.sum_const_zero]; rfl
    rwa [h0] at this
  rw [eq_zero_of_hasDerivWithinAt_zero h.T_pos hd ht, h.flow_zero _ hq]

/-- The derivative of the orbit map at the origin: `DΨ_t(0, p)(ζ, 0) = (ζ, t ∑ₑ ζₑ Yₑ(p))`. -/
theorem fderiv_susp_flow_zero (h : ODE.IsFlowBox (suspField Y) q₀ a r T K Ψ)
    (hX : ∀ c, ∀ q ∈ ball q₀ a, DifferentiableAt ℝ (Y c) q.2) (S : ι → ι → ι → ℝ)
    (hS : ∀ a' c, ∀ q ∈ ball q₀ a, VectorField.lieBracket ℝ (Y a') (Y c) q.2 = ∑ e, S a' c e • Y e q.2)
    {p : E} (hq : ((0 : ι → ℝ), p) ∈ ball q₀ r) (ζ : ι → ℝ) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    fderiv ℝ (Ψ t) (0, p) (ζ, 0) = (ζ, t • ∑ e, ζ e • Y e p) := by
  have hd : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun s : ℝ => s • ζ)
      (fun e => ζ e - ∑ c, (s • ζ) c * ∑ a', ((0 : ι → ℝ), p).1 a' * S a' c e) (Icc (-T) T) s := by
    intro s _
    have := ((hasDerivAt_id s).smul_const ζ).hasDerivWithinAt (s := Icc (-T) T)
    convert this using 1
    all_goals first | rfl | (funext e; simp)
  have := fderiv_susp_flow h hX S hS hq ζ (fun s => s • ζ) hd ht
  simp only [zero_smul, Pi.zero_apply, Finset.sum_const_zero, susp_flow_zero h hq ht] at this
  rw [this]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem mem_ball_snd {F : Type*} [NormedAddCommGroup F] {q q₀ : (ι → ℝ) × F} {a : ℝ} (hq : q ∈ ball q₀ a) :
    q.2 ∈ ball q₀.2 a := by
  rw [mem_ball] at hq ⊢
  exact lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hq

theorem mem_ball_pair {F : Type*} [NormedAddCommGroup F] {ξ : ι → ℝ} {p : F} {r : ℝ} (hr : 0 < r)
    (hξ : ξ ∈ ball (0 : ι → ℝ) r) : ((ξ, p) : (ι → ℝ) × F) ∈ ball ((0 : ι → ℝ), p) r := by
  rw [mem_ball] at hξ ⊢
  rw [Prod.dist_eq, dist_self, max_lt_iff]
  exact ⟨hξ, hr⟩

end Orbit

theorem contDiff_nsq : ContDiff ℝ 1 nsq := by
  unfold nsq
  exact ContDiff.sum fun i _ => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).contDiff.pow 2

theorem spaceForm_contDiff_X (k : ℝ) (i : Idx) : ContDiff ℝ 1 (SpaceForm.X k i) := by
  rcases i with m | ⟨a, b⟩
  · show ContDiff ℝ 1 (P k m)
    unfold P
    have h1 : ContDiff ℝ 1 (fun x : Fin 3 → ℝ => (1 - k * nsq x / 4) • (Pi.single m 1 : Fin 3 → ℝ)) :=
      ContDiff.smul (f := fun x => 1 - k * nsq x / 4) (g := fun _ => (Pi.single m 1 : Fin 3 → ℝ))
        (contDiff_const.sub ((contDiff_const.mul contDiff_nsq).div_const 4)) contDiff_const
    have h2 : ContDiff ℝ 1 (fun x : Fin 3 → ℝ => (k / 2 * x m) • x) :=
      ContDiff.smul (f := fun x : Fin 3 → ℝ => k / 2 * x m) (g := fun x => x)
        (contDiff_const.mul (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) m).contDiff) contDiff_id
    exact h1.add h2
  · show ContDiff ℝ 1 (R a b)
    unfold R
    have ha : ContDiff ℝ 1 (fun x : Fin 3 → ℝ => x a • (Pi.single b 1 : Fin 3 → ℝ)) :=
      ContDiff.smul (f := fun x : Fin 3 → ℝ => x a) (g := fun _ => (Pi.single b 1 : Fin 3 → ℝ))
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) a).contDiff contDiff_const
    have hb : ContDiff ℝ 1 (fun x : Fin 3 → ℝ => x b • (Pi.single a 1 : Fin 3 → ℝ)) :=
      ContDiff.smul (f := fun x : Fin 3 → ℝ => x b) (g := fun _ => (Pi.single a 1 : Fin 3 → ℝ))
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) b).contDiff contDiff_const
    exact ha.sub hb

theorem contDiffAt_suspField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    {Y : ι → E → E} {q : (ι → ℝ) × E} (hY : ∀ i, ContDiffAt ℝ 1 (Y i) q.2) : ContDiffAt ℝ 1 (suspField Y) q := by
  unfold suspField
  refine contDiffAt_const.prodMk (ContDiffAt.sum fun a _ => ?_)
  have h1 : ContDiffAt ℝ 1 (fun q : (ι → ℝ) × E => q.1 a) q :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) a).comp
      (ContinuousLinearMap.fst ℝ (ι → ℝ) E)).contDiff.contDiffAt
  exact ContDiffAt.smul (f := fun q : (ι → ℝ) × E => q.1 a) (g := fun q => Y a q.2) h1
    ((hY a).comp q contDiffAt_snd)

theorem psi_ne_zero_of_mem_ball (k : ℝ) {y : Fin 3 → ℝ} (hy : y ∈ ball (0 : Fin 3 → ℝ) (1 / (|k| + 1))) :
    ψ k y ≠ 0 := by
  have hk0 : 0 ≤ |k| := abs_nonneg k
  set δ := 1 / (|k| + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one (by positivity)]; linarith
  have hkδ : |k| * δ < 1 := by rw [hδ, mul_one_div, div_lt_one (by positivity)]; linarith
  rw [mem_ball, dist_zero_right] at hy
  have hi : ∀ i, y i ^ 2 ≤ ‖y‖ ^ 2 := fun i => by
    have := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (y i), sq_abs (y i), norm_nonneg y]
  have hn : nsq y ≤ 3 * ‖y‖ ^ 2 := by
    unfold nsq; rw [Fin.sum_univ_three]; linarith [hi 0, hi 1, hi 2]
  have hn0 : 0 ≤ nsq y := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hy2 : ‖y‖ ^ 2 ≤ δ ^ 2 := by nlinarith [norm_nonneg y]
  have hb : |k * nsq y / 4| < 1 := by
    rw [abs_div, abs_mul, abs_of_nonneg hn0, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have : |k| * nsq y ≤ |k| * (3 * δ ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hk0
    have : |k| * δ ^ 2 ≤ |k| * δ := mul_le_mul_of_nonneg_left (by nlinarith) hk0
    rw [div_lt_one (by norm_num)]
    nlinarith
  unfold ψ
  have := neg_abs_le (k * nsq y / 4)
  intro h0; linarith

/-- **A homogeneous and isotropic 3-metric is a constant multiple of the space form of curvature `k`, in orbit charts.**
Let `Y` be a family of fields near `p`, indexed like the Killing algebra of the space form (`Idx`), `C¹` at `p`, Killing for
a symmetric `G` near `p`, with the brackets `SpaceForm.S k` of that algebra near `p`, and with the rotations vanishing at
`p`. Then for some `T > 0`, the orbit maps `o ξ = exp(T ∑ ξₑ Yₑ)(p)` and `o₂ ξ = exp(T ∑ ξₑ Xₑ)(0)` of `Y` and of the
space form's fields satisfy `G(o ξ)(Do ζ, Do ζ') = c · δ/(1 + k|x|²/4)²(o₂ ξ)(Do₂ ζ, Do₂ ζ')` near `ξ = 0`, with
`c = G(p)(P₀(p), P₀(p))`; at `ξ = 0`, `Do ζ = T ∑ ζₑ Yₑ(p)` and `Do₂ ζ = T ∑ ζₑ Xₑ(0)` (on the translation directions,
`T` times the identity of `ℝ³`, so `o₂` is a chart there by the inverse function theorem). -/
theorem isometric_spaceForm (k : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Y : Idx → E → E) (p : E) {ρ : ℝ} (hρ : 0 < ρ)
    (hYc : ∀ i, ContDiffAt ℝ 1 (Y i) p)
    (hYd : ∀ i, ∀ y ∈ ball p ρ, DifferentiableAt ℝ (Y i) y)
    (hGd : ∀ y ∈ ball p ρ, DifferentiableAt ℝ G y)
    (hK : ∀ i, ∀ y ∈ ball p ρ, ∀ u w : E,
      fderiv ℝ G y (Y i y) u w + G y (fderiv ℝ (Y i) y u) w + G y u (fderiv ℝ (Y i) y w) = 0)
    (hS : ∀ i j, ∀ y ∈ ball p ρ, VectorField.lieBracket ℝ (Y i) (Y j) y = ∑ e, S k i j e • Y e y)
    (hsym : ∀ y ∈ ball p ρ, ∀ u w : E, G y u w = G y w u)
    (hiso : ∀ a b : Fin 3, Y (.inr (a, b)) p = 0) :
    ∃ (T ε : ℝ) (o : (Idx → ℝ) → E) (o₂ : (Idx → ℝ) → (Fin 3 → ℝ)), 0 < T ∧ 0 < ε ∧ o 0 = p ∧ o₂ 0 = 0 ∧
      (∀ ξ ∈ ball (0 : Idx → ℝ) ε, DifferentiableAt ℝ o ξ ∧ DifferentiableAt ℝ o₂ ξ) ∧
      (∀ ζ, fderiv ℝ o 0 ζ = T • ∑ e, ζ e • Y e p) ∧
      (∀ ζ, fderiv ℝ o₂ 0 ζ = T • ∑ e, ζ e • SpaceForm.X k e 0) ∧
      ∀ ξ ∈ ball (0 : Idx → ℝ) ε, ∀ ζ ζ',
        G (o ξ) (fderiv ℝ o ξ ζ) (fderiv ℝ o ξ ζ') =
          G p (Y (.inl 0) p) (Y (.inl 0) p) * metric k (o₂ ξ) (fderiv ℝ o₂ ξ ζ) (fderiv ℝ o₂ ξ ζ') := by
  -- flow boxes
  obtain ⟨A₁, hA₁, H₁⟩ := ODE.exists_isFlowBox (contDiffAt_suspField (q := ((0 : Idx → ℝ), p)) hYc)
  obtain ⟨r₁, T₁, K₁, Ψ₁, h₁⟩ := H₁ (min A₁ ρ) (lt_min hA₁ hρ) (min_le_left _ _)
  obtain ⟨A₂, hA₂, H₂⟩ := ODE.exists_isFlowBox (contDiffAt_suspField (q := ((0 : Idx → ℝ), (0 : Fin 3 → ℝ)))
    fun i => (spaceForm_contDiff_X k i).contDiffAt)
  have hδ : (0 : ℝ) < 1 / (|k| + 1) := by positivity
  obtain ⟨r₂, T₂, K₂, Ψ₂, h₂⟩ := H₂ (min A₂ (1 / (|k| + 1))) (lt_min hA₂ hδ) (min_le_left _ _)
  set T := min T₁ T₂
  have hT : 0 < T := lt_min h₁.T_pos h₂.T_pos
  have h₁' := h₁.mono h₁.r_pos le_rfl hT (min_le_left _ _)
  have h₂' := h₂.mono h₂.r_pos le_rfl hT (min_le_right _ _)
  have hTI : T ∈ Icc (-T) T := ⟨by linarith, le_rfl⟩
  -- the hypotheses on the balls of the flow boxes
  have hb₁ : ∀ q ∈ ball ((0 : Idx → ℝ), p) (min A₁ ρ), q.2 ∈ ball p ρ := fun q hq =>
    ball_subset_ball (min_le_right _ _) (mem_ball_snd hq)
  have hb₂ : ∀ q ∈ ball ((0 : Idx → ℝ), (0 : Fin 3 → ℝ)) (min A₂ (1 / (|k| + 1))), ψ k q.2 ≠ 0 := fun q hq =>
    psi_ne_zero_of_mem_ball k (ball_subset_ball (min_le_right _ _) (mem_ball_snd hq))
  set c := G p (Y (.inl 0) p) (Y (.inl 0) p)
  have hΓ : gramAt G Y p = c • gramAt (metric k) (SpaceForm.X k) 0 := by
    rw [spaceForm_gram_zero]
    refine gram_of_isotropy k G Y p hiso (fun a b u w => hK _ p (mem_ball_self hρ) u w)
      (fun a b m => hS _ _ p (mem_ball_self hρ)) (hsym p (mem_ball_self hρ))
  set ε := min r₁ r₂
  have hε : 0 < ε := lt_min h₁.r_pos h₂.r_pos
  have hq₁ : ∀ ξ ∈ ball (0 : Idx → ℝ) ε, ((ξ, p) : (Idx → ℝ) × E) ∈ ball ((0 : Idx → ℝ), p) r₁ := fun ξ hξ =>
    mem_ball_pair h₁.r_pos (ball_subset_ball (min_le_left _ _) hξ)
  have hq₂ : ∀ ξ ∈ ball (0 : Idx → ℝ) ε, ((ξ, (0 : Fin 3 → ℝ)) : (Idx → ℝ) × (Fin 3 → ℝ)) ∈
      ball ((0 : Idx → ℝ), (0 : Fin 3 → ℝ)) r₂ := fun ξ hξ =>
    mem_ball_pair h₂.r_pos (ball_subset_ball (min_le_right _ _) hξ)
  -- the orbit maps and their derivatives
  set o : (Idx → ℝ) → E := fun ξ => (Ψ₁ T (ξ, p)).2
  set o₂ : (Idx → ℝ) → (Fin 3 → ℝ) := fun ξ => (Ψ₂ T (ξ, 0)).2
  have hdo : ∀ ξ ∈ ball (0 : Idx → ℝ) ε, HasFDerivAt o ((ContinuousLinearMap.snd ℝ (Idx → ℝ) E).comp
      ((fderiv ℝ (Ψ₁ T) (ξ, p)).comp (ContinuousLinearMap.inl ℝ (Idx → ℝ) E))) ξ := fun ξ hξ =>
    hasFDerivAt_snd.comp ξ ((h₁'.differentiableAt_flow (hq₁ ξ hξ) hTI).hasFDerivAt.comp ξ
      (hasFDerivAt_prodMk_left ξ p))
  have hdo₂ : ∀ ξ ∈ ball (0 : Idx → ℝ) ε, HasFDerivAt o₂ ((ContinuousLinearMap.snd ℝ (Idx → ℝ) (Fin 3 → ℝ)).comp
      ((fderiv ℝ (Ψ₂ T) (ξ, 0)).comp (ContinuousLinearMap.inl ℝ (Idx → ℝ) (Fin 3 → ℝ)))) ξ := fun ξ hξ =>
    hasFDerivAt_snd.comp ξ ((h₂'.differentiableAt_flow (hq₂ ξ hξ) hTI).hasFDerivAt.comp ξ
      (hasFDerivAt_prodMk_left ξ (0 : Fin 3 → ℝ)))
  have hX₁ : ∀ c', ∀ q ∈ ball ((0 : Idx → ℝ), p) (min A₁ ρ), DifferentiableAt ℝ (Y c') q.2 := fun c' q hq =>
    hYd c' _ (hb₁ q hq)
  have hS₁ : ∀ a' c', ∀ q ∈ ball ((0 : Idx → ℝ), p) (min A₁ ρ),
      VectorField.lieBracket ℝ (Y a') (Y c') q.2 = ∑ e, S k a' c' e • Y e q.2 := fun a' c' q hq =>
    hS a' c' _ (hb₁ q hq)
  have hX₂ : ∀ c', ∀ q ∈ ball ((0 : Idx → ℝ), (0 : Fin 3 → ℝ)) (min A₂ (1 / (|k| + 1))),
      DifferentiableAt ℝ (SpaceForm.X k c') q.2 := fun c' q _ => spaceForm_differentiableAt_X k c' _
  have hS₂ : ∀ a' c', ∀ q ∈ ball ((0 : Idx → ℝ), (0 : Fin 3 → ℝ)) (min A₂ (1 / (|k| + 1))),
      VectorField.lieBracket ℝ (SpaceForm.X k a') (SpaceForm.X k c') q.2 = ∑ e, S k a' c' e • SpaceForm.X k e q.2 :=
    fun a' c' q _ => lieBracket_X k a' c' _
  have h0 : (0 : Idx → ℝ) ∈ ball (0 : Idx → ℝ) ε := mem_ball_self hε
  refine ⟨T, ε, o, o₂, hT, hε, ?_, ?_, fun ξ hξ => ⟨(hdo ξ hξ).differentiableAt, (hdo₂ ξ hξ).differentiableAt⟩,
    fun ζ => ?_, fun ζ => ?_, fun ξ hξ ζ ζ' => ?_⟩
  · show (Ψ₁ T (0, p)).2 = p
    rw [susp_flow_zero h₁' (hq₁ 0 h0) hTI]
  · show (Ψ₂ T (0, 0)).2 = 0
    rw [susp_flow_zero h₂' (hq₂ 0 h0) hTI]
  · rw [(hdo 0 h0).fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.coe_snd']
    rw [fderiv_susp_flow_zero h₁' hX₁ (S k) hS₁ (hq₁ 0 h0) ζ hTI]
  · rw [(hdo₂ 0 h0).fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.coe_snd']
    rw [fderiv_susp_flow_zero h₂' hX₂ (S k) hS₂ (hq₂ 0 h0) ζ hTI]
  · rw [(hdo ξ hξ).fderiv, (hdo₂ ξ hξ).fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.coe_snd']
    exact orbit_comparison h₁' h₂' (S k) hX₁ hS₁ G (fun q hq => hGd _ (hb₁ q hq))
      (fun c' q hq u w => hK c' _ (hb₁ q hq) u w) (fun q hq u w => hsym _ (hb₁ q hq) u w)
      hX₂ hS₂ (metric k) (fun q hq => (hasFDerivAt_metric k (hb₂ q hq)).differentiableAt)
      (fun c' q hq u w => spaceForm_killing k c' (hb₂ q hq) u w) (fun q _ u w => spaceForm_metric_symm k _ u w)
      (hq₁ ξ hξ) (hq₂ ξ hξ) c hΓ ζ ζ' hTI

end Lightlike
