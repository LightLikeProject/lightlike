import Lightlike.Spacetime.KillingOrbitChart

/-!
# The FLRW form from a Killing algebra isotropic along a worldline (route (A) to G1-024, four dimensions)

A metric `G` near a point of a Banach space with a family of Killing fields `Y` of the space-form type (`SpaceForm.Idx`,
structure constants `SpaceForm.S k`) whose rotations vanish along a `C¹` curve `c` (the worldline of an isotropic observer)
takes the FLRW form in the chart `Φ(t, ξ) = exp(T ∑ ξₑ Yₑ)(c t)` (`flrw_of_killing_algebra`):
`G(∂_t, ∂_t) = G(c t)(c' t, c' t)`, `G(∂_t, ∂_ζ) = 0` and `G(∂_ζ, ∂_ζ') = a(t) · δ/(1 + k|x|²/4)²(o₂ ξ)(Do₂ ζ, Do₂ ζ')`, with
`a(t) = G(c t)(P₀, P₀)` and `o₂` the orbit chart of the space form: Carroll's (8.1) (gr-qc/9712019, pp. 217-218),
`ds² = -dt² + a²(t) γ`, with `γ` maximally symmetric, up to the normalisation of `t`.
-/

open Set Metric
open scoped NNReal

noncomputable section

namespace Lightlike

open SpaceForm

section Time

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At a point where the rotations vanish and are Killing, `D R_ab(Pₘ) = δₘₐ P_b - δₘᵦ P_a`. -/
theorem fderiv_rot_trans (k : ℝ) (Y : Idx → E → E) (y : E) (hR0 : ∀ a b : Fin 3, Y (.inr (a, b)) y = 0)
    (hbr : ∀ (a b m : Fin 3), VectorField.lieBracket ℝ (Y (.inr (a, b))) (Y (.inl m)) y =
      ∑ e, S k (.inr (a, b)) (.inl m) e • Y e y) (a b m : Fin 3) :
    fderiv ℝ (Y (.inr (a, b))) y (Y (.inl m) y) =
      (if m = a then (1 : ℝ) else 0) • Y (.inl b) y - (if m = b then (1 : ℝ) else 0) • Y (.inl a) y := by
  have h := hbr a b m
  rw [VectorField.lieBracket, hR0, map_zero, zero_sub] at h
  have hsum : ∑ e, S k (.inr (a, b)) (.inl m) e • Y e y =
      (if m = b then (1 : ℝ) else 0) • Y (.inl a) y - (if m = a then (1 : ℝ) else 0) • Y (.inl b) y := by
    simp only [S, sub_smul, Finset.sum_sub_distrib]
    congr 1 <;> split_ifs <;> simp [ind, ite_smul, Finset.sum_ite_eq']
  rw [hsum] at h
  rw [← neg_neg (fderiv ℝ (Y (.inr (a, b))) y (Y (.inl m) y)), h]
  abel

/-- **Isotropy kills the cross terms.** At a point where the rotations vanish and are Killing, a vector `w` that every
rotation fixes to first order (`D R_ab(w) = 0`) is orthogonal to all the fields. -/
theorem pairing_zero_of_isotropy (k : ℝ) (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Y : Idx → E → E) (y w : E)
    (hR0 : ∀ a b : Fin 3, Y (.inr (a, b)) y = 0)
    (hK : ∀ a b : Fin 3, ∀ u w : E, fderiv ℝ G y (Y (.inr (a, b)) y) u w + G y (fderiv ℝ (Y (.inr (a, b))) y u) w +
      G y u (fderiv ℝ (Y (.inr (a, b))) y w) = 0)
    (hbr : ∀ (a b m : Fin 3), VectorField.lieBracket ℝ (Y (.inr (a, b))) (Y (.inl m)) y =
      ∑ e, S k (.inr (a, b)) (.inl m) e • Y e y)
    (hw : ∀ a b : Fin 3, fderiv ℝ (Y (.inr (a, b))) y w = 0) (e : Idx) : G y w (Y e y) = 0 := by
  rcases e with m | ⟨a, b⟩
  · -- choose `a ≠ m` and use the Killing equation of `R_{a m}` on `(w, P_a)`
    obtain ⟨a, ha⟩ : ∃ a : Fin 3, a ≠ m := ⟨m + 1, by fin_cases m <;> decide⟩
    have h := hK a m w (Y (.inl a) y)
    rw [hR0, map_zero, zero_apply, zero_apply, zero_add, hw, map_zero, zero_apply, zero_add,
      fderiv_rot_trans k Y y hR0 hbr] at h
    simpa [ha] using h
  · rw [hR0, map_zero]

/-- A field vanishing along a differentiable curve has zero derivative along its velocity. -/
theorem fderiv_apply_eq_zero_of_vanish_on_curve {Z : E → E} {c : ℝ → E} {c' : E} {t : ℝ}
    (hZ : DifferentiableAt ℝ Z (c t)) (hc : HasDerivAt c c' t) (h0 : ∀ s, Z (c s) = 0) :
    fderiv ℝ Z (c t) c' = 0 := by
  have h1 := HasFDerivAt.comp_hasDerivAt (l := Z) (f := c) t hZ.hasFDerivAt hc
  have h2 : HasDerivAt (Z ∘ c) 0 t := by
    have : (Z ∘ c) = fun _ => (0 : E) := funext fun s => h0 s
    rw [this]; exact hasDerivAt_const t 0
  exact h1.unique h2

end Time

section Orbit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ι : Type*} [Fintype ι]
  {Y : ι → E → E} {q₀ : (ι → ℝ) × E} {a r T : ℝ} {K : ℝ≥0} {Ψ : ℝ → (ι → ℝ) × E → (ι → ℝ) × E}

/-- The matrix `M ↦ C M`, `C e f = ∑ₐ ξₐ S a e f`, as a continuous linear map. -/
def adL (S : ι → ι → ι → ℝ) (ξ : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M e => ∑ f, (∑ a, ξ a * S a e f) * M f
      map_add' := fun M M' => by funext e; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c M => by
        funext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun f _ => by ring }

theorem adL_apply (S : ι → ι → ι → ℝ) (ξ M : ι → ℝ) (e : ι) : adL S ξ M e = ∑ f, (∑ a, ξ a * S a e f) * M f := rfl

/-- **Along the orbits, a vector orthogonal to the fields stays orthogonal, and keeps its length and its pairing with the
orbit directions.** For `v = (0, w)` with `G(y)(w, Yₑ y) = 0` for all `e`: `G(J_v, Yₑ) = 0`, `G(J_v, J_{(ζ, 0)}) = 0` and
`G(J_v, J_v) = G(y)(w, w)` along the suspension flow from `(ξ, y)`. -/
theorem orbit_time_data (h : ODE.IsFlowBox (suspField Y) q₀ a r T K Ψ)
    (hX : ∀ c, ∀ q ∈ ball q₀ a, DifferentiableAt ℝ (Y c) q.2) (S : ι → ι → ι → ℝ)
    (hS : ∀ a' c, ∀ q ∈ ball q₀ a, VectorField.lieBracket ℝ (Y a') (Y c) q.2 = ∑ e, S a' c e • Y e q.2)
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (hG : ∀ q ∈ ball q₀ a, DifferentiableAt ℝ G q.2)
    (hK : ∀ c, ∀ q ∈ ball q₀ a, ∀ u w : E, fderiv ℝ G q.2 (Y c q.2) u w + G q.2 (fderiv ℝ (Y c) q.2 u) w +
      G q.2 u (fderiv ℝ (Y c) q.2 w) = 0)
    (hsym : ∀ q ∈ ball q₀ a, ∀ u w : E, G q.2 u w = G q.2 w u)
    {q : (ι → ℝ) × E} (hq : q ∈ ball q₀ r) (w : E) (hw : ∀ e, G q.2 w (Y e q.2) = 0) (ζ : ι → ℝ)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    G (Ψ t q).2 (fderiv ℝ (Ψ t) q (0, w)).2 (fderiv ℝ (Ψ t) q (ζ, 0)).2 = 0 ∧
      G (Ψ t q).2 (fderiv ℝ (Ψ t) q (0, w)).2 (fderiv ℝ (Ψ t) q (0, w)).2 = G q.2 w w := by
  have hd := fun (v' : (ι → ℝ) × E) s (hs : s ∈ Icc (-T) T) =>
    hasDerivWithinAt_orbitData h hX S hS G hG hK hsym hq (0, w) v' hs
  -- the pairings `M = G(J_v, Y)` vanish
  have hM : ∀ v' : (ι → ℝ) × E, ∀ s ∈ Icc (-T) T, (orbitData G Y Ψ q (0, w) v' s).2.1 = 0 := by
    intro v' s hs
    have hu : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun s => (orbitData G Y Ψ q (0, w) v' s).2.1)
        (adL S q.1 (orbitData G Y Ψ q (0, w) v' s).2.1) (Icc (-T) T) s := fun s hs => by
      have hL := (((ContinuousLinearMap.fst ℝ (ι → ℝ) ((ι → ℝ) × ℝ)).comp
        (ContinuousLinearMap.snd ℝ (ι → ι → ℝ) ((ι → ℝ) × (ι → ℝ) × ℝ))).hasFDerivAt).comp_hasDerivWithinAt s
        (hd v' s hs)
      convert hL using 1
      all_goals first | rfl | (funext e; simp [orbitL_apply, adL_apply])
    have hz : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun _ : ℝ => (0 : ι → ℝ)) (adL S q.1 0) (Icc (-T) T) s :=
      fun s _ => by rw [map_zero]; exact hasDerivWithinAt_const _ _ _
    have h0 : (orbitData G Y Ψ q (0, w) v' 0).2.1 = 0 := by
      rw [orbitData_zero h G hq]; funext e; exact hw e
    exact ODE.eqOn_of_linear (A := fun _ => adL S q.1) (fun _ _ => le_rfl) hu hz h0 hs
  -- the pairings `N` are constant
  have hN : ∀ v' : (ι → ℝ) × E, ∀ s ∈ Icc (-T) T,
      HasDerivWithinAt (fun s => (orbitData G Y Ψ q (0, w) v' s).2.2.2) 0 (Icc (-T) T) s := by
    intro v' s hs
    have hL := (((ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ).comp ((ContinuousLinearMap.snd ℝ (ι → ℝ) ((ι → ℝ) × ℝ)).comp
        (ContinuousLinearMap.snd ℝ (ι → ι → ℝ) ((ι → ℝ) × (ι → ℝ) × ℝ)))).hasFDerivAt).comp_hasDerivWithinAt s
        (hd v' s hs)
    convert hL using 1
    all_goals first | rfl | simp [orbitL_apply, hM v' s hs]
  refine ⟨?_, ?_⟩
  · have := eq_zero_of_hasDerivWithinAt_zero h.T_pos (hN (ζ, 0)) ht
    rw [orbitData_zero h G hq] at this
    simpa [orbitData] using this
  · have := eq_zero_of_hasDerivWithinAt_zero h.T_pos (hN (0, w)) ht
    rw [orbitData_zero h G hq] at this
    simpa [orbitData] using this

end Orbit

/-- **The FLRW form from a Killing algebra isotropic along a worldline.** Let `Y` be a family of fields near `c t₀`,
indexed like the Killing algebra of the space form of curvature `k`, `C¹` at `c t₀`, Killing for a symmetric `G` near
`c t₀`, with the brackets `SpaceForm.S k` there, and with the rotations vanishing along a differentiable curve `c`. Then
for some `T, ε > 0`, in the chart `Φ(t, ξ) = exp(T ∑ ξₑ Yₑ)(c t)`, with `o₂` the orbit chart of the space form:
`G(∂_t, ∂_t) = G(c t)(c' t, c' t)`, `G(∂_t, ∂_ζ) = 0`, and `G(∂_ζ, ∂_ζ') = a(t) δ/(1 + k|x|²/4)²(o₂ ξ)(Do₂ ζ, Do₂ ζ')` with
`a(t) = G(c t)(P₀, P₀)`: in the coordinates `(t, o₂ ξ)` the metric is `b(t) dt² + a(t) δ/(1 + k|x|²/4)²`. At `ξ = 0`,
`∂_t Φ = c' t` and `∂_ζ Φ = T ∑ ζₑ Yₑ(c t)`, `Do₂(0) ζ = T ∑ ζₑ Xₑ(0)` (`T` times the identity on the translation
directions). -/
theorem flrw_of_killing_algebra (k : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Y : Idx → E → E) (c c' : ℝ → E) (t₀ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hYc : ∀ i, ContDiffAt ℝ 1 (Y i) (c t₀))
    (hYd : ∀ i, ∀ y ∈ ball (c t₀) ρ, DifferentiableAt ℝ (Y i) y)
    (hGd : ∀ y ∈ ball (c t₀) ρ, DifferentiableAt ℝ G y)
    (hK : ∀ i, ∀ y ∈ ball (c t₀) ρ, ∀ u w : E,
      fderiv ℝ G y (Y i y) u w + G y (fderiv ℝ (Y i) y u) w + G y u (fderiv ℝ (Y i) y w) = 0)
    (hS : ∀ i j, ∀ y ∈ ball (c t₀) ρ, VectorField.lieBracket ℝ (Y i) (Y j) y = ∑ e, S k i j e • Y e y)
    (hsym : ∀ y ∈ ball (c t₀) ρ, ∀ u w : E, G y u w = G y w u)
    (hc : ∀ t, HasDerivAt c (c' t) t) (hiso : ∀ t, ∀ a b : Fin 3, Y (.inr (a, b)) (c t) = 0) :
    ∃ (T ε : ℝ) (Φ : ℝ × (Idx → ℝ) → E) (o₂ : (Idx → ℝ) → (Fin 3 → ℝ)), 0 < T ∧ 0 < ε ∧ o₂ 0 = 0 ∧
      (∀ ζ, fderiv ℝ o₂ 0 ζ = T • ∑ e, ζ e • SpaceForm.X k e 0) ∧
      ∀ t ∈ ball t₀ ε, Φ (t, 0) = c t ∧ fderiv ℝ Φ (t, 0) (1, 0) = c' t ∧
        (∀ ζ, fderiv ℝ Φ (t, 0) (0, ζ) = T • ∑ e, ζ e • Y e (c t)) ∧
        ∀ ξ ∈ ball (0 : Idx → ℝ) ε, DifferentiableAt ℝ Φ (t, ξ) ∧ DifferentiableAt ℝ o₂ ξ ∧
          G (Φ (t, ξ)) (fderiv ℝ Φ (t, ξ) (1, 0)) (fderiv ℝ Φ (t, ξ) (1, 0)) = G (c t) (c' t) (c' t) ∧
          (∀ ζ, G (Φ (t, ξ)) (fderiv ℝ Φ (t, ξ) (1, 0)) (fderiv ℝ Φ (t, ξ) (0, ζ)) = 0) ∧
          ∀ ζ ζ', G (Φ (t, ξ)) (fderiv ℝ Φ (t, ξ) (0, ζ)) (fderiv ℝ Φ (t, ξ) (0, ζ')) =
            G (c t) (Y (.inl 0) (c t)) (Y (.inl 0) (c t)) * metric k (o₂ ξ) (fderiv ℝ o₂ ξ ζ) (fderiv ℝ o₂ ξ ζ') := by
  -- flow boxes
  obtain ⟨A₁, hA₁, H₁⟩ := ODE.exists_isFlowBox (contDiffAt_suspField (q := ((0 : Idx → ℝ), c t₀)) hYc)
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
  have hb₁ : ∀ q ∈ ball ((0 : Idx → ℝ), c t₀) (min A₁ ρ), q.2 ∈ ball (c t₀) ρ := fun q hq =>
    ball_subset_ball (min_le_right _ _) (mem_ball_snd hq)
  have hb₂ : ∀ q ∈ ball ((0 : Idx → ℝ), (0 : Fin 3 → ℝ)) (min A₂ (1 / (|k| + 1))), ψ k q.2 ≠ 0 := fun q hq =>
    psi_ne_zero_of_mem_ball k (ball_subset_ball (min_le_right _ _) (mem_ball_snd hq))
  -- the curve stays in the flow box for `t` near `t₀`
  obtain ⟨δ, hδ0, hcδ⟩ := Metric.continuousAt_iff.1 (hc t₀).continuousAt r₁ h₁.r_pos
  set ε := min (min r₁ r₂) δ
  have hε : 0 < ε := lt_min (lt_min h₁.r_pos h₂.r_pos) hδ0
  have hq₁ : ∀ t ∈ ball t₀ ε, ∀ ξ ∈ ball (0 : Idx → ℝ) ε,
      ((ξ, c t) : (Idx → ℝ) × E) ∈ ball ((0 : Idx → ℝ), c t₀) r₁ := by
    intro t ht ξ hξ
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨?_, hcδ (lt_of_lt_of_le (mem_ball.1 ht) (min_le_right _ _))⟩
    have := mem_ball.1 hξ
    exact lt_of_lt_of_le this ((min_le_left _ _).trans (min_le_left _ _))
  have hq₂ : ∀ ξ ∈ ball (0 : Idx → ℝ) ε, ((ξ, (0 : Fin 3 → ℝ)) : (Idx → ℝ) × (Fin 3 → ℝ)) ∈
      ball ((0 : Idx → ℝ), (0 : Fin 3 → ℝ)) r₂ := fun ξ hξ =>
    mem_ball_pair h₂.r_pos (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hξ)
  have hct : ∀ t ∈ ball t₀ ε, c t ∈ ball (c t₀) ρ := fun t ht =>
    hb₁ _ (h₁'.initial_mem (hq₁ t ht 0 (mem_ball_self hε)))
  -- the hypotheses on the balls of the flow boxes
  have hX₁ : ∀ c', ∀ q ∈ ball ((0 : Idx → ℝ), c t₀) (min A₁ ρ), DifferentiableAt ℝ (Y c') q.2 := fun c' q hq =>
    hYd c' _ (hb₁ q hq)
  have hS₁ : ∀ a' c', ∀ q ∈ ball ((0 : Idx → ℝ), c t₀) (min A₁ ρ),
      VectorField.lieBracket ℝ (Y a') (Y c') q.2 = ∑ e, S k a' c' e • Y e q.2 := fun a' c' q hq =>
    hS a' c' _ (hb₁ q hq)
  have hG₁ : ∀ q ∈ ball ((0 : Idx → ℝ), c t₀) (min A₁ ρ), DifferentiableAt ℝ G q.2 := fun q hq => hGd _ (hb₁ q hq)
  have hK₁ : ∀ c', ∀ q ∈ ball ((0 : Idx → ℝ), c t₀) (min A₁ ρ), ∀ u w : E, fderiv ℝ G q.2 (Y c' q.2) u w +
      G q.2 (fderiv ℝ (Y c') q.2 u) w + G q.2 u (fderiv ℝ (Y c') q.2 w) = 0 := fun c' q hq u w =>
    hK c' _ (hb₁ q hq) u w
  have hsym₁ : ∀ q ∈ ball ((0 : Idx → ℝ), c t₀) (min A₁ ρ), ∀ u w : E, G q.2 u w = G q.2 w u := fun q hq u w =>
    hsym _ (hb₁ q hq) u w
  have hX₂ : ∀ c', ∀ q ∈ ball ((0 : Idx → ℝ), (0 : Fin 3 → ℝ)) (min A₂ (1 / (|k| + 1))),
      DifferentiableAt ℝ (SpaceForm.X k c') q.2 := fun c' q _ => spaceForm_differentiableAt_X k c' _
  have hS₂ : ∀ a' c', ∀ q ∈ ball ((0 : Idx → ℝ), (0 : Fin 3 → ℝ)) (min A₂ (1 / (|k| + 1))),
      VectorField.lieBracket ℝ (SpaceForm.X k a') (SpaceForm.X k c') q.2 = ∑ e, S k a' c' e • SpaceForm.X k e q.2 :=
    fun a' c' q _ => lieBracket_X k a' c' _
  -- the charts and their derivatives
  set Φ : ℝ × (Idx → ℝ) → E := fun p => (Ψ₁ T (p.2, c p.1)).2
  set o₂ : (Idx → ℝ) → (Fin 3 → ℝ) := fun ξ => (Ψ₂ T (ξ, 0)).2
  have hg : ∀ t ξ, HasFDerivAt (fun p : ℝ × (Idx → ℝ) => (p.2, c p.1))
      ((ContinuousLinearMap.snd ℝ ℝ (Idx → ℝ)).prod
        ((ContinuousLinearMap.toSpanSingleton ℝ (c' t)).comp (ContinuousLinearMap.fst ℝ ℝ (Idx → ℝ)))) (t, ξ) :=
    fun t ξ => hasFDerivAt_snd.prodMk ((hc t).hasFDerivAt.comp (t, ξ) hasFDerivAt_fst)
  have hdΦ : ∀ t ∈ ball t₀ ε, ∀ ξ ∈ ball (0 : Idx → ℝ) ε, HasFDerivAt Φ
      ((ContinuousLinearMap.snd ℝ (Idx → ℝ) E).comp ((fderiv ℝ (Ψ₁ T) (ξ, c t)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (Idx → ℝ)).prod
          ((ContinuousLinearMap.toSpanSingleton ℝ (c' t)).comp (ContinuousLinearMap.fst ℝ ℝ (Idx → ℝ)))))) (t, ξ) :=
    fun t ht ξ hξ => hasFDerivAt_snd.comp (t, ξ)
      ((h₁'.differentiableAt_flow (hq₁ t ht ξ hξ) hTI).hasFDerivAt.comp (t, ξ) (hg t ξ))
  have hΦv : ∀ t ∈ ball t₀ ε, ∀ ξ ∈ ball (0 : Idx → ℝ) ε, ∀ τ ζ,
      fderiv ℝ Φ (t, ξ) (τ, ζ) = (fderiv ℝ (Ψ₁ T) (ξ, c t) (ζ, τ • c' t)).2 := by
    intro t ht ξ hξ τ ζ
    rw [(hdΦ t ht ξ hξ).fderiv]
    simp
  have hdo₂ : ∀ ξ ∈ ball (0 : Idx → ℝ) ε, HasFDerivAt o₂ ((ContinuousLinearMap.snd ℝ (Idx → ℝ) (Fin 3 → ℝ)).comp
      ((fderiv ℝ (Ψ₂ T) (ξ, 0)).comp (ContinuousLinearMap.inl ℝ (Idx → ℝ) (Fin 3 → ℝ)))) ξ := fun ξ hξ =>
    hasFDerivAt_snd.comp ξ ((h₂'.differentiableAt_flow (hq₂ ξ hξ) hTI).hasFDerivAt.comp ξ
      (hasFDerivAt_prodMk_left ξ (0 : Fin 3 → ℝ)))
  have h0 : (0 : Idx → ℝ) ∈ ball (0 : Idx → ℝ) ε := mem_ball_self hε
  have hΦ0 : ∀ t ∈ ball t₀ ε, Φ (t, 0) = c t := fun t ht => by
    show (Ψ₁ T (0, c t)).2 = c t
    rw [susp_flow_zero h₁' (hq₁ t ht 0 h0) hTI]
  refine ⟨T, ε, Φ, o₂, hT, hε, ?_, fun ζ => ?_, fun t ht => ⟨hΦ0 t ht, ?_, fun ζ => ?_, fun ξ hξ => ?_⟩⟩
  · show (Ψ₂ T (0, 0)).2 = 0
    rw [susp_flow_zero h₂' (hq₂ 0 h0) hTI]
  · rw [(hdo₂ 0 h0).fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.coe_snd']
    rw [fderiv_susp_flow_zero h₂' hX₂ (S k) hS₂ (hq₂ 0 h0) ζ hTI]
  · -- `∂_t Φ(t, 0) = c' t`: `Φ(·, 0) = c` near `t`
    have h1 : HasDerivAt (fun s => Φ (s, 0)) (fderiv ℝ Φ (t, 0) (1, 0)) t := by
      have := (hdΦ t ht 0 h0).comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : Idx → ℝ)))
      rw [← (hdΦ t ht 0 h0).fderiv] at this
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun s => Φ (s, 0)) (c' t) t :=
      (hc t).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds ht) fun s hs => hΦ0 s hs)
    exact h1.unique h2
  · rw [hΦv t ht 0 h0, zero_smul, fderiv_susp_flow_zero h₁' hX₁ (S k) hS₁ (hq₁ t ht 0 h0) ζ hTI]
  · -- the time direction is orthogonal to the fields at `c t`
    have hw : ∀ e, G (c t) (c' t) (Y e (c t)) = 0 := by
      refine pairing_zero_of_isotropy k G Y (c t) (c' t) (hiso t) (fun a b u w => hK _ _ (hct t ht) u w)
        (fun a b m => hS _ _ _ (hct t ht)) (fun a b => ?_)
      exact fderiv_apply_eq_zero_of_vanish_on_curve (hYd _ _ (hct t ht)) (hc t) (fun s => hiso s a b)
    have htd := orbit_time_data h₁' hX₁ (S k) hS₁ G hG₁ hK₁ hsym₁ (hq₁ t ht ξ hξ) (c' t) hw
    have hΓ : gramAt G Y (c t) = G (c t) (Y (.inl 0) (c t)) (Y (.inl 0) (c t)) •
        gramAt (metric k) (SpaceForm.X k) 0 := by
      rw [spaceForm_gram_zero]
      exact gram_of_isotropy k G Y (c t) (hiso t) (fun a b u w => hK _ _ (hct t ht) u w)
        (fun a b m => hS _ _ _ (hct t ht)) (hsym _ (hct t ht))
    refine ⟨(hdΦ t ht ξ hξ).differentiableAt, (hdo₂ ξ hξ).differentiableAt, ?_, fun ζ => ?_, fun ζ ζ' => ?_⟩
    · rw [hΦv t ht ξ hξ, one_smul]
      exact (htd 0 hTI).2
    · rw [hΦv t ht ξ hξ, hΦv t ht ξ hξ, one_smul, zero_smul]
      exact (htd ζ hTI).1
    · rw [hΦv t ht ξ hξ, hΦv t ht ξ hξ, zero_smul, (hdo₂ ξ hξ).fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.coe_snd']
      exact orbit_comparison h₁' h₂' (S k) hX₁ hS₁ G hG₁ hK₁ hsym₁
        hX₂ hS₂ (metric k) (fun q hq => (hasFDerivAt_metric k (hb₂ q hq)).differentiableAt)
        (fun c' q hq u w => spaceForm_killing k c' (hb₂ q hq) u w) (fun q _ u w => spaceForm_metric_symm k _ u w)
        (hq₁ t ht ξ hξ) (hq₂ ξ hξ) _ hΓ ζ ζ' hTI

end Lightlike
