import Lightlike.ODE.CommutingFlows

/-!
# The flow chart of a commuting family of vector fields

For finitely many `C¹` vector fields `Y i` on a real Banach space with `[Y i, Y j] = 0` near `x₀`,
the composition of their local flows

`f (t, x) = Φ i₁ (t i₁) (Φ i₂ (t i₂) (… x))`

is differentiable in `(t, x)` near `(0, x₀)`, with `∂f/∂t i = Y i ∘ f` and `∂f/∂x = id` at `t = 0`
(`Lightlike.ODE.exists_flowComp_of_commuting`). So `t ↦ f (t, x)` parametrises an integral
manifold of the span of the `Y i` through `x`: this is the map `f` in the proofs of Michor's
Theorem 3.17 and of the local Frobenius theorem 3.18.

The derivative in `t` is computed without commuting the flows: the chain rule gives
`D_x Φ_i (Y j)`, and `D_x Φ_i (Y j) = Y j ∘ Φ_i` because `[Y i, Y j] = 0`
(`IsFlowBox.fderiv_flow_apply_eq_of_lieBracket_eq_zero`).

## References

* `michor-2008`: P. W. Michor, *Topics in Differential Geometry*, Theorems 3.17 and 3.18,
  pages 31–33 of the author's version.
-/

open Set Metric Filter Topology
open scoped NNReal

noncomputable section

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- A finite family of positive numbers has a positive lower bound. -/
lemma exists_pos_forall_le [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ε > 0, ∀ i, ε ≤ f i := by
  cases nonempty_fintype ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · exact ⟨Finset.univ.inf' Finset.univ_nonempty f, (Finset.lt_inf'_iff _).2 fun i _ => hf i,
      fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩

/-- The composition of the maps `Φ i (t i)` along a list of indices, the head outermost. -/
def flowComp (Φ : ι → ℝ → E → E) : List ι → (ι → ℝ) → E → E
  | [], _, x => x
  | i :: l, t, x => Φ i (t i) (flowComp Φ l t x)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] lemma flowComp_nil (Φ : ι → ℝ → E → E) (t : ι → ℝ) (x : E) : flowComp Φ [] t x = x := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] lemma flowComp_cons (Φ : ι → ℝ → E → E) (i : ι) (l : List ι) (t : ι → ℝ) (x : E) :
    flowComp Φ (i :: l) t x = Φ i (t i) (flowComp Φ l t x) := rfl

variable [Fintype ι]

/-- The derivative of `(t, x) ↦ flowComp Φ l t x`, by the chain rule: for the list `i :: l` it is
`(τ, ξ) ↦ τ i • Y i (flowComp Φ (i :: l) t x) + D_x Φ_i (derivative for l)`. -/
def flowCompFDeriv (Y : ι → E → E) (Φ : ι → ℝ → E → E) :
    List ι → (ι → ℝ) → E → ((ι → ℝ) × E →L[ℝ] E)
  | [], _, _ => ContinuousLinearMap.snd ℝ (ι → ℝ) E
  | i :: l, t, x =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp
          (ContinuousLinearMap.fst ℝ (ι → ℝ) E)).smulRight (Y i (flowComp Φ (i :: l) t x)) +
        (fderiv ℝ (Φ i (t i)) (flowComp Φ l t x)).comp (flowCompFDeriv Y Φ l t x)

section Boxes

variable {Y : ι → E → E} {Φ : ι → ℝ → E → E} {x₀ : E} {a r T M : ℝ} {K : ι → ℝ≥0}

omit [Fintype ι] in
/-- The radius condition for a list passes to its tail. -/
lemma radius_tail_le (h : ∀ i, IsFlowBox (Y i) x₀ a r T (K i) (Φ i))
    (hM : ∀ i, ‖Y i x₀‖ + K i * a ≤ M) (i : ι) (l : List ι) {ρ : ℝ}
    (hρ : ρ + ((i :: l).length : ℝ) * (M * T) ≤ r) : ρ + (l.length : ℝ) * (M * T) ≤ r := by
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hρ
  have hT : 0 < T := (h i).T_pos
  have hMi : 0 ≤ ‖Y i x₀‖ + K i * a :=
    (norm_nonneg _).trans ((h i).norm_field_le ((h i).initial_mem (mem_ball_self (h i).r_pos)))
  have hMT : 0 ≤ M * T := mul_nonneg (hMi.trans (hM i)) hT.le
  nlinarith

omit [Fintype ι] in
/-- A composition of `n` flows, each for a time in `[-T, T]`, moves a point of the ball of radius
`ρ` about `x₀` into the ball of radius `ρ + n M T`, where `M` bounds the speeds. -/
theorem flowComp_mem (h : ∀ i, IsFlowBox (Y i) x₀ a r T (K i) (Φ i))
    (hM : ∀ i, ‖Y i x₀‖ + K i * a ≤ M) (l : List ι) {ρ : ℝ} {x : E} (hx : x ∈ ball x₀ ρ)
    {t : ι → ℝ} (ht : ∀ i, t i ∈ Icc (-T) T) (hρ : ρ + (l.length : ℝ) * (M * T) ≤ r) :
    flowComp Φ l t x ∈ ball x₀ (ρ + (l.length : ℝ) * (M * T)) := by
  induction l with
  | nil => simpa using hx
  | cons i l ih =>
    have hρ' := radius_tail_le h hM i l hρ
    have hT : 0 < T := (h i).T_pos
    have h1 := (h i).flow_mem_ball_add hρ' (ih hρ') (ht i)
    refine ball_subset_ball ?_ h1
    have : (‖Y i x₀‖ + K i * a) * T ≤ M * T := mul_le_mul_of_nonneg_right (hM i) hT.le
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

omit [Fintype ι] in
/-- A composition of flows stays in the ball of initial points, under the radius condition. -/
theorem flowComp_mem_ball (h : ∀ i, IsFlowBox (Y i) x₀ a r T (K i) (Φ i))
    (hM : ∀ i, ‖Y i x₀‖ + K i * a ≤ M) (l : List ι) {ρ : ℝ} {x : E} (hx : x ∈ ball x₀ ρ)
    {t : ι → ℝ} (ht : ∀ i, t i ∈ Icc (-T) T) (hρ : ρ + (l.length : ℝ) * (M * T) ≤ r) :
    flowComp Φ l t x ∈ ball x₀ r :=
  ball_subset_ball hρ (flowComp_mem h hM l hx ht hρ)

omit [Fintype ι] in
/-- A composition of flows that each preserve a set `Γ` preserves `Γ`. -/
theorem flowComp_mem_of_invariant (h : ∀ i, IsFlowBox (Y i) x₀ a r T (K i) (Φ i))
    (hM : ∀ i, ‖Y i x₀‖ + K i * a ≤ M) {Γ : Set E}
    (hΓ : ∀ i, ∀ x ∈ ball x₀ r, x ∈ Γ → ∀ t ∈ Icc (-T) T, Φ i t x ∈ Γ)
    (l : List ι) {ρ : ℝ} {x : E} (hx : x ∈ ball x₀ ρ) (hxΓ : x ∈ Γ)
    {t : ι → ℝ} (ht : ∀ i, t i ∈ Icc (-T) T) (hρ : ρ + (l.length : ℝ) * (M * T) ≤ r) :
    flowComp Φ l t x ∈ Γ := by
  induction l with
  | nil => exact hxΓ
  | cons i l ih =>
    have hρ' := radius_tail_le h hM i l hρ
    exact hΓ i _ (flowComp_mem_ball h hM l hx ht hρ') (ih hρ') (t i) (ht i)

omit [Fintype ι] in
/-- At `t = 0` the composition of flows is the identity on the ball of initial points. -/
theorem flowComp_zero (h : ∀ i, IsFlowBox (Y i) x₀ a r T (K i) (Φ i)) (l : List ι) {x : E}
    (hx : x ∈ ball x₀ r) : flowComp Φ l 0 x = x := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ih, (h i).flow_zero x hx]

variable [CompleteSpace E]

omit [Fintype ι] in
/-- At `t = 0` the derivative of the composition of flows in the initial point is the identity. -/
theorem flowCompFDeriv_zero_apply (h : ∀ i, IsFlowBox (Y i) x₀ a r T (K i) (Φ i)) (l : List ι)
    {x : E} (hx : x ∈ ball x₀ r) (ξ : E) : flowCompFDeriv Y Φ l 0 x (0, ξ) = ξ := by
  induction l with
  | nil => simp [flowCompFDeriv]
  | cons i l ih => simp [flowCompFDeriv, ih, flowComp_zero h l hx, (h i).fderiv_flow_zero hx]

/-- **The composition of flows is differentiable in `(t, x)`.** -/
theorem hasFDerivAt_flowComp (h : ∀ i, IsFlowBox (Y i) x₀ a r T (K i) (Φ i))
    (hM : ∀ i, ‖Y i x₀‖ + K i * a ≤ M) (l : List ι) {ρ : ℝ} {x : E} (hx : x ∈ ball x₀ ρ)
    {t : ι → ℝ} (ht : ∀ i, t i ∈ Ioo (-T) T) (hρ : ρ + (l.length : ℝ) * (M * T) ≤ r) :
    HasFDerivAt (fun p : (ι → ℝ) × E => flowComp Φ l p.1 p.2) (flowCompFDeriv Y Φ l t x)
      (t, x) := by
  induction l with
  | nil => exact hasFDerivAt_snd
  | cons i l ih =>
    have hρ' := radius_tail_le h hM i l hρ
    have hz : flowComp Φ l t x ∈ ball x₀ r :=
      flowComp_mem_ball h hM l hx (fun i => Ioo_subset_Icc_self (ht i)) hρ'
    have houter := (h i).hasFDerivAt_uncurry hz (ht i)
    have hinner : HasFDerivAt (fun p : (ι → ℝ) × E => (p.1 i, flowComp Φ l p.1 p.2))
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp
          (ContinuousLinearMap.fst ℝ (ι → ℝ) E)).prod (flowCompFDeriv Y Φ l t x)) (t, x) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).hasFDerivAt.comp (t, x)
        hasFDerivAt_fst).prodMk (ih hρ')
    have hcomp : HasFDerivAt ((fun q : ℝ × E => Φ i q.1 q.2) ∘
        fun p : (ι → ℝ) × E => (p.1 i, flowComp Φ l p.1 p.2)) _ (t, x) :=
      HasFDerivAt.comp (t, x) houter hinner
    refine hcomp.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
    simp [flowCompFDeriv]

/-- The derivative of the composition of flows is continuous in `(t, x)`. -/
theorem continuousAt_flowCompFDeriv (h : ∀ i, IsFlowBox (Y i) x₀ a r T (K i) (Φ i))
    (hM : ∀ i, ‖Y i x₀‖ + K i * a ≤ M) (l : List ι) {ρ : ℝ} {x : E} (hx : x ∈ ball x₀ ρ)
    {t : ι → ℝ} (ht : ∀ i, t i ∈ Ioo (-T) T) (hρ : ρ + (l.length : ℝ) * (M * T) ≤ r) :
    ContinuousAt (fun p : (ι → ℝ) × E => flowCompFDeriv Y Φ l p.1 p.2) (t, x) := by
  induction l with
  | nil => exact continuousAt_const
  | cons i l ih =>
    have hρ' := radius_tail_le h hM i l hρ
    have hz : flowComp Φ l t x ∈ ball x₀ r :=
      flowComp_mem_ball h hM l hx (fun i => Ioo_subset_Icc_self (ht i)) hρ'
    have hfc : ContinuousAt (fun p : (ι → ℝ) × E => flowComp Φ l p.1 p.2) (t, x) :=
      (hasFDerivAt_flowComp h hM l hx ht hρ').continuousAt
    have hfc' : ContinuousAt (fun p : (ι → ℝ) × E => flowComp Φ (i :: l) p.1 p.2) (t, x) :=
      (hasFDerivAt_flowComp h hM (i :: l) hx ht hρ).continuousAt
    have hYc : ContinuousAt (Y i) (flowComp Φ (i :: l) t x) :=
      ((h i).differentiableAt _
        ((h i).flow_mem _ hz (t i) (Ioo_subset_Icc_self (ht i)))).continuousAt
    have h1 : ContinuousAt (fun p : (ι → ℝ) × E =>
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp
          (ContinuousLinearMap.fst ℝ (ι → ℝ) E)).smulRight
            (Y i (flowComp Φ (i :: l) p.1 p.2))) (t, x) :=
      (ContinuousLinearMap.smulRightL ℝ ((ι → ℝ) × E) E
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp
          (ContinuousLinearMap.fst ℝ (ι → ℝ) E))).continuous.continuousAt.comp
        (ContinuousAt.comp (f := fun p : (ι → ℝ) × E => flowComp Φ (i :: l) p.1 p.2) hYc hfc')
    have hinner : ContinuousAt (fun p : (ι → ℝ) × E => (p.1 i, flowComp Φ l p.1 p.2)) (t, x) :=
      ((continuous_apply i).comp continuous_fst).continuousAt.prodMk hfc
    have hout : ContinuousAt (fun q : ℝ × E => fderiv ℝ (Φ i q.1) q.2)
        (t i, flowComp Φ l t x) :=
      (h i).continuousOn_fderiv_flow.continuousAt
        (prod_mem_nhds (Icc_mem_nhds (ht i).1 (ht i).2) (isOpen_ball.mem_nhds hz))
    have h2 : ContinuousAt ((fun q : ℝ × E => fderiv ℝ (Φ i q.1) q.2) ∘
        fun p : (ι → ℝ) × E => (p.1 i, flowComp Φ l p.1 p.2)) (t, x) :=
      ContinuousAt.comp (g := fun q : ℝ × E => fderiv ℝ (Φ i q.1) q.2) hout hinner
    exact h1.add (h2.clm_comp (ih hρ'))

omit [Fintype ι] in
/-- **The derivative of the composition of flows in the times.** Let `Γ` be a set preserved by
the flows on which the fields commute (`Γ = univ` if they commute everywhere). For `x ∈ Γ` the
derivative of `t ↦ flowComp Φ l t x` in the direction `τ` is
`∑ j in l, τ j • Y j (flowComp Φ l t x)`: each partial derivative of the composition is the
corresponding field at the image point. -/
theorem flowCompFDeriv_apply_fst (h : ∀ i, IsFlowBox (Y i) x₀ a r T (K i) (Φ i))
    (hM : ∀ i, ‖Y i x₀‖ + K i * a ≤ M) {Γ : Set E}
    (hΓ : ∀ i, ∀ x ∈ ball x₀ r, x ∈ Γ → ∀ t ∈ Icc (-T) T, Φ i t x ∈ Γ)
    (hYY : ∀ i j, ∀ y ∈ ball x₀ a, y ∈ Γ → VectorField.lieBracket ℝ (Y i) (Y j) y = 0)
    (l : List ι) {ρ : ℝ} {x : E} (hx : x ∈ ball x₀ ρ) (hxΓ : x ∈ Γ)
    {t : ι → ℝ} (ht : ∀ i, t i ∈ Icc (-T) T) (hρ : ρ + (l.length : ℝ) * (M * T) ≤ r)
    (τ : ι → ℝ) :
    flowCompFDeriv Y Φ l t x (τ, 0) = (l.map fun j => τ j • Y j (flowComp Φ l t x)).sum := by
  induction l with
  | nil => simp [flowCompFDeriv]
  | cons i l ih =>
    have hρ' := radius_tail_le h hM i l hρ
    have hz : flowComp Φ l t x ∈ ball x₀ r := flowComp_mem_ball h hM l hx ht hρ'
    have hzΓ : flowComp Φ l t x ∈ Γ := flowComp_mem_of_invariant h hM hΓ l hx hxΓ ht hρ'
    have hinv : ∀ j, fderiv ℝ (Φ i (t i)) (flowComp Φ l t x) (Y j (flowComp Φ l t x)) =
        Y j (Φ i (t i) (flowComp Φ l t x)) := fun j =>
      (h i).fderiv_flow_apply_eq_of_lieBracket_eq_zero (fun y hy => (h j).differentiableAt y hy)
        hz (fun u hu => hYY i j _ ((h i).flow_mem _ hz u hu) (hΓ i _ hz hzΓ u hu)) (ht i)
    have hsum : fderiv ℝ (Φ i (t i)) (flowComp Φ l t x)
        ((l.map fun j => τ j • Y j (flowComp Φ l t x)).sum) =
        (l.map fun j => τ j • Y j (Φ i (t i) (flowComp Φ l t x))).sum := by
      rw [map_list_sum, List.map_map]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      simp [hinv j]
    simp only [flowCompFDeriv, add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply,
      List.map_cons, List.sum_cons, flowComp_cons]
    rw [ih hρ', hsum]

end Boxes

/-- **The flow chart of a commuting family** (the map `f` of Michor's Theorems 3.17 and 3.18).

Let `Y i`, for `i` in a finite type, be vector fields that are `C¹` at `x₀`, and let `Γ` be a set
such that near `x₀` the fields commute on `Γ` and their integral curves starting in `Γ` stay in
`Γ` (for fields that commute near `x₀`, take `Γ = univ`). Then there are `ε > 0` and a map `f` of
`(t, x)` such that for `‖t‖ < ε` and `‖x - x₀‖ < ε`: `f` is differentiable at `(t, x)` with a derivative continuous there;
`f (0, x) = x`; at `t = 0` its derivative in the direction `(0, ξ)` is `ξ`; and if `x ∈ Γ` then
`f (t, x) ∈ Γ` and the derivative in the direction `(τ, 0)` is `∑ i, τ i • Y i (f (t, x))`, that
is `∂f/∂t i = Y i ∘ f`. For fixed `x ∈ Γ` the map `t ↦ f (t, x)` therefore parametrises an
integral manifold through `x` of the span of the `Y i`. -/
theorem exists_flowComp_of_commuting_on [CompleteSpace E] {Y : ι → E → E} {x₀ : E} {Γ : Set E}
    (hY : ∀ i, ContDiffAt ℝ 1 (Y i) x₀)
    (hYY : ∀ i j, ∀ᶠ y in 𝓝 x₀, y ∈ Γ → VectorField.lieBracket ℝ (Y i) (Y j) y = 0)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hΓ : ∀ i, ∀ (γ : ℝ → E) (T : ℝ), (∀ t ∈ Icc (-T) T,
      HasDerivAt γ (Y i (γ t)) t ∧ γ t ∈ ball x₀ a₀) → γ 0 ∈ Γ → ∀ t ∈ Icc (-T) T, γ t ∈ Γ) :
    ∃ (ε : ℝ) (f : (ι → ℝ) × E → E) (f' : (ι → ℝ) × E → ((ι → ℝ) × E →L[ℝ] E)), 0 < ε ∧
      (∀ x ∈ ball x₀ ε, f (0, x) = x ∧ ∀ ξ : E, f' (0, x) (0, ξ) = ξ) ∧
      ∀ t ∈ ball (0 : ι → ℝ) ε, ∀ x ∈ ball x₀ ε,
        (HasFDerivAt f (f' (t, x)) (t, x) ∧ ContinuousAt f' (t, x)) ∧
        (x ∈ Γ → f (t, x) ∈ Γ ∧ ∀ τ : ι → ℝ, f' (t, x) (τ, 0) = ∑ i, τ i • Y i (f (t, x))) := by
  have hYY' : ∀ᶠ y in 𝓝 x₀, ∀ i j, y ∈ Γ → VectorField.lieBracket ℝ (Y i) (Y j) y = 0 :=
    eventually_all.2 fun i => eventually_all.2 fun j => hYY i j
  obtain ⟨A₀, hA₀, H₀⟩ := Metric.eventually_nhds_iff_ball.1 hYY'
  choose A hA HA using fun i => exists_isFlowBox (hY i)
  obtain ⟨A', hA', hAle⟩ := exists_pos_forall_le A hA
  set a : ℝ := min A' (min A₀ a₀) with ha
  have ha0 : 0 < a := lt_min hA' (lt_min hA₀ ha₀)
  choose r T K Φ h using fun i => HA i a ha0 ((min_le_left _ _).trans (hAle i))
  obtain ⟨r₀, hr₀, hrle⟩ := exists_pos_forall_le r fun i => (h i).r_pos
  obtain ⟨T₀, hT₀, hTle⟩ := exists_pos_forall_le T fun i => (h i).T_pos
  set M : ℝ := ∑ i, (‖Y i x₀‖ + K i * a) with hMdef
  have hterm : ∀ i, 0 ≤ ‖Y i x₀‖ + K i * a := fun i =>
    (norm_nonneg _).trans ((h i).norm_field_le (mem_ball_self ha0))
  have hM : ∀ i, ‖Y i x₀‖ + K i * a ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => ‖Y i x₀‖ + K i * a) (fun i _ => hterm i)
      (Finset.mem_univ i)
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => hterm i
  set l : List ι := Finset.univ.toList with hl
  set n : ℝ := (l.length : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hnM : 0 ≤ n * M := mul_nonneg hn0 hM0
  have hnM1 : 0 < 2 * (n * M + 1) := by linarith
  set T' : ℝ := min T₀ (r₀ / (2 * (n * M + 1))) with hT'
  have hT'0 : 0 < T' := lt_min hT₀ (div_pos hr₀ hnM1)
  have hnMT : n * (M * T') ≤ r₀ / 2 := by
    have h1 : n * M * T' ≤ n * M * (r₀ / (2 * (n * M + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hnM
    have h2 : n * M * (r₀ / (2 * (n * M + 1))) ≤ r₀ / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hnM1]
      nlinarith
    calc n * (M * T') = n * M * T' := by ring
      _ ≤ r₀ / 2 := h1.trans h2
  have h' : ∀ i, IsFlowBox (Y i) x₀ a r₀ T' (K i) (Φ i) := fun i =>
    (h i).mono hr₀ (hrle i) hT'0 ((min_le_left _ _).trans (hTle i))
  have hbr : ∀ i j, ∀ y ∈ ball x₀ a, y ∈ Γ → VectorField.lieBracket ℝ (Y i) (Y j) y = 0 :=
    fun i j y hy hyΓ => H₀ y (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hy)
      i j hyΓ
  have hΓ' : ∀ i, ∀ x ∈ ball x₀ r₀, x ∈ Γ → ∀ t ∈ Icc (-T') T', Φ i t x ∈ Γ := by
    intro i x hx hxΓ t ht
    refine hΓ i (fun t => Φ i t x) T' (fun u hu => ⟨(h' i).hasDerivAt x hx u hu, ?_⟩) ?_ t ht
    · exact ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
        ((h' i).flow_mem x hx u hu)
    · simpa [(h' i).flow_zero x hx] using hxΓ
  set ε : ℝ := min (r₀ / 2) T' with hε
  have hε0 : 0 < ε := lt_min (half_pos hr₀) hT'0
  have hρ : r₀ / 2 + (l.length : ℝ) * (M * T') ≤ r₀ := by
    have : (l.length : ℝ) * (M * T') ≤ r₀ / 2 := hnMT
    linarith
  refine ⟨ε, fun p => flowComp Φ l p.1 p.2, fun p => flowCompFDeriv Y Φ l p.1 p.2, hε0,
    fun x hx => ?_, fun t ht x hx => ?_⟩
  · have hx' : x ∈ ball x₀ r₀ :=
      ball_subset_ball ((min_le_left _ _).trans (by linarith)) hx
    exact ⟨flowComp_zero h' l hx', fun ξ => flowCompFDeriv_zero_apply h' l hx' ξ⟩
  · have hx' : x ∈ ball x₀ (r₀ / 2) := ball_subset_ball (min_le_left _ _) hx
    have hti : ∀ i, t i ∈ Ioo (-T') T' := by
      intro i
      have h1 : |t i| < T' := by
        have h2 : ‖t i‖ ≤ ‖t‖ := norm_le_pi_norm t i
        have h3 : ‖t‖ < ε := mem_ball_zero_iff.1 ht
        rw [Real.norm_eq_abs] at h2
        exact lt_of_le_of_lt h2 (lt_of_lt_of_le h3 (min_le_right _ _))
      exact abs_lt.1 h1
    have hti' : ∀ i, t i ∈ Icc (-T') T' := fun i => Ioo_subset_Icc_self (hti i)
    refine ⟨⟨hasFDerivAt_flowComp h' hM l hx' hti hρ,
      continuousAt_flowCompFDeriv h' hM l hx' hti hρ⟩, fun hxΓ => ⟨?_, fun τ => ?_⟩⟩
    · exact flowComp_mem_of_invariant h' hM hΓ' l hx' hxΓ hti' hρ
    · have := flowCompFDeriv_apply_fst h' hM hΓ' hbr l hx' hxΓ hti' hρ τ
      rw [this]
      exact Finset.sum_map_toList _ _

/-- **The flow chart of a commuting family**: `exists_flowComp_of_commuting_on` for fields that
commute near `x₀`. There are `ε > 0` and a map `f` of `(t, x)` such that for `‖t‖ < ε` and
`‖x - x₀‖ < ε`: `f` is differentiable at `(t, x)`, its derivative in the direction `(τ, 0)` is
`∑ i, τ i • Y i (f (t, x))`, `f (0, x) = x`, and at `t = 0` its derivative in the direction
`(0, ξ)` is `ξ`. -/
theorem exists_flowComp_of_commuting [CompleteSpace E] {Y : ι → E → E} {x₀ : E}
    (hY : ∀ i, ContDiffAt ℝ 1 (Y i) x₀)
    (hYY : ∀ i j, ∀ᶠ y in 𝓝 x₀, VectorField.lieBracket ℝ (Y i) (Y j) y = 0) :
    ∃ (ε : ℝ) (f : (ι → ℝ) × E → E) (f' : (ι → ℝ) × E → ((ι → ℝ) × E →L[ℝ] E)), 0 < ε ∧
      (∀ x ∈ ball x₀ ε, f (0, x) = x ∧ ∀ ξ : E, f' (0, x) (0, ξ) = ξ) ∧
      ∀ t ∈ ball (0 : ι → ℝ) ε, ∀ x ∈ ball x₀ ε,
        (HasFDerivAt f (f' (t, x)) (t, x) ∧ ContinuousAt f' (t, x)) ∧
        ∀ τ : ι → ℝ, f' (t, x) (τ, 0) = ∑ i, τ i • Y i (f (t, x)) := by
  obtain ⟨ε, f, f', hε, h0, hd⟩ := exists_flowComp_of_commuting_on (Γ := univ) hY
    (fun i j => (hYY i j).mono fun y hy _ => hy) one_pos (fun _ _ _ _ _ _ _ => mem_univ _)
  exact ⟨ε, f, f', hε, h0, fun t ht x hx =>
    ⟨(hd t ht x hx).1, ((hd t ht x hx).2 (mem_univ x)).2⟩⟩

end Lightlike.ODE
