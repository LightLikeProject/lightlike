import Lightlike.Regge.ReggeEquations

/-!
# The gradient of the Regge action

`hasDerivAt_reggeAction` (`Lightlike/Regge/ReggeEquations.lean`) differentiates the Regge action
along every line `ℓ + τ v` in the space of edge lengths. This file proves the stronger statement
that, for a finite vertex set, the Regge action is (Fréchet) differentiable on the
finite-dimensional space `Finset V → ℝ` of length assignments, with derivative the linear functional
`v ↦ Σ_{interior} v_e δ_e + Σ_{boundary} v_e ψ_e`.

## Main results

* `differentiableAt_dihedral`: the dihedral angle is a differentiable function of the six edge
  lengths at a non-degenerate tetrahedron.
* `differentiableAt_reggeAction`: the Regge action is differentiable at non-degenerate lengths.
* `hasFDerivAt_reggeAction` (**Regge's equations, gradient form**): its derivative is
  `reggeGradient K ℓ`, i.e. `∂S/∂ℓ_e = δ_e` at interior and `ψ_e` at boundary edges.
-/

open Real Finset

namespace Lightlike.Regge

open Lightlike.PR (Complex3 dihedral vol2)

section Smooth

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The dihedral angle is differentiable in the lengths.** If six real functions `g₁, …, g₆`
(the lengths `pq, pr, qr, ps, qs, rs`) are differentiable at `y` and describe a non-degenerate
tetrahedron there, the dihedral angle at `pq` is differentiable at `y`. -/
theorem differentiableAt_dihedral {g₁ g₂ g₃ g₄ g₅ g₆ : F → ℝ} {y : F}
    (h₁ : DifferentiableAt ℝ g₁ y) (h₂ : DifferentiableAt ℝ g₂ y) (h₃ : DifferentiableAt ℝ g₃ y)
    (h₄ : DifferentiableAt ℝ g₄ y) (h₅ : DifferentiableAt ℝ g₅ y) (h₆ : DifferentiableAt ℝ g₆ y)
    (hpq : 0 < g₁ y) (hH₁ : 0 < heron (g₁ y) (g₂ y) (g₃ y)) (hH₂ : 0 < heron (g₁ y) (g₄ y) (g₅ y))
    (hV : 0 < vol2 (g₁ y) (g₃ y) (g₂ y) (g₆ y) (g₄ y) (g₅ y)) :
    DifferentiableAt ℝ (fun z => dihedral (g₁ z) (g₂ z) (g₃ z) (g₄ z) (g₅ z) (g₆ z)) y := by
  have hN : DifferentiableAt ℝ (fun z => numN (g₁ z) (g₂ z) (g₃ z) (g₄ z) (g₅ z) (g₆ z)) y := by
    unfold numN
    fun_prop
  have hH : DifferentiableAt ℝ
      (fun z => heron (g₁ z) (g₂ z) (g₃ z) * heron (g₁ z) (g₄ z) (g₅ z)) y := by
    unfold heron
    fun_prop
  have hP0 : 0 < heron (g₁ y) (g₂ y) (g₃ y) * heron (g₁ y) (g₄ y) (g₅ y) := mul_pos hH₁ hH₂
  have hS := hH.sqrt hP0.ne'
  have hsP : √(heron (g₁ y) (g₂ y) (g₃ y) * heron (g₁ y) (g₄ y) (g₅ y)) ≠ 0 :=
    (Real.sqrt_pos.mpr hP0).ne'
  have hC : DifferentiableAt ℝ (fun z => numN (g₁ z) (g₂ z) (g₃ z) (g₄ z) (g₅ z) (g₆ z) /
      √(heron (g₁ z) (g₂ z) (g₃ z) * heron (g₁ z) (g₄ z) (g₅ z))) y := by
    fun_prop (disch := assumption)
  have hid := heron_mul_sub_numN_sq (g₁ y) (g₂ y) (g₃ y) (g₄ y) (g₅ y) (g₆ y)
  have hgap : 0 < 576 * g₁ y ^ 2 * vol2 (g₁ y) (g₃ y) (g₂ y) (g₆ y) (g₄ y) (g₅ y) := by positivity
  have hsq : (numN (g₁ y) (g₂ y) (g₃ y) (g₄ y) (g₅ y) (g₆ y) /
      √(heron (g₁ y) (g₂ y) (g₃ y) * heron (g₁ y) (g₄ y) (g₅ y))) ^ 2 < 1 := by
    rw [div_pow, Real.sq_sqrt hP0.le, div_lt_one hP0]
    linarith
  have hbd := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hsq)
  have hA := (Real.differentiableAt_arccos.mpr ⟨hbd.1.ne', hbd.2.ne⟩).comp y hC
  refine hA.congr_of_eventuallyEq ?_
  have e1 : ∀ᶠ z in nhds y, 0 < g₁ z := h₁.continuousAt.eventually (lt_mem_nhds hpq)
  have e2 : ∀ᶠ z in nhds y, 0 < heron (g₁ z) (g₂ z) (g₃ z) * heron (g₁ z) (g₄ z) (g₅ z) :=
    hH.continuousAt.eventually (lt_mem_nhds hP0)
  filter_upwards [e1, e2] with z hz1 hz2
  simp only [Function.comp, dihedral]
  rw [cosDihedral_eq_numN hz1.ne' _ _ _ _ _ hz2.le]

end Smooth

/-- The exterior angles of a non-degenerate tetrahedron are differentiable functions of the six
edge lengths. -/
theorem differentiableAt_extAngles' {l : Fin 6 → ℝ} (h : TetNondeg l) (e : Fin 6) :
    DifferentiableAt ℝ (fun m : Fin 6 → ℝ => Lightlike.PR.extAngles m e) l := by
  obtain ⟨hl, hABC, hABD, hACD, hBCD, hV⟩ := h
  have pos : ∀ {x y : ℝ}, x = y → 0 < y → 0 < x := fun h hy => h ▸ hy
  have d : ∀ k : Fin 6, DifferentiableAt ℝ (fun m : Fin 6 → ℝ => m k) l :=
    fun k => differentiableAt_apply k l
  fin_cases e <;> simp only [Lightlike.PR.extAngles] <;> simp only [Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Matrix.cons_val] <;> refine DifferentiableAt.const_sub ?_ π
  · exact differentiableAt_dihedral (d 0) (d 2) (d 1) (d 4) (d 5) (d 3) (hl 0)
      (pos (by unfold heron; ring) hABC) (pos (by unfold heron; ring) hABD)
      (pos (by unfold vol2; ring) hV)
  · exact differentiableAt_dihedral (d 1) (d 0) (d 2) (d 5) (d 3) (d 4) (hl 1)
      (pos (by unfold heron; ring) hABC) (pos (by unfold heron; ring) hBCD)
      (pos (by unfold vol2; ring) hV)
  · exact differentiableAt_dihedral (d 2) (d 1) (d 0) (d 3) (d 4) (d 5) (hl 2)
      (pos (by unfold heron; ring) hABC) (pos (by unfold heron; ring) hACD)
      (pos (by unfold vol2; ring) hV)
  · exact differentiableAt_dihedral (d 3) (d 2) (d 4) (d 1) (d 5) (d 0) (hl 3)
      (pos (by unfold heron; ring) hACD) (pos (by unfold heron; ring) hBCD)
      (pos (by unfold vol2; ring) hV)
  · exact differentiableAt_dihedral (d 4) (d 0) (d 5) (d 2) (d 3) (d 1) (hl 4)
      (pos (by unfold heron; ring) hABD) (pos (by unfold heron; ring) hACD)
      (pos (by unfold vol2; ring) hV)
  · exact differentiableAt_dihedral (d 5) (d 0) (d 4) (d 1) (d 3) (d 2) (hl 5)
      (pos (by unfold heron; ring) hABD) (pos (by unfold heron; ring) hBCD)
      (pos (by unfold vol2; ring) hV)

/-- The Regge action `Lightlike.PR.reggeAction` of a non-degenerate tetrahedron is a differentiable
function of its six edge lengths. -/
theorem differentiableAt_reggeAction_tet {l : Fin 6 → ℝ} (h : TetNondeg l) :
    DifferentiableAt ℝ Lightlike.PR.reggeAction l := by
  have : Lightlike.PR.reggeAction = fun m => ∑ i, m i * Lightlike.PR.extAngles m i := rfl
  rw [this]
  exact DifferentiableAt.fun_sum fun i _ =>
    (differentiableAt_apply i l).mul (differentiableAt_extAngles' h i)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The labelled lengths of a tetrahedron depend linearly, hence differentiably, on the length
assignment. -/
theorem differentiableAt_labLen (ℓ : Finset V → ℝ) (p q r s : V) :
    DifferentiableAt ℝ (fun m : Finset V → ℝ => labLen m p q r s) ℓ := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;> exact differentiableAt_apply _ ℓ

/-- One tetrahedron's term `Σ_{e ⊂ t} ℓ_e θ_t(e)` of the Regge action is differentiable at
non-degenerate lengths. -/
theorem differentiableAt_tetSum {K : Complex3 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg K ℓ)
    {t : Finset V} (ht : t ∈ K.tets) :
    DifferentiableAt ℝ (fun m : Finset V → ℝ => ∑ e ∈ t.powersetCard 2, m e * dihedralAt m t e)
      ℓ := by
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ := exists_label ht
  have hnd := hK.tetNondeg hpq hpr hps hqr hqs hrs ht
  have hL := differentiableAt_labLen ℓ p q r s
  have hLi := differentiableAt_pi.mp hL
  have hR := (differentiableAt_reggeAction_tet hnd).comp ℓ hL
  have hlin : DifferentiableAt ℝ (fun m : Finset V → ℝ => π * ∑ i, labLen m p q r s i) ℓ :=
    (DifferentiableAt.fun_sum fun i _ => hLi i).const_mul π
  refine (hlin.sub hR).congr_of_eventuallyEq ?_
  have hev : ∀ᶠ m in nhds ℓ, ∀ i, labLen m p q r s i ≠ 0 := by
    have : ∀ i, ∀ᶠ m in nhds ℓ, 0 < labLen m p q r s i := fun i =>
      (hLi i).continuousAt.eventually (lt_mem_nhds (hnd.1 i))
    filter_upwards [Filter.eventually_all.mpr this] with m hm i using (hm i).ne'
  filter_upwards [hev] with m hm
  rw [tetSum_eq m m hpq hpr hps hqr hqs hrs hm]
  simp only [Pi.sub_apply, Function.comp, Lightlike.PR.reggeAction, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- **The Regge action is differentiable** at non-degenerate edge lengths, as a function on the
finite-dimensional space of length assignments. -/
theorem differentiableAt_reggeAction {K : Complex3 V} {ℓ : Finset V → ℝ}
    (hK : LengthsNondeg K ℓ) : DifferentiableAt ℝ (reggeAction K) ℓ := by
  have : reggeAction K = fun m => ∑ e ∈ intEdges K, 2 * π * m e + ∑ e ∈ bdryEdges K, π * m e -
      ∑ t ∈ K.tets, ∑ e ∈ t.powersetCard 2, m e * dihedralAt m t e :=
    funext (reggeAction_eq_sum_tets K)
  rw [this]
  exact ((DifferentiableAt.fun_sum fun e _ => (differentiableAt_apply e ℓ).const_mul (2 * π)).add
    (DifferentiableAt.fun_sum fun e _ => (differentiableAt_apply e ℓ).const_mul π)).sub
    (DifferentiableAt.fun_sum fun t ht => differentiableAt_tetSum hK ht)

/-- The gradient of the Regge action at the lengths `ℓ`: the linear functional
`v ↦ Σ_{interior} v_e δ_e + Σ_{boundary} v_e ψ_e` on length variations. -/
noncomputable def reggeGradient (K : Complex3 V) (ℓ : Finset V → ℝ) : (Finset V → ℝ) →L[ℝ] ℝ :=
  ∑ e ∈ intEdges K, deficit K ℓ e • ContinuousLinearMap.proj e +
    ∑ e ∈ bdryEdges K, bdryAngle K ℓ e • ContinuousLinearMap.proj e

omit [Fintype V] in
/-- The gradient applied to a variation `v`. -/
theorem reggeGradient_apply (K : Complex3 V) (ℓ v : Finset V → ℝ) :
    reggeGradient K ℓ v =
      ∑ e ∈ intEdges K, v e * deficit K ℓ e + ∑ e ∈ bdryEdges K, v e * bdryAngle K ℓ e := by
  simp [reggeGradient, mul_comm]

/-- **Regge's equations, gradient form.** At non-degenerate edge lengths the Regge action is
differentiable on the space of length assignments, and its derivative is `reggeGradient`:
`∂S/∂ℓ_e` is the deficit angle `δ_e` at an interior edge and the boundary angle `ψ_e` at a
boundary edge. -/
theorem hasFDerivAt_reggeAction {K : Complex3 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg K ℓ) :
    HasFDerivAt (reggeAction K) (reggeGradient K ℓ) ℓ := by
  have hd := (differentiableAt_reggeAction hK).hasFDerivAt
  convert hd using 1
  ext v
  have hline : HasDerivAt (fun τ : ℝ => ℓ + τ • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ℓ
  have h1 := hd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have h2 := hasDerivAt_reggeAction hK v
  have hfun : (reggeAction K ∘ fun τ : ℝ => ℓ + τ • v) =
      fun τ => reggeAction K fun e => ℓ e + τ * v e := by
    funext τ
    simp only [Function.comp]
    congr 1
  rw [hfun] at h1
  rw [reggeGradient_apply, h2.unique h1]

end Lightlike.Regge
