import Lightlike.ODE.FlowDeriv
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Orbits of a Killing algebra

For finitely many vector fields `X a` on a real Banach space `E` and a parameter `ξ : ι → ℝ`, the field
`W_ξ = ∑ₐ ξₐ Xₐ` and the suspension field `(ξ, y) ↦ (0, W_ξ y)` on `(ι → ℝ) × E` (`suspField`). The flow of the
suspension field from `(ξ, p)` keeps `ξ` and moves `y` along `W_ξ`; its derivative in `ξ` is the derivative of the
orbit map `ξ ↦ exp(W_ξ)(p)`. When the brackets close with constant structure constants `S`,
`[Xₐ, X_c] = ∑ₑ S a c e • Xₑ`, the derivative of the flow on vectors `(ζ, ∑_b d_b Xᵦ(p))` is `(ζ, ∑ₑ dₑ(t) Xₑ(y t))` with
`d` solving the linear equation `ḋₑ = ζₑ - ∑_c d_c ∑ₐ ξₐ S a c e` (`fderiv_susp_flow`), and when the fields are Killing
the Gram matrix `Γₑf(t) = G(y t)(Xₑ, X_f)` solves `Γ̇ = C Γ + Γ Cᵀ` with `C = ∑ₐ ξₐ S a` (`hasDerivWithinAt_gram`).
Both equations involve only the structure constants: this is route (A) to G1-024 (Carroll, gr-qc/9712019, around
equation (8.1)), the orbit map of a Killing algebra as an adapted chart.
-/

open Set Metric
open scoped NNReal

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

/-- The suspension field `(ξ, y) ↦ (0, ∑ₐ ξₐ Xₐ y)` on `(ι → ℝ) × E`. -/
def suspField (X : ι → E → E) (q : (ι → ℝ) × E) : (ι → ℝ) × E := (0, ∑ a, q.1 a • X a q.2)

/-- The derivative of the suspension field: `(ζ, η) ↦ (0, ∑ₐ ζₐ Xₐ y + ∑ₐ ξₐ DXₐ(y) η)`. -/
noncomputable def suspDeriv (X : ι → E → E) (q : (ι → ℝ) × E) : ((ι → ℝ) × E) →L[ℝ] ((ι → ℝ) × E) :=
  (0 : ((ι → ℝ) × E) →L[ℝ] (ι → ℝ)).prod
    (∑ a, (((ContinuousLinearMap.proj a).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) E)).smulRight (X a q.2) +
      q.1 a • (fderiv ℝ (X a) q.2).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) E)))

theorem suspDeriv_apply (X : ι → E → E) (q : (ι → ℝ) × E) (v : (ι → ℝ) × E) :
    suspDeriv X q v = (0, ∑ a, v.1 a • X a q.2 + ∑ a, q.1 a • fderiv ℝ (X a) q.2 v.2) := by
  simp [suspDeriv, Finset.sum_add_distrib]

theorem hasFDerivAt_suspField (X : ι → E → E) {q : (ι → ℝ) × E} (hX : ∀ a, DifferentiableAt ℝ (X a) q.2) :
    HasFDerivAt (suspField X) (suspDeriv X q) q := by
  have h2 : HasFDerivAt (fun q : (ι → ℝ) × E => ∑ a, q.1 a • X a q.2)
      (∑ a, (((ContinuousLinearMap.proj a).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) E)).smulRight (X a q.2) +
        q.1 a • (fderiv ℝ (X a) q.2).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) E))) q := by
    refine HasFDerivAt.fun_sum fun a _ => ?_
    have hc : HasFDerivAt (fun q : (ι → ℝ) × E => q.1 a)
        ((ContinuousLinearMap.proj a).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) E)) q :=
      ((ContinuousLinearMap.proj a).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) E)).hasFDerivAt
    have hf : HasFDerivAt (fun q : (ι → ℝ) × E => X a q.2)
        ((fderiv ℝ (X a) q.2).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) E)) q :=
      (hX a).hasFDerivAt.comp q hasFDerivAt_snd
    convert hc.smul hf using 1
    abel
  exact (hasFDerivAt_const (0 : ι → ℝ) q).prodMk h2 |>.congr_fderiv (by ext <;> simp [suspDeriv])

/-- A function with zero derivative on `[-T, T]` takes there its value at `0`. -/
theorem eq_zero_of_hasDerivWithinAt_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    {T : ℝ} (hT : 0 < T) (hd : ∀ s ∈ Icc (-T) T, HasDerivWithinAt f 0 (Icc (-T) T) s) {t : ℝ}
    (ht : t ∈ Icc (-T) T) : f t = f 0 := by
  have hc : ContinuousOn f (Icc (-T) T) := fun s hs => (hd s hs).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hc fun s hs =>
    (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
  rw [hconst t ht, hconst 0 ⟨by linarith, hT.le⟩]

section Flow

variable {X : ι → E → E} {q₀ : (ι → ℝ) × E} {a r T : ℝ} {K : ℝ≥0} {Ψ : ℝ → (ι → ℝ) × E → (ι → ℝ) × E}

/-- The flow of the suspension field keeps the parameter. -/
theorem susp_flow_fst (h : ODE.IsFlowBox (suspField X) q₀ a r T K Ψ) {q : (ι → ℝ) × E} (hq : q ∈ ball q₀ r)
    {t : ℝ} (ht : t ∈ Icc (-T) T) : (Ψ t q).1 = q.1 := by
  have hd : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun s => (Ψ s q).1) 0 (Icc (-T) T) s := by
    intro s hs
    have := (HasFDerivAt.comp_hasDerivAt (l := Prod.fst) (f := fun s => Ψ s q) s
      (hasFDerivAt_fst (𝕜 := ℝ) (p := Ψ s q)) (h.hasDerivAt q hq s hs)).hasDerivWithinAt (s := Icc (-T) T)
    simpa [Function.comp_def, suspField] using this
  rw [eq_zero_of_hasDerivWithinAt_zero h.T_pos hd ht, h.flow_zero q hq]

/-- The flow of the suspension field moves the point along `W_ξ`. -/
theorem susp_flow_snd (h : ODE.IsFlowBox (suspField X) q₀ a r T K Ψ) {q : (ι → ℝ) × E} (hq : q ∈ ball q₀ r)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    HasDerivAt (fun s => (Ψ s q).2) (∑ a, q.1 a • X a (Ψ t q).2) t := by
  have := HasFDerivAt.comp_hasDerivAt (l := Prod.snd) (f := fun s => Ψ s q) t
    (hasFDerivAt_snd (𝕜 := ℝ) (p := Ψ t q)) (h.hasDerivAt q hq t ht)
  simpa [Function.comp_def, suspField, susp_flow_fst h hq ht] using this

end Flow

/-- The algebra behind the orbit derivative: with `DXₑ(Xₐ) = DXₐ(Xₑ) + ∑_f S a e f X_f`, the field
`∑ₑ (ζₑ - ∑_c d_c Cᶜₑ) Xₑ + ∑ₑ dₑ DXₑ(W)` is `∑ₐ ζₐ Xₐ + ∑ₐ ξₐ DXₐ(∑ₑ dₑ Xₑ)`, `C c e = ∑ₐ ξₐ S a c e`. -/
theorem orbit_identity (S : ι → ι → ι → ℝ) (Xv : ι → E) (DX : ι → E →L[ℝ] E)
    (hbr : ∀ a e, DX e (Xv a) = DX a (Xv e) + ∑ f, S a e f • Xv f) (ξ ζ d : ι → ℝ) :
    ∑ e, (ζ e - ∑ c, d c * ∑ a, ξ a * S a c e) • Xv e + ∑ e, d e • DX e (∑ a, ξ a • Xv a) =
      ∑ a, ζ a • Xv a + ∑ a, ξ a • DX a (∑ e, d e • Xv e) := by
  have hL : ∑ e, d e • DX e (∑ a, ξ a • Xv a) =
      ∑ e, ∑ a, (d e * ξ a) • (DX a (Xv e) + ∑ f, S a e f • Xv f) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hbr a e, smul_smul]
  rw [hL]
  simp only [map_sum, map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul, sub_smul,
    Finset.sum_sub_distrib, Finset.sum_smul, Finset.mul_sum]
  have h1 : ∑ e, ∑ a, (d e * ξ a) • DX a (Xv e) = ∑ a, ∑ e, (ξ a * d e) • DX a (Xv e) := by
    rw [Finset.sum_comm]; simp only [mul_comm]
  have h2 : ∑ e, ∑ c, ∑ a, (d c * (ξ a * S a c e)) • Xv e = ∑ e, ∑ a, ∑ f, (d e * ξ a * S a e f) • Xv f := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [h1, h2]
  abel

/-- The algebra behind the Gram equation: for Killing data `DGₐ u w + B(DXₐ u, w) + B(u, DXₐ w) = 0` and closed brackets,
the derivative of `B(Xₑ, X_f)` along `W = ∑ₐ ξₐ Xₐ` is `∑_g Cₑg B(X_g, X_f) + ∑_g C_fg B(Xₑ, X_g)`, `C e g = ∑ₐ ξₐ S a e g`. -/
theorem gram_identity (S : ι → ι → ι → ℝ) (ξ : ι → ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) (Xv : ι → E)
    (DX : ι → E →L[ℝ] E) (DG : ι → E →L[ℝ] E →L[ℝ] ℝ)
    (hbr : ∀ a e, DX e (Xv a) = DX a (Xv e) + ∑ f, S a e f • Xv f)
    (hK : ∀ a u w, DG a u w + B (DX a u) w + B u (DX a w) = 0) (e f : ι) :
    (∑ a, ξ a • DG a) (Xv e) (Xv f) + B (DX e (∑ a, ξ a • Xv a)) (Xv f) + B (Xv e) (DX f (∑ a, ξ a • Xv a)) =
      ∑ g, (∑ a, ξ a * S a e g) * B (Xv g) (Xv f) + ∑ g, (∑ a, ξ a * S a f g) * B (Xv e) (Xv g) := by
  have per : ∀ a, DG a (Xv e) (Xv f) + B (DX e (Xv a)) (Xv f) + B (Xv e) (DX f (Xv a)) =
      ∑ g, S a e g * B (Xv g) (Xv f) + ∑ g, S a f g * B (Xv e) (Xv g) := by
    intro a
    rw [hbr a e, hbr a f]
    simp only [map_add, add_apply, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    linarith [hK a (Xv e) (Xv f)]
  calc (∑ a, ξ a • DG a) (Xv e) (Xv f) + B (DX e (∑ a, ξ a • Xv a)) (Xv f) + B (Xv e) (DX f (∑ a, ξ a • Xv a))
      = ∑ a, ξ a * (DG a (Xv e) (Xv f) + B (DX e (Xv a)) (Xv f) + B (Xv e) (DX f (Xv a))) := by
        simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          mul_add]
    _ = ∑ a, ξ a * (∑ g, S a e g * B (Xv g) (Xv f) + ∑ g, S a f g * B (Xv e) (Xv g)) := by simp only [per]
    _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm (f := fun a g => ξ a * (S a e g * B (Xv g) (Xv f))),
          Finset.sum_comm (f := fun a g => ξ a * (S a f g * B (Xv e) (Xv g)))]
        simp only [mul_assoc]

/-- The Gram matrix `Γₑf = G(y)(Xₑ y, X_f y)` of the fields at `y`. -/
def gramAt (G : E → E →L[ℝ] E →L[ℝ] ℝ) (X : ι → E → E) (y : E) : ι → ι → ℝ := fun e f => G y (X e y) (X f y)

/-- The linear map `Γ ↦ C Γ + Γ Cᵀ`, `C e g = ∑ₐ ξₐ S a e g`, of the Gram equation. -/
noncomputable def gramL (S : ι → ι → ι → ℝ) (ξ : ι → ℝ) : (ι → ι → ℝ) →L[ℝ] (ι → ι → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Γ e f => ∑ g, (∑ a, ξ a * S a e g) * Γ g f + ∑ g, (∑ a, ξ a * S a f g) * Γ e g
      map_add' := fun Γ Γ' => by
        funext e f; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun c Γ => by
        funext e f; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun g _ => by ring }

theorem gramL_apply (S : ι → ι → ι → ℝ) (ξ : ι → ℝ) (Γ : ι → ι → ℝ) (e f : ι) :
    gramL S ξ Γ e f = ∑ g, (∑ a, ξ a * S a e g) * Γ g f + ∑ g, (∑ a, ξ a * S a f g) * Γ e g := rfl


/-- The algebra behind the equation of `G(J, Xₑ)` along an orbit. -/
theorem data_identity_M (S : ι → ι → ι → ℝ) (ξ ζ : ι → ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) (Xv : ι → E)
    (DX : ι → E →L[ℝ] E) (DG : ι → E →L[ℝ] E →L[ℝ] ℝ)
    (hbr : ∀ a e, DX e (Xv a) = DX a (Xv e) + ∑ f, S a e f • Xv f)
    (hK : ∀ a u w, DG a u w + B (DX a u) w + B u (DX a w) = 0) (J : E) (e : ι) :
    (∑ a, ξ a • DG a) J (Xv e) + B (∑ a, ζ a • Xv a + ∑ a, ξ a • DX a J) (Xv e) + B J (DX e (∑ a, ξ a • Xv a)) =
      ∑ a, ζ a * B (Xv a) (Xv e) + ∑ f, (∑ a, ξ a * S a e f) * B J (Xv f) := by
  have per : ∀ a, DG a J (Xv e) + B (DX a J) (Xv e) + B J (DX e (Xv a)) = ∑ f, S a e f * B J (Xv f) := by
    intro a
    rw [hbr a e]
    simp only [map_add, map_sum, map_smul, smul_eq_mul]
    linarith [hK a J (Xv e)]
  calc (∑ a, ξ a • DG a) J (Xv e) + B (∑ a, ζ a • Xv a + ∑ a, ξ a • DX a J) (Xv e) + B J (DX e (∑ a, ξ a • Xv a))
      = ∑ a, ζ a * B (Xv a) (Xv e) + ∑ a, ξ a * (DG a J (Xv e) + B (DX a J) (Xv e) + B J (DX e (Xv a))) := by
        simp only [map_add, add_apply, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
          Finset.sum_add_distrib, mul_add]
        ring
    _ = ∑ a, ζ a * B (Xv a) (Xv e) + ∑ a, ξ a * ∑ f, S a e f * B J (Xv f) := by simp only [per]
    _ = _ := by
        congr 1
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp only [mul_assoc]

/-- The algebra behind the equation of `G(J, J')` along an orbit. -/
theorem data_identity_N (ξ ζ ζ' : ι → ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u w, B u w = B w u) (Xv : ι → E)
    (DX : ι → E →L[ℝ] E) (DG : ι → E →L[ℝ] E →L[ℝ] ℝ)
    (hK : ∀ a u w, DG a u w + B (DX a u) w + B u (DX a w) = 0) (J J' : E) :
    (∑ a, ξ a • DG a) J J' + B (∑ a, ζ a • Xv a + ∑ a, ξ a • DX a J) J' + B J (∑ a, ζ' a • Xv a + ∑ a, ξ a • DX a J') =
      ∑ a, ζ a * B J' (Xv a) + ∑ a, ζ' a * B J (Xv a) := by
  have hz : ∑ a, ξ a * (DG a J J' + B (DX a J) J' + B J (DX a J')) = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [hK a J J', mul_zero]
  have hs : ∀ a, B (Xv a) J' = B J' (Xv a) := fun a => hB _ _
  simp only [map_add, add_apply, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, hs]
  simp only [mul_add, Finset.sum_add_distrib] at hz
  linarith

/-- The linear equation of the orbit data `(Γ, G(J, X), G(J', X), G(J, J'))`: it involves only the structure constants
and the parameters `ξ, ζ, ζ'`. -/
noncomputable def orbitL (S : ι → ι → ι → ℝ) (ξ ζ ζ' : ι → ℝ) :
    ((ι → ι → ℝ) × (ι → ℝ) × (ι → ℝ) × ℝ) →L[ℝ] ((ι → ι → ℝ) × (ι → ℝ) × (ι → ℝ) × ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Q => (gramL S ξ Q.1,
        fun e => ∑ a, ζ a * Q.1 a e + ∑ f, (∑ a, ξ a * S a e f) * Q.2.1 f,
        fun e => ∑ a, ζ' a * Q.1 a e + ∑ f, (∑ a, ξ a * S a e f) * Q.2.2.1 f,
        ∑ a, ζ a * Q.2.2.1 a + ∑ a, ζ' a * Q.2.1 a)
      map_add' := fun Q Q' => by
        refine Prod.ext (map_add _ _ _) (Prod.ext ?_ (Prod.ext ?_ ?_))
        · funext e; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
        · funext e; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
        · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun c Q => by
        refine Prod.ext (map_smul _ _ _) (Prod.ext ?_ (Prod.ext ?_ ?_))
        · funext e; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
            mul_add, Finset.mul_sum]; congr 1 <;> refine Finset.sum_congr rfl fun g _ => by ring
        · funext e; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
            mul_add, Finset.mul_sum]; congr 1 <;> refine Finset.sum_congr rfl fun g _ => by ring
        · simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add,
            Finset.mul_sum]
          congr 1 <;> refine Finset.sum_congr rfl fun g _ => by ring }

theorem orbitL_apply (S : ι → ι → ι → ℝ) (ξ ζ ζ' : ι → ℝ) (Q : (ι → ι → ℝ) × (ι → ℝ) × (ι → ℝ) × ℝ) :
    orbitL S ξ ζ ζ' Q = (gramL S ξ Q.1,
        fun e => ∑ a, ζ a * Q.1 a e + ∑ f, (∑ a, ξ a * S a e f) * Q.2.1 f,
        fun e => ∑ a, ζ' a * Q.1 a e + ∑ f, (∑ a, ξ a * S a e f) * Q.2.2.1 f,
        ∑ a, ζ a * Q.2.2.1 a + ∑ a, ζ' a * Q.2.1 a) := rfl


/-- The orbit data at time `t` from `q`: the Gram matrix `Γ` at `y = (Ψ_t q).2`, the pairings `G(J, Xₑ)`, `G(J', Xₑ)` and
`G(J, J')` of the `E`-parts `J, J'` of `DΨ_t q v` and `DΨ_t q v'`. -/
noncomputable def orbitData (G : E → E →L[ℝ] E →L[ℝ] ℝ) (X : ι → E → E) (Ψ : ℝ → (ι → ℝ) × E → (ι → ℝ) × E)
    (q : (ι → ℝ) × E) (v v' : (ι → ℝ) × E) (t : ℝ) : (ι → ι → ℝ) × (ι → ℝ) × (ι → ℝ) × ℝ :=
  (gramAt G X (Ψ t q).2,
    fun e => G (Ψ t q).2 (fderiv ℝ (Ψ t) q v).2 (X e (Ψ t q).2),
    fun e => G (Ψ t q).2 (fderiv ℝ (Ψ t) q v').2 (X e (Ψ t q).2),
    G (Ψ t q).2 (fderiv ℝ (Ψ t) q v).2 (fderiv ℝ (Ψ t) q v').2)


section Variational

variable [CompleteSpace E] {X : ι → E → E} {q₀ : (ι → ℝ) × E} {a r T : ℝ} {K : ℝ≥0}
  {Ψ : ℝ → (ι → ℝ) × E → (ι → ℝ) × E}

/-- **The derivative of the suspension flow.** If the brackets close, `[Xₐ, X_c] = ∑ₑ S a c e • Xₑ`, then
`DΨ_t(ξ, y)(ζ, ∑_b d_b(0) Xᵦ(y)) = (ζ, ∑ₑ dₑ(t) Xₑ(Ψ_t))` for `d` solving `ḋₑ = ζₑ - ∑_c d_c ∑ₐ ξₐ S a c e`: both sides
solve the first variational equation of the suspension field with the same value at `0`. -/
theorem fderiv_susp_flow (h : ODE.IsFlowBox (suspField X) q₀ a r T K Ψ)
    (hX : ∀ c, ∀ q ∈ ball q₀ a, DifferentiableAt ℝ (X c) q.2) (S : ι → ι → ι → ℝ)
    (hS : ∀ a' c, ∀ q ∈ ball q₀ a, VectorField.lieBracket ℝ (X a') (X c) q.2 = ∑ e, S a' c e • X e q.2)
    {q : (ι → ℝ) × E} (hq : q ∈ ball q₀ r) (ζ : ι → ℝ) (d : ℝ → ι → ℝ)
    (hd : ∀ t ∈ Icc (-T) T, HasDerivWithinAt d (fun e => ζ e - ∑ c, d t c * ∑ a', q.1 a' * S a' c e)
      (Icc (-T) T) t)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    fderiv ℝ (Ψ t) q (ζ, ∑ b, d 0 b • X b q.2) = (ζ, ∑ e, d t e • X e (Ψ t q).2) := by
  set v0 : (ι → ℝ) × E := (ζ, ∑ b, d 0 b • X b q.2)
  have hl : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun s => fderiv ℝ (Ψ s) q v0)
      (fderiv ℝ (suspField X) (Ψ s q) (fderiv ℝ (Ψ s) q v0)) (Icc (-T) T) s := by
    intro s hs
    have := (h.hasDerivWithinAt_fderiv_flow hq hs).clm_apply (hasDerivWithinAt_const s (Icc (-T) T) v0)
    simpa using this
  have hu : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun s => ((ζ, ∑ e, d s e • X e (Ψ s q).2) : (ι → ℝ) × E))
      (fderiv ℝ (suspField X) (Ψ s q) (ζ, ∑ e, d s e • X e (Ψ s q).2)) (Icc (-T) T) s := by
    intro s hs
    have hy := h.flow_mem q hq s hs
    have hfd : fderiv ℝ (suspField X) (Ψ s q) = suspDeriv X (Ψ s q) :=
      (hasFDerivAt_suspField X (fun c => hX c _ hy)).fderiv
    rw [hfd, suspDeriv_apply, susp_flow_fst h hq hs]
    have hde : ∀ e, HasDerivWithinAt (fun s => d s e) (ζ e - ∑ c, d s c * ∑ a', q.1 a' * S a' c e)
        (Icc (-T) T) s := fun e => (hasDerivWithinAt_pi.1 (hd s hs)) e
    have hXe : ∀ e, HasDerivWithinAt (fun s => X e (Ψ s q).2)
        (fderiv ℝ (X e) (Ψ s q).2 (∑ a', q.1 a' • X a' (Ψ s q).2)) (Icc (-T) T) s := fun e =>
      (HasFDerivAt.comp_hasDerivAt (l := X e) (f := fun s => (Ψ s q).2) s (hX e _ hy).hasFDerivAt
        (susp_flow_snd h hq hs)).hasDerivWithinAt
    have hsum := HasDerivWithinAt.sum (u := Finset.univ) fun e _ => (hde e).smul (hXe e)
    have hpair := (hasDerivWithinAt_const s (Icc (-T) T) ζ).prodMk hsum
    convert hpair using 1
    · funext s'; simp
    · refine Prod.ext rfl ?_
      simp only
      have key := orbit_identity S (fun e => X e (Ψ s q).2) (fun e => fderiv ℝ (X e) (Ψ s q).2)
        (fun a' e => by
          have := hS a' e _ hy
          rw [VectorField.lieBracket] at this
          rw [← this]; abel) q.1 ζ (d s)
      rw [← key, add_comm]
      simp only [Finset.sum_add_distrib]
  have hA : ∀ s ∈ Icc (-T) T, ‖fderiv ℝ (suspField X) (Ψ s q)‖ ≤ K := fun s hs =>
    h.norm_fderiv_le _ (h.flow_mem q hq s hs)
  exact ODE.eqOn_of_linear (A := fun s => fderiv ℝ (suspField X) (Ψ s q)) hA hl hu (by
    simp only [h.fderiv_flow_zero hq, ContinuousLinearMap.id_apply, h.flow_zero q hq, v0]) ht

omit [CompleteSpace E] in
/-- **The Gram equation along an orbit.** If the fields are Killing for `G` and their brackets close, the Gram matrix along
the orbit `y(t) = (Ψ_t(ξ, y)).2` solves `Γ̇ = C Γ + Γ Cᵀ` (`gramL`), an equation in the structure constants only. -/
theorem hasDerivWithinAt_gram (h : ODE.IsFlowBox (suspField X) q₀ a r T K Ψ)
    (hX : ∀ c, ∀ q ∈ ball q₀ a, DifferentiableAt ℝ (X c) q.2) (S : ι → ι → ι → ℝ)
    (hS : ∀ a' c, ∀ q ∈ ball q₀ a, VectorField.lieBracket ℝ (X a') (X c) q.2 = ∑ e, S a' c e • X e q.2)
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (hG : ∀ q ∈ ball q₀ a, DifferentiableAt ℝ G q.2)
    (hK : ∀ c, ∀ q ∈ ball q₀ a, ∀ u w : E, fderiv ℝ G q.2 (X c q.2) u w + G q.2 (fderiv ℝ (X c) q.2 u) w +
      G q.2 u (fderiv ℝ (X c) q.2 w) = 0)
    {q : (ι → ℝ) × E} (hq : q ∈ ball q₀ r) {s : ℝ} (hs : s ∈ Icc (-T) T) :
    HasDerivWithinAt (fun s => gramAt G X (Ψ s q).2) (gramL S q.1 (gramAt G X (Ψ s q).2)) (Icc (-T) T) s := by
  have hy := h.flow_mem q hq s hs
  have hW := susp_flow_snd h hq hs
  have hGy : HasDerivWithinAt (fun s => G (Ψ s q).2) (fderiv ℝ G (Ψ s q).2 (∑ a', q.1 a' • X a' (Ψ s q).2))
      (Icc (-T) T) s :=
    (HasFDerivAt.comp_hasDerivAt (l := G) (f := fun s => (Ψ s q).2) s (hG _ hy).hasFDerivAt hW).hasDerivWithinAt
  have hXe : ∀ e, HasDerivWithinAt (fun s => X e (Ψ s q).2)
      (fderiv ℝ (X e) (Ψ s q).2 (∑ a', q.1 a' • X a' (Ψ s q).2)) (Icc (-T) T) s := fun e =>
    (HasFDerivAt.comp_hasDerivAt (l := X e) (f := fun s => (Ψ s q).2) s (hX e _ hy).hasFDerivAt hW).hasDerivWithinAt
  refine hasDerivWithinAt_pi.2 fun e => hasDerivWithinAt_pi.2 fun f => ?_
  have := (hGy.clm_apply (hXe e)).clm_apply (hXe f)
  convert this using 1
  all_goals try rfl
  rw [gramL_apply]
  have key := gram_identity S q.1 (G (Ψ s q).2) (fun e => X e (Ψ s q).2) (fun e => fderiv ℝ (X e) (Ψ s q).2)
    (fun a' => fderiv ℝ G (Ψ s q).2 (X a' (Ψ s q).2))
    (fun a' e => by
      have := hS a' e _ hy
      rw [VectorField.lieBracket] at this
      rw [← this]; abel)
    (fun a' u w => hK a' _ hy u w) e f
  simp only [gramAt]
  rw [← key]
  simp only [map_sum, map_smul, add_apply, sum_apply, smul_apply]

/-- The derivative of the suspension flow keeps the parameter direction. -/
theorem susp_fderiv_flow_fst (h : ODE.IsFlowBox (suspField X) q₀ a r T K Ψ)
    (hX : ∀ c, ∀ q ∈ ball q₀ a, DifferentiableAt ℝ (X c) q.2) {q : (ι → ℝ) × E} (hq : q ∈ ball q₀ r)
    (v : (ι → ℝ) × E) {t : ℝ} (ht : t ∈ Icc (-T) T) : (fderiv ℝ (Ψ t) q v).1 = v.1 := by
  have hd : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun s => (fderiv ℝ (Ψ s) q v).1) 0 (Icc (-T) T) s := by
    intro s hs
    have hy := h.flow_mem q hq s hs
    have h1 := (h.hasDerivWithinAt_fderiv_flow hq hs).clm_apply (hasDerivWithinAt_const s (Icc (-T) T) v)
    have h2 := (HasFDerivAt.comp_hasDerivWithinAt (l := Prod.fst) (f := fun s => fderiv ℝ (Ψ s) q v) s
      (hasFDerivAt_fst (𝕜 := ℝ) (p := fderiv ℝ (Ψ s) q v)) h1)
    rw [(hasFDerivAt_suspField X (fun c => hX c _ hy)).fderiv] at h2
    simpa [Function.comp_def, suspDeriv_apply] using h2
  rw [eq_zero_of_hasDerivWithinAt_zero h.T_pos hd ht, h.fderiv_flow_zero hq, ContinuousLinearMap.id_apply]

/-- The `E`-part of the derivative of the suspension flow solves `J̇ = ∑ₐ ζₐ Xₐ + DW_ξ J`. -/
theorem susp_fderiv_flow_snd (h : ODE.IsFlowBox (suspField X) q₀ a r T K Ψ)
    (hX : ∀ c, ∀ q ∈ ball q₀ a, DifferentiableAt ℝ (X c) q.2) {q : (ι → ℝ) × E} (hq : q ∈ ball q₀ r)
    (v : (ι → ℝ) × E) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    HasDerivWithinAt (fun s => (fderiv ℝ (Ψ s) q v).2)
      (∑ a, v.1 a • X a (Ψ t q).2 + ∑ a, q.1 a • fderiv ℝ (X a) (Ψ t q).2 (fderiv ℝ (Ψ t) q v).2)
      (Icc (-T) T) t := by
  have hy := h.flow_mem q hq t ht
  have h1 := (h.hasDerivWithinAt_fderiv_flow hq ht).clm_apply (hasDerivWithinAt_const t (Icc (-T) T) v)
  have h2 := (HasFDerivAt.comp_hasDerivWithinAt (l := Prod.snd) (f := fun s => fderiv ℝ (Ψ s) q v) t
    (hasFDerivAt_snd (𝕜 := ℝ) (p := fderiv ℝ (Ψ t) q v)) h1)
  rw [(hasFDerivAt_suspField X (fun c => hX c _ hy)).fderiv] at h2
  simpa [Function.comp_def, suspDeriv_apply, susp_flow_fst h hq ht, susp_fderiv_flow_fst h hX hq v ht] using h2

/-- **The orbit data solve a linear equation in the structure constants** (`orbitL`). -/
theorem hasDerivWithinAt_orbitData (h : ODE.IsFlowBox (suspField X) q₀ a r T K Ψ)
    (hX : ∀ c, ∀ q ∈ ball q₀ a, DifferentiableAt ℝ (X c) q.2) (S : ι → ι → ι → ℝ)
    (hS : ∀ a' c, ∀ q ∈ ball q₀ a, VectorField.lieBracket ℝ (X a') (X c) q.2 = ∑ e, S a' c e • X e q.2)
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (hG : ∀ q ∈ ball q₀ a, DifferentiableAt ℝ G q.2)
    (hK : ∀ c, ∀ q ∈ ball q₀ a, ∀ u w : E, fderiv ℝ G q.2 (X c q.2) u w + G q.2 (fderiv ℝ (X c) q.2 u) w +
      G q.2 u (fderiv ℝ (X c) q.2 w) = 0)
    (hsym : ∀ q ∈ ball q₀ a, ∀ u w : E, G q.2 u w = G q.2 w u)
    {q : (ι → ℝ) × E} (hq : q ∈ ball q₀ r) (v v' : (ι → ℝ) × E) {s : ℝ} (hs : s ∈ Icc (-T) T) :
    HasDerivWithinAt (orbitData G X Ψ q v v') (orbitL S q.1 v.1 v'.1 (orbitData G X Ψ q v v' s)) (Icc (-T) T) s := by
  have hy := h.flow_mem q hq s hs
  have hW := susp_flow_snd h hq hs
  have hGy : HasDerivWithinAt (fun s => G (Ψ s q).2) (fderiv ℝ G (Ψ s q).2 (∑ a', q.1 a' • X a' (Ψ s q).2))
      (Icc (-T) T) s :=
    (HasFDerivAt.comp_hasDerivAt (l := G) (f := fun s => (Ψ s q).2) s (hG _ hy).hasFDerivAt hW).hasDerivWithinAt
  have hXe : ∀ e, HasDerivWithinAt (fun s => X e (Ψ s q).2)
      (fderiv ℝ (X e) (Ψ s q).2 (∑ a', q.1 a' • X a' (Ψ s q).2)) (Icc (-T) T) s := fun e =>
    (HasFDerivAt.comp_hasDerivAt (l := X e) (f := fun s => (Ψ s q).2) s (hX e _ hy).hasFDerivAt hW).hasDerivWithinAt
  have hJ := susp_fderiv_flow_snd h hX hq v hs
  have hJ' := susp_fderiv_flow_snd h hX hq v' hs
  have hbr : ∀ a' e, fderiv ℝ (X e) (Ψ s q).2 (X a' (Ψ s q).2) =
      fderiv ℝ (X a') (Ψ s q).2 (X e (Ψ s q).2) + ∑ f, S a' e f • X f (Ψ s q).2 := fun a' e => by
    have := hS a' e _ hy
    rw [VectorField.lieBracket] at this
    rw [← this]; abel
  have hK' : ∀ a' u w, fderiv ℝ G (Ψ s q).2 (X a' (Ψ s q).2) u w + G (Ψ s q).2 (fderiv ℝ (X a') (Ψ s q).2 u) w +
      G (Ψ s q).2 u (fderiv ℝ (X a') (Ψ s q).2 w) = 0 := fun a' u w => hK a' _ hy u w
  rw [orbitL_apply]
  refine (hasDerivWithinAt_gram h hX S hS G hG hK hq hs).prodMk ((hasDerivWithinAt_pi.2 fun e => ?_).prodMk
    ((hasDerivWithinAt_pi.2 fun e => ?_).prodMk ?_))
  · have := (hGy.clm_apply hJ).clm_apply (hXe e)
    convert this using 1
    have key := data_identity_M S q.1 v.1 (G (Ψ s q).2) (fun e => X e (Ψ s q).2)
      (fun e => fderiv ℝ (X e) (Ψ s q).2) (fun a' => fderiv ℝ G (Ψ s q).2 (X a' (Ψ s q).2)) hbr hK'
      (fderiv ℝ (Ψ s) q v).2 e
    simp only [orbitData, gramAt]
    rw [← key]
    simp only [map_sum, map_smul, add_apply, sum_apply, smul_apply]
  · have := (hGy.clm_apply hJ').clm_apply (hXe e)
    convert this using 1
    have key := data_identity_M S q.1 v'.1 (G (Ψ s q).2) (fun e => X e (Ψ s q).2)
      (fun e => fderiv ℝ (X e) (Ψ s q).2) (fun a' => fderiv ℝ G (Ψ s q).2 (X a' (Ψ s q).2)) hbr hK'
      (fderiv ℝ (Ψ s) q v').2 e
    simp only [orbitData, gramAt]
    rw [← key]
    simp only [map_sum, map_smul, add_apply, sum_apply, smul_apply]
  · have := (hGy.clm_apply hJ).clm_apply hJ'
    convert this using 1
    have key := data_identity_N q.1 v.1 v'.1 (G (Ψ s q).2) (hsym _ hy) (fun e => X e (Ψ s q).2)
      (fun e => fderiv ℝ (X e) (Ψ s q).2) (fun a' => fderiv ℝ G (Ψ s q).2 (X a' (Ψ s q).2)) hK'
      (fderiv ℝ (Ψ s) q v).2 (fderiv ℝ (Ψ s) q v').2
    simp only [orbitData]
    rw [← key]
    simp only [map_sum, map_smul, add_apply, sum_apply, smul_apply]

theorem orbitData_zero (h : ODE.IsFlowBox (suspField X) q₀ a r T K Ψ) (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    {q : (ι → ℝ) × E} (hq : q ∈ ball q₀ r) (v v' : (ι → ℝ) × E) :
    orbitData G X Ψ q v v' 0 = (gramAt G X q.2, fun e => G q.2 v.2 (X e q.2), fun e => G q.2 v'.2 (X e q.2),
      G q.2 v.2 v'.2) := by
  simp only [orbitData, h.flow_zero q hq, h.fderiv_flow_zero hq, ContinuousLinearMap.id_apply]

end Variational

section Comparison

variable [CompleteSpace E] {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]

/-- **Two Killing algebras with the same structure constants have proportional metrics along their orbits.** For fields
`X` on `E` and `X₂` on `E₂`, Killing for symmetric `G`, `G₂`, with the same structure constants `S`, and Gram matrices
`Γ(p) = c Γ₂(p₂)`, the metrics pulled back along the suspension flows from `(ξ, p)` and `(ξ, p₂)` agree up to `c`:
`G(DΨ_t(ζ, 0), DΨ_t(ζ', 0)) = c G₂(DΨ₂_t(ζ, 0), DΨ₂_t(ζ', 0))`. Both sides are the last component of a solution of the
same linear equation (`orbitL`) with proportional initial values. -/
theorem orbit_comparison {X : ι → E → E} {q₀ : (ι → ℝ) × E} {a r T : ℝ} {K : ℝ≥0}
    {Ψ : ℝ → (ι → ℝ) × E → (ι → ℝ) × E} (h : ODE.IsFlowBox (suspField X) q₀ a r T K Ψ)
    {X₂ : ι → E₂ → E₂} {q₂₀ : (ι → ℝ) × E₂} {a₂ r₂ : ℝ} {K₂ : ℝ≥0}
    {Ψ₂ : ℝ → (ι → ℝ) × E₂ → (ι → ℝ) × E₂} (h₂ : ODE.IsFlowBox (suspField X₂) q₂₀ a₂ r₂ T K₂ Ψ₂)
    (S : ι → ι → ι → ℝ)
    (hX : ∀ c, ∀ q ∈ ball q₀ a, DifferentiableAt ℝ (X c) q.2)
    (hS : ∀ a' c, ∀ q ∈ ball q₀ a, VectorField.lieBracket ℝ (X a') (X c) q.2 = ∑ e, S a' c e • X e q.2)
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (hG : ∀ q ∈ ball q₀ a, DifferentiableAt ℝ G q.2)
    (hK : ∀ c, ∀ q ∈ ball q₀ a, ∀ u w : E, fderiv ℝ G q.2 (X c q.2) u w + G q.2 (fderiv ℝ (X c) q.2 u) w +
      G q.2 u (fderiv ℝ (X c) q.2 w) = 0)
    (hsym : ∀ q ∈ ball q₀ a, ∀ u w : E, G q.2 u w = G q.2 w u)
    (hX₂ : ∀ c, ∀ q ∈ ball q₂₀ a₂, DifferentiableAt ℝ (X₂ c) q.2)
    (hS₂ : ∀ a' c, ∀ q ∈ ball q₂₀ a₂, VectorField.lieBracket ℝ (X₂ a') (X₂ c) q.2 = ∑ e, S a' c e • X₂ e q.2)
    (G₂ : E₂ → E₂ →L[ℝ] E₂ →L[ℝ] ℝ) (hG₂ : ∀ q ∈ ball q₂₀ a₂, DifferentiableAt ℝ G₂ q.2)
    (hK₂ : ∀ c, ∀ q ∈ ball q₂₀ a₂, ∀ u w : E₂, fderiv ℝ G₂ q.2 (X₂ c q.2) u w + G₂ q.2 (fderiv ℝ (X₂ c) q.2 u) w +
      G₂ q.2 u (fderiv ℝ (X₂ c) q.2 w) = 0)
    (hsym₂ : ∀ q ∈ ball q₂₀ a₂, ∀ u w : E₂, G₂ q.2 u w = G₂ q.2 w u)
    {ξ : ι → ℝ} {p : E} {p₂ : E₂} (hq : ((ξ, p) : (ι → ℝ) × E) ∈ ball q₀ r)
    (hq₂ : ((ξ, p₂) : (ι → ℝ) × E₂) ∈ ball q₂₀ r₂) (c : ℝ) (hΓ : gramAt G X p = c • gramAt G₂ X₂ p₂)
    (ζ ζ' : ι → ℝ) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    G (Ψ t (ξ, p)).2 (fderiv ℝ (Ψ t) (ξ, p) (ζ, 0)).2 (fderiv ℝ (Ψ t) (ξ, p) (ζ', 0)).2 =
      c * G₂ (Ψ₂ t (ξ, p₂)).2 (fderiv ℝ (Ψ₂ t) (ξ, p₂) (ζ, 0)).2 (fderiv ℝ (Ψ₂ t) (ξ, p₂) (ζ', 0)).2 := by
  have hu := fun s (hs : s ∈ Icc (-T) T) =>
    hasDerivWithinAt_orbitData h hX S hS G hG hK hsym hq (ζ, 0) (ζ', 0) hs
  have hv : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun s => c • orbitData G₂ X₂ Ψ₂ (ξ, p₂) (ζ, 0) (ζ', 0) s)
      (orbitL S ξ ζ ζ' (c • orbitData G₂ X₂ Ψ₂ (ξ, p₂) (ζ, 0) (ζ', 0) s)) (Icc (-T) T) s := fun s hs => by
    rw [map_smul]
    exact (hasDerivWithinAt_orbitData h₂ hX₂ S hS₂ G₂ hG₂ hK₂ hsym₂ hq₂ (ζ, 0) (ζ', 0) hs).const_smul c
  have hA : ∀ s ∈ Icc (-T) T, ‖orbitL S ξ ζ ζ'‖ ≤ ‖orbitL S ξ ζ ζ'‖ := fun _ _ => le_rfl
  have heq := ODE.eqOn_of_linear (A := fun _ => orbitL S ξ ζ ζ') hA hu hv (by
    rw [orbitData_zero h G hq, orbitData_zero h₂ G₂ hq₂, hΓ]
    simp only [map_zero, zero_apply]
    ext <;> simp) ht
  have := congrArg (fun Q => Q.2.2.2) heq
  simpa [orbitData] using this

end Comparison


end Lightlike
