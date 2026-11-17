import Lightlike.Gauge.ConstraintsAPI

/-!
# The Jacobi identity for Physlib's Poisson bracket

For observables that are `C²` on the phase space `X × X`, `{f, {g, h}} + {g, {h, f}} + {h, {f, g}} = 0`
(`poissonBracket_jacobi`). The proof writes the bracket as the derivative of `g` along the Hamiltonian vector
field of `f`, `{f, g} = dg (X_f)` (`poissonBracket_eq_hamVec`), differentiates once more
(`hasFDerivAt_bracket`) and uses the symmetry of the second derivative. Physlib's Poisson bracket file lists
this identity as a TODO.

## References

* M. Henneaux and C. Teitelboim, *Quantization of Gauge Systems*, Princeton University Press (1992), Chapter 1.
-/
open ClassicalMechanics InnerProductSpace
open scoped ContDiff
namespace Lightlike.Gauge
variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The momentum part of the Riesz representative of a covector on `X × X`: `⟨Rp ℓ, w⟩ = ℓ (w, 0)`. -/
noncomputable def Rp (ℓ : X × X →L[ℝ] ℝ) : X := (InnerProductSpace.toDual ℝ X).symm (ℓ.comp (ContinuousLinearMap.inl ℝ X X))
/-- The position part of the Riesz representative of a covector on `X × X`: `⟨Rq ℓ, w⟩ = ℓ (0, w)`. -/
noncomputable def Rq (ℓ : X × X →L[ℝ] ℝ) : X := (InnerProductSpace.toDual ℝ X).symm (ℓ.comp (ContinuousLinearMap.inr ℝ X X))

/-- The Hamiltonian vector `(∂_q f, -∂_p f)` of a covector `ℓ = df`. -/
noncomputable def hamVec (ℓ : X × X →L[ℝ] ℝ) : X × X := (Rq ℓ, -Rp ℓ)

/-- The defining property of `Rp`. -/
theorem inner_Rp (m : X × X →L[ℝ] ℝ) (w : X) : ⟪Rp m, w⟫_ℝ = m (w, 0) := by
  have := congrArg (fun φ => φ w) ((InnerProductSpace.toDual ℝ X).apply_symm_apply (m.comp (ContinuousLinearMap.inl ℝ X X)))
  simp [Rp]

/-- The defining property of `Rq`. -/
theorem inner_Rq (m : X × X →L[ℝ] ℝ) (w : X) : ⟪Rq m, w⟫_ℝ = m (0, w) := by
  have := congrArg (fun φ => φ w) ((InnerProductSpace.toDual ℝ X).apply_symm_apply (m.comp (ContinuousLinearMap.inr ℝ X X)))
  simp [Rq]

/-- `m (X_ℓ) = ⟨R_p m, R_q ℓ⟩ - ⟨R_q m, R_p ℓ⟩`. -/
theorem apply_hamVec (ℓ m : X × X →L[ℝ] ℝ) :
    m (hamVec ℓ) = ⟪Rp m, Rq ℓ⟫_ℝ - ⟪Rq m, Rp ℓ⟫_ℝ := by
  rw [inner_Rp, inner_Rq]
  have : hamVec ℓ = (Rq ℓ, 0) + (0, -Rp ℓ) := by simp [hamVec]
  rw [this, map_add]
  have h2 : m (0, -Rp ℓ) = -m (0, Rp ℓ) := by
    rw [← map_neg]; simp
  rw [h2]; ring

/-- `m (X_ℓ) = - ℓ (X_m)`: the Poisson pairing of two covectors is antisymmetric. -/
theorem hamVec_antisymm (ℓ m : X × X →L[ℝ] ℝ) : m (hamVec ℓ) = -ℓ (hamVec m) := by
  rw [apply_hamVec, apply_hamVec, real_inner_comm (Rp ℓ) (Rq m), real_inner_comm (Rq ℓ) (Rp m)]; ring

omit [CompleteSpace X] in
/-- The derivative of the slice `p' ↦ (p', q)`. -/
theorem hasFDerivAt_inl_slice (x : X × X) :
    HasFDerivAt (fun p' : X => (p', x.2)) (ContinuousLinearMap.inl ℝ X X) x.1 := by
  have := (hasFDerivAt_id x.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) x.2 x.1)
  exact this.congr_fderiv (ContinuousLinearMap.ext fun v => by simp)

omit [CompleteSpace X] in
/-- The derivative of the slice `q' ↦ (p, q')`. -/
theorem hasFDerivAt_inr_slice (x : X × X) :
    HasFDerivAt (fun q' : X => (x.1, q')) (ContinuousLinearMap.inr ℝ X X) x.2 := by
  have := (hasFDerivAt_const (𝕜 := ℝ) x.1 x.2).prodMk (hasFDerivAt_id x.2)
  exact this.congr_fderiv (ContinuousLinearMap.ext fun v => by simp)

/-- The momentum gradient of `f` is `Rp (dF)`. -/
theorem gradient_p_eq (f : X → X → ℝ) (x : X × X) (hf : DifferentiableAt ℝ (fun y : X × X => f y.1 y.2) x) :
    gradient (fun p' => f p' x.2) x.1 = Rp (fderiv ℝ (fun y : X × X => f y.1 y.2) x) := by
  have hg : HasFDerivAt (fun y : X × X => f y.1 y.2) (fderiv ℝ (fun y : X × X => f y.1 y.2) x)
      ((fun p' : X => (p', x.2)) x.1) := by simpa using hf.hasFDerivAt
  have h2 := hg.comp x.1 (hasFDerivAt_inl_slice x)
  rw [gradient]
  rw [show (fun p' => f p' x.2) = (fun y : X × X => f y.1 y.2) ∘ (fun p' : X => (p', x.2)) from rfl, h2.fderiv]
  rfl

/-- The position gradient of `f` is `Rq (dF)`. -/
theorem gradient_q_eq (f : X → X → ℝ) (x : X × X) (hf : DifferentiableAt ℝ (fun y : X × X => f y.1 y.2) x) :
    gradient (fun q' => f x.1 q') x.2 = Rq (fderiv ℝ (fun y : X × X => f y.1 y.2) x) := by
  have hg : HasFDerivAt (fun y : X × X => f y.1 y.2) (fderiv ℝ (fun y : X × X => f y.1 y.2) x)
      ((fun q' : X => (x.1, q')) x.2) := by simpa using hf.hasFDerivAt
  have h2 := hg.comp x.2 (hasFDerivAt_inr_slice x)
  rw [gradient]
  rw [show (fun q' => f x.1 q') = (fun y : X × X => f y.1 y.2) ∘ (fun q' : X => (x.1, q')) from rfl, h2.fderiv]
  rfl

/-- Physlib's Poisson bracket is the derivative of `g` along the Hamiltonian vector of `f`: `{f, g} = dg (X_f)`. -/
theorem poissonBracket_eq_hamVec (f g : X → X → ℝ) (x : X × X)
    (hf : DifferentiableAt ℝ (fun y : X × X => f y.1 y.2) x)
    (hg : DifferentiableAt ℝ (fun y : X × X => g y.1 y.2) x) :
    poissonBracket f g x.1 x.2 =
      fderiv ℝ (fun y : X × X => g y.1 y.2) x (hamVec (fderiv ℝ (fun y : X × X => f y.1 y.2) x)) := by
  rw [apply_hamVec, poissonBracket, gradient_p_eq f x hf, gradient_q_eq f x hf, gradient_p_eq g x hg,
    gradient_q_eq g x hg, real_inner_comm (Rp (fderiv ℝ (fun y : X × X => g y.1 y.2) x))]
  congr 1
  exact real_inner_comm _ _

/-- A partial Riesz map as a continuous linear map, for a continuous linear embedding `ι : X →L X × X`. -/
noncomputable def rieszL (ι : X →L[ℝ] X × X) : (X × X →L[ℝ] ℝ) →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun ℓ : X × X →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ X).symm (ℓ.comp ι)
      map_add' := fun (ℓ m : X × X →L[ℝ] ℝ) => by simp
      map_smul' := fun (c : ℝ) (ℓ : X × X →L[ℝ] ℝ) => by simp }
    ‖ι‖ (fun ℓ : X × X →L[ℝ] ℝ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometryEquiv.norm_map]
      calc ‖ℓ.comp ι‖ ≤ ‖ℓ‖ * ‖ι‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖ι‖ * ‖ℓ‖ := mul_comm _ _)

/-- `hamVec` as a continuous linear map. -/
noncomputable def hamL : (X × X →L[ℝ] ℝ) →L[ℝ] X × X :=
  ContinuousLinearMap.prod (rieszL (ContinuousLinearMap.inr ℝ X X))
    (-rieszL (ContinuousLinearMap.inl ℝ X X))

/-- `hamL` is `hamVec`. -/
theorem hamL_apply (ℓ : X × X →L[ℝ] ℝ) : hamL ℓ = hamVec ℓ := rfl

/-- The derivative of the function `y ↦ dH_y (X_G (y))`, which is the bracket `{g, h}`. -/
theorem hasFDerivAt_bracket (G H : X × X → ℝ) (hG : ContDiff ℝ 2 G) (hH : ContDiff ℝ 2 H) (x : X × X) :
    HasFDerivAt (fun y => fderiv ℝ H y (hamVec (fderiv ℝ G y)))
      ((fderiv ℝ H x).comp (hamL.comp (fderiv ℝ (fderiv ℝ G) x)) +
        (fderiv ℝ (fderiv ℝ H) x).flip (hamVec (fderiv ℝ G x))) x := by
  have hG' : DifferentiableAt ℝ (fderiv ℝ G) x :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have hH' : DifferentiableAt ℝ (fderiv ℝ H) x :=
    ((hH.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have hl : HasFDerivAt (⇑(hamL (X := X))) hamL (fderiv ℝ G x) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (hamL (X := X))
  have hu : HasFDerivAt (fun y => hamL (fderiv ℝ G y)) (hamL.comp (fderiv ℝ (fderiv ℝ G) x)) x :=
    HasFDerivAt.comp (𝕜 := ℝ) (g := ⇑(hamL (X := X))) (f := fderiv ℝ G) x hl hG'.hasFDerivAt
  exact hH'.hasFDerivAt.clm_apply hu

/-- The bracket of `f` with `{g, h}` in terms of second derivatives: `D²H (X_f, X_g) - D²G (X_f, X_h)`. -/
theorem poissonBracket_bracket (f g h : X → X → ℝ) (hf : ContDiff ℝ 2 (fun x : X × X => f x.1 x.2))
    (hg : ContDiff ℝ 2 (fun x : X × X => g x.1 x.2)) (hh : ContDiff ℝ 2 (fun x : X × X => h x.1 x.2))
    (x : X × X) :
    poissonBracket f (fun p q => poissonBracket g h p q) x.1 x.2 =
      fderiv ℝ (fderiv ℝ fun y : X × X => h y.1 y.2) x
        (hamVec (fderiv ℝ (fun y : X × X => f y.1 y.2) x))
        (hamVec (fderiv ℝ (fun y : X × X => g y.1 y.2) x)) -
      fderiv ℝ (fderiv ℝ fun y : X × X => g y.1 y.2) x
        (hamVec (fderiv ℝ (fun y : X × X => f y.1 y.2) x))
        (hamVec (fderiv ℝ (fun y : X × X => h y.1 y.2) x)) := by
  set F : X × X → ℝ := fun y => f y.1 y.2 with hF
  set G : X × X → ℝ := fun y => g y.1 y.2 with hG
  set H : X × X → ℝ := fun y => h y.1 y.2 with hH
  have hP : (fun y : X × X => poissonBracket g h y.1 y.2) =
      fun y => fderiv ℝ H y (hamVec (fderiv ℝ G y)) := by
    funext y
    exact poissonBracket_eq_hamVec g h y (hg.differentiable (by norm_num) y)
      (hh.differentiable (by norm_num) y)
  have hd := hasFDerivAt_bracket G H hg hh x
  rw [poissonBracket_eq_hamVec f (fun p q => poissonBracket g h p q) x
    (hf.differentiable (by norm_num) x) (by simp only [hP]; exact hd.differentiableAt)]
  simp only [hP]
  rw [hd.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    hamL_apply]
  rw [hamVec_antisymm (fderiv ℝ H x) (fderiv ℝ (fderiv ℝ G) x (hamVec (fderiv ℝ F x)))]
  ring

/-- **The Jacobi identity** for the Poisson bracket of `C²` phase-space functions. -/
theorem poissonBracket_jacobi (f g h : X → X → ℝ) (hf : ContDiff ℝ 2 (fun x : X × X => f x.1 x.2))
    (hg : ContDiff ℝ 2 (fun x : X × X => g x.1 x.2)) (hh : ContDiff ℝ 2 (fun x : X × X => h x.1 x.2))
    (p q : X) :
    poissonBracket f (fun p q => poissonBracket g h p q) p q +
      poissonBracket g (fun p q => poissonBracket h f p q) p q +
      poissonBracket h (fun p q => poissonBracket f g p q) p q = 0 := by
  have e1 := poissonBracket_bracket f g h hf hg hh (p, q)
  have e2 := poissonBracket_bracket g h f hg hh hf (p, q)
  have e3 := poissonBracket_bracket h f g hh hf hg (p, q)
  have sF := (hf.contDiffAt (x := (p, q))).isSymmSndFDerivAt (by simp)
  have sG := (hg.contDiffAt (x := (p, q))).isSymmSndFDerivAt (by simp)
  have sH := (hh.contDiffAt (x := (p, q))).isSymmSndFDerivAt (by simp)
  simp only [] at e1 e2 e3
  rw [e1, e2, e3]
  rw [sF (hamVec (fderiv ℝ (fun y : X × X => h y.1 y.2) (p, q)))
    (hamVec (fderiv ℝ (fun y : X × X => g y.1 y.2) (p, q)))]
  rw [sG (hamVec (fderiv ℝ (fun y : X × X => f y.1 y.2) (p, q)))
    (hamVec (fderiv ℝ (fun y : X × X => h y.1 y.2) (p, q)))]
  rw [sH (hamVec (fderiv ℝ (fun y : X × X => g y.1 y.2) (p, q)))
    (hamVec (fderiv ℝ (fun y : X × X => f y.1 y.2) (p, q)))]
  ring

end Lightlike.Gauge
