import Lightlike.Gauge.PoissonJacobi
import Lightlike.Gauge.MatrixInverse
import Lightlike.Gauge.DiracAlgebra

/-!
# The Jacobi identity for the Dirac bracket

For `C²` constraints `φ_a` whose bracket matrix `C_{ab} = {φ_a, φ_b}` is nonsingular everywhere and `C²`
observables `f, g, h`, `{f, {g, h}_D}_D + {g, {h, f}_D}_D + {h, {f, g}_D}_D = 0`
(`diracBracket_jacobi`), where `{f, g}_D = {f, g} - ∑ {f, φ_a} (C⁻¹)_{ab} {φ_b, g}`.

The derivative of `{g, h}_D` along the Hamiltonian vector field of `u` is written with the Leibniz rule, the
derivative of the inverse matrix `d (C⁻¹) = - C⁻¹ (dC) C⁻¹` (`Lightlike/Gauge/MatrixInverse.lean`) and the
derivation property `{u, K} = dK (X_u)` (`poissonBracket_eq_hamVec`), in terms of the triple brackets
`{u, {p, q}}` (`fderiv_dirac`). The cyclic sum of the result is shown to vanish by the Jacobi identity of the
Poisson bracket (`Lightlike/Gauge/PoissonJacobi.lean`), degree by degree in `C⁻¹`
(`Lightlike/Gauge/DiracAlgebra.lean`). Only second derivatives of the data are used: each triple bracket
differentiates a bracket of `C²` functions once.

## References

* M. Henneaux and C. Teitelboim, *Quantization of Gauge Systems*, Princeton University Press (1992), Chapter 1.
-/
open ClassicalMechanics InnerProductSpace Matrix
namespace Lightlike.Gauge
variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {m : ℕ}

/-- a phase-space function as a function on `X × X` -/
def tl (f : X → X → ℝ) : X × X → ℝ := fun y => f y.1 y.2

/-- The bracket of `C²` functions as a function on `X × X`: `{f, g} (y) = dg_y (X_f (y))`. -/
theorem tl_pb (f g : X → X → ℝ) (hf : ContDiff ℝ 2 (tl f)) (hg : ContDiff ℝ 2 (tl g)) :
    tl (fun p q => poissonBracket f g p q) = fun y => fderiv ℝ (tl g) y (hamVec (fderiv ℝ (tl f) y)) := by
  funext y
  exact poissonBracket_eq_hamVec f g y (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)

/-- The derivative of the bracket of two `C²` functions. -/
theorem hasFDerivAt_tl_pb (f g : X → X → ℝ) (hf : ContDiff ℝ 2 (tl f)) (hg : ContDiff ℝ 2 (tl g)) (x : X × X) :
    HasFDerivAt (tl (fun p q => poissonBracket f g p q))
      ((fderiv ℝ (tl g) x).comp (hamL.comp (fderiv ℝ (fderiv ℝ (tl f)) x)) +
        (fderiv ℝ (fderiv ℝ (tl g)) x).flip (hamVec (fderiv ℝ (tl f) x))) x := by
  rw [tl_pb f g hf hg]
  exact hasFDerivAt_bracket (tl f) (tl g) hf hg x

/-- The bracket of two `C²` functions is differentiable. -/
theorem differentiable_tl_pb (f g : X → X → ℝ) (hf : ContDiff ℝ 2 (tl f)) (hg : ContDiff ℝ 2 (tl g)) :
    Differentiable ℝ (tl (fun p q => poissonBracket f g p q)) := fun x =>
  (hasFDerivAt_tl_pb f g hf hg x).differentiableAt

/-- the derivative of a bracket function along the Hamiltonian vector of `u` is a triple bracket -/
theorem dir_eq (u : X → X → ℝ) (hu : ContDiff ℝ 2 (tl u)) (K : X × X → ℝ) (x : X × X)
    (hK : DifferentiableAt ℝ K x) :
    poissonBracket u (fun p q => K (p, q)) x.1 x.2 = fderiv ℝ K x (hamVec (fderiv ℝ (tl u) x)) :=
  poissonBracket_eq_hamVec u (fun p q => K (p, q)) x (hu.differentiable (by norm_num) x) hK

/-- The derivative of a sum of triple products along a vector (Leibniz rule). -/
theorem fderiv_quad {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : E → ℝ)
    (Pv Pw : Fin m → E → ℝ) (Ci : Fin m → Fin m → E → ℝ) (x V : E)
    (hA : DifferentiableAt ℝ A x) (hPv : ∀ a, DifferentiableAt ℝ (Pv a) x)
    (hPw : ∀ a, DifferentiableAt ℝ (Pw a) x) (hCi : ∀ a b, DifferentiableAt ℝ (Ci a b) x) :
    fderiv ℝ (fun y => A y + ∑ a, ∑ b, Pv a y * Ci a b y * Pw b y) x V =
      fderiv ℝ A x V + ∑ a, ∑ b, (fderiv ℝ (Pv a) x V * Ci a b x * Pw b x +
        Pv a x * fderiv ℝ (Ci a b) x V * Pw b x + Pv a x * Ci a b x * fderiv ℝ (Pw b) x V) := by
  have hs : HasFDerivAt (fun y => A y + ∑ a, ∑ b, Pv a y * Ci a b y * Pw b y) _ x :=
    hA.hasFDerivAt.add (HasFDerivAt.fun_sum (u := Finset.univ) fun a _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) fun b _ =>
        (((hPv a).hasFDerivAt.mul (hCi a b).hasFDerivAt).mul (hPw b).hasFDerivAt))
  rw [hs.fderiv]
  simp only [_root_.add_apply, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, Pi.mul_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

section Dirac

variable (φ : Fin m → X → X → ℝ) (ob : Fin 3 → X → X → ℝ)

/-- The three observables followed by the `m` constraints. -/
def allObs : Fin 3 ⊕ Fin m → X → X → ℝ := Sum.elim ob φ

/-- The triple bracket `{i, {p, q}}` at a point. -/
noncomputable def Tt (x : X × X) (i p q : Fin 3 ⊕ Fin m) : ℝ :=
  poissonBracket (allObs φ ob i)
    (fun p' q' => poissonBracket (allObs φ ob p) (allObs φ ob q) p' q') x.1 x.2

/-- The Dirac bracket as a function of the point: `{v, w} + ∑ {v, φ_a} (C⁻¹)_{ab} {w, φ_b}`. -/
theorem dirac_expand (v w : Fin 3) :
    tl (fun p q => diracBracket φ (ob v) (ob w) p q) = fun y =>
      tl (fun p q => poissonBracket (ob v) (ob w) p q) y +
        ∑ a, ∑ b, tl (fun p q => poissonBracket (ob v) (φ a) p q) y *
          (bracketMatrix φ y.1 y.2)⁻¹ a b * tl (fun p q => poissonBracket (ob w) (φ b) p q) y := by
  funext y
  simp only [tl, diracBracket]
  have h : ∀ b, poissonBracket (φ b) (ob w) y.1 y.2 = -poissonBracket (ob w) (φ b) y.1 y.2 :=
    fun b => poissonBracket_antisymm (φ b) (ob w) y.1 y.2
  simp only [h, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- The derivative of `{v, w}_D` along the Hamiltonian vector of `u`, in terms of triple brackets. -/
theorem fderiv_dirac (hφ : ∀ a, ContDiff ℝ 2 (tl (φ a))) (ho : ∀ u, ContDiff ℝ 2 (tl (ob u)))
    (hdet : ∀ p q, (bracketMatrix φ p q).det ≠ 0) (x : X × X) (i : Fin 3 ⊕ Fin m) (v w : Fin 3) :
    fderiv ℝ (tl (fun p q => diracBracket φ (ob v) (ob w) p q)) x
        (hamVec (fderiv ℝ (tl (allObs φ ob i)) x)) =
      Dd (fun a b => (bracketMatrix φ x.1 x.2)⁻¹ a b)
        (fun u a => poissonBracket (ob u) (φ a) x.1 x.2) (Tt φ ob x) i v w := by
  have hAll : ContDiff ℝ 2 (tl (allObs φ ob i)) := by
    rcases i with u | a
    · exact ho u
    · exact hφ a
  set V := hamVec (fderiv ℝ (tl (allObs φ ob i)) x) with hV
  have hM : ∀ a b, Differentiable ℝ (fun y : X × X => bracketMatrix φ y.1 y.2 a b) :=
    fun a b => differentiable_tl_pb (φ a) (φ b) (hφ a) (hφ b)
  have hCi : ∀ a b, DifferentiableAt ℝ (fun y : X × X => (bracketMatrix φ y.1 y.2)⁻¹ a b) x :=
    fun a b => differentiableAt_inv_entry (fun y : X × X => bracketMatrix φ y.1 y.2)
      (fun i j => hM i j x) (hdet x.1 x.2) a b
  rw [dirac_expand, fderiv_quad _ _ _ _ x V
    (differentiable_tl_pb (ob v) (ob w) (ho v) (ho w) x)
    (fun a => differentiable_tl_pb (ob v) (φ a) (ho v) (hφ a) x)
    (fun b => differentiable_tl_pb (ob w) (φ b) (ho w) (hφ b) x) hCi]
  have d1 : fderiv ℝ (tl (fun p q => poissonBracket (ob v) (ob w) p q)) x V =
      Tt φ ob x i (.inl v) (.inl w) :=
    (dir_eq (allObs φ ob i) hAll _ x (differentiable_tl_pb (ob v) (ob w) (ho v) (ho w) x)).symm
  have d2 : ∀ (u : Fin 3) (a : Fin m), fderiv ℝ (tl (fun p q => poissonBracket (ob u) (φ a) p q)) x V =
      Tt φ ob x i (.inl u) (.inr a) := fun u a =>
    (dir_eq (allObs φ ob i) hAll _ x (differentiable_tl_pb (ob u) (φ a) (ho u) (hφ a) x)).symm
  have dM : ∀ c b : Fin m, fderiv ℝ (fun y : X × X => bracketMatrix φ y.1 y.2 c b) x V =
      Tt φ ob x i (.inr c) (.inr b) := fun c b =>
    (dir_eq (allObs φ ob i) hAll _ x (hM c b x)).symm
  have d3 : ∀ a b : Fin m, fderiv ℝ (fun y : X × X => (bracketMatrix φ y.1 y.2)⁻¹ a b) x V =
      -∑ b', ∑ c, (bracketMatrix φ x.1 x.2)⁻¹ a c * Tt φ ob x i (.inr c) (.inr b') *
        (bracketMatrix φ x.1 x.2)⁻¹ b' b := by
    intro a b
    rw [fderiv_inv_entry (fun y : X × X => bracketMatrix φ y.1 y.2) hM (fun y => hdet y.1 y.2) x V a b]
    simp only [dM]
  simp only [d1, d2, d3]
  unfold Dd
  simp only [tl]
  set c : Fin m → Fin m → ℝ := fun a b => (bracketMatrix φ x.1 x.2)⁻¹ a b with hc
  set P : Fin 3 → Fin m → ℝ := fun u a => poissonBracket (ob u) (φ a) x.1 x.2 with hP
  have hB : (∑ a, ∑ b, P v a * (-∑ b', ∑ c', c a c' * Tt φ ob x i (.inr c') (.inr b') * c b' b) * P w b) =
      -(∑ a, ∑ c', ∑ d, ∑ b, P v a * c a c' * Tt φ ob x i (.inr c') (.inr d) * c d b * P w b) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : ∀ b, P v a * (-∑ b', ∑ c', c a c' * Tt φ ob x i (.inr c') (.inr b') * c b' b) * P w b =
        -∑ b', ∑ c', P v a * c a c' * Tt φ ob x i (.inr c') (.inr b') * c b' b * P w b := by
      intro b
      rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c' _ => by ring
    simp only [h1, Finset.sum_neg_distrib]
    congr 1
    calc ∑ b, ∑ b', ∑ c', P v a * c a c' * Tt φ ob x i (.inr c') (.inr b') * c b' b * P w b
        = ∑ b, ∑ c', ∑ b', P v a * c a c' * Tt φ ob x i (.inr c') (.inr b') * c b' b * P w b :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ c', ∑ b, ∑ b', P v a * c a c' * Tt φ ob x i (.inr c') (.inr b') * c b' b * P w b :=
          Finset.sum_comm
      _ = ∑ c', ∑ b', ∑ b, P v a * c a c' * Tt φ ob x i (.inr c') (.inr b') * c b' b * P w b :=
          Finset.sum_congr rfl fun c' _ => Finset.sum_comm
  have hA : (∑ a, ∑ b, Tt φ ob x i (.inl v) (.inr a) * c a b * P w b) =
      ∑ a, Tt φ ob x i (.inl v) (.inr a) * ∑ b, c a b * P w b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp only [Finset.sum_add_distrib]
  rw [hB, hA]
  ring

/-- The inverse of the bracket matrix is antisymmetric. -/
theorem inv_bracketMatrix_antisymm (p q : X) (a b : Fin m) :
    (bracketMatrix φ p q)⁻¹ a b = -(bracketMatrix φ p q)⁻¹ b a := by
  have hT : ((bracketMatrix φ p q)⁻¹)ᵀ = -(bracketMatrix φ p q)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, bracketMatrix_transpose]
    by_cases hu : IsUnit (bracketMatrix φ p q).det
    · have h1 : (bracketMatrix φ p q) * (bracketMatrix φ p q)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
      refine Matrix.inv_eq_right_inv ?_
      rw [neg_mul_neg, h1]
    · have hu' : ¬ IsUnit (-bracketMatrix φ p q).det := by
        rw [Matrix.det_neg]
        intro h
        exact hu (by simpa using (IsUnit.mul_iff.mp h).2)
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.nonsing_inv_apply_not_isUnit _ hu']
      simp
  have := congrFun (congrFun hT b) a
  simpa using this

/-- The triple bracket is antisymmetric in its last two arguments. -/
theorem Tt_antisymm (hφ : ∀ a, ContDiff ℝ 2 (tl (φ a))) (ho : ∀ u, ContDiff ℝ 2 (tl (ob u)))
    (x : X × X) (i p q : Fin 3 ⊕ Fin m) : Tt φ ob x i p q = -Tt φ ob x i q p := by
  have hAll : ∀ j, ContDiff ℝ 2 (tl (allObs φ ob j)) := by
    intro j
    rcases j with u | a
    · exact ho u
    · exact hφ a
  have hfun : tl (fun p' q' => poissonBracket (allObs φ ob p) (allObs φ ob q) p' q') =
      -tl (fun p' q' => poissonBracket (allObs φ ob q) (allObs φ ob p) p' q') := by
    funext y
    exact poissonBracket_antisymm _ _ y.1 y.2
  have h1 : Tt φ ob x i p q = fderiv ℝ (tl (fun p' q' => poissonBracket (allObs φ ob p) (allObs φ ob q) p' q'))
      x (hamVec (fderiv ℝ (tl (allObs φ ob i)) x)) :=
    dir_eq (allObs φ ob i) (hAll i) _ x (differentiable_tl_pb _ _ (hAll p) (hAll q) x)
  have h2 : Tt φ ob x i q p = fderiv ℝ (tl (fun p' q' => poissonBracket (allObs φ ob q) (allObs φ ob p) p' q'))
      x (hamVec (fderiv ℝ (tl (allObs φ ob i)) x)) :=
    dir_eq (allObs φ ob i) (hAll i) _ x (differentiable_tl_pb _ _ (hAll q) (hAll p) x)
  rw [h1, h2, hfun, fderiv_neg]
  simp

/-- The triple bracket satisfies the Jacobi identity. -/
theorem Tt_jacobi (hφ : ∀ a, ContDiff ℝ 2 (tl (φ a))) (ho : ∀ u, ContDiff ℝ 2 (tl (ob u)))
    (x : X × X) (i p q : Fin 3 ⊕ Fin m) :
    Tt φ ob x i p q + Tt φ ob x p q i + Tt φ ob x q i p = 0 := by
  have hAll : ∀ j, ContDiff ℝ 2 (tl (allObs φ ob j)) := by
    intro j
    rcases j with u | a
    · exact ho u
    · exact hφ a
  exact poissonBracket_jacobi _ _ _ (hAll i) (hAll p) (hAll q) x.1 x.2

/-- `{u, {v, w}_D}_D` in terms of the triple brackets. -/
theorem dirac_eq_Jac (hφ : ∀ a, ContDiff ℝ 2 (tl (φ a))) (ho : ∀ u, ContDiff ℝ 2 (tl (ob u)))
    (hdet : ∀ p q, (bracketMatrix φ p q).det ≠ 0) (x : X × X) (u v w : Fin 3) :
    diracBracket φ (ob u) (fun p q => diracBracket φ (ob v) (ob w) p q) x.1 x.2 =
      Jac (fun a b => (bracketMatrix φ x.1 x.2)⁻¹ a b)
        (fun u a => poissonBracket (ob u) (φ a) x.1 x.2) (Tt φ ob x) u v w := by
  have hK : DifferentiableAt ℝ (tl (fun p q => diracBracket φ (ob v) (ob w) p q)) x := by
    have hM : ∀ a b, Differentiable ℝ (fun y : X × X => bracketMatrix φ y.1 y.2 a b) :=
      fun a b => differentiable_tl_pb (φ a) (φ b) (hφ a) (hφ b)
    have hCi : ∀ a b, DifferentiableAt ℝ (fun y : X × X => (bracketMatrix φ y.1 y.2)⁻¹ a b) x :=
      fun a b => differentiableAt_inv_entry (fun y : X × X => bracketMatrix φ y.1 y.2)
        (fun i j => hM i j x) (hdet x.1 x.2) a b
    rw [dirac_expand]
    exact (differentiable_tl_pb (ob v) (ob w) (ho v) (ho w) x).add
      (DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
        (((differentiable_tl_pb (ob v) (φ a) (ho v) (hφ a) x).mul (hCi a b)).mul
          (differentiable_tl_pb (ob w) (φ b) (ho w) (hφ b) x)))
  have key : ∀ i : Fin 3 ⊕ Fin m,
      poissonBracket (allObs φ ob i) (fun p q => diracBracket φ (ob v) (ob w) p q) x.1 x.2 =
      Dd (fun a b => (bracketMatrix φ x.1 x.2)⁻¹ a b)
        (fun u a => poissonBracket (ob u) (φ a) x.1 x.2) (Tt φ ob x) i v w := by
    intro i
    have hAll : ContDiff ℝ 2 (tl (allObs φ ob i)) := by
      rcases i with u | a
      · exact ho u
      · exact hφ a
    rw [← fderiv_dirac φ ob hφ ho hdet x i v w]
    exact dir_eq (allObs φ ob i) hAll _ x hK
  have k1 := key (.inl u)
  have k2 := fun b => key (.inr b)
  simp only [allObs, Sum.elim_inl, Sum.elim_inr] at k1 k2
  rw [show diracBracket φ (ob u) (fun p q => diracBracket φ (ob v) (ob w) p q) x.1 x.2 =
    poissonBracket (ob u) (fun p q => diracBracket φ (ob v) (ob w) p q) x.1 x.2 -
      ∑ a, ∑ b, poissonBracket (ob u) (φ a) x.1 x.2 * (bracketMatrix φ x.1 x.2)⁻¹ a b *
        poissonBracket (φ b) (fun p q => diracBracket φ (ob v) (ob w) p q) x.1 x.2 from rfl]
  unfold Jac
  rw [k1]
  simp only [k2]

end Dirac

/-- **The Jacobi identity for the Dirac bracket** of `C²` functions, for `C²` constraints whose bracket matrix
is nonsingular everywhere. -/
theorem diracBracket_jacobi {m : ℕ} (φ : Fin m → X → X → ℝ) (hφ : ∀ a, ContDiff ℝ 2 (tl (φ a)))
    (hC : ∀ p q, (bracketMatrix φ p q).det ≠ 0)
    (f g h : X → X → ℝ) (hf : ContDiff ℝ 2 (tl f)) (hg : ContDiff ℝ 2 (tl g)) (hh : ContDiff ℝ 2 (tl h))
    (p q : X) :
    diracBracket φ f (fun p q => diracBracket φ g h p q) p q +
      diracBracket φ g (fun p q => diracBracket φ h f p q) p q +
      diracBracket φ h (fun p q => diracBracket φ f g p q) p q = 0 := by
  let ob : Fin 3 → X → X → ℝ := ![f, g, h]
  have ho : ∀ u, ContDiff ℝ 2 (tl (ob u)) := by
    intro u
    fin_cases u
    · exact hf
    · exact hg
    · exact hh
  have e1 := dirac_eq_Jac φ ob hφ ho hC (p, q) 0 1 2
  have e2 := dirac_eq_Jac φ ob hφ ho hC (p, q) 1 2 0
  have e3 := dirac_eq_Jac φ ob hφ ho hC (p, q) 2 0 1
  have hcyc := Jac_cyc (fun a b => (bracketMatrix φ p q)⁻¹ a b)
    (fun a b => inv_bracketMatrix_antisymm φ p q a b)
    (fun u a => poissonBracket (ob u) (φ a) p q) (Tt φ ob (p, q)) (Tt_antisymm φ ob hφ ho (p, q))
    (Tt_jacobi φ ob hφ ho (p, q)) 0 1 2
  simp only [ob] at e1 e2 e3
  simp at e1 e2 e3
  rw [e1, e2, e3]
  exact hcyc

end Lightlike.Gauge
