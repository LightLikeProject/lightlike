import Mathlib
import Lightlike.Dirac.RicciIdentity
import Lightlike.Dirac.LichnerowiczFormula

/-!
# The Lichnerowicz formula in a general frame

For a frame field `F x a` (not necessarily constant) and skew connection matrices `ω x a`, the Dirac
operator is `D f = ∑ₐ γₐ ∇ₐ f` with `∇ₐ f = ∂_{Fₐ} f + spinForm (ωₐ) f` (`nablaF`).  Clifford
multiplication is parallel up to the vector-index connection, which gives
`D² f = ∑ₐ∑_b γₐγ_b ∇²f(Fₐ,F_b)` for the frame Hessian `hessF` (the term coming from `∂F` is
exactly the one subtracted in `hessF`).  Splitting into symmetric and antisymmetric parts and using
the Ricci identity `ricci_identity` (which *derives* what `lichnerowicz_frame` assumed) gives

`D² f = -∑ₐ ∇²f(Fₐ,Fₐ) + (s/4) f`,   `s = ∑ₐ_b R_{ab,ba}`,

where `R = curvF` is the structure-equation curvature, provided `R` has the Riemann pair and
Bianchi symmetries (hypotheses `hP`, `hB`; antisymmetry in the first pair is proved from the
torsion-free relation).

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The Dirac operator `D f = ∑ₐ γₐ ∇ₐ f` in a general frame. -/
noncomputable def diracF (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) (f : E n → V) : E n → V :=
  fun x => ∑ i, gam ρ i (nablaF ρ F ω i f x)

/-- Clifford multiplication is parallel up to the vector-index connection (general frame):
`∇ᵢ (γₖ g) = γₖ ∇ᵢ g + ∑ⱼ (ωᵢ)ₖⱼ γⱼ g`, for `ω x i` skew. -/
theorem nablaF_gam (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {x : E n}
    (hω : ∀ i a b, ω x i a b = -ω x i b a) (i k : Fin n) {g : E n → V}
    (hg : DifferentiableAt ℝ g x) :
    nablaF ρ F ω i (fun y => gam ρ k (g y)) x =
      gam ρ k (nablaF ρ F ω i g x) + ∑ j, (ω x i k j) • gam ρ j (g x) := by
  have hd : fderiv ℝ (fun y => gam ρ k (g y)) x (F x i) = gam ρ k (fderiv ℝ g x (F x i)) := by
    rw [show (fun y => gam ρ k (g y)) = gam ρ k ∘ g from rfl,
      ((gam ρ k).hasFDerivAt.comp x hg.hasFDerivAt).fderiv]
    rfl
  have hc := congrArg (fun L => L (g x)) (spinForm_comm ρ (hω i) k)
  simp only [sub_apply, mul_apply_eq_comp, sum_apply, smul_apply] at hc
  unfold nablaF
  rw [hd, map_add, ← hc]
  abel

/-- `∇ᵢ` commutes with finite sums of functions differentiable at `x`. -/
theorem nablaF_sum (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) {ι : Type*} (s : Finset ι) (g : ι → E n → V) (x : E n)
    (hg : ∀ j ∈ s, DifferentiableAt ℝ (g j) x) :
    nablaF ρ F ω i (fun y => ∑ j ∈ s, g j y) x = ∑ j ∈ s, nablaF ρ F ω i (g j) x := by
  have hd : fderiv ℝ (fun y => ∑ j ∈ s, g j y) x = ∑ j ∈ s, fderiv ℝ (g j) x := by
    exact (HasFDerivAt.fun_sum (fun j hj => (hg j hj).hasFDerivAt)).fderiv
  unfold nablaF
  rw [hd, sum_apply, map_sum, Finset.sum_add_distrib]

/-- `D² f = ∑ₐ_b γₐγ_b aₐb` with the frame Hessian `aₐb = ∇ₐ∇_b f − ∑ₖ (ωₐ)_bk ∇ₖ f`. -/
theorem diracF_diracF_hessian (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {x : E n}
    (hω : ∀ i a b, ω x i a b = -ω x i b a) {f : E n → V}
    (hf : ∀ j, DifferentiableAt ℝ (fun y => nablaF ρ F ω j f y) x) :
    diracF ρ F ω (diracF ρ F ω f) x =
      ∑ i, ∑ j, gam ρ i (gam ρ j (hessF ρ F ω f x i j)) := by
  have h1 : ∀ i, nablaF ρ F ω i (fun y => ∑ j, gam ρ j (nablaF ρ F ω j f y)) x =
      ∑ j, (gam ρ j (nablaF ρ F ω i (fun y => nablaF ρ F ω j f y) x) +
        ∑ k, (ω x i j k) • gam ρ k (nablaF ρ F ω j f x)) := by
    intro i
    rw [nablaF_sum ρ F ω i Finset.univ (fun j y => gam ρ j (nablaF ρ F ω j f y)) x
      (fun j _ => (gam ρ j).differentiableAt.comp x (hf j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact nablaF_gam ρ F ω hω i j (hf j)
  have h0 : diracF ρ F ω (diracF ρ F ω f) x =
      ∑ i, ∑ j, gam ρ i (gam ρ j (nablaF ρ F ω i (fun y => nablaF ρ F ω j f y) x)) +
      ∑ i, ∑ j, ∑ k, (ω x i j k) • gam ρ i (gam ρ k (nablaF ρ F ω j f x)) := by
    unfold diracF
    simp only [h1, map_sum, map_add, Finset.sum_add_distrib, map_smul]
  rw [h0]
  have h2 : ∑ i, ∑ j, ∑ k, (ω x i j k) • gam ρ i (gam ρ k (nablaF ρ F ω j f x)) =
      ∑ i, ∑ j, ∑ k, (ω x i k j) • gam ρ i (gam ρ j (nablaF ρ F ω k f x)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hessF, map_sub, map_sum, map_smul, hω i _ j, neg_smul, Finset.sum_neg_distrib]
  abel

/-- `D² f = -∑ₐ aₐₐ + ½ ∑ₐ_b γₐγ_b (aₐb - a_bₐ)` for the frame Hessian `a = hessF`. -/
theorem diracF_diracF_antisymm (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {x : E n}
    (hω : ∀ i a b, ω x i a b = -ω x i b a) {f : E n → V}
    (hf : ∀ j, DifferentiableAt ℝ (fun y => nablaF ρ F ω j f y) x) :
    diracF ρ F ω (diracF ρ F ω f) x =
      -∑ i, hessF ρ F ω f x i i +
      (1 / 2 : ℝ) • ∑ i, ∑ j, gam ρ i (gam ρ j
        (hessF ρ F ω f x i j - hessF ρ F ω f x j i)) := by
  rw [diracF_diracF_hessian ρ F ω hω hf]
  exact clifford_double_sum ρ (fun i j => hessF ρ F ω f x i j)

/-- The structure-equation curvature `curvF` is antisymmetric in the first pair, given the
torsion-free relation (which makes the structure functions antisymmetric). -/
lemma curvF_antisymm (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) (x : E n)
    (cs : Fin n → Fin n → Fin n → ℝ)
    (htors : ∀ a b c, ω x a b c - ω x b a c = cs a b c) (a b k l : Fin n) :
    curvF F ω cs x a b k l = - curvF F ω cs x b a k l := by
  have hcs : ∀ c, cs a b c = - cs b a c := fun c => by
    rw [← htors a b c, ← htors b a c]; ring
  simp only [curvF, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, hcs, neg_mul, Finset.sum_neg_distrib]
  simp only [omegaD]
  ring

/-- **Lichnerowicz formula in a general frame.**  For a `C²` spinor field `f`, a torsion-free
skew frame connection (`ω`, structure functions `cs`) whose curvature `curvF` has the Riemann
pair and first Bianchi symmetries, `D² f = -∑ₐ ∇²f(Fₐ,Fₐ) + (s/4) f` with
`s = ∑ₐ_b R_{ab,ba}`. -/
theorem lichnerowicz_general (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {f : E n → V} {x : E n}
    (hf2 : ContDiffAt ℝ 2 f x) (hF : ∀ a, DifferentiableAt ℝ (fun y => F y a) x)
    (hω : ∀ a k l, DifferentiableAt ℝ (fun y => ω y a k l) x)
    (hnf : ∀ j, DifferentiableAt ℝ (fun y => nablaF ρ F ω j f y) x)
    (hskew : ∀ a k l, ω x a k l = - ω x a l k) (cs : Fin n → Fin n → Fin n → ℝ)
    (hbr : ∀ a b, fderiv ℝ (fun y => F y b) x (F x a) - fderiv ℝ (fun y => F y a) x (F x b) =
      ∑ c, cs a b c • F x c)
    (htors : ∀ a b c, ω x a b c - ω x b a c = cs a b c)
    (hP : ∀ i j k l, curvF F ω cs x i j k l = curvF F ω cs x k l i j)
    (hB : ∀ i j k l, curvF F ω cs x i j k l + curvF F ω cs x j k i l +
      curvF F ω cs x k i j l = 0) :
    diracF ρ F ω (diracF ρ F ω f) x =
      -∑ i, hessF ρ F ω f x i i +
      ((1 / 4 : ℝ) * ∑ i, ∑ j, curvF F ω cs x i j j i) • f x := by
  rw [diracF_diracF_antisymm ρ F ω hskew hnf]
  have hr : ∀ i j, hessF ρ F ω f x i j - hessF ρ F ω f x j i =
      spinorCurvature (gam ρ) (fun a b k l => curvF F ω cs x a b k l) i j (f x) :=
    fun i j => ricci_identity ρ F ω hf2 hF hω hskew cs hbr htors i j
  simp only [hr]
  have h := congrArg (fun L => L (f x))
    (curvatureTerm_eq (gam ρ) (fun a b k l => curvF F ω cs x a b k l) (gam_relations ρ)
      (curvF_antisymm F ω x cs htors) hP hB)
  simp only [curvatureTerm, smul_apply, sum_apply, mul_apply_eq_comp, one_apply_eq_self] at h
  rw [← h]

end Lightlike.Dirac
