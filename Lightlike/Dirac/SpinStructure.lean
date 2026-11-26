import Mathlib
import Lightlike.Dirac.Flat
import Lightlike.Spacetime.Lorentzian

/-!
# Spin lifts of frame changes

A spin structure on a Riemannian manifold lifts every change of orthonormal frame, a rotation
`R ∈ SO(n)`, to an element of the spin group `Spin(n) ⊂ Cl(ℝⁿ, -‖·‖²)` acting on vectors by
conjugation, so that the lifts compose on triple overlaps.  This file fixes the algebraic part:
`IsSpinLift R s` says that `s` lies in Mathlib's `spinGroup` and conjugates the basis vector `eₐ` to
the vector with coordinates `R a ·`.  It is stated in the Clifford algebra itself, with no choice
of preimage under `ι`, so that no injectivity of `ι` is needed.

Lifts compose: if `s` lifts `R` and `t` lifts `R'` then `s * t` lifts `R' * R`
(`IsSpinLift.mul`), the algebraic content of the cocycle condition.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter II, §1 (spin groups) and §1
  (spin structures, Definition 1.3); no equation number is claimed.
-/

open CliffordAlgebra

namespace Lightlike.Dirac

variable {n : ℕ}

/-- `s` is a **spin lift** of the frame change `R`: `s` is in `Spin(n)` (Mathlib's `spinGroup` of
the form `Qneg n`) and conjugation by `s` sends the basis vector `eₐ` to `∑ᵦ R a b eᵦ`. -/
def IsSpinLift (R : Matrix (Fin n) (Fin n) ℝ) (s : CliffordAlgebra (Qneg n)) : Prop :=
  s ∈ spinGroup (Qneg n) ∧
    ∀ a, s * ι (Qneg n) (e a) * star s = ι (Qneg n) (∑ b, R a b • e b)

/-- The identity lifts the identity frame change. -/
theorem isSpinLift_one : IsSpinLift (1 : Matrix (Fin n) (Fin n) ℝ) 1 := by
  refine ⟨(spinGroup (Qneg n)).one_mem, fun a => ?_⟩
  simp [Matrix.one_apply, Finset.sum_ite_eq]

/-- Spin lifts compose: `s` lifts `R`, `t` lifts `R'`, then `s * t` lifts `R' * R`. -/
theorem IsSpinLift.mul {R R' : Matrix (Fin n) (Fin n) ℝ} {s t : CliffordAlgebra (Qneg n)}
    (hs : IsSpinLift R s) (ht : IsSpinLift R' t) : IsSpinLift (R' * R) (s * t) := by
  refine ⟨(spinGroup (Qneg n)).mul_mem hs.1 ht.1, fun a => ?_⟩
  have h1 : s * t * ι (Qneg n) (e a) * star (s * t) =
      s * (t * ι (Qneg n) (e a) * star t) * star s := by
    rw [star_mul]; noncomm_ring
  rw [h1, ht.2 a]
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  simp only [hs.2, map_sum, map_smul, Matrix.mul_apply, Finset.sum_smul]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

/-- A **spin cocycle** over a set of points `X` with the index set `ι` of a cover: on each overlap
`dom i ∩ dom j` the change from the frame `i` to the frame `j` is a matrix `Rot i j x` with a
chosen spin lift `lift i j x`, and both satisfy the cocycle condition on triple overlaps.  This is
the transition data of a spin structure; the bundle of frames it lives on is a separate layer. -/
structure SpinCocycle (n : ℕ) (X ι : Type*) where
  /-- The domain of the frame `i`. -/
  dom : ι → Set X
  /-- The change of frame from `i` to `j` at `x`. -/
  Rot : ι → ι → X → Matrix (Fin n) (Fin n) ℝ
  /-- Its chosen lift to `Spin(n)`. -/
  lift : ι → ι → X → CliffordAlgebra (Qneg n)
  isLift : ∀ i j x, x ∈ dom i → x ∈ dom j → IsSpinLift (Rot i j x) (lift i j x)
  rot_cocycle : ∀ i j k x, x ∈ dom i → x ∈ dom j → x ∈ dom k →
    Rot i k x = Rot j k x * Rot i j x
  lift_cocycle : ∀ i j k x, x ∈ dom i → x ∈ dom j → x ∈ dom k →
    lift i k x = lift i j x * lift j k x

/-- The trivial cocycle of a single frame: every change is the identity, lifted by `1`.  It shows
that `SpinCocycle` is satisfiable (the spin structure of a parallelizable manifold with a global
frame). -/
noncomputable def SpinCocycle.trivial (n : ℕ) (X : Type*) : SpinCocycle n X Unit where
  dom _ := Set.univ
  Rot _ _ _ := 1
  lift _ _ _ := 1
  isLift _ _ _ _ _ := isSpinLift_one
  rot_cocycle _ _ _ _ _ _ _ := by simp
  lift_cocycle _ _ _ _ _ _ _ := by simp

/-- On a triple overlap the lift of `i → k` is the product of the lifts, so it lifts the composed
rotation: the cocycle condition is consistent with `IsSpinLift.mul`. -/
theorem SpinCocycle.isLift_comp {X ι : Type*} (c : SpinCocycle n X ι) {i j k : ι} {x : X}
    (hi : x ∈ c.dom i) (hj : x ∈ c.dom j) (hk : x ∈ c.dom k) :
    IsSpinLift (c.Rot j k x * c.Rot i j x) (c.lift i j x * c.lift j k x) :=
  (c.isLift i j x hi hj).mul (c.isLift j k x hj hk)

section Manifold

open Bundle Manifold
open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- A **spin structure** on `M` for the metric `g`: a family of local orthonormal frames, with open
domains covering `M` and smooth on them, whose frame changes `Rot` (defined by
`F j a = ∑ b, Rot i j x a b • F i b`) carry lifts to `Spin(n)` satisfying the cocycle condition
(`SpinCocycle`).  The metric is positive definite because it has an orthonormal frame at every
point; the lifts exist only for frame changes in `SO(n)`, so `M` is oriented as well.  This is the
atlas form of the definition of Lawson–Michelsohn, *Spin Geometry*, II Def. 1.3, in place of
the principal `Spin(n)`-bundle double covering the frame bundle (a representation difference):
atlas form; equivalence with the principal `Spin(n)`-bundle definition not proved.  The frames are
smooth sections of the tangent bundle and the lifts are smooth maps into the Clifford algebra
(every linear coordinate of `lift i j` is smooth on the overlap). -/
structure SpinStructure (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (ι : Type*) extends
    SpinCocycle n M ι where
  /-- The local frame `i`. -/
  frame : ι → Fin n → Π x : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) x
  dom_open : ∀ i, IsOpen (dom i)
  dom_cover : ∀ x : M, ∃ i, x ∈ dom i
  frame_smooth : ∀ i a, ∀ x ∈ dom i,
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun y => (⟨y, frame i a y⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x
  lift_smooth : ∀ i j (φ : Module.Dual ℝ (CliffordAlgebra (Qneg n))) x, x ∈ dom i → x ∈ dom j →
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ (fun y => φ (lift i j y)) x
  frame_orthonormal : ∀ i a b x, x ∈ dom i →
    g.g x (frame i a x) (frame i b x) = if a = b then 1 else 0
  frame_change : ∀ i j x, x ∈ dom i → x ∈ dom j → ∀ a,
    frame j a x = ∑ b, Rot i j x a b • frame i b x

/-- The Euclidean bilinear form `v · w = ∑ᵢ vⁱ wⁱ` on `ℝⁿ`, as a continuous bilinear map. -/
noncomputable def euclideanForm (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)

@[simp] lemma euclideanForm_apply (v w : Fin n → ℝ) :
    euclideanForm n v w = ∑ i, v i * w i := by
  simp [euclideanForm, _root_.sum_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The flat Euclidean metric on `ℝⁿ`: the standard inner product on every tangent space.  Smooth
for the same reason as `Lightlike.minkowskiMetric`. -/
noncomputable def euclideanMetric (n : ℕ) : NondegMetric 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ) where
  g _ := euclideanForm n
  symm _ v w := by
    change euclideanForm n (v : Fin n → ℝ) w = euclideanForm n (w : Fin n → ℝ) v
    simp [mul_comm]
  nondegenerate _ v h := by
    funext i
    have := h (Pi.single i 1 : Fin n → ℝ)
    change euclideanForm n (v : Fin n → ℝ) (Pi.single i 1 : Fin n → ℝ) = 0 at this
    have h2 : (v : Fin n → ℝ) i = 0 := by simpa [Pi.single_apply] using this
    exact h2
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := euclideanForm n)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

/-- The standard global frame of `ℝⁿ` is a spin structure for the Euclidean metric, with the
trivial cocycle: `SpinStructure` is satisfiable (non-vacuity). -/
noncomputable def euclideanSpinStructure (n : ℕ) : SpinStructure (euclideanMetric n) Unit where
  toSpinCocycle := SpinCocycle.trivial n (Fin n → ℝ)
  frame _ a _ := Pi.single a 1
  dom_open _ := isOpen_univ
  dom_cover x := ⟨(), trivial⟩
  frame_smooth _ a x _ := by
    refine (contMDiffAt_section (IB := 𝓘(ℝ, Fin n → ℝ)) (F := Fin n → ℝ)
      (E := fun y : Fin n → ℝ => TangentSpace 𝓘(ℝ, Fin n → ℝ) y)
      (s := fun y => (Pi.single a 1 : TangentSpace 𝓘(ℝ, Fin n → ℝ) y)) x).2 ?_
    have h : (fun b : Fin n → ℝ => (trivializationAt (Fin n → ℝ)
        (fun y : Fin n → ℝ => TangentSpace 𝓘(ℝ, Fin n → ℝ) y) x
          (⟨b, (Pi.single a 1 : TangentSpace 𝓘(ℝ, Fin n → ℝ) b)⟩ :
            TangentBundle 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ))).2) = fun _ => Pi.single a 1 := by
      funext b
      simp
    rw [h]
    exact contMDiffAt_const
  lift_smooth _ _ _ _ _ _ := contMDiffAt_const
  frame_orthonormal _ a b _ _ := by
    change euclideanForm n (Pi.single a 1 : Fin n → ℝ) (Pi.single b 1 : Fin n → ℝ) = _
    by_cases h : a = b
    · subst h; simp [Pi.single_apply]
    · simp [Pi.single_apply, h, Ne.symm h]
  frame_change _ _ x _ _ a := by
    change (Pi.single a 1 : Fin n → ℝ) = ∑ b, (1 : Matrix (Fin n) (Fin n) ℝ) a b • (Pi.single b 1 : Fin n → ℝ)
    simp [Matrix.one_apply, Finset.sum_ite_eq]

end Manifold

end Lightlike.Dirac
