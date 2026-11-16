import Lightlike.SpinFoam.TwistedCohomology
import Lightlike.SU2.Su2Exp
import Lightlike.SU2.SpinRep

/-!
# The twisted complex for SU(2) with the adjoint representation, and the holonomy map

The coefficients are `su(2)` (traceless anti-Hermitian `2 × 2` matrices, a 3-dimensional real
space) with the adjoint action of `SU(2)`. For a connection `g : E → SU(2)` and variations `Φ`
of the edges, `holonomy_hasDerivAt` shows that `d1` is the differential of the holonomy
map: along curves `γₑ` through `gₑ` with `γₑ'(0) γₑ(0)⁻¹ = Φ(e)`, the holonomy `h` of a word
varies by `h'(0) h(0)⁻¹ = dword Φ`.

## Main results

* `su2`, `adRep`: `su(2)` as a real subspace and the adjoint representation of `SU(2)` on it.
* `holonomy_hasDerivAt`: the derivative of the holonomy of a word along edge curves is `d1`.
* `expCurve`: the curves `exp(tΦ) g` through the connection with velocity `Φ`.
* `face_variation_iff`: for a flat connection, the face holonomies along `expCurve` vary by `X`
  exactly when `d1 Φ = X`.
* `h2_trivial_iff_face_variation`: for a flat connection, `H² = 0` iff `d1` is onto iff every variation `X` of the
  face holonomies is realised by varying the edges.
-/

open Matrix Lightlike.SU2

namespace Lightlike.SpinFoam

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `su(2)` as a real subspace of the complex `2 × 2` matrices. -/
def su2 : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {X | IsSu2 X}
  add_mem' {a b} ha hb :=
    ⟨by rw [conjTranspose_add, ha.1, hb.1, neg_add], by rw [trace_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' c X hX :=
    ⟨by rw [conjTranspose_smul, hX.1, smul_neg, star_trivial], by
      rw [trace_smul, hX.2, smul_zero]⟩

lemma mem_su2 {X : Matrix (Fin 2) (Fin 2) ℂ} : X ∈ su2 ↔ IsSu2 X := Iff.rfl

lemma coe_inv_su2 (g : SU2) :
    ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = star (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl

lemma star_mul_su2 (g : SU2) :
    star (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 (Matrix.mem_specialUnitaryGroup_iff.1 g.2).1

lemma isSu2_conj (g : SU2) {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X) :
    IsSu2 ((g : Matrix (Fin 2) (Fin 2) ℂ) * X * ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [coe_inv_su2]
  refine ⟨?_, ?_⟩
  · rw [← star_eq_conjTranspose, star_mul, star_mul, star_star, ← mul_assoc,
      star_eq_conjTranspose X, hX.1]
    simp [mul_assoc]
  · rw [trace_mul_comm, ← mul_assoc, trace_mul_comm, star_mul_su2, mul_one]
    exact hX.2

/-- The adjoint action of `g ∈ SU(2)` on `su(2)`: `X ↦ g X g⁻¹`. -/
noncomputable def adMap (g : SU2) : su2 →ₗ[ℝ] su2 where
  toFun X := ⟨(g : Matrix (Fin 2) (Fin 2) ℂ) * X * ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ),
    isSu2_conj g X.2⟩
  map_add' X Y := by ext1; simp [mul_add, add_mul]
  map_smul' c X := by ext1; simp

lemma adMap_coe (g : SU2) (X : su2) :
    ((adMap g X : su2) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) * X * ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- The adjoint representation of `SU(2)` on `su(2)`. -/
noncomputable def adRep : Representation ℝ SU2 su2 where
  toFun := adMap
  map_one' := by
    ext1 X; ext1; simp [adMap_coe]
  map_mul' g h := by
    ext1 X; ext1
    simp [adMap_coe, mul_assoc]

lemma mul_star_su2 (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff.1 (Matrix.mem_specialUnitaryGroup_iff.1 g.2).1

section Holonomy

/-- The conjugate transpose is continuous for the operator-norm topology, which is the product
topology on `2 × 2` matrices. -/
local instance : @ContinuousStar (Matrix (Fin 2) (Fin 2) ℂ)
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ :=
  ⟨(inferInstance : @ContinuousStar _ instTopologicalSpaceMatrix _).continuous_star⟩

variable {E : Type*}

/-- The matrix curve of a traversed edge: `c e` forwards, its conjugate transpose (the inverse
in `SU(2)`) backwards. -/
def lcurve (c : E → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (l : E × Bool) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ := if l.2 then c l.1 t else star (c l.1 t)

/-- The matrix curve of the holonomy of a word along the edge curves `c`. -/
def hcurve (c : E → ℝ → Matrix (Fin 2) (Fin 2) ℂ) :
    List (E × Bool) → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | [], _ => 1
  | l :: w, t => lcurve c l t * hcurve c w t

lemma adRep_coe (g : SU2) (X : su2) :
    ((adRep g X : su2) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) * X * star (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- **`d1` is the differential of the holonomy map.** Let the edge curves `c e` pass through the
connection `g e` at `t = 0` with velocity `Φ e · g e` (so `Φ e = c'(0) c(0)⁻¹ ∈ su(2)`). Then the
holonomy of every word has velocity `(dword Φ w) · hol g w`, that is `h'(0) h(0)⁻¹ = dword Φ w`:
the variation of the face holonomies is `d1 Φ`. -/
theorem holonomy_hasDerivAt (g : E → SU2) (Φ : E → su2)
    (c : E → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hc0 : ∀ e, c e 0 = g e)
    (hcd : ∀ e, HasDerivAt (c e) ((Φ e : Matrix (Fin 2) (Fin 2) ℂ) * g e) 0)
    (w : List (E × Bool)) :
    hcurve c w 0 = ((hol g w : SU2) : Matrix (Fin 2) (Fin 2) ℂ) ∧
    HasDerivAt (hcurve c w)
      (((dword adRep g Φ w : su2) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((hol g w : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) 0 := by
  induction w with
  | nil =>
    refine ⟨rfl, ?_⟩
    simp only [hcurve, hol, dword, Submodule.coe_zero, zero_mul]
    exact hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | cons l w ih =>
    obtain ⟨ih0, ihd⟩ := ih
    obtain ⟨e, s⟩ := l
    have hL0 : lcurve c (e, s) 0 = ((lh g (e, s) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) := by
      cases s <;> simp [lcurve, lh, hc0, coe_inv_su2]
    have hLd : HasDerivAt (lcurve c (e, s))
        (((lc adRep g (e, s) (Φ e) : su2) : Matrix (Fin 2) (Fin 2) ℂ) *
          ((lh g (e, s) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) 0 := by
      cases s
      · have := (hcd e).star
        have hfun : lcurve c (e, false) = fun t => star (c e t) := by
          funext t; simp [lcurve]
        have e1 : lc adRep g (e, false) (Φ e) = -(adRep (g e)⁻¹ (Φ e)) := by simp [lc]
        have e2 : lh g (e, false) = (g e)⁻¹ := by simp [lh]
        rw [e1, e2, hfun]
        convert this using 1
        · rfl
        · have hΦ : star (Φ e : Matrix (Fin 2) (Fin 2) ℂ) = -(Φ e : Matrix (Fin 2) (Fin 2) ℂ) :=
            (Φ e).2.1
          have hA : ((adRep (g e)⁻¹ (Φ e) : su2) : Matrix (Fin 2) (Fin 2) ℂ) =
              star (g e : Matrix (Fin 2) (Fin 2) ℂ) * Φ e * (g e : Matrix (Fin 2) (Fin 2) ℂ) := by
            rw [adRep_coe, coe_inv_su2]; simp
          have hB := mul_star_su2 (g e)
          rw [Submodule.coe_neg, hA, coe_inv_su2, star_mul, hΦ]
          simp only [neg_mul, mul_neg, mul_assoc]
          rw [hB, mul_one]
      · have hfun : lcurve c (e, true) = c e := by funext t; simp [lcurve]
        have e1 : lc adRep g (e, true) (Φ e) = Φ e := by simp [lc]
        have e2 : lh g (e, true) = g e := by simp [lh]
        rw [e1, e2, hfun]
        exact hcd e
    have := hLd.mul ihd
    refine ⟨by simp [hcurve, hL0, ih0, hol, Submonoid.coe_mul], ?_⟩
    convert this using 1
    · rfl
    · funext t; rfl
    · have hρ : ∀ (h : SU2) (x : su2),
          ((adRep h x : su2) : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ) =
            (h : Matrix (Fin 2) (Fin 2) ℂ) * x := fun h x => by
        rw [adRep_coe, mul_assoc, mul_assoc, star_mul_su2 h, mul_one]
      rw [hL0, ih0]
      simp only [dword, hol, Submonoid.coe_mul, Submodule.coe_add, add_mul, mul_assoc]
      congr 1
      rw [← mul_assoc, hρ, mul_assoc]

/-- The coefficient space `su(2) ≅ ℝ³` is finite-dimensional, so `H²` is finite-dimensional
linear algebra over `ℝ` once the 2-complex is finite. -/
instance : FiniteDimensional ℝ su2 := inferInstance

/-- The edge curves `t ↦ exp(t Φ e) · g e`, which leave `g e` with velocity `Φ e · g e`. -/
noncomputable def expCurve (g : E → SU2) (Φ : E → su2) (e : E) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp (t • (Φ e : Matrix (Fin 2) (Fin 2) ℂ)) * (g e : Matrix (Fin 2) (Fin 2) ℂ)

lemma expCurve_zero (g : E → SU2) (Φ : E → su2) (e : E) : expCurve g Φ e 0 = g e := by
  simp [expCurve]

lemma expCurve_hasDerivAt (g : E → SU2) (Φ : E → su2) (e : E) :
    HasDerivAt (expCurve g Φ e)
      ((Φ e : Matrix (Fin 2) (Fin 2) ℂ) * (g e : Matrix (Fin 2) (Fin 2) ℂ)) 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Φ e : Matrix (Fin 2) (Fin 2) ℂ) (0 : ℝ)).mul_const
    (g e : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

section Criterion

variable {Vtx F : Type*}

/-- **The variation criterion, step by step.** For a flat `SU(2)` connection `g` on the 2-complex
`C`, a prescribed first-order change `X f ∈ su(2)` of every face holonomy (from the identity) is
realised by the curves `exp(t Φ e) · g e` exactly when `X = d1 Φ`. -/
theorem face_variation_iff (C : Cell2 Vtx E F) {g : E → SU2} (hg : Flat C g)
    (Φ : E → su2) (X : F → su2) :
    (∀ f, HasDerivAt (hcurve (expCurve g Φ) (C.bdry f)) (X f : Matrix (Fin 2) (Fin 2) ℂ) 0) ↔
      d1 adRep C g Φ = X := by
  have key : ∀ f, HasDerivAt (hcurve (expCurve g Φ) (C.bdry f))
      ((d1 adRep C g Φ f : su2) : Matrix (Fin 2) (Fin 2) ℂ) 0 := by
    intro f
    have h := (holonomy_hasDerivAt g Φ (expCurve g Φ) (expCurve_zero g Φ)
      (expCurve_hasDerivAt g Φ) (C.bdry f)).2
    rw [hg f] at h
    simpa [d1] using h
  constructor
  · intro hX
    funext f
    exact Subtype.ext ((key f).unique (hX f))
  · rintro rfl f
    exact key f

/-- **Criterion (BNG 2009, §4.4), `SU(2)` coefficients.** For a flat `SU(2)` connection `g` on a
finite 2-complex, the following are equivalent: (1) `H²(C, Ad g) = 0`; (2) the holonomy map has a
surjective differential `d1`; (3) every first-order change `X f ∈ su(2)` of the face holonomies
is realised by varying the edge holonomies. -/
theorem h2_trivial_iff_face_variation (C : Cell2 Vtx E F) {g : E → SU2} (hg : Flat C g) :
    (Subsingleton (H2 adRep C g) ↔ Function.Surjective (d1 adRep C g)) ∧
    (Function.Surjective (d1 adRep C g) ↔
      ∀ X : F → su2, ∃ Φ : E → su2,
        ∀ f, HasDerivAt (hcurve (expCurve g Φ) (C.bdry f)) (X f : Matrix (Fin 2) (Fin 2) ℂ) 0) := by
  refine ⟨(d1_surjective_iff _ C g).symm, ⟨fun hs X => ?_, fun h X => ?_⟩⟩
  · obtain ⟨Φ, hΦ⟩ := hs X
    exact ⟨Φ, (face_variation_iff C hg Φ X).2 hΦ⟩
  · obtain ⟨Φ, hΦ⟩ := h X
    exact ⟨Φ, (face_variation_iff C hg Φ X).1 hΦ⟩

end Criterion

end Holonomy

end Lightlike.SpinFoam
