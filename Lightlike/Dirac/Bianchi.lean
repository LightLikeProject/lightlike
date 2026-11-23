import Mathlib
import Lightlike.Dirac.CurvatureSymmetry

/-!
# First Bianchi identity for the structure-equation curvature

Algebraic part: for a skew torsion-free frame connection `w` with structure constants `cs`, the
cyclic sum of the quadratic part of `curvF` equals the Jacobi quadratic expression.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ}

/-- Koszul formula: a connection that is skew in its last two indices and has torsion `cs`
is determined by `cs`. -/
lemma koszul_of_torsion (w : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (cs : Fin n → Fin n → Fin n → ℝ)
    (hw : ∀ a k l, w a k l = - w a l k) (ht : ∀ a b c, w a b c - w b a c = cs a b c)
    (a b c : Fin n) : w a b c = (cs a b c - cs b c a + cs c a b) / 2 := by
  have e1 := ht a b c
  have e2 := ht b c a
  have e3 := ht c a b
  have := hw a b c; have := hw b c a; have := hw c a b
  have := hw b a c; have := hw c b a; have := hw a c b
  linarith

lemma bianchi_quadratic (w : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (cs : Fin n → Fin n → Fin n → ℝ) (hsk : ∀ a b c, cs a b c = - cs b a c)
    (hw : ∀ a k l, w a k l = - w a l k) (ht : ∀ a b c, w a b c - w b a c = cs a b c)
    (a b k l : Fin n) :
    ((w b * w a - w a * w b) k l - ∑ c, cs a b c * w c k l) +
    ((w k * w b - w b * w k) a l - ∑ c, cs b k c * w c a l) +
    ((w a * w k - w k * w a) b l - ∑ c, cs k a c * w c b l) =
      ∑ m, (cs b k m * cs a m l + cs k a m * cs b m l + cs a b m * cs k m l) := by
  simp only [Matrix.mul_apply, Matrix.sub_apply]
  simp only [koszul_of_torsion w cs hw ht]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  obtain ⟨u, hu⟩ : ∃ u : Fin n → Fin n → Fin n → ℝ, ∀ a b c, cs a b c = u a b c - u b a c :=
    ⟨fun a b c => cs a b c / 2, fun a b c => by
      show cs a b c = cs a b c / 2 - cs b a c / 2
      linarith [hsk a b c]⟩
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [hu]
  ring

variable {V : Type*}

/-- Differentiating the torsion relation `ωₐ,bc - ω_b,ac = cs a b c` (valid near `x`) along `Fₑ`. -/
lemma omegaD_torsion (F : E n → Fin n → E n) (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (cs : E n → Fin n → Fin n → Fin n → ℝ) {x : E n}
    (hω : ∀ a k l, DifferentiableAt ℝ (fun y => ω y a k l) x)
    (ht : ∀ᶠ y in nhds x, ∀ a b c, ω y a b c - ω y b a c = cs y a b c) (e a b c : Fin n) :
    omegaD F ω x e a b c - omegaD F ω x e b a c = fderiv ℝ (fun y => cs y a b c) x (F x e) := by
  have h : (fun y => ω y a b c - ω y b a c) =ᶠ[nhds x] fun y => cs y a b c :=
    ht.mono fun y hy => hy a b c
  rw [← h.fderiv_eq, fderiv_fun_sub (hω a b c) (hω b a c)]
  rfl

/-- **First Bianchi identity for `curvF`**, from the Jacobi identity of the structure functions.
Here `cs y` are the structure functions of the frame near `x`, `ω y` is a skew torsion-free
frame connection near `x`, and `hJ` is the Jacobi identity
`∂ₐ c_bce + ∂_b c_cae + ∂_c c_abe + ∑ₘ (c_bcm cₐme + c_cam c_bme + c_abm c_cme) = 0` at `x`. -/
theorem curvF_bianchi (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) (cs : E n → Fin n → Fin n → Fin n → ℝ) {x : E n}
    (hω : ∀ a k l, DifferentiableAt ℝ (fun y => ω y a k l) x)
    (hskew : ∀ᶠ y in nhds x, ∀ a k l, ω y a k l = - ω y a l k)
    (ht : ∀ᶠ y in nhds x, ∀ a b c, ω y a b c - ω y b a c = cs y a b c)
    (hJ : ∀ a b c e, fderiv ℝ (fun y => cs y b c e) x (F x a) +
        fderiv ℝ (fun y => cs y c a e) x (F x b) + fderiv ℝ (fun y => cs y a b e) x (F x c) +
        ∑ m, (cs x b c m * cs x a m e + cs x c a m * cs x b m e + cs x a b m * cs x c m e) = 0)
    (i j k l : Fin n) :
    curvF F ω (cs x) x i j k l + curvF F ω (cs x) x j k i l + curvF F ω (cs x) x k i j l = 0 := by
  have hw : ∀ a k l, ω x a k l = - ω x a l k := hskew.self_of_nhds
  have htx : ∀ a b c, ω x a b c - ω x b a c = cs x a b c := ht.self_of_nhds
  have hsk : ∀ a b c, cs x a b c = - cs x b a c := fun a b c => by
    rw [← htx a b c, ← htx b a c]; ring
  have bq := bianchi_quadratic (ω x) (cs x) hsk hw htx i j k l
  simp only [Matrix.sub_apply] at bq
  have t1 := omegaD_torsion F ω cs hω ht i j k l
  have t2 := omegaD_torsion F ω cs hω ht j i k l
  have t3 := omegaD_torsion F ω cs hω ht k i j l
  have t4 := omegaD_torsion F ω cs hω ht j k i l
  have t5 := omegaD_torsion F ω cs hω ht j i k l
  have s1 : fderiv ℝ (fun y => cs y k i l) x (F x j) = - fderiv ℝ (fun y => cs y i k l) x (F x j) := by
    rw [← omegaD_torsion F ω cs hω ht j i k l, ← omegaD_torsion F ω cs hω ht j k i l]; ring
  have hj := hJ i j k l
  simp only [curvF, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  linarith

end Lightlike.Dirac
