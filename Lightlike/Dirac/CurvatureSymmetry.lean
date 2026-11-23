import Mathlib
import Lightlike.Dirac.LichnerowiczGeneral

/-!
# Symmetries of the structure-equation curvature `curvF`

For a frame connection `ω` that is skew in a neighbourhood of `x`, the curvature matrices
`curvF F ω cs x a b` are skew matrices (`curvF_skew_kl`).  Together with the antisymmetry in the
first pair (`curvF_antisymm`, from torsion-freeness) and the first Bianchi identity, this gives the
pair symmetry (`pair_symm_of_bianchi`), so the hypothesis `hP` of `lichnerowicz_general` follows
from `hB`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- If `ω` is skew near `x`, so is the derivative matrix `omegaD`. -/
lemma omegaD_skew (F : E n → Fin n → E n) (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    {x : E n} (hskew : ∀ᶠ y in nhds x, ∀ a k l, ω y a k l = - ω y a l k) (a b k l : Fin n) :
    omegaD F ω x a b k l = - omegaD F ω x a b l k := by
  have h : (fun y => ω y b k l) =ᶠ[nhds x] fun y => -ω y b l k :=
    hskew.mono fun y hy => hy b k l
  simp only [omegaD]
  rw [h.fderiv_eq, fderiv_fun_neg]
  rfl

/-- `curvF` consists of skew matrices when `ω` is skew near `x`. -/
lemma curvF_skew_kl (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {x : E n}
    (hskew : ∀ᶠ y in nhds x, ∀ a k l, ω y a k l = - ω y a l k)
    (cs : Fin n → Fin n → Fin n → ℝ) (a b k l : Fin n) :
    curvF F ω cs x a b k l = - curvF F ω cs x a b l k := by
  have hx : ∀ a k l, ω x a k l = - ω x a l k := hskew.self_of_nhds
  have hprod : ∀ a b k l, (ω x b * ω x a) k l = (ω x a * ω x b) l k := by
    intro a b k l
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hx b k m, hx a m l, hx a l m, hx b m k]
    ring
  simp only [curvF, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, omegaD_skew F ω hskew a b k l, omegaD_skew F ω hskew b a k l, hprod a b k l,
    hprod b a k l, hx _ k l, Finset.sum_neg_distrib, mul_neg]
  ring

/-- Algebraic fact: a four-index tensor that is skew in both pairs and satisfies the cyclic
Bianchi identity (in the first three indices) is symmetric under exchange of the pairs. -/
lemma pair_symm_of_bianchi (R : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h1 : ∀ a b c d, R a b c d = - R b a c d) (h2 : ∀ a b c d, R a b c d = - R a b d c)
    (hB : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0) (i j k l : Fin n) :
    R i j k l = R k l i j := by
  have e1 := hB i j k l
  have e2 := hB j k l i
  have e3 := hB k l i j
  have e4 := hB l i j k
  have := h1 i j k l; have := h2 i j k l
  have := h1 j k i l; have := h2 j k l i; have := h2 j k i l
  have := h1 k i j l; have := h2 k l j i; have := h1 k l j i
  have := h1 l j k i; have := h2 l j k i
  have := h1 l i k j; have := h2 l i k j; have := h2 i k l j; have := h1 i k l j
  have := h1 l i j k; have := h2 i j l k; have := h1 j i l k
  have := h2 k i j l; have := h2 k l i j; have := h1 k l i j
  have := h2 l j i k; have := h1 l j i k
  have := h1 i k j l; have := h2 i k j l
  have := h1 j k l i; have := h2 j l k i
  have := h1 j l k i; have := h1 j l i k; have := h2 j l i k
  linarith

/-- `curvF` has the pair symmetry as soon as it satisfies the first Bianchi identity (torsion-free,
`ω` skew near `x`). -/
lemma curvF_pair_symm (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {x : E n}
    (hskew : ∀ᶠ y in nhds x, ∀ a k l, ω y a k l = - ω y a l k)
    (cs : Fin n → Fin n → Fin n → ℝ)
    (htors : ∀ a b c, ω x a b c - ω x b a c = cs a b c)
    (hB : ∀ i j k l, curvF F ω cs x i j k l + curvF F ω cs x j k i l +
      curvF F ω cs x k i j l = 0) (i j k l : Fin n) :
    curvF F ω cs x i j k l = curvF F ω cs x k l i j :=
  pair_symm_of_bianchi (fun a b c d => curvF F ω cs x a b c d)
    (fun a b c d => curvF_antisymm F ω x cs htors a b c d)
    (fun a b c d => curvF_skew_kl F ω hskew cs a b c d) hB i j k l

/-- **Lichnerowicz formula in a general frame, pair symmetry derived.**  As `lichnerowicz_general`,
but the pair symmetry `hP` is no longer a hypothesis: it follows from the first Bianchi identity
`hB`, torsion-freeness and skewness of `ω` near `x`. -/
theorem lichnerowicz_general' (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {f : E n → V} {x : E n}
    (hf2 : ContDiffAt ℝ 2 f x) (hF : ∀ a, DifferentiableAt ℝ (fun y => F y a) x)
    (hω : ∀ a k l, DifferentiableAt ℝ (fun y => ω y a k l) x)
    (hnf : ∀ j, DifferentiableAt ℝ (fun y => nablaF ρ F ω j f y) x)
    (hskewN : ∀ᶠ y in nhds x, ∀ a k l, ω y a k l = - ω y a l k)
    (cs : Fin n → Fin n → Fin n → ℝ)
    (hbr : ∀ a b, fderiv ℝ (fun y => F y b) x (F x a) - fderiv ℝ (fun y => F y a) x (F x b) =
      ∑ c, cs a b c • F x c)
    (htors : ∀ a b c, ω x a b c - ω x b a c = cs a b c)
    (hB : ∀ i j k l, curvF F ω cs x i j k l + curvF F ω cs x j k i l +
      curvF F ω cs x k i j l = 0) :
    diracF ρ F ω (diracF ρ F ω f) x =
      -∑ i, hessF ρ F ω f x i i +
      ((1 / 4 : ℝ) * ∑ i, ∑ j, curvF F ω cs x i j j i) • f x :=
  lichnerowicz_general ρ F ω hf2 hF hω hnf hskewN.self_of_nhds cs hbr htors
    (curvF_pair_symm F ω hskewN cs htors hB) hB

end Lightlike.Dirac
