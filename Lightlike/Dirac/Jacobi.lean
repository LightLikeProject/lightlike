import Mathlib
import Lightlike.Dirac.Bianchi

/-!
# Jacobi identity for the structure functions of a frame

For a `C²` frame `F` with structure functions `cs` (`[Fₐ, F_b] = ∑_c cs a b c F_c` near `x`) which
is linearly independent at `x`, the Jacobi identity of vector fields (Mathlib's
`VectorField.leibniz_identity_lieBracket`) gives the Jacobi identity of the structure functions,
`jacobi_structure`.  With `curvF_bianchi` this yields the first Bianchi identity for `curvF`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

open VectorField

variable {n : ℕ}

/-- The bracket of a frame field with a bracket of frame fields, expanded in the frame. -/
lemma bracket_bracket (F : E n → Fin n → E n) (cs : E n → Fin n → Fin n → Fin n → ℝ) {x : E n}
    (hFd : ∀ a, DifferentiableAt ℝ (fun y => F y a) x)
    (hcs : ∀ a b c, DifferentiableAt ℝ (fun y => cs y a b c) x)
    (hbrN : ∀ᶠ y in nhds x, ∀ a b, fderiv ℝ (fun z => F z b) y (F y a) -
      fderiv ℝ (fun z => F z a) y (F y b) = ∑ c, cs y a b c • F y c) (a b c : Fin n) :
    lieBracket ℝ (fun y => F y a) (lieBracket ℝ (fun y => F y b) (fun y => F y c)) x =
      ∑ e, (fderiv ℝ (fun y => cs y b c e) x (F x a) +
        ∑ m, cs x b c m * cs x a m e) • F x e := by
  have hev : lieBracket ℝ (fun y => F y b) (fun y => F y c) =ᶠ[nhds x]
      fun y => ∑ e, cs y b c e • F y e := hbrN.mono fun y hy => hy b c
  have hx : lieBracket ℝ (fun y => F y b) (fun y => F y c) x = ∑ e, cs x b c e • F x e :=
    hev.self_of_nhds
  have hGd : fderiv ℝ (fun y => ∑ e, cs y b c e • F y e) x (F x a) =
      ∑ e, (fderiv ℝ (fun y => cs y b c e) x (F x a) • F x e +
        cs x b c e • fderiv ℝ (fun y => F y e) x (F x a)) := by
    have hD : ∀ e ∈ Finset.univ, HasFDerivAt (fun y => cs y b c e • F y e)
        (cs x b c e • fderiv ℝ (fun y => F y e) x +
          (fderiv ℝ (fun y => cs y b c e) x).smulRight (F x e)) x :=
      fun e _ => (hcs b c e).hasFDerivAt.smul (hFd e).hasFDerivAt
    rw [(HasFDerivAt.fun_sum hD).fderiv]
    simp only [sum_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [add_comm]
  have hbr_a : ∀ e, fderiv ℝ (fun y => F y e) x (F x a) - fderiv ℝ (fun y => F y a) x (F x e) =
      ∑ d, cs x a e d • F x d := fun e => hbrN.self_of_nhds a e
  have hL : fderiv ℝ (fun y => F y a) x (∑ e, cs x b c e • F x e) =
      ∑ e, cs x b c e • fderiv ℝ (fun y => F y a) x (F x e) := by
    rw [map_sum]; simp only [map_smul]
  have e1 : lieBracket ℝ (fun y => F y a) (lieBracket ℝ (fun y => F y b) (fun y => F y c)) x =
      fderiv ℝ (lieBracket ℝ (fun y => F y b) (fun y => F y c)) x (F x a) -
        fderiv ℝ (fun y => F y a) x (lieBracket ℝ (fun y => F y b) (fun y => F y c) x) := rfl
  rw [e1, hev.fderiv_eq, hx, hGd, hL, ← Finset.sum_sub_distrib]
  have h2 : ∀ e, (fderiv ℝ (fun y => cs y b c e) x (F x a) • F x e +
        cs x b c e • fderiv ℝ (fun y => F y e) x (F x a)) -
        cs x b c e • fderiv ℝ (fun y => F y a) x (F x e) =
      fderiv ℝ (fun y => cs y b c e) x (F x a) • F x e +
        cs x b c e • ∑ d, cs x a e d • F x d := by
    intro e
    rw [← hbr_a e, smul_sub]
    abel
  simp only [h2]
  simp only [Finset.smul_sum, smul_smul, Finset.sum_add_distrib, add_smul, Finset.sum_smul]
  congr 1
  exact Finset.sum_comm

/-- **Jacobi identity for the structure functions of a frame.**  If `F` is a `C²` frame,
linearly independent at `x`, with `[Fₐ, F_b] = ∑ c_abe F_e` near `x` and `cs` skew in the first two
indices near `x`, then
`∂ₐ c_bce + ∂_b c_cae + ∂_c c_abe + ∑ₘ (c_bcm cₐme + c_cam c_bme + c_abm c_cme) = 0` at `x`. -/
theorem jacobi_structure (F : E n → Fin n → E n) (cs : E n → Fin n → Fin n → Fin n → ℝ) {x : E n}
    (hF2 : ∀ a, ContDiffAt ℝ 2 (fun y => F y a) x)
    (hcs : ∀ a b c, DifferentiableAt ℝ (fun y => cs y a b c) x)
    (hbrN : ∀ᶠ y in nhds x, ∀ a b, fderiv ℝ (fun z => F z b) y (F y a) -
      fderiv ℝ (fun z => F z a) y (F y b) = ∑ c, cs y a b c • F y c)
    (hsk : ∀ᶠ y in nhds x, ∀ a b c, cs y a b c = - cs y b a c)
    (hli : LinearIndependent ℝ (F x)) (a b c e : Fin n) :
    fderiv ℝ (fun y => cs y b c e) x (F x a) +
        fderiv ℝ (fun y => cs y c a e) x (F x b) + fderiv ℝ (fun y => cs y a b e) x (F x c) +
        ∑ m, (cs x b c m * cs x a m e + cs x c a m * cs x b m e + cs x a b m * cs x c m e) = 0 := by
  have hFd : ∀ a, DifferentiableAt ℝ (fun y => F y a) x :=
    fun a => (hF2 a).differentiableAt (by norm_num)
  have hBB := bracket_bracket F cs hFd hcs hbrN
  have hjac := leibniz_identity_lieBracket (𝕜 := ℝ) (n := 2) (by simp [minSmoothness_of_isRCLikeNormedField])
    (hF2 a) (hF2 b) (hF2 c)
  rw [lieBracket_swap (V := lieBracket ℝ (fun y => F y a) (fun y => F y b)), hBB c a b,
    hBB a b c, hBB b a c] at hjac
  have hskx : ∀ a b c, cs x a b c = - cs x b a c := hsk.self_of_nhds
  have hdsk : ∀ p q r s, fderiv ℝ (fun y => cs y q r s) x (F x p) =
      - fderiv ℝ (fun y => cs y r q s) x (F x p) := by
    intro p q r s
    have h : (fun y => cs y q r s) =ᶠ[nhds x] fun y => - cs y r q s :=
      hsk.mono fun y hy => hy q r s
    rw [h.fderiv_eq, fderiv_fun_neg]
    rfl
  have hsum : ∑ m, cs x a c m * cs x b m e = - ∑ m, cs x c a m * cs x b m e := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [hskx a c m]; ring
  have h0 : ∑ e', ((fderiv ℝ (fun y => cs y b c e') x (F x a) + ∑ m, cs x b c m * cs x a m e') +
      (fderiv ℝ (fun y => cs y a b e') x (F x c) + ∑ m, cs x a b m * cs x c m e') -
      (fderiv ℝ (fun y => cs y a c e') x (F x b) + ∑ m, cs x a c m * cs x b m e')) • F x e' = 0 := by
    simp only [add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hjac ⊢
    linear_combination (norm := module) hjac
  have := Fintype.linearIndependent_iff.mp hli _ h0 e
  have d1 := hdsk b a c e
  simp only [Finset.sum_add_distrib]
  linarith

/-- **First Bianchi identity for `curvF`, from the frame alone.**  For a `C²` frame `F`, linearly
independent at `x`, with structure functions `cs` (near `x`) and a skew torsion-free frame
connection `ω` (near `x`), the cyclic sum of `curvF` vanishes. -/
theorem curvF_bianchi_frame (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) (cs : E n → Fin n → Fin n → Fin n → ℝ) {x : E n}
    (hF2 : ∀ a, ContDiffAt ℝ 2 (fun y => F y a) x) (hli : LinearIndependent ℝ (F x))
    (hω : ∀ a k l, DifferentiableAt ℝ (fun y => ω y a k l) x)
    (hskew : ∀ᶠ y in nhds x, ∀ a k l, ω y a k l = - ω y a l k)
    (ht : ∀ᶠ y in nhds x, ∀ a b c, ω y a b c - ω y b a c = cs y a b c)
    (hbrN : ∀ᶠ y in nhds x, ∀ a b, fderiv ℝ (fun z => F z b) y (F y a) -
      fderiv ℝ (fun z => F z a) y (F y b) = ∑ c, cs y a b c • F y c) (i j k l : Fin n) :
    curvF F ω (cs x) x i j k l + curvF F ω (cs x) x j k i l + curvF F ω (cs x) x k i j l = 0 := by
  have hcs : ∀ a b c, DifferentiableAt ℝ (fun y => cs y a b c) x := fun a b c =>
    ((hω a b c).sub (hω b a c)).congr_of_eventuallyEq (ht.mono fun y hy => (hy a b c).symm)
  have hsk : ∀ᶠ y in nhds x, ∀ a b c, cs y a b c = - cs y b a c := by
    filter_upwards [ht] with y hy a b c
    rw [← hy a b c, ← hy b a c]; ring
  exact curvF_bianchi F ω cs hω hskew ht
    (jacobi_structure F cs hF2 hcs hbrN hsk hli) i j k l

end Lightlike.Dirac
