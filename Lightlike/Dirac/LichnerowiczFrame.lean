import Mathlib
import Lightlike.Dirac.Jacobi

/-!
# The Lichnerowicz formula in a frame, with no curvature hypothesis

`lichnerowicz_general'` needed the first Bianchi identity of `curvF` as a hypothesis; for an honest
`C²` frame (linearly independent, structure functions, torsion-free skew connection) it is a
theorem (`curvF_bianchi_frame`), so the formula holds with only frame data as hypotheses.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Lichnerowicz formula in a `C²` frame.**  For a `C²` frame `F` (linearly independent at `x`) with
structure functions `cs` and a skew, torsion-free frame connection `ω` near `x`, and a `C²` spinor
field `f`: `D² f = -∑ᵢ ∇²f(Fᵢ,Fᵢ) + (s/4) f`, with `s = ∑ᵢⱼ Rᵢⱼ,ⱼᵢ` the scalar curvature of `curvF`.
No curvature identity is assumed. -/
theorem lichnerowicz_frame_general (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {f : E n → V} {x : E n}
    (hf2 : ContDiffAt ℝ 2 f x) (hF2 : ∀ a, ContDiffAt ℝ 2 (fun y => F y a) x)
    (hli : LinearIndependent ℝ (F x))
    (hω : ∀ a k l, DifferentiableAt ℝ (fun y => ω y a k l) x)
    (hnf : ∀ j, DifferentiableAt ℝ (fun y => nablaF ρ F ω j f y) x)
    (hskew : ∀ᶠ y in nhds x, ∀ a k l, ω y a k l = - ω y a l k)
    (cs : E n → Fin n → Fin n → Fin n → ℝ)
    (hbrN : ∀ᶠ y in nhds x, ∀ a b, fderiv ℝ (fun z => F z b) y (F y a) -
      fderiv ℝ (fun z => F z a) y (F y b) = ∑ c, cs y a b c • F y c)
    (ht : ∀ᶠ y in nhds x, ∀ a b c, ω y a b c - ω y b a c = cs y a b c) :
    diracF ρ F ω (diracF ρ F ω f) x =
      -∑ i, hessF ρ F ω f x i i +
      ((1 / 4 : ℝ) * ∑ i, ∑ j, curvF F ω (cs x) x i j j i) • f x :=
  lichnerowicz_general' ρ F ω hf2 (fun a => (hF2 a).differentiableAt (by norm_num)) hω hnf hskew
    (cs x) (fun a b => hbrN.self_of_nhds a b) (fun a b c => ht.self_of_nhds a b c)
    (curvF_bianchi_frame F ω cs hF2 hli hω hskew ht hbrN)

end Lightlike.Dirac
