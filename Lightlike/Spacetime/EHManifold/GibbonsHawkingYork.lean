import Lightlike.Spacetime.VariationChristoffel
import Lightlike.Spacetime.EHManifold.BoxDirichlet

/-!
# The Gibbons–Hawking–York boundary density on a coordinate face, and its variation

For a coordinate metric `g` and the face `x^i = const` (with `g^{ii} ≠ 0`), in the notation of
Dyer–Hinterbichler (4.1) to (4.3):

* the unit conormal is `n_β = δ^i_β / √|g^{ii}|`, the induced inverse metric is
  `h^{αβ} = g^{αβ} - g^{αi} g^{βi} / g^{ii}` (`faceHup`; it annihilates the index `i`: `faceHup_right`);
* the extrinsic curvature `K = h^{αβ} (∂_α n_β - Γ^μ_{αβ} n_μ)` is `-(1/√|g^{ii}|) h^{αβ} Γ^i_{αβ}`
  (`faceK`), the term with `∂_α n_β` dropping out because `h^{αi} = 0`;
* the boundary density `2 √|h| K` is `2 √|g| √|g^{ii}| K` (`ghyDensity`), with `√|h| = √|g| √|g^{ii}|` for
  the induced metric of the face.

`hasDerivAt_ghyDensity`: at a point where the perturbation vanishes,
`d/dt ghyDensity (g + t h) = -2 √|g| h^{αβ} δΓ^i_{αβ}` at `t = 0`.

The identifications of `K` and `√|h|` with these coordinate expressions are the definitions used here; they
are not derived from an induced metric on a hypersurface.

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eqs. (4.1) to (4.3), p. 20.
-/

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The induced inverse metric `h^{αβ} = g^{αβ} - g^{αi} g^{βi} / g^{ii}` of the face `x^i = const`. -/
def faceHup (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ) (α β : Fin n) : ℝ :=
  (g x)⁻¹ α β - (g x)⁻¹ α i * (g x)⁻¹ β i / (g x)⁻¹ i i

/-- The induced inverse metric annihilates the normal index. -/
lemma faceHup_right (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ)
    (hii : (g x)⁻¹ i i ≠ 0) (α : Fin n) : faceHup g i x α i = 0 := by
  unfold faceHup
  field_simp
  ring

/-- The same for the first index, for a symmetric inverse metric. -/
lemma faceHup_left (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ)
    (hii : (g x)⁻¹ i i ≠ 0) (hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a) (β : Fin n) :
    faceHup g i x i β = 0 := by
  unfold faceHup
  rw [hinv i β]
  field_simp
  ring

/-- **The extrinsic curvature of the face `x^i = const`**: `K = -(1/√|g^{ii}|) h^{αβ} Γ^i_{αβ}`. -/
def faceK (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  -(1 / √|(g x)⁻¹ i i|) * ∑ α, ∑ β, faceHup g i x α β * christoffel g i α β x

/-- **The Gibbons–Hawking–York boundary density** `2 √|h| K` of the face `x^i = const`. -/
def ghyDensity (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  2 * √|(g x).det| * √|(g x)⁻¹ i i| * faceK g i x

/-- **The variation of the Gibbons–Hawking–York density** at a point where the perturbation vanishes. -/
theorem hasDerivAt_ghyDensity (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) (hgd : ∀ l k, DifferentiableAt ℝ (fun y => g y l k) x)
    (hhd : ∀ l k, DifferentiableAt ℝ (fun y => h y l k) x) (hG : (g x).det ≠ 0)
    (hii : (g x)⁻¹ i i ≠ 0) (hx0 : h x = 0) :
    HasDerivAt (fun t : ℝ => ghyDensity (fun y => g y + t • h y) i x)
      (-2 * √|(g x).det| * ∑ α, ∑ β, faceHup g i x α β * dChristoffel g h i α β x) 0 := by
  have hfun : (fun t : ℝ => ghyDensity (fun y => g y + t • h y) i x) =
      fun t => (2 * √|(g x).det| * √|(g x)⁻¹ i i| * -(1 / √|(g x)⁻¹ i i|)) *
        ∑ α, ∑ β, faceHup g i x α β * christoffel (fun y => g y + t • h y) i α β x := by
    funext t
    simp only [ghyDensity, faceK, faceHup, hx0, smul_zero, add_zero]
    ring
  have hsq : √|(g x)⁻¹ i i| ≠ 0 := (Real.sqrt_pos.2 (abs_pos.2 hii)).ne'
  have hc : 2 * √|(g x).det| * √|(g x)⁻¹ i i| * -(1 / √|(g x)⁻¹ i i|) = -2 * √|(g x).det| := by
    field_simp
  rw [hfun, hc]
  refine HasDerivAt.const_mul _ ?_
  refine HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun β _ => ?_
  exact (hasDerivAt_christoffel_add_smul g h x hgd hhd hG i α β).const_mul _

/-- At a point where the perturbation vanishes, the Christoffel symbols of `g + t h` are affine in `t`. -/
lemma christoffel_add_smul_of_zero (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hgd : ∀ l k, DifferentiableAt ℝ (fun y => g y l k) x)
    (hhd : ∀ l k, DifferentiableAt ℝ (fun y => h y l k) x) (hx0 : h x = 0) (t : ℝ) (i j k : Fin n) :
    christoffel (fun y => g y + t • h y) i j k x =
      christoffel g i j k x + t * dChristoffel g h i j k x := by
  unfold christoffel dChristoffel
  simp only [pd_add_smul g h t _ _ _ x (hgd _ _) (hhd _ _), hx0, smul_zero, add_zero,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_mul, zero_add]
  rw [← mul_assoc, mul_comm t (1 / 2), mul_assoc, ← mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **At a point where the perturbation vanishes, the Gibbons–Hawking–York density of `g + t h` is affine
in `t`**, with slope `-2 √|g| h^{αβ} δΓ^i_{αβ}`. -/
theorem ghyDensity_add_smul_of_zero (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) (hgd : ∀ l k, DifferentiableAt ℝ (fun y => g y l k) x)
    (hhd : ∀ l k, DifferentiableAt ℝ (fun y => h y l k) x) (hii : (g x)⁻¹ i i ≠ 0) (hx0 : h x = 0)
    (t : ℝ) :
    ghyDensity (fun y => g y + t • h y) i x =
      ghyDensity g i x +
        t * (-2 * √|(g x).det| * ∑ α, ∑ β, faceHup g i x α β * dChristoffel g h i α β x) := by
  have hs : ∑ α, ∑ β, faceHup g i x α β * christoffel (fun y => g y + t • h y) i α β x =
      ∑ α, ∑ β, faceHup g i x α β * christoffel g i α β x +
        t * ∑ α, ∑ β, faceHup g i x α β * dChristoffel g h i α β x := by
    simp only [christoffel_add_smul_of_zero g h x hgd hhd hx0, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    ring
  have hsq : √|(g x)⁻¹ i i| ≠ 0 := (Real.sqrt_pos.2 (abs_pos.2 hii)).ne'
  have hunf : ghyDensity (fun y => g y + t • h y) i x =
      2 * √|(g x).det| * √|(g x)⁻¹ i i| * (-(1 / √|(g x)⁻¹ i i|) *
        ∑ α, ∑ β, faceHup g i x α β * christoffel (fun y => g y + t • h y) i α β x) := by
    simp only [ghyDensity, faceK, faceHup, hx0, smul_zero, add_zero]
  rw [hunf, hs]
  unfold ghyDensity faceK
  field_simp
  ring

end Lightlike
