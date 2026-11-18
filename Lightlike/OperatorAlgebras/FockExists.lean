import Lightlike.OperatorAlgebras.FockKernel
import Lightlike.OperatorAlgebras.GramUnitary
import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# Existence of the Fock representation

Helper lemmas for `T-OP2-P1` (`Tasks/OP/T_OP2_P1.lean`).
-/

open scoped InnerProductSpace ComplexOrder ComplexConjugate

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]

/-- The Fock kernel as a matrix with entries in `ℂ →L[ℂ] ℂ`, for Mathlib's reproducing kernel Hilbert
spaces. -/
noncomputable def fockKer (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h] :
    Matrix h h (ℂ →L[ℂ] ℂ) :=
  Matrix.of fun f g => fockGram f g • ContinuousLinearMap.id ℂ ℂ

lemma fockGram_conj' (f g : h) : fockGram g f = (starRingEnd ℂ) (fockGram f g) := by
  have h3 : (⟪g, f⟫_ℂ).im = -(⟪f, g⟫_ℂ).im := by
    have := inner_conj_symm (𝕜 := ℂ) g f
    rw [← this, Complex.conj_im]
  have h1 : symp h (-g) f = -symp h (-f) g := by
    simp only [symp, inner_neg_left, Complex.neg_im, h3]
  have h2 : ‖-g + f‖ = ‖-f + g‖ := by
    rw [← norm_neg]; congr 1; abel
  unfold fockGram
  rw [h1, h2]
  simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I, Complex.conj_ofReal,
    map_ofNat, Complex.ofReal_neg]
  congr 2
  push_cast
  ring

theorem posSemidef_fockKer : (fockKer h).PosSemidef := by
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  refine ⟨?_, fun vv => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, fockKer, Matrix.of_apply, star_smul, star_one]
    have hs : star (ContinuousLinearMap.id ℂ ℂ) = ContinuousLinearMap.id ℂ ℂ :=
      star_one (ℂ →L[ℂ] ℂ)
    simp only [hs, RCLike.star_def]
    rw [← fockGram_conj' j i]
  · have hq := (posSemidef_fockMat (h := h)).2 vv
    have : (vv.sum fun x w => vv.sum fun x' w' => ⟪fockKer h x' x w, w'⟫_ℂ) =
        vv.sum fun i a => vv.sum fun j b => star a * fockMat h i j * b := by
      refine Finsupp.sum_congr fun x _ => Finsupp.sum_congr fun x' _ => ?_
      simp only [fockKer, fockMat, Matrix.of_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, RCLike.inner_apply, smul_eq_mul, map_mul, RCLike.star_def]
      rw [fockGram_conj' x x']
      simp only [starRingEnd_self_apply]
      ring
    rw [this]
    exact (Complex.nonneg_iff.1 hq).1

end Lightlike.OperatorAlgebras
