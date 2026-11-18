import Lightlike.OperatorAlgebras.ShaleSufficiency

/-!
# Trust check: the one-mode squeezing transformation

On the one-particle space `ℂ` (one mode) the squeezing `z ↦ a z + b z̄`, with real `a`, `b` and `a² - b² = 1`,
is a Bogoliubov transformation (`Bogoliubov.squeeze`). Its antilinear part is `z ↦ b z̄`
(`Bogoliubov.squeeze_betaPart`): the definition `betaPart` gives the known off-diagonal Bogoliubov coefficient,
which is not zero for `b ≠ 0`. With one mode it is Hilbert-Schmidt, so the squeezing is implemented in every Fock
representation of `ℂ` (`implements_squeeze`), as the Stone-von Neumann theorem says.
-/

open scoped InnerProductSpace
open Complex

namespace Lightlike.OperatorAlgebras

/-- The real-linear map `z ↦ a z + b z̄` of `ℂ`. -/
noncomputable def squeezeMap (a b : ℝ) : ℂ →L[ℝ] ℂ :=
  a • ContinuousLinearMap.id ℝ ℂ + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

lemma squeezeMap_apply (a b : ℝ) (z : ℂ) :
    squeezeMap a b z = (a : ℂ) * z + (b : ℂ) * (starRingEnd ℂ) z := by
  simp [squeezeMap, Complex.real_smul]

lemma squeezeMap_comp (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) (z : ℂ) :
    squeezeMap a (-b) (squeezeMap a b z) = z := by
  have h1 : ((a : ℂ)) ^ 2 - (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  rw [squeezeMap_apply, squeezeMap_apply]
  simp only [map_add, map_mul, conj_ofReal, Complex.conj_conj, Complex.ofReal_neg]
  linear_combination z * h1

/-- **The one-mode squeezing** `z ↦ a z + b z̄`, `a² - b² = 1`, as a Bogoliubov transformation of `ℂ`. -/
noncomputable def Bogoliubov.squeeze (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) : Bogoliubov ℂ where
  toEquiv := ContinuousLinearEquiv.equivOfInverse (squeezeMap a b) (squeezeMap a (-b))
    (squeezeMap_comp a b hab) (fun z => by
      have := squeezeMap_comp a (-b) (by rw [neg_sq]; exact hab) z
      rwa [neg_neg] at this)
  symp_map z w := by
    have h1 : ((a : ℂ)) ^ 2 - (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
    show (⟪squeezeMap a b z, squeezeMap a b w⟫_ℂ).im = (⟪z, w⟫_ℂ).im
    rw [squeezeMap_apply, squeezeMap_apply, RCLike.inner_apply, RCLike.inner_apply]
    simp only [map_add, map_mul, conj_ofReal, Complex.conj_conj]
    have h2 : ((starRingEnd ℂ) w * z).im = -(w * (starRingEnd ℂ) z).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    have h3 : ((a : ℂ) * w + (b : ℂ) * (starRingEnd ℂ) w) * ((a : ℂ) * (starRingEnd ℂ) z + (b : ℂ) * z) =
        ((a ^ 2 : ℝ) : ℂ) * (w * (starRingEnd ℂ) z) + ((b ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) w * z) +
          ((a * b : ℝ) : ℂ) * (w * z + (starRingEnd ℂ) (w * z)) := by
      simp only [map_mul]
      push_cast
      ring
    have h4 : (w * z + (starRingEnd ℂ) (w * z)).im = 0 := by simp; ring
    rw [h3, Complex.add_im, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul,
      Complex.im_ofReal_mul, h4, h2]
    have h5 : (a ^ 2 - b ^ 2) * (w * (starRingEnd ℂ) z).im = (w * (starRingEnd ℂ) z).im := by
      rw [hab, one_mul]
    linarith

lemma Bogoliubov.squeeze_apply (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) (z : ℂ) :
    (Bogoliubov.squeeze a b hab).toEquiv z = (a : ℂ) * z + (b : ℂ) * (starRingEnd ℂ) z :=
  squeezeMap_apply a b z

/-- **The antilinear part of the squeezing is `z ↦ b z̄`.** -/
theorem Bogoliubov.squeeze_betaPart (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) (z : ℂ) :
    (Bogoliubov.squeeze a b hab).betaPart z = (b : ℂ) * (starRingEnd ℂ) z := by
  unfold Bogoliubov.betaPart
  rw [Bogoliubov.squeeze_apply, Bogoliubov.squeeze_apply]
  simp only [smul_eq_mul, map_mul, conj_I]
  linear_combination ((1 / 2 : ℂ) * (a : ℂ) * z - (1 / 2 : ℂ) * (b : ℂ) * (starRingEnd ℂ) z) * Complex.I_mul_I

/-- **The one-mode squeezing is implemented** in every Fock representation of `ℂ`: with finitely many modes
every antilinear part is Hilbert-Schmidt. -/
theorem implements_squeeze {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (R : FockRep ℂ K) (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) :
    Implements R.toCCRRep (Bogoliubov.squeeze a b hab) := by
  refine shale_sufficiency_of_hilbertSchmidt R _ fun ι v => ?_
  have hfin : Finite ι := by
    exact v.orthonormal.linearIndependent.finite_of_isNoetherian
  have := Fintype.ofFinite ι
  exact (hasSum_fintype _).summable

end Lightlike.OperatorAlgebras
