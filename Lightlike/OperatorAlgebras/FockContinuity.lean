import Lightlike.OperatorAlgebras.FockIrreducible

/-!
# Norm continuity of the Weyl unitaries of a Fock representation

`CCRRep` asks for continuity of `t ↦ W (t f) ψ` along real lines only. In a Fock representation
`f ↦ W f ψ` is continuous for the norm topology of the one-particle space (`FockRep.continuous_W`): on the
coherent vectors `W g Ω` it follows from the Gram function, and the coherent vectors span a dense subspace.

Also the representation `f ↦ W (T f)` twisted by a Bogoliubov transformation (`Bogoliubov.twist`).
Helpers for the sufficiency part of Shale's criterion (`T-OP2-P7`, `Tasks/OP/T_OP2_P7.lean`).
-/

open scoped InnerProductSpace
open Complex

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_sq_kv_sub (R : FockRep h K) (a b : h) :
    ‖kv R a - kv R b‖ ^ 2 = 2 - 2 * (fockGram a b).re := by
  have h1 := norm_sub_sq (𝕜 := ℂ) (kv R a) (kv R b)
  rw [norm_kv, norm_kv, inner_kv] at h1
  rw [h1]
  change (1 : ℝ) ^ 2 - 2 * (fockGram a b).re + 1 ^ 2 = _
  ring

/-- The coherent vectors `W f Ω` depend continuously on `f`. -/
lemma continuous_kv (R : FockRep h K) : Continuous (kv R : h → K) := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun b : h => Real.sqrt (2 - 2 * (fockGram b a).re) := by
    have := continuous_fockGram.comp (continuous_id.prodMk (continuous_const (y := a)))
    exact (continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp this))).sqrt
  have h0 : Real.sqrt (2 - 2 * (fockGram a a).re) = 0 := by simp [fockGram_self]
  have := hc.tendsto a
  rw [h0] at this
  refine this.congr fun b => ?_
  rw [← Real.sqrt_sq (norm_nonneg (kv R b - kv R a)), norm_sq_kv_sub]

/-- **The Weyl unitaries of a Fock representation are strongly continuous** for the norm topology of the
one-particle space. -/
theorem FockRep.continuous_W (R : FockRep h K) (ψ : K) : Continuous fun f : h => R.W f ψ := by
  refine continuous_of_dense_isometries (fun f => R.W f) (dense_range_fockMap R) (fun χ hχ => ?_) ψ
  obtain ⟨c, rfl⟩ := hχ
  have hsum : fockMap R c = ∑ g ∈ c.support, c g • R.W g R.Ω := by
    unfold fockMap; rw [Finsupp.linearCombination_apply]; rfl
  rw [hsum]
  simp only [map_sum, map_smul]
  refine continuous_finset_sum _ fun g _ => Continuous.const_smul ?_ _
  have hs : Continuous fun f : h => symp h f g := by
    unfold symp
    exact Complex.continuous_im.comp (continuous_id.inner continuous_const)
  have hw : ∀ f, R.W f (R.W g R.Ω) =
      cexp (-(I * ((symp h f g / 2 : ℝ) : ℂ))) • kv R (f + g) := fun f => R.weyl f g R.Ω
  simp only [hw]
  exact (Complex.continuous_exp.comp
    ((continuous_const.mul (Complex.continuous_ofReal.comp (hs.div_const 2))).neg)).smul
    ((continuous_kv R).comp (continuous_id.add continuous_const))

/-- **The representation twisted by a Bogoliubov transformation**, `f ↦ W (T f)`: again a representation of
the Weyl relations, since `T` is real-linear and preserves the symplectic form. -/
noncomputable def Bogoliubov.twist (T : Bogoliubov h) (R : CCRRep h K) : CCRRep h K where
  W f := R.W (T.toEquiv f)
  W_zero := by rw [map_zero]; exact R.W_zero
  weyl f g ψ := by rw [R.weyl, T.symp_map, map_add]
  continuous_line f ψ := by
    have h1 : ∀ t : ℝ, T.toEquiv ((t : ℂ) • f) = (t : ℂ) • T.toEquiv f := fun t => by
      rw [Complex.coe_smul, map_smul, Complex.coe_smul]
    simp only [h1]
    exact R.continuous_line _ ψ

@[simp] lemma Bogoliubov.twist_W (T : Bogoliubov h) (R : CCRRep h K) (f : h) :
    (T.twist R).W f = R.W (T.toEquiv f) := rfl

end Lightlike.OperatorAlgebras
