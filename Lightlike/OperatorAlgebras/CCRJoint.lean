import Lightlike.OperatorAlgebras.FockUnique
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Joint strong continuity of the Weyl unitaries in finitely many degrees of freedom

A representation of the Weyl relations (`CCRRep`) is required to be strongly continuous along real lines,
`t ↦ W (t f) ψ`. In finite dimensions this gives joint strong continuity `z ↦ W z ψ`
(`CCRRep.continuous_W`): by the Weyl relation `W (t₀ f₀ + ∑ tᵢ fᵢ) = e^{iσ/2} W (t₀ f₀) W (∑ tᵢ fᵢ)` one basis
direction at a time, since a strongly continuous family of isometries is jointly continuous with its argument
(`continuous_apply_of_isometries`).
-/

open scoped InnerProductSpace
open Filter Topology

namespace Lightlike.OperatorAlgebras

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A strongly continuous family of isometries `U x` is jointly continuous in `(x, ψ)`. -/
lemma continuous_apply_of_isometries {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (U : X → K ≃ₗᵢ[ℂ] K)
    (hU : ∀ ψ, Continuous fun x => U x ψ) {x : Y → X} (hx : Continuous x) {v : Y → K} (hv : Continuous v) :
    Continuous fun y => U (x y) (v y) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  have h1 : Tendsto (fun y => U (x y) (v y₀)) (𝓝 y₀) (𝓝 (U (x y₀) (v y₀))) := ((hU (v y₀)).comp hx).continuousAt
  have h3 : Tendsto (fun y => U (x y) (v y) - U (x y) (v y₀)) (𝓝 y₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [← map_sub, LinearIsometryEquiv.norm_map]
    exact (tendsto_iff_norm_sub_tendsto_zero.mp hv.continuousAt)
  have := h1.add h3
  simp only [add_sub_cancel, add_zero] at this
  exact this

/-- The Weyl relation solved for `W (f + g)`: `W (f + g) ψ = e^{iσ(f, g)/2} W f (W g ψ)`. -/
lemma CCRRep.W_add_apply (R : CCRRep h K) (f g : h) (ψ : K) :
    R.W (f + g) ψ = Complex.exp (Complex.I * (symp h f g / 2 : ℝ)) • R.W f (R.W g ψ) := by
  rw [R.weyl, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]

lemma continuous_symp_pair : Continuous fun p : h × h => symp h p.1 p.2 := by
  unfold symp
  fun_prop

/-- **Joint continuity along finitely many directions**: `t ↦ W (∑ tᵢ fᵢ) ψ` is continuous on `ℝᵐ`. -/
lemma CCRRep.continuous_sum (R : CCRRep h K) : ∀ {m : ℕ} (f : Fin m → h) (ψ : K),
    Continuous fun t : Fin m → ℝ => R.W (∑ i, (t i : ℂ) • f i) ψ
  | 0, f, ψ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, R.W_zero_apply]
    exact continuous_const
  | m + 1, f, ψ => by
    have hrest : Continuous fun t : Fin (m + 1) → ℝ => R.W (∑ i : Fin m, (t i.succ : ℂ) • f i.succ) ψ :=
      (CCRRep.continuous_sum R (fun i => f i.succ) ψ).comp (continuous_pi fun i => continuous_apply i.succ)
    have hline : Continuous fun t : Fin (m + 1) → ℝ => ((t 0 : ℝ) : ℂ) • f 0 :=
      (Complex.continuous_ofReal.comp (continuous_apply 0)).smul continuous_const
    have hsum : Continuous fun t : Fin (m + 1) → ℝ => ∑ i : Fin m, (t i.succ : ℂ) • f i.succ :=
      continuous_finset_sum _ fun i _ =>
        (Complex.continuous_ofReal.comp (continuous_apply i.succ)).smul continuous_const
    have hphase : Continuous fun t : Fin (m + 1) → ℝ =>
        Complex.exp (Complex.I * (symp h ((t 0 : ℂ) • f 0) (∑ i : Fin m, (t i.succ : ℂ) • f i.succ) / 2 : ℝ)) := by
      have := continuous_symp_pair.comp (hline.prodMk hsum)
      exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (this.div_const 2)))
    have hW : Continuous fun t : Fin (m + 1) → ℝ =>
        R.W ((t 0 : ℂ) • f 0) (R.W (∑ i : Fin m, (t i.succ : ℂ) • f i.succ) ψ) :=
      continuous_apply_of_isometries (fun s : ℝ => R.W ((s : ℂ) • f 0)) (fun φ => R.continuous_line (f 0) φ)
        (continuous_apply 0) hrest
    refine (hphase.smul hW).congr fun t => ?_
    rw [Fin.sum_univ_succ, R.W_add_apply]
    rfl

/-- **Joint strong continuity**: for a finite-dimensional `h`, `z ↦ W z ψ` is continuous. -/
theorem CCRRep.continuous_W [FiniteDimensional ℂ h] (R : CCRRep h K) (ψ : K) : Continuous fun z => R.W z ψ := by
  let b := Module.finBasis ℝ h
  have hz : ∀ z : h, z = ∑ i, ((b.repr z i : ℝ) : ℂ) • b i := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    simp only [← Complex.coe_smul]
  have hc : Continuous fun z : h => fun i => b.repr z i :=
    continuous_pi fun i => (b.coord i).continuous_of_finiteDimensional
  refine ((R.continuous_sum b ψ).comp hc).congr fun z => ?_
  simp only [Function.comp_apply]
  rw [← hz]

end Lightlike.OperatorAlgebras
