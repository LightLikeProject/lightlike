import Mathlib
import Lightlike.Canonical.FirstOrderPotential
import Lightlike.Canonical.HamiltonianBracket
import Lightlike.Canonical.LineIntegral

/-!
# The smeared Hamiltonian constraint with first derivatives of the metric only

After one integration by parts, `H[N] = ∫ (N K − N √h L + ∂_ρ N √h w^ρ)`, with the Einstein `ΓΓ` Lagrangian `L`
and the vector `w^ρ` of `Lightlike/Canonical/FirstOrderPotential.lean` (`hamiltonianConstraint_eq_firstOrder`).
-/

open Matrix MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

lemma contDiff_inv_comp {g : TensorField d} (hg : SmoothTensor g) (hdet : ∀ y, (g y).det ≠ 0) (a b : Fin d) :
    ContDiff ℝ ∞ (fun y => (g y)⁻¹ a b) := by
  rw [contDiff_iff_contDiffAt]
  exact fun y => contDiffAt_inv_entry g (fun i j => (hg i j).contDiffAt) (hdet y) a b

lemma contDiff_christoffel {g : TensorField d} (hg : SmoothTensor g) (hdet : ∀ y, (g y).det ≠ 0) (i j k : Fin d) :
    ContDiff ℝ ∞ (fun y => Lightlike.christoffel g i j k y) := by
  have e : (fun y => Lightlike.christoffel g i j k y) = fun y => (1 / 2 : ℝ) * ∑ l, (g y)⁻¹ i l *
      (Lightlike.pd j (fun y => g y l k) y + Lightlike.pd k (fun y => g y l j) y -
        Lightlike.pd l (fun y => g y j k) y) := rfl
  rw [e]
  exact contDiff_const.mul (ContDiff.sum fun l _ => (contDiff_inv_comp hg hdet i l).mul
    (((smooth_pd (hg l k) j).add (smooth_pd (hg l j) k)).sub (smooth_pd (hg j k) l)))

lemma contDiff_sqrt_det {g : TensorField d} (hg : SmoothTensor g) (hpos : ∀ y, 0 < (g y).det) :
    ContDiff ℝ ∞ (fun y => Real.sqrt (g y).det) := by
  have hdet : ContDiff ℝ ∞ (fun y => (g y).det) := by
    rw [contDiff_iff_contDiffAt]
    exact fun y => contDiffAt_det (x := y) g (fun a b => (hg a b).contDiffAt)
  exact hdet.sqrt fun y => (hpos y).ne'

/-- `√h w^ρ` is smooth. -/
lemma contDiff_sqrt_w {g : TensorField d} (hg : SmoothTensor g) (hpos : ∀ y, 0 < (g y).det) (ρ : Fin d) :
    ContDiff ℝ ∞ (fun y => Real.sqrt (g y).det * wJ (g y)⁻¹ (jet1 g y) ρ) := by
  have hdet : ∀ y, (g y).det ≠ 0 := fun y => (hpos y).ne'
  have hw : (fun y => wJ (g y)⁻¹ (jet1 g y) ρ) = fun y =>
      (∑ σ, ∑ ν, (g y)⁻¹ σ ν * Lightlike.christoffel g ρ σ ν y) -
        ∑ σ, (g y)⁻¹ ρ σ * ∑ l, Lightlike.christoffel g l σ l y := rfl
  have : ContDiff ℝ ∞ (fun y => wJ (g y)⁻¹ (jet1 g y) ρ) := by
    rw [hw]
    exact (ContDiff.sum fun σ _ => ContDiff.sum fun ν _ => (contDiff_inv_comp hg hdet σ ν).mul
      (contDiff_christoffel hg hdet ρ σ ν)).sub
      (ContDiff.sum fun σ _ => (contDiff_inv_comp hg hdet ρ σ).mul
        (ContDiff.sum fun l _ => contDiff_christoffel hg hdet l σ l))
  exact (contDiff_sqrt_det hg hpos).mul this

end Lightlike.Canonical

end

section Smooth

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- The 1-jet arrays `∂_k h_ab`. -/
abbrev H1arr (d : ℕ) := Fin d → Fin d → Fin d → ℝ

lemma contDiffAt_gamJ {Z : (Fin d → Fin d → ℝ) × H1arr d} (hdet : (Matrix.of Z.1).det ≠ 0) (i j k : Fin d) :
    ContDiffAt ℝ ∞ (fun Z : (Fin d → Fin d → ℝ) × H1arr d => gamJ (Matrix.of Z.1)⁻¹ Z.2 i j k) Z := by
  have hHi : ∀ a b, ContDiffAt ℝ ∞ (fun Z : (Fin d → Fin d → ℝ) × H1arr d => ((Matrix.of Z.1)⁻¹) a b) Z :=
    fun a b => contDiffAt_inv_entry (fun Z : (Fin d → Fin d → ℝ) × H1arr d => Matrix.of Z.1)
      (fun i j => by simp only [Matrix.of_apply]; fun_prop) hdet a b
  have h1 : ∀ a b c, ContDiffAt ℝ ∞ (fun Z : (Fin d → Fin d → ℝ) × H1arr d => Z.2 a b c) Z :=
    fun a b c => by fun_prop
  unfold gamJ
  exact contDiffAt_const.mul (ContDiffAt.sum fun l _ => (hHi i l).mul (((h1 j l k).add (h1 k l j)).sub (h1 l j k)))

lemma contDiffAt_LgJ {Z : (Fin d → Fin d → ℝ) × H1arr d} (hdet : (Matrix.of Z.1).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun Z : (Fin d → Fin d → ℝ) × H1arr d => LgJ (Matrix.of Z.1)⁻¹ Z.2) Z := by
  have hHi : ∀ a b, ContDiffAt ℝ ∞ (fun Z : (Fin d → Fin d → ℝ) × H1arr d => ((Matrix.of Z.1)⁻¹) a b) Z :=
    fun a b => contDiffAt_inv_entry (fun Z : (Fin d → Fin d → ℝ) × H1arr d => Matrix.of Z.1)
      (fun i j => by simp only [Matrix.of_apply]; fun_prop) hdet a b
  unfold LgJ
  exact ContDiffAt.sum fun σ _ => ContDiffAt.sum fun ν _ => (hHi σ ν).mul
    (ContDiffAt.sum fun ρ _ => ContDiffAt.sum fun l _ =>
      (((contDiffAt_gamJ hdet ρ l σ).mul (contDiffAt_gamJ hdet l ρ ν)).sub
        ((contDiffAt_gamJ hdet ρ σ ν).mul (contDiffAt_gamJ hdet l ρ l))))

lemma contDiffAt_wJ {Z : (Fin d → Fin d → ℝ) × H1arr d} (hdet : (Matrix.of Z.1).det ≠ 0) (ρ : Fin d) :
    ContDiffAt ℝ ∞ (fun Z : (Fin d → Fin d → ℝ) × H1arr d => wJ (Matrix.of Z.1)⁻¹ Z.2 ρ) Z := by
  have hHi : ∀ a b, ContDiffAt ℝ ∞ (fun Z : (Fin d → Fin d → ℝ) × H1arr d => ((Matrix.of Z.1)⁻¹) a b) Z :=
    fun a b => contDiffAt_inv_entry (fun Z : (Fin d → Fin d → ℝ) × H1arr d => Matrix.of Z.1)
      (fun i j => by simp only [Matrix.of_apply]; fun_prop) hdet a b
  unfold wJ
  exact (ContDiffAt.sum fun σ _ => ContDiffAt.sum fun ν _ => (hHi σ ν).mul (contDiffAt_gamJ hdet ρ σ ν)).sub
    (ContDiffAt.sum fun σ _ => (hHi ρ σ).mul (ContDiffAt.sum fun l _ => contDiffAt_gamJ hdet l σ l))

end Lightlike.Canonical

end

end Smooth

section Integrated

open Matrix MeasureTheory

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

lemma contDiff_jetPair {g π : TensorField d} (hg : SmoothTensor g) (hπ : SmoothTensor π) :
    ContDiff ℝ ∞ (fun y => (((fun a b => g y a b, jet1 g y) : (Fin d → Fin d → ℝ) × H1arr d),
      (fun a b => π y a b : Fin d → Fin d → ℝ))) := by
  refine ContDiff.prodMk (ContDiff.prodMk ?_ ?_) ?_
  · exact contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => hg a b
  · exact contDiff_pi.mpr fun k => contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => smooth_pd (hg a b) k
  · exact contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => hπ a b

/-- `√h L` is smooth. -/
lemma contDiff_sqrt_L {g : TensorField d} (hg : SmoothTensor g) (hpos : ∀ y, 0 < (g y).det) :
    ContDiff ℝ ∞ (fun y => Real.sqrt (g y).det * LgJ (g y)⁻¹ (jet1 g y)) := by
  have hz : ContDiff ℝ ∞ (fun y => ((fun a b => g y a b, jet1 g y) : (Fin d → Fin d → ℝ) × H1arr d)) := by
    refine ContDiff.prodMk ?_ ?_
    · exact contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => hg a b
    · exact contDiff_pi.mpr fun k => contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => smooth_pd (hg a b) k
  have hL : ContDiff ℝ ∞ (fun y => LgJ (g y)⁻¹ (jet1 g y)) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have h0 : (Matrix.of (((fun a b => g y a b, jet1 g y) : (Fin d → Fin d → ℝ) × H1arr d).1)).det ≠ 0 := by
      show (g y).det ≠ 0
      exact (hpos y).ne'
    exact ContDiffAt.comp (g := fun Z : (Fin d → Fin d → ℝ) × H1arr d => LgJ (Matrix.of Z.1)⁻¹ Z.2)
      (f := fun y => ((fun a b => g y a b, jet1 g y) : (Fin d → Fin d → ℝ) × H1arr d)) y
      (contDiffAt_LgJ h0) hz.contDiffAt
  exact (contDiff_sqrt_det hg hpos).mul hL

/-- The kinetic density of smooth data is smooth. -/
lemma contDiff_kineticDensity {g π : TensorField d} (hg : SmoothTensor g) (hπ : SmoothTensor π)
    (hpos : ∀ y, 0 < (g y).det) : ContDiff ℝ ∞ (kineticDensity g π) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hz : ContDiff ℝ ∞ (fun y => ((fun a b => g y a b, fun a b => π y a b) : Arr d)) :=
    ContDiff.prodMk (contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => hg a b)
      (contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => hπ a b)
  have := (contDiffAt_Kfun (1 / ((d : ℝ) - 1)) (Z := ((fun a b => g y a b, fun a b => π y a b) : Arr d))
    (by show 0 < (g y).det; exact hpos y)).comp y hz.contDiffAt
  exact this

/-- The first-order density of the smeared Hamiltonian constraint:
`N K − N √h L + ∂_ρ N √h w^ρ`. -/
def firstOrderDensity (N : (Fin d → ℝ) → ℝ) (h π : TensorField d) (x : Fin d → ℝ) : ℝ :=
  N x * kineticDensity h π x - N x * (Real.sqrt (h x).det * LgJ (h x)⁻¹ (jet1 h x)) +
    ∑ ρ, Lightlike.pd ρ N x * (Real.sqrt (h x).det * wJ (h x)⁻¹ (jet1 h x) ρ)

/-- **The smeared Hamiltonian constraint in first-order form**, after one integration by parts. -/
theorem hamiltonianConstraint_eq_firstOrder {N : (Fin d → ℝ) → ℝ} (hN : ContDiff ℝ ∞ N)
    (hNc : HasCompactSupport N) {h π : TensorField d} (hh : SmoothTensor h) (hπ : SmoothTensor π)
    (hsymm : ∀ y a b, h y a b = h y b a) (hpos : ∀ y, (h y).PosDef) :
    hamiltonianConstraint N h π = ∫ x, firstOrderDensity N h π x := by
  have hp : ∀ y, 0 < (h y).det := fun y => (hpos y).det_pos
  set V : Fin d → (Fin d → ℝ) → ℝ := fun ρ y => Real.sqrt (h y).det * wJ (h y)⁻¹ (jet1 h y) ρ with hV
  have hVs : ∀ ρ, ContDiff ℝ ∞ (V ρ) := fun ρ => contDiff_sqrt_w hh hp ρ
  have hF : ∀ ρ, ContDiff ℝ ∞ (fun y => N y * V ρ y) := fun ρ => hN.mul (hVs ρ)
  have hFc : ∀ ρ, HasCompactSupport (fun y => N y * V ρ y) := fun ρ => hNc.mul_right
  obtain ⟨hPi, hP0⟩ := integral_sum_pd_eq_zero hF hFc
  have hham : ContDiff ℝ ∞ (hamiltonianDensity h π) := contDiff_hamiltonianDensity hh hπ hpos
  have hK := contDiff_kineticDensity hh hπ hp
  have hL := contDiff_sqrt_L hh hp
  -- the first-order density is integrable
  have hFOi : Integrable (fun x => firstOrderDensity N h π x) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · unfold firstOrderDensity
      exact (((hN.continuous.mul hK.continuous).sub (hN.continuous.mul hL.continuous))).add
        (continuous_finsetSum _ fun ρ _ => (smooth_pd hN ρ).continuous.mul (hVs ρ).continuous)
    · unfold firstOrderDensity
      refine HasCompactSupport.add (HasCompactSupport.sub (hNc.mul_right) (hNc.mul_right)) ?_
      exact hcs_sum _ _ fun ρ _ => (hNc.fderiv_apply (𝕜 := ℝ) (Pi.single ρ 1)).mul_right
  have hpt : ∀ x, N x * hamiltonianDensity h π x = firstOrderDensity N h π x -
      ∑ ρ, Lightlike.pd ρ (fun y => N y * V ρ y) x := by
    intro x
    have hs := sqrtDet_mul_scalar hh hsymm (hp x)
    have hpdV : ∀ ρ, Lightlike.pd ρ (fun y => N y * V ρ y) x =
        Lightlike.pd ρ N x * V ρ x + N x * Lightlike.pd ρ (V ρ) x := fun ρ =>
      Lightlike.pd_mul (diff_of_smooth hN x) (diff_of_smooth (hVs ρ) x) ρ
    simp only [hpdV, Finset.sum_add_distrib]
    unfold firstOrderDensity hamiltonianDensity
    have e : N x * (kineticDensity h π x - Real.sqrt (h x).det * Lightlike.scalarCurvature h x) =
        N x * kineticDensity h π x - N x * (Real.sqrt (h x).det * Lightlike.scalarCurvature h x) := by ring
    rw [e, hs]
    have e2 : N x * (Real.sqrt (h x).det * LgJ (h x)⁻¹ (jet1 h x) + ∑ ρ, Lightlike.pd ρ (V ρ) x) =
        N x * (Real.sqrt (h x).det * LgJ (h x)⁻¹ (jet1 h x)) + ∑ ρ, N x * Lightlike.pd ρ (V ρ) x := by
      rw [mul_add, Finset.mul_sum]
    rw [e2]
    simp only [hV]
    ring
  unfold hamiltonianConstraint
  have : ∀ x, N x * hamiltonianDensity h π x = firstOrderDensity N h π x -
      ∑ ρ, Lightlike.pd ρ (fun y => N y * V ρ y) x := hpt
  simp only [this]
  rw [integral_sub hFOi hPi, hP0, sub_zero]

end Lightlike.Canonical

end

end Integrated
