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
    (hsymm : ∀ y a b, h y a b = h y b a) (hp : ∀ y, 0 < (h y).det) :
    hamiltonianConstraint N h π = ∫ x, firstOrderDensity N h π x := by
  set V : Fin d → (Fin d → ℝ) → ℝ := fun ρ y => Real.sqrt (h y).det * wJ (h y)⁻¹ (jet1 h y) ρ with hV
  have hVs : ∀ ρ, ContDiff ℝ ∞ (V ρ) := fun ρ => contDiff_sqrt_w hh hp ρ
  have hF : ∀ ρ, ContDiff ℝ ∞ (fun y => N y * V ρ y) := fun ρ => hN.mul (hVs ρ)
  have hFc : ∀ ρ, HasCompactSupport (fun y => N y * V ρ y) := fun ρ => hNc.mul_right
  obtain ⟨hPi, hP0⟩ := integral_sum_pd_eq_zero hF hFc
  have hham : ContDiff ℝ ∞ (hamiltonianDensity h π) := contDiff_hamiltonianDensity_of_det hh hπ hp
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

section Variation

open Matrix MeasureTheory Metric Set Filter

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- The parameters of the first-order density: the lapse, its gradient, the metric and momentum, the 1-jet. -/
abbrev Par (d : ℕ) := ℝ × (Fin d → ℝ) × (Arr d × H1arr d)

/-- The first-order Hamiltonian density as a function of its parameters. -/
def Phi1 (c : ℝ) (q : Par d) : ℝ :=
  q.1 * Kfun c q.2.2.1 -
      q.1 * (Real.sqrt (Matrix.of q.2.2.1.1).det * LgJ (Matrix.of q.2.2.1.1)⁻¹ q.2.2.2) +
    ∑ ρ, q.2.1 ρ * (Real.sqrt (Matrix.of q.2.2.1.1).det * wJ (Matrix.of q.2.2.1.1)⁻¹ q.2.2.2 ρ)

/-- The parameters at `x`. -/
def Z1 (N : (Fin d → ℝ) → ℝ) (g π : TensorField d) (x : Fin d → ℝ) : Par d :=
  (N x, fun ρ => Lightlike.pd ρ N x, (((fun a b => g x a b, fun a b => π x a b) : Arr d), jet1 g x))

/-- The direction of the variation `g + t k` of the parameters. -/
def V1 (k : TensorField d) (x : Fin d → ℝ) : Par d :=
  (0, 0, (((fun a b => k x a b, fun _ _ => 0) : Arr d), jet1 k x))

lemma firstOrderDensity_eq_Phi1 (N : (Fin d → ℝ) → ℝ) (g π : TensorField d) (x : Fin d → ℝ) :
    firstOrderDensity N g π x = Phi1 (1 / ((d : ℝ) - 1)) (Z1 N g π x) := by
  unfold firstOrderDensity Phi1 Z1
  rw [kineticDensity_eq_kinJ]
  rfl

lemma jet1_add_smul {h k : TensorField d} (hh : SmoothTensor h) (hk : SmoothTensor k) (t : ℝ)
    (x : Fin d → ℝ) : jet1 (fun y => h y + t • k y) x = jet1 h x + t • jet1 k x := by
  have := congrArg (fun J : Jet d => J.2.1) (jetAt_add_smul hh hk t x)
  simpa [jetAt] using this

lemma Z1_add_smul {N : (Fin d → ℝ) → ℝ} {h k π : TensorField d} (hh : SmoothTensor h) (hk : SmoothTensor k)
    (t : ℝ) (x : Fin d → ℝ) :
    Z1 N (fun y => h y + t • k y) π x = Z1 N h π x + t • V1 k x := by
  unfold Z1 V1
  refine Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext (Prod.ext ?_ ?_) ?_))
  · funext a b; simp
  · funext a b; simp
  · exact jet1_add_smul hh hk t x

lemma contDiffAt_Phi1 (c : ℝ) {q : Par d} (hdet : 0 < (Matrix.of q.2.2.1.1).det) :
    ContDiffAt ℝ ∞ (Phi1 c) q := by
  have h1 : ∀ i j, ContDiffAt ℝ ∞ (fun q : Par d => (Matrix.of q.2.2.1.1) i j) q := fun i j => by
    simp only [Matrix.of_apply]; fun_prop
  have hK : ContDiffAt ℝ ∞ (fun q : Par d => Kfun c q.2.2.1) q :=
    ContDiffAt.comp (g := Kfun c) (f := fun q : Par d => q.2.2.1) q (contDiffAt_Kfun c hdet) (by fun_prop)
  have hs : ContDiffAt ℝ ∞ (fun q : Par d => Real.sqrt (Matrix.of q.2.2.1.1).det) q :=
    (contDiffAt_det (fun q : Par d => Matrix.of q.2.2.1.1) h1).sqrt hdet.ne'
  have hZ : ContDiffAt ℝ ∞ (fun q : Par d => ((q.2.2.1.1, q.2.2.2) : (Fin d → Fin d → ℝ) × H1arr d)) q := by
    fun_prop
  have hL : ContDiffAt ℝ ∞ (fun q : Par d => LgJ (Matrix.of q.2.2.1.1)⁻¹ q.2.2.2) q :=
    ContDiffAt.comp (g := fun Z : (Fin d → Fin d → ℝ) × H1arr d => LgJ (Matrix.of Z.1)⁻¹ Z.2)
      (f := fun q : Par d => ((q.2.2.1.1, q.2.2.2) : (Fin d → Fin d → ℝ) × H1arr d)) q
      (contDiffAt_LgJ hdet.ne') hZ
  have hW : ∀ ρ, ContDiffAt ℝ ∞ (fun q : Par d => wJ (Matrix.of q.2.2.1.1)⁻¹ q.2.2.2 ρ) q := fun ρ =>
    ContDiffAt.comp (g := fun Z : (Fin d → Fin d → ℝ) × H1arr d => wJ (Matrix.of Z.1)⁻¹ Z.2 ρ)
      (f := fun q : Par d => ((q.2.2.1.1, q.2.2.2) : (Fin d → Fin d → ℝ) × H1arr d)) q
      (contDiffAt_wJ hdet.ne' ρ) hZ
  have hq1 : ContDiffAt ℝ ∞ (fun q : Par d => q.1) q := by fun_prop
  have hq2 : ∀ ρ, ContDiffAt ℝ ∞ (fun q : Par d => q.2.1 ρ) q := fun ρ => by fun_prop
  unfold Phi1
  exact ((hq1.mul hK).sub (hq1.mul (hs.mul hL))).add (ContDiffAt.sum fun ρ _ => (hq2 ρ).mul (hs.mul (hW ρ)))

lemma fderiv_eq_zero_of_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → ℝ) (q V : E)
    (h : ∀ t : ℝ, Φ (q + t • V) = 0) : fderiv ℝ Φ q V = 0 := by
  by_cases hd : DifferentiableAt ℝ Φ q
  · have hline : HasDerivAt (fun s : ℝ => q + s • V) V 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add q
      exact HasDerivAt.congr_deriv this (by simp)
    have h2 : HasFDerivAt Φ (fderiv ℝ Φ q) (q + (0 : ℝ) • V) := by simpa using hd.hasFDerivAt
    have h3 := h2.comp_hasDerivAt (0 : ℝ) hline
    have h4 : HasDerivAt (fun s : ℝ => Φ (q + s • V)) 0 0 := by
      have : (fun s : ℝ => Φ (q + s • V)) = fun _ => 0 := funext h
      rw [this]; exact hasDerivAt_const _ _
    exact h3.unique h4
  · simp [fderiv_zero_of_not_differentiableAt hd]

lemma continuous_Z1 {N : (Fin d → ℝ) → ℝ} (hN : ContDiff ℝ ∞ N) {h π : TensorField d} (hh : SmoothTensor h)
    (hπ : SmoothTensor π) : Continuous (Z1 N h π) := by
  unfold Z1
  refine Continuous.prodMk hN.continuous (Continuous.prodMk ?_ (Continuous.prodMk (Continuous.prodMk ?_ ?_) ?_))
  · exact continuous_pi fun ρ => (smooth_pd hN ρ).continuous
  · exact continuous_pi fun a => continuous_pi fun b => (hh a b).continuous
  · exact continuous_pi fun a => continuous_pi fun b => (hπ a b).continuous
  · exact continuous_pi fun k => continuous_pi fun a => continuous_pi fun b => (smooth_pd (hh a b) k).continuous

lemma continuous_V1 {k : TensorField d} (hk : SmoothTensor k) : Continuous (V1 k) := by
  unfold V1
  refine Continuous.prodMk continuous_const (Continuous.prodMk continuous_const
    (Continuous.prodMk (Continuous.prodMk ?_ continuous_const) ?_))
  · exact continuous_pi fun a => continuous_pi fun b => (hk a b).continuous
  · exact continuous_pi fun j => continuous_pi fun a => continuous_pi fun b => (smooth_pd (hk a b) j).continuous

set_option maxHeartbeats 1600000 in
/-- **Differentiation of the smeared Hamiltonian constraint along a compactly supported symmetric variation,
in first-order form**: `d/dt H[N](h + t k, π) = ∫ Φ₁'(Z₁ x)(V₁ x)`. -/
theorem dirDeriv_hamiltonianConstraint_first {N : (Fin d → ℝ) → ℝ} (hN : ContDiff ℝ ∞ N)
    (hNc : HasCompactSupport N) {h π k : TensorField d} (hh : SmoothTensor h) (hπ : SmoothTensor π)
    (hsymm : ∀ y a b, h y a b = h y b a) (hpos : ∀ y, (h y).PosDef) (hk : SmoothTensor k)
    (hkc : ∀ i j, HasCompactSupport (fun x => k x i j)) (hks : ∀ y a b, k y a b = k y b a) :
    Integrable (fun x => fderiv ℝ (Phi1 (1 / ((d : ℝ) - 1))) (Z1 N h π x) (V1 k x)) volume ∧
      dirDeriv (hamiltonianConstraint N) h π k 0 =
        ∫ x, fderiv ℝ (Phi1 (1 / ((d : ℝ) - 1))) (Z1 N h π x) (V1 k x) := by
  set c : ℝ := 1 / ((d : ℝ) - 1) with hc
  obtain ⟨ε, hε, hεdet⟩ := exists_eps_det hh hpos hkc hk
  have hWdet : ∀ t : ℝ, ∀ x, Matrix.of (Z1 N h π x + t • V1 k x).2.2.1.1 = h x + t • k x := by
    intro t x; ext a b; simp [Z1, V1]
  have hΦ : ∀ t : ℝ, |t| < ε → ∀ x, ContDiffAt ℝ 1 (Phi1 c) (Z1 N h π x + t • V1 k x) := by
    intro t ht x
    have := contDiffAt_Phi1 c (q := Z1 N h π x + t • V1 k x) (by rw [hWdet]; exact hεdet t ht x)
    exact this.of_le (by simp)
  have hzero : ∀ t : ℝ, ∀ x, x ∉ tsupport N →
      Phi1 c (Z1 N h π x + t • V1 k x) = 0 ∧ fderiv ℝ (Phi1 c) (Z1 N h π x + t • V1 k x) (V1 k x) = 0 := by
    intro t x hx
    have hN0 : N x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hdN0 : ∀ ρ, Lightlike.pd ρ N x = 0 := by
      intro ρ
      simp only [Lightlike.pd]
      have hev : N =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
      rw [hev.fderiv_eq (𝕜 := ℝ)]
      simp
    have hP : ∀ s : ℝ, Phi1 c (Z1 N h π x + t • V1 k x + s • V1 k x) = 0 := by
      intro s
      unfold Phi1
      simp [Z1, V1, hN0, hdN0]
    refine ⟨by simpa using hP 0, ?_⟩
    exact fderiv_eq_zero_of_line _ _ _ hP
  have hDI := integral_hasDerivAt_line (E := Par d) (Phi1 c) (Z1 N h π) (V1 k) hNc hε
    (continuous_Z1 hN hh hπ) (continuous_V1 hk) hΦ hzero
  have hint : ∀ᶠ t in 𝓝 (0 : ℝ), hamiltonianConstraint N (fun x => h x + t • k x) π =
      ∫ x, Phi1 c (Z1 N h π x + t • V1 k x) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    have ht' : |t| < ε := by simpa [Real.dist_eq] using mem_ball.mp ht
    have hg : SmoothTensor (fun y => h y + t • k y) := smoothTensor_add_smul hh hk t
    have hgs : ∀ y a b, (fun y => h y + t • k y) y a b = (fun y => h y + t • k y) y b a := by
      intro y a b; simp [hsymm y a b, hks y a b]
    rw [hamiltonianConstraint_eq_firstOrder hN hNc hg hπ hgs (fun y => hεdet t ht' y)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [firstOrderDensity_eq_Phi1, Z1_add_smul hh hk t x]
  refine ⟨hDI.1, ?_⟩
  have hDD := hDI.2.congr_of_eventuallyEq hint
  unfold dirDeriv
  simp only [Pi.zero_apply, smul_zero, add_zero]
  exact hDD.deriv

end Lightlike.Canonical

end

end Variation



section Split

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- The part of the first-order density multiplying the lapse: `K − √h L`. -/
def Psi (c : ℝ) (z : Arr d × H1arr d) : ℝ :=
  Kfun c z.1 - Real.sqrt (Matrix.of z.1.1).det * LgJ (Matrix.of z.1.1)⁻¹ z.2

/-- The part multiplying `∂_ρ N`: `√h w^ρ`. -/
def Theta (ρ : Fin d) (z : Arr d × H1arr d) : ℝ :=
  Real.sqrt (Matrix.of z.1.1).det * wJ (Matrix.of z.1.1)⁻¹ z.2 ρ

lemma Phi1_eq (c : ℝ) (q : Par d) :
    Phi1 c q = q.1 * Psi c q.2.2 + ∑ ρ, q.2.1 ρ * Theta ρ q.2.2 := by
  unfold Phi1 Psi Theta
  ring

lemma contDiffAt_Psi (c : ℝ) {z : Arr d × H1arr d} (hdet : 0 < (Matrix.of z.1.1).det) :
    ContDiffAt ℝ ∞ (Psi c) z := by
  have := contDiffAt_Phi1 c (q := ((1 : ℝ), (fun _ => (0 : ℝ)), z)) (by simpa using hdet)
  have e : Psi c = fun z : Arr d × H1arr d => Phi1 c ((1 : ℝ), (fun _ : Fin d => (0 : ℝ)), z) := by
    funext z; rw [Phi1_eq]; simp
  rw [e]
  exact ContDiffAt.comp (g := Phi1 c) (f := fun z : Arr d × H1arr d => ((1 : ℝ), (fun _ => (0 : ℝ)), z)) z
    this (by fun_prop)

lemma contDiffAt_Theta (ρ : Fin d) {z : Arr d × H1arr d} (hdet : 0 < (Matrix.of z.1.1).det) :
    ContDiffAt ℝ ∞ (Theta ρ) z := by
  have := contDiffAt_Phi1 1 (q := ((0 : ℝ), (fun r => if r = ρ then (1 : ℝ) else 0), z)) (by simpa using hdet)
  have e : Theta ρ = fun z : Arr d × H1arr d => Phi1 1 ((0 : ℝ), (fun r : Fin d => if r = ρ then (1 : ℝ) else 0), z) := by
    funext z; rw [Phi1_eq]; simp [Theta]
  rw [e]
  exact ContDiffAt.comp (g := Phi1 1)
    (f := fun z : Arr d × H1arr d => ((0 : ℝ), (fun r => if r = ρ then (1 : ℝ) else 0), z)) z this (by fun_prop)

/-- **The derivative of `Φ₁` in a direction that does not change the lapse and its gradient.** -/
lemma fderiv_Phi1_third (c : ℝ) {q : Par d} (hdet : 0 < (Matrix.of q.2.2.1.1).det)
    (V3 : Arr d × H1arr d) :
    fderiv ℝ (Phi1 c) q ((0 : ℝ), (0 : Fin d → ℝ), V3) =
      q.1 * fderiv ℝ (Psi c) q.2.2 V3 + ∑ ρ, q.2.1 ρ * fderiv ℝ (Theta ρ) q.2.2 V3 := by
  have hline3 : HasDerivAt (fun s : ℝ => q.2.2 + s • V3) V3 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const V3).const_add q.2.2
    exact HasDerivAt.congr_deriv this (by simp)
  have hΨ : HasDerivAt (fun s : ℝ => Psi c (q.2.2 + s • V3)) (fderiv ℝ (Psi c) q.2.2 V3) 0 := by
    have h2 : HasFDerivAt (Psi c) (fderiv ℝ (Psi c) q.2.2) (q.2.2 + (0 : ℝ) • V3) := by
      simpa using ((contDiffAt_Psi c hdet).differentiableAt (by simp)).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) hline3
  have hΘ : ∀ ρ, HasDerivAt (fun s : ℝ => Theta ρ (q.2.2 + s • V3)) (fderiv ℝ (Theta ρ) q.2.2 V3) 0 := by
    intro ρ
    have h2 : HasFDerivAt (Theta ρ) (fderiv ℝ (Theta ρ) q.2.2) (q.2.2 + (0 : ℝ) • V3) := by
      simpa using ((contDiffAt_Theta ρ hdet).differentiableAt (by simp)).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) hline3
  have hsum : HasDerivAt (fun s : ℝ => q.1 * Psi c (q.2.2 + s • V3) + ∑ ρ, q.2.1 ρ * Theta ρ (q.2.2 + s • V3))
      (q.1 * fderiv ℝ (Psi c) q.2.2 V3 + ∑ ρ, q.2.1 ρ * fderiv ℝ (Theta ρ) q.2.2 V3) 0 :=
    (hΨ.const_mul q.1).add (HasDerivAt.fun_sum fun ρ _ => (hΘ ρ).const_mul (q.2.1 ρ))
  have hline : HasDerivAt (fun s : ℝ => q + s • ((0 : ℝ), (0 : Fin d → ℝ), V3)) ((0 : ℝ), (0 : Fin d → ℝ), V3) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const ((0 : ℝ), (0 : Fin d → ℝ), V3)).const_add q
    exact HasDerivAt.congr_deriv this (by simp)
  have h2 : HasFDerivAt (Phi1 c) (fderiv ℝ (Phi1 c) q) (q + (0 : ℝ) • ((0 : ℝ), (0 : Fin d → ℝ), V3)) := by
    simpa using ((contDiffAt_Phi1 c hdet).differentiableAt (by simp)).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) hline
  have e : (Phi1 c ∘ fun s : ℝ => q + s • ((0 : ℝ), (0 : Fin d → ℝ), V3)) =
      fun s : ℝ => q.1 * Psi c (q.2.2 + s • V3) + ∑ ρ, q.2.1 ρ * Theta ρ (q.2.2 + s • V3) := by
    funext s
    simp only [Function.comp, Phi1_eq]
    simp
  rw [e] at h3
  exact h3.unique hsum

end Lightlike.Canonical

end

end Split
