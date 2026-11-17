import Mathlib
import Lightlike.Canonical.HamiltonianSmooth
import Lightlike.Canonical.PiGradient
import Lightlike.Canonical.PairingCovariance
import Lightlike.Canonical.IntegrationByParts

/-!
# The bracket of a smeared momentum constraint with a smeared Hamiltonian constraint

`{D[ξ], H[N]} = H[ξ^k ∂_k N]` for smooth compactly supported `ξ`, `N` and smooth data with positive definite `h`.
-/

open Matrix MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

lemma contDiff_Zpt {h π : TensorField d} (hh : SmoothTensor h) (hπ : SmoothTensor π) :
    ContDiff ℝ ∞ (fun y => Zpt h π y) := by
  refine ContDiff.prodMk (ContDiff.prodMk ?_ ?_) ?_
  · exact contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => hh a b
  · exact contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => hπ a b
  · exact ContDiff.prodMk (contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => hh a b)
      (ContDiff.prodMk
        (contDiff_pi.mpr fun k => contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => smooth_pd (hh a b) k)
        (contDiff_pi.mpr fun k => contDiff_pi.mpr fun l => contDiff_pi.mpr fun a => contDiff_pi.mpr fun b =>
          smooth_pd (smooth_pd (hh a b) l) k))

/-- **The Hamiltonian density of smooth data is smooth.** -/
theorem contDiff_hamiltonianDensity {h π : TensorField d} (hh : SmoothTensor h) (hπ : SmoothTensor π)
    (hpos : ∀ y, (h y).PosDef) : ContDiff ℝ ∞ (hamiltonianDensity h π) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hH : 0 < (h y).det := (hpos y).det_pos
  have e : hamiltonianDensity h π = fun z => Phi (1 / ((d : ℝ) - 1)) (Zpt h π z) := by
    funext z; exact hamiltonianDensity_eq_Phi hh (hpos z).det_pos
  rw [e]
  have hΦ : ContDiffAt ℝ ∞ (Phi (1 / ((d : ℝ) - 1))) (Zpt h π y) :=
    contDiffAt_Phi _ (by show 0 < (h y).det; exact hH) (by show (h y).det ≠ 0; exact hH.ne')
  exact hΦ.comp y (contDiff_Zpt hh hπ).contDiffAt

/-- The `π`-gradient of the Hamiltonian constraint is a smooth tensor field for smooth data. -/
theorem smoothTensor_hamiltonianPiGradient {N : (Fin d → ℝ) → ℝ} (hN : ContDiff ℝ ∞ N) {h π : TensorField d}
    (hh : SmoothTensor h) (hπ : SmoothTensor π) (hpos : ∀ y, (h y).PosDef) :
    SmoothTensor (hamiltonianPiGradient N h π) := by
  intro i j
  have hdet : ContDiff ℝ ∞ (fun y => (h y).det) := by
    rw [contDiff_iff_contDiffAt]
    exact fun y => contDiffAt_det (x := y) h (fun a b => (hh a b).contDiffAt)
  have hs : ContDiff ℝ ∞ (fun y => Real.sqrt (h y).det) :=
    hdet.sqrt fun y => (hpos y).det_pos.ne'
  have hHP : ∀ a b, ContDiff ℝ ∞ (fun y => (h y * π y) a b) := fun a b => by
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun k _ => (hh a k).mul (hπ k b)
  have hHPH : ∀ a b, ContDiff ℝ ∞ (fun y => (h y * π y * h y) a b) := fun a b => by
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun k _ => (hHP a k).mul (hh k b)
  have htr : ContDiff ℝ ∞ (fun y => (h y * π y).trace) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact ContDiff.sum fun a _ => hHP a a
  unfold hamiltonianPiGradient
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, two_nsmul, Matrix.add_apply]
  exact (hN.div hs fun y => (Real.sqrt_pos.mpr (hpos y).det_pos).ne').mul
    (((hHPH j i).add (hHPH j i)).sub ((contDiff_const.mul htr).mul (hh j i)))

/-- The pointwise identity behind `{D[ξ], H[N]} = H[ξ^k ∂_k N]`: the integrand of `D[ξ](Gπ, π) − dH[N](ℒ_ξ h)`
minus that of `H[ξ^k ∂_k N]` is a sum of coordinate derivatives. -/
theorem bracket_pointwise {ξ : VectorField d} {N : (Fin d → ℝ) → ℝ}
    (hξ : SmoothVec ξ) (hN : ContDiff ℝ ∞ N) {h π : TensorField d}
    (hh : SmoothTensor h) (hpos : ∀ x, (h x).PosDef) (hπ : SmoothTensor π) (x : Fin d → ℝ) :
    momentumDensity ξ (hamiltonianPiGradient N h π) π x -
        N x * hamDirDeriv h π (lieTensor ξ h) x =
      (∑ k, ξ x k * Lightlike.pd k N x) * hamiltonianDensity h π x +
        (∑ k, Lightlike.pd k (fun y => ξ y k * ∑ i, ∑ j, π y i j * hamiltonianPiGradient N h π y i j) x -
          ∑ k, Lightlike.pd k (fun y => N y * (ξ y k * hamiltonianDensity h π y)) x) := by
  have hG : SmoothTensor (hamiltonianPiGradient N h π) := smoothTensor_hamiltonianPiGradient hN hh hπ hpos
  have hham : ContDiff ℝ ∞ (hamiltonianDensity h π) := contDiff_hamiltonianDensity hh hπ hpos
  have hH : 0 < (h x).det := (hpos x).det_pos
  have hpair := pairing_covariance hξ hG hπ x
  have hdens : hamDerivH ξ h π x + dkinJ (1 / ((d : ℝ) - 1)) (h x) (π x) 0 (lieDens ξ π x) =
      ∑ k, Lightlike.pd k (fun y => ξ y k * hamiltonianDensity h π y) x := hamDerivH_add_pi hξ hh hπ hpos x
  have hgrad := hamiltonianPiGradient_pairing N h π x hH (lieDens ξ π x)
  rw [← hamDerivH_eq_dir hξ hh hpos x]
  have hmd : momentumDensity ξ (hamiltonianPiGradient N h π) π x =
      ∑ i, ∑ j, π x i j * lieDeriv ξ (hamiltonianPiGradient N h π) i j x := rfl
  have hP2 : ∀ k, Lightlike.pd k (fun y => N y * (ξ y k * hamiltonianDensity h π y)) x =
      Lightlike.pd k N x * (ξ x k * hamiltonianDensity h π x) +
        N x * Lightlike.pd k (fun y => ξ y k * hamiltonianDensity h π y) x := by
    intro k
    exact Lightlike.pd_mul (diff_of_smooth hN x)
      (diff_of_smooth ((hξ k).mul hham) x) k
  simp only [hP2, Finset.sum_add_distrib]
  have e1 : ∑ i, ∑ j, (π x i j * lieDeriv ξ (hamiltonianPiGradient N h π) i j x +
      hamiltonianPiGradient N h π x i j * lieDens ξ π x i j) =
      (∑ i, ∑ j, π x i j * lieDeriv ξ (hamiltonianPiGradient N h π) i j x) +
        ∑ i, ∑ j, hamiltonianPiGradient N h π x i j * lieDens ξ π x i j := by
    simp only [Finset.sum_add_distrib]
  have e2 : (∑ k, ξ x k * Lightlike.pd k N x) * hamiltonianDensity h π x =
      ∑ k, Lightlike.pd k N x * (ξ x k * hamiltonianDensity h π x) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
  have e3 : N x * ∑ k, Lightlike.pd k (fun y => ξ y k * hamiltonianDensity h π y) x =
      ∑ k, N x * Lightlike.pd k (fun y => ξ y k * hamiltonianDensity h π y) x := by rw [Finset.mul_sum]
  rw [e1] at hpair
  rw [hmd]
  rw [e2]
  have hN' : N x * (∑ k, Lightlike.pd k (fun y => ξ y k * hamiltonianDensity h π y) x -
      dkinJ (1 / ((d : ℝ) - 1)) (h x) (π x) 0 (lieDens ξ π x)) = N x * hamDerivH ξ h π x := by
    rw [← hdens]; ring
  linear_combination hpair - N x * hdens + hgrad - e3

/-- **The bracket of a smeared momentum constraint with a smeared Hamiltonian constraint**:
`{D[ξ], H[N]} = H[ξ^k ∂_k N]`, for smooth compactly supported `ξ`, `N` and smooth data `(h, π)` with `h` positive
definite and `π` symmetric (the symmetry is not used in the proof).

The comparison with the cited source (Hojman-Kuchar-Teitelboim 1976; Thiemann 2007, Chapter 1) is pending: neither
has been read. Differences to be approved: (a) `C^∞` data and compactly supported test fields, `h` positive
definite; (b) one global chart `ℝᵈ`, no manifold and no foliation; (c) units `16πG = 1` and the kinetic coefficient
`1/(d - 1)` (`1/2` for `d = 3`); (d) the momentum constraint in the Lie-derivative form; (e) the bracket through
`π`-gradients and Gateaux derivatives, and the sign conventions of `admBracket` and `lieBracket`. A grid
computation in dimension two (`scripts/adm_algebra_check.py`) agrees with the statement to three digits. -/
theorem bracket_momentum_hamiltonian {ξ : VectorField d} {N : (Fin d → ℝ) → ℝ}
    (hξ : SmoothVec ξ) (hξc : ∀ k, HasCompactSupport (fun y => ξ y k))
    (hN : ContDiff ℝ ∞ N) (hNc : HasCompactSupport N) {h π : TensorField d}
    (hh : SmoothTensor h) (hpos : ∀ x, (h x).PosDef) (hπ : SmoothTensor π) (hπs : ∀ x, (π x)ᵀ = π x) :
    admBracket (momentumConstraint ξ) (hamiltonianConstraint N) (fun h _ => lieTensor ξ h)
        (hamiltonianPiGradient N) h π =
      hamiltonianConstraint (fun x => ∑ k, ξ x k * Lightlike.pd k N x) h π := by
  set G := hamiltonianPiGradient N h π with hGdef
  have hG : SmoothTensor G := smoothTensor_hamiltonianPiGradient hN hh hπ hpos
  have hπc : ∀ i j, Continuous (fun x => π x i j) := fun i j => (hπ i j).continuous
  have hL : SmoothTensor (lieTensor ξ h) := smoothTensor_lieTensor hh hξ
  have hLc : ∀ i j, HasCompactSupport (fun x => lieTensor ξ h x i j) := fun i j => hcs_lieDeriv hξc h i j
  have h1 := dirDeriv_momentum_h hξ hξc hh hG hπc
  have h2 := dirDeriv_hamiltonianConstraint hN hNc hh hpos hπc hL hLc
  unfold admBracket
  rw [h1, h2.2]
  have hham : ContDiff ℝ ∞ (hamiltonianDensity h π) := contDiff_hamiltonianDensity hh hπ hpos
  have hA := integrable_momentumDensity hG hξ hξc hπc
  have hB := h2.1
  -- the derivative-sum terms
  have hF1 : ∀ k, ContDiff ℝ ∞ (fun y => ξ y k * ∑ i, ∑ j, π y i j * G y i j) := fun k =>
    (hξ k).mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hπ i j).mul (hG i j))
  have hF1c : ∀ k, HasCompactSupport (fun y => ξ y k * ∑ i, ∑ j, π y i j * G y i j) := fun k =>
    (hξc k).mul_right
  have hF2 : ∀ k, ContDiff ℝ ∞ (fun y => N y * (ξ y k * hamiltonianDensity h π y)) := fun k =>
    hN.mul ((hξ k).mul hham)
  have hF2c : ∀ k, HasCompactSupport (fun y => N y * (ξ y k * hamiltonianDensity h π y)) := fun k =>
    hNc.mul_right
  obtain ⟨hP1i, hP1⟩ := integral_sum_pd_eq_zero hF1 hF1c
  obtain ⟨hP2i, hP2⟩ := integral_sum_pd_eq_zero hF2 hF2c
  -- the right-hand side density
  have hRi : Integrable (fun x => (∑ k, ξ x k * Lightlike.pd k N x) * hamiltonianDensity h π x) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (continuous_finsetSum _ fun k _ => (hξ k).continuous.mul (smooth_pd hN k).continuous).mul hham.continuous
    · refine HasCompactSupport.mul_right ?_
      exact hcs_sum _ _ fun k _ => (hNc.fderiv_apply (𝕜 := ℝ) (Pi.single k 1)).mul_left (f := fun y => ξ y k)
  unfold momentumConstraint hamiltonianConstraint
  rw [← integral_sub hA hB]
  have hpt : ∀ x, momentumDensity ξ G π x - N x * hamDirDeriv h π (lieTensor ξ h) x =
      (∑ k, ξ x k * Lightlike.pd k N x) * hamiltonianDensity h π x +
        (∑ k, Lightlike.pd k (fun y => ξ y k * ∑ i, ∑ j, π y i j * G y i j) x -
          ∑ k, Lightlike.pd k (fun y => N y * (ξ y k * hamiltonianDensity h π y)) x) :=
    fun x => bracket_pointwise hξ hN hh hpos hπ x
  have hint : ∀ x, (∑ k, Lightlike.pd k N x * ξ x k) * hamiltonianDensity h π x =
      (∑ k, ξ x k * Lightlike.pd k N x) * hamiltonianDensity h π x := fun x => by
    congr 1; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hP12 : Integrable (fun x => (∑ k, Lightlike.pd k (fun y => ξ y k * ∑ i, ∑ j, π y i j * G y i j) x) -
      ∑ k, Lightlike.pd k (fun y => N y * (ξ y k * hamiltonianDensity h π y)) x) volume := hP1i.sub hP2i
  simp only [hpt]
  rw [integral_add hRi hP12, integral_sub hP1i hP2i, hP1, hP2]
  simp

end Lightlike.Canonical

end
