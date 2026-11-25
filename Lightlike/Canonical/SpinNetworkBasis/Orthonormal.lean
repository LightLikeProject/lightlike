import Lightlike.HarmonicAnalysis.PeterWeylSU2
import Lightlike.Spin4.Haar

/-!
# Spin networks, step B: orthonormality of the product coefficients on `SU(2)^E`

Row G2-010 (milestone OP, task T-CA2): spin networks are an orthonormal basis of the gauge-invariant
`L²(SU(2)^E)` of a graph with edge set `E` (Ashtekar–Lewandowski 1995; Baez 1996, Lemma 3).

This file does the first step. On the space `E → SU(2)` of edge holonomies with the product Haar
probability measure `haarPi E`, a *spin labelling* `n : E → ℕ` and *magnetic indices*
`i j : ∀ e, Fin (n e + 1)` give the function
`phi n i j h = ∏_e √(n e + 1) · D^{n e}_{i e, j e}(h e)`.
`phi_inner` computes `∫ Φ_b conj Φ_a` by Fubini and the Schur orthogonality relations of `SU(2)`
(`su2_schur_orthogonality`, `schur_orthogonality_ne`), and `orthonormal_phiLp` states that these functions form an
orthonormal family of `L²(SU(2)^E)`, indexed by `Σ n, Idx n × Idx n`.

Supporting lemmas for the spin-network basis theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.Canonical.SpinNetworkBasis

open Lightlike Lightlike.Spin4 Lightlike.HarmonicAnalysis Lightlike.HarmonicAnalysis.UnitaryMatrixRep

noncomputable section

instance haarSU2_isHaar : haarSU2.IsHaarMeasure := by unfold haarSU2; infer_instance

/-- `SU(2)`, a subspace of `2 × 2` complex matrices, is second countable (so `E → SU(2)` is Borel). -/
instance secondCountableSU2 : SecondCountableTopology SU2 :=
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  inferInstanceAs (SecondCountableTopology
    (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)))

/-- The product Haar probability measure on the space `E → SU(2)` of edge holonomies. -/
def haarPi (E : Type) [Fintype E] : Measure (E → SU2) := Measure.pi fun _ => haarSU2

instance (E : Type) [Fintype E] : IsProbabilityMeasure (haarPi E) := by
  unfold haarPi; infer_instance

/-- Magnetic indices of a spin labelling `n`: on each edge `e` an index of the spin-`n e / 2` representation. -/
abbrev Idx {E : Type} (n : E → ℕ) : Type := ∀ e, Fin (n e + 1)

/-- The normalised matrix coefficient `√(n+1) · D^n_{ij}(g)` of the spin-`n/2` representation. -/
def phiEdge (n : ℕ) (i j : Fin (n + 1)) (g : SU2) : ℂ :=
  ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * SU2.spinMat n g i j

/-- The product coefficient `h ↦ ∏_e √(n e + 1) · D^{n e}_{i e, j e}(h e)` on `SU(2)^E`. -/
def phi {E : Type} [Fintype E] (n : E → ℕ) (i j : Idx n) (h : E → SU2) : ℂ :=
  ∏ e, phiEdge (n e) (i e) (j e) (h e)

lemma continuous_phiEdge (n : ℕ) (i j : Fin (n + 1)) : Continuous (phiEdge n i j) := by
  unfold phiEdge
  exact continuous_const.mul
    (((continuous_apply j).comp ((continuous_apply i).comp (SU2.continuous_spinRep (n := n)))))

lemma continuous_phi {E : Type} [Fintype E] (n : E → ℕ) (i j : Idx n) : Continuous (phi n i j) := by
  unfold phi
  exact continuous_finsetProd _ fun e _ => (continuous_phiEdge _ _ _).comp (continuous_apply e)

/-- Orthogonality of the normalised coefficients of one spin: `∫ Φ_{kl} conj Φ_{ij} = δ_{ki} δ_{lj}`. -/
lemma phiEdge_inner_eq (n : ℕ) (i j k l : Fin (n + 1)) :
    ∫ g, phiEdge n k l g * starRingEnd ℂ (phiEdge n i j g) ∂haarSU2 =
      if k = i ∧ l = j then 1 else 0 := by
  have h := su2_schur_orthogonality haarSU2 n k l j i
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hs : ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) = (n : ℂ) + 1 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; ring
  have e1 : ∀ g, phiEdge n k l g * starRingEnd ℂ (phiEdge n i j g) =
      ((n : ℂ) + 1) * (SU2.spinMat n g k l * starRingEnd ℂ (SU2.spinMat n g i j)) := by
    intro g
    simp only [phiEdge, map_mul, Complex.conj_ofReal]
    rw [← hs]; ring
  simp_rw [e1]
  rw [integral_const_mul, h]
  split_ifs
  · field_simp
  · simp

/-- Orthogonality of normalised coefficients of different spins. -/
lemma phiEdge_inner_ne {n m : ℕ} (hnm : n ≠ m) (i j : Fin (n + 1)) (k l : Fin (m + 1)) :
    ∫ g, phiEdge m k l g * starRingEnd ℂ (phiEdge n i j g) ∂haarSU2 = 0 := by
  have h := schur_orthogonality_ne haarSU2 (su2Spin_isIrreducible m) (su2Spin_isIrreducible n)
    (su2Spin_not_equivalent (Ne.symm hnm)) k l j i
  have e1 : ∀ g, phiEdge m k l g * starRingEnd ℂ (phiEdge n i j g) =
      (((Real.sqrt ((m : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) *
        (SU2.spinMat m g k l * starRingEnd ℂ (SU2.spinMat n g i j)) := by
    intro g
    simp only [phiEdge, map_mul, Complex.conj_ofReal]
    ring
  simp_rw [e1]
  rw [integral_const_mul]
  simp only [su2Spin_mat] at h
  rw [h, mul_zero]

variable {E : Type} [Fintype E]

lemma phi_mul_conj {n m : E → ℕ} (i j : Idx n) (k l : Idx m) (h : E → SU2) :
    phi m k l h * starRingEnd ℂ (phi n i j h) =
      ∏ e, (phiEdge (m e) (k e) (l e) (h e) * starRingEnd ℂ (phiEdge (n e) (i e) (j e) (h e))) := by
  simp only [phi, map_prod, Finset.prod_mul_distrib]

/-- **Orthogonality of the product coefficients, same spin labelling**
(Fubini and Schur orthogonality): `∫ Φ_{kl} conj Φ_{ij} = δ_{ki} δ_{lj}`. -/
theorem phi_inner_eq (n : E → ℕ) (i j k l : Idx n) :
    ∫ h, phi n k l h * starRingEnd ℂ (phi n i j h) ∂haarPi E =
      if k = i ∧ l = j then 1 else 0 := by
  simp_rw [phi_mul_conj]
  rw [haarPi, integral_fintype_prod_eq_prod
    (f := fun e g => phiEdge (n e) (k e) (l e) g * starRingEnd ℂ (phiEdge (n e) (i e) (j e) g))
    (μ := fun _ : E => haarSU2)]
  simp_rw [phiEdge_inner_eq]
  rw [Finset.prod_boole]
  simp [funext_iff, forall_and]

/-- **Orthogonality of the product coefficients, different spin labellings.** -/
theorem phi_inner_ne {n m : E → ℕ} (hnm : n ≠ m) (i j : Idx n) (k l : Idx m) :
    ∫ h, phi m k l h * starRingEnd ℂ (phi n i j h) ∂haarPi E = 0 := by
  obtain ⟨e, he⟩ := Function.ne_iff.1 hnm
  simp_rw [phi_mul_conj]
  rw [haarPi, integral_fintype_prod_eq_prod
    (f := fun e g => phiEdge (m e) (k e) (l e) g * starRingEnd ℂ (phiEdge (n e) (i e) (j e) g))
    (μ := fun _ : E => haarSU2)]
  exact Finset.prod_eq_zero (Finset.mem_univ e) (phiEdge_inner_ne he _ _ _ _)

/-- The product coefficient as a continuous function on `SU(2)^E`. -/
def phiC (n : E → ℕ) (i j : Idx n) : C(E → SU2, ℂ) := ⟨phi n i j, continuous_phi n i j⟩

/-- The product coefficient as an element of `L²(SU(2)^E)`. -/
def phiLp (n : E → ℕ) (i j : Idx n) : Lp ℂ 2 (haarPi E) :=
  ContinuousMap.toLp (E := ℂ) 2 (haarPi E) ℂ (phiC n i j)

lemma inner_phiLp (n m : E → ℕ) (i j : Idx n) (k l : Idx m) :
    inner ℂ (phiLp n i j) (phiLp m k l) =
      ∫ h, phi m k l h * starRingEnd ℂ (phi n i j h) ∂haarPi E := by
  unfold phiLp
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := haarPi E) (𝕜 := ℂ) (phiC n i j),
    ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := haarPi E) (𝕜 := ℂ) (phiC m k l)] with x h1 h2
  rw [h1, h2]
  simp [phiC]

/-- **The product coefficients are an orthonormal family of `L²(SU(2)^E, haarPi E)`**, indexed by a spin
labelling and two families of magnetic indices. -/
theorem orthonormal_phiLp :
    Orthonormal ℂ (fun a : (Σ n : E → ℕ, Idx n × Idx n) => phiLp a.1 a.2.1 a.2.2) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨n, i, j⟩ ⟨m, k, l⟩
  simp only
  rw [inner_phiLp]
  by_cases hnm : n = m
  · subst hnm
    rw [phi_inner_eq]
    simp [Sigma.mk.injEq, eq_comm]
  · rw [phi_inner_ne hnm, ite_eq_right_iff.2]
    intro h
    exact absurd (Sigma.mk.inj_iff.1 h).1 hnm

end

end Lightlike.Canonical.SpinNetworkBasis

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.Idx := _root_.Lightlike.Canonical.SpinNetworkBasis.Idx
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.continuous_phi := _root_.Lightlike.Canonical.SpinNetworkBasis.continuous_phi
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.continuous_phiEdge := _root_.Lightlike.Canonical.SpinNetworkBasis.continuous_phiEdge
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.haarPi := _root_.Lightlike.Canonical.SpinNetworkBasis.haarPi
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.haarSU2_isHaar := _root_.Lightlike.Canonical.SpinNetworkBasis.haarSU2_isHaar
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.inner_phiLp := _root_.Lightlike.Canonical.SpinNetworkBasis.inner_phiLp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.orthonormal_phiLp := _root_.Lightlike.Canonical.SpinNetworkBasis.orthonormal_phiLp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phi := _root_.Lightlike.Canonical.SpinNetworkBasis.phi
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phiC := _root_.Lightlike.Canonical.SpinNetworkBasis.phiC
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phiEdge := _root_.Lightlike.Canonical.SpinNetworkBasis.phiEdge
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phiEdge_inner_eq := _root_.Lightlike.Canonical.SpinNetworkBasis.phiEdge_inner_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phiEdge_inner_ne := _root_.Lightlike.Canonical.SpinNetworkBasis.phiEdge_inner_ne
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phiLp := _root_.Lightlike.Canonical.SpinNetworkBasis.phiLp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phi_inner_eq := _root_.Lightlike.Canonical.SpinNetworkBasis.phi_inner_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phi_inner_ne := _root_.Lightlike.Canonical.SpinNetworkBasis.phi_inner_ne
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phi_mul_conj := _root_.Lightlike.Canonical.SpinNetworkBasis.phi_mul_conj
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.secondCountableSU2 := _root_.Lightlike.Canonical.SpinNetworkBasis.secondCountableSU2
