import Lightlike.Canonical.SpinNetworkBasis.Gauge

/-!
# Spin networks, step D2: the gauge action preserves each spin-labelled block

Row G2-010 (milestone OP, task T-CA2). For a spin labelling `n` let `Wn n` be the (finite-dimensional) span of the
classes `phiLp n i j` in `L²(SU(2)^E)`. The gauge action sends `phi n i j` to a linear combination of the
`phi n k l` with the *same* `n` (`phi_act`: multiplicativity of the spin matrices and the multilinear expansion
`Finset.prod_univ_sum`), hence `gauge g` preserves `Wn n` (`gauge_mem_Wn`).

Supporting lemmas for the spin-network basis theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.Canonical.SpinNetworkBasis

open Lightlike Lightlike.Spin4 Lightlike.HarmonicAnalysis

noncomputable section

variable {V E : Type} [Fintype E] (src tgt : E → V)

/-- One edge: `phiEdge n i j (a b c⁻¹)` expanded through the multiplicativity of `spinMat n`. -/
lemma phiEdge_mul (n : ℕ) (i j : Fin (n + 1)) (a b c : SU2) :
    phiEdge n i j (a * b * c⁻¹) =
      ∑ q : Fin (n + 1) × Fin (n + 1),
        (SU2.spinMat n a i q.1 * SU2.spinMat n (c⁻¹ : SU2) q.2 j) * phiEdge n q.1 q.2 b := by
  have key : SU2.spinMat n ((a * b * c⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) i j =
      ∑ q : Fin (n + 1) × Fin (n + 1),
        SU2.spinMat n a i q.1 * SU2.spinMat n b q.1 q.2 * SU2.spinMat n (c⁻¹ : SU2) q.2 j := by
    rw [Fintype.sum_prod_type]
    simp only [Submonoid.coe_mul, SU2.spinMat_mul, Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
  unfold phiEdge
  rw [key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **The gauge action on the product coefficients**: `phi n i j ∘ act g` is a combination of the
`phi n k l` with the same spin labelling `n`. -/
lemma phi_act [DecidableEq E] (g : V → SU2) (n : E → ℕ) (i j : Idx n) (h : E → SU2) :
    phi n i j (act src tgt g h) =
      ∑ p ∈ Fintype.piFinset (fun e => (Finset.univ : Finset (Fin (n e + 1) × Fin (n e + 1)))),
        (∏ e, (SU2.spinMat (n e) (g (src e)) (i e) (p e).1 *
          SU2.spinMat (n e) ((g (tgt e))⁻¹ : SU2) (p e).2 (j e))) *
          phi n (fun e => (p e).1) (fun e => (p e).2) h := by
  unfold phi act
  simp_rw [phiEdge_mul]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.prod_mul_distrib]

omit [Fintype E] in
lemma continuous_act (g : V → SU2) : Continuous (act src tgt g) :=
  continuous_pi fun e => (continuous_const.mul (continuous_apply e)).mul continuous_const

/-- `gauge g` on a continuous class is the class of the composite. -/
lemma gauge_toLp (g : V → SU2) (a : C(E → SU2, ℂ)) :
    gauge src tgt g (ContinuousMap.toLp (E := ℂ) 2 (haarPi E) ℂ a) =
      ContinuousMap.toLp (E := ℂ) 2 (haarPi E) ℂ (a.comp ⟨act src tgt g, continuous_act src tgt g⟩) := by
  refine Lp.ext ?_
  have h2 := (measurePreserving_act src tgt g).quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := haarPi E) (𝕜 := ℂ) a)
  filter_upwards [gauge_ae src tgt g (ContinuousMap.toLp (E := ℂ) 2 (haarPi E) ℂ a), h2,
    ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := haarPi E) (𝕜 := ℂ)
      (a.comp ⟨act src tgt g, continuous_act src tgt g⟩)] with x hx1 hx2 hx3
  rw [hx3]
  exact hx1.trans hx2

/-- The span of the classes `phiLp n i j` for a fixed spin labelling `n`. -/
def Wn (n : E → ℕ) : Submodule ℂ (Lp ℂ 2 (haarPi E)) :=
  Submodule.span ℂ (Set.range fun p : Idx n × Idx n => phiLp n p.1 p.2)

lemma phiLp_mem_Wn (n : E → ℕ) (i j : Idx n) : phiLp n i j ∈ Wn n :=
  Submodule.subset_span ⟨(i, j), rfl⟩

/-- **The gauge action on the classes `phiLp`**: a combination of the `phiLp n k l`. -/
lemma gauge_phiLp_mem_Wn [DecidableEq E] (g : V → SU2) (n : E → ℕ) (i j : Idx n) :
    gauge src tgt g (phiLp n i j) ∈ Wn n := by
  have hC : (phiC n i j).comp ⟨act src tgt g, continuous_act src tgt g⟩ =
      ∑ p ∈ Fintype.piFinset (fun e => (Finset.univ : Finset (Fin (n e + 1) × Fin (n e + 1)))),
        (∏ e, (SU2.spinMat (n e) (g (src e)) (i e) (p e).1 *
          SU2.spinMat (n e) ((g (tgt e))⁻¹ : SU2) (p e).2 (j e))) •
          phiC n (fun e => (p e).1) (fun e => (p e).2) := by
    ext h
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.coe_sum,
      ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact phi_act src tgt g n i j h
  unfold phiLp
  rw [gauge_toLp, hC, map_sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (phiLp_mem_Wn n _ _)

/-- **`gauge g` preserves each spin-labelled block `Wn n`.** -/
lemma gauge_mem_Wn (g : V → SU2) (n : E → ℕ) {v : Lp ℂ 2 (haarPi E)} (hv : v ∈ Wn n) :
    gauge src tgt g v ∈ Wn n := by
  have : (Wn n).map (gauge src tgt g).toLinearMap ≤ Wn n := by
    unfold Wn
    rw [Submodule.map_span_le]
    rintro _ ⟨p, rfl⟩
    classical
    exact gauge_phiLp_mem_Wn src tgt g n p.1 p.2
  exact this ⟨v, hv, rfl⟩

end

end Lightlike.Canonical.SpinNetworkBasis

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.Wn := _root_.Lightlike.Canonical.SpinNetworkBasis.Wn
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.continuous_act := _root_.Lightlike.Canonical.SpinNetworkBasis.continuous_act
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.gauge_mem_Wn := _root_.Lightlike.Canonical.SpinNetworkBasis.gauge_mem_Wn
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.gauge_phiLp_mem_Wn := _root_.Lightlike.Canonical.SpinNetworkBasis.gauge_phiLp_mem_Wn
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.gauge_toLp := _root_.Lightlike.Canonical.SpinNetworkBasis.gauge_toLp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phiEdge_mul := _root_.Lightlike.Canonical.SpinNetworkBasis.phiEdge_mul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phiLp_mem_Wn := _root_.Lightlike.Canonical.SpinNetworkBasis.phiLp_mem_Wn
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_010.phi_act := _root_.Lightlike.Canonical.SpinNetworkBasis.phi_act
