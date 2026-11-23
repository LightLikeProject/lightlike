import Lightlike.Rows.G2_010.HilbertBasis
import Lightlike.HarmonicAnalysis.PeterWeylClassFunctions

/-!
# Spin networks, step D: the gauge action on `L²(SU(2)^E)`

Row G2-010 (milestone OP, task T-CA2). A graph is given by a vertex type `V`, an edge type `E` (finite) and
source and target maps `src tgt : E → V`. A gauge transformation `g : V → SU(2)` acts on holonomies by
`(act g h)_e = g_{src e} · h_e · g_{tgt e}⁻¹`. This action preserves the product Haar measure
(`measurePreserving_act`, left and right invariance of `haarSU2` on each factor), so it gives isometries
`gauge g` of `L²(SU(2)^E)` (`f ↦ f ∘ act g`). The gauge-invariant subspace is `gaugeInv`.

Supporting lemmas for the spin-network basis theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.Rows.G2_010

open Lightlike Lightlike.Spin4 Lightlike.HarmonicAnalysis

noncomputable section

variable {V E : Type} [Fintype E] (src tgt : E → V)

/-- The gauge action on holonomies: `(act g h)_e = g_{src e} h_e g_{tgt e}⁻¹`. -/
def act (g : V → SU2) (h : E → SU2) : E → SU2 := fun e => g (src e) * h e * (g (tgt e))⁻¹

omit [Fintype E] in
lemma act_act_inv (g : V → SU2) (h : E → SU2) :
    act src tgt g (act src tgt g⁻¹ h) = h := by
  funext e
  simp [act, mul_assoc]

omit [Fintype E] in
lemma act_inv_act (g : V → SU2) (h : E → SU2) :
    act src tgt g⁻¹ (act src tgt g h) = h := by
  funext e
  simp [act, mul_assoc]

/-- The gauge action preserves the product Haar measure. -/
lemma measurePreserving_act (g : V → SU2) :
    MeasurePreserving (act src tgt g) (haarPi E) (haarPi E) := by
  unfold haarPi act
  exact measurePreserving_pi (fun _ => haarSU2) (fun _ => haarSU2)
    (f := fun e x => g (src e) * x * (g (tgt e))⁻¹)
    (fun e => (measurePreserving_mul_right haarSU2 (g (tgt e))⁻¹).comp
      (measurePreserving_mul_left haarSU2 (g (src e))))

/-- The gauge transformation `g` as a linear isometry of `L²(SU(2)^E)`: `f ↦ f ∘ act g`. -/
def gauge (g : V → SU2) : Lp ℂ 2 (haarPi E) →ₗᵢ[ℂ] Lp ℂ 2 (haarPi E) :=
  Lp.compMeasurePreservingₗᵢ ℂ (act src tgt g) (measurePreserving_act src tgt g)

lemma gauge_ae (g : V → SU2) (f : Lp ℂ 2 (haarPi E)) :
    gauge src tgt g f =ᵐ[haarPi E] f ∘ act src tgt g :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_act src tgt g)

/-- `gauge g⁻¹` is a left inverse of `gauge g`. -/
lemma gauge_inv_gauge (g : V → SU2) (f : Lp ℂ 2 (haarPi E)) :
    gauge src tgt g⁻¹ (gauge src tgt g f) = f := by
  refine Lp.ext ?_
  have h1 := gauge_ae src tgt g⁻¹ (gauge src tgt g f)
  have h2 := (measurePreserving_act src tgt g⁻¹).quasiMeasurePreserving.ae_eq_comp
    (gauge_ae src tgt g f)
  filter_upwards [h1, h2] with h e1 e2
  rw [e1]
  simp only [Function.comp_apply] at e2 ⊢
  rw [e2, act_act_inv]

/-- `gauge g` is a right inverse of `gauge g⁻¹`. -/
lemma gauge_gauge_inv (g : V → SU2) (f : Lp ℂ 2 (haarPi E)) :
    gauge src tgt g (gauge src tgt g⁻¹ f) = f := by
  simpa using gauge_inv_gauge src tgt g⁻¹ f

/-- The gauge-invariant subspace of `L²(SU(2)^E)`: the classes fixed by every gauge transformation. -/
def gaugeInv : Submodule ℂ (Lp ℂ 2 (haarPi E)) where
  carrier := {f | ∀ g : V → SU2, gauge src tgt g f = f}
  add_mem' := fun {a b} ha hb g => by rw [map_add, ha g, hb g]
  zero_mem' := fun g => map_zero _
  smul_mem' := fun c {a} ha g => by rw [map_smul, ha g]

lemma mem_gaugeInv {f : Lp ℂ 2 (haarPi E)} :
    f ∈ gaugeInv src tgt ↔ ∀ g : V → SU2, gauge src tgt g f = f := Iff.rfl

end

end Lightlike.Rows.G2_010
