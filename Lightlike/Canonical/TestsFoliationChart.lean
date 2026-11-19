import Lightlike.Canonical.FoliationChart
import Lightlike.Canonical.TestsFoliation
import Lightlike.Spacetime.FlatConnection

/-!
# Trust checks of the adapted-chart form of the foliation data

The identity chart of Minkowski space is adapted to `τ = x⁰`, the ADM metric of each slice is the Euclidean metric, and,
for the flat (Levi-Civita) connection, the extrinsic curvature and the ADM momentum of each slice vanish.
-/

open Manifold

noncomputable section

namespace Lightlike.Canonical

variable {m : ℕ}

/-- The time coordinate of Minkowski space is adapted to its own chart. -/
theorem isAdaptedChart_minkowski (q : Fin (m + 1) → ℝ) :
    IsAdaptedChart m (fun y : Fin (m + 1) → ℝ => y 0) q := by
  intro y _
  rw [extChartAt_model_space_eq_id]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- **The ADM metric of a slice of Minkowski space is the Euclidean metric**: `h_ij = δ_ij`. -/
theorem admSliceMetric_minkowski (q : Fin (m + 1) → ℝ) (t : ℝ) (x : Fin m → ℝ) :
    admSliceMetric (Lightlike.minkowskiMetric (m + 1)).toNondegMetric q t x = 1 := by
  ext i j
  simp only [admSliceMetric, Matrix.of_apply]
  have h := Lightlike.minkowski_coordMetric (n := m + 1) q
  rw [show (Lightlike.minkowskiMetric (m + 1)).toNondegMetric.coordMetric q =
    (Lightlike.minkowskiMetric (m + 1)).coordMetric q from rfl, h]
  simp [Lightlike.eta, Lightlike.etaDiag, Matrix.diagonal_apply, Matrix.one_apply, Fin.succ_inj]


/-- **The slices `x⁰ = const` of Minkowski space have zero extrinsic curvature and zero ADM momentum** (flat
connection, which is the Levi-Civita connection of `η`). -/
theorem admSliceMomentum_minkowski (q : Fin (m + 1) → ℝ) (t : ℝ) (x : Fin m → ℝ) :
    admSliceMomentum (mink m) (fun y => y 0) (Lightlike.flatConnection (Fin (m + 1) → ℝ)) q t x = 0 := by
  have hd : ∀ z : Fin (m + 1) → ℝ,
      fderiv ℝ (unitNormal (mink m) (fun y => y 0) : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) z = 0 := by
    intro z
    have hn : (unitNormal (mink m) (fun y => y 0) : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) =
        fun _ => (Pi.single 0 1 : Fin (m + 1) → ℝ) := funext unitNormal_minkowski
    rw [hn]
    exact fderiv_const_apply _
  have hK : admSliceExtrinsic (mink m) (fun y => y 0) (Lightlike.flatConnection (Fin (m + 1) → ℝ)) q t x = 0 := by
    have h0 : ∀ p : Fin (m + 1) → ℝ,
        (Lightlike.flatConnection (Fin (m + 1) → ℝ) (unitNormal (mink m) (fun y => y 0)) p :
          TangentSpace 𝓘(ℝ, Fin (m + 1) → ℝ) p →L[ℝ] TangentSpace 𝓘(ℝ, Fin (m + 1) → ℝ) p) = 0 := by
      intro p
      rw [Lightlike.flatConnection_apply]
      exact hd p
    ext i j
    simp only [admSliceExtrinsic, Matrix.of_apply, Matrix.zero_apply]
    exact extrinsicCurvature_eq_zero_of_cov (h0 _) _ _
  simp [admSliceMomentum, hK]

end Lightlike.Canonical
