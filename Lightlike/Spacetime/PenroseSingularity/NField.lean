import Lightlike.Spacetime.PenroseSingularity.FutureAlong

/-!
# The timelike normalisation `N` along a future null geodesic (G1-012, step D4)

For a null vector `w` and a timelike vector `y` with `g(w, y) < 0`, `N = y / (-g(w, y))` satisfies `g(N, w) = -1` and
`g(N, N) < 0`; if `y` is future directed for a time orientation, so is `N`.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} {x : M}

/-- `N = y / (-g(w, y))`. -/
def nVec (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (y w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    TangentSpace 𝓘(ℝ, Fin n → ℝ) x :=
  (-g.g x w y)⁻¹ • y

/-- `g(N, w) = -1`. -/
theorem nVec_pair_w {y w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x} (hw : g.g x w y < 0) :
    g.g x (nVec g y w) w = -1 := by
  unfold nVec
  rw [map_smul, smul_apply, g.symm x y w, smul_eq_mul]
  have hne : g.g x w y ≠ 0 := hw.ne
  field_simp

/-- `g(N, N) < 0`. -/
theorem nVec_timelike {y w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x} (hy : g.g x y y < 0) (hw : g.g x w y < 0) :
    g.g x (nVec g y w) (nVec g y w) < 0 := by
  unfold nVec
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hc : 0 < ((-g.g x w y)⁻¹) := by
    have : 0 < -g.g x w y := by linarith
    positivity
  have := mul_pos hc hc
  nlinarith

/-- `g(N, z) < 0` whenever `g(y, z) < 0`. -/
theorem nVec_future {y w z : TangentSpace 𝓘(ℝ, Fin n → ℝ) x} (hyz : g.g x y z < 0) (hw : g.g x w y < 0) :
    g.g x (nVec g y w) z < 0 := by
  unfold nVec
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hc : 0 < ((-g.g x w y)⁻¹) := by
    have : 0 < -g.g x w y := by linarith
    positivity
  nlinarith

end Lightlike.Penrose
