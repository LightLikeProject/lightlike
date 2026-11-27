import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.KTypeOppositeL2
import Lightlike.Lorentz.SL2RPlancherel.KKL2

/-!
# The Plancherel isometry of the continuous part of an opposite-sign block

For natural `l, s`, let `K` be the closure in `L²(0, ∞)` of the opposite-sign ladder images
`blockEN s l G` (by `closure_range_blockEN` the orthocomplement of the discrete directions).  The
weighted transform `blockF s l` extends from the images to a linear isometry `blockL2N s l : K → L²(0, ∞)`
(`norm_blockL2N`), the Plancherel formula of the continuous part of the block.  Layer 2c-v of the
Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The continuous part of the opposite-sign block: the closure of the ladder images. -/
abbrev contPartN (s l : ℕ) : Submodule ℂ L2Ioi := (LinearMap.range (blockEN s l)).topologicalClosure

/-- The continuous part is complete (it is closed). -/
instance (s l : ℕ) : CompleteSpace (contPartN s l) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The ladder images as vectors of the continuous part. -/
def blockENc (s l : ℕ) : smoothCS →ₗ[ℂ] contPartN s l :=
  (blockEN s l).codRestrict (contPartN s l) fun G =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ G)

/-- The ladder images are dense in the continuous part. -/
theorem denseRange_blockENc (s l : ℕ) : DenseRange (blockENc s l) := by
  have hclos : (LinearMap.range (blockENc s l)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro y hy
    -- `y` is orthogonal to every image, hence to their closure, which contains `y`
    have horth : ∀ G : smoothCS, inner ℂ (blockEN s l G) (y : L2Ioi) = 0 := fun G => by
      have := (Submodule.mem_orthogonal _ _).1 hy (blockENc s l G) (LinearMap.mem_range_self _ G)
      exact this
    have hy' : (y : L2Ioi) ∈ (LinearMap.range (blockEN s l))ᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro _ ⟨G, rfl⟩
      exact horth G
    have hyc : (y : L2Ioi) ∈ (contPartN s l)ᗮ := by
      show (y : L2Ioi) ∈ (LinearMap.range (blockEN s l)).topologicalClosureᗮ
      rw [Submodule.orthogonal_closure]
      exact hy'
    have hself := (Submodule.mem_orthogonal _ _).1 hyc (y : L2Ioi) y.2
    have : (y : L2Ioi) = 0 := inner_self_eq_zero.mp hself
    exact Subtype.ext this
  have := Submodule.dense_iff_topologicalClosure_eq_top.2 hclos
  rwa [LinearMap.coe_range] at this

/-- The block identity on the ladder images, in the continuous part. -/
theorem norm_blockENc (s l : ℕ) (G : smoothCS) : ‖blockF s l G‖ = ‖blockENc s l G‖ := by
  rw [norm_blockFN]
  rfl

/-- **The Plancherel isometry of the continuous part of an opposite-sign block**: the extension of
`π √(sinh ξ) hLRN s G l ↦ √(ρ tanh(πρ) w_l(ρ) w_s(ρ)) / 2 · Ĝ(ρ)` to a linear isometry
`contPartN s l → L²(0, ∞)`. -/
def blockL2N (s l : ℕ) : contPartN s l →ₗᵢ[ℂ] L2Ioi :=
  LinearMap.extendOfIsometry (blockF s l) (denseRange_blockENc s l) (norm_blockENc s l)

/-- On the ladder images, `blockL2N` is the weighted transform. -/
theorem blockL2N_apply (s l : ℕ) (G : smoothCS) : blockL2N s l (blockENc s l G) = blockF s l G :=
  LinearMap.extendOfIsometry_eq (blockF s l) (denseRange_blockENc s l) (norm_blockENc s l) G

/-- **The Plancherel identity of the continuous part of an opposite-sign block.** -/
theorem norm_blockL2N (s l : ℕ) (H : contPartN s l) : ‖blockL2N s l H‖ = ‖H‖ :=
  (blockL2N s l).norm_map H

/-- The discrete part is finite dimensional. -/
instance (s l : ℕ) : FiniteDimensional ℂ (discSpan s l) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- **The decomposition of an opposite-sign block**: every `H ∈ L²(0, ∞)` splits orthogonally into
its continuous part (in the closure of the ladder images, mapped isometrically by `blockL2N`) and its
discrete part (in the span of the `min(l, s)` discrete directions):
`‖H‖² = ‖blockL2N (P_cont H)‖² + ‖P_disc H‖²`. -/
theorem norm_sq_eq_cont_add_disc (s l : ℕ) (H : L2Ioi) :
    ‖H‖ ^ 2 = ‖blockL2N s l ((contPartN s l).orthogonalProjectionOnto H)‖ ^ 2 +
      ‖(discSpan s l).orthogonalProjectionOnto H‖ ^ 2 := by
  rw [norm_blockL2N, Submodule.norm_sq_eq_add_norm_sq_projection H (discSpan s l), add_comm]
  congr 2
  have key : ∀ (K' : Submodule ℂ L2Ioi) [K'.HasOrthogonalProjection], contPartN s l = K' →
      ‖(contPartN s l).orthogonalProjectionOnto H‖ = ‖K'.orthogonalProjectionOnto H‖ := by
    rintro K' _ rfl
    rfl
  exact (key _ (closure_range_blockEN s l)).symm

end Lightlike.Lorentz.SL2RPlancherel
