import Lightlike.Dirac.SpinorBundle
import Lightlike.Dirac.SpinLichnerowicz

/-!
# The Lichnerowicz formula on smooth sections of the spinor bundle

For a spin structure `S` of a Riemannian manifold `M` (any boundaryless model `I` on `ℝⁿ`) and a
Clifford module `ρ`, the Dirac operator `D = SpinorSection.dirac` and the rough Laplacian
`∇*∇ = SpinorSection.roughLaplacian` act on the smooth sections of the spinor bundle
`SpinorBundle S ρ` (`Lightlike/Dirac/SpinorBundle.lean`). **The Lichnerowicz formula**
(`SpinorSection.dirac_dirac`): for every smooth section `σ` and every point `x`,

  `D (D σ) (x) = ∇*∇ σ (x) + (R(x) / 4) σ(x)`

in the fibre at `x`, with `R` the scalar curvature of the Levi-Civita connection
(Lawson–Michelsohn, *Spin Geometry*, II Theorem 8.8; comparison with the source pending).

The proof reads the identity in a frame `i` with `x ∈ S.dom i`: the representation of a section in the
frame is injective on the fibre, the representations of `D σ` and `∇*∇ σ` are the frame operators of the
representation of `σ` (`SpinorSection.toField_dirac`, `toField_roughLaplacian`), the frame Dirac operator
is local (`SpinStructure.dirac_congr`), and in the frame `D² = ∇*∇ + R/4`
(`SpinStructure.dirac_sq_eq_rough_add_scal_div_four`).
-/

open Bundle Manifold Filter
open scoped Manifold ContDiff Topology

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type} [TopologicalSpace M] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (Fin n → ℝ) H} [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  {g : NondegMetric I M} {ι : Type} {S : SpinStructure g ι} {ρ : CliffordRep n V}

/-- The frame Dirac operator at `x` depends only on the germ of the representation at `x`. -/
lemma SpinStructure.dirac_congr (i : ι) {x : M} {φ₁ φ₂ : M → V} (h : φ₁ =ᶠ[𝓝 x] φ₂) :
    S.dirac ρ i φ₁ x = S.dirac ρ i φ₂ x := by
  unfold SpinStructure.dirac SpinStructure.nabla
  simp only [S.nablaV_congr ρ i _ h]

/-- The representation of the fibre at `x` in a frame `i` with `x ∈ S.dom i` is injective. -/
lemma SpinStructure.coordChange_injective {i : ι} {x : M} (hx : x ∈ S.dom i) :
    Function.Injective fun v : V => (S.spinorCore ρ).coordChange ((S.spinorCore ρ).indexAt x) i x v := by
  intro v w h
  have hb : x ∈ (S.spinorCore ρ).baseSet ((S.spinorCore ρ).indexAt x) := (S.spinorCore ρ).mem_baseSet_at x
  have hi : x ∈ (S.spinorCore ρ).baseSet i := by rwa [SpinStructure.spinorCore_baseSet]
  have h2 := congrArg ((S.spinorCore ρ).coordChange i ((S.spinorCore ρ).indexAt x) x) h
  simp only at h2
  rwa [(S.spinorCore ρ).coordChange_comp _ i _ x ⟨⟨hb, hi⟩, hb⟩,
    (S.spinorCore ρ).coordChange_comp _ i _ x ⟨⟨hb, hi⟩, hb⟩,
    (S.spinorCore ρ).coordChange_self _ x hb, (S.spinorCore ρ).coordChange_self _ x hb] at h2

/-- **The Lichnerowicz formula on smooth spinor sections**: `D(Dσ) = ∇*∇σ + (R/4) σ` at every point. -/
theorem SpinorSection.dirac_dirac (σ : SpinorSection S ρ) (x : M) :
    σ.dirac.dirac x =
      σ.roughLaplacian x + ((1 / 4 : ℝ) * (leviCivita g).scalarCurvatureAt g x) • σ x := by
  obtain ⟨i, hx⟩ := S.dom_cover x
  refine SpinStructure.coordChange_injective (ρ := ρ) hx ?_
  have hlin : (S.spinorCore ρ).coordChange ((S.spinorCore ρ).indexAt x) i x
      (σ.roughLaplacian x + ((1 / 4 : ℝ) * (leviCivita g).scalarCurvatureAt g x) • σ x) =
      (S.spinorCore ρ).coordChange ((S.spinorCore ρ).indexAt x) i x (σ.roughLaplacian x) +
        ((1 / 4 : ℝ) * (leviCivita g).scalarCurvatureAt g x) •
          (S.spinorCore ρ).coordChange ((S.spinorCore ρ).indexAt x) i x (σ x) := by
    erw [map_add, map_smul]
  simp only
  rw [hlin]
  have hrep : ∀ τ : SpinorSection S ρ,
      (S.spinorCore ρ).coordChange ((S.spinorCore ρ).indexAt x) i x (τ x) = τ.toField.rep i x :=
    fun τ => (τ.rep_of_mem hx).symm
  rw [hrep, hrep, hrep]
  set ψ := σ.toField with hψdef
  have hψ : ψ.IsSmooth := σ.toField_isSmooth
  -- the representation of `D σ` near `x`
  have hnear : (σ.dirac.toField.rep i) =ᶠ[𝓝 x] (ψ.dirac hψ.funDiffAt).rep i := by
    filter_upwards [(S.dom_open i).mem_nhds hx] with y hy
    exact σ.toField_dirac hy
  rw [σ.dirac.toField_dirac hx, σ.toField_roughLaplacian hx]
  change S.dirac ρ i (σ.dirac.toField.rep i) x = _
  rw [SpinStructure.dirac_congr i hnear]
  exact SpinStructure.dirac_sq_eq_rough_add_scal_div_four hψ hx

/-- Non-vacuity of `SpinorSection.dirac_dirac`: the constant section `v` of the spinor bundle of the
Euclidean spin structure of `ℝⁿ`. -/
example {n : ℕ} (ρ : CliffordRep n V) (v : V) (x : Fin n → ℝ) :
    let σ := SpinorSection.ofField (constSpinorField ρ v) (constSpinorField_isSmooth ρ v)
    σ.dirac.dirac x = σ.roughLaplacian x +
      ((1 / 4 : ℝ) * (leviCivita (euclideanMetric n)).scalarCurvatureAt (euclideanMetric n) x) • σ x :=
  SpinorSection.dirac_dirac _ x

end Lightlike.Dirac
