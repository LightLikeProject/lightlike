import Lightlike.Spacetime.PenroseSingularity.FamilyGram
import Lightlike.Spacetime.PenroseSingularity.GeodesicNonzero
import Lightlike.Spacetime.PenroseSingularity.FlowFamily
import Lightlike.Spacetime.EnergyConditions

/-!
# A degenerate Gram vector at a focal point (G1-012, step D4)

For a flow family of null normal geodesics, the Gram matrix `Qg σ t` of the `σ`-derivatives is positive
semidefinite (the Jacobi fields are orthogonal to the null velocity). If it is not positive definite at `t`, there is
a vector `v ≠ 0` with `v ⬝ᵥ Qg σ t *ᵥ v = 0`.
-/

open Set Filter Topology Manifold Bundle Matrix
open scoped Manifold ContDiff Matrix

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}
  {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
  {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
  {J : Set ℝ} {Sg : Set (Fin m → ℝ)}

/-- The Jacobi field `∂_v Γ (zS σ) t` of a flow family. -/
def jacV (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M)
    (zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M) (σ v : Fin m → ℝ) (t : ℝ) :
    TangentSpace 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) :=
  mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') t) σ v

/-- The quadratic form of the Gram matrix is the squared norm of the Jacobi field. -/
theorem qg_quadratic (σ v : Fin m → ℝ) (t : ℝ) :
    v ⬝ᵥ (Qg g Γ zS σ t *ᵥ v) = g.g (Γ (zS σ) t) (jacV g Γ zS σ v t) (jacV g Γ zS σ v t) := by
  set L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) :=
    mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') t) σ with hL
  set B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ := g.g (Γ (zS σ) t) with hB
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have hJ : jacV g Γ zS σ v t = ∑ i, v i • L (Pi.single i 1) := by
    show L v = _
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul]
  have hQ : ∀ i j, Qg g Γ zS σ t i j = B (L (Pi.single i 1)) (L (Pi.single j 1)) := fun i j => rfl
  show _ = B (jacV g Γ zS σ v t) (jacV g Γ zS σ v t)
  rw [hJ]
  simp only [Matrix.mulVec, dotProduct, hQ, map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hs : B (L (Pi.single j 1)) (L (Pi.single i 1)) = B (L (Pi.single i 1)) (L (Pi.single j 1)) :=
    g.symm (Γ (zS σ) t) _ _
  rw [hs]; ring

/-- The Gram matrix is symmetric. -/
theorem qg_isHermitian (σ : Fin m → ℝ) (t : ℝ) : (Qg g Γ zS σ t).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [Qg, Matrix.of_apply, star_trivial]
  exact g.symm _ _ _

/-- The Jacobi fields of a null flow family are orthogonal to the velocity. -/
theorem FlowFamily.jacV_orth (hF : FlowFamily g Γ zS Nz J Sg)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, g.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) (v : Fin m → ℝ) {t : ℝ} (ht : t ∈ J) :
    g.g (Γ (zS σ) t) (phase (n := n) (Γ (zS σ)) t).snd (jacV g Γ zS σ v t) = 0 := by
  set L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) :=
    mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') t) σ with hL
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have hJ : jacV g Γ zS σ v t = ∑ i, v i • L (Pi.single i 1) := by
    show L v = _
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul]
  have h0 := hF.omega_zero hk hperp σ hσ
  set B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ := g.g (Γ (zS σ) t) with hB
  set w : Fin n → ℝ := (phase (n := n) (Γ (zS σ)) t).snd with hw
  have h1 : ∀ i, B w (L (Pi.single i 1)) = 0 := fun i => h0 i t ht
  show B w (jacV g Γ zS σ v t) = 0
  rw [hJ]
  simp only [map_sum, map_smul, h1, smul_zero, Finset.sum_const_zero]

/-- **A degenerate Gram vector.** If the Gram matrix is not positive definite at `t` (and the initial velocity is
non-zero), some non-zero `v` has a null Jacobi field `jacV v t` orthogonal to the velocity. -/
theorem FlowFamily.exists_degenerate_vector (hF : FlowFamily g Γ zS Nz J Sg) (hnm : n = m + 2)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, g.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) (hw0 : (phase (n := n) (Γ (zS σ)) 0).snd ≠ 0) {t : ℝ} (ht : t ∈ J)
    (hQ : ¬ (Qg g Γ zS σ t).PosDef) :
    ∃ v : Fin m → ℝ, v ≠ 0 ∧ g.g (Γ (zS σ) t) (jacV g Γ zS σ v t) (jacV g Γ zS σ v t) = 0 := by
  have hnonneg : ∀ v : Fin m → ℝ, 0 ≤ g.g (Γ (zS σ) t) (jacV g Γ zS σ v t) (jacV g Γ zS σ v t) := by
    intro v
    subst hnm
    have hnull := hF.null_of_zero hk σ hσ t ht
    have hne : (phase (n := m + 2) (Γ (zS σ)) t).snd ≠ 0 :=
      phase_snd_ne_zero g hF.isOpen_J hF.convex_J.isPreconnected (hF.geo _ (hF.mem_Nz σ hσ)) hF.zero_mem ht hw0
    have horth := hF.jacV_orth hk hperp hσ v ht
    have hsymm := g.symm (Γ (zS σ) t) (jacV g Γ zS σ v t) (phase (n := m + 2) (Γ (zS σ)) t).snd
    exact null_orth_nonneg (g.lorentzian (Γ (zS σ) t)) (k := (phase (n := m + 2) (Γ (zS σ)) t).snd)
      hnull hne (by rw [hsymm]; exact horth)
  by_contra hcon
  push Not at hcon
  refine hQ (Matrix.PosDef.of_dotProduct_mulVec_pos (qg_isHermitian σ t) fun x hx => ?_)
  have h := hcon x hx
  have := hnonneg x
  rw [star_trivial, qg_quadratic]
  exact lt_of_le_of_ne this (Ne.symm h)

end Lightlike.Penrose
