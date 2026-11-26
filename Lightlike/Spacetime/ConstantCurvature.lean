import Lightlike.Spacetime.Corners.ChartAgreement
import Lightlike.Spacetime.LieMetric
import Lightlike.Spacetime.LeviCivita
import Lightlike.Spacetime.Corners.Bridge
import Lightlike.Spacetime.Minkowski

/-!
# Constant curvature and maximal symmetry of a pseudo-Riemannian manifold

For a smooth symmetric nondegenerate metric `g` (`NondegMetric`, any signature) on a manifold `M` modelled on
`Fin n → ℝ` (any model with corners):

* `HasConstantCurvature g K`: for every locally smooth Levi-Civita connection, the curvature is
  `R(X, Y) Z = K (g(Y, Z) X - g(X, Z) Y)` at every point (the curvature of a maximally symmetric space,
  Carroll, *Lecture Notes on General Relativity*, eq. (3.191), with the sign convention of `curvatureAt`);
* `IsMaximallySymmetric g K`: constant curvature `K` and `n (n + 1) / 2` smooth Killing fields of the Levi-Civita
  connection that are linearly independent (at most that many exist on a connected manifold:
  `finrank_killingFieldSpace_le` for the model `𝓘(ℝ, Fin n → ℝ)`).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 2 M]

/-- **Constant curvature `K`**: every locally smooth Levi-Civita connection of `g` has
`R(X, Y) Z = K (g(Y, Z) X - g(X, Z) Y)` at every point. -/
def HasConstantCurvature (g : NondegMetric I M) (K : ℝ) : Prop :=
  ∀ (cov : Connection I M) [LocallySmoothConnectionW cov], cov.IsLeviCivita g →
    ∀ (x : M) (X Y Z : TangentSpace I x),
      cov.curvatureAt x X Y Z = K • (g.g x Y Z • X - g.g x X Z • Y)

/-- **Maximally symmetric with curvature `K`**: constant curvature `K`, and `n (n + 1) / 2` smooth vector fields
that are Killing for the Levi-Civita connection `leviCivita g` and linearly independent. -/
def IsMaximallySymmetric (g : NondegMetric I M) (K : ℝ) : Prop :=
  HasConstantCurvature g K ∧
    ∃ Y : Fin (n * (n + 1) / 2) → Π p : M, TangentSpace I p,
      (∀ i, ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
          (fun q : M => (⟨q, Y i q⟩ : TangentBundle I M)) ∧
        ∀ p, IsKillingAt (leviCivita g) g (Y i) p) ∧
      LinearIndependent ℝ Y


section OfCharts

variable (cov : Connection I M) [LocallySmoothConnectionW cov] (x₀ : M)

lemma Rhat_zero_leftW (p : M) (b c : Fin n → ℝ) : RhatW cov x₀ p 0 b c = 0 := by
  simpa using Rhat_smul_leftW cov x₀ p 0 0 b c

lemma Rhat_zero_midW (p : M) (a c : Fin n → ℝ) : RhatW cov x₀ p a 0 c = 0 := by
  simpa using Rhat_smul_midW cov x₀ p 0 a 0 c

lemma Rhat_zero_rightW (p : M) (a b : Fin n → ℝ) : RhatW cov x₀ p a b 0 = 0 := by
  simpa using Rhat_smul_rightW cov x₀ p 0 a b 0

/-- `RhatW` is trilinear: its value is the sum over the standard basis. -/
lemma Rhat_expandW (p : M) (a b c : Fin n → ℝ) :
    RhatW cov x₀ p a b c = ∑ μ, ∑ ν, ∑ σ, (a μ * b ν * c σ) •
      RhatW cov x₀ p (Pi.single μ 1) (Pi.single ν 1) (Pi.single σ 1) := by
  have sumL : ∀ (s : Finset (Fin n)) (f : Fin n → Fin n → ℝ) (b c : Fin n → ℝ),
      RhatW cov x₀ p (∑ i ∈ s, f i) b c = ∑ i ∈ s, RhatW cov x₀ p (f i) b c := by
    intro s f b c
    induction s using Finset.induction_on with
    | empty => simpa using Rhat_zero_leftW cov x₀ p b c
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Rhat_add_leftW, ih]
  have sumM : ∀ (s : Finset (Fin n)) (f : Fin n → Fin n → ℝ) (a c : Fin n → ℝ),
      RhatW cov x₀ p a (∑ i ∈ s, f i) c = ∑ i ∈ s, RhatW cov x₀ p a (f i) c := by
    intro s f a c
    induction s using Finset.induction_on with
    | empty => simpa using Rhat_zero_midW cov x₀ p a c
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Rhat_add_midW, ih]
  have sumR : ∀ (s : Finset (Fin n)) (f : Fin n → Fin n → ℝ) (a b : Fin n → ℝ),
      RhatW cov x₀ p a b (∑ i ∈ s, f i) = ∑ i ∈ s, RhatW cov x₀ p a b (f i) := by
    intro s f a b
    induction s using Finset.induction_on with
    | empty => simpa using Rhat_zero_rightW cov x₀ p a b
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Rhat_add_rightW, ih]
  have dec : ∀ u : Fin n → ℝ, u = ∑ i, u i • (Pi.single i 1 : Fin n → ℝ) := fun u => by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [dec a, dec b, dec c]
  rw [sumL]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Rhat_smul_leftW, sumM, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Rhat_smul_midW, sumR, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Rhat_smul_rightW, smul_smul, smul_smul]


/-- The curvature at the point `φ⁻¹ y` of the chart at `x₀`, when the coordinate Riemann tensor there is that of
constant curvature `K`. -/
theorem curvatureAt_of_chart {g : NondegMetric I M} (hLC : cov.IsLeviCivita g) {K : ℝ}
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt I x₀).target)
    (h : ∀ ρ σ μ ν : Fin n, riemannW (range I) (g.coordMetricW x₀) ρ σ μ ν y =
      K * ((if ρ = μ then 1 else 0) * g.coordMetricW x₀ y σ ν -
        (if ρ = ν then 1 else 0) * g.coordMetricW x₀ y σ μ))
    (X Y Z : TangentSpace I ((extChartAt I x₀).symm y)) :
    cov.curvatureAt ((extChartAt I x₀).symm y) X Y Z =
      K • (g.g ((extChartAt I x₀).symm y) Y Z • X - g.g ((extChartAt I x₀).symm y) X Z • Y) := by
  have hp : ((extChartAt I x₀).symm y) ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet := symm_mem_chartTriv_baseSetW (I := I) x₀ hy
  have inj : ∀ u v : TangentSpace I ((extChartAt I x₀).symm y), hvW x₀ ((extChartAt I x₀).symm y) u = hvW x₀ ((extChartAt I x₀).symm y) v → u = v := fun u v huv => by
    rw [← symmL_hvW x₀ hp u, ← symmL_hvW x₀ hp v, huv]
  apply inj
  rw [hv_curvatureAtW cov x₀ hp, Rhat_expandW, hv_smul'W x₀ hp, hv_subW x₀ hp, hv_smul'W x₀ hp,
    hv_smul'W x₀ hp]
  set G := g.coordMetricW x₀ y with hGdef
  have hR : ∀ μ ν σ, RhatW cov x₀ ((extChartAt I x₀).symm y) (Pi.single μ 1) (Pi.single ν 1) (Pi.single σ 1) =
      fun ρ => riemannW (range I) (g.coordMetricW x₀) ρ σ μ ν y := by
    intro μ ν σ
    ext ρ
    have := riemann_coord_compW cov x₀ g hLC hy μ ν σ ρ
    rwa [hv_curvatureAtW cov x₀ hp, hv_coordFieldW x₀ hp, hv_coordFieldW x₀ hp,
      hv_coordFieldW x₀ hp] at this
  have hdec : ∀ u : TangentSpace I ((extChartAt I x₀).symm y), u = ∑ k, hvW x₀ ((extChartAt I x₀).symm y) u k • coordFieldW (I := I) x₀ k ((extChartAt I x₀).symm y) := by
    intro u
    conv_lhs => rw [← symmL_hvW x₀ hp u]
    have : hvW x₀ ((extChartAt I x₀).symm y) u = ∑ k, hvW x₀ ((extChartAt I x₀).symm y) u k • (Pi.single k 1 : Fin n → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, symmL_eq_coordFieldW x₀ hp k]
    simp [Finset.sum_apply, Pi.single_apply]
  have hG : ∀ a b : Fin n, g.g ((extChartAt I x₀).symm y) (coordFieldW (I := I) x₀ a ((extChartAt I x₀).symm y)) (coordFieldW (I := I) x₀ b ((extChartAt I x₀).symm y)) = G a b :=
    fun a b => g_coordFieldW g x₀ a b hy
  have hsym : ∀ a b, G a b = G b a := fun a b => by rw [← hG a b, ← hG b a, g.symm]
  have hg : ∀ u v : TangentSpace I ((extChartAt I x₀).symm y), g.g ((extChartAt I x₀).symm y) u v = ∑ a, ∑ b, hvW x₀ ((extChartAt I x₀).symm y) u a * hvW x₀ ((extChartAt I x₀).symm y) v b * G a b := by
    intro u v
    conv_lhs => rw [hdec u, hdec v]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, hG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  ext ρ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR, h, Pi.sub_apply, hg]
  have e1 : ∀ A Bv C : Fin n → ℝ, ∑ μ, ∑ ν, ∑ σ, A μ * Bv ν * C σ * (K * ((if ρ = μ then 1 else 0) * G σ ν)) =
      K * ((∑ a, ∑ b, Bv a * C b * G a b) * A ρ) := by
    intro A Bv C
    rw [Finset.sum_eq_single ρ (fun μ _ hμ => by simp [Ne.symm hμ]) (by simp)]
    simp only [ite_true, one_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [hsym σ ν]; ring
  have e2 : ∀ A Bv C : Fin n → ℝ, ∑ μ, ∑ ν, ∑ σ, A μ * Bv ν * C σ * (K * ((if ρ = ν then 1 else 0) * G σ μ)) =
      K * ((∑ a, ∑ b, A a * C b * G a b) * Bv ρ) := by
    intro A Bv C
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single ρ (fun ν _ hν => by simp [Ne.symm hν]) (by simp)]
    simp only [ite_true, one_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [hsym σ μ]; ring
  have split : ∀ A Bv C : Fin n → ℝ, ∑ μ, ∑ ν, ∑ σ, A μ * Bv ν * C σ * (K * ((if ρ = μ then 1 else 0) * G σ ν -
      (if ρ = ν then 1 else 0) * G σ μ)) =
      ∑ μ, ∑ ν, ∑ σ, A μ * Bv ν * C σ * (K * ((if ρ = μ then 1 else 0) * G σ ν)) -
      ∑ μ, ∑ ν, ∑ σ, A μ * Bv ν * C σ * (K * ((if ρ = ν then 1 else 0) * G σ μ)) := by
    intro A Bv C
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
      Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [split, e1, e2]
  ring

/-- **Constant curvature from the charts**: if in every chart the coordinate Riemann tensor of the coordinate metric
is `R^ρ_{σμν} = K (δ^ρ_μ g_{σν} - δ^ρ_ν g_{σμ})` on the chart target, the manifold has constant curvature `K`. -/
theorem HasConstantCurvature.of_charts {g : NondegMetric I M} {K : ℝ}
    (h : ∀ (x₀ : M) {y : Fin n → ℝ}, y ∈ (extChartAt I x₀).target → ∀ ρ σ μ ν : Fin n,
      riemannW (range I) (g.coordMetricW x₀) ρ σ μ ν y =
        K * ((if ρ = μ then 1 else 0) * g.coordMetricW x₀ y σ ν -
          (if ρ = ν then 1 else 0) * g.coordMetricW x₀ y σ μ)) :
    HasConstantCurvature g K := by
  intro cov _ hLC x
  have hy : extChartAt I x x ∈ (extChartAt I x).target := mem_extChartAt_target x
  have key := curvatureAt_of_chart cov x hLC hy (h x hy)
  have hpx : (extChartAt I x).symm (extChartAt I x x) = x := (extChartAt I x).left_inv
    (mem_extChartAt_source x)
  exact hpx ▸ key

end OfCharts


/-- **Non-vacuity of `HasConstantCurvature.of_charts`: Minkowski space `ℝⁿ` has constant curvature `0`.** Its
coordinate metric is the constant `η` in every chart (`minkowski_coordMetric`), whose Riemann tensor vanishes. -/
theorem hasConstantCurvature_minkowski (n : ℕ) :
    HasConstantCurvature (minkowskiMetric n).toNondegMetric 0 :=
  HasConstantCurvature.of_charts fun x₀ y _ ρ σ μ ν => by
    rw [NondegMetric.coordMetricW_eq_coordMetric, range_modelWithCornersSelf_eq_univ, riemannW_univ,
      show (minkowskiMetric n).toNondegMetric.coordMetric x₀ = (minkowskiMetric n).coordMetric x₀ from rfl,
      minkowski_coordMetric, riemann_const]
    ring

end Lightlike
