import Lightlike.Spacetime.KillingRigidityCoord
import Lightlike.Spacetime.ChartConnection
import Lightlike.Spacetime.CurvatureSymmetries
import Lightlike.Spacetime.LieMetric
import Lightlike.Spacetime.KillingMinkowski

/-!
# Killing rigidity on a manifold (G1-024)

For a metric of any signature on a manifold modelled on `Fin n → ℝ` and a smooth vector field `X`:

* `chartCovector`, `contDiffOn_chartCovector`: the covector `θ_b = g(X, ∂_b)` in the chart at `x₀`, smooth on the chart
  target;
* `covCo_chartCovector`: its coordinate covariant derivative is `∇_a θ_b = g(∇_{∂_a} X, ∂_b)` for the Levi-Civita
  connection; `covCo_chartCovector_killing`: a Killing field (`IsKillingAt`) gives Killing's equation for `θ`;
* `rigVec_chartCovector`: `θ` and `∂θ` vanish at a chart point iff `X` and `∇X` vanish there;
* `killing_eq_zero_of_eq_zero`: **Killing rigidity**: on a connected manifold, a smooth Killing field with `X(p₀) = 0`
  and `∇X(p₀) = 0` vanishes everywhere (the coordinate rigidity `rigVec_eq_zero_of_isPreconnected` in a ball of each
  chart, and the set where `X` and `∇X` vanish is open and closed);
* `killingFieldSpace`, `finrank_killingFieldSpace_le`: the smooth Killing fields form a real vector space, of finite
  dimension at most `n (n + 1) / 2` on a connected nonempty manifold: `X ↦ (g(X, ∂_b), g(∇_{∂_a} X, ∂_b))` at a point is
  linear and injective (rigidity) into `ℝⁿ` times the antisymmetric matrices.

## References

* M. Blau, *Lecture Notes on General Relativity* (version of 15 November 2026,
  http://www.blau.itp.unibe.ch/newlecturesGR.pdf), section 14.1, the statement after (14.2), p. 337: "a Killing vector
  field `K^μ(x)` is completely and uniquely determined everywhere by the values of `K_μ(x₀)` and `∇_μ K_ν(x₀)` at a
  single point `x₀`"; eq. (14.4), p. 338: "an n-dimensional space(-time) can have at most `n(n+1)/2` independent Killing
  vectors".
-/

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

/-- The covector `θ_b = g(X, ∂_b)` of a vector field in the chart at `x₀`, as a function of the chart point. -/
def chartCovector (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (X : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p) (x₀ : M)
    (y : Fin n → ℝ) (b : Fin n) : ℝ :=
  g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (X ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
    (coordField x₀ b ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))

variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) {X : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}

/-- The coordinate fields are smooth on the chart domain. -/
theorem contMDiffAt_coordField (x₀ : M) (i : Fin n) {p : M} (hp : p ∈ (chartTriv n x₀).baseSet) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, coordField x₀ i q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) p :=
  ((chartTriv n x₀).contMDiffOn_localFrame_baseSet ∞ (Pi.basisFun ℝ (Fin n)) i).contMDiffAt
    ((chartTriv n x₀).open_baseSet.mem_nhds hp)

/-- `θ_b = g(X, ∂_b)` is smooth on the chart target, for a smooth vector field `X`. -/
theorem contDiffOn_chartCovector
    (hX : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))) (x₀ : M) (b : Fin n) :
    ContDiffOn ℝ ∞ (fun y => chartCovector g X x₀ y b) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  have hF : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ (gpair g X (coordField x₀ b)) (chartTriv n x₀).baseSet :=
    fun p hp => (contMDiffAt_gpair g (hX p) (contMDiffAt_coordField x₀ b hp)).contMDiffWithinAt
  have hcomp := hF.comp (contMDiffOn_extChartAt_symm x₀) fun y hy => symm_mem_chartTriv_baseSet x₀ hy
  exact (contMDiffOn_iff_contDiffOn.mp hcomp).congr fun y _ => rfl

/-- **The covariant derivative of `θ` in coordinates is that of `X` on the manifold**:
`∇_a θ_b = g(∇_{∂_a} X, ∂_b)` for the Levi-Civita connection. -/
theorem covCo_chartCovector (hX : ∀ p, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) p) (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (a b : Fin n) :
    covCo (g.coordMetric x₀) (chartCovector g X x₀) a b y =
      g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
        (leviCivita g X ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
          (coordField x₀ a ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)))
        (coordField x₀ b ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hz : ψ.symm y ∈ ψ.source := ψ.map_target hy
  have hgp := mdiffAt_gpair g (hX (ψ.symm y)) (mdiffAt_coordField x₀ b hp)
  have h1 := mfderiv_eq_chart (gpair g X (coordField x₀ b)) x₀ _ hz hgp (coordField x₀ a (ψ.symm y))
  rw [mfderiv_chart_coordField x₀ a hy, ψ.right_inv hy] at h1
  have hev : (gpair g X (coordField x₀ b) ∘ ψ.symm) =ᶠ[𝓝 y] fun y' => chartCovector g X x₀ y' b :=
    Eventually.of_forall fun _ => rfl
  rw [hev.fderiv_eq] at h1
  have hc := leviCivita_compat g (coordField x₀ a) X (coordField x₀ b) (ψ.symm y)
    (mdiffAt_coordField x₀ a hp) (hX _) (mdiffAt_coordField x₀ b hp)
  have hΓ := leviCivita_coordField g x₀ hy a b
  unfold covCo
  have hpd : pd a (fun z => chartCovector g X x₀ z b) y =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) (gpair g X (coordField x₀ b)) (ψ.symm y) (coordField x₀ a (ψ.symm y)) :=
    h1.symm
  rw [hpd]
  have hgpair : (fun q => g.g q (X q) (coordField x₀ b q)) = gpair g X (coordField x₀ b) := rfl
  rw [← hgpair, hc, hΓ]
  simp only [map_sum, map_smul, smul_eq_mul, chartCovector]
  ring

/-- A Killing field gives a covector satisfying Killing's equation on the chart target. -/
theorem covCo_chartCovector_killing (hX : ∀ p, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) p)
    (hK : ∀ p, IsKillingAt (leviCivita g) g X p) (x₀ : M) :
    ∀ y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target, ∀ a b,
      covCo (g.coordMetric x₀) (chartCovector g X x₀) a b y +
        covCo (g.coordMetric x₀) (chartCovector g X x₀) b a y = 0 := by
  intro y hy a b
  rw [covCo_chartCovector g hX x₀ hy, covCo_chartCovector g hX x₀ hy]
  have := hK _ (coordField x₀ a ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
    (coordField x₀ b ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
  rw [g.symm _ (coordField x₀ a _)] at this
  exact this

/-- At a chart point, `θ` and its first derivatives are the pairings of `X` and `∇X` with the coordinate fields. -/
theorem rigVec_chartCovector (hX : ∀ p, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) p) (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    rigVec (chartCovector g X x₀) y = 0 ↔
      X ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) = 0 ∧ leviCivita g X ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) = 0 := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hcov := covCo_chartCovector g hX x₀ hy
  unfold covCo at hcov
  constructor
  · intro h
    have hθ : ∀ b, chartCovector g X x₀ y b = 0 := fun b => congrFun h (Sum.inl b)
    have hdθ : ∀ a b, pd a (fun w => chartCovector g X x₀ w b) y = 0 := fun a b => congrFun h (Sum.inr (a, b))
    have hX0 : X (ψ.symm y) = 0 := by
      refine eq_of_g_coordField g x₀ hy fun l => ?_
      rw [show g.g _ (X (ψ.symm y)) _ = chartCovector g X x₀ y l from rfl, hθ l, map_zero, zero_apply]
    refine ⟨hX0, ?_⟩
    apply ContinuousLinearMap.coe_injective
    refine (coordBasis x₀ hp).ext fun a => ?_
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_apply]
    rw [← coordField_apply x₀ a hy]
    refine eq_of_g_coordField g x₀ hy fun l => ?_
    have := hcov a l
    simp only [hθ, mul_zero, Finset.sum_const_zero, sub_zero, hdθ] at this
    rw [← this, map_zero, zero_apply]
  · rintro ⟨hX0, hC0⟩
    have hθ : ∀ b, chartCovector g X x₀ y b = 0 := fun b => by
      simp only [chartCovector]; rw [← hψ, hX0, map_zero, zero_apply]
    funext i
    rcases i with b | ⟨a, b⟩
    · exact hθ b
    · show pd a (fun w => chartCovector g X x₀ w b) y = 0
      have hC0' : leviCivita g X ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) = 0 := hC0
      have := hcov a b
      simp only [hθ, mul_zero, Finset.sum_const_zero, sub_zero, hC0', map_zero, zero_apply] at this
      exact this

/-- **Killing rigidity on a manifold** (Blau, after (14.2)): on a connected manifold, a smooth Killing field `X` of the
Levi-Civita connection with `X(p₀) = 0` and `∇X(p₀) = 0` at one point vanishes everywhere. -/
theorem killing_eq_zero_of_eq_zero [PreconnectedSpace M]
    (hX : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    (hK : ∀ p, IsKillingAt (leviCivita g) g X p) {p₀ : M} (h0 : X p₀ = 0) (h1 : leviCivita g X p₀ = 0) :
    ∀ p, X p = 0 := by
  have hXd : ∀ p, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) p := fun p =>
    (hX p).mdifferentiableAt (by simp)
  set Z := {p : M | X p = 0 ∧ leviCivita g X p = 0} with hZ
  -- around every point, a chart ball on which `Z` is all or nothing
  have hloc : ∀ p : M, ∃ N ∈ 𝓝 p, (N ∩ Z).Nonempty → N ⊆ Z := by
    intro p
    set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) p with hψ
    obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target p) (ψ p) (mem_extChartAt_target p)
    set B := Metric.ball (ψ p) r
    have hT := g.isCoordMetric_coordMetric p
    have hgB : IsCoordMetric (g.coordMetric p) B :=
      { isOpen := Metric.isOpen_ball, symm := fun y hy => hT.symm y (hrT hy),
        isUnit_det := fun y hy => hT.isUnit_det y (hrT hy), smooth := fun i j => (hT.smooth i j).mono hrT }
    have hgs : ∀ z a b, g.coordMetric p z a b = g.coordMetric p z b a := fun z a b => by
      have := congrFun (congrFun (g.coordMetric_transpose p z) a) b
      simpa [Matrix.transpose_apply] using this.symm
    have hθ : ∀ c, ContDiffOn ℝ ∞ (fun z => chartCovector g X p z c) B := fun c =>
      (contDiffOn_chartCovector g hX p c).mono hrT
    have hKB : ∀ z ∈ B, ∀ a b, covCo (g.coordMetric p) (chartCovector g X p) a b z +
        covCo (g.coordMetric p) (chartCovector g X p) b a z = 0 := fun z hz =>
      covCo_chartCovector_killing g hXd hK p z (hrT hz)
    refine ⟨ψ.source ∩ ψ ⁻¹' B, ?_, ?_⟩
    · exact Filter.inter_mem ((isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p))
        ((continuousAt_extChartAt p).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
    · rintro ⟨q, ⟨hqs, hqB⟩, hqZ⟩ q' ⟨hq's, hq'B⟩
      have hq0 : rigVec (chartCovector g X p) (ψ q) = 0 := by
        rw [rigVec_chartCovector g hXd p (hrT hqB), ψ.left_inv hqs]; exact hqZ
      have := rigVec_eq_zero_of_isPreconnected hgB hgs hθ (convex_ball _ _).isPreconnected hKB hqB hq0 (ψ q') hq'B
      rw [rigVec_chartCovector g hXd p (hrT hq'B), ψ.left_inv hq's] at this
      exact this
  have hopen : IsOpen Z := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨N, hN, hNZ⟩ := hloc p
    exact Filter.mem_of_superset hN (hNZ ⟨p, mem_of_mem_nhds hN, hp⟩)
  have hclosed : IsClosed Z := isClosed_iff_clusterPt.2 fun p hp => by
    obtain ⟨N, hN, hNZ⟩ := hloc p
    have : (N ∩ Z).Nonempty := (clusterPt_principal_iff.1 hp) N hN
    exact hNZ this (mem_of_mem_nhds hN)
  have hZu : Z = univ := (IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨p₀, h0, h1⟩)
  intro p
  have : p ∈ Z := hZu ▸ mem_univ p
  exact this.1

/-- **The Killing fields** of the Levi-Civita connection: the smooth vector fields `X` with `g(∇_v X, w) + g(v, ∇_w X) = 0`
everywhere, a real vector space. -/
def killingFieldSpace : Submodule ℝ (Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p) where
  carrier := {X | ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) ∧ ∀ p, IsKillingAt (leviCivita g) g X p}
  add_mem' := by
    rintro X Y ⟨hX, hKX⟩ ⟨hY, hKY⟩
    refine ⟨hX.add_section hY, fun p v w => ?_⟩
    have hcov := (leviCivita g).isCovariantDerivativeOn (s := Set.univ)
    rw [hcov.add ((hX p).mdifferentiableAt (by simp)) ((hY p).mdifferentiableAt (by simp))]
    simp only [add_apply, map_add]
    linarith [hKX p v w, hKY p v w]
  zero_mem' := by
    refine ⟨contMDiff_zeroSection _ _, fun p v w => ?_⟩
    have hcov := (leviCivita g).isCovariantDerivativeOn (s := Set.univ)
    rw [hcov.zero]
    simp
  smul_mem' := by
    rintro c X ⟨hX, hKX⟩
    refine ⟨hX.const_smul_section, fun p v w => ?_⟩
    have hcov := (leviCivita g).isCovariantDerivativeOn (s := Set.univ)
    rw [hcov.smul_const c ((hX p).mdifferentiableAt (by simp))]
    simp only [smul_apply, map_smul, smul_eq_mul]
    rw [← mul_add, hKX p v w, mul_zero]

/-- **At most `n (n + 1) / 2` independent Killing fields** (Blau (14.4)): on a connected nonempty manifold the Killing
fields form a finite-dimensional space of dimension at most `n (n + 1) / 2`. -/
theorem finrank_killingFieldSpace_le [PreconnectedSpace M] [Nonempty M] :
    Module.Finite ℝ (killingFieldSpace g) ∧ Module.finrank ℝ (killingFieldSpace g) ≤ n * (n + 1) / 2 := by
  obtain ⟨p₀⟩ := ‹Nonempty M›
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ with hψ
  have hy₀ : ψ p₀ ∈ ψ.target := mem_extChartAt_target p₀
  have hp₀ : ψ.symm (ψ p₀) = p₀ := ψ.left_inv (mem_extChartAt_source p₀)
  have hcov := (leviCivita g).isCovariantDerivativeOn (s := Set.univ)
  -- the value and the covariant derivative at `p₀`, paired with the coordinate fields
  let Φ : killingFieldSpace g →ₗ[ℝ] (Fin n → ℝ) × antisymmMatrices n :=
    { toFun := fun K => (fun b => g.g p₀ (K.1 p₀) (coordField p₀ b p₀),
        ⟨Matrix.of fun a b => g.g p₀ (leviCivita g K.1 p₀ (coordField p₀ a p₀)) (coordField p₀ b p₀), by
          intro a b
          have := K.2.2 p₀ (coordField p₀ a p₀) (coordField p₀ b p₀)
          rw [g.symm p₀ (coordField p₀ a p₀)] at this
          simp only [Matrix.of_apply]
          linarith⟩)
      map_add' := fun K L => by
        ext b
        · simp
        · simp only [Submodule.coe_add, Matrix.of_apply, Prod.snd_add, Submodule.coe_add, Matrix.add_apply]
          rw [hcov.add ((K.2.1 p₀).mdifferentiableAt (by simp)) ((L.2.1 p₀).mdifferentiableAt (by simp))]
          simp
      map_smul' := fun c K => by
        ext b
        · simp
        · simp only [SetLike.val_smul, Matrix.of_apply, Prod.smul_snd, Matrix.smul_apply,
            RingHom.id_apply]
          rw [hcov.smul_const c ((K.2.1 p₀).mdifferentiableAt (by simp))]
          simp }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro K hK
    have h1 : ∀ b, g.g p₀ (K.1 p₀) (coordField p₀ b p₀) = 0 := fun b => congrFun (congrArg Prod.fst hK) b
    have h2 : ∀ a b, g.g p₀ (leviCivita g K.1 p₀ (coordField p₀ a p₀)) (coordField p₀ b p₀) = 0 := fun a b =>
      congrFun (congrFun (congrArg (fun x => (x.2 : Matrix (Fin n) (Fin n) ℝ)) hK) a) b
    have hX0 : K.1 p₀ = 0 := by
      have := eq_of_g_coordField g p₀ hy₀ (v := K.1 (ψ.symm (ψ p₀))) (w := 0) fun l => by
        rw [map_zero, zero_apply]
        rw [hp₀]; exact h1 l
      rwa [hp₀] at this
    have hC0 : leviCivita g K.1 p₀ = 0 := by
      have hp := symm_mem_chartTriv_baseSet p₀ hy₀
      have h2' : ∀ a b, g.g (ψ.symm (ψ p₀)) (leviCivita g K.1 (ψ.symm (ψ p₀)) (coordField p₀ a (ψ.symm (ψ p₀))))
          (coordField p₀ b (ψ.symm (ψ p₀))) = 0 := fun a b => by rw [hp₀]; exact h2 a b
      have hq : leviCivita g K.1 (ψ.symm (ψ p₀)) = 0 := by
        apply ContinuousLinearMap.coe_injective
        refine (coordBasis p₀ hp).ext fun a => ?_
        simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_apply]
        rw [← coordField_apply p₀ a hy₀]
        exact eq_of_g_coordField g p₀ hy₀ (w := 0) fun l => by rw [map_zero, zero_apply]; exact h2' a l
      rwa [hp₀] at hq
    exact Subtype.ext (funext (killing_eq_zero_of_eq_zero g K.2.1 K.2.2 hX0 hC0))
  have hfin : Module.Finite ℝ (killingFieldSpace g) := Module.Finite.of_injective Φ hinj
  refine ⟨hfin, (LinearMap.finrank_le_finrank_of_injective hinj).trans ?_⟩
  have := Module.Free.of_divisionRing ℝ (antisymmMatrices n)
  rw [Module.finrank_prod, Module.finrank_fin_fun, finrank_antisymmMatrices]
  rcases n with _ | m
  · simp
  · have h2 : (m + 1) * (m + 1 + 1) = (m + 1) * m + 2 * (m + 1) := by ring
    simp only [Nat.add_sub_cancel]
    rw [h2, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2), add_comm]

end Lightlike
