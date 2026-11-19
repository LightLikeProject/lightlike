import Lightlike.Spacetime.ChartChange
import Lightlike.Regge.Geodesic.Equation
import Lightlike.Spacetime.SchwarzschildManifold

/-!
# Geodesics are chart-independent

Let `φ` be a chart change from `V` into `U` and `g` a coordinate metric on `U`. If `(c, u)` is a geodesic of the
pulled-back metric `pullback g φ` staying in `V`, then `(φ ∘ c, J u)` with `J = ∂φ` is a geodesic of `g`
(`Lightlike.Geodesic.IsGeodesicOn.map_chartChange`). The proof is the transformation law of the Christoffel
symbols (`christoffel_pullback`): the inhomogeneous term `∂²φ` cancels the derivative of the Jacobian along the
curve.

Conversely, for an injective chart change, a curve `c` whose image `φ ∘ c` is a geodesic of `g` is a geodesic of
the pulled-back metric (`IsGeodesicOn.lift_chartChange`), by the local existence and uniqueness of geodesics.
-/

open Matrix Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U V : Set (Fin n → ℝ)}
  {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-- Reordering a fourfold sum. -/
lemma sum4_comm (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ b, ∑ c, ∑ ν, ∑ l, F b c ν l = ∑ ν, ∑ l, ∑ b, ∑ c, F b c ν l := by
  calc ∑ b, ∑ c, ∑ ν, ∑ l, F b c ν l = ∑ b, ∑ ν, ∑ c, ∑ l, F b c ν l :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ ν, ∑ b, ∑ c, ∑ l, F b c ν l := Finset.sum_comm
    _ = ∑ ν, ∑ b, ∑ l, ∑ c, F b c ν l :=
        Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ ν, ∑ l, ∑ b, ∑ c, F b c ν l := Finset.sum_congr rfl fun ν _ => Finset.sum_comm

/-- The algebra of the transformation: with the Christoffel law
`Σ_a J_a Γ'^a_{bc} = Σ_{νl} Γ_{νl} J^ν_b J^l_c + H_{bc}`. -/
lemma accel_transform (J : Fin n → ℝ) (Jm : Fin n → Fin n → ℝ) (Γ' : Fin n → Fin n → Fin n → ℝ)
    (Γ H : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hlaw : ∀ b c, ∑ a, J a * Γ' a b c = ∑ ν, ∑ l, Γ ν l * Jm ν b * Jm l c + H b c) :
    ∑ a, ((∑ k, u k * H k a) * u a + J a * (-∑ b, ∑ c, Γ' a b c * u b * u c)) =
      -∑ ν, ∑ l, Γ ν l * (∑ b, Jm ν b * u b) * (∑ c, Jm l c * u c) := by
  have h1 : ∑ a, J a * (-∑ b, ∑ c, Γ' a b c * u b * u c) =
      -∑ b, ∑ c, (∑ a, J a * Γ' a b c) * u b * u c := by
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : ∑ a, (∑ k, u k * H k a) * u a = ∑ b, ∑ c, H b c * u b * u c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have h3 : ∑ ν, ∑ l, Γ ν l * (∑ b, Jm ν b * u b) * (∑ c, Jm l c * u c) =
      ∑ b, ∑ c, (∑ ν, ∑ l, Γ ν l * Jm ν b * Jm l c) * u b * u c := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [sum4_comm fun b c ν l => Γ ν l * Jm ν b * Jm l c * u b * u c]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  rw [Finset.sum_add_distrib, h1, h2, h3]
  simp only [hlaw, add_mul, Finset.sum_add_distrib]
  ring

/-- **Geodesics are chart-independent**: the image of a geodesic of the pulled-back metric under a chart
change is a geodesic, with velocity `J u`. -/
theorem IsGeodesicOn.map_chartChange (hg : Lightlike.IsCoordMetric g U)
    (hφ : Lightlike.IsChartChange φ V U) {c u : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hgeo : IsGeodesicOn (Lightlike.pullback g φ) c u I) (hc : ∀ t ∈ I, c t ∈ V) :
    IsGeodesicOn g (fun t => φ (c t)) (fun t => Lightlike.jac φ (c t) *ᵥ u t) I where
  pos := fun t ht => by
    rw [hasDerivAt_pi]
    intro μ
    have hd : DifferentiableAt ℝ (fun z => φ z μ) (c t) :=
      ((hφ.smooth μ).contDiffAt (hφ.isOpen.mem_nhds (hc t ht))).differentiableAt (by simp)
    refine (hasDerivAt_comp_pd hd (hgeo.pos t ht)).congr_deriv ?_
    show ∑ k, u t k * Lightlike.pd k (fun z => φ z μ) (c t) = ∑ k, Lightlike.jac φ (c t) μ k * u t k
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  vel := fun t ht => by
    rw [hasDerivAt_pi]
    intro μ
    have hV := hc t ht
    -- the derivative of the Jacobian along the curve
    have hJ : ∀ a, HasDerivAt (fun s => Lightlike.jac φ (c s) μ a)
        (∑ k, u t k * Lightlike.hess φ μ k a (c t)) t := fun a => by
      have hd : DifferentiableAt ℝ (fun z => Lightlike.jac φ z μ a) (c t) :=
        ((hφ.contDiffOn_jac μ a).contDiffAt (hφ.isOpen.mem_nhds hV)).differentiableAt (by simp)
      exact hasDerivAt_comp_pd hd (hgeo.pos t ht)
    have hu : ∀ a, HasDerivAt (fun s => u s a) (accel (Lightlike.pullback g φ) (c t) (u t) a) t :=
      fun a => hasDerivAt_pi.1 (hgeo.vel t ht) a
    have hsum : HasDerivAt (fun s => ∑ a, Lightlike.jac φ (c s) μ a * u s a)
        (∑ a, ((∑ k, u t k * Lightlike.hess φ μ k a (c t)) * u t a +
          Lightlike.jac φ (c t) μ a * accel (Lightlike.pullback g φ) (c t) (u t) a)) t :=
      HasDerivAt.fun_sum fun a _ => (hJ a).mul (hu a)
    refine hsum.congr_deriv ?_
    have hlaw : ∀ b d, ∑ a, Lightlike.jac φ (c t) μ a *
        Lightlike.christoffel (Lightlike.pullback g φ) a b d (c t) =
        ∑ ν, ∑ l, Lightlike.christoffel g μ ν l (φ (c t)) * Lightlike.jac φ (c t) ν b *
          Lightlike.jac φ (c t) l d + Lightlike.hess φ μ b d (c t) := fun b d =>
      Lightlike.christoffel_pullback hg hφ hV μ b d
    exact accel_transform (fun a => Lightlike.jac φ (c t) μ a) (fun ν b => Lightlike.jac φ (c t) ν b)
      (fun a b d => Lightlike.christoffel (Lightlike.pullback g φ) a b d (c t))
      (fun ν l => Lightlike.christoffel g μ ν l (φ (c t))) (fun b d => Lightlike.hess φ μ b d (c t))
      (u t) hlaw

/-- A geodesic of `g₁` in an open set on which `g₁ = g₂` is a geodesic of `g₂`. -/
theorem IsGeodesicOn.congr_metric {g₁ g₂ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hU : IsOpen U)
    (h : ∀ y ∈ U, g₁ y = g₂ y) {c u : ℝ → Fin n → ℝ} {I : Set ℝ} (hgeo : IsGeodesicOn g₁ c u I)
    (hc : ∀ t ∈ I, c t ∈ U) : IsGeodesicOn g₂ c u I where
  pos := hgeo.pos
  vel := fun t ht => by
    have : accel g₂ (c t) (u t) = accel g₁ (c t) (u t) := by
      funext i
      simp only [accel, Lightlike.christoffel_congr_on hU h (hc t ht)]
    rw [this]
    exact hgeo.vel t ht

/-- Translating the parameter of a geodesic. -/
theorem IsGeodesicOn.shift {c u : ℝ → Fin n → ℝ} {I : Set ℝ} (h : IsGeodesicOn g c u I) (a : ℝ) :
    IsGeodesicOn g (fun t => c (t - a)) (fun t => u (t - a)) ((fun t => t - a) ⁻¹' I) where
  pos := fun t ht => (h.pos (t - a) ht).comp_sub_const t a
  vel := fun t ht => (h.vel (t - a) ht).comp_sub_const t a

/-- **Lifting a geodesic through an injective chart change.** If `φ ∘ c = σ` is a geodesic of `g` with velocity
`wσ`, then `c` is a geodesic of the pulled-back metric, with velocity `J⁻¹ wσ`. -/
theorem IsGeodesicOn.lift_chartChange {g' : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : Lightlike.IsCoordMetric g U) (hg' : Lightlike.IsCoordMetric g' V)
    (hφ : Lightlike.IsChartChange φ V U) (hpull : ∀ y ∈ V, Lightlike.pullback g φ y = g' y)
    (hinj : InjOn φ V) {σ wσ c : ℝ → Fin n → ℝ} {O : Set ℝ} (hO : IsOpen O)
    (hσ : IsGeodesicOn g σ wσ O) (hcV : ∀ s ∈ O, c s ∈ V) (hcσ : ∀ s ∈ O, φ (c s) = σ s) :
    IsGeodesicOn g' c (fun s => (Lightlike.jac φ (c s))⁻¹ *ᵥ wσ s) O := by
  -- the local statement at `s₀`
  have key : ∀ s₀ ∈ O, ∃ γ w : ℝ → Fin n → ℝ, ∃ I : Set ℝ, I ∈ 𝓝 s₀ ∧ IsGeodesicOn g' γ w I ∧
      c =ᶠ[𝓝 s₀] γ ∧ (fun s => (Lightlike.jac φ (c s))⁻¹ *ᵥ wσ s) =ᶠ[𝓝 s₀] w := by
    intro s₀ hs₀
    set v₀ := (Lightlike.jac φ (c s₀))⁻¹ *ᵥ wσ s₀ with hv₀
    obtain ⟨r, hr, ε, hε, H⟩ := exists_geodesic hg' (hcV s₀ hs₀) v₀
    obtain ⟨γ₀, w₀, hγ0, hw0, hγ⟩ := H v₀ (by simpa using hr.le)
    set γ : ℝ → Fin n → ℝ := fun t => γ₀ (t - s₀) with hγdef
    set w : ℝ → Fin n → ℝ := fun t => w₀ (t - s₀) with hwdef
    have hsh : IsGeodesicOn g' γ w ((fun t => t - s₀) ⁻¹' Ioo (-ε) ε) := hγ.shift s₀
    have hI1 : (fun t => t - s₀) ⁻¹' Ioo (-ε) ε ∈ 𝓝 s₀ :=
      (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
        (by simpa using Ioo_mem_nhds (neg_lt_zero.2 hε) hε)
    have hγs : γ s₀ = c s₀ := by simp [hγdef, hγ0]
    have hws : w s₀ = v₀ := by simp [hwdef, hw0]
    have hcont : ContinuousAt γ s₀ := (hsh.pos s₀ (mem_of_mem_nhds hI1)).continuousAt
    have hV : γ ⁻¹' V ∈ 𝓝 s₀ :=
      hcont.preimage_mem_nhds (hφ.isOpen.mem_nhds (by rw [hγs]; exact hcV s₀ hs₀))
    obtain ⟨I, hIsub, hIopen, hIs⟩ := mem_nhds_iff.1 (inter_mem hI1 hV)
    have hgeoI : IsGeodesicOn g' γ w I :=
      ⟨fun t ht => hsh.pos t (hIsub ht).1, fun t ht => hsh.vel t (hIsub ht).1⟩
    have hγV : ∀ t ∈ I, γ t ∈ V := fun t ht => (hIsub ht).2
    have hpb : IsGeodesicOn (Lightlike.pullback g φ) γ w I :=
      hgeoI.congr_metric hφ.isOpen (fun y hy => (hpull y hy).symm) hγV
    have himg := hpb.map_chartChange hg hφ hγV
    have hJ : ∀ y ∈ V, Lightlike.jac φ y * (Lightlike.jac φ y)⁻¹ = 1 := fun y hy =>
      Matrix.mul_nonsing_inv _ (hφ.isUnit_det y hy)
    have hJ' : ∀ y ∈ V, (Lightlike.jac φ y)⁻¹ * Lightlike.jac φ y = 1 := fun y hy =>
      Matrix.nonsing_inv_mul _ (hφ.isUnit_det y hy)
    have huniq := himg.eventuallyEq hg (hIopen.mem_nhds hIs) (hO.mem_nhds hs₀) hσ
      (hφ.mapsTo (hγV s₀ hIs)) (by rw [hγs]; exact hcσ s₀ hs₀)
      (by rw [hγs, hws, hv₀, Matrix.mulVec_mulVec, hJ _ (hcV s₀ hs₀), Matrix.one_mulVec])
    have hev : ∀ᶠ s in 𝓝 s₀, c s = γ s ∧ (Lightlike.jac φ (c s))⁻¹ *ᵥ wσ s = w s := by
      filter_upwards [huniq, hIopen.mem_nhds hIs, hO.mem_nhds hs₀] with s hs hsI hsO
      have h1 : φ (γ s) = σ s := (Prod.mk.inj hs).1
      have h2 : Lightlike.jac φ (γ s) *ᵥ w s = wσ s := (Prod.mk.inj hs).2
      have hcs : c s = γ s := hinj (hcV s hsO) (hγV s hsI) (by rw [hcσ s hsO, h1])
      refine ⟨hcs, ?_⟩
      rw [hcs, ← h2, Matrix.mulVec_mulVec, hJ' _ (hγV s hsI), Matrix.one_mulVec]
    exact ⟨γ, w, I, hIopen.mem_nhds hIs, hgeoI, hev.mono fun s hs => hs.1, hev.mono fun s hs => hs.2⟩
  constructor
  · intro s₀ hs₀
    obtain ⟨γ, w, I, hI, hgeo, h1, h2⟩ := key s₀ hs₀
    have := (hgeo.pos s₀ (mem_of_mem_nhds hI)).congr_of_eventuallyEq h1
    rwa [← h2.self_of_nhds] at this
  · intro s₀ hs₀
    obtain ⟨γ, w, I, hI, hgeo, h1, h2⟩ := key s₀ hs₀
    have := (hgeo.vel s₀ (mem_of_mem_nhds hI)).congr_of_eventuallyEq h2
    rwa [← h2.self_of_nhds, ← h1.self_of_nhds] at this

end Lightlike.Geodesic
