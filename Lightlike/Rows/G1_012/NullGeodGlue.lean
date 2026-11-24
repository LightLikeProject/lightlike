import Lightlike.Rows.G1_012.NullGeodCausal
import Lightlike.Rows.G1_012.GeodesicUnique
import Lightlike.Spacetime.GeodesicChartChange

/-!
# Locality, affine reparametrisation and gluing of null geodesics (G1-012)

`IsNullGeodesicOn` is a local notion (a chart statement near each parameter). This file proves that
it only depends on the germ of the curve (`IsNullGeodesicOn.congr_eventuallyEq`), is invariant under
affine reparametrisation (`IsNullGeodesicOn.comp_affine`) and that two null geodesics on open
parameter sets which agree on the overlap glue to one on the union (`IsNullGeodesicOn.union`).
-/

open Bundle Manifold Set Filter Topology Matrix
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}
  {γ γ' : ℝ → M} {J : Set ℝ}

/-- **Null geodesics are local**: they depend only on the germ of the curve at each parameter. -/
theorem IsNullGeodesicOn.congr_eventuallyEq (h : IsNullGeodesicOn g γ J)
    (hev : ∀ t ∈ J, γ =ᶠ[𝓝 t] γ') : IsNullGeodesicOn g γ' J := by
  intro t ht
  obtain ⟨w, O, hO, hsrc, hgeo, hw0, hbil⟩ := h t ht
  have hev' := hev t ht
  have hγt : γ' t = γ t := (hev'.self_of_nhds).symm
  set O' : Set ℝ := {s | γ s = γ' s} ∩ O with hO'
  have hO'n : O' ∈ 𝓝 t := Filter.inter_mem hev' hO
  -- the chart at `γ' t = γ t`
  have hO'o : ∀ s ∈ interior O', O' ∈ 𝓝 s := fun s hs => mem_interior_iff_mem_nhds.1 hs
  refine ⟨w, interior O', interior_mem_nhds.2 hO'n, fun s hs => ?_, ?_, ?_, ?_⟩
  · have hs' := interior_subset hs
    rw [hγt, ← hs'.1]; exact hsrc s hs'.2
  · refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · have hs' := interior_subset hs
      have h1 := hgeo.pos s hs'.2
      rw [hγt]
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [mem_interior_iff_mem_nhds.1 hs] with r hr
      show _ = _
      rw [hr.1]
    · have hs' := interior_subset hs
      have h1 := hgeo.vel s hs'.2
      rw [hγt]
      rw [show γ' s = γ s from hs'.1.symm]
      exact h1
  · exact hw0
  · rw [hγt]; exact hbil

/-- Scaling a vector scales its square norm by `c²`. -/
theorem bil_smul_self (G : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (u : Fin n → ℝ) :
    bil G (c • u) (c • u) = c ^ 2 * bil G u u := by
  simp only [bil, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

/-- **Null geodesics are invariant under affine reparametrisation.** -/
theorem IsNullGeodesicOn.comp_affine (h : IsNullGeodesicOn g γ J) {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    IsNullGeodesicOn g (fun s => γ (c * s + d)) ((fun s => c * s + d) ⁻¹' J) := by
  intro t ht
  obtain ⟨w, O, hO, hsrc, hgeo, hw0, hbil⟩ := h (c * t + d) ht
  have hcont : Continuous fun s : ℝ => c * s + d := by fun_prop
  have hO' : (fun s => c * s + d) ⁻¹' O ∈ 𝓝 t := hcont.continuousAt.preimage_mem_nhds hO
  refine ⟨fun s => c • w (c * s + d), (fun s => c * s + d) ⁻¹' O, hO', fun s hs => hsrc _ hs,
    ?_, ?_, ?_⟩
  · set a' : ℝ := -d / c with ha'
    have h1 := (hgeo.scale c).shift a'
    have e : ∀ s : ℝ, c * (s - a') = c * s + d := fun s => by rw [ha']; field_simp; ring
    have hset : (fun s : ℝ => s - a') ⁻¹' ((fun s => c * s) ⁻¹' O) =
        (fun s => c * s + d) ⁻¹' O := by
      ext s; simp only [mem_preimage, e]
    rw [hset] at h1
    simpa only [e] using h1
  · simp only [ne_eq, smul_eq_zero, hc, false_or]; exact hw0
  · rw [bil_smul_self, hbil, mul_zero]

open Classical in
/-- **Gluing null geodesics.** Two null geodesics on open parameter sets which agree on the overlap
glue to a null geodesic on the union. -/
theorem IsNullGeodesicOn.union {γ₁ γ₂ : ℝ → M} {J₁ J₂ : Set ℝ} (h₁ : IsNullGeodesicOn g γ₁ J₁)
    (h₂ : IsNullGeodesicOn g γ₂ J₂) (hJ₁ : IsOpen J₁) (hJ₂ : IsOpen J₂)
    (hag : EqOn γ₁ γ₂ (J₁ ∩ J₂)) :
    IsNullGeodesicOn g (fun s => if s ∈ J₁ then γ₁ s else γ₂ s) (J₁ ∪ J₂) := by
  have h1 : IsNullGeodesicOn g (fun s => if s ∈ J₁ then γ₁ s else γ₂ s) J₁ :=
    h₁.congr_eventuallyEq fun s hs => by
      filter_upwards [hJ₁.mem_nhds hs] with r hr
      simp [hr]
  have h2 : IsNullGeodesicOn g (fun s => if s ∈ J₁ then γ₁ s else γ₂ s) J₂ :=
    h₂.congr_eventuallyEq fun s hs => by
      filter_upwards [hJ₂.mem_nhds hs] with r hr
      by_cases hr1 : r ∈ J₁
      · simp [hr1, hag ⟨hr1, hr⟩]
      · simp [hr1]
  intro t ht
  exact ht.elim (fun h => h1 t h) (fun h => h2 t h)

end Lightlike.Penrose
