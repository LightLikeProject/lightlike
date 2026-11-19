import Lightlike.Spacetime.FLRWManifold
import Lightlike.Spacetime.Hypersurface

/-!
# Trust check of GE13: a constant-time slice of FLRW has `K = (ȧ/a) h`

On the FLRW manifold `flrwOpen hI k` (`FLRWManifold.lean`) with the metric `g = -dt² + a(t)² dx²/(1 + k|x|²/4)²`, the slices of
constant cosmic time `t` are the level sets of `cosmicTime`, with the unit normal `∂_t` and `ε = -1`
(`isUnitNormal_flrwSlice`). For the Levi-Civita connection the second fundamental form is
`K(v, w) = (ȧ/a) (g(v, w) + v⁰ w⁰)` (`secondFF_flrwSlice`), the Hubble rate times the induced metric `h = g + n♭ ⊗ n♭` of the slice;
on tangent vectors `K = (ȧ/a) g` (`secondFF_flrwSlice_tangent`).

* `christoffel_congr_nhds`: the Christoffel symbols at `x` depend only on the metric near `x`;
* `flrw_coordField`: the coordinate fields of the open subset `flrwOpen` are the constant basis vectors.

Comparison: Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity* (gr-qc/0703035), eq. (3.24), p. 45, `L_m γ = −2N K`
(read): with lapse `N = 1` and `γ = a² γ^(k)` it gives `K = −(ȧ/a) γ`, ours with the opposite sign convention of the
extrinsic curvature (the GE13 convention, `K(v, w) = g(∇_v n, w)`, Gourgoulhon's (2.43) `K(u, v) = −u · ∇_v n`).
-/

open Manifold Set Filter TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section
namespace Lightlike

/-- **The Christoffel symbols at `x` depend only on the metric near `x`.** -/
theorem christoffel_congr_nhds {n : ℕ} {g₁ g₂ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    (h : g₁ =ᶠ[𝓝 x] g₂) (i j l : Fin n) : christoffel g₁ i j l x = christoffel g₂ i j l x := by
  unfold christoffel
  rw [h.eq_of_nhds]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : ∀ p q : Fin n, (fun y => g₁ y p q) =ᶠ[𝓝 x] (fun y => g₂ y p q) := fun p q =>
    h.mono fun y hy => by simp only [hy]
  rw [pd_congr (e m l) j, pd_congr (e m j) l, pd_congr (e j l) m]

namespace Cosmology

variable {I : Set ℝ} (hI : IsOpen I) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a I) (hpos : ∀ t ∈ I, 0 < a t) (k : ℝ)

/-- Every point of `flrwOpen` lies in the chart target of every chart. -/
theorem flrw_mem_target (x₀ y : flrwOpen hI k) :
    (y : Fin 4 → ℝ) ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).target := by
  have hs : y ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).source := by
    rw [extChartAt_source]
    simp [Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
  have := (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).map_source hs
  rwa [opens_extChartAt_apply] at this

/-- The inverse chart of `flrwOpen` is the inclusion. -/
theorem flrw_symm (x₀ y : flrwOpen hI k) : (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).symm (y : Fin 4 → ℝ) = y :=
  Subtype.ext (opens_extChartAt_symm _ x₀ (flrw_mem_target hI k x₀ y))

/-- **The coordinate fields of `flrwOpen` are the constant basis vectors.** -/
theorem flrw_coordField (x₀ y : flrwOpen hI k) (i : Fin 4) :
    coordField x₀ i y = (Pi.single i 1 : Fin 4 → ℝ) := by
  have h := coordField_apply x₀ i (flrw_mem_target hI k x₀ y)
  rw [coordBasis_apply, opens_symmL] at h
  rw [flrw_symm] at h
  exact h

/-- The cosmic time on the FLRW manifold. -/
def cosmicTime : flrwOpen hI k → ℝ := fun y => (y : Fin 4 → ℝ) 0

/-- The FLRW metric on two vectors: `g(v, w) = -v⁰w⁰ + Σᵢ (a S)² vⁱ wⁱ`. -/
theorem flrw_g_apply (y : flrwOpen hI k) (v w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) y) :
    (flrwManifoldMetric hI ha hpos k).g y v w = ∑ μ, dF a k (y : Fin 4 → ℝ) μ * v μ * w μ := by
  show matForm (flrwMetric a k (y : Fin 4 → ℝ)) v w = _
  refine (matForm_apply _ _ _).trans ?_
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_eq_single μ]
  · simp only [flrwMetric, Matrix.diagonal_apply_eq, dF]; ring
  · intro ν _ hν; simp [flrwMetric, Matrix.diagonal_apply_ne _ (Ne.symm hν)]
  · simp

/-- A vector of `ℝ⁴` is the sum of its components times the basis vectors. -/
theorem vec_eq_sum_single (v : Fin 4 → ℝ) : v = ∑ i, v i • (Pi.single i 1 : Fin 4 → ℝ) := by
  funext μ
  simp [Finset.sum_apply, Pi.single_apply]

/-- A tangent vector of `flrwOpen` is the sum of its components times the coordinate fields. -/
theorem flrw_vec_eq (x₀ y : flrwOpen hI k) (v : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) y) :
    v = ∑ i, v i • coordField x₀ i y := by
  simp only [flrw_coordField]
  exact vec_eq_sum_single v

/-- **The derivative of the cosmic time** is the time component: `dt(v) = v⁰`. -/
theorem mfderiv_cosmicTime (x₀ y : flrwOpen hI k) (v : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) y) :
    mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ) (cosmicTime hI k) y v = v 0 := by
  have hfun : cosmicTime hI k = (fun z : Fin 4 → ℝ => z 0) ∘ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀) := by
    funext z
    show (z : Fin 4 → ℝ) 0 = (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀ z) 0
    rw [opens_extChartAt_apply]
  have hs : y ∈ (chartAt (Fin 4 → ℝ) x₀).source := by
    simp [Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
  have hψ : MDifferentiableAt 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, Fin 4 → ℝ) (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀) y :=
    mdifferentiableAt_extChartAt hs
  have hp : MDifferentiableAt 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ) (fun z : Fin 4 → ℝ => z 0) (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀ y) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).differentiable _).mdifferentiableAt
  rw [hfun, mfderiv_comp y hp hψ]
  have hpd : mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ) (fun z : Fin 4 → ℝ => z 0) (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀ y) =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0) := by
    rw [mfderiv_eq_fderiv]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).fderiv
  rw [hpd]
  have hid : mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, Fin 4 → ℝ) (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀) y =
      ContinuousLinearMap.id ℝ (Fin 4 → ℝ) := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt hs, opens_continuousLinearMapAt]
  erw [hid]
  rfl

/-- **The constant-time slices of FLRW have the unit normal `∂_t`** (`ε = -1`). -/
theorem isUnitNormal_flrwSlice (x₀ : flrwOpen hI k) :
    Hypersurface.IsUnitNormal (flrwManifoldMetric hI ha hpos k).toNondegMetric (cosmicTime hI k) (coordField x₀ 0) (-1) x₀ := by
  refine ⟨Or.inr rfl, Eventually.of_forall fun y => ?_, ?_, Eventually.of_forall fun y => ?_,
    Eventually.of_forall fun y v => ?_⟩
  · exact (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).contDiff.contMDiff).comp
      contMDiff_subtype_val).contMDiffAt
  · have h : ContMDiffOn 𝓘(ℝ, Fin 4 → ℝ) (𝓘(ℝ, Fin 4 → ℝ).prod 𝓘(ℝ, Fin 4 → ℝ)) ∞
        (fun q : flrwOpen hI k => (⟨q, coordField x₀ 0 q⟩ : TangentBundle 𝓘(ℝ, Fin 4 → ℝ) (flrwOpen hI k)))
        (chartTriv 4 x₀).baseSet :=
      (chartTriv 4 x₀).contMDiffOn_localFrame_baseSet ∞ (Pi.basisFun ℝ (Fin 4)) 0
    filter_upwards [(chartTriv 4 x₀).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀)] with y hy
    exact h.contMDiffAt ((chartTriv 4 x₀).open_baseSet.mem_nhds hy)
  · show (flrwManifoldMetric hI ha hpos k).g y (coordField x₀ 0 y) (coordField x₀ 0 y) = -1
    rw [flrw_g_apply, flrw_coordField]
    simp [Fin.sum_univ_four, dF]
  · rw [mfderiv_cosmicTime hI k x₀ y v]
    show v 0 = 0 ↔ (flrwManifoldMetric hI ha hpos k).g y (coordField x₀ 0 y) v = 0
    rw [flrw_g_apply, flrw_coordField]
    simp only [Fin.sum_univ_four, dF]
    simp

/-- The Christoffel symbols `Γ^m_{i0}` of FLRW at a point of the manifold: `(ȧ/a) δ^m_i` for spatial `i`, zero for `i = 0`. -/
theorem flrw_christoffel_t (x₀ y : flrwOpen hI k) (m i : Fin 4) :
    christoffel ((flrwManifoldMetric hI ha hpos k).toNondegMetric.coordMetric x₀) m i 0 (y : Fin 4 → ℝ) =
      if i ≠ 0 ∧ m = i then Hf a (y : Fin 4 → ℝ) else 0 := by
  have hy := flrw_mem_target hI k x₀ y
  have hev : (flrwManifoldMetric hI ha hpos k).toNondegMetric.coordMetric x₀ =ᶠ[𝓝 (y : Fin 4 → ℝ)] flrwMetric a k := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin 4 → ℝ)) x₀).mem_nhds hy] with z hz
    exact flrwManifoldMetric_coordMetric hI ha hpos k x₀ hz
  rw [christoffel_congr_nhds hev]
  have hyI : (y : Fin 4 → ℝ) 0 ∈ I := y.2.1
  have hda : DifferentiableAt ℝ a ((y : Fin 4 → ℝ) 0) :=
    (ha.contDiffAt (hI.mem_nhds hyI)).differentiableAt (by simp)
  have hD : Dn k (y : Fin 4 → ℝ) ≠ 0 := (y.2.2).ne'
  rw [christoffel_flrw hda (hpos _ hyI).ne' hD]
  fin_cases m <;> fin_cases i <;> simp [Γf]

/-- **A constant-time slice of FLRW has `K = (ȧ/a) h`** (trust check of GE13): for the Levi-Civita connection and the unit
normal `∂_t`, `K(v, w) = (ȧ/a)(t) (g(v, w) + v⁰ w⁰)`, the Hubble rate times the induced metric `h = g + n♭ ⊗ n♭`. -/
theorem secondFF_flrwSlice (x₀ y : flrwOpen hI k) (v w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) y) :
    Hypersurface.secondFF (leviCivita (flrwManifoldMetric hI ha hpos k).toNondegMetric)
      (flrwManifoldMetric hI ha hpos k).toNondegMetric (coordField x₀ 0) y v w =
      Hf a (y : Fin 4 → ℝ) * ((flrwManifoldMetric hI ha hpos k).g y v w + v 0 * w 0) := by
  set g := (flrwManifoldMetric hI ha hpos k).toNondegMetric with hgdef
  have hcov : ∀ i, leviCivita g (coordField x₀ 0) y (coordField x₀ i y) =
      ∑ m, christoffel (g.coordMetric x₀) m i 0 (y : Fin 4 → ℝ) • coordField x₀ m y := by
    intro i
    have := leviCivita_coordField g x₀ (flrw_mem_target hI k x₀ y) i 0
    rwa [flrw_symm] at this
  have hnv : leviCivita g (coordField x₀ 0) y v =
      ((fun μ => Hf a (y : Fin 4 → ℝ) * (if μ = 0 then 0 else v μ)) : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) y) := by
    conv_lhs => rw [flrw_vec_eq hI k x₀ y v]
    rw [map_sum]
    simp only [map_smul]
    simp only [hcov]
    simp only [hgdef, flrw_christoffel_t, flrw_coordField]
    change (∑ i, v i • ∑ m, (if i ≠ 0 ∧ m = i then Hf a (y : Fin 4 → ℝ) else 0) • (Pi.single m 1 : Fin 4 → ℝ)) = _
    funext μ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four]
    fin_cases μ <;> simp <;> ring
  unfold Hypersurface.secondFF
  rw [hnv]
  show (flrwManifoldMetric hI ha hpos k).g y
    ((fun μ => Hf a (y : Fin 4 → ℝ) * (if μ = 0 then 0 else v μ)) : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) y) w = _
  erw [flrw_g_apply, flrw_g_apply]
  simp only [Fin.sum_univ_four, dF]
  simp
  ring

/-- **On tangent vectors of the slice `K = (ȧ/a) g`**: if `dt(v) = dt(w) = 0` then `K(v, w) = (ȧ/a) g(v, w)`. -/
theorem secondFF_flrwSlice_tangent (x₀ y : flrwOpen hI k) (v w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) y)
    (hv : mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, ℝ) (cosmicTime hI k) y v = 0) :
    Hypersurface.secondFF (leviCivita (flrwManifoldMetric hI ha hpos k).toNondegMetric)
      (flrwManifoldMetric hI ha hpos k).toNondegMetric (coordField x₀ 0) y v w =
      Hf a (y : Fin 4 → ℝ) * (flrwManifoldMetric hI ha hpos k).g y v w := by
  rw [secondFF_flrwSlice, show v 0 = 0 from (mfderiv_cosmicTime hI k x₀ y v).symm.trans hv, zero_mul, add_zero]

end Cosmology
end Lightlike
