import Lightlike.Regge.Geodesic.Metric
import Lightlike.Spacetime.RiemannSymmetry

/-!
# The geodesic equation in a chart

Step 2 of RC6a. A geodesic of the coordinate metric `g` is a curve `γ` with velocity `w = γ'`
and acceleration `w' = -Γ(γ)(w, w)`, the Christoffel symbols of the core (`Lightlike.christoffel`). As a
first-order system on positions and velocities this is the flow of the geodesic vector field
`(x, v) ↦ (v, -Γ(x)(v, v))`, which is smooth on `U × ℝⁿ`, so Picard–Lindelöf applies.

## Definitions

* `accel g x v = -Γ(x)(v, v)`; `geodField g (x, v) = (v, accel g x v)`.
* `IsGeodesicOn g γ w I`: on `I`, `γ' = w` and `w' = accel g γ w`.

## Main results

* `contDiffOn_geodField`: the geodesic vector field is smooth on `U × ℝⁿ`.
* `exists_geodesic`: through every point of `U`, with every initial velocity near a given one,
  there is a geodesic, all defined on a common interval around `0`.
* `IsGeodesicOn.eventuallyEq`: two geodesics with the same initial point and velocity agree near
  the initial time.
* `IsGeodesicOn.scale`: `t ↦ γ(c t)` is a geodesic with velocity `c w(c t)`.
* `IsGeodesicOn.hasDerivAt_speed`: **geodesics have constant speed**, `g(w, w)' = 0`, by metric
  compatibility.
-/

open Set Filter Topology Matrix
open scoped ContDiff

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The acceleration of a geodesic through `x` with velocity `v`: `-Γ(x)(v, v)`. -/
noncomputable def accel (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x v : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => -∑ j, ∑ k, Lightlike.christoffel g i j k x * v j * v k

/-- The **geodesic vector field** on positions and velocities, `(x, v) ↦ (v, -Γ(x)(v, v))`. -/
noncomputable def geodField (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (p.2, accel g p.1 p.2)

/-- `γ` is a **geodesic** on `I` with velocity `w`: `γ' = w` and `w' = -Γ(γ)(w, w)` on `I`. -/
structure IsGeodesicOn (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (γ w : ℝ → Fin n → ℝ)
    (I : Set ℝ) : Prop where
  /-- The velocity is the derivative of the position. -/
  pos : ∀ t ∈ I, HasDerivAt γ (w t) t
  /-- The geodesic equation. -/
  vel : ∀ t ∈ I, HasDerivAt w (accel g (γ t) (w t)) t

/-- The acceleration is quadratic in the velocity. -/
theorem accel_smul (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (c : ℝ)
    (v : Fin n → ℝ) : accel g x (c • v) = c ^ 2 • accel g x v := by
  funext i
  simp only [accel, Pi.smul_apply, smul_eq_mul]
  rw [mul_neg, neg_inj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The geodesic vector field is smooth** on `U × ℝⁿ`. -/
theorem contDiffOn_geodField (hg : Lightlike.IsCoordMetric g U) :
    ContDiffOn ℝ ∞ (geodField g) (U ×ˢ univ) := by
  have hΓ : ∀ i j k, ContDiffOn ℝ ∞
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Lightlike.christoffel g i j k p.1) (U ×ˢ univ) :=
    fun i j k => (hg.contDiffOn_christoffel i j k).comp contDiffOn_fst fun p hp => hp.1
  refine contDiffOn_snd.prodMk ?_
  refine contDiffOn_pi.mpr fun i => ?_
  simp only [accel]
  refine (ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_).neg
  exact ((hΓ i j k).mul (by fun_prop : ContDiff ℝ ∞
    fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 j).contDiffOn).mul (by fun_prop : ContDiff ℝ ∞
    fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 k).contDiffOn

/-- The geodesic vector field is `C¹` at every point of `U × ℝⁿ`. -/
theorem contDiffAt_geodField (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (v : Fin n → ℝ) : ContDiffAt ℝ 1 (geodField g) (x, v) :=
  ((contDiffOn_geodField hg).contDiffAt ((hg.isOpen.prod isOpen_univ).mem_nhds
    (mk_mem_prod hx (mem_univ v)))).of_le (by exact_mod_cast le_top)

/-- A geodesic is an integral curve of the geodesic vector field. -/
theorem IsGeodesicOn.hasDerivAt_phase {γ w : ℝ → Fin n → ℝ} {I : Set ℝ}
    (h : IsGeodesicOn g γ w I) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => (γ s, w s)) (geodField g (γ t, w t)) t :=
  (h.pos t ht).prodMk (h.vel t ht)

/-- An integral curve of the geodesic vector field is a geodesic. -/
theorem isGeodesicOn_of_phase {α : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} {I : Set ℝ}
    (h : ∀ t ∈ I, HasDerivAt α (geodField g (α t)) t) :
    IsGeodesicOn g (fun t => (α t).1) (fun t => (α t).2) I :=
  ⟨fun t ht => (h t ht).fst, fun t ht => (h t ht).snd⟩

/-- **Geodesics exist.** Through `x ∈ U`, for every initial velocity `v` within `r` of `v₀`, there
is a geodesic with `γ 0 = x`, `γ' 0 = v`, all defined on the common interval `(-ε, ε)`. -/
theorem exists_geodesic (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (v₀ : Fin n → ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ v, ‖v - v₀‖ ≤ r →
      ∃ γ w : ℝ → Fin n → ℝ, γ 0 = x ∧ w 0 = v ∧ IsGeodesicOn g γ w (Ioo (-ε) ε) := by
  obtain ⟨r, hr, ε, hε, H⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
      (contDiffAt_geodField hg hx v₀) 0
  refine ⟨r, hr, ε, hε, fun v hv => ?_⟩
  have hmem : (x, v) ∈ Metric.closedBall (x, v₀) r := by
    rw [Metric.mem_closedBall, Prod.dist_eq, dist_self, dist_eq_norm]
    exact max_le hr.le hv
  obtain ⟨α, hα0, hα⟩ := H _ hmem
  refine ⟨fun t => (α t).1, fun t => (α t).2, by simp [hα0], by simp [hα0], ?_⟩
  exact isGeodesicOn_of_phase fun t ht => by simpa using hα t (by simpa using ht)

/-- **Geodesics are unique**: two geodesics through `x ∈ U` with the same initial velocity agree
near the initial time. -/
theorem IsGeodesicOn.eventuallyEq (hg : Lightlike.IsCoordMetric g U) {γ w γ' w' : ℝ → Fin n → ℝ}
    {I I' : Set ℝ} {t₀ : ℝ} (hI : I ∈ 𝓝 t₀) (hI' : I' ∈ 𝓝 t₀) (h : IsGeodesicOn g γ w I)
    (h' : IsGeodesicOn g γ' w' I') (hx : γ t₀ ∈ U) (h0 : γ t₀ = γ' t₀) (h1 : w t₀ = w' t₀) :
    (fun t => (γ t, w t)) =ᶠ[𝓝 t₀] fun t => (γ' t, w' t) := by
  obtain ⟨K, s, hs, hK⟩ := (contDiffAt_geodField hg hx (w t₀)).exists_lipschitzOnWith
  -- both phase curves stay in `s` near `t₀`
  have hc : ContinuousAt (fun t => (γ t, w t)) t₀ :=
    (h.hasDerivAt_phase (mem_of_mem_nhds hI)).continuousAt
  have hc' : ContinuousAt (fun t => (γ' t, w' t)) t₀ :=
    (h'.hasDerivAt_phase (mem_of_mem_nhds hI')).continuousAt
  have e1 : ∀ᶠ t in 𝓝 t₀, (γ t, w t) ∈ s := hc.eventually_mem hs
  have e2 : ∀ᶠ t in 𝓝 t₀, (γ' t, w' t) ∈ s := by
    have : (γ' t₀, w' t₀) = (γ t₀, w t₀) := by rw [h0, h1]
    exact hc'.eventually_mem (this ▸ hs)
  refine ODE_solution_unique_of_eventually (v := fun _ => geodField g) (s := fun _ => s)
    (Eventually.of_forall fun _ => hK) ?_ ?_ (by simp [h0, h1])
  · filter_upwards [hI, e1] with t ht hts
    exact ⟨h.hasDerivAt_phase ht, hts⟩
  · filter_upwards [hI', e2] with t ht hts
    exact ⟨h'.hasDerivAt_phase ht, hts⟩

/-- **Rescaling a geodesic**: `t ↦ γ(c t)` is a geodesic with velocity `t ↦ c w(c t)`. -/
theorem IsGeodesicOn.scale {γ w : ℝ → Fin n → ℝ} {I : Set ℝ} (h : IsGeodesicOn g γ w I)
    (c : ℝ) : IsGeodesicOn g (fun t => γ (c * t)) (fun t => c • w (c * t))
      ((fun t => c * t) ⁻¹' I) := by
  constructor
  · intro t ht
    exact ((h.pos (c * t) ht).scomp t ((hasDerivAt_id' t).const_mul c)).congr_deriv
      (by rw [mul_one])
  · intro t ht
    refine (((h.vel (c * t) ht).scomp t ((hasDerivAt_id' t).const_mul c)).const_smul
      c).congr_deriv ?_
    rw [accel_smul, mul_one, smul_smul, sq]

/-! ## Constant speed -/

/-- The derivative of `f ∘ γ` through partial derivatives: `(f ∘ γ)' = Σ_k w_k ∂_k f`. -/
theorem hasDerivAt_comp_pd {f : (Fin n → ℝ) → ℝ} {γ : ℝ → Fin n → ℝ} {w : Fin n → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t)) (hγ : HasDerivAt γ w t) :
    HasDerivAt (fun s => f (γ s)) (∑ k, w k * Lightlike.pd k f (γ t)) t := by
  refine (hf.hasFDerivAt.comp_hasDerivAt t hγ).congr_deriv ?_
  have hw : w = ∑ k, w k • (Pi.single k 1 : Fin n → ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single w]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext j
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk]
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, smul_eq_mul, Lightlike.pd]

/-- **Geodesics have constant speed**: along a geodesic in `U`, `g(w, w)` has derivative `0`.
The derivative of the metric is `∂_k g_{ij} = Γ_{ikj} + Γ_{jki}` (metric compatibility), and the
geodesic equation lowered with `g` gives the opposite of the same cubic sum. -/
theorem IsGeodesicOn.hasDerivAt_speed (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ}
    {I : Set ℝ} (h : IsGeodesicOn g γ w I) {t : ℝ} (ht : t ∈ I) (hγt : γ t ∈ U) :
    HasDerivAt (fun s => normSq g (γ s) (w s)) 0 t := by
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) (γ t) := fun i j =>
    ((hg.smooth i j).contDiffAt (hg.isOpen.mem_nhds hγt)).differentiableAt (by simp)
  have hgij : ∀ i j, HasDerivAt (fun s => g (γ s) i j)
      (∑ k, w t k * Lightlike.pd k (fun y => g y i j) (γ t)) t :=
    fun i j => hasDerivAt_comp_pd (hdiff i j) (h.pos t ht)
  have hw : ∀ i, HasDerivAt (fun s => w s i) (accel g (γ t) (w t) i) t := fun i =>
    hasDerivAt_pi.mp (h.vel t ht) i
  -- `normSq = Σ_i Σ_j w_i g_ij w_j`
  have hform : (fun s => normSq g (γ s) (w s)) =
      fun s => ∑ i, ∑ j, w s i * (g (γ s) i j * w s j) := by
    funext s
    simp only [normSq, dotProduct, mulVec, Finset.mul_sum]
  rw [hform]
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hw i).mul ((hgij i j).mul (hw j))
  refine hd.congr_deriv ?_
  simp only [Pi.mul_apply]
  -- the algebra: metric compatibility and the lowered geodesic equation
  set v := w t
  set y₀ := γ t with hy₀
  have hpd : ∀ k i j, Lightlike.pd k (fun z => g z i j) y₀ =
      Lightlike.christoffelFirst g i k j y₀ + Lightlike.christoffelFirst g j k i y₀ :=
    fun k i j => hg.pd_eq_christoffelFirst hγt k i j
  have hlow : ∀ j, ∑ i, g y₀ i j * accel g y₀ v i =
      -∑ k, ∑ l, Lightlike.christoffelFirst g j k l y₀ * v k * v l := by
    intro j
    have hsym : ∀ i, g y₀ i j = g y₀ j i := fun i => by
      have := congrFun (congrFun (hg.symm y₀ hγt) j) i
      simpa [Matrix.transpose_apply] using this
    simp only [accel, mul_neg, Finset.sum_neg_distrib, neg_inj]
    simp only [hsym, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hg.lower_christoffel hγt j k l, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hlow' : ∀ i, ∑ j, g y₀ i j * accel g y₀ v j =
      -∑ k, ∑ l, Lightlike.christoffelFirst g i k l y₀ * v k * v l := by
    intro i
    rw [← hlow i]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := congrFun (congrFun (hg.symm y₀ hγt) i) j
    simp only [Matrix.transpose_apply] at this
    rw [this]
  -- split the derivative into three sums and evaluate each
  set S := ∑ j, ∑ k, ∑ l, Lightlike.christoffelFirst g j k l y₀ * v j * v k * v l with hS
  have hsplit : (∑ i, ∑ j, (accel g y₀ v i * (g y₀ i j * v j) +
      v i * ((∑ k, v k * Lightlike.pd k (fun z => g z i j) y₀) * v j + g y₀ i j * accel g y₀ v j))) =
      (∑ i, ∑ j, accel g y₀ v i * (g y₀ i j * v j)) + (∑ i, ∑ j, v i * (g y₀ i j * accel g y₀ v j)) +
      ∑ i, ∑ j, v i * ((∑ k, v k * Lightlike.pd k (fun z => g z i j) y₀) * v j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hT1 : (∑ i, ∑ j, accel g y₀ v i * (g y₀ i j * v j)) = -S := by
    rw [Finset.sum_comm, hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ∑ i, accel g y₀ v i * (g y₀ i j * v j) = (∑ i, g y₀ i j * accel g y₀ v i) * v j by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring,
      hlow j, neg_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hT3 : (∑ i, ∑ j, v i * (g y₀ i j * accel g y₀ v j)) = -S := by
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ∑ j, v i * (g y₀ i j * accel g y₀ v j) = v i * ∑ j, g y₀ i j * accel g y₀ v j by
        rw [Finset.mul_sum],
      hlow' i, mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hA : ∑ i, ∑ j, ∑ k, Lightlike.christoffelFirst g i k j y₀ * v i * v k * v j = S := by
    rw [hS]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  have hB : ∑ i, ∑ j, ∑ k, Lightlike.christoffelFirst g j k i y₀ * v j * v k * v i = S := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finset.sum_comm
  have hT2 : (∑ i, ∑ j, v i * ((∑ k, v k * Lightlike.pd k (fun z => g z i j) y₀) * v j)) =
      (∑ i, ∑ j, ∑ k, Lightlike.christoffelFirst g i k j y₀ * v i * v k * v j) +
        ∑ i, ∑ j, ∑ k, Lightlike.christoffelFirst g j k i y₀ * v j * v k * v i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hpd]
    ring
  rw [hA, hB] at hT2
  rw [hsplit, hT1, hT3, hT2]
  ring

end Lightlike.Geodesic
