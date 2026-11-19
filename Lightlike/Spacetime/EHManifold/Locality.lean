import Lightlike.Spacetime.Curvature

/-!
# Locality of the coordinate curvature

The Christoffel symbols, the Riemann and Ricci tensors and the scalar curvature of a coordinate metric
`g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ` at a point `x` depend only on the germ of `g` at `x`: if `g` and
`g'` agree on a neighbourhood of `x`, they have the same curvature at `x` (`riemann_congr`, `ricci_congr`,
`scalarCurvature_congr`), and the same curvature near `x` (`christoffel_eventuallyEq`,
`scalarCurvature_eventuallyEq`).

Supporting lemmas for the Einstein–Hilbert variation on a manifold (a chart gives the metric components only
on the chart's target); no catalogue entry.
-/

open Filter Topology Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ} {g g' : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}

lemma eventuallyEq_entry (h : g =ᶠ[𝓝 x] g') (a b : Fin n) :
    (fun y => g y a b) =ᶠ[𝓝 x] fun y => g' y a b :=
  h.mono fun y hy => by
    show g y a b = g' y a b
    rw [hy]

lemma pd_eventuallyEq {f f' : (Fin n → ℝ) → ℝ} (h : f =ᶠ[𝓝 x] f') (k : Fin n) :
    pd k f =ᶠ[𝓝 x] pd k f' :=
  h.fderiv.mono fun y hy => by
    show fderiv ℝ f y (Pi.single k 1) = fderiv ℝ f' y (Pi.single k 1)
    rw [hy]

/-- The Christoffel symbols of two metrics that agree near `x` agree near `x`. -/
theorem christoffel_eventuallyEq (h : g =ᶠ[𝓝 x] g') (i j k : Fin n) :
    christoffel g i j k =ᶠ[𝓝 x] christoffel g' i j k := by
  have h1 : ∀ a b c : Fin n,
      pd a (fun y => g y b c) =ᶠ[𝓝 x] pd a (fun y => g' y b c) := fun a b c =>
    pd_eventuallyEq (eventuallyEq_entry h b c) a
  have hall : ∀ᶠ y in 𝓝 x, g y = g' y ∧
      ∀ a b c : Fin n, pd a (fun z => g z b c) y = pd a (fun z => g' z b c) y :=
    h.and (eventually_all.2 fun a => eventually_all.2 fun b => eventually_all.2 fun c => h1 a b c)
  exact hall.mono fun y hy => by
    show christoffel g i j k y = christoffel g' i j k y
    unfold christoffel
    simp only [hy.1, hy.2]

/-- The Riemann tensor at `x` depends only on the germ of the metric at `x`. -/
theorem riemann_congr (h : g =ᶠ[𝓝 x] g') (ρ σ μ ν : Fin n) :
    riemann g ρ σ μ ν x = riemann g' ρ σ μ ν x := by
  have hc : ∀ i j k : Fin n, christoffel g i j k x = christoffel g' i j k x := fun i j k =>
    (christoffel_eventuallyEq h i j k).eq_of_nhds
  have hp : ∀ a i j k : Fin n, pd a (christoffel g i j k) x = pd a (christoffel g' i j k) x :=
    fun a i j k => (pd_eventuallyEq (christoffel_eventuallyEq h i j k) a).eq_of_nhds
  unfold riemann
  simp only [hc, hp]

/-- The Ricci tensor at `x` depends only on the germ of the metric at `x`. -/
theorem ricci_congr (h : g =ᶠ[𝓝 x] g') (σ ν : Fin n) : ricci g σ ν x = ricci g' σ ν x := by
  unfold ricci
  simp only [riemann_congr h]

/-- **The scalar curvature at `x` depends only on the germ of the metric at `x`.** -/
theorem scalarCurvature_congr (h : g =ᶠ[𝓝 x] g') : scalarCurvature g x = scalarCurvature g' x := by
  unfold scalarCurvature
  simp only [ricci_congr h, h.eq_of_nhds]

/-- The scalar curvatures of two metrics that agree near `x` agree near `x`. -/
theorem scalarCurvature_eventuallyEq (h : g =ᶠ[𝓝 x] g') :
    scalarCurvature g =ᶠ[𝓝 x] scalarCurvature g' :=
  h.eventuallyEq_nhds.mono fun _ hy => scalarCurvature_congr hy

end Lightlike
