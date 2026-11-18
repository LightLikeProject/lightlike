import Lightlike.Spacetime.VariationExchange

/-!
# The first variation of the Riemann, Ricci and scalar curvature in coordinates (GE15, stage S2)

For smooth `g, h` on `ℝⁿ` with `det g x ≠ 0`: `hasDerivAt_riemann` is the first variation of the coordinate Riemann tensor of `g + t h` at `x`
in terms of `δΓ = dChristoffel` and its derivatives (the linearised Riemann tensor), `hasDerivAt_ricci` that of the Ricci tensor
(`dRicci`), and `hasDerivAt_scalarCurvature` that of the scalar curvature, `δR = ∑ (-(g⁻¹ h g⁻¹)^{σν} R_{σν} + g^{σν} δR_{σν})`.

**Limits.** Stage S2 of the first variation of the Einstein-Hilbert action: the Palatini identity (`δR` as a divergence) and the integral
statement are later stages.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

section
variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (x : Fin n → ℝ) (hx : (g x).det ≠ 0)
include hg hh hx

theorem hasDerivAt_christoffel_x (i j k : Fin n) :
    HasDerivAt (fun t : ℝ => christoffel (fun z => g z + t • h z) i j k x) (dChristoffel g h i j k x) 0 :=
  hasDerivAt_christoffel_add_smul g h x (fun l k => ((hg l k).differentiable (by simp)) x)
    (fun l k => ((hh l k).differentiable (by simp)) x) hx i j k

/-- **The first variation of the Riemann tensor** in coordinates. -/
theorem hasDerivAt_riemann (ρ σ μ ν : Fin n) :
    HasDerivAt (fun t : ℝ => riemann (fun z => g z + t • h z) ρ σ μ ν x)
      (pd μ (dChristoffel g h ρ ν σ) x - pd ν (dChristoffel g h ρ μ σ) x +
        ∑ l, (dChristoffel g h ρ μ l x * christoffel g l ν σ x + christoffel g ρ μ l x * dChristoffel g h l ν σ x -
          dChristoffel g h ρ ν l x * christoffel g l μ σ x - christoffel g ρ ν l x * dChristoffel g h l μ σ x)) 0 := by
  have hΓ0 : ∀ a b c, christoffel (fun z => g z + (0 : ℝ) • h z) a b c x = christoffel g a b c x := by
    intro a b c; simp
  have h1 := hasDerivAt_pd_christoffel g h hg hh x hx ρ ν σ μ
  have h2 := hasDerivAt_pd_christoffel g h hg hh x hx ρ μ σ ν
  have h3 : ∀ l, HasDerivAt (fun t : ℝ => christoffel (fun z => g z + t • h z) ρ μ l x * christoffel (fun z => g z + t • h z) l ν σ x -
      christoffel (fun z => g z + t • h z) ρ ν l x * christoffel (fun z => g z + t • h z) l μ σ x)
      (dChristoffel g h ρ μ l x * christoffel g l ν σ x + christoffel g ρ μ l x * dChristoffel g h l ν σ x -
          (dChristoffel g h ρ ν l x * christoffel g l μ σ x + christoffel g ρ ν l x * dChristoffel g h l μ σ x)) 0 := by
    intro l
    have a1 := (hasDerivAt_christoffel_x g h hg hh x hx ρ μ l).mul (hasDerivAt_christoffel_x g h hg hh x hx l ν σ)
    have a2 := (hasDerivAt_christoffel_x g h hg hh x hx ρ ν l).mul (hasDerivAt_christoffel_x g h hg hh x hx l μ σ)
    have := a1.sub a2
    simp only [hΓ0] at this
    exact this
  have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun l _ => h3 l
  have h5 := (h1.sub h2).add h4
  unfold riemann
  convert h5 using 1
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring


/-- The first variation of the Ricci tensor in coordinates, `δR_{σν} = ∑_ρ δR^ρ_{σρν}`. -/
def dRicci (σ ν : Fin n) : ℝ :=
  ∑ ρ, (pd ρ (dChristoffel g h ρ ν σ) x - pd ν (dChristoffel g h ρ ρ σ) x +
        ∑ l, (dChristoffel g h ρ ρ l x * christoffel g l ν σ x + christoffel g ρ ρ l x * dChristoffel g h l ν σ x -
          dChristoffel g h ρ ν l x * christoffel g l ρ σ x - christoffel g ρ ν l x * dChristoffel g h l ρ σ x))

theorem hasDerivAt_ricci (σ ν : Fin n) :
    HasDerivAt (fun t : ℝ => ricci (fun z => g z + t • h z) σ ν x) (dRicci g h x σ ν) 0 := by
  have := HasDerivAt.fun_sum (u := Finset.univ) fun ρ _ => hasDerivAt_riemann g h hg hh x hx ρ σ ρ ν
  unfold ricci dRicci
  exact this

/-- **The first variation of the scalar curvature** in coordinates:
`δR = ∑ (-(g⁻¹ h g⁻¹)^{σν} R_{σν} + g^{σν} δR_{σν})`. -/
theorem hasDerivAt_scalarCurvature :
    HasDerivAt (fun t : ℝ => scalarCurvature (fun z => g z + t • h z) x)
      (∑ σ, ∑ ν, (-((g x)⁻¹ * h x * (g x)⁻¹) σ ν * ricci g σ ν x + (g x)⁻¹ σ ν * dRicci g h x σ ν)) 0 := by
  have hinv : ∀ σ ν, HasDerivAt (fun t : ℝ => ((g x + t • h x)⁻¹) σ ν) (-((g x)⁻¹ * h x * (g x)⁻¹) σ ν) 0 :=
    fun σ ν => hasDerivAt_inv_add_smul (g x) (h x) hx σ ν
  have h1 : ∀ σ ν, HasDerivAt (fun t : ℝ => ((g x + t • h x)⁻¹) σ ν * ricci (fun z => g z + t • h z) σ ν x)
      (-((g x)⁻¹ * h x * (g x)⁻¹) σ ν * ricci g σ ν x + (g x)⁻¹ σ ν * dRicci g h x σ ν) 0 := by
    intro σ ν
    have := (hinv σ ν).mul (hasDerivAt_ricci g h hg hh x hx σ ν)
    convert this using 1
    simp
  have := HasDerivAt.fun_sum (u := Finset.univ) fun σ _ => HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => h1 σ ν
  unfold scalarCurvature
  exact this

end

end Lightlike
