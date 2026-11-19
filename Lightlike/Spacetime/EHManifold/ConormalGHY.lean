import Lightlike.Spacetime.EHManifold.GibbonsHawkingYork
import Lightlike.Spacetime.EHManifold.ConormalAlg

/-!
# The Gibbons–Hawking–York density of a boundary with a general conormal

For a boundary `{u = 0}` with conormal `ν_α = ∂_α u` and `dν_{αβ} = ∂_α ∂_β u`:

* `conormalHup g ν x α β = g^{αβ} - N^α N^β / N²` with `N^α = g^{αβ} ν_β`: the induced inverse metric;
* `ghyDensityOf g ν dν x = 2 √|g| h^{αβ} (∂_α ν_β - Γ^μ_{αβ} ν_μ)`: the Gibbons–Hawking–York density
  `2 √|h| K` of the boundary, with respect to the coordinate volume of coordinates `(y, u)` adapted to the
  boundary with unit Jacobian (for instance the graph chart `u = x_i - γ(x')`): `√|h| = √|g| |N|` and
  `K = h^{αβ} ∇_α (ν_β / |N|) = h^{αβ} ∇_α ν_β / |N|`, since `h^{αβ} ν_β = 0`;
* `ghyDensityOf_add_smul_of_zero`: at a point where the perturbation `h` vanishes, the density of `g + t h`
  is affine in `t` with slope `-2 √|g| h^{αβ} δΓ^μ_{αβ} ν_μ`;
* `ghySlopeOf_eq_neg_flux`: if moreover the derivatives of `h` at the point are `∂_τ h_{ab} = ν_τ k_{ab}`
  (which holds when `h` vanishes on the boundary), the slope is `-√|g| W^ρ ν_ρ`: minus the flux of the
  Palatini vector through the boundary.

For `ν = e_i`, `dν = 0` this is the coordinate-face case of `GibbonsHawkingYork.lean` and `GHYBox.lean`.

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eqs. (4.1) to (4.4), p. 20.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The induced inverse metric `g^{αβ} - N^α N^β / N²` of a boundary with conormal `ν`, where
`N^α = g^{αβ} ν_β`. -/
def conormalHup (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ν : Fin n → ℝ) (x : Fin n → ℝ)
    (α β : Fin n) : ℝ :=
  (g x)⁻¹ α β - (∑ b, (g x)⁻¹ α b * ν b) * (∑ b, (g x)⁻¹ β b * ν b) /
    (∑ a, ν a * ∑ b, (g x)⁻¹ a b * ν b)

/-- **The Gibbons–Hawking–York density** `2 √|g| h^{αβ} (∂_α ν_β - Γ^μ_{αβ} ν_μ)` of a boundary with conormal
`ν` and derivative `dν` of the conormal. -/
def ghyDensityOf (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ν : Fin n → ℝ)
    (dν : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  2 * √|(g x).det| * ∑ α, ∑ β, conormalHup g ν x α β *
    (dν α β - ∑ μ, christoffel g μ α β x * ν μ)

/-- **The variation of the Christoffel symbols at a boundary point**: if `h` vanishes at the point and its
derivatives there are `∂_τ h_{ab} = ν_τ k_{ab}`. -/
theorem dChristoffel_of_conormal (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (ν : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (hx0 : h x = 0)
    (hpd : ∀ τ a b, pd τ (fun z => h z a b) x = ν τ * k a b) (ρ σ τ : Fin n) :
    dChristoffel g h ρ σ τ x =
      (1 / 2) * (ν σ * (∑ l, (g x)⁻¹ ρ l * k l τ) + ν τ * (∑ l, (g x)⁻¹ ρ l * k l σ) -
        (∑ b, (g x)⁻¹ ρ b * ν b) * k σ τ) := by
  unfold dChristoffel
  rw [hx0]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, neg_zero, zero_mul, zero_add]
  congr 1
  simp only [hpd]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **`h^{αβ} δΓ^μ_{αβ} ν_μ = ½ W^ρ ν_ρ`** at a boundary point where the perturbation vanishes. -/
theorem sum_conormalHup_dChristoffel (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (ν : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (hx0 : h x = 0)
    (hpd : ∀ τ a b, pd τ (fun z => h z a b) x = ν τ * k a b)
    (hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a) (hk : ∀ a b, k a b = k b a)
    (hS0 : (∑ a, ν a * ∑ b, (g x)⁻¹ a b * ν b) ≠ 0) :
    ∑ α, ∑ β, conormalHup g ν x α β * ∑ μ, dChristoffel g h μ α β x * ν μ =
      (1 / 2) * ∑ ρ, Wvec g h ρ x * ν ρ := by
  have hD := fun ρ σ τ => dChristoffel_of_conormal g h x ν k hx0 hpd ρ σ τ
  have e1 := conormal_hup (fun a b => (g x)⁻¹ a b) k ν (fun ρ σ τ => dChristoffel g h ρ σ τ x) hinv hk
    hD hS0
  have e2 := conormal_flux (fun a b => (g x)⁻¹ a b) k ν (fun ρ σ τ => dChristoffel g h ρ σ τ x) hinv hk
    hD
  unfold conormalHup
  refine e1.trans ?_
  rw [← e2]
  rfl

/-- **At a point where the perturbation vanishes, the Gibbons–Hawking–York density of `g + t h` is affine
in `t`**, with slope `-2 √|g| h^{αβ} δΓ^μ_{αβ} ν_μ`. -/
theorem ghyDensityOf_add_smul_of_zero (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (ν : Fin n → ℝ) (dν : Fin n → Fin n → ℝ) (hgd : ∀ l k, DifferentiableAt ℝ (fun y => g y l k) x)
    (hhd : ∀ l k, DifferentiableAt ℝ (fun y => h y l k) x) (hx0 : h x = 0) (t : ℝ) :
    ghyDensityOf (fun y => g y + t • h y) ν dν x =
      ghyDensityOf g ν dν x +
        t * (-2 * √|(g x).det| *
          ∑ α, ∑ β, conormalHup g ν x α β * ∑ μ, dChristoffel g h μ α β x * ν μ) := by
  have hH : ∀ α β, conormalHup (fun y => g y + t • h y) ν x α β = conormalHup g ν x α β := by
    intro α β
    simp only [conormalHup, hx0, smul_zero, add_zero]
  have hs : ∑ α, ∑ β, conormalHup g ν x α β *
        (dν α β - ∑ μ, christoffel (fun y => g y + t • h y) μ α β x * ν μ) =
      (∑ α, ∑ β, conormalHup g ν x α β * (dν α β - ∑ μ, christoffel g μ α β x * ν μ)) -
        t * ∑ α, ∑ β, conormalHup g ν x α β * ∑ μ, dChristoffel g h μ α β x * ν μ := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    have e : ∑ μ, christoffel (fun y => g y + t • h y) μ α β x * ν μ =
        (∑ μ, christoffel g μ α β x * ν μ) + t * ∑ μ, dChristoffel g h μ α β x * ν μ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun μ _ => by
        rw [christoffel_add_smul_of_zero g h x hgd hhd hx0]
        ring
    rw [e]
    ring
  have hunf : ghyDensityOf (fun y => g y + t • h y) ν dν x =
      2 * √|(g x).det| * ∑ α, ∑ β, conormalHup g ν x α β *
        (dν α β - ∑ μ, christoffel (fun y => g y + t • h y) μ α β x * ν μ) := by
    simp only [ghyDensityOf, hH, hx0, smul_zero, add_zero]
  rw [hunf, hs]
  unfold ghyDensityOf
  ring

/-- **The slope of the Gibbons–Hawking–York density is minus the Palatini flux through the boundary**, at
a boundary point where the perturbation vanishes with derivatives `∂_τ h_{ab} = ν_τ k_{ab}`. -/
theorem ghySlopeOf_eq_neg_flux (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (ν : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (hx0 : h x = 0)
    (hpd : ∀ τ a b, pd τ (fun z => h z a b) x = ν τ * k a b)
    (hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a) (hk : ∀ a b, k a b = k b a)
    (hS0 : (∑ a, ν a * ∑ b, (g x)⁻¹ a b * ν b) ≠ 0) :
    -2 * √|(g x).det| * ∑ α, ∑ β, conormalHup g ν x α β * ∑ μ, dChristoffel g h μ α β x * ν μ =
      -∑ ρ, ehFlux g h ρ x * ν ρ := by
  rw [sum_conormalHup_dChristoffel g h x ν k hx0 hpd hinv hk hS0]
  have e : ∑ ρ, ehFlux g h ρ x * ν ρ = √|(g x).det| * ∑ ρ, Wvec g h ρ x * ν ρ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by
      unfold ehFlux
      ring
  rw [e]
  ring

end Lightlike
