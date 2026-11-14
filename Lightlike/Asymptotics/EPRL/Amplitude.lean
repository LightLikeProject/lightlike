import Lightlike.Spin4.CoherentIntertwiner
import Lightlike.Oscillatory.Gaussian
import Lightlike.Oscillatory.PhaseReduction

/-!
# The coherent 15j integral and the Euclidean EPRL vertex integral

The large-spin asymptotics of the SU(2) 15j symbol and of the Euclidean EPRL vertex are
statements about integrals over `SU(2)^5` and `Spin(4)^5` of products of coherent-state
propagators (Barrett, Fairbairn, Hellmann, arXiv:0912.4907, eq. (1); Barrett, Dowdall, Fairbairn,
Gomes, Hellmann, J. Math. Phys. 50 (2009) 112504, arXiv:0902.1170, section 3). This file defines
these integrals and the Hessian that enters their asymptotics.

* The ten edges `ab`, `a < b`, of the complete graph `K₅` are ordered
  `01, 02, 03, 04, 12, 13, 14, 23, 24, 34`, as in `Lightlike.Spin4.k5Spins`: `edgeSrc` and `edgeTgt`.
* Boundary data `g : BdryData` assign to each edge `e = ab` two matrices, `g e 0 = g_ab` at the
  node `a` and `g e 1 = g_ba` at the node `b`. For `g_ab ∈ SU(2)`, the spin-`1/2` coherent state
  is the first column `g_ab e₀`, and the second column of `g_ab ε` is the antilinear structure map
  `J (g_ab e₀)`.
* `prop g X e = ⟨J g_ab e₀ | X_a† X_b | g_ba e₀⟩ = ((g_ab ε)† X_a† X_b g_ba)₀₀`, the propagator of
  the edge `e`. By `Lightlike.Spin4.inner_cohState`, its power `n` is the overlap of the spin-`n/2`
  coherent states of `X_a g_ab ε` and `X_b g_ba`.
* `coh15j n g = ∫_{SU(2)^5} Π_e prop^{n_e}` (Haar probability measure on each factor) and
  `eprlCoh n m g = ∫_{Spin(4)^5} Π_e prop(X⁺)^{n_e} prop(X⁻)^{m_e}`, the coherent integral forms of
  the 15j symbol and of the EPRL vertex (`γ < 1`, where both chiral halves of a boundary state
  carry the same normal). Spins are doubled: `n_e = 2j_e`.
* `chart X θ` moves `X_a` to `X_a exp((i/2) θ_a · σ)` for `a = 0, …, 3` and keeps `X_4`, which is
  the gauge fixing used in the asymptotic analysis; `hessAmp n g X` is the Hessian at `θ = 0` of
  `θ ↦ Π_e prop^{n_e}` in this chart, divided by the value at `X`. At a critical point it is the
  Hessian of `log Π_e prop^{n_e}`.
-/

open Matrix MeasureTheory Complex

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4

/-- The node `a` of the edge `e = ab`, `a < b`, of `K₅`, in the edge order
`01, 02, 03, 04, 12, 13, 14, 23, 24, 34`. -/
def edgeSrc : Fin 10 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3]

/-- The node `b` of the edge `e = ab`, `a < b`, of `K₅`. -/
def edgeTgt : Fin 10 → Fin 5 := ![1, 2, 3, 4, 2, 3, 4, 3, 4, 4]

/-- The matrix `ε = [[0, -1], [1, 0]]`. For `g ∈ SU(2)` with first column `(α, β)`, the first
column of `g ε` is `(-β̄, ᾱ)`, the image of `(α, β)` under the antilinear structure map `J`. -/
def epsMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- Boundary data of a 4-simplex: two matrices per edge `e = ab`, `g e 0 = g_ab` at the node `a`
and `g e 1 = g_ba` at the node `b`. -/
abbrev BdryData := Fin 10 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ

/-- **The propagator** of the edge `e = ab`:
`⟨J g_ab e₀ | X_a† X_b | g_ba e₀⟩ = ((g_ab ε)† X_a† X_b g_ba)₀₀`. -/
noncomputable def prop (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (e : Fin 10) : ℂ :=
  ((g e 0 * epsMat)ᴴ * (X (edgeSrc e))ᴴ * X (edgeTgt e) * g e 1) 0 0

/-- The integrand of the coherent 15j integral, `F_n(X) = Π_e prop(X)_e^{n_e}`, with doubled spins
`n`. -/
noncomputable def cohAmp (n : Fin 10 → ℕ) (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) :
    ℂ :=
  ∏ e, prop g X e ^ n e

/-- **The coherent 15j integral** `∫_{SU(2)^5} Π_e prop(X)_e^{n_e} dX`, with the Haar probability
measure on each factor (BFH, eq. (1), without the sign `(-1)^χ`). -/
noncomputable def coh15j (n : Fin 10 → ℕ) (g : BdryData) : ℂ :=
  ∫ X : Fin 5 → SU2, cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)) ∂(haarN (N := 5))

/-- **The coherent EPRL integral** `∫_{Spin(4)^5} Π_e prop(X⁺)_e^{n_e} prop(X⁻)_e^{m_e} dX`, with
`X = (X⁺, X⁻)` and the Haar probability measure on each factor; `n` and `m` are the doubled
self-dual and anti-self-dual spins. -/
noncomputable def eprlCoh (n m : Fin 10 → ℕ) (g : BdryData) : ℂ :=
  ∫ X : Fin 5 → Spin4, cohAmp n g (fun a => ((X a).1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      cohAmp m g (fun a => ((X a).2 : Matrix (Fin 2) (Fin 2) ℂ)) ∂Measure.pi fun _ => haarSpin4

/-- The element `(i/2) θ · σ = (i/2) [[θ₂, θ₀ - iθ₁], [θ₀ + iθ₁, -θ₂]]` of `su(2)`, with the Pauli
matrices `σ`. -/
noncomputable def su2Gen (θ : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (I / 2) • !![(θ 2 : ℂ), θ 0 - I * θ 1; θ 0 + I * θ 1, -(θ 2 : ℂ)]

/-- **The chart** around `X`: `X_a ↦ X_a exp((i/2) θ_a · σ)` for `a = 0, …, 3`, with
`θ_a = (θ_{3a}, θ_{3a+1}, θ_{3a+2})`, and `X_4` fixed. -/
noncomputable def chart (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (θ : Fin 12 → ℝ) :
    Fin 5 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun a => if h : (a : ℕ) < 4 then
    X a * NormedSpace.exp (su2Gen fun k => θ (finProdFinEquiv (⟨a, h⟩, k))) else X a

/-- **The Hessian** `H = F(X)⁻¹ ∂²_θ F(chart X θ)|_{θ=0}` of `F = cohAmp n g` in the chart around
`X`, a `12 × 12` complex matrix. At a critical point (`∂_θ F = 0`) it is the Hessian of `log F`. -/
noncomputable def hessAmp (n : Fin 10 → ℕ) (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 12) (Fin 12) ℂ :=
  (cohAmp n g X)⁻¹ • Lightlike.Oscillatory.hessMat (fun θ => cohAmp n g (chart X θ)) 0

end Lightlike.Asymptotics.EPRL
