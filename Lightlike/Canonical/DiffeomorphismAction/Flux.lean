import Lightlike.Canonical.DiffeomorphismAction.Pullback

/-!
# Diffeomorphisms act on fluxes (row G2-015)

The second piece of the diffeomorphism action on the holonomy–flux algebra (`lost-2006`).  The electric field is a
matrix-valued vector density `E^a(x)` on the chart `ℝ³` (`Fl n`).  A `C¹` map `φ` pulls it back by the adjugate of the
Jacobian, `(φ*E)^a(x) = ∑_b adj(Dφ(x))^a_b E^b(φ x)` (`pullFlux`); for invertible `Dφ` this is
`det Dφ · (Dφ)⁻¹ E`, the usual transformation of a vector density of weight one.

The flux of `E` through a parametrised surface `σ : ℝ² → ℝ³` smeared with a matrix-valued function `f` is
`∫_{[0,1]²} tr (f · ∑_a (∂₁σ × ∂₂σ)_a E^a(σ))` (`Surf.flux`).  The covariance `flux S (φ*E) = flux (φ∘S) E`
(`Surf.flux_pullFlux`) is the content of this file; it uses only the identity `D s × D t = cof(D)(s × t)`
(`cross3_mulVec`), so it needs no invertibility of `Dφ`.
-/

open Matrix Set MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ}

/-- A **flux field** (electric field): a matrix-valued vector density on the chart `ℝ³`. -/
abbrev Fl (n : ℕ) := (Fin 3 → ℝ) → Fin 3 → Matrix (Fin n) (Fin n) ℂ

/-- The Jacobian matrix `(∂_b φ^a)(x)` of a map of the chart. -/
def jac (φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => fderiv ℝ φ x (Pi.single b 1) a

/-- The Jacobian matrix represents the Fréchet derivative. -/
lemma jac_mulVec (φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (x w : Fin 3 → ℝ) : jac φ x *ᵥ w = fderiv ℝ φ x w := by
  ext b
  have hv : w = ∑ a, w a • (Pi.single a (1 : ℝ) : Fin 3 → ℝ) := by
    ext c
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, jac, Matrix.mulVec,
    dotProduct, Matrix.of_apply, mul_comm]

/-- The **pullback of a flux field**: `(φ*E)^a(x) = ∑_b adj(Dφ(x))^a_b E^b(φ x)`. -/
def pullFlux (φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (E : Fl n) : Fl n :=
  fun x a => ∑ b, (((jac φ x).adjugate a b : ℝ) : ℂ) • E (φ x) b

/-- The cross product on `ℝ³`. -/
def cross3 (s t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![s 1 * t 2 - s 2 * t 1, s 2 * t 0 - s 0 * t 2, s 0 * t 1 - s 1 * t 0]

/-- `D s × D t = adj(D)ᵀ (s × t)` (the cofactor identity). -/
lemma cross3_mulVec (D : Matrix (Fin 3) (Fin 3) ℝ) (s t : Fin 3 → ℝ) (b : Fin 3) :
    cross3 (D *ᵥ s) (D *ᵥ t) b = ∑ a, D.adjugate a b * cross3 s t a := by
  fin_cases b <;>
    simp [cross3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.adjugate_fin_three] <;> ring

/-- A **parametrised surface** with a smearing function: a `C¹` map `σ : ℝ² → ℝ³` (only `[0,1]²` matters) and a
matrix-valued smearing function `f`. -/
structure Surf (n : ℕ) where
  /-- the parametrisation -/
  σ : ℝ × ℝ → Fin 3 → ℝ
  /-- the smearing function -/
  f : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ
  /-- smoothness of the parametrisation -/
  smooth : ContDiff ℝ 1 σ

namespace Surf

/-- The flux **integrand** at a parameter point: `tr (f · ∑_a (∂₁σ × ∂₂σ)_a E^a(σ))`. -/
def integrand (S : Surf n) (E : Fl n) (p : ℝ × ℝ) : ℂ :=
  ((S.f p) * ∑ a, ((cross3 (fderiv ℝ S.σ p (1, 0)) (fderiv ℝ S.σ p (0, 1)) a : ℝ) : ℂ) • E (S.σ p) a).trace

/-- The **flux** of `E` through the surface `S`, smeared with `S.f`. -/
def flux (S : Surf n) (E : Fl n) : ℂ :=
  ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, S.integrand E (u, v)

/-- The **image surface** `φ ∘ σ` under a `C¹` map `φ` of the chart (same smearing function). -/
def map (φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (hφ : ContDiff ℝ 1 φ) (S : Surf n) : Surf n where
  σ := φ ∘ S.σ
  f := S.f
  smooth := hφ.comp S.smooth

/-- Chain rule for the image surface. -/
lemma fderiv_map {φ : (Fin 3 → ℝ) → Fin 3 → ℝ} (hφ : ContDiff ℝ 1 φ) (S : Surf n) (p : ℝ × ℝ) (w : ℝ × ℝ) :
    fderiv ℝ (S.map φ hφ).σ p w = jac φ (S.σ p) *ᵥ fderiv ℝ S.σ p w := by
  have h1 : HasFDerivAt φ (fderiv ℝ φ (S.σ p)) (S.σ p) :=
    ((hφ.differentiable one_ne_zero) (S.σ p)).hasFDerivAt
  have h2 : HasFDerivAt S.σ (fderiv ℝ S.σ p) p :=
    ((S.smooth.differentiable one_ne_zero) p).hasFDerivAt
  rw [jac_mulVec]
  have := (h1.comp p h2).fderiv
  simp only [map] at this ⊢
  rw [this]
  rfl

/-- **Covariance of the flux integrand**: the integrand of `φ*E` on `S` is the integrand of `E` on `φ ∘ S`. -/
lemma integrand_pullFlux {φ : (Fin 3 → ℝ) → Fin 3 → ℝ} (hφ : ContDiff ℝ 1 φ) (S : Surf n) (E : Fl n)
    (p : ℝ × ℝ) : S.integrand (pullFlux φ E) p = (S.map φ hφ).integrand E p := by
  unfold integrand
  have hc : ∀ b, cross3 (fderiv ℝ (S.map φ hφ).σ p (1, 0)) (fderiv ℝ (S.map φ hφ).σ p (0, 1)) b =
      ∑ a, (jac φ (S.σ p)).adjugate a b * cross3 (fderiv ℝ S.σ p (1, 0)) (fderiv ℝ S.σ p (0, 1)) a := by
    intro b
    rw [fderiv_map hφ, fderiv_map hφ, cross3_mulVec]
  have hσ : (S.map φ hφ).σ p = φ (S.σ p) := rfl
  have hf : (S.map φ hφ).f p = S.f p := rfl
  rw [hσ, hf]
  congr 2
  simp only [pullFlux, hc, Finset.smul_sum, smul_smul, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [mul_comm]

/-- **Covariance of the flux**: `flux S (φ*E) = flux (φ ∘ S) E`. -/
theorem flux_pullFlux {φ : (Fin 3 → ℝ) → Fin 3 → ℝ} (hφ : ContDiff ℝ 1 φ) (S : Surf n) (E : Fl n) :
    S.flux (pullFlux φ E) = (S.map φ hφ).flux E := by
  unfold flux
  simp only [integrand_pullFlux hφ]

end Surf

end Lightlike.Canonical
