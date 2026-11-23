import Lightlike.Canonical.HolonomyPaths

/-!
# Diffeomorphisms act on connections and on holonomies (row G2-015)

The first piece of the diffeomorphism action on the holonomy–flux algebra (the setting of the uniqueness theorem of
Lewandowski–Okołów–Sahlmann–Thiemann, `lost-2006`): a `C¹` map `φ` of the chart `ℝ³` pulls a connection
`A_a(x)` back to `(φ*A)_a(x) = ∑_b (∂_a φ^b)(x) A_b(φ x)` (`pullConn`), and the holonomy of the pulled-back
connection along an edge `e` is the holonomy of `A` along the image edge `φ ∘ e`
(`holonomy_pullConn`).  The image edge is `Edge.map` (`hol_pullConn`).
-/

open Matrix Set
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ}

/-- The **pullback of a connection** by a map `φ` of the chart `ℝ³`:
`(φ*A)_a(x) = ∑_b (∂_a φ^b)(x) A_b(φ x)`. -/
def pullConn (φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (A : MatConn n) : MatConn n :=
  fun x a => ∑ b, ((fderiv ℝ φ x (Pi.single a 1) b : ℝ) : ℂ) • A (φ x) b

/-- The transport coefficient of the pulled-back connection along `e` is the transport coefficient of `A`
along `φ ∘ e`. -/
lemma transportCoeff_pullConn (A : MatConn n) {φ : (Fin 3 → ℝ) → Fin 3 → ℝ} (hφ : ContDiff ℝ 1 φ)
    {e : ℝ → Fin 3 → ℝ} (he : ContDiff ℝ 1 e) (t : ℝ) :
    transportCoeff (pullConn φ A) e t = transportCoeff A (φ ∘ e) t := by
  have hd : deriv (φ ∘ e) t = fderiv ℝ φ (e t) (deriv e t) := by
    have h1 : HasFDerivAt φ (fderiv ℝ φ (e t)) (e t) :=
      ((hφ.differentiable one_ne_zero) (e t)).hasFDerivAt
    exact (h1.comp_hasDerivAt t ((he.differentiable one_ne_zero) t).hasDerivAt).deriv
  have hlin : ∀ b, fderiv ℝ φ (e t) (deriv e t) b =
      ∑ a, deriv e t a * fderiv ℝ φ (e t) (Pi.single a 1) b := by
    intro b
    have hv : deriv e t = ∑ a, deriv e t a • (Pi.single a (1 : ℝ) : Fin 3 → ℝ) := by
      ext c
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold transportCoeff pullConn
  simp only [Function.comp_apply, hd, hlin, Complex.ofReal_sum, Complex.ofReal_mul, Finset.smul_sum,
    Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

/-- **Covariance of the holonomy**: the holonomy of the pulled-back connection along `e` is the holonomy of `A`
along the image path `φ ∘ e`. -/
theorem holonomy_pullConn (A : MatConn n) {φ : (Fin 3 → ℝ) → Fin 3 → ℝ} (hφ : ContDiff ℝ 1 φ)
    {e : ℝ → Fin 3 → ℝ} (he : ContDiff ℝ 1 e) (t₁ t₂ : ℝ) :
    holonomy (pullConn φ A) e t₁ t₂ = holonomy A (φ ∘ e) t₁ t₂ := by
  have h : transportCoeff (pullConn φ A) e = transportCoeff A (φ ∘ e) :=
    funext (transportCoeff_pullConn A hφ he)
  simp only [holonomy, transport, h]

namespace Edge

/-- The **image edge** `φ ∘ e` of an edge under a `C¹` map `φ` of the chart. -/
def map (φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (hφ : ContDiff ℝ 1 φ) (e : Edge) : Edge where
  path := φ ∘ e.path
  t₀ := e.t₀
  t₁ := e.t₁
  le := e.le
  smooth := hφ.comp e.smooth

/-- **Covariance of the edge holonomy**: `(φ*A)(e) = A(φ ∘ e)`. -/
theorem hol_pullConn (A : MatConn n) {φ : (Fin 3 → ℝ) → Fin 3 → ℝ} (hφ : ContDiff ℝ 1 φ) (e : Edge) :
    e.hol (pullConn φ A) = (e.map φ hφ).hol A :=
  holonomy_pullConn A hφ e.smooth e.t₀ e.t₁

end Edge

end Lightlike.Canonical
