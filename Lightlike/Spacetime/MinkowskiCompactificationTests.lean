import Lightlike.Spacetime.MinkowskiCompactification

/-!
# A non-conformal rescaling does not give the Einstein static universe (G1-016, trust check)

The Minkowski metric is `ω⁻²` times the Einstein static metric `-dη² + dχ² + sin² χ dΩ²`
(`minkowski_eq_conformal_esu`). A rescaling of the time direction only, `-λ² dη² + dχ² + sin² χ dΩ²`, is conformal to it
exactly when `λ² = 1`: for `λ² ≠ 1` no function `c` satisfies the identity on every tangent vector
(`not_conformal_time_rescaling`), so the compactification needs the conformal factor `ω⁻²` and not any rescaling.
-/

namespace Lightlike

open Real

/-- **A non-conformal rescaling fails**: if `λ² ≠ 1`, the form `-λ² a² + b² + sin² χ q` is not a multiple of the
Einstein static universe form `-a² + b² + sin² χ q` on the tangent vectors `a ∂_η + b ∂_χ + w`
(`q = dΩ²(w, w)`). -/
theorem not_conformal_time_rescaling {lam : ℝ} (hlam : lam ^ 2 ≠ 1) (χ : ℝ) :
    ¬ ∃ c : ℝ, ∀ a b q : ℝ,
      -(lam ^ 2) * a ^ 2 + b ^ 2 + sin χ ^ 2 * q = c * (-a ^ 2 + b ^ 2 + sin χ ^ 2 * q) := by
  rintro ⟨c, hc⟩
  have h1 := hc 0 1 0
  have h2 := hc 1 0 0
  apply hlam
  nlinarith

/-- **Non-vacuity**: for `λ² = 1` the form is the Einstein static universe form, with `c = 1`. -/
theorem conformal_time_rescaling_one {lam : ℝ} (hlam : lam ^ 2 = 1) (χ : ℝ) :
    ∃ c : ℝ, ∀ a b q : ℝ,
      -(lam ^ 2) * a ^ 2 + b ^ 2 + sin χ ^ 2 * q = c * (-a ^ 2 + b ^ 2 + sin χ ^ 2 * q) :=
  ⟨1, fun a b q => by rw [hlam]; ring⟩

end Lightlike
