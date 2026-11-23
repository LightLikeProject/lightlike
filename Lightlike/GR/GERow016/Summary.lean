import Lightlike.GR.GERow016.ScriPlus
import Lightlike.GR.GERow016.AdSBoundary
import Lightlike.Spacetime.MinkowskiCompactification

/-!
# Conformal compactification: Minkowski null infinity and the conformal boundary of anti-de Sitter space

A summary of gap row GE7, collecting the statements spread over `ConformalMinkowski.lean`, `ConformalPoincare.lean`,
`AdSConformal.lean`, `AdSInversion.lean`, `MinkowskiCompactification.lean` and the files of this folder:

* Minkowski space is conformal to a region of the Einstein static universe, with the conformal factor
  `conformalFactor` (`pullback_compact`, `pullback_esu_doubling`, `compactify_mem`), and its null infinity is the set
  `scriPlus` on which the factor vanishes.
* The Poincaré group acts on the compactification by conformal transformations (`poincare_conformal`); the time
  translation extends to `scriPlus` as the translation of retarded time (`scriTimeShift_scriPoint`).
* A rescaling of `t` and `r` separately by `arctan` is not conformal (`arctan_not_conformal`).
* The conformal boundary of global anti-de Sitter space is `adsBoundary`; the isometries act on it conformally
  (`adsBdyMetric_timeShift`, `dilation_conformal_boundary`, `specialConformal3_conformal`).
-/

open Real

namespace Lightlike

/-- **Null infinity of Minkowski space, in one statement**: the conformal factor of the compactification is `scriFactor`
of the compactified point, vanishes on future null infinity, every outgoing null ray ends on it, and the time
translation maps it to itself by translating the retarded time. -/
theorem minkowski_scri_summary :
    (∀ y : Fin 4 → ℝ, scriFactor (compactify y) = conformalFactor y) ∧
      (∀ p ∈ scriPlus, scriFactor p = 0) ∧
      (∀ u θ φ : ℝ, Filter.Tendsto (fun r : ℝ => compactify ![u + r, r, θ, φ]) Filter.atTop
        (nhds (scriPoint u θ φ))) ∧
      (∀ a u θ φ : ℝ, scriTimeShift a (scriPoint u θ φ) = scriPoint (u + a) θ φ) :=
  ⟨scriFactor_compactify, fun _ hp => scriFactor_scriPlus hp, compactify_tendsto_scriPoint,
    scriTimeShift_scriPoint⟩

/-- **The non-conformal rescaling `(t, r) ↦ (arctan t, arctan r)` fails** (restated from `ConformalMinkowski.lean`). -/
theorem minkowski_nonconformal_fails :
    ¬ ∃ c : ℝ, pullback compactMetric nonConf ![1, 2, π / 2, 0] = c • minkSph ![1, 2, π / 2, 0] :=
  arctan_not_conformal

end Lightlike
