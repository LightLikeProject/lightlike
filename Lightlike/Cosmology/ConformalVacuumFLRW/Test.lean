import Lightlike.Cosmology.ConformalVacuumFLRW.Conformal

/-!
# Tests for the G1-037 rows (Fourier-mode shadow of CO11)

Sanity checks on the statements of `Bogoliubov.lean` and `Conformal.lean`.
-/

namespace Lightlike.Adiabatic

#check @conformalPotential_massless_conformal
#check @not_bogoliubovDecay_conformal_alphaVacuum
#check @bogBeta_conformalData_alphaVacuum

/-- De Sitter in conformal time, `a(η) = -1/η`: the massless conformally coupled potential
vanishes (trust check 2). -/
example (η : ℝ) : conformalPotential (fun η => -1 / η) 0 (1 / 6) η = 0 :=
  conformalPotential_massless_conformal _ η

/-- The conformal vacuum is exact: `β = 0` against itself. -/
example (r : ModeData) : bogBeta r r = 0 := bogBeta_self r

/-- An α-vacuum with `a = 1` over the conformal vacuum is not adiabatic of order `3`. -/
example (η θ : ℝ) :
    ¬ BogoliubovDecay 3
      (fun k => bogBeta (conformalData k η) (alphaVacuum 1 θ (conformalData k η))) :=
  not_bogoliubovDecay_conformal_alphaVacuum η 1 θ one_pos 3

end Lightlike.Adiabatic
