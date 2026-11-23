import Lightlike.Rows.G1_053.Converse

/-!
# Gibbs = diagonal KMS states; failure of KMS for non-Gibbs weights; a two-level test

* `gibbs_eq_diagState`: the Gibbs state of `GibbsKMS.lean` is the diagonal functional with weights `e^{-βλₙ}/Z`;
* `not_isKMSState_of_weights`: if the weights violate `pₙ = pₘ e^{-β(λₙ - λₘ)}` for some `m n`, then
  `diagState b p` is not `(τ, β)`-KMS (`β > 0`);
* `not_isKMSState_uniform`, `not_isKMSState_pure`: the uniform weights (a "trace") and a pure state `p = δ_{m₀}` are not
  KMS at any `β > 0` for a flow whose spectrum is not constant (the failing-KMS checks);
* `twoLevel_kms_at_two_pi`, `twoLevel_uniform_not_kms`: a concrete instance on `ℂ²` at `β = 2π`.
-/

namespace Lightlike.Rows.G1_053

open Lightlike.OperatorAlgebras.GibbsKMS
open scoped InnerProductSpace

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The Gibbs state is the diagonal functional with weights `e^{-βλₙ}/Z`. -/
theorem gibbs_eq_diagState (b : HilbertBasis ι ℂ H) (ev : ι → ℝ) (β : ℝ) :
    gibbs b ev β = diagState b (fun n => (Real.exp (-(β * ev n)) : ℂ) / (partition ev β : ℂ)) := by
  funext A
  unfold gibbs diagState
  rw [← tsum_div_const]
  congr 1
  funext n
  ring

/-- **Failure of KMS**: if the weights of a diagonal state violate the Gibbs relation, it is not `β`-KMS. -/
theorem not_isKMSState_of_weights [DecidableEq ι] (b : HilbertBasis ι ℂ H) (ev : ι → ℝ) (p : ι → ℂ)
    {β : ℝ} (hβ : 0 < β) {m n : ι}
    (hne : p n ≠ p m * Complex.exp (-(β * (ev n - ev m)))) :
    ¬ IsKMSState (dyn b ev) (diagState b p) β :=
  fun h => hne (weights_of_isKMSState b ev p hβ h m n)

/-- The uniform weights `pₙ = 1` are not `β`-KMS (`β > 0`) when the spectrum is not constant. -/
theorem not_isKMSState_uniform [DecidableEq ι] (b : HilbertBasis ι ℂ H) (ev : ι → ℝ)
    {β : ℝ} (hβ : 0 < β) {m n : ι} (hev : ev n ≠ ev m) :
    ¬ IsKMSState (dyn b ev) (diagState b (fun _ => 1)) β := by
  refine not_isKMSState_of_weights b ev _ hβ (m := m) (n := n) ?_
  intro h
  have h' : Complex.exp (-(β * (ev n - ev m))) = ((Real.exp (-(β * (ev n - ev m))) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [one_mul, h', eq_comm] at h
  have h2 : Real.exp (-(β * (ev n - ev m))) = 1 := by exact_mod_cast h
  rw [Real.exp_eq_one_iff] at h2
  have : β * (ev n - ev m) = 0 := by linarith
  rcases mul_eq_zero.mp this with h3 | h3
  · exact hβ.ne' h3
  · exact hev (by linarith)

/-- A pure state `p = δ_{m₀}` is not `β`-KMS (`β > 0`) when some `evₙ ≠ ev_{m₀}`. -/
theorem not_isKMSState_pure [DecidableEq ι] (b : HilbertBasis ι ℂ H) (ev : ι → ℝ)
    {β : ℝ} (hβ : 0 < β) (m₀ : ι) {n : ι} (hev : ev n ≠ ev m₀) :
    ¬ IsKMSState (dyn b ev) (diagState b (fun k => if k = m₀ then 1 else 0)) β := by
  refine not_isKMSState_of_weights b ev _ hβ (m := m₀) (n := n) ?_
  have hn : n ≠ m₀ := fun h => hev (by rw [h])
  simp only [hn, ite_true, ite_false, one_mul, ne_eq]
  exact fun h => Complex.exp_ne_zero _ h.symm

/-- The two-level system `ℂ²` with its standard Hilbert basis and eigenvalues `0, 1`: the Gibbs state is KMS at `β = 2π`. -/
theorem twoLevel_kms_at_two_pi :
    IsKMSState (dyn (EuclideanSpace.basisFun (Fin 2) ℂ).toHilbertBasis (fun i : Fin 2 => (i : ℝ)))
      (gibbs (EuclideanSpace.basisFun (Fin 2) ℂ).toHilbertBasis (fun i : Fin 2 => (i : ℝ)) (2 * Real.pi))
      (2 * Real.pi) :=
  isKMSState_gibbs _ _ (by positivity) (Summable.of_finite)

/-- On `ℂ²` the uniform weights are not KMS at `β = 2π` for the flow with eigenvalues `0, 1`. -/
theorem twoLevel_uniform_not_kms :
    ¬ IsKMSState (dyn (EuclideanSpace.basisFun (Fin 2) ℂ).toHilbertBasis (fun i : Fin 2 => (i : ℝ)))
      (diagState (EuclideanSpace.basisFun (Fin 2) ℂ).toHilbertBasis (fun _ => 1)) (2 * Real.pi) :=
  not_isKMSState_uniform _ _ (by positivity) (m := 0) (n := 1) (by simp)

end Lightlike.Rows.G1_053
