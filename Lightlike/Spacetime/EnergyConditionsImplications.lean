import Lightlike.Spacetime.EnergyConditions

/-!
# Energy conditions (GE14): the implications between them

For a bilinear form `T` (the stress-energy at a point) on a four-dimensional Lorentzian vector space
`(V, g)`:

* `weakEC_of_dominantEC`: the dominant condition implies the weak one (it contains it);
* `nullEC_of_weakEC`: the weak condition implies the null one;
* `nullEC_of_strongEC`: the strong condition implies the null one;
* `nullEC_of_dominantEC`: the dominant condition implies the null one.

The null conditions follow from the timelike ones by continuity: a null vector `k` is the limit
`ε → 0+` of the timelike vectors `k + ε w`, for `w` timelike with `g(k, w) ≤ 0`. No other
implication holds between the weak and the strong condition: a positive cosmological constant
satisfies the weak and violates the strong one (`cosmo_energyConditions`), and a perfect fluid with
`ρ = -1`, `p = 1` satisfies the strong and violates the weak one (`fluid_strongEC_iff`,
`fluid_weakEC_iff`).

## Source

Curiel, *A Primer on Energy Conditions*, arXiv 1405.0403, section 2.1, pp. 5-6 (the four physical
forms); the implications are stated there in the discussion after the table (the comparison with
that passage is pending: not read at that location). Carroll, gr-qc/9712019, eq. (4.72) for the weak
condition.

**Limits.** Pointwise on a normed real vector space (the continuity of `v ↦ T v v` needs a norm in
this formulation), dimension four; no manifold.
-/

noncomputable section
namespace Lightlike


variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {g T : V →L[ℝ] V →L[ℝ] ℝ}

/-- The diagonal `v ↦ B v v` of a continuous bilinear form is continuous. -/
theorem continuous_diag (B : V →L[ℝ] V →L[ℝ] ℝ) : Continuous fun v : V => B v v :=
  Continuous.clm_apply B.continuous continuous_id

/-- A null vector `k` is a limit of timelike vectors `k + ε w` (`ε > 0`) in a Lorentzian space. -/
theorem exists_null_approx (hg : IsLorentzianForm 4 g) {k : V} (hk : g k k = 0) :
    ∃ w : V, ∀ ε : ℝ, 0 < ε → g (k + ε • w) (k + ε • w) < 0 := by
  obtain ⟨u, hu⟩ := hg.exists_timelike (by norm_num)
  have expand : ∀ (w : V) (ε : ℝ), g (k + ε • w) (k + ε • w) =
      2 * ε * g k w + ε ^ 2 * g w w + g k k := by
    intro w ε
    have hs := lorentz_symm_aux hg w k
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hs]
    ring
  rcases le_total (g k u) 0 with h | h
  · refine ⟨u, fun ε hε => ?_⟩
    rw [expand, hk]
    nlinarith [mul_pos hε hε, mul_nonpos_of_nonneg_of_nonpos hε.le h]
  · refine ⟨-u, fun ε hε => ?_⟩
    rw [expand, hk]
    have : g k (-u) = -g k u := by simp
    have h2 : g (-u) (-u) = g u u := by simp
    rw [this, h2]
    nlinarith [mul_pos hε hε, mul_nonneg hε.le h]

/-- A continuous function that is nonnegative on timelike vectors is nonnegative on null vectors. -/
theorem nonneg_null_of_timelike (hg : IsLorentzianForm 4 g) {F : V → ℝ} (hF : Continuous F)
    (h : ∀ v, g v v < 0 → 0 ≤ F v) {k : V} (hk : g k k = 0) : 0 ≤ F k := by
  obtain ⟨w, hw⟩ := exists_null_approx hg hk
  have hc : Continuous fun ε : ℝ => F (k + ε • w) :=
    hF.comp (continuous_const.add (continuous_id.smul continuous_const))
  have := nonneg_of_pos_nonneg hc fun ε hε => h _ (hw ε hε)
  simpa using this

/-- **The weak energy condition implies the null energy condition.** -/
theorem nullEC_of_weakEC (hg : IsLorentzianForm 4 g) (h : WeakEC g T) : NullEC g T := fun _ hk =>
  nonneg_null_of_timelike hg (F := fun v => T v v) (continuous_diag T) h hk

/-- **The strong energy condition implies the null energy condition.** -/
theorem nullEC_of_strongEC [FiniteDimensional ℝ V] (hg : IsLorentzianForm 4 g)
    (h : StrongEC g T hg) : NullEC g T := by
  intro k hk
  have := nonneg_null_of_timelike hg
    (F := fun v => T v v - (1 / 2) * traceG g T hg.bilinForm_nondegenerate * g v v)
    ((continuous_diag T).sub (continuous_const.mul (continuous_diag g))) h hk
  simpa [hk] using this

/-- **The dominant energy condition implies the weak energy condition.** -/
theorem weakEC_of_dominantEC [FiniteDimensional ℝ V] {hg : IsLorentzianForm 4 g}
    (h : DominantEC g T hg) : WeakEC g T := fun v hv => (h.1 v hv).1

/-- **The dominant energy condition implies the null energy condition.** -/
theorem nullEC_of_dominantEC [FiniteDimensional ℝ V] (hg : IsLorentzianForm 4 g)
    (h : DominantEC g T hg) : NullEC g T :=
  nullEC_of_weakEC hg (weakEC_of_dominantEC h)

/-- Non-vacuity: dust satisfies the dominant condition (`dust_energyConditions`), hence the null one
through the implication. -/
example [FiniteDimensional ℝ V] {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm 4 g) {u : V}
    (hu : g u u = -1) {ρ : ℝ} (hρ : 0 ≤ ρ) : NullEC g (dustT g u ρ) :=
  nullEC_of_dominantEC hg (dust_energyConditions hg hu hρ).2.2.2

end Lightlike
