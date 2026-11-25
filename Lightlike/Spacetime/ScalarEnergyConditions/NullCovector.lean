import Lightlike.Spacetime.ScalarEnergyConditions.KleinGordonNEC

/-!
# A covector that vanishes on all null vectors is zero (G1-010)

In a Lorentz frame `e₀, …, e_{m+1}` the vectors `e₀ + eᵢ` and `e₀ − eᵢ` (`i ≠ 0`) are null. A covector `θ` that
vanishes on them vanishes on `e₀` and on every `eᵢ`, hence is zero. This is the converse used for the equality case
of the null energy condition of the Klein–Gordon field: `T(k, k) = (dφ k)²` vanishes on all null `k` exactly when
`dφ = 0`.

* `covector_eq_zero_of_null`: a covector vanishing on all `g`-null vectors is zero (dimension `≥ 2`).
* `covector_null_eq_zero_iff`: the same as an equivalence.
* `scalarT_null_trivial_iff`: for the Klein–Gordon tensor, `T(k, k) = 0` for every null `k` iff `dφ = 0`.

**Limits.** Pointwise statements; the proofs use only a Lorentz frame, no source is cited.
-/

noncomputable section
namespace Lightlike

section Pointwise
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- In a Lorentz frame the vectors `e₀ ± eᵢ` (`i ≠ 0`) are null. -/
theorem frame_null_add_sub {n : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} {e : Module.Basis (Fin (n + 2)) ℝ V}
    (he : ∀ i j, g (e i) (e j) = eta (n + 2) i j) {i : Fin (n + 2)} (hi : i ≠ 0) (s : ℝ) (hs : s * s = 1) :
    g (e 0 + s • e i) (e 0 + s • e i) = 0 := by
  have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
  have h0 : g (e 0) (e 0) = -1 := by simp [he, eta_apply, etaDiag]
  have hii : g (e i) (e i) = 1 := by simp [he, eta_apply, etaDiag, hi']
  have h0i : g (e 0) (e i) = 0 := by simp [he, eta_apply, Ne.symm hi]
  have hi0 : g (e i) (e 0) = 0 := by simp [he, eta_apply, hi]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, h0, hii, h0i, hi0]
  linear_combination hs

/-- **A covector vanishing on all null vectors is zero** (dimension at least two). -/
theorem covector_eq_zero_of_null {n : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm (n + 2) g)
    (θ : V →L[ℝ] ℝ) (h : ∀ k : V, g k k = 0 → θ k = 0) : θ = 0 := by
  obtain ⟨e, he⟩ := hg
  have key : ∀ i : Fin (n + 2), i ≠ 0 → θ (e 0) = 0 ∧ θ (e i) = 0 := by
    intro i hi
    have h1 := h _ (frame_null_add_sub he hi 1 (by norm_num))
    have h2 := h _ (frame_null_add_sub he hi (-1) (by norm_num))
    simp only [map_add, map_smul, smul_eq_mul] at h1 h2
    constructor <;> linarith
  have h0 : θ (e 0) = 0 := (key 1 (by simp)).1
  have : ∀ i, θ (e i) = 0 := fun i => by
    by_cases hi : i = 0
    · rw [hi]; exact h0
    · exact (key i hi).2
  exact ContinuousLinearMap.coe_injective (e.ext fun i => by simp [this i])

/-- A covector vanishes on all null vectors iff it is zero. -/
theorem covector_null_eq_zero_iff {n : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm (n + 2) g)
    (θ : V →L[ℝ] ℝ) : (∀ k : V, g k k = 0 → θ k = 0) ↔ θ = 0 :=
  ⟨covector_eq_zero_of_null hg θ, fun h k _ => by simp [h]⟩

/-- **Equality case of the null energy condition for a Klein–Gordon field**: `T(k, k) = 0` for every null `k` iff
`dφ = 0`, for every potential value. -/
theorem scalarT_null_trivial_iff [FiniteDimensional ℝ V] (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g)
    (dφ : V →L[ℝ] ℝ) (Vp : ℝ) :
    (∀ k : V, g k k = 0 → scalarT g hg dφ Vp k k = 0) ↔ dφ = 0 := by
  rw [← covector_null_eq_zero_iff (n := 2) hg dφ]
  exact forall_congr' fun k => imp_congr_right fun hk => scalarT_null_eq_zero_iff g hg dφ Vp hk
