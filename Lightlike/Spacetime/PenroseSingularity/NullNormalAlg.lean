import Mathlib

/-!
# The null normals of a Lorentzian plane (G1-012, step D2, algebra)

In the plane `P = span(N₁, N₂)` with Gram matrix `G` (`det G < 0`) and a vector `τ` with `bᵢ = B(Nᵢ, τ)`,
the vectors `k = α N₁ + β N₂` with `α = λ c₁ ∓ b₂`, `β = λ c₂ ± b₁` (`λ = √(-det G)`, `c = G⁻¹ b`) are null,
and `B(k, τ) = λ · bᵀ G⁻¹ b`.
-/

noncomputable section

namespace Lightlike.Penrose.NullNormal

/-- `D = -det G = G₁₂² - G₁₁ G₂₂`. -/
def Dd (G11 G12 G22 : ℝ) : ℝ := G12 ^ 2 - G11 * G22

/-- The quadratic form `Q(b) = G₂₂ b₁² - 2 G₁₂ b₁ b₂ + G₁₁ b₂²`. -/
def Qq (G11 G12 G22 b1 b2 : ℝ) : ℝ := G22 * b1 ^ 2 - 2 * G12 * b1 * b2 + G11 * b2 ^ 2

/-- Coefficient of `N₁` in `k_s`, `s = ±1`: `λ c₁ - s b₂`. -/
def kα (G11 G12 G22 b1 b2 s : ℝ) : ℝ :=
  Real.sqrt (Dd G11 G12 G22) * (-(G22 * b1 - G12 * b2) / Dd G11 G12 G22) - s * b2

/-- Coefficient of `N₂` in `k_s`: `λ c₂ + s b₁`. -/
def kβ (G11 G12 G22 b1 b2 s : ℝ) : ℝ :=
  Real.sqrt (Dd G11 G12 G22) * ((G12 * b1 - G11 * b2) / Dd G11 G12 G22) + s * b1

theorem kα_kβ_null {G11 G12 G22 b1 b2 s : ℝ} (hD : 0 < Dd G11 G12 G22) (hs : s ^ 2 = 1) :
    G11 * kα G11 G12 G22 b1 b2 s ^ 2 + 2 * G12 * kα G11 G12 G22 b1 b2 s * kβ G11 G12 G22 b1 b2 s +
      G22 * kβ G11 G12 G22 b1 b2 s ^ 2 = 0 := by
  have hl : Real.sqrt (Dd G11 G12 G22) ^ 2 = Dd G11 G12 G22 := Real.sq_sqrt hD.le
  have hD0 : Dd G11 G12 G22 ≠ 0 := hD.ne'
  unfold kα kβ
  set l := Real.sqrt (Dd G11 G12 G22)
  have hDe : Dd G11 G12 G22 = G12 ^ 2 - G11 * G22 := rfl
  rw [hDe] at hl hD0 ⊢
  field_simp
  linear_combination ((G11 * G22 - G12 ^ 2) * (G11 * b2 ^ 2 - 2 * G12 * b1 * b2 + G22 * b1 ^ 2)) * hl +
    ((G12 ^ 2 - G11 * G22) ^ 2 * (G11 * b2 ^ 2 - 2 * G12 * b1 * b2 + G22 * b1 ^ 2)) * hs

theorem kα_mul_add_kβ_mul {G11 G12 G22 b1 b2 s : ℝ} (hD : 0 < Dd G11 G12 G22) :
    kα G11 G12 G22 b1 b2 s * b1 + kβ G11 G12 G22 b1 b2 s * b2 =
      -(Real.sqrt (Dd G11 G12 G22) * Qq G11 G12 G22 b1 b2 / Dd G11 G12 G22) := by
  have hD0 : Dd G11 G12 G22 ≠ 0 := hD.ne'
  unfold kα kβ Qq
  have hDe : Dd G11 G12 G22 = G12 ^ 2 - G11 * G22 := rfl
  rw [hDe] at hD0 ⊢
  field_simp
  ring

/-- **A null vector of the plane is parallel to `k₊` or `k₋`.** -/
theorem exists_sign_parallel {G11 G12 G22 b1 b2 a b : ℝ} (hD : 0 < Dd G11 G12 G22)
    (hnull : G11 * a ^ 2 + 2 * G12 * a * b + G22 * b ^ 2 = 0) :
    ∃ s : ℝ, s ^ 2 = 1 ∧
      a * kβ G11 G12 G22 b1 b2 s = b * kα G11 G12 G22 b1 b2 s := by
  have hl : Real.sqrt (Dd G11 G12 G22) ^ 2 = Dd G11 G12 G22 := Real.sq_sqrt hD.le
  have hD0 : Dd G11 G12 G22 ≠ 0 := hD.ne'
  have key : (a * kβ G11 G12 G22 b1 b2 1 - b * kα G11 G12 G22 b1 b2 1) *
      (a * kβ G11 G12 G22 b1 b2 (-1) - b * kα G11 G12 G22 b1 b2 (-1)) = 0 := by
    unfold kα kβ
    set l := Real.sqrt (Dd G11 G12 G22)
    have hDe : Dd G11 G12 G22 = G12 ^ 2 - G11 * G22 := rfl
    rw [hDe] at hl hD0 ⊢
    field_simp
    linear_combination ((-(G11 * a * b2) + G12 * a * b1 - G12 * b * b2 + G22 * b * b1) ^ 2) * hl +
      ((G12 ^ 2 - G11 * G22) * (G22 * b1 ^ 2 - 2 * G12 * b1 * b2 + G11 * b2 ^ 2)) * hnull
  rcases mul_eq_zero.1 key with h | h
  · exact ⟨1, by norm_num, by linarith⟩
  · exact ⟨-1, by norm_num, by linarith⟩

section Geometry

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- The geometric hypotheses on the plane `span(N₁, N₂)` and the timelike vector `τ`:
independence of `N₁, N₂` (as functionals `B(Nᵢ, ·)`), spacelikeness of the common kernel,
a Lorentz-type functional, and `B(τ, τ) < 0`. -/
structure PlaneData (N1 N2 τ : V) : Prop where
  symm : ∀ v w, B v w = B w v
  indep : ∀ a b : ℝ, (∀ v, a * B N1 v + b * B N2 v = 0) → a = 0 ∧ b = 0
  spacelike : ∀ v, B N1 v = 0 → B N2 v = 0 → v ≠ 0 → 0 < B v v
  lorentz : ∃ φ : V →ₗ[ℝ] ℝ, ∀ v, φ v = 0 → 0 ≤ B v v
  timelike : B τ τ < 0

variable {B} {N1 N2 τ : V}

theorem PlaneData.det_ne (h : PlaneData B N1 N2 τ) :
    Dd (B N1 N1) (B N1 N2) (B N2 N2) ≠ 0 := by
  intro hD0
  have hD : B N1 N2 ^ 2 - B N1 N1 * B N2 N2 = 0 := hD0
  have h21 : B N2 N1 = B N1 N2 := h.symm _ _
  -- a nonzero kernel vector of the Gram matrix
  obtain ⟨a, b, hab, e1, e2⟩ : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      B N1 N1 * a + B N1 N2 * b = 0 ∧ B N1 N2 * a + B N2 N2 * b = 0 := by
    by_cases h0 : B N1 N1 = 0 ∧ B N1 N2 = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h0.1], by simp [h0.2]⟩
    · refine ⟨B N1 N2, -B N1 N1, ?_, by ring, by nlinarith⟩
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      exact h0 ⟨by linarith [hc.2], hc.1⟩
  set w : V := a • N1 + b • N2 with hw
  have hBw : ∀ v, B w v = a * B N1 v + b * B N2 v := fun v => by
    simp [hw, LinearMap.add_apply, LinearMap.smul_apply]
  have hwN1 : B w N1 = 0 := by
    rw [hBw N1, h21]; linarith
  have hwN2 : B w N2 = 0 := by
    rw [hBw N2]; linarith
  have hww : B w w = 0 := by
    rw [hBw w, h.symm N1 w, h.symm N2 w, hwN1, hwN2]; ring
  have hw0 : w = 0 := by
    by_contra hne
    exact absurd (h.spacelike w (by rw [h.symm]; exact hwN1) (by rw [h.symm]; exact hwN2) hne)
      (by rw [hww]; exact lt_irrefl 0)
  have hall : ∀ v, a * B N1 v + b * B N2 v = 0 := fun v => by rw [← hBw, hw0]; simp
  obtain ⟨ha, hb⟩ := h.indep a b hall
  rcases hab with h1 | h1
  · exact h1 ha
  · exact h1 hb

set_option maxHeartbeats 1600000 in
/-- The core of the construction: `D > 0` (the plane is Lorentzian) and `Q > 0`. -/
theorem PlaneData.D_pos_Q_pos (h : PlaneData B N1 N2 τ) :
    0 < Dd (B N1 N1) (B N1 N2) (B N2 N2) ∧
      0 < Qq (B N1 N1) (B N1 N2) (B N2 N2) (B N1 τ) (B N2 τ) := by
  have hD0 := h.det_ne
  have hDe : Dd (B N1 N1) (B N1 N2) (B N2 N2) = B N1 N2 ^ 2 - B N1 N1 * B N2 N2 := rfl
  set G11 := B N1 N1 with hG11
  set G12 := B N1 N2 with hG12
  set G22 := B N2 N2 with hG22
  set b1 := B N1 τ with hb1
  set b2 := B N2 τ with hb2
  have hDne : G12 ^ 2 - G11 * G22 ≠ 0 := hD0
  have h21 : B N2 N1 = G12 := h.symm _ _
  set c1 : ℝ := -(G22 * b1 - G12 * b2) / (G12 ^ 2 - G11 * G22) with hc1
  set c2 : ℝ := (G12 * b1 - G11 * b2) / (G12 ^ 2 - G11 * G22) with hc2
  set τ' : V := c1 • N1 + c2 • N2 with hτ'
  set τ'' : V := τ - τ' with hτ''
  have hBτ' : ∀ v, B τ' v = c1 * B N1 v + c2 * B N2 v := fun v => by
    simp [hτ', LinearMap.add_apply, LinearMap.smul_apply]
  have hDne2 : -(G22 * G11) + G12 ^ 2 ≠ 0 := fun h' => hDne (by linarith)
  have e1 : B N1 τ' = b1 := by
    rw [h.symm N1 τ', hBτ' N1, h21, ← hG11]
    rw [hc1, hc2, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hDne]; ring
  have e2 : B N2 τ' = b2 := by
    rw [h.symm N2 τ', hBτ' N2, ← hG12, ← hG22]
    rw [hc1, hc2, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hDne]; ring
  have k1 : B N1 τ'' = 0 := by simp [hτ'', e1, hb1]
  have k2 : B N2 τ'' = 0 := by simp [hτ'', e2, hb2]
  have hpos : 0 ≤ B τ'' τ'' := by
    by_cases h0 : τ'' = 0
    · simp [h0]
    · exact (h.spacelike τ'' k1 k2 h0).le
  have hcross : B τ' τ'' = 0 := by rw [hBτ', k1, k2]; ring
  have hdec : B τ τ = B τ' τ' + B τ'' τ'' := by
    have hτeq : τ = τ' + τ'' := by simp [hτ'']
    have h1 : B τ τ = B (τ' + τ'') (τ' + τ'') := by rw [← hτeq]
    rw [h1]
    simp only [LinearMap.add_apply, map_add]
    rw [h.symm τ'' τ', hcross]; ring
  have hQ : B τ' τ' = -(Qq G11 G12 G22 b1 b2 / (G12 ^ 2 - G11 * G22)) := by
    rw [hBτ', e1, e2, hc1, hc2]
    unfold Qq
    field_simp
    ring
  have hneg : -(Qq G11 G12 G22 b1 b2 / (G12 ^ 2 - G11 * G22)) < 0 := by
    rw [← hQ]; linarith [h.timelike, hdec, hpos]
  have hQD : 0 < Qq G11 G12 G22 b1 b2 / (G12 ^ 2 - G11 * G22) := by linarith
  by_cases hDp : 0 < G12 ^ 2 - G11 * G22
  · refine ⟨hDp, ?_⟩
    rcases div_pos_iff.1 hQD with h' | h'
    · exact h'.1
    · exact absurd h'.2 (not_lt.2 hDp.le)
  · exfalso
    have hDn : G12 ^ 2 - G11 * G22 < 0 := lt_of_le_of_ne (not_lt.1 hDp) hDne
    have hQn : Qq G11 G12 G22 b1 b2 < 0 := by
      rcases div_pos_iff.1 hQD with h' | h'
      · exact absurd h'.2 hDp
      · exact h'.1
    have hGG : 0 < G11 * G22 := by nlinarith [sq_nonneg G12]
    have hG22n : G22 < 0 := by
      by_contra hc
      have hc' : 0 < G22 := lt_of_le_of_ne (not_lt.1 hc) (by
        intro h0; rw [← h0] at hGG; simp at hGG)
      have h11 : 0 < G11 := by
        by_contra h11; have : G11 ≤ 0 := not_lt.1 h11
        nlinarith
      have : 0 ≤ G22 * Qq G11 G12 G22 b1 b2 := by
        unfold Qq
        nlinarith [sq_nonneg (G22 * b1 - G12 * b2), sq_nonneg b2]
      nlinarith
    have hG11n : G11 < 0 := by
      by_contra hc
      have : 0 ≤ G11 := not_lt.1 hc
      nlinarith
    obtain ⟨φ, hφ⟩ := h.lorentz
    obtain ⟨a, b, hab, hφab⟩ : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a * φ N1 + b * φ N2 = 0 := by
      by_cases h0 : φ N1 = 0 ∧ φ N2 = 0
      · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h0.1]⟩
      · refine ⟨φ N2, -φ N1, ?_, by ring⟩
        by_contra hc
        rw [not_or, not_not, not_not] at hc
        exact h0 ⟨by linarith [hc.2], hc.1⟩
    set w : V := a • N1 + b • N2 with hw
    have hBw : ∀ v, B w v = a * B N1 v + b * B N2 v := fun v => by
      simp [hw, LinearMap.add_apply, LinearMap.smul_apply]
    have hφw : φ w = 0 := by simp [hw, hφab]
    have hww : B w w = a * (a * G11 + b * G12) + b * (a * G12 + b * G22) := by
      rw [hBw w, h.symm N1 w, h.symm N2 w, hBw N1, hBw N2, h21]
    have hge := hφ w hφw
    rw [hww] at hge
    -- the Gram form is negative definite
    have hid : G11 * (a * (a * G11 + b * G12) + b * (a * G12 + b * G22)) =
        (G11 * a + G12 * b) ^ 2 + (G11 * G22 - G12 ^ 2) * b ^ 2 := by ring
    have hle : G11 * (a * (a * G11 + b * G12) + b * (a * G12 + b * G22)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hG11n.le hge
    have hcoef : 0 < G11 * G22 - G12 ^ 2 := by linarith
    have hsq := sq_nonneg (G11 * a + G12 * b)
    have hbb : b ^ 2 ≤ 0 := by
      by_contra hcon
      have hp : 0 < b ^ 2 := not_le.1 hcon
      have := mul_pos hcoef hp
      linarith [hid, hle]
    have hb0 : b = 0 := by
      have : b ^ 2 = 0 := le_antisymm hbb (sq_nonneg b)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    rw [hb0] at hid hle hsq
    have ha0 : a = 0 := by
      have h1 : (G11 * a + G12 * 0) ^ 2 ≤ 0 := by nlinarith [hid, hle]
      have h2 : G11 * a + G12 * 0 = 0 := by
        have : (G11 * a + G12 * 0) ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      have h3 : G11 * a = 0 := by simpa using h2
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 hG11n.ne
      · exact h4
    rcases hab with h1 | h1
    · exact h1 ha0
    · exact h1 hb0


/-- **Every vector orthogonal to `ker Df` lies in the plane.** -/
theorem PlaneData.exists_decomp (h : PlaneData B N1 N2 τ) (ν : V)
    (hν : ∀ v, B N1 v = 0 → B N2 v = 0 → B ν v = 0) : ∃ a b : ℝ, ν = a • N1 + b • N2 := by
  have hD0 := h.det_ne
  set G11 := B N1 N1 with hG11
  set G12 := B N1 N2 with hG12
  set G22 := B N2 N2 with hG22
  have hDne : G12 ^ 2 - G11 * G22 ≠ 0 := hD0
  have h21 : B N2 N1 = G12 := h.symm _ _
  set d1 := B N1 ν with hd1
  set d2 := B N2 ν with hd2
  set a : ℝ := -(G22 * d1 - G12 * d2) / (G12 ^ 2 - G11 * G22) with ha
  set b : ℝ := (G12 * d1 - G11 * d2) / (G12 ^ 2 - G11 * G22) with hb
  set ν' : V := a • N1 + b • N2 with hν'
  set ν'' : V := ν - ν' with hν''
  have hBν' : ∀ v, B ν' v = a * B N1 v + b * B N2 v := fun v => by
    simp [hν', LinearMap.add_apply, LinearMap.smul_apply]
  have e1 : B N1 ν' = d1 := by
    rw [h.symm N1 ν', hBν' N1, h21, ← hG11]
    rw [ha, hb, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hDne]; ring
  have e2 : B N2 ν' = d2 := by
    rw [h.symm N2 ν', hBν' N2, ← hG12, ← hG22]
    rw [ha, hb, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hDne]; ring
  have k1 : B N1 ν'' = 0 := by simp [hν'', e1, hd1]
  have k2 : B N2 ν'' = 0 := by simp [hν'', e2, hd2]
  have h0 : B ν ν'' = 0 := hν ν'' k1 k2
  have h1 : B ν' ν'' = 0 := by rw [hBν', k1, k2]; ring
  have hsq : B ν'' ν'' = 0 := by
    have : B ν'' ν'' = B ν ν'' - B ν' ν'' := by
      simp only [hν'', map_sub, LinearMap.sub_apply]
      rw [h.symm ν' ν]
    rw [this, h0, h1]; ring
  have hz : ν'' = 0 := by
    by_contra hne
    have := h.spacelike ν'' k1 k2 hne
    rw [hsq] at this
    exact lt_irrefl _ this
  refine ⟨a, b, ?_⟩
  have : ν = ν' + ν'' := by simp [hν'']
  rw [this, hz, add_zero]

end Geometry

end Lightlike.Penrose.NullNormal
