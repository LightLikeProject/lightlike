import Lightlike.GR.SpinorHelicity

/-!
# Three-particle kinematics and three-point amplitudes fixed by little-group scaling

Three massless particles, all outgoing, with square spinors `λ_i = |i]` and angle spinors `λ̃_i = ⟨i|`
(`SpinorHelicity.lean`), and momentum conservation `Σ_i p_i = 0`, i.e. `Σ_i λ_i λ̃_iᵀ = 0`
(`Conserved3`, `conserved3_iff`).

* **3-particle special kinematics** (`special_kinematics`, Elvang-Huang p. 18, (2.56)): either all angle
  brackets `⟨ij⟩` vanish or all square brackets `[ij]` vanish; the proof is (2.56) and
  `⟨12⟩[23] = −⟨1|p₂|3] = 0` (`angleBr_mul_squareBr_conserved`, `contract_conserved3`).
* **Three-point amplitudes are fixed by little-group scaling** (Elvang-Huang (2.94)–(2.96), p. 28): the
  ansatz `⟨12⟩^{x₁₂} ⟨13⟩^{x₁₃} ⟨23⟩^{x₂₃}` (`angleAnsatz`) scales as `t₁^{x₁₂+x₁₃} t₂^{x₁₂+x₂₃} t₃^{x₁₃+x₂₃}`
  under `|i⟩ ↦ tᵢ |i⟩` (`angleAnsatz_littleGroup`); it has the little-group weights `−2hᵢ` of (2.93)
  iff (2.95) holds (`angleAnsatz_weights_iff`), iff `x₁₂ = h₃ − h₁ − h₂`, `x₁₃ = h₂ − h₁ − h₃`,
  `x₂₃ = h₁ − h₂ − h₃` (2.96) (`angle_exponents_iff`). The square-bracket ansatz has the opposite
  exponents (`squareAnsatz_littleGroup`, `square_exponents_iff`, (2.98)).
* **The dimension count** (Elvang-Huang p. 29): brackets have mass dimension 1 (`angleAnsatz_dilation`,
  `squareAnsatz_dilation`); the angle amplitude has dimension `−(h₁ + h₂ + h₃)`, the square amplitude
  `h₁ + h₂ + h₃`, and for `Σhᵢ ≠ 0` exactly one is positive (`three_point_dimension`); `HasMassDim`,
  `HasMassDim.unique`; (2.97) has dimension `1` and (2.98) dimension `−1` (`gluon_mmp_massDim`,
  `gluon_mmp_square_massDim`). **The selection** (`three_point_selection`): with the source's physical input
  "the three-point amplitude has mass dimension 1" (p. 29, from locality and (2.99)) as a hypothesis, the
  angle ansatz is the one for `Σhᵢ = −1` and the square ansatz the one for `Σhᵢ = +1`.
* Trust checks: the gluon amplitude `⟨12⟩³/(⟨13⟩⟨23⟩)` of (2.97) has the weights of `1⁻2⁻3⁺`
  (`gluon_mmp_littleGroup`); the square-bracket alternative `[13][23]/[12]³` of (2.98) too
  (`gluon_mmp_square_littleGroup`).

Helicities enter through `Hᵢ = 2hᵢ ∈ ℤ` (half-integer helicities).

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697: §2.4, p. 18, (2.56) and the argument
  after it; §2.6, p. 27, (2.92); p. 28, (2.93)–(2.96); p. 29, (2.97)–(2.98).
-/

open Matrix Complex

noncomputable section

namespace Lightlike.SpinorHelicity

/-- Momentum conservation for three massless particles, all outgoing, in spinors:
`Σ_i λ_{i,a} λ̃_{i,ḃ} = 0`. -/
def Conserved3 (l lt : Fin 3 → Fin 2 → ℂ) : Prop :=
  ∀ a b, l 0 a * lt 0 b + l 1 a * lt 1 b + l 2 a * lt 2 b = 0

/-- `Conserved3` is `p₁ + p₂ + p₃ = 0` for `pᵢ = nullMom λᵢ λ̃ᵢ`. -/
theorem conserved3_iff (l lt : Fin 3 → Fin 2 → ℂ) :
    Conserved3 l lt ↔ nullMom (l 0) (lt 0) + nullMom (l 1) (lt 1) + nullMom (l 2) (lt 2) = 0 := by
  have key : ∀ p : Fin 4 → ℂ, p = 0 ↔ momBispinor p = 0 := fun p => by
    constructor
    · rintro rfl; ext i j; fin_cases i <;> fin_cases j <;> simp [momBispinor]
    · intro h; rw [← momOf_momBispinor p, h]; funext μ; fin_cases μ <;> simp [momOf]
  have hadd : ∀ p q : Fin 4 → ℂ, momBispinor (p + q) = momBispinor p + momBispinor q := by
    intro p q; ext i j; fin_cases i <;> fin_cases j <;> simp [momBispinor] <;> ring
  rw [key, hadd, hadd, momBispinor_nullMom, momBispinor_nullMom, momBispinor_nullMom]
  constructor
  · intro h; ext a b; simp only [Matrix.add_apply, Matrix.neg_apply, vecMulVec_apply, Matrix.zero_apply]
    linear_combination -h a b
  · intro h a b
    have := congrFun (congrFun h a) b
    simp only [Matrix.add_apply, Matrix.neg_apply, vecMulVec_apply, Matrix.zero_apply] at this
    linear_combination -this

/-- **Contraction with momentum conservation**: `Σ_i ⟨A i⟩ [i B] = 0` for any spinors `A`, `B`
(Elvang-Huang (2.38) with conservation). The certificate was found by a linear solve (sympy). -/
theorem contract_conserved3 {l lt : Fin 3 → Fin 2 → ℂ} (h : Conserved3 l lt) (A B : Fin 2 → ℂ) :
    angleBr A (lt 0) * squareBr (l 0) B + angleBr A (lt 1) * squareBr (l 1) B +
      angleBr A (lt 2) * squareBr (l 2) B = 0 := by
  simp only [angleBr_eq, squareBr_eq]
  linear_combination (B 1 * A 1) * h 0 0 - (B 1 * A 0) * h 0 1 - (B 0 * A 1) * h 1 0 +
    (B 0 * A 0) * h 1 1

/-- `⟨i j⟩ [j k] = 0` for `i, j, k` distinct (Elvang-Huang p. 18: `⟨12⟩[23] = ⟨1|(p₁ + p₃)|3] = 0`). -/
theorem angleBr_mul_squareBr_conserved {l lt : Fin 3 → Fin 2 → ℂ} (h : Conserved3 l lt) {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    angleBr (lt i) (lt j) * squareBr (l j) (l k) = 0 := by
  have hc := contract_conserved3 h (lt i) (l k)
  have hii : angleBr (lt i) (lt i) = 0 := by rw [angleBr_eq]; ring
  have hkk : squareBr (l k) (l k) = 0 := by rw [squareBr_eq]; ring
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

/-- `⟨i j⟩ [j i] = 0` for `i ≠ j` (Elvang-Huang (2.56): `⟨12⟩[12] = (p₁ + p₂)² = p₃² = 0`). -/
theorem angleBr_mul_squareBr_self_conserved {l lt : Fin 3 → Fin 2 → ℂ} (h : Conserved3 l lt) :
    angleBr (lt 0) (lt 1) * squareBr (l 1) (l 0) = 0 ∧
      angleBr (lt 0) (lt 2) * squareBr (l 2) (l 0) = 0 ∧
        angleBr (lt 1) (lt 2) * squareBr (l 2) (l 1) = 0 := by
  have c0 := contract_conserved3 h (lt 0) (l 0)
  have c1 := contract_conserved3 h (lt 1) (l 1)
  have c2 := contract_conserved3 h (lt 2) (l 2)
  simp only [angleBr_eq, squareBr_eq] at c0 c1 c2 ⊢
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (c0 + c1 - c2) / 2
  · linear_combination (c0 - c1 + c2) / 2
  · linear_combination (-c0 + c1 + c2) / 2

/-- **3-particle special kinematics** (Elvang-Huang p. 18): for three massless momenta with
`p₁ + p₂ + p₃ = 0`, either all angle brackets or all square brackets vanish. -/
theorem special_kinematics {l lt : Fin 3 → Fin 2 → ℂ} (h : Conserved3 l lt) :
    (angleBr (lt 0) (lt 1) = 0 ∧ angleBr (lt 0) (lt 2) = 0 ∧ angleBr (lt 1) (lt 2) = 0) ∨
      (squareBr (l 0) (l 1) = 0 ∧ squareBr (l 0) (l 2) = 0 ∧ squareBr (l 1) (l 2) = 0) := by
  obtain ⟨s01, s02, s12⟩ := angleBr_mul_squareBr_self_conserved h
  have t := fun {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) =>
    angleBr_mul_squareBr_conserved h hij hjk hik
  have a10 : angleBr (lt 1) (lt 0) = -angleBr (lt 0) (lt 1) := angleBr_antisymm _ _
  have a20 : angleBr (lt 2) (lt 0) = -angleBr (lt 0) (lt 2) := angleBr_antisymm _ _
  have a21 : angleBr (lt 2) (lt 1) = -angleBr (lt 1) (lt 2) := angleBr_antisymm _ _
  have q10 : squareBr (l 1) (l 0) = -squareBr (l 0) (l 1) := squareBr_antisymm _ _
  have q20 : squareBr (l 2) (l 0) = -squareBr (l 0) (l 2) := squareBr_antisymm _ _
  have q21 : squareBr (l 2) (l 1) = -squareBr (l 1) (l 2) := squareBr_antisymm _ _
  by_cases h01 : angleBr (lt 0) (lt 1) = 0
  · by_cases h02 : angleBr (lt 0) (lt 2) = 0
    · by_cases h12 : angleBr (lt 1) (lt 2) = 0
      · exact Or.inl ⟨h01, h02, h12⟩
      · -- `⟨12⟩ ≠ 0`
        right
        have e1 := t (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide)
        have e2 := t (i := 2) (j := 1) (k := 0) (by decide) (by decide) (by decide)
        rw [q21, mul_neg, neg_eq_zero, mul_eq_zero, or_iff_right h12] at s12
        rw [a21, neg_mul, neg_eq_zero, mul_eq_zero, or_iff_right h12, q10, neg_eq_zero] at e2
        rw [mul_eq_zero, or_iff_right h12, q20, neg_eq_zero] at e1
        exact ⟨e2, e1, s12⟩
    · -- `⟨02⟩ ≠ 0`
      right
      have e1 := t (i := 0) (j := 2) (k := 1) (by decide) (by decide) (by decide)
      have e2 := t (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)
      rw [q20, mul_neg, neg_eq_zero, mul_eq_zero, or_iff_right h02] at s02
      rw [a20, neg_mul, neg_eq_zero, mul_eq_zero, or_iff_right h02] at e2
      rw [mul_eq_zero, or_iff_right h02, q21, neg_eq_zero] at e1
      exact ⟨e2, s02, e1⟩
  · -- `⟨01⟩ ≠ 0`
    right
    have e1 := t (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
    have e2 := t (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)
    rw [q10, mul_neg, neg_eq_zero, mul_eq_zero, or_iff_right h01] at s01
    rw [a10, neg_mul, neg_eq_zero, mul_eq_zero, or_iff_right h01] at e2
    rw [mul_eq_zero, or_iff_right h01] at e1
    exact ⟨s01, e2, e1⟩

/-! ## Three-point amplitudes and little-group scaling -/

/-- The angle-bracket ansatz `c ⟨12⟩^{x₁₂} ⟨13⟩^{x₁₃} ⟨23⟩^{x₂₃}` (Elvang-Huang (2.94)). -/
def angleAnsatz (c : ℂ) (x12 x13 x23 : ℤ) (lt : Fin 3 → Fin 2 → ℂ) : ℂ :=
  c * angleBr (lt 0) (lt 1) ^ x12 * angleBr (lt 0) (lt 2) ^ x13 * angleBr (lt 1) (lt 2) ^ x23

/-- The square-bracket ansatz `c [12]^{y₁₂} [13]^{y₁₃} [23]^{y₂₃}`. -/
def squareAnsatz (c : ℂ) (y12 y13 y23 : ℤ) (l : Fin 3 → Fin 2 → ℂ) : ℂ :=
  c * squareBr (l 0) (l 1) ^ y12 * squareBr (l 0) (l 2) ^ y13 * squareBr (l 1) (l 2) ^ y23

lemma angleBr_smul_smul (s t : ℂ) (a b : Fin 2 → ℂ) :
    angleBr (s • a) (t • b) = s * t * angleBr a b := by
  simp only [angleBr_eq, Pi.smul_apply, smul_eq_mul]; ring

lemma squareBr_smul_smul (s t : ℂ) (a b : Fin 2 → ℂ) :
    squareBr (s • a) (t • b) = s * t * squareBr a b := by
  simp only [squareBr_eq, Pi.smul_apply, smul_eq_mul]; ring

/-- **The little-group scaling of the angle ansatz**: under `|i⟩ ↦ tᵢ |i⟩` it is multiplied by
`t₁^{x₁₂+x₁₃} t₂^{x₁₂+x₂₃} t₃^{x₁₃+x₂₃}`. -/
theorem angleAnsatz_littleGroup (c : ℂ) (x12 x13 x23 : ℤ) {t : Fin 3 → ℂ} (ht : ∀ i, t i ≠ 0)
    (lt : Fin 3 → Fin 2 → ℂ) :
    angleAnsatz c x12 x13 x23 (fun i => t i • lt i) =
      t 0 ^ (x12 + x13) * t 1 ^ (x12 + x23) * t 2 ^ (x13 + x23) * angleAnsatz c x12 x13 x23 lt := by
  simp only [angleAnsatz, angleBr_smul_smul, mul_zpow, zpow_add₀ (ht 0), zpow_add₀ (ht 1),
    zpow_add₀ (ht 2)]
  ring

/-- **The little-group scaling of the square ansatz**: under `|i] ↦ tᵢ⁻¹ |i]` it is multiplied by
`t₁^{−(y₁₂+y₁₃)} t₂^{−(y₁₂+y₂₃)} t₃^{−(y₁₃+y₂₃)}`. -/
theorem squareAnsatz_littleGroup (c : ℂ) (y12 y13 y23 : ℤ) {t : Fin 3 → ℂ} (ht : ∀ i, t i ≠ 0)
    (l : Fin 3 → Fin 2 → ℂ) :
    squareAnsatz c y12 y13 y23 (fun i => (t i)⁻¹ • l i) =
      t 0 ^ (-(y12 + y13)) * t 1 ^ (-(y12 + y23)) * t 2 ^ (-(y13 + y23)) *
        squareAnsatz c y12 y13 y23 l := by
  simp only [squareAnsatz, squareBr_smul_smul, mul_zpow, _root_.inv_zpow', neg_add,
    zpow_add₀ (ht 0), zpow_add₀ (ht 1), zpow_add₀ (ht 2)]
  ring

/-- **(2.95) ⟺ (2.96)**: with `Hᵢ = 2hᵢ`, the weight equations `−2h₁ = x₁₂ + x₁₃`, `−2h₂ = x₁₂ + x₂₃`,
`−2h₃ = x₁₃ + x₂₃` have the unique solution `x₁₂ = h₃ − h₁ − h₂`, `x₁₃ = h₂ − h₁ − h₃`,
`x₂₃ = h₁ − h₂ − h₃`. -/
theorem angle_exponents_iff (x12 x13 x23 H1 H2 H3 : ℤ) :
    (x12 + x13 = -H1 ∧ x12 + x23 = -H2 ∧ x13 + x23 = -H3) ↔
      (2 * x12 = H3 - H1 - H2 ∧ 2 * x13 = H2 - H1 - H3 ∧ 2 * x23 = H1 - H2 - H3) := by
  omega

/-- The square-bracket version (2.98): `y₁₂ = h₁ + h₂ − h₃` etc. -/
theorem square_exponents_iff (y12 y13 y23 H1 H2 H3 : ℤ) :
    (-(y12 + y13) = -H1 ∧ -(y12 + y23) = -H2 ∧ -(y13 + y23) = -H3) ↔
      (2 * y12 = H1 + H2 - H3 ∧ 2 * y13 = H1 + H3 - H2 ∧ 2 * y23 = H2 + H3 - H1) := by
  omega

lemma zpow_two_injective {m n : ℤ} (h : (2 : ℂ) ^ m = (2 : ℂ) ^ n) : m = n := by
  have h' : (2 : ℝ) ^ m = (2 : ℝ) ^ n := by
    have := congrArg (fun z : ℂ => ‖z‖) h
    simpa [norm_zpow] using this
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) h'

/-- **Three-point amplitudes are fixed by little-group scaling** (Elvang-Huang (2.93)–(2.96)): a nonzero
angle ansatz has the little-group weights `−2hᵢ` (`Hᵢ = 2hᵢ`) for all scalings iff its exponents are
`x₁₂ = h₃ − h₁ − h₂`, `x₁₃ = h₂ − h₁ − h₃`, `x₂₃ = h₁ − h₂ − h₃`. -/
theorem angleAnsatz_weights_iff {c : ℂ} {x12 x13 x23 : ℤ} {lt : Fin 3 → Fin 2 → ℂ}
    (hA : angleAnsatz c x12 x13 x23 lt ≠ 0) (H1 H2 H3 : ℤ) :
    (∀ t : Fin 3 → ℂ, (∀ i, t i ≠ 0) →
        angleAnsatz c x12 x13 x23 (fun i => t i • lt i) =
          t 0 ^ (-H1) * t 1 ^ (-H2) * t 2 ^ (-H3) * angleAnsatz c x12 x13 x23 lt) ↔
      (2 * x12 = H3 - H1 - H2 ∧ 2 * x13 = H2 - H1 - H3 ∧ 2 * x23 = H1 - H2 - H3) := by
  rw [← angle_exponents_iff]
  constructor
  · intro hw
    have key : ∀ t : Fin 3 → ℂ, (∀ j, t j ≠ 0) →
        t 0 ^ (x12 + x13) * t 1 ^ (x12 + x23) * t 2 ^ (x13 + x23) =
          t 0 ^ (-H1) * t 1 ^ (-H2) * t 2 ^ (-H3) := by
      intro t ht
      have := hw t ht
      rw [angleAnsatz_littleGroup c x12 x13 x23 ht] at this
      exact mul_right_cancel₀ hA this
    have k0 := key ![2, 1, 1] (by intro j; fin_cases j <;> norm_num)
    have k1 := key ![1, 2, 1] (by intro j; fin_cases j <;> norm_num)
    have k2 := key ![1, 1, 2] (by intro j; fin_cases j <;> norm_num)
    norm_num at k0 k1 k2
    exact ⟨zpow_two_injective (k0.trans (zpow_neg 2 H1).symm),
      zpow_two_injective (k1.trans (zpow_neg 2 H2).symm),
      zpow_two_injective (k2.trans (zpow_neg 2 H3).symm)⟩
  · rintro ⟨e1, e2, e3⟩ t ht
    rw [angleAnsatz_littleGroup c x12 x13 x23 ht, e1, e2, e3]

/-- Trust check (Elvang-Huang (2.97)): the gluon amplitude `g ⟨12⟩³ / (⟨13⟩⟨23⟩)` scales with the
little-group weights `−2hᵢ = (2, 2, −2)` of `1⁻ 2⁻ 3⁺`. -/
theorem gluon_mmp_littleGroup (g : ℂ) {t : Fin 3 → ℂ} (ht : ∀ i, t i ≠ 0) (lt : Fin 3 → Fin 2 → ℂ) :
    angleAnsatz g 3 (-1) (-1) (fun i => t i • lt i) =
      t 0 ^ (2 : ℤ) * t 1 ^ (2 : ℤ) * t 2 ^ (-2 : ℤ) * angleAnsatz g 3 (-1) (-1) lt := by
  rw [angleAnsatz_littleGroup g 3 (-1) (-1) ht]
  norm_num

/-- Trust check (Elvang-Huang (2.98)): the square-bracket alternative `g' [13][23] / [12]³` has the same
little-group weights `(2, 2, −2)`. -/
theorem gluon_mmp_square_littleGroup (g : ℂ) {t : Fin 3 → ℂ} (ht : ∀ i, t i ≠ 0)
    (l : Fin 3 → Fin 2 → ℂ) :
    squareAnsatz g (-3) 1 1 (fun i => (t i)⁻¹ • l i) =
      t 0 ^ (2 : ℤ) * t 1 ^ (2 : ℤ) * t 2 ^ (-2 : ℤ) * squareAnsatz g (-3) 1 1 l := by
  rw [squareAnsatz_littleGroup g (-3) 1 1 ht]
  norm_num

/-! ## Mass dimension (Elvang-Huang p. 29) -/

/-- Brackets have mass dimension `1` (Elvang-Huang p. 29, from (2.24)): under `λ ↦ s λ`, `λ̃ ↦ s λ̃`
(so `p ↦ s² p`) the angle ansatz is multiplied by `(s²)^{x₁₂ + x₁₃ + x₂₃}`. -/
theorem angleAnsatz_dilation (c : ℂ) (x12 x13 x23 : ℤ) {s : ℂ} (hs : s ≠ 0)
    (lt : Fin 3 → Fin 2 → ℂ) :
    angleAnsatz c x12 x13 x23 (fun i => s • lt i) =
      (s ^ 2) ^ (x12 + x13 + x23) * angleAnsatz c x12 x13 x23 lt := by
  have h2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  simp only [angleAnsatz, angleBr_smul_smul, mul_zpow, zpow_add₀ h2, ← sq]
  ring

/-- The square ansatz has mass dimension `y₁₂ + y₁₃ + y₂₃`. -/
theorem squareAnsatz_dilation (c : ℂ) (y12 y13 y23 : ℤ) {s : ℂ} (hs : s ≠ 0)
    (l : Fin 3 → Fin 2 → ℂ) :
    squareAnsatz c y12 y13 y23 (fun i => s • l i) =
      (s ^ 2) ^ (y12 + y13 + y23) * squareAnsatz c y12 y13 y23 l := by
  have h2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  simp only [squareAnsatz, squareBr_smul_smul, mul_zpow, zpow_add₀ h2, ← sq]
  ring

/-- **The dimension count** (Elvang-Huang p. 29): with the exponents fixed by little-group scaling, the
angle amplitude (2.96) has mass dimension `−(h₁ + h₂ + h₃)` and the square amplitude `h₁ + h₂ + h₃`
(`Hᵢ = 2hᵢ`); so for `h₁ + h₂ + h₃ ≠ 0` exactly one of them has positive dimension (for `1⁻2⁻3⁺`, `+1` for
(2.97) and `−1` for (2.98)). -/
theorem three_point_dimension {x12 x13 x23 y12 y13 y23 H1 H2 H3 : ℤ}
    (hx : 2 * x12 = H3 - H1 - H2 ∧ 2 * x13 = H2 - H1 - H3 ∧ 2 * x23 = H1 - H2 - H3)
    (hy : 2 * y12 = H1 + H2 - H3 ∧ 2 * y13 = H1 + H3 - H2 ∧ 2 * y23 = H2 + H3 - H1) :
    2 * (x12 + x13 + x23) = -(H1 + H2 + H3) ∧ 2 * (y12 + y13 + y23) = H1 + H2 + H3 ∧
      (H1 + H2 + H3 ≠ 0 → (0 < x12 + x13 + x23 ↔ ¬ 0 < y12 + y13 + y23)) := by
  omega

/-- A three-point function of the spinors has **mass dimension `k`** if it scales as `(s²)^k` under
`λᵢ ↦ s λᵢ`, `λ̃ᵢ ↦ s λ̃ᵢ` (so `pᵢ ↦ s² pᵢ`; brackets have dimension `1`, Elvang-Huang p. 29). -/
def HasMassDim (A : (Fin 3 → Fin 2 → ℂ) → (Fin 3 → Fin 2 → ℂ) → ℂ) (k : ℤ)
    (l lt : Fin 3 → Fin 2 → ℂ) : Prop :=
  ∀ s : ℂ, s ≠ 0 → A (fun i => s • l i) (fun i => s • lt i) = (s ^ 2) ^ k * A l lt

lemma sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  have : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  exact_mod_cast this

lemma sqrt_two_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact_mod_cast this.ne'

/-- The mass dimension of a nonzero function is unique. -/
theorem HasMassDim.unique {A : (Fin 3 → Fin 2 → ℂ) → (Fin 3 → Fin 2 → ℂ) → ℂ} {k k' : ℤ}
    {l lt : Fin 3 → Fin 2 → ℂ} (hA : A l lt ≠ 0) (h : HasMassDim A k l lt)
    (h' : HasMassDim A k' l lt) : k = k' := by
  have e := (h _ sqrt_two_ne).symm.trans (h' _ sqrt_two_ne)
  rw [sqrt_two_sq] at e
  exact zpow_two_injective (mul_right_cancel₀ hA e)

/-- **The angle ansatz has mass dimension `x₁₂ + x₁₃ + x₂₃`** (and no other, if it is nonzero). -/
theorem hasMassDim_angleAnsatz (c : ℂ) (x12 x13 x23 : ℤ) (l lt : Fin 3 → Fin 2 → ℂ) :
    HasMassDim (fun _ lt => angleAnsatz c x12 x13 x23 lt) (x12 + x13 + x23) l lt :=
  fun _ hs => angleAnsatz_dilation c x12 x13 x23 hs lt

/-- **The square ansatz has mass dimension `y₁₂ + y₁₃ + y₂₃`.** -/
theorem hasMassDim_squareAnsatz (c : ℂ) (y12 y13 y23 : ℤ) (l lt : Fin 3 → Fin 2 → ℂ) :
    HasMassDim (fun l _ => squareAnsatz c y12 y13 y23 l) (y12 + y13 + y23) l lt :=
  fun _ hs => squareAnsatz_dilation c y12 y13 y23 hs l

/-- **(2.97) has mass dimension `1`** (Elvang-Huang p. 29). -/
theorem gluon_mmp_massDim (g : ℂ) (l lt : Fin 3 → Fin 2 → ℂ) :
    HasMassDim (fun _ lt => angleAnsatz g 3 (-1) (-1) lt) 1 l lt := by
  simpa using hasMassDim_angleAnsatz g 3 (-1) (-1) l lt

/-- **(2.98) has mass dimension `−1`** (Elvang-Huang p. 29). -/
theorem gluon_mmp_square_massDim (g : ℂ) (l lt : Fin 3 → Fin 2 → ℂ) :
    HasMassDim (fun l _ => squareAnsatz g (-3) 1 1 l) (-1) l lt := by
  simpa using hasMassDim_squareAnsatz g (-3) 1 1 l lt

/-- **The selection of the three-point amplitude** (Elvang-Huang p. 29, with the physical input that the
three-point amplitude has mass dimension `1` as a hypothesis): a nonzero angle ansatz with the
little-group weights `−2hᵢ` (`Hᵢ = 2hᵢ`) has mass dimension `1` iff `h₁ + h₂ + h₃ = −1`; a nonzero
square ansatz with these weights has mass dimension `1` iff `h₁ + h₂ + h₃ = +1`. -/
theorem three_point_selection {c : ℂ} {x12 x13 x23 y12 y13 y23 H1 H2 H3 : ℤ}
    {l lt : Fin 3 → Fin 2 → ℂ}
    (hx : 2 * x12 = H3 - H1 - H2 ∧ 2 * x13 = H2 - H1 - H3 ∧ 2 * x23 = H1 - H2 - H3)
    (hy : 2 * y12 = H1 + H2 - H3 ∧ 2 * y13 = H1 + H3 - H2 ∧ 2 * y23 = H2 + H3 - H1)
    (hA : angleAnsatz c x12 x13 x23 lt ≠ 0) (hB : squareAnsatz c y12 y13 y23 l ≠ 0) :
    (HasMassDim (fun _ lt => angleAnsatz c x12 x13 x23 lt) 1 l lt ↔ H1 + H2 + H3 = -2) ∧
      (HasMassDim (fun l _ => squareAnsatz c y12 y13 y23 l) 1 l lt ↔ H1 + H2 + H3 = 2) := by
  constructor
  · constructor
    · intro h
      have := HasMassDim.unique (A := fun _ lt => angleAnsatz c x12 x13 x23 lt) hA h
        (hasMassDim_angleAnsatz c x12 x13 x23 l lt)
      omega
    · intro h
      have hk : x12 + x13 + x23 = 1 := by omega
      simpa [hk] using hasMassDim_angleAnsatz c x12 x13 x23 l lt
  · constructor
    · intro h
      have := HasMassDim.unique (A := fun l _ => squareAnsatz c y12 y13 y23 l) hB h
        (hasMassDim_squareAnsatz c y12 y13 y23 l lt)
      omega
    · intro h
      have hk : y12 + y13 + y23 = 1 := by omega
      simpa [hk] using hasMassDim_squareAnsatz c y12 y13 y23 l lt

end Lightlike.SpinorHelicity
