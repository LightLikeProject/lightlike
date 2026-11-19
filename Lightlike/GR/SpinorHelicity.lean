import Lightlike.GR.ComplexMinkowski
import Physlib.Relativity.Fermions.Weyl.Metric

/-!
# Spinor-helicity variables

Conventions of Elvang-Huang (Appendix A): the mostly-plus metric, `p · q = −p⁰q⁰ + p⃗ · q⃗`
(`mdot`); the momentum bispinor `p_{aḃ} = p_μ (σ^μ)_{aḃ} = [[−p⁰ + p³, p¹ − i p²], [p¹ + i p², −p⁰ − p³]]`
(`momBispinor`, (A.10)–(A.11)), with `det p = −p · p` ((A.12), `det_momBispinor`); `ε^{ab} = ε^{ȧḃ} =
[[0, 1], [−1, 0]]` ((A.3), Physlib's `Fermion.metricRaw`). The square spinor is `λ_a = |p]_a`, the angle
spinor `λ̃_ȧ = ⟨p|_ȧ`.

* **Null momenta factorise** (`mdot_self_eq_zero_iff`, (2.16), pp. 10–11): `p · p = 0` iff
  `p_{aḃ} = −λ_a λ̃_ḃ`; every pair of spinors gives a null momentum (`nullMom`, `mdot_nullMom_self`).
  The bispinor is `−√2` times the adjugate of G3-061's `spinorMat` (`momBispinor_eq_adjugate`,
  `mdot_self_eq_neg_qC`).
* **The factorisation is unique up to little-group scaling** (`exists_littleGroup_of_eq`, p. 11, (2.92)):
  `(λ, λ̃) ↦ (t⁻¹ λ, t λ̃)`, which leaves the momentum invariant (`nullMom_littleGroup`).
* **Brackets** (2.22): `⟨p q⟩ = ⟨p|_ȧ ε^{ȧḃ} ⟨q|_ḃ` (`angleBr`), `[p q] = ε^{ab} |p]_b |q]_a` (`squareBr`),
  antisymmetric (2.23); `⟨p q⟩ [p q] = 2 p · q` (`angleBr_mul_squareBr`, (2.24)); the Mandelstam variable
  `s_{ij} = −(p_i + p_j)²` (2.39) is `⟨i j⟩ [j i]` (`mandelstam_nullMom`).
* **The Schouten identity** (2.46)–(2.48) for angle and square brackets (`schouten_angleBr`,
  `schouten_squareBr`, `schouten_raise`).
* **Little-group weights** (2.92): `⟨i j⟩ ↦ t ⟨i j⟩`, `[i j] ↦ t⁻¹ [i j]` under `|i⟩ ↦ t |i⟩`,
  `|i] ↦ t⁻¹ |i]` (`angleBr_smul_left`, `squareBr_smul_left`).

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697: Appendix A, p. 244, (A.1)–(A.12); §2.1,
  p. 9, (2.6)–(2.8); §2.2, pp. 10–11, (2.13), (2.16) and "det p = 0 ⇔ p_{aḃ} = −λ_a λ̃_ḃ"; §2.3, p. 12,
  (2.22)–(2.24); p. 15, (2.39); p. 16, (2.46)–(2.48); §2.6, p. 27, (2.92).
-/

open Matrix Complex

noncomputable section

namespace Lightlike.SpinorHelicity

/-- `ε^{ab}` (Elvang-Huang (A.3)), Physlib's `Fermion.metricRaw`. -/
abbrev epsU : Matrix (Fin 2) (Fin 2) ℂ := Fermion.metricRaw

@[simp] lemma epsU_00 : epsU 0 0 = 0 := rfl
@[simp] lemma epsU_01 : epsU 0 1 = 1 := rfl
@[simp] lemma epsU_10 : epsU 1 0 = -1 := rfl
@[simp] lemma epsU_11 : epsU 1 1 = 0 := rfl

/-- The mostly-plus Minkowski product `p · q = −p⁰q⁰ + p¹q¹ + p²q² + p³q³` (Elvang-Huang Appendix A). -/
def mdot (p q : Fin 4 → ℂ) : ℂ := -p 0 * q 0 + p 1 * q 1 + p 2 * q 2 + p 3 * q 3

/-- The momentum bispinor `p_{aḃ} = p_μ (σ^μ)_{aḃ}` (Elvang-Huang (A.10)–(A.11), (2.7)). -/
def momBispinor (p : Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-p 0 + p 3, p 1 - I * p 2; p 1 + I * p 2, -p 0 - p 3]

/-- `det p_{aḃ} = −p · p` (Elvang-Huang (A.12), (2.8)). -/
theorem det_momBispinor (p : Fin 4 → ℂ) : (momBispinor p).det = -mdot p p := by
  simp only [momBispinor, det_fin_two_of, mdot]
  ring_nf
  rw [I_sq]
  ring

/-- The momentum of a bispinor (the inverse of `momBispinor`). -/
def momOf (m : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℂ :=
  ![-(m 0 0 + m 1 1) / 2, (m 0 1 + m 1 0) / 2, (m 1 0 - m 0 1) / (2 * I), (m 0 0 - m 1 1) / 2]

lemma momBispinor_momOf (m : Matrix (Fin 2) (Fin 2) ℂ) : momBispinor (momOf m) = m := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [momBispinor, momOf] <;> field_simp <;> ring_nf

lemma momOf_momBispinor (p : Fin 4 → ℂ) : momOf (momBispinor p) = p := by
  funext μ
  fin_cases μ <;> simp [momBispinor, momOf]
  field_simp
  ring

/-- Momenta are bispinors. -/
def momEquiv : (Fin 4 → ℂ) ≃ Matrix (Fin 2) (Fin 2) ℂ where
  toFun := momBispinor
  invFun := momOf
  left_inv := momOf_momBispinor
  right_inv := momBispinor_momOf

/-- The bispinor is `−√2` times the adjugate of G3-061's spinor matrix (Adamo's `x^{αα̇}`). -/
lemma momBispinor_eq_adjugate (p : Fin 4 → ℂ) :
    momBispinor p = -(Real.sqrt 2 : ℂ) • adjugate (spinorMat p) := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    exact_mod_cast this.ne'
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [momBispinor, spinorMat, adjugate_fin_two, h2] <;> ring

/-- `p · p = −qC p`: G3-061's `qC` has the signature `(+, −, −, −)`. -/
lemma mdot_self_eq_neg_qC (p : Fin 4 → ℂ) : mdot p p = -qC p := by
  simp only [mdot, qC]
  ring

/-- **Null momenta factorise** (Elvang-Huang (2.16), pp. 10–11): `p · p = 0` iff `p_{aḃ} = −λ_a λ̃_ḃ`. -/
theorem mdot_self_eq_zero_iff (p : Fin 4 → ℂ) :
    mdot p p = 0 ↔ ∃ l lt : Fin 2 → ℂ, momBispinor p = -vecMulVec l lt := by
  rw [← neg_eq_zero, ← det_momBispinor, det_eq_zero_iff_vecMulVec]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨-a, b, by rw [h]; ext i j; simp [vecMulVec_apply]⟩
  · rintro ⟨l, lt, h⟩
    exact ⟨-l, lt, by rw [h]; ext i j; simp [vecMulVec_apply]⟩

/-- The null momentum `p_{aḃ} = −λ_a λ̃_ḃ` of a pair of spinors (square `λ = |p]`, angle `λ̃ = ⟨p|`). -/
def nullMom (l lt : Fin 2 → ℂ) : Fin 4 → ℂ := momOf (-vecMulVec l lt)

lemma momBispinor_nullMom (l lt : Fin 2 → ℂ) : momBispinor (nullMom l lt) = -vecMulVec l lt :=
  momBispinor_momOf _

lemma mdot_nullMom_self (l lt : Fin 2 → ℂ) : mdot (nullMom l lt) (nullMom l lt) = 0 :=
  (mdot_self_eq_zero_iff _).2 ⟨l, lt, momBispinor_nullMom l lt⟩

/-- **Little-group scaling leaves the momentum invariant** (Elvang-Huang (2.92)):
`|p⟩ ↦ t |p⟩`, `|p] ↦ t⁻¹ |p]`. -/
theorem nullMom_littleGroup {t : ℂ} (ht : t ≠ 0) (l lt : Fin 2 → ℂ) :
    nullMom (t⁻¹ • l) (t • lt) = nullMom l lt := by
  unfold nullMom
  congr 1
  ext i j
  simp [vecMulVec_apply]
  field_simp

/-- **The factorisation is unique up to little-group scaling** (Elvang-Huang p. 11: "the angle and
square spinors are only defined up to an overall scaling that leaves `p^μ` invariant"). -/
theorem exists_littleGroup_of_eq {l lt l' lt' : Fin 2 → ℂ} (h : vecMulVec l lt = vecMulVec l' lt')
    (hne : vecMulVec l lt ≠ 0) : ∃ t : ℂ, t ≠ 0 ∧ l' = t⁻¹ • l ∧ lt' = t • lt := by
  have hll : ∀ c d, l c * lt d = l' c * lt' d := fun c d => by
    have := congrFun (congrFun h c) d
    simpa [vecMulVec_apply] using this
  obtain ⟨a, b, hab⟩ : ∃ a b, l a * lt b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (by ext c d; simpa [vecMulVec_apply] using hcon c d)
  have hla : l a ≠ 0 := left_ne_zero_of_mul hab
  have hltb : lt b ≠ 0 := right_ne_zero_of_mul hab
  have hab' : l' a * lt' b ≠ 0 := by rw [← hll]; exact hab
  have hl'a : l' a ≠ 0 := left_ne_zero_of_mul hab'
  have hlt'b : lt' b ≠ 0 := right_ne_zero_of_mul hab'
  refine ⟨lt' b / lt b, div_ne_zero hlt'b hltb, ?_, ?_⟩
  · funext c
    simp only [Pi.smul_apply, smul_eq_mul, inv_div]
    rw [div_mul_eq_mul_div, eq_div_iff hlt'b]
    linear_combination (-1 : ℂ) * hll c b
  · funext c
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hltb]
    refine mul_left_cancel₀ hl'a ?_
    linear_combination (-(lt b)) * hll a c + (lt c) * hll a b

/-! ## Brackets -/

/-- The angle bracket `⟨p q⟩ = ⟨p|_ȧ |q⟩^ȧ = ⟨p|_ȧ ε^{ȧḃ} ⟨q|_ḃ` of angle spinors (Elvang-Huang (2.13),
(2.22)). -/
def angleBr (lt lt' : Fin 2 → ℂ) : ℂ := ∑ a, ∑ b, lt a * epsU a b * lt' b

/-- The square bracket `[p q] = [p|^a |q]_a = ε^{ab} |p]_b |q]_a` of square spinors (Elvang-Huang (2.13),
(2.22)). -/
def squareBr (l l' : Fin 2 → ℂ) : ℂ := ∑ a, ∑ b, epsU a b * l b * l' a

lemma angleBr_eq (lt lt' : Fin 2 → ℂ) : angleBr lt lt' = lt 0 * lt' 1 - lt 1 * lt' 0 := by
  simp [angleBr, Fin.sum_univ_two]; ring

lemma squareBr_eq (l l' : Fin 2 → ℂ) : squareBr l l' = l 1 * l' 0 - l 0 * l' 1 := by
  simp [squareBr, Fin.sum_univ_two]; ring

/-- `⟨p q⟩ = −⟨q p⟩` (Elvang-Huang (2.23)). -/
theorem angleBr_antisymm (lt lt' : Fin 2 → ℂ) : angleBr lt lt' = -angleBr lt' lt := by
  simp only [angleBr_eq]; ring

/-- `[p q] = −[q p]` (Elvang-Huang (2.23)). -/
theorem squareBr_antisymm (l l' : Fin 2 → ℂ) : squareBr l l' = -squareBr l' l := by
  simp only [squareBr_eq]; ring

/-- **`⟨p q⟩ [p q] = 2 p · q`** (Elvang-Huang (2.24)). -/
theorem angleBr_mul_squareBr (l lt l' lt' : Fin 2 → ℂ) :
    angleBr lt lt' * squareBr l l' = 2 * mdot (nullMom l lt) (nullMom l' lt') := by
  simp only [angleBr_eq, squareBr_eq, mdot, nullMom, momOf]
  simp [vecMulVec_apply]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The Mandelstam variable `s = −(p + q)²` (Elvang-Huang (2.39), all momenta outgoing). -/
def mandelstam (p q : Fin 4 → ℂ) : ℂ := -mdot (p + q) (p + q)

/-- **`s_{ij} = ⟨i j⟩ [j i]`** for null momenta (Elvang-Huang (2.24), (2.39)). -/
theorem mandelstam_nullMom (l lt l' lt' : Fin 2 → ℂ) :
    mandelstam (nullMom l lt) (nullMom l' lt') = angleBr lt lt' * squareBr l' l := by
  have h1 := mdot_nullMom_self l lt
  have h2 := mdot_nullMom_self l' lt'
  have h3 := angleBr_mul_squareBr l lt l' lt'
  rw [squareBr_antisymm l' l]
  simp only [mandelstam, mdot, Pi.add_apply] at h1 h2 h3 ⊢
  linear_combination -h1 - h2 + h3

/-! ## The Schouten identity -/

/-- **The Schouten identity for angle brackets** (Elvang-Huang (2.48)):
`⟨r i⟩⟨j k⟩ + ⟨r j⟩⟨k i⟩ + ⟨r k⟩⟨i j⟩ = 0`. -/
theorem schouten_angleBr (r i j k : Fin 2 → ℂ) :
    angleBr r i * angleBr j k + angleBr r j * angleBr k i + angleBr r k * angleBr i j = 0 := by
  simp only [angleBr_eq]; ring

/-- **The Schouten identity for square brackets** (Elvang-Huang p. 16):
`[r i][j k] + [r j][k i] + [r k][i j] = 0`. -/
theorem schouten_squareBr (r i j k : Fin 2 → ℂ) :
    squareBr r i * squareBr j k + squareBr r j * squareBr k i + squareBr r k * squareBr i j = 0 := by
  simp only [squareBr_eq]; ring

/-- The raised angle spinor `|p⟩^ȧ = ε^{ȧḃ} ⟨p|_ḃ` (Elvang-Huang (2.13)). -/
def raise (lt : Fin 2 → ℂ) : Fin 2 → ℂ := fun a => ∑ b, epsU a b * lt b

/-- **The Schouten identity as a vector identity** (Elvang-Huang (2.47)):
`|i⟩⟨j k⟩ + |j⟩⟨k i⟩ + |k⟩⟨i j⟩ = 0`. -/
theorem schouten_raise (i j k : Fin 2 → ℂ) :
    raise i * (fun _ => angleBr j k) + raise j * (fun _ => angleBr k i) +
      raise k * (fun _ => angleBr i j) = 0 := by
  funext a
  fin_cases a <;> simp [raise, angleBr_eq, Fin.sum_univ_two] <;> ring

/-! ## Little-group weights -/

/-- Under `|i⟩ ↦ t |i⟩`, `⟨i j⟩ ↦ t ⟨i j⟩` (Elvang-Huang (2.92)). -/
theorem angleBr_smul_left (t : ℂ) (lt lt' : Fin 2 → ℂ) :
    angleBr (t • lt) lt' = t * angleBr lt lt' := by
  simp only [angleBr_eq, Pi.smul_apply, smul_eq_mul]; ring

/-- Under `|i] ↦ t⁻¹ |i]`, `[i j] ↦ t⁻¹ [i j]` (Elvang-Huang (2.92)). -/
theorem squareBr_smul_left (t : ℂ) (l l' : Fin 2 → ℂ) :
    squareBr (t⁻¹ • l) l' = t⁻¹ * squareBr l l' := by
  simp only [squareBr_eq, Pi.smul_apply, smul_eq_mul]; ring

/-- The Mandelstam variables are little-group invariant. -/
theorem mandelstam_littleGroup {t : ℂ} (ht : t ≠ 0) (l lt l' lt' : Fin 2 → ℂ) :
    angleBr (t • lt) lt' * squareBr l' (t⁻¹ • l) = angleBr lt lt' * squareBr l' l := by
  rw [angleBr_smul_left, squareBr_antisymm l', squareBr_smul_left, squareBr_antisymm l l']
  field_simp

/-- On G3-061's null cone: `p · p = 0` iff `qC p = 0` (so `qC_eq_zero_iff_tmul` applies). -/
lemma mdot_self_eq_zero_iff_qC (p : Fin 4 → ℂ) : mdot p p = 0 ↔ qC p = 0 := by
  rw [mdot_self_eq_neg_qC, neg_eq_zero]

/-- A trust check: the momentum `(E, 0, 0, E)` along the `z`-axis is `−λ λ̃` with `λ = (0, 1)`,
`λ̃ = (0, 2E)`. -/
example (E : ℂ) : nullMom ![0, 1] ![0, 2 * E] = ![E, 0, 0, E] := by
  funext μ
  fin_cases μ <;> simp [nullMom, momOf]

end Lightlike.SpinorHelicity
