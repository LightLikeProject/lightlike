import Mathlib
import Physlib.Relativity.Fermions.Weyl.Metric

/-!
# Zero-rest-mass fields and the Maxwell spinor decomposition

Spinor indices take values in `Fin 2`; `ε_{αβ}` is Physlib's `Fermion.metricRaw` (`ε₀₁ = 1`), used
for dotted and undotted indices alike.

* **The Maxwell spinor decomposition** (Adamo (3.2)–(3.4)): a bispinor 2-form `F_{αα̇ββ̇}`,
  antisymmetric under `(αα̇) ↔ (ββ̇)`, is `F = ε_{αβ} F̃_{α̇β̇} + ε_{α̇β̇} F_{αβ}` with the symmetric
  anti-self-dual and self-dual parts `F_{αβ} = ½ ε_{γ̇δ̇} F_{αγ̇βδ̇}`, `F̃_{α̇β̇} = ½ ε_{γδ} F_{γα̇δβ̇}`
  ((3.3) up to the sign named below; `maxwell_decomposition`, `asdPart`, `sdPart`), and conversely
  (`parts_ofParts`): a linear equivalence between 2-forms and pairs of symmetric spinors (`maxwellEquiv`).
* **Maxwell's equations are the spin-1 z.r.m. equations** (Adamo (3.7)–(3.11)), pointwise in the
  first derivatives (`maxwell_iff_zrm_D`) and for a 2-form field on an open set (`maxwell_iff_zrm`).
* **Zero-rest-mass fields of every helicity** (Adamo (3.15)): `IsZrmNeg`, `IsZrmPos` (helicity
  `∓(n + 1)/2`), `IsZrmScalar` (`□Φ = 0`); the components of a `C²` z.r.m. field solve the wave
  equation (`IsZrmNeg.box_eq_zero`, `IsZrmPos.box_eq_zero`; not stated in the source); the momentum
  eigenstates of Adamo p. 32 are z.r.m. fields (`planeWave_isZrmNeg`, `planeWave_isZrmPos`,
  `planeWave_isZrmScalar`).

## References

* T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196: `ε` (1.5)–(1.7), p. 6; §3.1, pp. 23–25: the
  field strength (3.1), its decomposition (3.2), the SD and ASD parts (3.3), (3.4), the Maxwell
  equations and Bianchi identity (3.7)–(3.8), the spin-1 z.r.m. equations (3.10)–(3.11), the
  z.r.m. equations of helicity `h` (3.15); p. 32, Exercise "momentum eigenstates", item 3.

Regularity: Mathlib proves that holomorphic functions are `C^∞` only in one variable, so the
wave-equation theorems assume `C²`.

Difference from the source (sign): Adamo's `ε` is (1.5) for both index positions (`ε^{αβ}` and `ε_{αβ}` are the
same matrix by (1.6)) with "lower to the right, raise to the left" (1.7). Read with these conventions, the parts of (3.3) are
`-asdPart F` and `-sdPart F`, and the right side of (3.2) is `-F`: (3.2)–(3.3) and (3.4) disagree by an overall sign. The parts
here are the ones for which (3.4) holds, `½ ε_{γδ} F_{γα̇δβ̇}` and `½ ε_{γ̇δ̇} F_{αγ̇βδ̇}`. The z.r.m. equations are linear, so
they do not see the sign.
-/

open Matrix

noncomputable section

namespace Lightlike.Spinor

/-- The spinor metric `ε_{αβ}` (Physlib's `Fermion.metricRaw`). -/
abbrev eps : Matrix (Fin 2) (Fin 2) ℂ := Fermion.metricRaw

@[simp] lemma eps_00 : eps 0 0 = 0 := rfl
@[simp] lemma eps_01 : eps 0 1 = 1 := rfl
@[simp] lemma eps_10 : eps 1 0 = -1 := rfl
@[simp] lemma eps_11 : eps 1 1 = 0 := rfl

/-- A bispinor 2-tensor `F_{αα̇ββ̇}`. -/
abbrev Bispinor2 := Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ

/-- `F` is antisymmetric under `(αα̇) ↔ (ββ̇)`: a 2-form. -/
def IsAntisymm (F : Bispinor2) : Prop := ∀ a a' b b', F b b' a a' = -F a a' b b'

/-- A symmetric spinor `φ_{αβ}`. -/
def IsSymm (φ : Fin 2 → Fin 2 → ℂ) : Prop := ∀ a b, φ b a = φ a b

/-- The anti-self-dual part `F_{αβ} = ½ ε_{γ̇δ̇} F_{αγ̇βδ̇}` (Adamo (3.3) up to the overall sign named in the header). -/
def asdPart (F : Bispinor2) : Fin 2 → Fin 2 → ℂ := fun α β =>
  (1 / 2) * ∑ γ, ∑ δ, eps γ δ * F α γ β δ

/-- The self-dual part `F̃_{α̇β̇} = ½ ε_{γδ} F_{γα̇δβ̇}` (Adamo (3.3) up to the overall sign named in the header). -/
def sdPart (F : Bispinor2) : Fin 2 → Fin 2 → ℂ := fun α' β' =>
  (1 / 2) * ∑ γ, ∑ δ, eps γ δ * F γ α' δ β'

/-- The 2-form `ε_{αβ} F̃_{α̇β̇} + ε_{α̇β̇} F_{αβ}` of a pair of spinors (Adamo (3.4)). -/
def ofParts (φ φt : Fin 2 → Fin 2 → ℂ) : Bispinor2 := fun α α' β β' =>
  eps α β * φt α' β' + eps α' β' * φ α β

/-- **The Maxwell spinor decomposition** (Adamo (3.2)–(3.4)). -/
theorem maxwell_decomposition {F : Bispinor2} (hF : IsAntisymm F) :
    F = ofParts (asdPart F) (sdPart F) := by
  have d0 : F 0 0 0 0 = 0 := by have := hF 0 0 0 0; linear_combination this / 2
  have d1 : F 0 1 0 1 = 0 := by have := hF 0 1 0 1; linear_combination this / 2
  have d2 : F 1 0 1 0 = 0 := by have := hF 1 0 1 0; linear_combination this / 2
  have d3 : F 1 1 1 1 = 0 := by have := hF 1 1 1 1; linear_combination this / 2
  have r0 : F 0 1 0 0 = -F 0 0 0 1 := hF 0 0 0 1
  have r1 : F 1 0 0 0 = -F 0 0 1 0 := hF 0 0 1 0
  have r2 : F 1 0 0 1 = -F 0 1 1 0 := hF 0 1 1 0
  have r3 : F 1 1 0 0 = -F 0 0 1 1 := hF 0 0 1 1
  have r4 : F 1 1 0 1 = -F 0 1 1 1 := hF 0 1 1 1
  have r5 : F 1 1 1 0 = -F 1 0 1 1 := hF 1 0 1 1
  funext α α' β β'
  fin_cases α <;> fin_cases α' <;> fin_cases β <;> fin_cases β' <;>
    simp only [ofParts, asdPart, sdPart, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      eps_00, eps_01, eps_10, eps_11, d0, d1, d2, d3, r0, r1, r2, r3, r4, r5] <;> ring

lemma asdPart_symm {F : Bispinor2} (hF : IsAntisymm F) : IsSymm (asdPart F) := by
  intro a b
  simp only [asdPart, Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11]
  rw [hF a 0 b 1, hF a 1 b 0]
  ring

lemma sdPart_symm {F : Bispinor2} (hF : IsAntisymm F) : IsSymm (sdPart F) := by
  intro a b
  simp only [sdPart, Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11]
  rw [hF 0 a 1 b, hF 1 a 0 b]
  ring

lemma ofParts_antisymm {φ φt : Fin 2 → Fin 2 → ℂ} (hφ : IsSymm φ) (hφt : IsSymm φt) :
    IsAntisymm (ofParts φ φt) := by
  intro a a' b b'
  simp only [ofParts]
  rw [hφ b a, hφt b' a']
  have e1 : eps b a = -eps a b := by fin_cases a <;> fin_cases b <;> simp
  have e2 : eps b' a' = -eps a' b' := by fin_cases a' <;> fin_cases b' <;> simp
  rw [e1, e2]; ring

/-- **The parts of `ε F̃ + ε̄ F` are `F` and `F̃`** for symmetric spinors. -/
theorem parts_ofParts {φ φt : Fin 2 → Fin 2 → ℂ} (hφ : IsSymm φ) (hφt : IsSymm φt) :
    asdPart (ofParts φ φt) = φ ∧ sdPart (ofParts φ φt) = φt := by
  have s1 := hφ 0 1
  have s2 := hφt 0 1
  constructor
  · funext a b
    fin_cases a <;> fin_cases b <;>
      simp only [asdPart, ofParts, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, eps_00,
        eps_01, eps_10, eps_11, s1, s2] <;> ring
  · funext a b
    fin_cases a <;> fin_cases b <;>
      simp only [sdPart, ofParts, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, eps_00,
        eps_01, eps_10, eps_11, s1, s2] <;> ring

/-- **2-forms are pairs of symmetric spinors**: the Maxwell decomposition as an equivalence. -/
def maxwellEquiv : {F : Bispinor2 // IsAntisymm F} ≃
    {φ : Fin 2 → Fin 2 → ℂ // IsSymm φ} × {φt : Fin 2 → Fin 2 → ℂ // IsSymm φt} where
  toFun F := (⟨asdPart F.1, asdPart_symm F.2⟩, ⟨sdPart F.1, sdPart_symm F.2⟩)
  invFun p := ⟨ofParts p.1.1 p.2.1, ofParts_antisymm p.1.2 p.2.2⟩
  left_inv F := Subtype.ext (maxwell_decomposition F.2).symm
  right_inv p := by
    obtain ⟨h1, h2⟩ := parts_ofParts p.1.2 p.2.2
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

/-! ## Maxwell's equations and the spin-1 zero-rest-mass equations, pointwise

`D c c' = ∂_{cc'} F` is the derivative of a 2-form field at a point, antisymmetric in its last two
index pairs. The certificates below were generated by a linear-algebra computation (sympy); the
closed and divergence equations and the two spin-1 z.r.m. systems span the same space modulo the
antisymmetry. -/

/-- The derivative `D c c' = ∂_{cc'} F` of a 2-form field at a point. -/
abbrev DerivTensor := Fin 2 → Fin 2 → Bispinor2

/-- `dF = 0`: `∂_a F_{bc} + ∂_b F_{ca} + ∂_c F_{ab} = 0`. -/
def ClosedD (D : DerivTensor) : Prop :=
  ∀ a a' b b' c c', D a a' b b' c c' + D b b' c c' a a' + D c c' a a' b b' = 0

/-- `∂^a F_{ab} = 0`, with `η^{ac} ↔ ε^{αγ} ε^{α̇γ̇}`. -/
def DivFreeD (D : DerivTensor) : Prop :=
  ∀ b b', ∑ a, ∑ a', ∑ c, ∑ c', eps a c * eps a' c' * D c c' a a' b b' = 0

/-- The negative helicity spin-1 z.r.m. equation `∂^{αβ̇} F_{αβ} = 0` on the ASD part (Adamo (3.11)). -/
def ZrmASDD (D : DerivTensor) : Prop :=
  ∀ β δ', ∑ α, ∑ γ, eps α γ * asdPart (D γ δ') α β = 0

/-- The positive helicity spin-1 z.r.m. equation `∂^{βα̇} F̃_{α̇β̇} = 0` on the SD part (Adamo (3.10)). -/
def ZrmSDD (D : DerivTensor) : Prop :=
  ∀ β β', ∑ α', ∑ γ', eps α' γ' * sdPart (D β γ') α' β' = 0

set_option maxHeartbeats 1600000 in
/-- **Maxwell's equations are the two spin-1 zero-rest-mass equations** (Adamo (3.7)–(3.11)), pointwise:
`dF = 0` and `∂^a F_{ab} = 0` hold iff the ASD and SD parts satisfy the z.r.m. equations. -/
theorem maxwell_iff_zrm_D {D : DerivTensor} (hD : ∀ c c', IsAntisymm (D c c')) :
    ClosedD D ∧ DivFreeD D ↔ ZrmASDD D ∧ ZrmSDD D := by
  have hD' : ∀ c c' a a' b b', D c c' b b' a a' = -D c c' a a' b b' := fun c c' => hD c c'
  constructor
  · rintro ⟨hc, hd⟩
    simp only [DivFreeD, Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11] at hd
    refine ⟨fun β δ' => ?_, fun β β' => ?_⟩
    · fin_cases β <;> fin_cases δ' <;> simp only [asdPart, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, eps_00, eps_01, eps_10, eps_11]
      · linear_combination (-1/2) * hc 0 0 0 0 1 1 + (1/2) * hc 0 0 0 1 1 0 + (1/2) * hd 0 0 +
            (1/2) * hD' 0 0 0 0 1 1 + (-1/2) * hD' 0 0 0 1 1 0
      · linear_combination (-1/2) * hc 0 0 1 1 0 1 + (1/2) * hc 0 1 0 1 1 0 + (1/2) * hd 0 1 +
            (1/2) * hD' 0 1 0 0 1 1 + (-1/2) * hD' 0 1 0 1 1 0
      · linear_combination (-1/2) * hc 0 0 1 0 1 1 + (1/2) * hd 1 0 + (1/4) * hD' 0 1 1 0 1 0 +
            (1/2) * hD' 1 0 0 0 1 1
      · linear_combination (-1/2) * hc 0 1 1 0 1 1 + (1/2) * hd 1 1 + (-1/4) * hD' 0 0 1 1 1 1 +
            (1/2) * hD' 0 1 1 0 1 1 + (1/2) * hD' 1 0 0 1 1 1
    · fin_cases β <;> fin_cases β' <;> simp only [sdPart, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, eps_00, eps_01, eps_10, eps_11]
      · linear_combination (-1/2) * hc 0 0 0 0 1 1 + (1/2) * hc 0 0 1 0 0 1 + (1/2) * hd 0 0 +
            (1/2) * hD' 0 0 0 0 1 1 + (-1/2) * hD' 0 0 0 1 1 0
      · linear_combination (-1/2) * hc 0 0 0 1 1 1 + (1/2) * hc 0 1 0 1 1 0 + (1/2) * hd 0 1 +
            (1/2) * hD' 0 1 0 0 1 1 + (-1/2) * hD' 0 1 0 1 1 0
      · linear_combination (-1/2) * hc 0 0 1 1 1 0 + (1/2) * hd 1 0 + (1/4) * hD' 0 1 1 0 1 0 +
            (1/2) * hD' 1 0 0 0 1 1
      · linear_combination (-1/2) * hc 0 1 1 1 1 0 + (1/2) * hd 1 1 + (-1/4) * hD' 0 0 1 1 1 1 +
            (1/2) * hD' 0 1 1 0 1 1 + (1/2) * hD' 1 0 0 1 1 1
  · rintro ⟨hA, hS⟩
    simp only [ZrmASDD, ZrmSDD, asdPart, sdPart, Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11] at hA hS
    refine ⟨fun a a' b b' c c' => ?_, fun b b' => ?_⟩
    · fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;> fin_cases c <;> fin_cases c' <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
      · linear_combination (3/2) * hD' 0 0 0 0 0 0
      · linear_combination hD' 0 0 0 0 0 1 + (1/2) * hD' 0 1 0 0 0 0
      · linear_combination hD' 0 0 0 0 1 0 + (1/2) * hD' 1 0 0 0 0 0
      · linear_combination hD' 0 0 0 0 1 1 + (1/2) * hD' 1 1 0 0 0 0
      · linear_combination hD' 0 0 0 0 0 1 + (1/2) * hD' 0 1 0 0 0 0
      · linear_combination (1/2) * hD' 0 0 0 1 0 1 + hD' 0 1 0 0 0 1
      · linear_combination hA 0 0 + (-1) * hS 0 0 + (1/2) * hD' 0 0 0 1 1 0 +
            (1/2) * hD' 0 1 0 0 1 0 + (1/2) * hD' 1 0 0 0 0 1
      · linear_combination hA 0 1 + (-1) * hS 0 1 + (1/2) * hD' 0 0 0 1 1 1 +
            (1/2) * hD' 0 1 0 0 1 1 + (1/2) * hD' 1 1 0 0 0 1
      · linear_combination hD' 0 0 0 0 1 0 + (1/2) * hD' 1 0 0 0 0 0
      · linear_combination (-1) * hA 0 0 + hS 0 0 + (1/2) * hD' 0 0 0 1 1 0 +
            (1/2) * hD' 0 1 0 0 1 0 + (1/2) * hD' 1 0 0 0 0 1
      · linear_combination (1/2) * hD' 0 0 1 0 1 0 + hD' 1 0 0 0 1 0
      · linear_combination (-1) * hA 1 0 + hS 1 0 + (1/2) * hD' 0 0 1 0 1 1 +
            (1/2) * hD' 1 0 0 0 1 1 + (1/2) * hD' 1 1 0 0 1 0
      · linear_combination hD' 0 0 0 0 1 1 + (1/2) * hD' 1 1 0 0 0 0
      · linear_combination (-1) * hA 0 1 + hS 0 1 + (1/2) * hD' 0 0 0 1 1 1 +
            (1/2) * hD' 0 1 0 0 1 1 + (1/2) * hD' 1 1 0 0 0 1
      · linear_combination hA 1 0 + (-1) * hS 1 0 + (1/2) * hD' 0 0 1 0 1 1 +
            (1/2) * hD' 1 0 0 0 1 1 + (1/2) * hD' 1 1 0 0 1 0
      · linear_combination (1/2) * hD' 0 0 1 1 1 1 + hD' 1 1 0 0 1 1
      · linear_combination hD' 0 0 0 0 0 1 + (1/2) * hD' 0 1 0 0 0 0
      · linear_combination (1/2) * hD' 0 0 0 1 0 1 + hD' 0 1 0 0 0 1
      · linear_combination (-1) * hA 0 0 + hS 0 0 + (1/2) * hD' 0 0 0 1 1 0 +
            (1/2) * hD' 0 1 0 0 1 0 + (1/2) * hD' 1 0 0 0 0 1
      · linear_combination (-1) * hA 0 1 + hS 0 1 + (1/2) * hD' 0 0 0 1 1 1 +
            (1/2) * hD' 0 1 0 0 1 1 + (1/2) * hD' 1 1 0 0 0 1
      · linear_combination (1/2) * hD' 0 0 0 1 0 1 + hD' 0 1 0 0 0 1
      · linear_combination (3/2) * hD' 0 1 0 1 0 1
      · linear_combination hD' 0 1 0 1 1 0 + (1/2) * hD' 1 0 0 1 0 1
      · linear_combination hD' 0 1 0 1 1 1 + (1/2) * hD' 1 1 0 1 0 1
      · linear_combination hA 0 0 + (-1) * hS 0 0 + (1/2) * hD' 0 0 0 1 1 0 +
            (1/2) * hD' 0 1 0 0 1 0 + (1/2) * hD' 1 0 0 0 0 1
      · linear_combination hD' 0 1 0 1 1 0 + (1/2) * hD' 1 0 0 1 0 1
      · linear_combination (1/2) * hD' 0 1 1 0 1 0 + hD' 1 0 0 1 1 0
      · linear_combination (-1) * hA 1 1 + hS 1 1 + (1/2) * hD' 0 1 1 0 1 1 +
            (1/2) * hD' 1 0 0 1 1 1 + (1/2) * hD' 1 1 0 1 1 0
      · linear_combination hA 0 1 + (-1) * hS 0 1 + (1/2) * hD' 0 0 0 1 1 1 +
            (1/2) * hD' 0 1 0 0 1 1 + (1/2) * hD' 1 1 0 0 0 1
      · linear_combination hD' 0 1 0 1 1 1 + (1/2) * hD' 1 1 0 1 0 1
      · linear_combination hA 1 1 + (-1) * hS 1 1 + (1/2) * hD' 0 1 1 0 1 1 +
            (1/2) * hD' 1 0 0 1 1 1 + (1/2) * hD' 1 1 0 1 1 0
      · linear_combination (1/2) * hD' 0 1 1 1 1 1 + hD' 1 1 0 1 1 1
      · linear_combination hD' 0 0 0 0 1 0 + (1/2) * hD' 1 0 0 0 0 0
      · linear_combination hA 0 0 + (-1) * hS 0 0 + (1/2) * hD' 0 0 0 1 1 0 +
            (1/2) * hD' 0 1 0 0 1 0 + (1/2) * hD' 1 0 0 0 0 1
      · linear_combination (1/2) * hD' 0 0 1 0 1 0 + hD' 1 0 0 0 1 0
      · linear_combination hA 1 0 + (-1) * hS 1 0 + (1/2) * hD' 0 0 1 0 1 1 +
            (1/2) * hD' 1 0 0 0 1 1 + (1/2) * hD' 1 1 0 0 1 0
      · linear_combination (-1) * hA 0 0 + hS 0 0 + (1/2) * hD' 0 0 0 1 1 0 +
            (1/2) * hD' 0 1 0 0 1 0 + (1/2) * hD' 1 0 0 0 0 1
      · linear_combination hD' 0 1 0 1 1 0 + (1/2) * hD' 1 0 0 1 0 1
      · linear_combination (1/2) * hD' 0 1 1 0 1 0 + hD' 1 0 0 1 1 0
      · linear_combination hA 1 1 + (-1) * hS 1 1 + (1/2) * hD' 0 1 1 0 1 1 +
            (1/2) * hD' 1 0 0 1 1 1 + (1/2) * hD' 1 1 0 1 1 0
      · linear_combination (1/2) * hD' 0 0 1 0 1 0 + hD' 1 0 0 0 1 0
      · linear_combination (1/2) * hD' 0 1 1 0 1 0 + hD' 1 0 0 1 1 0
      · linear_combination (3/2) * hD' 1 0 1 0 1 0
      · linear_combination hD' 1 0 1 0 1 1 + (1/2) * hD' 1 1 1 0 1 0
      · linear_combination (-1) * hA 1 0 + hS 1 0 + (1/2) * hD' 0 0 1 0 1 1 +
            (1/2) * hD' 1 0 0 0 1 1 + (1/2) * hD' 1 1 0 0 1 0
      · linear_combination (-1) * hA 1 1 + hS 1 1 + (1/2) * hD' 0 1 1 0 1 1 +
            (1/2) * hD' 1 0 0 1 1 1 + (1/2) * hD' 1 1 0 1 1 0
      · linear_combination hD' 1 0 1 0 1 1 + (1/2) * hD' 1 1 1 0 1 0
      · linear_combination (1/2) * hD' 1 0 1 1 1 1 + hD' 1 1 1 0 1 1
      · linear_combination hD' 0 0 0 0 1 1 + (1/2) * hD' 1 1 0 0 0 0
      · linear_combination hA 0 1 + (-1) * hS 0 1 + (1/2) * hD' 0 0 0 1 1 1 +
            (1/2) * hD' 0 1 0 0 1 1 + (1/2) * hD' 1 1 0 0 0 1
      · linear_combination (-1) * hA 1 0 + hS 1 0 + (1/2) * hD' 0 0 1 0 1 1 +
            (1/2) * hD' 1 0 0 0 1 1 + (1/2) * hD' 1 1 0 0 1 0
      · linear_combination (1/2) * hD' 0 0 1 1 1 1 + hD' 1 1 0 0 1 1
      · linear_combination (-1) * hA 0 1 + hS 0 1 + (1/2) * hD' 0 0 0 1 1 1 +
            (1/2) * hD' 0 1 0 0 1 1 + (1/2) * hD' 1 1 0 0 0 1
      · linear_combination hD' 0 1 0 1 1 1 + (1/2) * hD' 1 1 0 1 0 1
      · linear_combination (-1) * hA 1 1 + hS 1 1 + (1/2) * hD' 0 1 1 0 1 1 +
            (1/2) * hD' 1 0 0 1 1 1 + (1/2) * hD' 1 1 0 1 1 0
      · linear_combination (1/2) * hD' 0 1 1 1 1 1 + hD' 1 1 0 1 1 1
      · linear_combination hA 1 0 + (-1) * hS 1 0 + (1/2) * hD' 0 0 1 0 1 1 +
            (1/2) * hD' 1 0 0 0 1 1 + (1/2) * hD' 1 1 0 0 1 0
      · linear_combination hA 1 1 + (-1) * hS 1 1 + (1/2) * hD' 0 1 1 0 1 1 +
            (1/2) * hD' 1 0 0 1 1 1 + (1/2) * hD' 1 1 0 1 1 0
      · linear_combination hD' 1 0 1 0 1 1 + (1/2) * hD' 1 1 1 0 1 0
      · linear_combination (1/2) * hD' 1 0 1 1 1 1 + hD' 1 1 1 0 1 1
      · linear_combination (1/2) * hD' 0 0 1 1 1 1 + hD' 1 1 0 0 1 1
      · linear_combination (1/2) * hD' 0 1 1 1 1 1 + hD' 1 1 0 1 1 1
      · linear_combination (1/2) * hD' 1 0 1 1 1 1 + hD' 1 1 1 0 1 1
      · linear_combination (3/2) * hD' 1 1 1 1 1 1
    · fin_cases b <;> fin_cases b' <;> simp only [Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, eps_00, eps_01, eps_10, eps_11]
      · linear_combination hA 0 0 + hS 0 0 + (1/2) * hD' 0 0 0 1 1 0 + (-1/2) * hD' 0 1 0 0 1 0 +
            (-1/2) * hD' 1 0 0 0 0 1 + (1/2) * hD' 1 1 0 0 0 0
      · linear_combination hA 0 1 + hS 0 1 + (1/2) * hD' 0 0 0 1 1 1 + (-1/2) * hD' 0 1 0 0 1 1 +
            (-1/2) * hD' 1 0 0 1 0 1 + (1/2) * hD' 1 1 0 0 0 1
      · linear_combination hA 1 0 + hS 1 0 + (1/2) * hD' 0 0 1 0 1 1 + (-1/2) * hD' 0 1 1 0 1 0 +
            (-1/2) * hD' 1 0 0 0 1 1 + (1/2) * hD' 1 1 0 0 1 0
      · linear_combination hA 1 1 + hS 1 1 + (1/2) * hD' 0 0 1 1 1 1 + (-1/2) * hD' 0 1 1 0 1 1 +
            (-1/2) * hD' 1 0 0 1 1 1 + (1/2) * hD' 1 1 0 1 1 0

/-! ## Zero-rest-mass fields

Fields are functions of the coordinates `x^{αα̇}` of complexified Minkowski space (Adamo (1.2)),
`∂_{αα̇} = ∂/∂x^{αα̇}` is the holomorphic partial derivative, and indices are raised with `ε`
(Adamo (1.5)–(1.7)): `∂^{αα̇} = ε^{αβ} ε^{α̇β̇} ∂_{ββ̇}`. A field with `n + 1` spinor indices is a
family `φ i` indexed by `i : Fin (n + 1) → Fin 2`. -/

/-- The coordinates `x^{αα̇}` of complexified Minkowski space. -/
abbrev SpinorCoord := Fin 2 → Fin 2 → ℂ

/-- The coordinate vector of `x^{αα̇}`. -/
def coordVec (α α' : Fin 2) : SpinorCoord := Pi.single α (Pi.single α' 1)

/-- The holomorphic partial derivative `∂_{αα̇} f = ∂f/∂x^{αα̇}`. -/
def pd (f : SpinorCoord → ℂ) (α α' : Fin 2) (x : SpinorCoord) : ℂ :=
  fderiv ℂ f x (coordVec α α')

/-- The wave operator `□ Φ = ∂^{αα̇} ∂_{αα̇} Φ = ε^{αβ} ε^{α̇β̇} ∂_{ββ̇} ∂_{αα̇} Φ` (Adamo (3.15)). -/
def box (f : SpinorCoord → ℂ) (x : SpinorCoord) : ℂ :=
  ∑ α, ∑ β, ∑ α', ∑ β', eps α β * eps α' β' * pd (pd f α α') β β' x

/-- A field with `n + 1` totally symmetric spinor indices. -/
def IsSymmField (n : ℕ) (φ : (Fin (n + 1) → Fin 2) → SpinorCoord → ℂ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1) → Fin 2), φ (i ∘ σ) = φ i

/-- **A z.r.m. field of helicity `-(n + 1)/2`** on `U` (Adamo (3.15), `h < 0`): totally symmetric
undotted `φ_{α₁⋯α_{n+1}}` with `∂^{α₁β̇} φ_{α₁α₂⋯α_{n+1}} = 0`. -/
structure IsZrmNeg (n : ℕ) (U : Set SpinorCoord) (φ : (Fin (n + 1) → Fin 2) → SpinorCoord → ℂ) :
    Prop where
  symm : IsSymmField n φ
  eqn : ∀ (β' : Fin 2) (i : Fin n → Fin 2), ∀ x ∈ U,
    ∑ α, ∑ γ, ∑ δ', eps α γ * eps β' δ' * pd (φ (Fin.cons α i)) γ δ' x = 0

/-- **A z.r.m. field of helicity `(n + 1)/2`** on `U` (Adamo (3.15), `h > 0`): totally symmetric
dotted `φ̃_{α̇₁⋯α̇_{n+1}}` with `∂^{βα̇₁} φ̃_{α̇₁α̇₂⋯α̇_{n+1}} = 0`. -/
structure IsZrmPos (n : ℕ) (U : Set SpinorCoord) (φ : (Fin (n + 1) → Fin 2) → SpinorCoord → ℂ) :
    Prop where
  symm : IsSymmField n φ
  eqn : ∀ (β : Fin 2) (i : Fin n → Fin 2), ∀ x ∈ U,
    ∑ α', ∑ γ, ∑ δ', eps β γ * eps α' δ' * pd (φ (Fin.cons α' i)) γ δ' x = 0

/-- **A z.r.m. field of helicity `0`** on `U` (Adamo (3.15), `h = 0`): `□ Φ = 0`. -/
def IsZrmScalar (U : Set SpinorCoord) (Φ : SpinorCoord → ℂ) : Prop := ∀ x ∈ U, box Φ x = 0

lemma sum_eps_mul_eq_zero_iff (X : Fin 2 → ℂ) : (∀ β', ∑ δ', eps β' δ' * X δ' = 0) ↔ ∀ δ', X δ' = 0 := by
  simp only [Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11, Fin.forall_fin_two]
  constructor
  · rintro ⟨h0, h1⟩; exact ⟨by linear_combination -h1, by linear_combination h0⟩
  · rintro ⟨h0, h1⟩; constructor <;> simp [h0, h1]

/-- The algebraic core of the wave equation: if `H α b b' c c'` is symmetric in `(bb') ↔ (cc')` and
`ε^{αγ} H α β β' γ δ' = 0`, then `ε^{bc} ε^{b'c'} H β b b' c c' = 0`. Certificate found by a linear
solve (sympy). -/
lemma wave_algebra (H : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ)
    (hs : ∀ a b b' c c', H a b b' c c' = H a c c' b b')
    (hz : ∀ δ' β β', ∑ α, ∑ γ, eps α γ * H α β β' γ δ' = 0) (β : Fin 2) :
    ∑ b, ∑ c, ∑ b', ∑ c', eps b c * eps b' c' * H β b b' c c' = 0 := by
  fin_cases β <;>
    simp only [Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, eps_00, eps_01, eps_10,
      eps_11] at hz ⊢
  · linear_combination (-1) * hs 0 0 0 1 1 + hs 0 0 1 1 0 + 2 * hs 1 0 0 0 1 + (-2) * hz 0 0 1 +
      2 * hz 1 0 0
  · linear_combination (-2) * hs 0 1 0 1 1 + hs 1 0 0 1 1 + (-1) * hs 1 0 1 1 0 + (-2) * hz 0 1 1 +
      2 * hz 1 1 0

lemma pd_sum_mul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → SpinorCoord → ℂ) {x : SpinorCoord}
    (hf : ∀ i ∈ s, DifferentiableAt ℂ (f i) x) (α α' : Fin 2) :
    pd (fun y => ∑ i ∈ s, c i * f i y) α α' x = ∑ i ∈ s, c i * pd (f i) α α' x := by
  have h : HasFDerivAt (fun y => ∑ i ∈ s, c i * f i y) (∑ i ∈ s, c i • fderiv ℂ (f i) x) x :=
    HasFDerivAt.fun_sum fun i hi => (hf i hi).hasFDerivAt.const_mul (c i)
  rw [pd, h.fderiv]
  simp [pd]

lemma differentiableAt_pd {f : SpinorCoord → ℂ} {x : SpinorCoord} (hf : ContDiffAt ℂ 2 f x)
    (α α' : Fin 2) : DifferentiableAt ℂ (pd f α α') x := by
  show DifferentiableAt ℂ (fun y => fderiv ℂ f y (coordVec α α')) x
  have h1 : DifferentiableAt ℂ (fderiv ℂ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact h1.clm_apply (differentiableAt_const _)

/-- `∂_{ββ̇} ∂_{γδ̇} f` is the second derivative on the two coordinate vectors. -/
lemma pd_pd {f : SpinorCoord → ℂ} {x : SpinorCoord} (hf : ContDiffAt ℂ 2 f x) (γ δ' β β' : Fin 2) :
    pd (pd f γ δ') β β' x = fderiv ℂ (fderiv ℂ f) x (coordVec β β') (coordVec γ δ') := by
  have h1 : DifferentiableAt ℂ (fderiv ℂ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have := fderiv_clm_apply h1 (differentiableAt_const (coordVec γ δ'))
  show fderiv ℂ (fun y => fderiv ℂ f y (coordVec γ δ')) x (coordVec β β') = _
  rw [this]
  simp

/-- The negative helicity components on the open set `U`, `C²`, satisfy the wave equation. -/
theorem IsZrmNeg.box_eq_zero {n : ℕ} {U : Set SpinorCoord} (hU : IsOpen U)
    {φ : (Fin (n + 1) → Fin 2) → SpinorCoord → ℂ} (hφ : IsZrmNeg n U φ)
    (hreg : ∀ i, ContDiffOn ℂ 2 (φ i) U) (i : Fin (n + 1) → Fin 2) : IsZrmScalar U (φ i) := by
  intro x hx
  rw [← Fin.cons_self_tail i]
  set j := Fin.tail i
  have hc : ∀ α, ContDiffAt ℂ 2 (φ (Fin.cons α j)) x := fun α =>
    (hreg _).contDiffAt (hU.mem_nhds hx)
  -- the z.r.m. equation with the dotted index lowered, near `x`
  have hz0 : ∀ δ', ∀ y ∈ U, ∑ α, ∑ γ, eps α γ * pd (φ (Fin.cons α j)) γ δ' y = 0 := by
    intro δ' y hy
    have := (sum_eps_mul_eq_zero_iff (fun δ' => ∑ α, ∑ γ, eps α γ * pd (φ (Fin.cons α j)) γ δ' y)).1
      (fun β' => by
        have h := hφ.eqn β' j y hy
        simp only [Fin.sum_univ_two] at h ⊢
        linear_combination h) δ'
    exact this
  set H : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ := fun α b b' c c' =>
    fderiv ℂ (fderiv ℂ (φ (Fin.cons α j))) x (coordVec b b') (coordVec c c') with hH
  have hpp : ∀ α γ δ' β β', pd (pd (φ (Fin.cons α j)) γ δ') β β' x = H α β β' γ δ' :=
    fun α γ δ' β β' => pd_pd (hc α) γ δ' β β'
  have hs : ∀ a b b' c c', H a b b' c c' = H a c c' b b' := fun a b b' c c' =>
    (hc a).isSymmSndFDerivAt (by simp) _ _
  have hz : ∀ δ' β β', ∑ α, ∑ γ, eps α γ * H α β β' γ δ' = 0 := by
    intro δ' β β'
    have hev : (fun y => ∑ α, ∑ γ, eps α γ * pd (φ (Fin.cons α j)) γ δ' y) =ᶠ[nhds x] fun _ => 0 :=
      Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hz0 δ' y hy
    have h0 : pd (fun y => ∑ α, ∑ γ, eps α γ * pd (φ (Fin.cons α j)) γ δ' y) β β' x = 0 := by
      rw [pd, hev.fderiv_eq]
      simp
    have hsplit : (fun y => ∑ α, ∑ γ, eps α γ * pd (φ (Fin.cons α j)) γ δ' y) =
        fun y => ∑ p : Fin 2 × Fin 2, eps p.1 p.2 * pd (φ (Fin.cons p.1 j)) p.2 δ' y := by
      funext y; simp only [Fintype.sum_prod_type]
    rw [hsplit, pd_sum_mul _ _ _ (fun p _ => differentiableAt_pd (hc p.1) _ _)] at h0
    simpa only [Fintype.sum_prod_type, hpp] using h0
  have hw := wave_algebra H hs hz (i 0)
  simp only [box, hpp]
  simp only [Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11] at hw ⊢
  linear_combination hw

/-- The positive helicity components on the open set `U`, `C²`, satisfy the wave equation. -/
theorem IsZrmPos.box_eq_zero {n : ℕ} {U : Set SpinorCoord} (hU : IsOpen U)
    {φ : (Fin (n + 1) → Fin 2) → SpinorCoord → ℂ} (hφ : IsZrmPos n U φ)
    (hreg : ∀ i, ContDiffOn ℂ 2 (φ i) U) (i : Fin (n + 1) → Fin 2) : IsZrmScalar U (φ i) := by
  intro x hx
  rw [← Fin.cons_self_tail i]
  set j := Fin.tail i
  have hc : ∀ α, ContDiffAt ℂ 2 (φ (Fin.cons α j)) x := fun α =>
    (hreg _).contDiffAt (hU.mem_nhds hx)
  have hz0 : ∀ γ, ∀ y ∈ U, ∑ α', ∑ δ', eps α' δ' * pd (φ (Fin.cons α' j)) γ δ' y = 0 := by
    intro γ y hy
    exact (sum_eps_mul_eq_zero_iff (fun γ => ∑ α', ∑ δ', eps α' δ' * pd (φ (Fin.cons α' j)) γ δ' y)).1
      (fun β => by
        have h := hφ.eqn β j y hy
        simp only [Fin.sum_univ_two] at h ⊢
        linear_combination h) γ
  -- `G α b b' c c'` is the second derivative with undotted and dotted slots exchanged
  set G : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ := fun α b b' c c' =>
    fderiv ℂ (fderiv ℂ (φ (Fin.cons α j))) x (coordVec b' b) (coordVec c' c) with hG
  have hpp : ∀ α γ δ' β β', pd (pd (φ (Fin.cons α j)) γ δ') β β' x = G α β' β δ' γ :=
    fun α γ δ' β β' => pd_pd (hc α) γ δ' β β'
  have hs : ∀ a b b' c c', G a b b' c c' = G a c c' b b' := fun a b b' c c' =>
    (hc a).isSymmSndFDerivAt (by simp) _ _
  have hz : ∀ δ' β β', ∑ α, ∑ γ, eps α γ * G α β β' γ δ' = 0 := by
    intro γ β' β
    have hev : (fun y => ∑ α', ∑ δ', eps α' δ' * pd (φ (Fin.cons α' j)) γ δ' y) =ᶠ[nhds x]
        fun _ => 0 := Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hz0 γ y hy
    have h0 : pd (fun y => ∑ α', ∑ δ', eps α' δ' * pd (φ (Fin.cons α' j)) γ δ' y) β β' x = 0 := by
      rw [pd, hev.fderiv_eq]
      simp
    have hsplit : (fun y => ∑ α', ∑ δ', eps α' δ' * pd (φ (Fin.cons α' j)) γ δ' y) =
        fun y => ∑ p : Fin 2 × Fin 2, eps p.1 p.2 * pd (φ (Fin.cons p.1 j)) γ p.2 y := by
      funext y; simp only [Fintype.sum_prod_type]
    rw [hsplit, pd_sum_mul _ _ _ (fun p _ => differentiableAt_pd (hc p.1) _ _)] at h0
    simpa only [Fintype.sum_prod_type, hpp] using h0
  have hw := wave_algebra G hs hz (i 0)
  simp only [box, hpp]
  simp only [Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11] at hw ⊢
  linear_combination hw

/-! ### Momentum eigenstates (Adamo p. 32, Exercise "momentum eigenstates", item 3) -/

/-- The linear form `x ↦ k_{αα̇} x^{αα̇}` of `k_{αα̇} = p_α p̃_α̇`. -/
def kForm (p pt : Fin 2 → ℂ) : SpinorCoord →L[ℂ] ℂ :=
  ∑ α, ∑ α', (p α * pt α') • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) α').comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => Fin 2 → ℂ) α))

lemma kForm_apply (p pt : Fin 2 → ℂ) (x : SpinorCoord) :
    kForm p pt x = ∑ α, ∑ α', p α * pt α' * x α α' := by
  simp [kForm]

lemma kForm_coordVec (p pt : Fin 2 → ℂ) (γ δ' : Fin 2) : kForm p pt (coordVec γ δ') = p γ * pt δ' := by
  rw [kForm_apply]
  fin_cases γ <;> fin_cases δ' <;> simp [coordVec, Fin.sum_univ_two, Pi.single_apply]

/-- The plane wave `e^{i k·x}`, `k_{αα̇} = p_α p̃_α̇`. -/
def planeWave (p pt : Fin 2 → ℂ) (x : SpinorCoord) : ℂ := Complex.exp (Complex.I * kForm p pt x)

lemma hasFDerivAt_planeWave (p pt : Fin 2 → ℂ) (x : SpinorCoord) :
    HasFDerivAt (planeWave p pt) (planeWave p pt x • (Complex.I • kForm p pt)) x :=
  ((kForm p pt).hasFDerivAt.const_mul Complex.I).cexp

lemma pd_const_mul_planeWave (c : ℂ) (p pt : Fin 2 → ℂ) (γ δ' : Fin 2) :
    pd (fun x => c * planeWave p pt x) γ δ' =
      fun x => c * (Complex.I * (p γ * pt δ')) * planeWave p pt x := by
  funext x
  rw [pd, ((hasFDerivAt_planeWave p pt x).const_mul c).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, kForm_coordVec]
  ring

/-- **Momentum eigenstates of negative helicity**: `p_{α₁} ⋯ p_{α_{n+1}} e^{i k·x}` is a z.r.m. field of
helicity `-(n + 1)/2` (Adamo p. 32). -/
theorem planeWave_isZrmNeg (n : ℕ) (p pt : Fin 2 → ℂ) :
    IsZrmNeg n Set.univ (fun i x => (∏ k, p (i k)) * planeWave p pt x) where
  symm σ i := by
    funext x
    simp only [Function.comp_apply]
    rw [Equiv.prod_comp σ (fun k => p (i k))]
  eqn β' i x _ := by
    simp only [pd_const_mul_planeWave, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11]
    ring

/-- **Momentum eigenstates of positive helicity**: `p̃_{α̇₁} ⋯ p̃_{α̇_{n+1}} e^{i k·x}` (Adamo p. 32). -/
theorem planeWave_isZrmPos (n : ℕ) (p pt : Fin 2 → ℂ) :
    IsZrmPos n Set.univ (fun i x => (∏ k, pt (i k)) * planeWave p pt x) where
  symm σ i := by
    funext x
    simp only [Function.comp_apply]
    rw [Equiv.prod_comp σ (fun k => pt (i k))]
  eqn β i x _ := by
    simp only [pd_const_mul_planeWave, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11]
    ring

/-- **The helicity-0 momentum eigenstate** `e^{i k·x}` solves the wave equation (Adamo p. 32). -/
theorem planeWave_isZrmScalar (p pt : Fin 2 → ℂ) : IsZrmScalar Set.univ (planeWave p pt) := by
  intro x _
  have h1 : ∀ α α', pd (planeWave p pt) α α' = fun x => Complex.I * (p α * pt α') * planeWave p pt x := by
    intro α α'
    have := pd_const_mul_planeWave 1 p pt α α'
    simp only [one_mul] at this
    exact this
  simp only [box, h1, pd_const_mul_planeWave, Fin.sum_univ_two, eps_00, eps_01, eps_10, eps_11]
  ring

/-! ### Maxwell fields -/

/-- A 2-form field `F_{αα̇ββ̇}(x)`. -/
abbrev FormField := Fin 2 → Fin 2 → Fin 2 → Fin 2 → SpinorCoord → ℂ

/-- The value of a 2-form field at `x`. -/
def FormField.at (F : FormField) (x : SpinorCoord) : Bispinor2 := fun a a' b b' => F a a' b b' x

/-- `D c c' a a' b b' = ∂_{cc'} F_{aa'bb'}(x)`. -/
def FormField.deriv (F : FormField) (x : SpinorCoord) : DerivTensor :=
  fun c c' a a' b b' => pd (F a a' b b') c c' x

/-- The ASD part `F_{αβ}(x)`, as a field with two undotted indices. -/
def FormField.asd (F : FormField) : (Fin 2 → Fin 2) → SpinorCoord → ℂ :=
  fun i x => asdPart (F.at x) (i 0) (i 1)

/-- The SD part `F̃_{α̇β̇}(x)`, as a field with two dotted indices. -/
def FormField.sd (F : FormField) : (Fin 2 → Fin 2) → SpinorCoord → ℂ :=
  fun i x => sdPart (F.at x) (i 0) (i 1)

lemma isSymmField_one {φ : (Fin 2 → Fin 2) → SpinorCoord → ℂ}
    (h : ∀ a b, φ ![b, a] = φ ![a, b]) : IsSymmField 1 φ := by
  intro σ i
  have hi : ∀ j : Fin 2 → Fin 2, j = ![j 0, j 1] := fun j => by
    funext k; fin_cases k <;> rfl
  have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  rw [hi (i ∘ σ), hi i]
  simp only [Function.comp_apply]
  generalize σ 0 = u, σ 1 = v at h01
  fin_cases u <;> fin_cases v
  · exact absurd rfl h01
  · rfl
  · exact h (i 0) (i 1)
  · exact absurd rfl h01

lemma pd_neg (f : SpinorCoord → ℂ) (c c' : Fin 2) : pd (fun y => -f y) c c' = fun x => -pd f c c' x := by
  funext x; simp [pd]

lemma deriv_antisymm {F : FormField} (hF : ∀ x, IsAntisymm (F.at x)) (x : SpinorCoord) (c c' : Fin 2) :
    IsAntisymm (F.deriv x c c') := by
  intro a a' b b'
  have : F b b' a a' = fun y => -F a a' b b' y := funext fun y => hF y a a' b b'
  simp only [FormField.deriv, this, pd_neg]

lemma pd_asd {U : Set SpinorCoord} (hU : IsOpen U) {F : FormField}
    (hd : ∀ a a' b b', DifferentiableOn ℂ (F a a' b b') U) {x : SpinorCoord} (hx : x ∈ U)
    (α β γ δ' : Fin 2) : pd (F.asd ![α, β]) γ δ' x = asdPart (F.deriv x γ δ') α β := by
  have hda : ∀ a a' b b', DifferentiableAt ℂ (F a a' b b') x := fun a a' b b' =>
    (hd a a' b b').differentiableAt (hU.mem_nhds hx)
  have e : F.asd ![α, β] = fun y => ∑ p : Fin 2 × Fin 2, ((1 / 2) * eps p.1 p.2) * F α p.1 β p.2 y := by
    funext y
    simp only [FormField.asd, asdPart, FormField.at, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
  rw [e, pd_sum_mul _ _ _ (fun p _ => hda _ _ _ _)]
  simp only [asdPart, FormField.deriv, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

lemma pd_sd {U : Set SpinorCoord} (hU : IsOpen U) {F : FormField}
    (hd : ∀ a a' b b', DifferentiableOn ℂ (F a a' b b') U) {x : SpinorCoord} (hx : x ∈ U)
    (α' β' γ δ' : Fin 2) : pd (F.sd ![α', β']) γ δ' x = sdPart (F.deriv x γ δ') α' β' := by
  have hda : ∀ a a' b b', DifferentiableAt ℂ (F a a' b b') x := fun a a' b b' =>
    (hd a a' b b').differentiableAt (hU.mem_nhds hx)
  have e : F.sd ![α', β'] = fun y => ∑ p : Fin 2 × Fin 2, ((1 / 2) * eps p.1 p.2) * F p.1 α' p.2 β' y := by
    funext y
    simp only [FormField.sd, sdPart, FormField.at, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
  rw [e, pd_sum_mul _ _ _ (fun p _ => hda _ _ _ _)]
  simp only [sdPart, FormField.deriv, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

lemma cons_fin_one (α : Fin 2) (i : Fin 1 → Fin 2) : (Fin.cons α i : Fin 2 → Fin 2) = ![α, i 0] := by
  funext k; fin_cases k <;> rfl

/-- **Maxwell's equations for a 2-form field are the spin-1 z.r.m. equations** (Adamo (3.7)–(3.11)):
on an open set, `dF = 0` and `∂^a F_{ab} = 0` hold iff the ASD part is a z.r.m. field of helicity
`-1` and the SD part one of helicity `+1`. -/
theorem maxwell_iff_zrm {U : Set SpinorCoord} (hU : IsOpen U) {F : FormField}
    (hF : ∀ x, IsAntisymm (F.at x)) (hd : ∀ a a' b b', DifferentiableOn ℂ (F a a' b b') U) :
    (∀ x ∈ U, ClosedD (F.deriv x) ∧ DivFreeD (F.deriv x)) ↔
      IsZrmNeg 1 U F.asd ∧ IsZrmPos 1 U F.sd := by
  have hsymA : IsSymmField 1 F.asd := isSymmField_one fun a b => by
    funext y; simp only [FormField.asd, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact asdPart_symm (hF y) a b
  have hsymS : IsSymmField 1 F.sd := isSymmField_one fun a b => by
    funext y; simp only [FormField.sd, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact sdPart_symm (hF y) a b
  -- the z.r.m. equations of the parts at `x` are `ZrmASDD` and `ZrmSDD` of the derivative
  have hA : ∀ x ∈ U, (∀ (β' : Fin 2) (i : Fin 1 → Fin 2),
      ∑ α, ∑ γ, ∑ δ', eps α γ * eps β' δ' * pd (F.asd (Fin.cons α i)) γ δ' x = 0) ↔
      ZrmASDD (F.deriv x) := by
    intro x hx
    simp only [cons_fin_one, pd_asd hU hd hx]
    constructor
    · intro h β δ'
      have := (sum_eps_mul_eq_zero_iff (fun δ' => ∑ α, ∑ γ, eps α γ * asdPart (F.deriv x γ δ') α β)).1
        (fun β' => by
          have h' := h β' ![β]
          simp only [Fin.sum_univ_two, Matrix.cons_val_zero] at h' ⊢
          linear_combination h') δ'
      exact this
    · intro h β' i
      have h0 := fun δ' => h (i 0) δ'
      simp only [Fin.sum_univ_two] at h0 ⊢
      linear_combination eps β' 0 * h0 0 + eps β' 1 * h0 1
  have hS : ∀ x ∈ U, (∀ (β : Fin 2) (i : Fin 1 → Fin 2),
      ∑ α', ∑ γ, ∑ δ', eps β γ * eps α' δ' * pd (F.sd (Fin.cons α' i)) γ δ' x = 0) ↔
      ZrmSDD (F.deriv x) := by
    intro x hx
    simp only [cons_fin_one, pd_sd hU hd hx]
    constructor
    · intro h γ β'
      have := (sum_eps_mul_eq_zero_iff (fun γ => ∑ α', ∑ δ', eps α' δ' * sdPart (F.deriv x γ δ') α' β')).1
        (fun β => by
          have h' := h β ![β']
          simp only [Fin.sum_univ_two, Matrix.cons_val_zero] at h' ⊢
          linear_combination h') γ
      exact this
    · intro h β i
      have h0 := fun γ => h γ (i 0)
      simp only [Fin.sum_univ_two] at h0 ⊢
      linear_combination eps β 0 * h0 0 + eps β 1 * h0 1
  constructor
  · intro h
    refine ⟨⟨hsymA, fun β' i x hx => ?_⟩, ⟨hsymS, fun β i x hx => ?_⟩⟩
    · exact ((hA x hx).2 ((maxwell_iff_zrm_D (deriv_antisymm hF x)).1 (h x hx)).1) β' i
    · exact ((hS x hx).2 ((maxwell_iff_zrm_D (deriv_antisymm hF x)).1 (h x hx)).2) β i
  · rintro ⟨hn, hp⟩ x hx
    exact (maxwell_iff_zrm_D (deriv_antisymm hF x)).2
      ⟨(hA x hx).1 (fun β' i => hn.eqn β' i x hx), (hS x hx).1 (fun β i => hp.eqn β i x hx)⟩

end Lightlike.Spinor
