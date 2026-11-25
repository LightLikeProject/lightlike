import Mathlib

/-!
# The conformal group acts on the null-cone compactification; scri is preserved by the Poincaré group and dilations only

Row G1-016 (milestone GE7), clause "the conformal action of the isometry group on the boundary", in the Dirac
(projective null cone) picture of the compactification.  For a real vector space `V` with a symmetric bilinear form `B`
(any signature; Minkowski space is `V = ℝ⁴` with `B = diag(-1, 1, 1, 1)`), the points of `V` embed in the null cone
`B x x = P⁺ P⁻` of `ℝ × ℝ × V` by `x ↦ (1, B x x, x)` (`dirac`), the conformal compactification is the set of rays of the cone,
and **infinity is the set `P⁺ = 0`** (the cone of the point `(0, 1, 0)`, which is the point at infinity).

Each of the following linear maps of `ℝ × ℝ × V` preserves the cone form `coneForm` (so maps the cone to itself), and
acts on the embedded points as the stated transformation of `V`:

* an isometry `Λ` of `B` (rotations and boosts): `isoAct Λ`, `x ↦ Λ x` (`isoAct_dirac`);
* a translation by `a`: `transAct a`, `x ↦ x + a` (`transAct_dirac`);
* a dilation by `l ≠ 0`: `dilAct l`, `x ↦ l x` (`dilAct_dirac`);
* the special conformal transformation with parameter `b`: `specAct b`,
  `x ↦ (x + B x x • b) / (1 + 2 B b x + B b b · B x x)` (`specAct_dirac`).

Isometries, translations and dilations keep `P⁺ = 0` (they preserve infinity: `isoAct_fst`, `transAct_fst`, `dilAct_fst`), whereas
a special conformal transformation does not: it moves the point at infinity `(0, 1, 0)` to the finite point `b`, off
infinity when `B b b ≠ 0` (`specAct_infinity`).  Not proved here: that this picture agrees with the null-angle picture
`(η, χ)` of `MinkowskiCompactification.lean` (the identification of the two compactifications), or that these maps are
continuous on the projective space (they are linear on the cone).
-/

set_option linter.unusedSectionVars false

namespace Lightlike

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The quadratic form of the cone: `B x x - P⁺ P⁻`. -/
def coneForm (B : LinearMap.BilinForm ℝ V) (P : ℝ × ℝ × V) : ℝ := B P.2.2 P.2.2 - P.1 * P.2.1

/-- The Dirac embedding of `V` in the null cone. -/
def dirac (B : LinearMap.BilinForm ℝ V) (x : V) : ℝ × ℝ × V := (1, B x x, x)

/-- The Dirac embedding lands in the null cone: `coneForm B (dirac B x) = 0`. -/
theorem coneForm_dirac (B : LinearMap.BilinForm ℝ V) (x : V) : coneForm B (dirac B x) = 0 := by
  simp [coneForm, dirac]

/-- An isometry of `B` acting on the cone. -/
def isoAct (Λ : V →ₗ[ℝ] V) (P : ℝ × ℝ × V) : ℝ × ℝ × V := (P.1, P.2.1, Λ P.2.2)

/-- An isometry of `B` preserves the cone form. -/
theorem coneForm_isoAct (B : LinearMap.BilinForm ℝ V) {Λ : V →ₗ[ℝ] V} (hΛ : ∀ x, B (Λ x) (Λ x) = B x x)
    (P : ℝ × ℝ × V) : coneForm B (isoAct Λ P) = coneForm B P := by
  simp [coneForm, isoAct, hΛ]

/-- An isometry acts on the embedded points as `x ↦ Λ x`. -/
theorem isoAct_dirac (B : LinearMap.BilinForm ℝ V) {Λ : V →ₗ[ℝ] V} (hΛ : ∀ x, B (Λ x) (Λ x) = B x x)
    (x : V) : isoAct Λ (dirac B x) = dirac B (Λ x) := by
  simp [isoAct, dirac, hΛ]

/-- An isometry does not change the coordinate `P⁺`, so it preserves infinity `P⁺ = 0`. -/
theorem isoAct_fst (Λ : V →ₗ[ℝ] V) (P : ℝ × ℝ × V) : (isoAct Λ P).1 = P.1 := rfl

/-- The translation by `a` acting on the cone. -/
def transAct (B : LinearMap.BilinForm ℝ V) (a : V) (P : ℝ × ℝ × V) : ℝ × ℝ × V :=
  (P.1, P.2.1 + 2 * B a P.2.2 + B a a * P.1, P.2.2 + P.1 • a)

/-- A translation preserves the cone form. -/
theorem coneForm_transAct (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) (a : V) (P : ℝ × ℝ × V) :
    coneForm B (transAct B a P) = coneForm B P := by
  obtain ⟨p, q, x⟩ := P
  have h : B x a = B a x := (hB.eq a x).symm
  simp only [coneForm, transAct, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h]
  ring

/-- A translation acts on the embedded points as `x ↦ x + a`. -/
theorem transAct_dirac (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) (a x : V) :
    transAct B a (dirac B x) = dirac B (x + a) := by
  have h : B x a = B a x := (hB.eq a x).symm
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only [transAct, dirac, map_add, LinearMap.add_apply, h, mul_one]
    ring
  · simp [transAct, dirac]

/-- A translation does not change `P⁺`, so it preserves infinity. -/
theorem transAct_fst (B : LinearMap.BilinForm ℝ V) (a : V) (P : ℝ × ℝ × V) : (transAct B a P).1 = P.1 := rfl

/-- The dilation by `l` acting on the cone. -/
noncomputable def dilAct (l : ℝ) (P : ℝ × ℝ × V) : ℝ × ℝ × V := (P.1 / l, l * P.2.1, P.2.2)

/-- A dilation preserves the cone form. -/
theorem coneForm_dilAct (B : LinearMap.BilinForm ℝ V) {l : ℝ} (hl : l ≠ 0) (P : ℝ × ℝ × V) :
    coneForm B (dilAct l P) = coneForm B P := by
  simp only [coneForm, dilAct]
  field_simp

/-- A dilation acts on the embedded points as the dilation, up to the scale `l⁻¹` of the ray. -/
theorem dilAct_dirac (B : LinearMap.BilinForm ℝ V) {l : ℝ} (hl : l ≠ 0) (x : V) :
    dilAct l (dirac B x) = l⁻¹ • dirac B (l • x) := by
  simp only [dilAct, dirac, map_smul, LinearMap.smul_apply, smul_eq_mul, Prod.smul_mk, Prod.mk.injEq]
  refine ⟨by simp [div_eq_inv_mul], ?_, ?_⟩
  · field_simp
  · rw [smul_smul, inv_mul_cancel₀ hl, one_smul]

/-- A dilation scales `P⁺` by `l⁻¹`, so it preserves infinity `P⁺ = 0`. -/
theorem dilAct_fst (l : ℝ) (P : ℝ × ℝ × V) : (dilAct l P).1 = P.1 / l := rfl

/-- The special conformal transformation with parameter `b` acting on the cone. -/
def specAct (B : LinearMap.BilinForm ℝ V) (b : V) (P : ℝ × ℝ × V) : ℝ × ℝ × V :=
  (P.1 + 2 * B b P.2.2 + B b b * P.2.1, P.2.1, P.2.2 + P.2.1 • b)

/-- A special conformal transformation preserves the cone form. -/
theorem coneForm_specAct (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) (b : V) (P : ℝ × ℝ × V) :
    coneForm B (specAct B b P) = coneForm B P := by
  obtain ⟨p, q, x⟩ := P
  have h : B x b = B b x := (hB.eq b x).symm
  simp only [coneForm, specAct, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h]
  ring

/-- On the embedded points the map is `(1 + 2 B b x + B b b · B x x, B x x, x + B x x • b)`, i.e. the special conformal
transformation `x ↦ (x + B x x • b) / (1 + 2 B b x + B b b · B x x)` up to the scale `D` of the ray. -/
theorem specAct_dirac (B : LinearMap.BilinForm ℝ V) (b x : V) :
    specAct B b (dirac B x) = (1 + 2 * B b x + B b b * B x x, B x x, x + B x x • b) := by
  simp [specAct, dirac]

/-- The scale-`D` form: when `D = 1 + 2 B b x + B b b · B x x ≠ 0`, `specAct B b (dirac B x) = D • dirac B x'` with
`x' = D⁻¹ • (x + B x x • b)`, provided `B` is symmetric. -/
theorem specAct_dirac_smul (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) (b x : V)
    (hD : 1 + 2 * B b x + B b b * B x x ≠ 0) :
    specAct B b (dirac B x) =
      (1 + 2 * B b x + B b b * B x x) • dirac B ((1 + 2 * B b x + B b b * B x x)⁻¹ • (x + B x x • b)) := by
  set D := 1 + 2 * B b x + B b b * B x x with hDdef
  have h : B x b = B b x := (hB.eq b x).symm
  have hq : B (x + B x x • b) (x + B x x • b) = B x x * D := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h, hDdef]
    ring
  rw [specAct_dirac]
  simp only [dirac, map_smul, LinearMap.smul_apply, smul_eq_mul, hq, Prod.smul_mk, Prod.mk.injEq]
  refine ⟨by simp [hDdef], ?_, ?_⟩
  · field_simp
  · rw [smul_smul, mul_inv_cancel₀ hD, one_smul]

/-- **A special conformal transformation moves infinity**: the point at infinity `(0, 1, 0)` of the cone goes to
`(B b b, 1, b)`, which is off infinity when `B b b ≠ 0` (it is the embedded point `b` up to scale). -/
theorem specAct_infinity (B : LinearMap.BilinForm ℝ V) (b : V) :
    specAct B b ((0, 1, 0) : ℝ × ℝ × V) = (B b b, 1, b) := by
  simp [specAct]

/-- The image of the point at infinity under `specAct B b` is off infinity when `B b b ≠ 0`. -/
theorem specAct_infinity_fst_ne (B : LinearMap.BilinForm ℝ V) {b : V} (hb : B b b ≠ 0) :
    (specAct B b ((0, 1, 0) : ℝ × ℝ × V)).1 ≠ 0 := by
  rw [specAct_infinity]; exact hb

end Lightlike
