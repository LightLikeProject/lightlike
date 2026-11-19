import Lightlike.GR.ComplexMinkowski
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Lines of `CP³` and the Klein quadric: the compactified complexified Minkowski space

The 2-planes of `ℂ⁴` (the lines of `CP³`, `Gr2`) correspond one to one to the points of the Klein
quadric `Q = {[X] ∈ ℙ(ℂ⁶) | X⁰¹X²³ - X⁰²X¹³ + X⁰³X¹² = 0}` (`kleinEquiv`): a plane with a basis
`(Z₁, Z₂)` goes to its Plücker coordinates `[Z₁ ∧ Z₂]` (`toKlein`, independent of the basis up to
scale, `pluckerVec_comb`), and a point `[X]` of `Q` to the plane `{Z | Z ∧ X = 0}` (`planeOf`),
which is the span of `Z₁, Z₂` whenever `X = Z₁ ∧ Z₂ ≠ 0` (`planeOf_pluckerVec`); every nonzero point
of `Q` is such a product (`exists_pluckerVec_eq`, from `klein_decomposable`). Adamo identifies `Q`
with the compactified complexified Minkowski space.

The affine part: a plane is a twistor line `twistorLine x` iff it meets the plane at infinity
`λ = 0` only in `0` (`isTwistorLine_iff`), iff its Plücker coordinate `X²³ = I_AB X^AB` is nonzero
(`inf_infinityPlane_eq_bot_iff`); so **the complement of the chart is exactly the set of lines
meeting the line at infinity `I`** (`compl_range_twistorLine`).

## References

* T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196: lines of `CP³` and points of `M_C`, §1.4,
  pp. 9–10; the bi-twistor of a point (2.25), p. 19; footnote 2, p. 20: "the quadric
  Q = {X ∈ CP⁵ | X² = 0} ... is something known as the Klein quadric, which represents points in Q as
  lines in a complex projective 3-space"; p. 20: "I_AB X^AB = 0, which defines a set of points 'at
  infinity' in the usual sense of conformal compactification"; (2.29) and p. 21: `I_AB X^AB = ⟨λ₁ λ₂⟩`,
  lines with `I_AB X^AB = 0` are the points at infinity.

Difference (representation): the lines of `CP³` are the 2-dimensional subspaces of `ℂ⁴` and the
line at infinity `I` is the plane `λ = 0` (`infinityPlane`); `Q` lies in `ℙ(ℂ⁶)` with the coordinates
`(X⁰¹, X⁰², X⁰³, X¹², X¹³, X²³)`.
-/

open Matrix
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace Lightlike

/-! ## Plücker coordinates in `ℂ⁶` -/

/-- The index pairs `01, 02, 03, 12, 13, 23`. -/
def pluckerPair : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The Plücker vector `Z₁ ∧ Z₂ ∈ ℂ⁶`. -/
def pluckerVec (Z₁ Z₂ : Fin 4 → ℂ) : Fin 6 → ℂ := fun k => plucker Z₁ Z₂ (pluckerPair k).1 (pluckerPair k).2

/-- The skew matrix of a vector of `ℂ⁶`. -/
def toSkew (X : Fin 6 → ℂ) : Fin 4 → Fin 4 → ℂ :=
  ![![0, X 0, X 1, X 2], ![-X 0, 0, X 3, X 4], ![-X 1, -X 3, 0, X 5], ![-X 2, -X 4, -X 5, 0]]

lemma toSkew_pluckerVec (Z₁ Z₂ : Fin 4 → ℂ) : toSkew (pluckerVec Z₁ Z₂) = plucker Z₁ Z₂ := by
  funext a b
  fin_cases a <;> fin_cases b <;> simp [toSkew, pluckerVec, pluckerPair, plucker] <;> ring

lemma toSkew_skew (X : Fin 6 → ℂ) (a b : Fin 4) : toSkew X b a = -toSkew X a b := by
  fin_cases a <;> fin_cases b <;> simp [toSkew]

/-- The Klein form `X⁰¹X²³ - X⁰²X¹³ + X⁰³X¹²` (the Pfaffian). -/
def kleinForm (X : Fin 6 → ℂ) : ℂ := X 0 * X 5 - X 1 * X 4 + X 2 * X 3

lemma kleinForm_pluckerVec (Z₁ Z₂ : Fin 4 → ℂ) : kleinForm (pluckerVec Z₁ Z₂) = 0 := by
  have := plucker_klein Z₁ Z₂
  simp only [kleinForm, pluckerVec, pluckerPair]
  simpa using this

lemma kleinForm_smul (c : ℂ) (X : Fin 6 → ℂ) : kleinForm (c • X) = c ^ 2 * kleinForm X := by
  simp only [kleinForm, Pi.smul_apply, smul_eq_mul]; ring

/-- **The Plücker vector changes by the determinant** under a change of the two vectors. -/
lemma pluckerVec_comb (α β γ δ : ℂ) (Z₁ Z₂ : Fin 4 → ℂ) :
    pluckerVec (α • Z₁ + β • Z₂) (γ • Z₁ + δ • Z₂) = (α * δ - β * γ) • pluckerVec Z₁ Z₂ := by
  funext k
  fin_cases k <;> simp [pluckerVec, pluckerPair, plucker] <;> ring

/-- **The Plücker vector is nonzero iff the two vectors are independent.** -/
theorem pluckerVec_ne_zero_iff (Z₁ Z₂ : Fin 4 → ℂ) :
    pluckerVec Z₁ Z₂ ≠ 0 ↔ LinearIndependent ℂ ![Z₁, Z₂] := by
  rw [LinearIndependent.pair_iff]
  constructor
  · intro h s t hst
    have hZ := fun i => congrFun hst i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hZ
    obtain ⟨k, hk⟩ := Function.ne_iff.1 h
    set a := (pluckerPair k).1
    set b := (pluckerPair k).2
    have hab : Z₁ a * Z₂ b - Z₂ a * Z₁ b ≠ 0 := hk
    have ha := hZ a
    have hb := hZ b
    constructor
    · have : s * (Z₁ a * Z₂ b - Z₂ a * Z₁ b) = 0 := by linear_combination Z₂ b * ha - Z₂ a * hb
      exact (mul_eq_zero.1 this).resolve_right hab
    · have : t * (Z₁ a * Z₂ b - Z₂ a * Z₁ b) = 0 := by linear_combination Z₁ a * hb - Z₁ b * ha
      exact (mul_eq_zero.1 this).resolve_right hab
  · intro h h0
    have hall : ∀ a b, Z₁ a * Z₂ b - Z₂ a * Z₁ b = 0 := fun a b => by
      have := congrFun (congrFun (toSkew_pluckerVec Z₁ Z₂) a) b
      rw [h0] at this
      have h' : toSkew 0 a b = 0 := by fin_cases a <;> fin_cases b <;> simp [toSkew]
      rw [h'] at this
      unfold plucker at this
      exact this.symm
    by_cases hZ₁ : Z₁ = 0
    · have := h 1 0 (by simp [hZ₁])
      exact one_ne_zero this.1
    · obtain ⟨a, ha⟩ := Function.ne_iff.1 hZ₁
      have ha' : Z₁ a ≠ 0 := ha
      have key := h (Z₂ a / Z₁ a) (-1) (by
        funext b
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [div_mul_eq_mul_div, show Z₂ a * Z₁ b = Z₁ a * Z₂ b by linear_combination -(hall a b),
          mul_div_cancel_left₀ _ ha']
        ring)
      exact one_ne_zero (neg_eq_zero.1 key.2)

/-! ## The plane of a bivector -/

/-- `Z ∧ X` in components: `(Z ∧ X)_{ABC} = Z_A X_BC - Z_B X_AC + Z_C X_AB`. -/
def wedgeMap (X : Fin 6 → ℂ) : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → Fin 4 → Fin 4 → ℂ) where
  toFun Z A B C := Z A * toSkew X B C - Z B * toSkew X A C + Z C * toSkew X A B
  map_add' Z W := by funext A B C; simp only [Pi.add_apply]; ring
  map_smul' c Z := by funext A B C; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The plane `{Z | Z ∧ X = 0}` of a bivector `X`. -/
def planeOf (X : Fin 6 → ℂ) : Submodule ℂ (Fin 4 → ℂ) := LinearMap.ker (wedgeMap X)

lemma planeOf_smul {c : ℂ} (hc : c ≠ 0) (X : Fin 6 → ℂ) : planeOf (c • X) = planeOf X := by
  ext Z
  simp only [planeOf, LinearMap.mem_ker, wedgeMap, LinearMap.coe_mk, AddHom.coe_mk]
  have hs : ∀ a b, toSkew (c • X) a b = c * toSkew X a b := fun a b => by
    fin_cases a <;> fin_cases b <;> simp [toSkew]
  simp only [hs]
  constructor
  · intro h; funext A B C
    have := congrFun (congrFun (congrFun h A) B) C
    simp only [Pi.zero_apply] at this ⊢
    have : c * (Z A * toSkew X B C - Z B * toSkew X A C + Z C * toSkew X A B) = 0 := by
      linear_combination this
    exact (mul_eq_zero.1 this).resolve_left hc
  · intro h; funext A B C
    have := congrFun (congrFun (congrFun h A) B) C
    simp only [Pi.zero_apply] at this ⊢
    linear_combination c * this

/-- **The plane of `Z₁ ∧ Z₂ ≠ 0` is the span of `Z₁, Z₂`.** -/
theorem planeOf_pluckerVec {Z₁ Z₂ : Fin 4 → ℂ} (h : LinearIndependent ℂ ![Z₁, Z₂]) :
    planeOf (pluckerVec Z₁ Z₂) = Submodule.span ℂ {Z₁, Z₂} := by
  have hX := toSkew_pluckerVec Z₁ Z₂
  apply le_antisymm
  · intro Z hZ
    have hw : ∀ A B C, Z A * plucker Z₁ Z₂ B C - Z B * plucker Z₁ Z₂ A C + Z C * plucker Z₁ Z₂ A B = 0 :=
      fun A B C => by
        have := congrFun (congrFun (congrFun (LinearMap.mem_ker.1 hZ) A) B) C
        simpa [wedgeMap, hX] using this
    obtain ⟨k, hk⟩ := Function.ne_iff.1 ((pluckerVec_ne_zero_iff Z₁ Z₂).2 h)
    set a := (pluckerPair k).1
    set b := (pluckerPair k).2
    have hab : plucker Z₁ Z₂ a b ≠ 0 := hk
    rw [Submodule.mem_span_pair]
    refine ⟨(Z a * Z₂ b - Z b * Z₂ a) / plucker Z₁ Z₂ a b,
      (Z b * Z₁ a - Z a * Z₁ b) / plucker Z₁ Z₂ a b, ?_⟩
    funext C
    have hC := hw C a b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    unfold plucker at hC hab ⊢
    linear_combination -hC
  · rw [Submodule.span_le]
    intro Z hZ
    rcases hZ with rfl | rfl
    · refine LinearMap.mem_ker.2 (funext fun A => funext fun B => funext fun C => ?_)
      simp only [wedgeMap, LinearMap.coe_mk, AddHom.coe_mk, hX, plucker, Pi.zero_apply]
      ring
    · refine LinearMap.mem_ker.2 (funext fun A => funext fun B => funext fun C => ?_)
      simp only [wedgeMap, LinearMap.coe_mk, AddHom.coe_mk, hX, plucker, Pi.zero_apply]
      ring

lemma finrank_span_pair {Z₁ Z₂ : Fin 4 → ℂ} (h : LinearIndependent ℂ ![Z₁, Z₂]) :
    Module.finrank ℂ (Submodule.span ℂ ({Z₁, Z₂} : Set (Fin 4 → ℂ))) = 2 := by
  have := finrank_span_eq_card h
  rw [Fintype.card_fin] at this
  rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union] at this

/-- **Every nonzero point of the Klein quadric is a Plücker vector** (`klein_decomposable`). -/
theorem exists_pluckerVec_eq {X : Fin 6 → ℂ} (hX : X ≠ 0) (hQ : kleinForm X = 0) :
    ∃ Z₁ Z₂ : Fin 4 → ℂ, pluckerVec Z₁ Z₂ = X := by
  have hS : toSkew X ≠ 0 := by
    intro h0; apply hX; funext k
    have h := fun a b => congrFun (congrFun h0 a) b
    fin_cases k
    · simpa [toSkew] using h 0 1
    · simpa [toSkew] using h 0 2
    · simpa [toSkew] using h 0 3
    · simpa [toSkew] using h 1 2
    · simpa [toSkew] using h 1 3
    · simpa [toSkew] using h 2 3
  have hPf : toSkew X 0 1 * toSkew X 2 3 - toSkew X 0 2 * toSkew X 1 3 + toSkew X 0 3 * toSkew X 1 2 = 0 := by
    simpa [toSkew, kleinForm] using hQ
  obtain ⟨Z₁, Z₂, hZ⟩ := klein_decomposable (toSkew X) (fun A B => toSkew_skew X A B) hPf hS
  refine ⟨Z₁, Z₂, funext fun k => ?_⟩
  fin_cases k
  · simpa [pluckerVec, pluckerPair, toSkew] using (hZ 0 1).symm
  · simpa [pluckerVec, pluckerPair, toSkew] using (hZ 0 2).symm
  · simpa [pluckerVec, pluckerPair, toSkew] using (hZ 0 3).symm
  · simpa [pluckerVec, pluckerPair, toSkew] using (hZ 1 2).symm
  · simpa [pluckerVec, pluckerPair, toSkew] using (hZ 1 3).symm
  · simpa [pluckerVec, pluckerPair, toSkew] using (hZ 2 3).symm

/-! ## The bijection -/

/-- The lines of `CP³`: the 2-dimensional subspaces of `ℂ⁴`. -/
def Gr2 : Type := {L : Submodule ℂ (Fin 4 → ℂ) // Module.finrank ℂ L = 2}

/-- The Klein quadric in `ℙ(ℂ⁶)`. -/
def KleinQuadric : Set (ℙ ℂ (Fin 6 → ℂ)) := {p | kleinForm p.rep = 0}

lemma mem_kleinQuadric_mk (X : Fin 6 → ℂ) (hX : X ≠ 0) :
    Projectivization.mk ℂ X hX ∈ KleinQuadric ↔ kleinForm X = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ X hX
  show kleinForm (Projectivization.mk ℂ X hX).rep = 0 ↔ _
  rw [← ha, Units.smul_def, kleinForm_smul]
  simp [a.ne_zero]

/-- A basis `(b 0, b 1)` of a plane. -/
def Gr2.basis (L : Gr2) : Module.Basis (Fin 2) ℂ L.1 := Module.finBasisOfFinrankEq ℂ L.1 L.2

lemma Gr2.linearIndependent (L : Gr2) :
    LinearIndependent ℂ ![(L.basis 0 : Fin 4 → ℂ), (L.basis 1 : Fin 4 → ℂ)] := by
  have := L.basis.linearIndependent.map' L.1.subtype (Submodule.ker_subtype _)
  convert this using 1
  funext i; fin_cases i <;> rfl

lemma Gr2.span_basis (L : Gr2) :
    Submodule.span ℂ {(L.basis 0 : Fin 4 → ℂ), (L.basis 1 : Fin 4 → ℂ)} = L.1 := by
  have h := L.basis.span_eq
  have : ({(L.basis 0 : Fin 4 → ℂ), (L.basis 1 : Fin 4 → ℂ)} : Set (Fin 4 → ℂ)) =
      L.1.subtype '' Set.range L.basis := by
    ext Z; simp [Fin.exists_fin_two, eq_comm]
  rw [this, ← Submodule.map_span, h, Submodule.map_top, Submodule.range_subtype]

/-- **The Plücker point of a line of `CP³`.** -/
def toKlein (L : Gr2) : ℙ ℂ (Fin 6 → ℂ) :=
  Projectivization.mk ℂ (pluckerVec (L.basis 0) (L.basis 1))
    ((pluckerVec_ne_zero_iff _ _).2 L.linearIndependent)

lemma toKlein_mem (L : Gr2) : toKlein L ∈ KleinQuadric :=
  (mem_kleinQuadric_mk _ _).2 (kleinForm_pluckerVec _ _)

lemma rep_toKlein (L : Gr2) :
    ∃ c : ℂ, c ≠ 0 ∧ (toKlein L).rep = c • pluckerVec (L.basis 0) (L.basis 1) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (pluckerVec (L.basis 0) (L.basis 1))
    ((pluckerVec_ne_zero_iff _ _).2 L.linearIndependent)
  exact ⟨a, a.ne_zero, by rw [toKlein, ← ha, Units.smul_def]⟩

lemma finrank_planeOf {X : Fin 6 → ℂ} (hX : X ≠ 0) (hQ : kleinForm X = 0) :
    Module.finrank ℂ (planeOf X) = 2 := by
  obtain ⟨Z₁, Z₂, rfl⟩ := exists_pluckerVec_eq hX hQ
  have h := (pluckerVec_ne_zero_iff Z₁ Z₂).1 hX
  rw [planeOf_pluckerVec h, finrank_span_pair h]

/-- **The line of `CP³` of a point of the Klein quadric.** -/
def fromKlein (p : KleinQuadric) : Gr2 := ⟨planeOf p.1.rep, finrank_planeOf p.1.rep_nonzero p.2⟩

lemma fromKlein_toKlein (L : Gr2) : fromKlein ⟨toKlein L, toKlein_mem L⟩ = L := by
  obtain ⟨c, hc, h⟩ := rep_toKlein L
  apply Subtype.ext
  show planeOf (toKlein L).rep = L.1
  rw [h, planeOf_smul hc, planeOf_pluckerVec L.linearIndependent, L.span_basis]

lemma toKlein_fromKlein (p : KleinQuadric) : toKlein (fromKlein p) = p.1 := by
  obtain ⟨Z₁, Z₂, hZ⟩ := exists_pluckerVec_eq p.1.rep_nonzero p.2
  have hind := (pluckerVec_ne_zero_iff Z₁ Z₂).1 (hZ ▸ p.1.rep_nonzero)
  set L := fromKlein p
  have hL : L.1 = Submodule.span ℂ {Z₁, Z₂} := by
    show planeOf p.1.rep = _
    rw [← hZ, planeOf_pluckerVec hind]
  have h0 : (L.basis 0 : Fin 4 → ℂ) ∈ Submodule.span ℂ {Z₁, Z₂} := hL ▸ (L.basis 0).2
  have h1 : (L.basis 1 : Fin 4 → ℂ) ∈ Submodule.span ℂ {Z₁, Z₂} := hL ▸ (L.basis 1).2
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 h0
  obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.1 h1
  have hP : pluckerVec (L.basis 0) (L.basis 1) = (α * δ - β * γ) • p.1.rep := by
    rw [← hαβ, ← hγδ, pluckerVec_comb, hZ]
  have hd : α * δ - β * γ ≠ 0 := by
    intro h0'
    have := (pluckerVec_ne_zero_iff _ _).2 L.linearIndependent
    rw [hP, h0', zero_smul] at this
    exact this rfl
  conv_rhs => rw [← Projectivization.mk_rep p.1]
  rw [toKlein, Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 (α * δ - β * γ) hd, by rw [Units.smul_def, Units.val_mk0, hP]⟩

/-- **The lines of `CP³` correspond one to one to the points of the Klein quadric** (Adamo, footnote
2, p. 20). -/
def kleinEquiv : Gr2 ≃ KleinQuadric where
  toFun L := ⟨toKlein L, toKlein_mem L⟩
  invFun := fromKlein
  left_inv := fromKlein_toKlein
  right_inv p := Subtype.ext (toKlein_fromKlein p)

/-! ## The affine part and the lines at infinity -/

/-- The twistor line of a point, as a line of `CP³`. -/
def Gr2.ofPoint (x : Fin 4 → ℂ) : Gr2 := ⟨twistorLine x, finrank_twistorLine x⟩

/-- **A line of `CP³` is a twistor line iff it misses the plane at infinity.** -/
theorem isTwistorLine_iff (L : Gr2) : (∃ x, twistorLine x = L.1) ↔ L.1 ⊓ infinityPlane = ⊥ := by
  constructor
  · rintro ⟨x, hx⟩; rw [← hx]; exact twistorLine_inf_infinity x
  · intro h; exact exists_twistorLine_eq L.1 L.2 h

/-- **A line meets the plane at infinity iff its Plücker coordinate `X²³ = I_AB X^AB` vanishes**
(Adamo p. 21: `I_AB X^AB = ⟨λ₁ λ₂⟩`). -/
theorem inf_infinityPlane_eq_bot_iff (L : Gr2) :
    L.1 ⊓ infinityPlane = ⊥ ↔ (toKlein L).rep 5 ≠ 0 := by
  obtain ⟨c, hc, h⟩ := rep_toKlein L
  set b₀ : Fin 4 → ℂ := (L.basis 0).1
  set b₁ : Fin 4 → ℂ := (L.basis 1).1
  have h5 : (toKlein L).rep 5 = c * (b₀ 2 * b₁ 3 - b₁ 2 * b₀ 3) := by
    rw [h]; simp [pluckerVec, pluckerPair, plucker, b₀, b₁]
  rw [h5, mul_ne_zero_iff, and_iff_right hc]
  set M : Matrix (Fin 2) (Fin 2) ℂ := !![b₀ 2, b₁ 2; b₀ 3, b₁ 3]
  have hdet : M.det = b₀ 2 * b₁ 3 - b₁ 2 * b₀ 3 := by rw [det_fin_two]; simp [M]
  have hind := L.linearIndependent
  have hspan := L.span_basis
  constructor
  · intro hbot hzero
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (hdet.trans hzero)
    set Z : Fin 4 → ℂ := v 0 • b₀ + v 1 • b₁
    have hZL : Z ∈ L.1 := hspan ▸ Submodule.mem_span_pair.2 ⟨v 0, v 1, rfl⟩
    have hZI : Z ∈ infinityPlane := by
      rw [infinityPlane, LinearMap.mem_ker, lambdaPart_apply]
      have e0 := congrFun hMv 0
      have e1 := congrFun hMv 1
      simp [M, mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
      funext i; fin_cases i
      · simp [Z]; linear_combination e0
      · simp [Z]; linear_combination e1
    have hZ0 : Z = 0 := by
      have : Z ∈ L.1 ⊓ infinityPlane := ⟨hZL, hZI⟩
      rw [hbot] at this; exact this
    have := (LinearIndependent.pair_iff.1 hind) (v 0) (v 1) hZ0
    exact hv (funext fun i => by fin_cases i <;> simp [this.1, this.2])
  · intro hne
    rw [eq_bot_iff]
    rintro Z ⟨hZL, hZI⟩
    rw [Submodule.mem_bot]
    rw [← hspan] at hZL
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hZL
    have hlam := congrFun (LinearMap.mem_ker.1 hZI)
    simp only [lambdaPart_apply] at hlam
    have e0 := hlam 0
    have e1 := hlam 1
    simp at e0 e1
    have hs : s * (b₀ 2 * b₁ 3 - b₁ 2 * b₀ 3) = 0 := by linear_combination b₁ 3 * e0 - b₁ 2 * e1
    have ht : t * (b₀ 2 * b₁ 3 - b₁ 2 * b₀ 3) = 0 := by linear_combination b₀ 2 * e1 - b₀ 3 * e0
    rw [(mul_eq_zero.1 hs).resolve_right hne, (mul_eq_zero.1 ht).resolve_right hne, zero_smul,
      zero_smul, add_zero]

/-- **The complement of the affine chart is the set of lines meeting the line at infinity `I`**:
a line of `CP³` is not a twistor line iff it meets `λ = 0`, iff `I_AB X^AB = X²³ = 0`. -/
theorem compl_range_twistorLine :
    {L : Gr2 | ¬ ∃ x, twistorLine x = L.1} = {L : Gr2 | L.1 ⊓ infinityPlane ≠ ⊥} ∧
      {L : Gr2 | L.1 ⊓ infinityPlane ≠ ⊥} = {L : Gr2 | (toKlein L).rep 5 = 0} := by
  constructor
  · ext L; simp only [Set.mem_ofPred_eq, isTwistorLine_iff]
  · ext L; simp only [Set.mem_ofPred_eq, ne_eq, inf_infinityPlane_eq_bot_iff, not_not]

/-- **The affine chart is `ℂ⁴`**: `x ↦ twistorLine x` is injective, with image the lines missing `I`. -/
theorem twistorLine_affine_chart :
    Function.Injective Gr2.ofPoint ∧
      Set.range Gr2.ofPoint = {L : Gr2 | (toKlein L).rep 5 ≠ 0} := by
  refine ⟨fun x y h => twistorLine_injective (congrArg Subtype.val h), ?_⟩
  ext L
  simp only [Set.mem_range, Set.mem_ofPred_eq, ← inf_infinityPlane_eq_bot_iff, ← isTwistorLine_iff]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩; exact ⟨x, Subtype.ext hx⟩

end Lightlike
