import Lightlike.PonzanoRegge.Asymptotics

/-!
# The saddle point of Racah's sum and the geometry of the tetrahedron

Racah's formula writes the 6j symbol as an alternating sum of ratios of factorials. With the
spins scaled by `λ` and the shifted edge lengths `ℓ = λj + ½`, Stirling's formula turns the summand
into `exp ψ(σ)`, where

  `ψ(x) = x log x − Σᵢ (x − Aᵢ) log(x − Aᵢ) − Σₖ (Bₖ − x) log(Bₖ − x) + iπx`.

Here `Aᵢ` are the four face perimeters, `Bₖ` the three sums of the four edges that avoid a pair
of opposite edges, and `iπx` carries the alternating sign. This file proves the exact algebra of
the saddle point of `ψ`, which is where the tetrahedron appears.

* The critical points of `ψ` solve `x ∏ₖ (Bₖ − x) + ∏ᵢ (x − Aᵢ) = 0`, in which the quartic and cubic
  terms cancel: a quadratic `qa x² + qb x + qc` with `qa = 2(ℓ₀ℓ₃ + ℓ₁ℓ₄ + ℓ₂ℓ₅)`.
* Its discriminant is `−576 · vol2` (`disc_eq`), so the two saddles are complex conjugate exactly
  when the tetrahedron is Euclidean. The upper one is `saddle ℓ = (−qb + 24 i √vol2)/(2 qa)`.
* `|saddle − c|² = Q(c)/qa` for real `c` (`normSq_saddle_sub`).
* **Edge identity** (`edgeProd_zero_re`, `edgeProd_zero_im`): for the edge `AB`, the product
  `(s − A₀)(s − A₁)(B₀ − s̄)(B₂ − s̄)` is a positive multiple of `−cos φ + i sin φ`, with `φ` the
  interior dihedral angle at `AB`. Its argument is the exterior dihedral angle
  (`arg_edgeProd_zero`).

Labelling as in `PonzanoRegge/`: `ℓ = (AB, BC, CA, CD, AD, BD)`; faces `ABC, ABD, BCD, ACD`;
opposite pairs `(AB, CD), (BC, AD), (CA, BD)`.
-/

open Real

namespace Lightlike.Asymptotics

/-- The four face perimeters `Aᵢ` of the faces `ABC, ABD, BCD, ACD`, for edge lengths
`l = (AB, BC, CA, CD, AD, BD)`. -/
def faceSum (l : Fin 6 → ℝ) (i : Fin 4) : ℝ :=
  ![l 0 + l 1 + l 2, l 0 + l 4 + l 5, l 3 + l 1 + l 5, l 3 + l 4 + l 2] i

/-- The three sums `Bₖ` of the four edges avoiding an opposite pair: avoiding `(CA, BD)`,
`(AB, CD)` and `(BC, AD)`. -/
def quadSum (l : Fin 6 → ℝ) (k : Fin 3) : ℝ :=
  ![l 0 + l 1 + l 3 + l 4, l 1 + l 2 + l 4 + l 5, l 2 + l 0 + l 5 + l 3] k

/-- The squared volume `vol2` of the core file, applied to a length vector. -/
noncomputable def vol2l (l : Fin 6 → ℝ) : ℝ := PR.vol2 (l 0) (l 1) (l 2) (l 3) (l 4) (l 5)

/-- Leading coefficient of the saddle-point quadratic: `2(ℓ₀ℓ₃ + ℓ₁ℓ₄ + ℓ₂ℓ₅)`. -/
def qa (l : Fin 6 → ℝ) : ℝ := 2 * (l 0 * l 3 + l 1 * l 4 + l 2 * l 5)

/-- Linear coefficient of the saddle-point quadratic: `e₃(B) − e₃(A)`. -/
def qb (l : Fin 6 → ℝ) : ℝ :=
  quadSum l 0 * quadSum l 1 * quadSum l 2 -
    (faceSum l 0 * faceSum l 1 * faceSum l 2 + faceSum l 0 * faceSum l 1 * faceSum l 3 +
      faceSum l 0 * faceSum l 2 * faceSum l 3 + faceSum l 1 * faceSum l 2 * faceSum l 3)

/-- Constant coefficient of the saddle-point quadratic: `A₀A₁A₂A₃`. -/
def qc (l : Fin 6 → ℝ) : ℝ := faceSum l 0 * faceSum l 1 * faceSum l 2 * faceSum l 3

/-- The saddle-point polynomial `Q(x) = x ∏ₖ (Bₖ − x) + ∏ᵢ (x − Aᵢ)` at a real point. -/
def saddleQ (l : Fin 6 → ℝ) (x : ℝ) : ℝ :=
  x * ((quadSum l 0 - x) * (quadSum l 1 - x) * (quadSum l 2 - x)) +
    (x - faceSum l 0) * (x - faceSum l 1) * (x - faceSum l 2) * (x - faceSum l 3)

/-- The upper saddle point `(−qb + 24 i √vol2) / (2 qa)`. -/
noncomputable def saddle (l : Fin 6 → ℝ) : ℂ :=
  ⟨-qb l / (2 * qa l), 12 * √(vol2l l) / qa l⟩

/-- A Euclidean tetrahedron: every face perimeter is smaller than every sum `Bₖ` (these twelve
differences are exactly the twelve strict triangle inequalities of the faces, see
`quadSum_sub_faceSum`), and `vol2 > 0`. -/
def IsEuclid (l : Fin 6 → ℝ) : Prop := (∀ i k, faceSum l i < quadSum l k) ∧ 0 < vol2l l

section Simp

variable (l : Fin 6 → ℝ)

@[simp] lemma faceSum_zero : faceSum l 0 = l 0 + l 1 + l 2 := rfl
@[simp] lemma faceSum_one : faceSum l 1 = l 0 + l 4 + l 5 := rfl
@[simp] lemma faceSum_two : faceSum l 2 = l 3 + l 1 + l 5 := rfl
@[simp] lemma faceSum_three : faceSum l 3 = l 3 + l 4 + l 2 := rfl
@[simp] lemma quadSum_zero : quadSum l 0 = l 0 + l 1 + l 3 + l 4 := rfl
@[simp] lemma quadSum_one : quadSum l 1 = l 1 + l 2 + l 4 + l 5 := rfl
@[simp] lemma quadSum_two : quadSum l 2 = l 2 + l 0 + l 5 + l 3 := rfl

@[simp] lemma saddle_re : (saddle l).re = -qb l / (2 * qa l) := rfl
@[simp] lemma saddle_im : (saddle l).im = 12 * √(vol2l l) / qa l := rfl

end Simp

/-- The twelve differences `Bₖ − Aᵢ` are the twelve triangle factors `ℓₐ + ℓ_b − ℓ_c` of the four
faces, each exactly once. -/
lemma quadSum_sub_faceSum (l : Fin 6 → ℝ) :
    quadSum l 0 - faceSum l 0 = l 3 + l 4 - l 2 ∧ quadSum l 1 - faceSum l 0 = l 4 + l 5 - l 0 ∧
    quadSum l 2 - faceSum l 0 = l 3 + l 5 - l 1 ∧ quadSum l 0 - faceSum l 1 = l 1 + l 3 - l 5 ∧
    quadSum l 1 - faceSum l 1 = l 1 + l 2 - l 0 ∧ quadSum l 2 - faceSum l 1 = l 2 + l 3 - l 4 ∧
    quadSum l 0 - faceSum l 2 = l 0 + l 4 - l 5 ∧ quadSum l 1 - faceSum l 2 = l 2 + l 4 - l 3 ∧
    quadSum l 2 - faceSum l 2 = l 0 + l 2 - l 1 ∧ quadSum l 0 - faceSum l 3 = l 0 + l 1 - l 2 ∧
    quadSum l 1 - faceSum l 3 = l 1 + l 5 - l 3 ∧ quadSum l 2 - faceSum l 3 = l 0 + l 5 - l 4 := by
  simp only [faceSum_zero, faceSum_one, faceSum_two, faceSum_three, quadSum_zero, quadSum_one,
    quadSum_two]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- **The discriminant of the saddle-point quadratic is `−576 vol2`.** So the saddle points are
complex conjugate exactly when the tetrahedron is Euclidean. -/
theorem disc_eq (l : Fin 6 → ℝ) : qb l ^ 2 - 4 * qa l * qc l = -576 * vol2l l := by
  simp only [qa, qb, qc, vol2l, PR.vol2, faceSum_zero, faceSum_one, faceSum_two, faceSum_three,
    quadSum_zero, quadSum_one, quadSum_two]
  ring

/-- `Q(x) = qa x² + qb x + qc`: the quartic and cubic terms cancel. -/
lemma saddleQ_eq (l : Fin 6 → ℝ) (x : ℝ) : saddleQ l x = qa l * x ^ 2 + qb l * x + qc l := by
  simp only [saddleQ, qa, qb, qc, faceSum_zero, faceSum_one, faceSum_two, faceSum_three,
    quadSum_zero, quadSum_one, quadSum_two]
  ring

/-- `Q(Aᵢ) = Aᵢ ∏ₖ (Bₖ − Aᵢ)`. -/
lemma saddleQ_faceSum (l : Fin 6 → ℝ) (i : Fin 4) :
    saddleQ l (faceSum l i) = faceSum l i *
      ((quadSum l 0 - faceSum l i) * (quadSum l 1 - faceSum l i) * (quadSum l 2 - faceSum l i)) := by
  unfold saddleQ
  fin_cases i <;> simp

/-- `Q(Bₖ) = ∏ᵢ (Bₖ − Aᵢ)`. -/
lemma saddleQ_quadSum (l : Fin 6 → ℝ) (k : Fin 3) :
    saddleQ l (quadSum l k) = (quadSum l k - faceSum l 0) * (quadSum l k - faceSum l 1) *
      (quadSum l k - faceSum l 2) * (quadSum l k - faceSum l 3) := by
  unfold saddleQ
  fin_cases k <;> simp

section Euclid

variable {l : Fin 6 → ℝ}

lemma IsEuclid.lt (h : IsEuclid l) (i : Fin 4) (k : Fin 3) : faceSum l i < quadSum l k := h.1 i k

lemma IsEuclid.vol2_pos (h : IsEuclid l) : 0 < vol2l l := h.2

/-- The edge lengths of a Euclidean tetrahedron are positive. -/
lemma IsEuclid.length_pos (h : IsEuclid l) (e : Fin 6) : 0 < l e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := quadSum_sub_faceSum l
  have := h.lt; have a00 := this 0 0; have a01 := this 0 1; have a02 := this 0 2
  have a10 := this 1 0; have a11 := this 1 1; have a12 := this 1 2
  have a20 := this 2 0; have a21 := this 2 1; have a22 := this 2 2
  have a30 := this 3 0; have a31 := this 3 1; have a32 := this 3 2
  fin_cases e <;> simp <;> linarith

lemma IsEuclid.qa_pos (h : IsEuclid l) : 0 < qa l := by
  have hp := h.length_pos
  unfold qa
  have := hp 0; have := hp 1; have := hp 2; have := hp 3; have := hp 4; have := hp 5
  positivity

lemma IsEuclid.saddle_im_pos (h : IsEuclid l) : 0 < (saddle l).im := by
  rw [saddle_im]
  have := Real.sqrt_pos.mpr h.vol2_pos
  have := h.qa_pos
  positivity

end Euclid

/-- The saddle point is a root of `qa x² + qb x + qc` (for `vol2 ≥ 0` and `qa ≠ 0`). -/
theorem saddle_root {l : Fin 6 → ℝ} (hv : 0 ≤ vol2l l) (ha : qa l ≠ 0) :
    (qa l : ℂ) * saddle l ^ 2 + qb l * saddle l + qc l = 0 := by
  have hW := Real.sq_sqrt hv
  have hd := disc_eq l
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two,
      saddle_re, saddle_im, Complex.zero_re]
    field_simp
    nlinarith [hW, hd]
  · simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, pow_two, saddle_re, saddle_im, Complex.zero_im]
    field_simp
    ring

/-- `|saddle − c|² = Q(c)/qa` for real `c`. -/
theorem normSq_saddle_sub {l : Fin 6 → ℝ} (hv : 0 ≤ vol2l l) (ha : qa l ≠ 0) (c : ℝ) :
    Complex.normSq (saddle l - c) = saddleQ l c / qa l := by
  have hW := Real.sq_sqrt hv
  have hd := disc_eq l
  rw [saddleQ_eq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, saddle_re,
    saddle_im, sub_zero]
  field_simp
  have : (qb l) ^ 2 = 4 * qa l * qc l - 576 * vol2l l := by linarith
  nlinarith [hW, this]

/-! ## The edge identity -/

/-- `2 qa · saddle = −qb + 24 i √vol2`. -/
lemma two_qa_mul_saddle {l : Fin 6 → ℝ} (ha : qa l ≠ 0) :
    (2 * qa l : ℂ) * saddle l = ⟨-qb l, 24 * √(vol2l l)⟩ := by
  apply Complex.ext
  · simp; field_simp
  · simp; field_simp; ring

/-- Real and imaginary parts of a product of four numbers with a common imaginary part. -/
lemma prod_four_common_im (r₁ r₂ r₃ r₄ b : ℝ) :
    let z : ℂ := (⟨r₁, b⟩ : ℂ) * ⟨r₂, b⟩ * ⟨r₃, b⟩ * ⟨r₄, b⟩
    z.re = r₁ * r₂ * r₃ * r₄ - b ^ 2 * (r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₂ * r₃ + r₂ * r₄ + r₃ * r₄) +
      b ^ 4 ∧
    z.im = b * (r₁ * r₂ * r₃ + r₁ * r₂ * r₄ + r₁ * r₃ * r₄ + r₂ * r₃ * r₄) -
      b ^ 3 * (r₁ + r₂ + r₃ + r₄) := by
  intro z
  simp only [z, Complex.mul_re, Complex.mul_im]
  constructor <;> ring

/-- The product attached to the edge `AB`: the faces through `AB` are `ABC, ABD` (`A₀, A₁`) and the
sums through `AB` are `B₀, B₂`. -/
noncomputable def edgeProd0 (l : Fin 6 → ℝ) : ℂ :=
  (saddle l - faceSum l 0) * (saddle l - faceSum l 1) *
    ((quadSum l 0 : ℂ) - (starRingEnd ℂ) (saddle l)) *
    ((quadSum l 2 : ℂ) - (starRingEnd ℂ) (saddle l))

/-- The positive factor of the edge identity at `AB`: four triangle factors of the faces `BCD` and
`ACD` at the opposite edge `CD`. -/
def edgeF0 (l : Fin 6 → ℝ) : ℝ := (l 3 + l 5 - l 1) * (l 1 + l 3 - l 5) * (l 3 + l 4 - l 2) *
  (l 2 + l 3 - l 4)

/-- The polynomial `−4ℓ₀² N` where `N` is the numerator of `cosDihedral` at `AB`. -/
def edgeM0 (l : Fin 6 → ℝ) : ℝ :=
  l 0 ^ 4 - l 0 ^ 2 * l 1 ^ 2 - l 0 ^ 2 * l 2 ^ 2 + 2 * l 0 ^ 2 * l 3 ^ 2 - l 0 ^ 2 * l 4 ^ 2 -
    l 0 ^ 2 * l 5 ^ 2 - l 1 ^ 2 * l 4 ^ 2 + l 1 ^ 2 * l 5 ^ 2 + l 2 ^ 2 * l 4 ^ 2 - l 2 ^ 2 * l 5 ^ 2

/-- The edge product at `AB`, scaled by `(2 qa)⁴`, as a product of four numbers with the common
imaginary part `24 √vol2`. -/
lemma edgeProd0_scaled {l : Fin 6 → ℝ} (ha : qa l ≠ 0) :
    (2 * qa l : ℂ) ^ 4 * edgeProd0 l =
      (⟨-qb l - 2 * qa l * faceSum l 0, 24 * √(vol2l l)⟩ : ℂ) *
        ⟨-qb l - 2 * qa l * faceSum l 1, 24 * √(vol2l l)⟩ *
        ⟨2 * qa l * quadSum l 0 + qb l, 24 * √(vol2l l)⟩ *
        ⟨2 * qa l * quadSum l 2 + qb l, 24 * √(vol2l l)⟩ := by
  have hs := two_qa_mul_saddle ha
  have e1 : (2 * qa l : ℂ) * (saddle l - faceSum l 0) =
      ⟨-qb l - 2 * qa l * faceSum l 0, 24 * √(vol2l l)⟩ := by
    rw [mul_sub, hs]; apply Complex.ext <;> simp
  have e2 : (2 * qa l : ℂ) * (saddle l - faceSum l 1) =
      ⟨-qb l - 2 * qa l * faceSum l 1, 24 * √(vol2l l)⟩ := by
    rw [mul_sub, hs]; apply Complex.ext <;> simp
  have hc : (2 * qa l : ℂ) * (starRingEnd ℂ) (saddle l) = ⟨-qb l, -(24 * √(vol2l l))⟩ := by
    have := congrArg (starRingEnd ℂ) hs
    rw [map_mul] at this
    simp only [map_mul, map_ofNat, Complex.conj_ofReal] at this
    rw [this]; apply Complex.ext <;> simp
  have e3 : (2 * qa l : ℂ) * ((quadSum l 0 : ℂ) - (starRingEnd ℂ) (saddle l)) =
      ⟨2 * qa l * quadSum l 0 + qb l, 24 * √(vol2l l)⟩ := by
    rw [mul_sub, hc]; apply Complex.ext <;> simp
  have e4 : (2 * qa l : ℂ) * ((quadSum l 2 : ℂ) - (starRingEnd ℂ) (saddle l)) =
      ⟨2 * qa l * quadSum l 2 + qb l, 24 * √(vol2l l)⟩ := by
    rw [mul_sub, hc]; apply Complex.ext <;> simp
  rw [← e1, ← e2, ← e3, ← e4, edgeProd0]
  ring

lemma re_im_scaled (l : Fin 6 → ℝ) (z : ℂ) :
    ((2 * qa l : ℂ) ^ 4 * z).re = 16 * qa l ^ 4 * z.re ∧
      ((2 * qa l : ℂ) ^ 4 * z).im = 16 * qa l ^ 4 * z.im := by
  rw [show (2 * qa l : ℂ) ^ 4 = ((16 * qa l ^ 4 : ℝ) : ℂ) by push_cast; ring]
  exact ⟨Complex.re_ofReal_mul _ _, Complex.im_ofReal_mul _ _⟩

/-- **Edge identity, real part**: `Re(edgeProd0) · qa² = F · M`. -/
theorem edgeProd_zero_re {l : Fin 6 → ℝ} (hv : 0 ≤ vol2l l) (ha : qa l ≠ 0) :
    (edgeProd0 l).re * qa l ^ 2 = edgeF0 l * edgeM0 l := by
  have hW := Real.sq_sqrt hv
  obtain ⟨hre, -⟩ := prod_four_common_im (-qb l - 2 * qa l * faceSum l 0)
    (-qb l - 2 * qa l * faceSum l 1) (2 * qa l * quadSum l 0 + qb l)
    (2 * qa l * quadSum l 2 + qb l) (24 * √(vol2l l))
  have hk := congrArg Complex.re (edgeProd0_scaled ha)
  rw [hre, (re_im_scaled l _).1] at hk
  have hpoly : 16 * qa l ^ 4 * (edgeProd0 l).re = 16 * qa l ^ 2 * (edgeF0 l * edgeM0 l) := by
    rw [hk]
    rw [show (24 * √(vol2l l)) ^ 4 = 24 ^ 4 * (√(vol2l l) ^ 2) ^ 2 by ring,
      show (24 * √(vol2l l)) ^ 2 = 24 ^ 2 * √(vol2l l) ^ 2 by ring, hW]
    simp only [qa, qb, edgeF0, edgeM0, vol2l, PR.vol2, faceSum_zero, faceSum_one, faceSum_two,
      faceSum_three, quadSum_zero, quadSum_one, quadSum_two]
    ring
  have : 16 * qa l ^ 2 * ((edgeProd0 l).re * qa l ^ 2) = 16 * qa l ^ 2 * (edgeF0 l * edgeM0 l) := by
    rw [← hpoly]; ring
  exact mul_left_cancel₀ (by positivity) this

/-- **Edge identity, imaginary part**: `Im(edgeProd0) · qa² = 24 ℓ₀ F √vol2`. -/
theorem edgeProd_zero_im {l : Fin 6 → ℝ} (hv : 0 ≤ vol2l l) (ha : qa l ≠ 0) :
    (edgeProd0 l).im * qa l ^ 2 = 24 * l 0 * edgeF0 l * √(vol2l l) := by
  have hW := Real.sq_sqrt hv
  obtain ⟨-, him⟩ := prod_four_common_im (-qb l - 2 * qa l * faceSum l 0)
    (-qb l - 2 * qa l * faceSum l 1) (2 * qa l * quadSum l 0 + qb l)
    (2 * qa l * quadSum l 2 + qb l) (24 * √(vol2l l))
  have hk := congrArg Complex.im (edgeProd0_scaled ha)
  rw [him, (re_im_scaled l _).2] at hk
  have hpoly : 16 * qa l ^ 4 * (edgeProd0 l).im =
      16 * qa l ^ 2 * (24 * l 0 * edgeF0 l * √(vol2l l)) := by
    rw [hk]
    rw [show (24 * √(vol2l l)) ^ 3 = 24 ^ 3 * √(vol2l l) ^ 2 * √(vol2l l) by ring, hW]
    simp only [qa, qb, edgeF0, vol2l, PR.vol2, faceSum_zero, faceSum_one, faceSum_two,
      faceSum_three, quadSum_zero, quadSum_one, quadSum_two]
    ring
  have : 16 * qa l ^ 2 * ((edgeProd0 l).im * qa l ^ 2) =
      16 * qa l ^ 2 * (24 * l 0 * edgeF0 l * √(vol2l l)) := by
    rw [← hpoly]; ring
  exact mul_left_cancel₀ (by positivity) this

/-- `16 · area²` of a triangle with sides `a, b, c` (Heron), as a product of four factors. -/
def heron (a b c : ℝ) : ℝ := (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c)

/-- The product of `16 · area²` of the two faces `ABC, ABD` through `AB`. -/
def edgeH0 (l : Fin 6 → ℝ) : ℝ := heron (l 0) (l 1) (l 2) * heron (l 0) (l 4) (l 5)

/-- `M² + 576 ℓ₀² vol2 = 16² · area(ABC)² · area(ABD)²`: the identity `sin² φ + cos² φ = 1` at
`AB`, with `sin φ = 3 V ℓ₀ / (2 · area · area)`. -/
lemma edgeM0_sq_add (l : Fin 6 → ℝ) : edgeM0 l ^ 2 + 576 * l 0 ^ 2 * vol2l l = edgeH0 l := by
  simp only [edgeM0, edgeH0, heron, vol2l, PR.vol2]
  ring

section Euclid

variable {l : Fin 6 → ℝ}

lemma IsEuclid.edgeF0_pos (h : IsEuclid l) : 0 < edgeF0 l := by
  obtain ⟨h1, -, h3, h4, -, h6, -, -, -, -, -, -⟩ := quadSum_sub_faceSum l
  have a := sub_pos.mpr (h.lt 0 0); have b := sub_pos.mpr (h.lt 0 2)
  have c := sub_pos.mpr (h.lt 1 0); have d := sub_pos.mpr (h.lt 1 2)
  rw [h1] at a; rw [h3] at b; rw [h4] at c; rw [h6] at d
  unfold edgeF0
  positivity

lemma IsEuclid.heron_pos_zero (h : IsEuclid l) : 0 < heron (l 0) (l 1) (l 2) := by
  obtain ⟨-, -, -, -, h5, -, -, -, h9, h10, -, -⟩ := quadSum_sub_faceSum l
  have a := sub_pos.mpr (h.lt 1 1); have b := sub_pos.mpr (h.lt 2 2)
  have c := sub_pos.mpr (h.lt 3 0)
  rw [h5] at a; rw [h9] at b; rw [h10] at c
  have hp := h.length_pos
  have := hp 0; have := hp 1; have := hp 2
  unfold heron
  have : 0 < -l 0 + l 1 + l 2 := by linarith
  have : 0 < l 0 - l 1 + l 2 := by linarith
  positivity

lemma IsEuclid.heron_pos_one (h : IsEuclid l) : 0 < heron (l 0) (l 4) (l 5) := by
  obtain ⟨-, h2, -, -, -, -, h7, -, -, -, -, h12⟩ := quadSum_sub_faceSum l
  have a := sub_pos.mpr (h.lt 0 1); have b := sub_pos.mpr (h.lt 2 0)
  have c := sub_pos.mpr (h.lt 3 2)
  rw [h2] at a; rw [h7] at b; rw [h12] at c
  have hp := h.length_pos
  have := hp 0; have := hp 4; have := hp 5
  unfold heron
  have : 0 < -l 0 + l 4 + l 5 := by linarith
  have : 0 < l 0 - l 4 + l 5 := by linarith
  positivity

lemma IsEuclid.edgeH0_pos (h : IsEuclid l) : 0 < edgeH0 l :=
  mul_pos h.heron_pos_zero h.heron_pos_one

/-- The core's `cosDihedral` at `AB` is `−M/√H`. -/
lemma IsEuclid.cosDihedral_zero (h : IsEuclid l) :
    PR.cosDihedral (l 0) (l 2) (l 1) (l 4) (l 5) (l 3) = -edgeM0 l / √(edgeH0 l) := by
  have h0 := (h.length_pos 0).ne'
  unfold PR.cosDihedral
  simp only
  have hnum : (l 2 ^ 2 + l 4 ^ 2 - l 3 ^ 2) / 2 -
      (l 2 ^ 2 + l 0 ^ 2 - l 1 ^ 2) / (2 * l 0) * ((l 4 ^ 2 + l 0 ^ 2 - l 5 ^ 2) / (2 * l 0)) =
      -edgeM0 l / (4 * l 0 ^ 2) := by
    unfold edgeM0; field_simp; ring
  have hden : (l 2 ^ 2 - ((l 2 ^ 2 + l 0 ^ 2 - l 1 ^ 2) / (2 * l 0)) ^ 2) *
      (l 4 ^ 2 - ((l 4 ^ 2 + l 0 ^ 2 - l 5 ^ 2) / (2 * l 0)) ^ 2) = edgeH0 l / (4 * l 0 ^ 2) ^ 2 := by
    unfold edgeH0 heron; field_simp; ring
  rw [hnum, hden, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  have : 0 < √(edgeH0 l) := Real.sqrt_pos.mpr h.edgeH0_pos
  field_simp

lemma IsEuclid.edgeProd0_im_pos (h : IsEuclid l) : 0 < (edgeProd0 l).im := by
  have hq := h.qa_pos
  have him := edgeProd_zero_im h.vol2_pos.le hq.ne'
  have : 0 < 24 * l 0 * edgeF0 l * √(vol2l l) := by
    have := h.length_pos 0; have := h.edgeF0_pos; have := Real.sqrt_pos.mpr h.vol2_pos
    positivity
  rw [← him] at this
  exact pos_of_mul_pos_left this (by positivity)

/-- `‖edgeProd0‖ · qa² = F √H`. -/
lemma IsEuclid.norm_edgeProd0 (h : IsEuclid l) : ‖edgeProd0 l‖ * qa l ^ 2 = edgeF0 l * √(edgeH0 l) := by
  have hq := h.qa_pos
  have hre := edgeProd_zero_re h.vol2_pos.le hq.ne'
  have him := edgeProd_zero_im h.vol2_pos.le hq.ne'
  have hW := Real.sq_sqrt h.vol2_pos.le
  have hF := h.edgeF0_pos
  have hsq : (‖edgeProd0 l‖ * qa l ^ 2) ^ 2 = (edgeF0 l * √(edgeH0 l)) ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply, mul_pow, Real.sq_sqrt h.edgeH0_pos.le,
      ← edgeM0_sq_add]
    have e : (edgeProd0 l).re * (edgeProd0 l).re + (edgeProd0 l).im * (edgeProd0 l).im =
        ((edgeProd0 l).re * qa l ^ 2) ^ 2 / (qa l ^ 2) ^ 2 +
          ((edgeProd0 l).im * qa l ^ 2) ^ 2 / (qa l ^ 2) ^ 2 := by
      field_simp
    rw [e, hre, him]
    field_simp
    rw [hW]
    ring
  have h1 : 0 ≤ ‖edgeProd0 l‖ * qa l ^ 2 := by positivity
  have h2 : 0 ≤ edgeF0 l * √(edgeH0 l) := by positivity
  exact (pow_left_inj₀ h1 h2 two_ne_zero).mp hsq

/-- **The argument of the edge product at `AB` is the exterior dihedral angle at `AB`.** -/
theorem IsEuclid.arg_edgeProd0 (h : IsEuclid l) : Complex.arg (edgeProd0 l) = PR.extAngles l 0 := by
  have him := h.edgeProd0_im_pos
  have hne : edgeProd0 l ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at him; exact lt_irrefl 0 him
  have hq := h.qa_pos
  have hcos : Real.cos (Complex.arg (edgeProd0 l)) = edgeM0 l / √(edgeH0 l) := by
    rw [Complex.cos_arg hne]
    have hn := h.norm_edgeProd0
    have hre := edgeProd_zero_re h.vol2_pos.le hq.ne'
    have hF := h.edgeF0_pos
    have hH : 0 < √(edgeH0 l) := Real.sqrt_pos.mpr h.edgeH0_pos
    have hnorm : ‖edgeProd0 l‖ = edgeF0 l * √(edgeH0 l) / qa l ^ 2 := by
      field_simp; linarith
    have hre' : (edgeProd0 l).re = edgeF0 l * edgeM0 l / qa l ^ 2 := by
      field_simp; linarith
    rw [hnorm, hre']
    field_simp
  have harg0 : 0 ≤ Complex.arg (edgeProd0 l) := Complex.arg_nonneg_iff.mpr him.le
  have hargπ : Complex.arg (edgeProd0 l) ≤ π := Complex.arg_le_pi _
  have e1 : Complex.arg (edgeProd0 l) = Real.arccos (edgeM0 l / √(edgeH0 l)) := by
    rw [← hcos, Real.arccos_cos harg0 hargπ]
  rw [e1]
  simp only [PR.extAngles, PR.dihedral, Matrix.cons_val_zero]
  rw [h.cosDihedral_zero, neg_div, Real.arccos_neg]
  ring

end Euclid

/-! ## All six edges, by the symmetry of the tetrahedron -/

/-- For each edge `e`, a relabelling of the edges induced by a permutation of the vertices that
moves `AB` to `e`: `l ∘ edgePerm e` has `e` in the place of `AB`, with the core's argument order of
`dihedral` at `e`. -/
def edgePerm : Fin 6 → Fin 6 → Fin 6 :=
  ![![0, 1, 2, 3, 4, 5], ![1, 2, 0, 4, 5, 3], ![2, 0, 1, 5, 3, 4], ![3, 4, 2, 0, 1, 5],
    ![4, 5, 0, 1, 2, 3], ![5, 4, 0, 2, 1, 3]]

/-- The two faces through each edge. -/
def edgeFaces : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (3, 2), (1, 3), (1, 2)]

/-- The two sums `Bₖ` through each edge. -/
def edgeQuads : Fin 6 → Fin 3 × Fin 3 := ![(0, 2), (1, 0), (2, 1), (0, 2), (1, 0), (1, 2)]

/-- The edge product at the edge `e`: `(s − A_f)(s − A_f')(B_q − s̄)(B_q' − s̄)` over the two faces
and the two sums through `e`. -/
noncomputable def edgeProd (l : Fin 6 → ℝ) (e : Fin 6) : ℂ :=
  (saddle l - faceSum l (edgeFaces e).1) * (saddle l - faceSum l (edgeFaces e).2) *
    ((quadSum l (edgeQuads e).1 : ℂ) - (starRingEnd ℂ) (saddle l)) *
    ((quadSum l (edgeQuads e).2 : ℂ) - (starRingEnd ℂ) (saddle l))

lemma qa_comp_edgePerm (l : Fin 6 → ℝ) (e : Fin 6) : qa (l ∘ edgePerm e) = qa l := by
  fin_cases e <;> simp [qa, edgePerm] <;> ring

lemma qb_comp_edgePerm (l : Fin 6 → ℝ) (e : Fin 6) : qb (l ∘ edgePerm e) = qb l := by
  fin_cases e <;> simp [qb, edgePerm] <;> ring

lemma vol2l_comp_edgePerm (l : Fin 6 → ℝ) (e : Fin 6) : vol2l (l ∘ edgePerm e) = vol2l l := by
  fin_cases e <;> simp [vol2l, PR.vol2, edgePerm] <;> ring

lemma saddle_comp_edgePerm (l : Fin 6 → ℝ) (e : Fin 6) : saddle (l ∘ edgePerm e) = saddle l := by
  unfold saddle
  rw [qa_comp_edgePerm, qb_comp_edgePerm, vol2l_comp_edgePerm]

/-- How the face perimeters move under `edgePerm e`. -/
def facePerm : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![3, 2, 1, 0], ![1, 3, 2, 0], ![1, 2, 3, 0]]

/-- How the sums `Bₖ` move under `edgePerm e`. -/
def quadPerm : Fin 6 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1], ![0, 1, 2], ![1, 2, 0], ![1, 0, 2]]

lemma faceSum_comp_edgePerm (l : Fin 6 → ℝ) (e : Fin 6) (i : Fin 4) :
    faceSum (l ∘ edgePerm e) i = faceSum l (facePerm e i) := by
  fin_cases e <;> fin_cases i <;> simp [edgePerm, facePerm] <;> ring

lemma quadSum_comp_edgePerm (l : Fin 6 → ℝ) (e : Fin 6) (k : Fin 3) :
    quadSum (l ∘ edgePerm e) k = quadSum l (quadPerm e k) := by
  fin_cases e <;> fin_cases k <;> simp [edgePerm, quadPerm] <;> ring

lemma IsEuclid.comp_edgePerm {l : Fin 6 → ℝ} (h : IsEuclid l) (e : Fin 6) :
    IsEuclid (l ∘ edgePerm e) := by
  refine ⟨fun i k => ?_, by rw [vol2l_comp_edgePerm]; exact h.vol2_pos⟩
  rw [faceSum_comp_edgePerm, quadSum_comp_edgePerm]
  exact h.lt _ _

lemma edgeProd0_comp_edgePerm (l : Fin 6 → ℝ) (e : Fin 6) :
    edgeProd0 (l ∘ edgePerm e) = edgeProd l e := by
  unfold edgeProd0 edgeProd
  rw [saddle_comp_edgePerm, faceSum_comp_edgePerm, faceSum_comp_edgePerm, quadSum_comp_edgePerm,
    quadSum_comp_edgePerm]
  fin_cases e <;> simp [facePerm, quadPerm, edgeFaces, edgeQuads]

lemma extAngles_comp_edgePerm (l : Fin 6 → ℝ) (e : Fin 6) :
    PR.extAngles (l ∘ edgePerm e) 0 = PR.extAngles l e := by
  fin_cases e <;> simp [PR.extAngles, edgePerm]

/-- **At every edge, the argument of the edge product is the exterior dihedral angle.** -/
theorem IsEuclid.arg_edgeProd {l : Fin 6 → ℝ} (h : IsEuclid l) (e : Fin 6) :
    Complex.arg (edgeProd l e) = PR.extAngles l e := by
  rw [← edgeProd0_comp_edgePerm, (h.comp_edgePerm e).arg_edgeProd0, extAngles_comp_edgePerm]

lemma IsEuclid.edgeProd_im_pos {l : Fin 6 → ℝ} (h : IsEuclid l) (e : Fin 6) :
    0 < (edgeProd l e).im := by
  rw [← edgeProd0_comp_edgePerm]
  exact (h.comp_edgePerm e).edgeProd0_im_pos

/-! ## Arguments and the critical point -/

lemma arg_pos_of_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < Complex.arg z := by
  refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) fun h => ?_
  rw [eq_comm, Complex.arg_eq_zero_iff] at h; linarith [h.2]

lemma arg_lt_pi_of_im_pos {z : ℂ} (hz : 0 < z.im) : Complex.arg z < π := by
  refine lt_of_le_of_ne (Complex.arg_le_pi z) fun h => ?_
  rw [Complex.arg_eq_pi_iff] at h; linarith [h.2]

/-- If `x`, `y` and `x y` all lie in the upper half-plane, then `arg (x y) = arg x + arg y`. -/
lemma arg_mul_of_im_pos {x y : ℂ} (hx : 0 < x.im) (hy : 0 < y.im) (hxy : 0 < (x * y).im) :
    Complex.arg (x * y) = Complex.arg x + Complex.arg y := by
  have hx0 : x ≠ 0 := fun h => by rw [h, Complex.zero_im] at hx; exact lt_irrefl 0 hx
  have hy0 : y ≠ 0 := fun h => by rw [h, Complex.zero_im] at hy; exact lt_irrefl 0 hy
  have h := Complex.arg_mul_coe_angle hx0 hy0
  rw [← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  have a1 := Complex.arg_nonneg_iff.mpr hxy.le
  have a2' := arg_lt_pi_of_im_pos hxy
  have b1' := arg_pos_of_im_pos hx
  have b2' := arg_lt_pi_of_im_pos hx
  have c1' := arg_pos_of_im_pos hy
  have c2' := arg_lt_pi_of_im_pos hy
  have hk1 : (k : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have hk2 : (-1 : ℝ) < k := by nlinarith [Real.pi_pos]
  have hk1' : k < 1 := by exact_mod_cast hk1
  have hk2' : -1 < k := by exact_mod_cast hk2
  have : k = 0 := by omega
  rw [this] at hk
  simp at hk
  linarith

/-- `αᵢ = arg (s − Aᵢ)`, the angle of the saddle seen from the face perimeter `Aᵢ`. -/
noncomputable def angA (l : Fin 6 → ℝ) (i : Fin 4) : ℝ := Complex.arg (saddle l - faceSum l i)

/-- `βₖ = arg (Bₖ − s̄) = −arg (Bₖ − s)`. -/
noncomputable def angB (l : Fin 6 → ℝ) (k : Fin 3) : ℝ :=
  Complex.arg ((quadSum l k : ℂ) - (starRingEnd ℂ) (saddle l))

section Euclid

variable {l : Fin 6 → ℝ}

lemma IsEuclid.im_saddle_sub (h : IsEuclid l) (c : ℝ) : 0 < (saddle l - c).im := by
  simpa using h.saddle_im_pos

lemma IsEuclid.im_sub_conj_saddle (h : IsEuclid l) (c : ℝ) :
    0 < ((c : ℂ) - (starRingEnd ℂ) (saddle l)).im := by
  simpa using h.saddle_im_pos

/-- `(s − A)(B − s̄)` lies in the upper half-plane when `A < B`: its imaginary part is
`Im s · (B − A)`. -/
lemma IsEuclid.im_pair_pos (h : IsEuclid l) {a b : ℝ} (hab : a < b) :
    0 < ((saddle l - a) * ((b : ℂ) - (starRingEnd ℂ) (saddle l))).im := by
  have : ((saddle l - a) * ((b : ℂ) - (starRingEnd ℂ) (saddle l))).im =
      (saddle l).im * (b - a) := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [this]
  exact mul_pos h.saddle_im_pos (sub_pos.mpr hab)

/-- **At every edge, the four angles add up to the exterior dihedral angle.** -/
theorem IsEuclid.angle_sum_edge (h : IsEuclid l) (e : Fin 6) :
    angA l (edgeFaces e).1 + angB l (edgeQuads e).1 + (angA l (edgeFaces e).2 + angB l (edgeQuads e).2)
      = PR.extAngles l e := by
  have hx := h.im_pair_pos (h.lt (edgeFaces e).1 (edgeQuads e).1)
  have hy := h.im_pair_pos (h.lt (edgeFaces e).2 (edgeQuads e).2)
  have hprod : (saddle l - faceSum l (edgeFaces e).1) *
      ((quadSum l (edgeQuads e).1 : ℂ) - (starRingEnd ℂ) (saddle l)) *
      ((saddle l - faceSum l (edgeFaces e).2) *
        ((quadSum l (edgeQuads e).2 : ℂ) - (starRingEnd ℂ) (saddle l))) = edgeProd l e := by
    unfold edgeProd; ring
  have hxy : 0 < ((saddle l - faceSum l (edgeFaces e).1) *
      ((quadSum l (edgeQuads e).1 : ℂ) - (starRingEnd ℂ) (saddle l)) *
      ((saddle l - faceSum l (edgeFaces e).2) *
        ((quadSum l (edgeQuads e).2 : ℂ) - (starRingEnd ℂ) (saddle l)))).im := by
    rw [hprod]; exact h.edgeProd_im_pos e
  rw [← h.arg_edgeProd e, ← hprod, arg_mul_of_im_pos hx hy hxy,
    arg_mul_of_im_pos (h.im_saddle_sub _) (h.im_sub_conj_saddle _) hx,
    arg_mul_of_im_pos (h.im_saddle_sub _) (h.im_sub_conj_saddle _) hy]
  rfl

lemma IsEuclid.extAngles_lt_pi (h : IsEuclid l) (e : Fin 6) : PR.extAngles l e < π := by
  rw [← h.arg_edgeProd e]; exact arg_lt_pi_of_im_pos (h.edgeProd_im_pos e)

lemma IsEuclid.angA_pos (h : IsEuclid l) (i : Fin 4) : 0 < angA l i :=
  arg_pos_of_im_pos (h.im_saddle_sub _)

lemma IsEuclid.angB_pos (h : IsEuclid l) (k : Fin 3) : 0 < angB l k :=
  arg_pos_of_im_pos (h.im_sub_conj_saddle _)

/-- The angle sums give `Σ αᵢ + Σ βₖ < 2π`: summing the six edge identities counts every `αᵢ`
three times and every `βₖ` four times, and every exterior angle is below `π`. -/
lemma IsEuclid.sum_angles_lt (h : IsEuclid l) :
    angA l 0 + angA l 1 + angA l 2 + angA l 3 + (angB l 0 + angB l 1 + angB l 2) < 2 * π := by
  have e0 := h.angle_sum_edge 0; have e1 := h.angle_sum_edge 1; have e2 := h.angle_sum_edge 2
  have e3 := h.angle_sum_edge 3; have e4 := h.angle_sum_edge 4; have e5 := h.angle_sum_edge 5
  simp [edgeFaces, edgeQuads] at e0 e1 e2 e3 e4 e5
  have t0 := h.extAngles_lt_pi 0; have t1 := h.extAngles_lt_pi 1; have t2 := h.extAngles_lt_pi 2
  have t3 := h.extAngles_lt_pi 3; have t4 := h.extAngles_lt_pi 4; have t5 := h.extAngles_lt_pi 5
  have := h.angA_pos 0; have := h.angA_pos 1; have := h.angA_pos 2; have := h.angA_pos 3
  have := h.angB_pos 0; have := h.angB_pos 1; have := h.angB_pos 2
  linarith

end Euclid

/-! ## The phase function at the saddle -/

open Complex in
/-- The phase `ψ(x) = x log x − Σᵢ (x − Aᵢ) log(x − Aᵢ) − Σₖ (Bₖ − x) log(Bₖ − x) + iπx`, the
Stirling exponent of Racah's summand (principal logarithms). -/
noncomputable def phase (l : Fin 6 → ℝ) (x : ℂ) : ℂ :=
  x * log x - ∑ i, (x - faceSum l i) * log (x - faceSum l i) -
    ∑ k, ((quadSum l k : ℂ) - x) * log ((quadSum l k : ℂ) - x) + π * I * x

open Complex in
/-- `ψ'(x) = log x − Σᵢ log(x − Aᵢ) + Σₖ log(Bₖ − x) + iπ`. -/
noncomputable def dphase (l : Fin 6 → ℝ) (x : ℂ) : ℂ :=
  log x - ∑ i, log (x - faceSum l i) + ∑ k, log ((quadSum l k : ℂ) - x) + π * I

/-- `ψ''(x) = 1/x − Σᵢ 1/(x − Aᵢ) + Σₖ 1/(x − Bₖ)`. -/
noncomputable def d2phase (l : Fin 6 → ℝ) (x : ℂ) : ℂ :=
  1 / x - ∑ i, 1 / (x - faceSum l i) + ∑ k, 1 / (x - quadSum l k)

/-- Euler's relation for the homogeneous phase: `ψ(x) − x ψ'(x) = Σ Aᵢ log(x − Aᵢ) − Σ Bₖ log(Bₖ − x)`. -/
lemma phase_sub_mul_dphase (l : Fin 6 → ℝ) (x : ℂ) :
    phase l x - x * dphase l x = ∑ i, (faceSum l i : ℂ) * Complex.log (x - faceSum l i) -
      ∑ k, (quadSum l k : ℂ) * Complex.log ((quadSum l k : ℂ) - x) := by
  simp only [phase, dphase, Fin.sum_univ_four, Fin.sum_univ_three]
  ring

/-- The saddle-point equation in product form: `s ∏ₖ (Bₖ − s) = −∏ᵢ (s − Aᵢ)`. -/
lemma saddle_prod_eq {l : Fin 6 → ℝ} (hv : 0 ≤ vol2l l) (ha : qa l ≠ 0) :
    saddle l * (((quadSum l 0 : ℂ) - saddle l) * ((quadSum l 1 : ℂ) - saddle l) *
      ((quadSum l 2 : ℂ) - saddle l)) =
      -((saddle l - faceSum l 0) * (saddle l - faceSum l 1) * (saddle l - faceSum l 2) *
        (saddle l - faceSum l 3)) := by
  have h := saddle_root hv ha
  have hq : ∀ x : ℂ, x * (((quadSum l 0 : ℂ) - x) * ((quadSum l 1 : ℂ) - x) * ((quadSum l 2 : ℂ) - x)) +
      (x - faceSum l 0) * (x - faceSum l 1) * (x - faceSum l 2) * (x - faceSum l 3) =
      (qa l : ℂ) * x ^ 2 + qb l * x + qc l := by
    intro x
    simp only [qa, qb, qc, faceSum_zero, faceSum_one, faceSum_two, faceSum_three, quadSum_zero,
      quadSum_one, quadSum_two]
    push_cast; ring
  linear_combination hq (saddle l) + h

section Euclid

variable {l : Fin 6 → ℝ}

lemma IsEuclid.saddle_ne_zero (h : IsEuclid l) : saddle l ≠ 0 := fun h0 => by
  have := h.saddle_im_pos; rw [h0, Complex.zero_im] at this; exact lt_irrefl 0 this

lemma IsEuclid.saddle_sub_ne_zero (h : IsEuclid l) (c : ℝ) : saddle l - c ≠ 0 := fun h0 => by
  have := h.im_saddle_sub c; rw [h0, Complex.zero_im] at this; exact lt_irrefl 0 this

lemma IsEuclid.sub_saddle_ne_zero (h : IsEuclid l) (c : ℝ) : (c : ℂ) - saddle l ≠ 0 := fun h0 => by
  have := h.im_saddle_sub c
  rw [← neg_sub, h0, neg_zero, Complex.zero_im] at this; exact lt_irrefl 0 this

lemma IsEuclid.arg_sub_saddle (h : IsEuclid l) (k : Fin 3) :
    Complex.arg ((quadSum l k : ℂ) - saddle l) = -angB l k := by
  unfold angB
  have him : ((quadSum l k : ℂ) - saddle l).im < 0 := by simpa using h.saddle_im_pos
  have : (quadSum l k : ℂ) - (starRingEnd ℂ) (saddle l) =
      (starRingEnd ℂ) ((quadSum l k : ℂ) - saddle l) := by simp
  rw [this, Complex.arg_conj, ite_eq_right (fun hpi => by
    rw [Complex.arg_eq_pi_iff] at hpi; linarith [hpi.2])]
  ring

/-- The sum of the angles: `Σ αᵢ + Σ βₖ − arg s = π`. -/
theorem IsEuclid.angle_sum_saddle (h : IsEuclid l) :
    angA l 0 + angA l 1 + angA l 2 + angA l 3 + (angB l 0 + angB l 1 + angB l 2) -
      Complex.arg (saddle l) = π := by
  have hq := h.qa_pos
  have hp := saddle_prod_eq h.vol2_pos.le hq.ne'
  have hs := h.saddle_ne_zero
  have hA := h.saddle_sub_ne_zero
  have hB := h.sub_saddle_ne_zero
  have hL := congrArg (fun z => (Complex.arg z : Real.Angle)) hp
  rw [Complex.arg_mul_coe_angle hs (by simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨⟨hB _, hB _⟩, hB _⟩),
    Complex.arg_mul_coe_angle (by simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨hB _, hB _⟩) (hB _),
    Complex.arg_mul_coe_angle (hB _) (hB _),
    Complex.arg_neg_coe_angle (by simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨⟨⟨hA _, hA _⟩, hA _⟩, hA _⟩),
    Complex.arg_mul_coe_angle (by simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨⟨hA _, hA _⟩, hA _⟩) (hA _),
    Complex.arg_mul_coe_angle (by simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨hA _, hA _⟩) (hA _),
    Complex.arg_mul_coe_angle (hA _) (hA _)] at hL
  rw [h.arg_sub_saddle 0, h.arg_sub_saddle 1, h.arg_sub_saddle 2] at hL
  simp only [← Real.Angle.coe_add] at hL
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hL
  obtain ⟨k, hk⟩ := hL
  have hsum := h.sum_angles_lt
  have a0 := h.angA_pos 0; have a1 := h.angA_pos 1; have a2 := h.angA_pos 2
  have a3 := h.angA_pos 3; have b0 := h.angB_pos 0; have b1 := h.angB_pos 1
  have b2 := h.angB_pos 2
  have hs1 := arg_pos_of_im_pos h.saddle_im_pos
  have hs2 := arg_lt_pi_of_im_pos h.saddle_im_pos
  simp only [angA] at a0 a1 a2 a3 hsum hk ⊢
  have hk1 : (k : ℝ) < 0 := by nlinarith [Real.pi_pos]
  have hk2 : (-2 : ℝ) < k := by nlinarith [Real.pi_pos]
  have hk1' : k < 0 := by exact_mod_cast hk1
  have hk2' : -2 < k := by exact_mod_cast hk2
  have : k = -1 := by omega
  rw [this] at hk
  push_cast at hk
  linarith

/-- **The saddle point is a critical point of the phase** (principal branches): `ψ'(s) = 0`. -/
theorem IsEuclid.dphase_saddle (h : IsEuclid l) : dphase l (saddle l) = 0 := by
  have hq := h.qa_pos
  have hp := saddle_prod_eq h.vol2_pos.le hq.ne'
  have hs := h.saddle_ne_zero
  have hA := h.saddle_sub_ne_zero
  have hB := h.sub_saddle_ne_zero
  apply Complex.ext
  · -- real part: `‖s‖ ∏ ‖Bₖ − s‖ = ∏ ‖s − Aᵢ‖`
    have hn := congrArg (fun z => ‖z‖) hp
    simp only [norm_mul, norm_neg] at hn
    have p0 : ‖saddle l‖ ≠ 0 := (norm_pos_iff.mpr hs).ne'
    have pb : ∀ k : Fin 3, ‖(quadSum l k : ℂ) - saddle l‖ ≠ 0 := fun k => (norm_pos_iff.mpr (hB _)).ne'
    have pa : ∀ i : Fin 4, ‖saddle l - faceSum l i‖ ≠ 0 := fun i => (norm_pos_iff.mpr (hA _)).ne'
    have hlog := congrArg Real.log hn
    rw [Real.log_mul p0 (mul_ne_zero (mul_ne_zero (pb 0) (pb 1)) (pb 2)),
      Real.log_mul (mul_ne_zero (pb 0) (pb 1)) (pb 2), Real.log_mul (pb 0) (pb 1),
      Real.log_mul (mul_ne_zero (mul_ne_zero (pa 0) (pa 1)) (pa 2)) (pa 3),
      Real.log_mul (mul_ne_zero (pa 0) (pa 1)) (pa 2), Real.log_mul (pa 0) (pa 1)] at hlog
    simp only [dphase, Fin.sum_univ_four, Fin.sum_univ_three, Complex.add_re, Complex.sub_re,
      Complex.log_re, Complex.zero_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    linarith
  · simp only [dphase, Fin.sum_univ_four, Fin.sum_univ_three, Complex.add_im, Complex.sub_im,
      Complex.log_im, Complex.zero_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [h.arg_sub_saddle 0, h.arg_sub_saddle 1, h.arg_sub_saddle 2]
    have := h.angle_sum_saddle
    simp only [angA] at this
    linarith

/-- The value of the phase at the saddle: `ψ(s) = Σ Aᵢ log(s − Aᵢ) − Σ Bₖ log(Bₖ − s)`. -/
theorem IsEuclid.phase_saddle (h : IsEuclid l) :
    phase l (saddle l) = ∑ i, (faceSum l i : ℂ) * Complex.log (saddle l - faceSum l i) -
      ∑ k, (quadSum l k : ℂ) * Complex.log ((quadSum l k : ℂ) - saddle l) := by
  rw [← phase_sub_mul_dphase, h.dphase_saddle, mul_zero, sub_zero]

/-- **The imaginary part of the saddle value is the Regge action**: `Im ψ(s) = Σₑ ℓₑ θₑ`. -/
theorem IsEuclid.im_phase_saddle (h : IsEuclid l) :
    (phase l (saddle l)).im = PR.reggeAction l := by
  rw [h.phase_saddle]
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, Complex.sub_im, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.log_im, zero_mul, add_zero]
  rw [h.arg_sub_saddle 0, h.arg_sub_saddle 1, h.arg_sub_saddle 2]
  have e0 := h.angle_sum_edge 0; have e1 := h.angle_sum_edge 1; have e2 := h.angle_sum_edge 2
  have e3 := h.angle_sum_edge 3; have e4 := h.angle_sum_edge 4; have e5 := h.angle_sum_edge 5
  simp [edgeFaces, edgeQuads] at e0 e1 e2 e3 e4 e5
  simp only [PR.reggeAction, Fin.sum_univ_six]
  rw [← e0, ← e1, ← e2, ← e3, ← e4, ← e5]
  simp only [angA, faceSum_zero, faceSum_one, faceSum_two, faceSum_three, quadSum_zero,
    quadSum_one, quadSum_two]
  ring

end Euclid

/-! ## The real part of the saddle value and the second derivative -/

/-- The exponential rate of the inverse of Racah's prefactor `∏ Δ(face)`:
`½ (Σᵢ Aᵢ log Aᵢ − Σᵢ Σₖ (Bₖ − Aᵢ) log(Bₖ − Aᵢ))`. By `quadSum_sub_faceSum` the twelve numbers
`Bₖ − Aᵢ` are the triangle factors, so this is `½ Σ_faces (P log P − Σ t log t)`
(`prefactorRate_eq_faces`). -/
noncomputable def prefactorRate (l : Fin 6 → ℝ) : ℝ :=
  (1 / 2) * (∑ i, faceSum l i * Real.log (faceSum l i) -
    ∑ i, ∑ k, (quadSum l k - faceSum l i) * Real.log (quadSum l k - faceSum l i))

/-- `P log P − Σ t log t` for a triangle with sides `a, b, c` (perimeter `P`, triangle factors
`t = P − 2a, P − 2b, P − 2c`). -/
noncomputable def faceRate (a b c : ℝ) : ℝ :=
  (a + b + c) * Real.log (a + b + c) - (-a + b + c) * Real.log (-a + b + c) -
    (a - b + c) * Real.log (a - b + c) - (a + b - c) * Real.log (a + b - c)

lemma prefactorRate_eq_faces (l : Fin 6 → ℝ) :
    prefactorRate l = (1 / 2) * (faceRate (l 0) (l 1) (l 2) + faceRate (l 0) (l 4) (l 5) +
      faceRate (l 3) (l 1) (l 5) + faceRate (l 3) (l 4) (l 2)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := quadSum_sub_faceSum l
  simp only [prefactorRate, Fin.sum_univ_four, Fin.sum_univ_three]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  simp only [faceRate, faceSum_zero, faceSum_one, faceSum_two, faceSum_three]
  ring_nf

section Euclid

variable {l : Fin 6 → ℝ}

lemma IsEuclid.faceSum_pos (h : IsEuclid l) (i : Fin 4) : 0 < faceSum l i := by
  have hp := h.length_pos
  have := hp 0; have := hp 1; have := hp 2; have := hp 3; have := hp 4; have := hp 5
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, faceSum_zero, faceSum_one,
    faceSum_two, faceSum_three] <;> positivity

lemma IsEuclid.log_norm_saddle_sub_face (h : IsEuclid l) (i : Fin 4) :
    Real.log ‖saddle l - faceSum l i‖ = (1 / 2) * (Real.log (faceSum l i) +
      Real.log (quadSum l 0 - faceSum l i) + Real.log (quadSum l 1 - faceSum l i) +
      Real.log (quadSum l 2 - faceSum l i) - Real.log (qa l)) := by
  have hq := h.qa_pos
  have hn := normSq_saddle_sub h.vol2_pos.le hq.ne' (faceSum l i)
  rw [saddleQ_faceSum] at hn
  have ha := h.faceSum_pos i
  have d0 := sub_pos.mpr (h.lt i 0); have d1 := sub_pos.mpr (h.lt i 1)
  have d2 := sub_pos.mpr (h.lt i 2)
  have hsq : Real.log ‖saddle l - faceSum l i‖ = (1 / 2) * Real.log (Complex.normSq (saddle l - faceSum l i)) := by
    rw [← Complex.sq_norm, Real.log_pow]; push_cast; ring
  rw [hsq, hn, Real.log_div (by positivity) hq.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) d2.ne', Real.log_mul d0.ne' d1.ne']
  ring

lemma IsEuclid.log_norm_quad_sub_saddle (h : IsEuclid l) (k : Fin 3) :
    Real.log ‖(quadSum l k : ℂ) - saddle l‖ = (1 / 2) * (Real.log (quadSum l k - faceSum l 0) +
      Real.log (quadSum l k - faceSum l 1) + Real.log (quadSum l k - faceSum l 2) +
      Real.log (quadSum l k - faceSum l 3) - Real.log (qa l)) := by
  have hq := h.qa_pos
  have hn := normSq_saddle_sub h.vol2_pos.le hq.ne' (quadSum l k)
  rw [saddleQ_quadSum] at hn
  have d0 := sub_pos.mpr (h.lt 0 k); have d1 := sub_pos.mpr (h.lt 1 k)
  have d2 := sub_pos.mpr (h.lt 2 k); have d3 := sub_pos.mpr (h.lt 3 k)
  have hsq : Real.log ‖(quadSum l k : ℂ) - saddle l‖ =
      (1 / 2) * Real.log (Complex.normSq (saddle l - quadSum l k)) := by
    rw [← Complex.sq_norm, Real.log_pow, ← norm_neg, neg_sub]; push_cast; ring
  rw [hsq, hn, Real.log_div (by positivity) hq.ne', Real.log_mul (by positivity) d3.ne',
    Real.log_mul (by positivity) d2.ne', Real.log_mul d0.ne' d1.ne']

/-- **The real part of the saddle value is the rate of the prefactor**: `Re ψ(s) = D`, so the
exponential growth of Racah's sum cancels that of `∏ Δ(face)` exactly. -/
theorem IsEuclid.re_phase_saddle (h : IsEuclid l) : (phase l (saddle l)).re = prefactorRate l := by
  rw [h.phase_saddle]
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.log_re, zero_mul, sub_zero]
  rw [h.log_norm_saddle_sub_face 0, h.log_norm_saddle_sub_face 1, h.log_norm_saddle_sub_face 2,
    h.log_norm_saddle_sub_face 3, h.log_norm_quad_sub_saddle 0, h.log_norm_quad_sub_saddle 1,
    h.log_norm_quad_sub_saddle 2]
  simp only [prefactorRate, Fin.sum_univ_four, Fin.sum_univ_three, faceSum_zero, faceSum_one,
    faceSum_two, faceSum_three, quadSum_zero, quadSum_one, quadSum_two]
  ring

/-- The algebra behind `ψ''(s)`: if `∏ (s − aᵢ) = s ∏ (s − bₖ)` and `Σ aᵢ = Σ bₖ`, then
`(1/s − Σ 1/(s − aᵢ) + Σ 1/(s − bₖ)) ∏ (s − aᵢ) = −(2 (e₂(a) − e₂(b)) s + e₃(b) − e₃(a))`. -/
lemma d2_aux {s a0 a1 a2 a3 b0 b1 b2 : ℂ} (hs : s ≠ 0) (hA0 : s - a0 ≠ 0) (hA1 : s - a1 ≠ 0)
    (hA2 : s - a2 ≠ 0) (hA3 : s - a3 ≠ 0) (hB0 : s - b0 ≠ 0) (hB1 : s - b1 ≠ 0) (hB2 : s - b2 ≠ 0)
    (he : a0 + a1 + a2 + a3 = b0 + b1 + b2)
    (hP : (s - a0) * (s - a1) * (s - a2) * (s - a3) = s * ((s - b0) * (s - b1) * (s - b2))) :
    (1 / s - (1 / (s - a0) + 1 / (s - a1) + 1 / (s - a2) + 1 / (s - a3)) +
      (1 / (s - b0) + 1 / (s - b1) + 1 / (s - b2))) * ((s - a0) * (s - a1) * (s - a2) * (s - a3)) =
    -(2 * ((a0 * a1 + a0 * a2 + a0 * a3 + a1 * a2 + a1 * a3 + a2 * a3) -
        (b0 * b1 + b0 * b2 + b1 * b2)) * s +
      (b0 * b1 * b2 - (a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3))) := by
  have e1 : (1 / s + (1 / (s - b0) + 1 / (s - b1) + 1 / (s - b2))) *
      ((s - a0) * (s - a1) * (s - a2) * (s - a3)) =
      (s - b0) * (s - b1) * (s - b2) + s * ((s - b1) * (s - b2) + (s - b0) * (s - b2) +
        (s - b0) * (s - b1)) := by
    rw [hP]; field_simp
  have e2 : (1 / (s - a0) + 1 / (s - a1) + 1 / (s - a2) + 1 / (s - a3)) *
      ((s - a0) * (s - a1) * (s - a2) * (s - a3)) =
      (s - a1) * (s - a2) * (s - a3) + (s - a0) * (s - a2) * (s - a3) +
        (s - a0) * (s - a1) * (s - a3) + (s - a0) * (s - a1) * (s - a2) := by
    field_simp
  have : (1 / s - (1 / (s - a0) + 1 / (s - a1) + 1 / (s - a2) + 1 / (s - a3)) +
      (1 / (s - b0) + 1 / (s - b1) + 1 / (s - b2))) * ((s - a0) * (s - a1) * (s - a2) * (s - a3)) =
      (1 / s + (1 / (s - b0) + 1 / (s - b1) + 1 / (s - b2))) *
        ((s - a0) * (s - a1) * (s - a2) * (s - a3)) -
      (1 / (s - a0) + 1 / (s - a1) + 1 / (s - a2) + 1 / (s - a3)) *
        ((s - a0) * (s - a1) * (s - a2) * (s - a3)) := by ring
  rw [this, e1, e2]
  linear_combination (3 * s ^ 2) * he

/-- **The second derivative at the saddle**: `ψ''(s) · ∏ᵢ (s − Aᵢ) = −24 i √vol2`. -/
theorem IsEuclid.d2phase_saddle (h : IsEuclid l) :
    d2phase l (saddle l) * ((saddle l - faceSum l 0) * (saddle l - faceSum l 1) *
      (saddle l - faceSum l 2) * (saddle l - faceSum l 3)) =
      -(24 * Complex.I * (√(vol2l l) : ℂ)) := by
  have hq := h.qa_pos
  have hp := saddle_prod_eq h.vol2_pos.le hq.ne'
  have hA := h.saddle_sub_ne_zero
  have hB : ∀ k : Fin 3, saddle l - (quadSum l k : ℂ) ≠ 0 := fun k h0 =>
    h.sub_saddle_ne_zero (quadSum l k) (by rw [← neg_sub, h0, neg_zero])
  have hlin : (2 * qa l : ℂ) * saddle l + qb l = 24 * Complex.I * (√(vol2l l) : ℂ) := by
    rw [two_qa_mul_saddle hq.ne']; apply Complex.ext <;> simp
  rw [← hlin]
  have hP : (saddle l - faceSum l 0) * (saddle l - faceSum l 1) * (saddle l - faceSum l 2) *
      (saddle l - faceSum l 3) = saddle l * ((saddle l - quadSum l 0) * (saddle l - quadSum l 1) *
        (saddle l - quadSum l 2)) := by
    linear_combination hp
  have he : ((faceSum l 0 : ℂ) + faceSum l 1 + faceSum l 2 + faceSum l 3) =
      (quadSum l 0 : ℂ) + quadSum l 1 + quadSum l 2 := by
    simp only [faceSum_zero, faceSum_one, faceSum_two, faceSum_three, quadSum_zero, quadSum_one,
      quadSum_two]
    push_cast; ring
  simp only [d2phase, Fin.sum_univ_four, Fin.sum_univ_three]
  rw [d2_aux h.saddle_ne_zero (hA _) (hA _) (hA _) (hA _) (hB 0) (hB 1) (hB 2) he hP]
  simp only [qa, qb, faceSum_zero, faceSum_one, faceSum_two, faceSum_three, quadSum_zero,
    quadSum_one, quadSum_two]
  push_cast
  ring

end Euclid

end Lightlike.Asymptotics
