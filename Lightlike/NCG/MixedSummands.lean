import Lightlike.NCG.PartialUnits
import Lightlike.NCG.QuaternionSummands
import Lightlike.NCG.ComplexSummands

/-!
# Mixed algebras `⊕ Mₙ(ℝ) × ⊕ Mₙ(ℂ) × ⊕ Mₙ(ℍ)`

T. Krajewski, arXiv:hep-th/9701081, Section 2, p. 2 (`A = ⊕ Mₙᵢ(K)`, `K = ℝ, ℂ, ℍ`) and Section 3.1, p. 10 (read). The
three unit constructions use only multiplicativity, `*` and real linearity, so they apply to `π` restricted to one factor,
a non-unital `*`-homomorphism `ψ`:

* a real factor: the units `ψ(E^i_{αβ})` (`partialR`);
* a complex factor: the complex-linear and antilinear parts `ψ±(Y) = ½(ψ(Y) ∓ i ψ(iY))` (`psiPart`), multiplicative,
  orthogonal and self-adjoint, with units `ψ±(E^i_{αβ})` (`partialC`);
* a quaternionic factor: `partialH` (`QuaternionSummands.lean`).

The three systems multiply to `0` across factors (`mul_eq_zero_of_mem_span`) and their block units add to
`π(1) = 1`, so together they are one system of matrix units over `ι₁ ⊕ (blocks ⊕ ι₃)` (`unitsMixed`), and with `φ`
(`phiMixed`: `a₁`, `(a₂, ā₂)`, the `2n × 2n` complex matrices of `a₃`) a complexification (`mixedComplexification`):
`exists_unitary_mixed` is the uniqueness theorem for every real finite spectral triple over a mixed algebra.
-/

namespace Lightlike.NCG

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

section RealFactor

/-- `E^i_{αβ} E^i_{γδ} = δ_βγ E^i_{αδ}` for the real units. -/
lemma unitR_mul_same (i : ι) (α β γ δ : Fin (n i)) :
    unitR i α β * unitR i γ δ = if β = γ then unitR (n := n) i α δ else 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    by_cases hβ : β = γ
    · subst hβ
      simp [unitR, Matrix.single_mul_single_same]
    · simp [unitR, hβ, Matrix.single_mul_single_of_ne (h := hβ)]
  · split_ifs <;> simp [unitR, Pi.single_eq_of_ne hk]

/-- Real units of different summands multiply to `0`. -/
lemma unitR_mul_ne (i j : ι) (hij : i ≠ j) (α β : Fin (n i)) (γ δ : Fin (n j)) :
    unitR (n := n) i α β * unitR j γ δ = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [unitR, Pi.single_eq_of_ne hij]
  · simp [unitR, Pi.single_eq_of_ne hk]

/-- `(E^i_{αβ})* = E^i_{βα}` for the real units. -/
lemma star_unitR (i : ι) (α β : Fin (n i)) : star (unitR i α β) = unitR (n := n) i β α := by
  funext k
  by_cases hk : k = i
  · subst hk
    refine Matrix.ext fun γ δ => ?_
    by_cases h1 : α = δ <;> by_cases h2 : β = γ <;> simp [unitR, Matrix.star_apply, Matrix.single_apply, h1, h2]
  · simp [unitR, Pi.single_eq_of_ne hk]

variable (ψ : MatSumR n →⋆ₙₐ[ℝ] (H →L[ℂ] H))

/-- **The units of a real factor**: `ψ(E^i_{αβ})`. -/
def partialR : PartialUnits n H where
  U i x y := ψ (unitR i x y)
  mul_same i x y z w := by
    rw [← map_mul, unitR_mul_same]
    split_ifs <;> simp
  mul_ne i j hij x y z w := by rw [← map_mul, unitR_mul_ne i j hij, map_zero]
  star_U i x y := by rw [← map_star, star_unitR]

/-- `∑_α E^i_{αα} = 1ᵢ` for the real units. -/
lemma sum_unitR_block (i : ι) : ∑ α, unitR (n := n) i α α = Pi.single i 1 := by
  funext k
  rw [Finset.sum_apply]
  by_cases hk : k = i
  · subst hk
    simp only [unitR, Pi.single_eq_same, Matrix.sum_single_one]
  · simp only [unitR, Pi.single_eq_of_ne hk, Finset.sum_const_zero]

/-- The block units of a real factor: `∑ₓ ψ(E^i_{xx}) = ψ(1ᵢ)`. -/
lemma sum_partialR (i : ι) : ∑ x, (partialR ψ).U i x x = ψ (Pi.single i 1) := by
  show ∑ x, ψ (unitR i x x) = _
  rw [← map_sum, sum_unitR_block]

/-- `∑ᵢ ψ(1ᵢ) = ψ(1)`. -/
lemma sum_sum_partialR : ∑ i, ∑ x, (partialR ψ).U i x x = ψ 1 := by
  simp only [sum_partialR]
  rw [← map_sum, Finset.univ_sum_single (fun i => (1 : Matrix (Fin (n i)) (Fin (n i)) ℝ))]
  rfl

/-- **`σ ∘ φ = ψ` on a real factor**: `∑_{ixy} a^i_{xy} ψ(E^i_{xy}) = ψ(a)`. -/
lemma sum_phiR_partialR (a : MatSumR n) : ∑ i, ∑ x, ∑ y, phiR a i x y • (partialR ψ).U i x y = ψ a := by
  have h : ∀ i x y, phiR a i x y • (partialR ψ).U i x y = ψ (a i x y • unitR i x y) := fun i x y => by
    rw [map_smul]; rfl
  simp only [h, ← map_sum]
  congr 1
  have h2 : ∀ i, ∑ x, ∑ y, a i x y • unitR (n := n) i x y = Pi.single i (a i) := fun i => by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply]
    by_cases hk : k = i
    · subst hk
      simp only [unitR, Pi.single_eq_same, Matrix.smul_single, smul_eq_mul, mul_one]
      exact (Matrix.matrix_eq_sum_single _).symm
    · simp only [unitR, Pi.single_eq_of_ne hk, smul_zero, Finset.sum_const_zero]
  simp only [h2]
  exact Finset.univ_sum_single a

/-- The units of a real factor lie in the complex span of its image. -/
lemma partialR_mem_span (i : ι) (x y : Fin (n i)) :
    (partialR ψ).U i x y ∈ Submodule.span ℂ (Set.range ψ) :=
  Submodule.subset_span ⟨_, rfl⟩

end RealFactor

section ComplexFactor

variable (ψ : MatSum n →⋆ₙₐ[ℝ] (H →L[ℂ] H))

/-- The sign `-1` for the fundamental part (`true`), `+1` for the conjugate part (`false`). -/
def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- **The complex-linear (`true`) and antilinear (`false`) parts** `ψ±(Y) = ½(ψ(Y) ∓ i ψ(iY))`. -/
def psiPart (b : Bool) (Y : MatSum n) : H →L[ℂ] H := (1 / 2 : ℂ) • (ψ Y + (sgn b * Complex.I) • ψ (Complex.I • Y))

/-- `ψ₊ + ψ₋ = ψ`. -/
lemma psiPart_add (Y : MatSum n) : psiPart ψ true Y + psiPart ψ false Y = ψ Y := by
  simp only [psiPart, sgn, if_true, Bool.false_eq_true, if_false]
  module

/-- **`ψ_b(Y) ψ_c(Y') = δ_bc ψ_b(YY')`**: `ψ(iY) ψ(iY') = -ψ(YY')`. -/
lemma psiPart_mul (b c : Bool) (Y Y' : MatSum n) :
    psiPart ψ b Y * psiPart ψ c Y' = if b = c then psiPart ψ b (Y * Y') else 0 := by
  have h0 : ψ Y * ψ Y' = ψ (Y * Y') := (map_mul ψ Y Y').symm
  have h1 : ψ Y * ψ (Complex.I • Y') = ψ (Complex.I • (Y * Y')) := by rw [← map_mul, mul_smul_comm]
  have h2 : ψ (Complex.I • Y) * ψ Y' = ψ (Complex.I • (Y * Y')) := by rw [← map_mul, smul_mul_assoc]
  have h3 : ψ (Complex.I • Y) * ψ (Complex.I • Y') = -ψ (Y * Y') := by
    rw [← map_mul, smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul, map_neg]
  simp only [psiPart, smul_mul_smul_comm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h0, h1, h2, h3]
  cases b <;> cases c <;> simp only [sgn, if_true, Bool.false_eq_true, if_false, reduceCtorEq] <;>
    match_scalars <;> (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> norm_num

/-- `ψ_b(Y)* = ψ_b(Y*)`. -/
lemma star_psiPart (b : Bool) (Y : MatSum n) : star (psiPart ψ b Y) = psiPart ψ b (star Y) := by
  simp only [psiPart, star_smul, star_add, ← map_star, Complex.star_def, Complex.conj_I, map_mul, map_div₀,
    map_one, map_ofNat, map_neg, neg_smul, map_neg]
  cases b <;> simp only [sgn, if_true, Bool.false_eq_true, if_false, map_neg, map_one] <;> module

/-- `ψ(rY) = r ψ(Y)` for real `r`, with `r` acting as a complex scalar. -/
lemma psi_rsmul (r : ℝ) (Y : MatSum n) : ψ (r • Y) = (r : ℂ) • ψ Y := by
  rw [map_smul]; rfl

/-- `cY = Re c · Y + Im c · (iY)`. -/
lemma smul_eq_re_im (c : ℂ) (Y : MatSum n) : c • Y = c.re • Y + c.im • (Complex.I • Y) := by
  rw [smul_eq_re_add_im, smul_one_mul]

/-- `i(cY) = -Im c · Y + Re c · (iY)`. -/
lemma I_smul_smul_eq (c : ℂ) (Y : MatSum n) :
    Complex.I • (c • Y) = (-c.im) • Y + c.re • (Complex.I • Y) := by
  rw [smul_smul, smul_eq_re_im]
  simp [Complex.mul_re, Complex.mul_im]

/-- `ψ₊` is complex-linear: `c ψ₊(Y) = ψ₊(cY)`. -/
lemma smul_psiPart_true (c : ℂ) (Y : MatSum n) : c • psiPart ψ true Y = psiPart ψ true (c • Y) := by
  simp only [psiPart, sgn, if_true]
  rw [I_smul_smul_eq, smul_eq_re_im c Y, map_add, map_add, psi_rsmul, psi_rsmul, psi_rsmul, psi_rsmul]
  conv_lhs => rw [← Complex.re_add_im c]
  match_scalars <;> (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)

/-- `ψ₋` is antilinear: `c̄ ψ₋(Y) = ψ₋(cY)`. -/
lemma smul_psiPart_false (c : ℂ) (Y : MatSum n) :
    starRingEnd ℂ c • psiPart ψ false Y = psiPart ψ false (c • Y) := by
  simp only [psiPart, sgn, Bool.false_eq_true, if_false]
  rw [I_smul_smul_eq, smul_eq_re_im c Y, map_add, map_add, psi_rsmul, psi_rsmul, psi_rsmul, psi_rsmul]
  conv_lhs => rw [← Complex.re_add_im c]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  match_scalars <;> (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)

/-- `ψ_b(0) = 0`. -/
lemma psiPart_zero (b : Bool) : psiPart ψ b (0 : MatSum n) = 0 := by
  simp [psiPart]

/-- `ψ_b` is additive. -/
lemma psiPart_add' (b : Bool) (Y Y' : MatSum n) : psiPart ψ b (Y + Y') = psiPart ψ b Y + psiPart ψ b Y' := by
  simp only [psiPart, smul_add, map_add]
  module

/-- `ψ_b` as an additive map. -/
def psiPartA (b : Bool) : MatSum n →+ (H →L[ℂ] H) where
  toFun := psiPart ψ b
  map_zero' := psiPart_zero ψ b
  map_add' := psiPart_add' ψ b

/-- `ψ_b(Y)` lies in the complex span of the image of `ψ`. -/
lemma psiPart_mem_span (b : Bool) (Y : MatSum n) : psiPart ψ b Y ∈ Submodule.span ℂ (Set.range ψ) :=
  Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))

/-- **The nonzero blocks of a complex factor**: `(i, b)` with `ψ_b(1ᵢ) ≠ 0`. -/
abbrev BlocksP := {p : ι × Bool // psiPart ψ p.2 (Pi.single p.1 1) ≠ 0}

/-- The nonzero blocks form a finite type. -/
noncomputable instance blocksPFintype : Fintype (BlocksP ψ) :=
  @Subtype.fintype _ _ (Classical.decPred _) _

/-- **The units of a complex factor**: `ψ_b(E^i_{αβ})` over the nonzero blocks. -/
def partialC : PartialUnits (fun p : BlocksP ψ => n p.1.1) H where
  U p x y := psiPart ψ p.1.2 (unitC p.1.1 x y)
  mul_same p x y z w := by
    rw [psiPart_mul, if_pos rfl, unitC_mul_same]
    split_ifs <;> simp [psiPart_zero]
  mul_ne p q hpq x y z w := by
    rw [psiPart_mul]
    by_cases hb : p.1.2 = q.1.2
    · have hi : p.1.1 ≠ q.1.1 := fun hi => hpq (Subtype.ext (Prod.ext hi hb))
      rw [if_pos hb, unitC_mul_ne _ _ hi, psiPart_zero]
    · rw [if_neg hb]
  star_U p x y := by rw [star_psiPart, star_unitC]

/-- **Sums over the nonzero elements**: if `G` vanishes where `f` does, the sum of `G` over `{p | f p ≠ 0}` is its sum. -/
lemma sum_subtype_ne_zero {α M N : Type*} [Fintype α] [AddCommMonoid M] [Zero N] (f : α → N)
    [Fintype {p // f p ≠ 0}] (G : α → M) (hG : ∀ p, f p = 0 → G p = 0) :
    ∑ p : {p // f p ≠ 0}, G p.1 = ∑ p, G p := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun p => f p ≠ 0) (fun p => by rw [Finset.mem_filter]; simp) G]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun p _ hp => hG p ?_
  simpa using hp

/-- `ψ_b(E^i_{xy}) = 0` on a zero block. -/
lemma psiPart_unitC_zero (p : ι × Bool) (hp : psiPart ψ p.2 (Pi.single p.1 1) = 0) (x y : Fin (n p.1)) :
    psiPart ψ p.2 (unitC p.1 x y) = 0 := by
  have h : unitC p.1 x y = Pi.single p.1 1 * unitC p.1 x y := by
    funext k
    by_cases hk : k = p.1
    · subst hk; simp [unitC]
    · simp [unitC, Pi.single_eq_of_ne hk]
  have hm := psiPart_mul ψ p.2 p.2 (Pi.single p.1 1) (unitC p.1 x y)
  rw [if_pos rfl] at hm
  rw [h, ← hm, hp, zero_mul]

/-- The block unit of a complex factor: `∑ₓ ψ_b(E^i_{xx}) = ψ_b(1ᵢ)`. -/
lemma sum_partialC (p : BlocksP ψ) : ∑ x, (partialC ψ).U p x x = psiPart ψ p.1.2 (Pi.single p.1.1 1) := by
  show ∑ x, psiPartA ψ p.1.2 (unitC p.1.1 x x) = _
  rw [← map_sum, sum_unitC_block]; rfl

/-- The block units of a complex factor add to `ψ(1)`. -/
lemma sum_sum_partialC : ∑ p, ∑ x, (partialC ψ).U p x x = ψ 1 := by
  have h1 : ∀ p : BlocksP ψ, ∑ x, (partialC ψ).U p x x = psiPart ψ p.1.2 (Pi.single p.1.1 1) := fun p => by
    show ∑ x, psiPartA ψ p.1.2 (unitC p.1.1 x x) = _
    rw [← map_sum, sum_unitC_block]; rfl
  simp only [h1]
  rw [sum_subtype_ne_zero (fun p : ι × Bool => psiPart ψ p.2 (Pi.single p.1 1)) _ (fun p hp => hp),
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, psiPart_add]
  rw [← map_sum, Finset.univ_sum_single (fun i => (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ))]
  rfl

/-- `φ` on a complex factor: `aᵢ` on the fundamental block, `āᵢ` on the conjugate one. -/
def phiPAll (a : MatSum n) (q : ι × Bool) : Matrix (Fin (n q.1)) (Fin (n q.1)) ℂ :=
  if q.2 then a q.1 else (a q.1).map (starRingEnd ℂ)

/-- The contribution of a block `(i, b)`: `∑_{xy} φ(a)_{xy} ψ_b(E^i_{xy})`. -/
def GP (a : MatSum n) (q : ι × Bool) : H →L[ℂ] H := ∑ x, ∑ y, phiPAll a q x y • psiPart ψ q.2 (unitC q.1 x y)

/-- `φ(1) = 1` on a block. -/
lemma phiPAll_one (q : ι × Bool) : phiPAll (1 : MatSum n) q = 1 := by
  by_cases hb : q.2 = true <;> simp [phiPAll, hb]

/-- `φ` is multiplicative on a block. -/
lemma phiPAll_mul (a b : MatSum n) (q : ι × Bool) : phiPAll (a * b) q = phiPAll a q * phiPAll b q := by
  by_cases hb : q.2 = true <;> simp [phiPAll, hb, Matrix.map_mul]

/-- `φ(0) = 0` on a block. -/
lemma phiPAll_zero (q : ι × Bool) : phiPAll (0 : MatSum n) q = 0 := by
  by_cases hb : q.2 = true <;> simp [phiPAll, hb]

/-- `φ` is additive on a block. -/
lemma phiPAll_add (a b : MatSum n) (q : ι × Bool) : phiPAll (a + b) q = phiPAll a q + phiPAll b q := by
  by_cases hb : q.2 = true <;> simp [phiPAll, hb, Matrix.map_add]

/-- `φ(a*) = φ(a)*` on a block. -/
lemma phiPAll_star (a : MatSum n) (q : ι × Bool) : phiPAll (star a) q = star (phiPAll a q) := by
  refine Matrix.ext fun x y => ?_
  by_cases hb : q.2 = true <;> simp [phiPAll, hb, Matrix.star_apply]

/-- `φ` commutes with the real scalars on a block. -/
lemma phiPAll_algebraMap (r : ℝ) (q : ι × Bool) :
    phiPAll (algebraMap ℝ (MatSum n) r) q = algebraMap ℝ _ r := by
  refine Matrix.ext fun x y => ?_
  by_cases hb : q.2 = true <;> by_cases hxy : x = y <;>
    simp [phiPAll, hb, hxy, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

/-- **`σ ∘ φ = ψ` on a complex factor.** -/
lemma sum_phiP_partialC (a : MatSum n) :
    ∑ p : BlocksP ψ, ∑ x, ∑ y, phiPAll a p.1 x y • (partialC ψ).U p x y = ψ a := by
  change ∑ p : BlocksP ψ, GP ψ a p.1 = _
  rw [sum_subtype_ne_zero (fun p : ι × Bool => psiPart ψ p.2 (Pi.single p.1 1)) (GP ψ a)
    (fun q hq => Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by
      rw [psiPart_unitC_zero ψ q hq x y, smul_zero]), Fintype.sum_prod_type]
  simp only [GP, Fintype.sum_bool, phiPAll, if_true, Bool.false_eq_true, if_false, Matrix.map_apply,
    smul_psiPart_true, smul_psiPart_false]
  have hs : ∀ (b : Bool) (i : ι), ∑ x, ∑ y, psiPart ψ b (a i x y • unitC i x y) = psiPart ψ b (Pi.single i (a i)) :=
    fun b i => by
      show ∑ x, ∑ y, psiPartA ψ b (a i x y • unitC i x y) = psiPartA ψ b (Pi.single i (a i))
      rw [← sum_smul_unitC a i, map_sum]
      simp only [map_sum]
  simp only [hs, psiPart_add]
  rw [← map_sum, Finset.univ_sum_single]

end ComplexFactor

/-- **Units in orthogonal spans multiply to `0`**: if `ψ(a) ψ'(b) = 0` for all `a`, `b`, then `X Y = 0` for `X`, `Y` in the
complex spans of the images. -/
lemma mul_eq_zero_of_mem_span {A B : Type*} (ψ : A → H →L[ℂ] H) (ψ' : B → H →L[ℂ] H) (h : ∀ a b, ψ a * ψ' b = 0)
    {X Y : H →L[ℂ] H} (hX : X ∈ Submodule.span ℂ (Set.range ψ)) (hY : Y ∈ Submodule.span ℂ (Set.range ψ')) :
    X * Y = 0 := by
  induction hX using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, rfl⟩ := hs
    induction hY using Submodule.span_induction with
    | mem t ht => obtain ⟨b, rfl⟩ := ht; exact h a b
    | zero => exact mul_zero _
    | add Y₁ Y₂ _ _ h₁ h₂ => rw [mul_add, h₁, h₂, add_zero]
    | smul c Y _ hY' => rw [mul_smul_comm, hY', smul_zero]
  | zero => exact zero_mul _
  | add X₁ X₂ _ _ h₁ h₂ => rw [add_mul, h₁, h₂, add_zero]
  | smul c X _ hX' => rw [smul_mul_assoc, hX', smul_zero]

section Mixed

variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι₃]
  [DecidableEq ι₃] {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ} {n₃ : ι₃ → ℕ}

variable (n₁ n₂ n₃) in
/-- **A mixed algebra** `⊕ Mₙ(ℝ) × ⊕ Mₙ(ℂ) × ⊕ Mₙ(ℍ)` (Krajewski, Section 2, p. 2). -/
abbrev MatSumMixed := MatSumR n₁ × MatSum n₂ × MatSumH n₃

variable (T : FiniteSpectralTriple (MatSumMixed n₁ n₂ n₃) H)

/-- `π` on the real factor. -/
def psi₁ : MatSumR n₁ →⋆ₙₐ[ℝ] (H →L[ℂ] H) := T.π.toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inl ℝ _ _)

/-- `π` on the complex factor. -/
def psi₂ : MatSum n₂ →⋆ₙₐ[ℝ] (H →L[ℂ] H) :=
  T.π.toNonUnitalStarAlgHom.comp ((NonUnitalStarAlgHom.inr ℝ _ _).comp (NonUnitalStarAlgHom.inl ℝ _ _))

/-- `π` on the quaternionic factor. -/
def psi₃ : MatSumH n₃ →⋆ₙₐ[ℝ] (H →L[ℂ] H) :=
  T.π.toNonUnitalStarAlgHom.comp ((NonUnitalStarAlgHom.inr ℝ _ _).comp (NonUnitalStarAlgHom.inr ℝ _ _))

/-- `ψ₁(a) = π(a, 0, 0)`. -/
lemma psi₁_apply (a : MatSumR n₁) : psi₁ T a = T.π (a, 0, 0) := rfl

/-- `ψ₂(a) = π(0, a, 0)`. -/
lemma psi₂_apply (a : MatSum n₂) : psi₂ T a = T.π (0, a, 0) := rfl

/-- `ψ₃(a) = π(0, 0, a)`. -/
lemma psi₃_apply (a : MatSumH n₃) : psi₃ T a = T.π (0, 0, a) := rfl

/-- `ψ₁ ψ₂ = 0`. -/
lemma psi₁_mul_psi₂ (a b) : psi₁ T a * psi₂ T b = 0 := by
  rw [psi₁_apply, psi₂_apply, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_zero, zero_mul]
  exact map_zero T.π
/-- `ψ₂ ψ₁ = 0`. -/
lemma psi₂_mul_psi₁ (a b) : psi₂ T a * psi₁ T b = 0 := by
  rw [psi₁_apply, psi₂_apply, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_zero, zero_mul]
  exact map_zero T.π
/-- `ψ₁ ψ₃ = 0`. -/
lemma psi₁_mul_psi₃ (a b) : psi₁ T a * psi₃ T b = 0 := by
  rw [psi₁_apply, psi₃_apply, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_zero, zero_mul]
  exact map_zero T.π
/-- `ψ₃ ψ₁ = 0`. -/
lemma psi₃_mul_psi₁ (a b) : psi₃ T a * psi₁ T b = 0 := by
  rw [psi₁_apply, psi₃_apply, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_zero, zero_mul]
  exact map_zero T.π
/-- `ψ₂ ψ₃ = 0`. -/
lemma psi₂_mul_psi₃ (a b) : psi₂ T a * psi₃ T b = 0 := by
  rw [psi₂_apply, psi₃_apply, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_zero, zero_mul]
  exact map_zero T.π
/-- `ψ₃ ψ₂ = 0`. -/
lemma psi₃_mul_psi₂ (a b) : psi₃ T a * psi₂ T b = 0 := by
  rw [psi₂_apply, psi₃_apply, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_zero, zero_mul]
  exact map_zero T.π

/-- `π = ψ₁ + ψ₂ + ψ₃`. -/
lemma pi_eq_psi (a : MatSumMixed n₁ n₂ n₃) : T.π a = psi₁ T a.1 + (psi₂ T a.2.1 + psi₃ T a.2.2) := by
  rw [psi₁_apply, psi₂_apply, psi₃_apply, ← map_add, ← map_add]
  congr 1
  ext <;> simp

/-- The units of the complex and quaternionic factors. -/
def partialCH : PartialUnits (Sum.elim (fun p : BlocksP (psi₂ T) => n₂ p.1.1) (fun i => n₃ i * 2)) H :=
  (partialC (psi₂ T)).sum (partialH (psi₃ T))
    (fun _ _ _ _ _ _ => mul_eq_zero_of_mem_span _ _ (psi₂_mul_psi₃ T) (psiPart_mem_span _ _ _) (UH_mem_span _ _ _ _))
    (fun _ _ _ _ _ _ => mul_eq_zero_of_mem_span _ _ (psi₃_mul_psi₂ T) (UH_mem_span _ _ _ _) (psiPart_mem_span _ _ _))

/-- The real units against the complex and quaternionic ones. -/
lemma partialR_mul_CH (k : ι₁) (x y : Fin (n₁ k)) (q : BlocksP (psi₂ T) ⊕ ι₃)
    (z w : Fin (Sum.elim (fun p : BlocksP (psi₂ T) => n₂ p.1.1) (fun i => n₃ i * 2) q)) :
    (partialR (psi₁ T)).U k x y * (partialCH T).U q z w = 0 := by
  cases q with
  | inl p => exact mul_eq_zero_of_mem_span _ _ (psi₁_mul_psi₂ T) (partialR_mem_span _ _ _ _) (psiPart_mem_span _ _ _)
  | inr i => exact mul_eq_zero_of_mem_span _ _ (psi₁_mul_psi₃ T) (partialR_mem_span _ _ _ _) (UH_mem_span _ _ _ _)

/-- The complex and quaternionic units against the real ones. -/
lemma partialCH_mul_R (q : BlocksP (psi₂ T) ⊕ ι₃)
    (z w : Fin (Sum.elim (fun p : BlocksP (psi₂ T) => n₂ p.1.1) (fun i => n₃ i * 2) q)) (k : ι₁) (x y : Fin (n₁ k)) :
    (partialCH T).U q z w * (partialR (psi₁ T)).U k x y = 0 := by
  cases q with
  | inl p => exact mul_eq_zero_of_mem_span _ _ (psi₂_mul_psi₁ T) (psiPart_mem_span _ _ _) (partialR_mem_span _ _ _ _)
  | inr i => exact mul_eq_zero_of_mem_span _ _ (psi₃_mul_psi₁ T) (UH_mem_span _ _ _ _) (partialR_mem_span _ _ _ _)

/-- **The units of a mixed algebra**, over `ι₁ ⊕ (blocks ⊕ ι₃)`. -/
def partialMixed : PartialUnits (Sum.elim n₁ (Sum.elim (fun p : BlocksP (psi₂ T) => n₂ p.1.1) (fun i => n₃ i * 2))) H :=
  (partialR (psi₁ T)).sum (partialCH T) (partialR_mul_CH T) (partialCH_mul_R T)

/-- **The block units of a mixed algebra add to `1`.** -/
lemma sum_partialMixed : ∑ q, ∑ x, (partialMixed T).U q x x = 1 := by
  have h1 : ∑ a, ∑ x, (partialMixed T).U (Sum.inl a) x x = psi₁ T 1 := sum_sum_partialR (psi₁ T)
  have h2 : ∑ a, ∑ x, (partialMixed T).U (Sum.inr (Sum.inl a)) x x = psi₂ T 1 := sum_sum_partialC (psi₂ T)
  have h3 : ∑ a, ∑ x, (partialMixed T).U (Sum.inr (Sum.inr a)) x x = psi₃ T 1 := sum_sum_UH (psi₃ T)
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, h1, h2, h3]
  rw [← map_one T.π, pi_eq_psi T 1]
  rfl

/-- **The matrix units of a mixed algebra.** -/
def unitsMixed : MatrixUnits (Sum.elim n₁ (Sum.elim (fun p : BlocksP (psi₂ T) => n₂ p.1.1) (fun i => n₃ i * 2))) H :=
  (partialMixed T).toMatrixUnits (sum_partialMixed T)

/-- The dimensions of the irreducible representations of a mixed algebra. -/
abbrev dMixed : BlocksP (psi₂ T) ⊕ ι₃ → ℕ := Sum.elim (fun p : BlocksP (psi₂ T) => n₂ p.1.1) (fun i => n₃ i * 2)

/-- `φ(a)` on the irreducible representations: `a₁` on the real ones, `a₂` or `ā₂` on the complex ones, the complex
`2n × 2n` matrices of `a₃` on the quaternionic ones. -/
def phiMixedFun (a : MatSumMixed n₁ n₂ n₃) : MatSum (Sum.elim n₁ (dMixed T)) := fun q =>
  match q with
  | .inl k => phiR a.1 k
  | .inr (.inl p) => phiPAll a.2.1 p.1
  | .inr (.inr i) => phiH a.2.2 i

/-- **`φ` for a mixed algebra**, a real `*`-homomorphism. -/
def phiMixed : MatSumMixed n₁ n₂ n₃ →⋆ₐ[ℝ] MatSum (Sum.elim n₁ (dMixed T)) where
  toFun := phiMixedFun T
  map_one' := by
    funext q
    rcases q with k | p | i
    · exact congrFun (map_one (phiR (n := n₁))) k
    · exact phiPAll_one _
    · exact congrFun (map_one (phiH (n := n₃))) i
  map_mul' a b := by
    funext q
    rcases q with k | p | i
    · exact congrFun (map_mul phiR a.1 b.1) k
    · exact phiPAll_mul _ _ _
    · exact congrFun (map_mul phiH a.2.2 b.2.2) i
  map_zero' := by
    funext q
    rcases q with k | p | i
    · exact congrFun (map_zero (phiR (n := n₁))) k
    · exact phiPAll_zero _
    · exact congrFun (map_zero (phiH (n := n₃))) i
  map_add' a b := by
    funext q
    rcases q with k | p | i
    · exact congrFun (map_add phiR a.1 b.1) k
    · exact phiPAll_add _ _ _
    · exact congrFun (map_add phiH a.2.2 b.2.2) i
  commutes' r := by
    funext q
    rcases q with k | p | i
    · exact congrFun (phiR.commutes r) k
    · exact phiPAll_algebraMap r _
    · exact congrFun ((phiH (n := n₃)).commutes r) i
  map_star' a := by
    funext q
    rcases q with k | p | i
    · exact congrFun (map_star phiR a.1) k
    · exact phiPAll_star _ _
    · exact congrFun (map_star phiH a.2.2) i

/-- **`σ ∘ φ = π`** for a mixed algebra: the three factor identities. -/
lemma unitsMixed_hom_phiMixed (a : MatSumMixed n₁ n₂ n₃) : (unitsMixed T).hom (phiMixed T a) = T.π a := by
  rw [MatrixUnits.hom_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ k, ∑ x, ∑ y, phiMixed T a (Sum.inl k) x y • (unitsMixed T).U (Sum.inl k) x y = psi₁ T a.1 :=
    sum_phiR_partialR (psi₁ T) a.1
  have h2 : ∑ p, ∑ x, ∑ y, phiMixed T a (Sum.inr (Sum.inl p)) x y • (unitsMixed T).U (Sum.inr (Sum.inl p)) x y =
      psi₂ T a.2.1 := sum_phiP_partialC (psi₂ T) a.2.1
  have h3 : ∑ i, ∑ x, ∑ y, phiMixed T a (Sum.inr (Sum.inr i)) x y • (unitsMixed T).U (Sum.inr (Sum.inr i)) x y =
      psi₃ T a.2.2 := sum_phiH_UH (psi₃ T) a.2.2
  rw [h1, h2, h3, pi_eq_psi]

/-- `π(x) ≠ 0` for `x ≠ 0`. -/
lemma pi_ne_zero_of_ne (x : MatSumMixed n₁ n₂ n₃) (hx : x ≠ 0) : T.π x ≠ 0 :=
  fun h => hx (T.injective_π (h.trans (map_zero T.π).symm))

/-- The spans of the factors lie in the span of `π(A)`. -/
lemma span_psi_le {B : Type*} (ψ : B → H →L[ℂ] H) (hψ : ∀ b, ∃ a, T.π a = ψ b) :
    Submodule.span ℂ (Set.range ψ) ≤ Submodule.span ℂ (Set.range T.π) :=
  Submodule.span_mono fun _ ⟨b, hb⟩ => hb ▸ hψ b

/-- **The complexification of a triple over a mixed algebra.** -/
def mixedComplexification [∀ i, NeZero (n₁ i)] [∀ i, NeZero (n₃ i)] :
    Complexification T (Sum.elim n₁ (dMixed T)) where
  σ := (unitsMixed T).hom
  injective_σ := (unitsMixed T).hom_injective_of_block fun q => by
    rcases q with k | p | i
    · show ∑ x, (partialR (psi₁ T)).U k x x ≠ 0
      rw [sum_partialR, psi₁_apply]
      refine pi_ne_zero_of_ne T _ fun h => ?_
      have := congrFun (congrArg Prod.fst h) k
      simp at this
    · show ∑ x, (partialC (psi₂ T)).U p x x ≠ 0
      rw [sum_partialC]
      exact p.2
    · show ∑ x, UH (psi₃ T) i x x ≠ 0
      rw [sum_UH, psi₃_apply]
      refine pi_ne_zero_of_ne T _ fun h => ?_
      have := congrFun (congrArg (fun z => z.2.2) h) i
      simp at this
  φ := phiMixed T
  pi_eq a := (unitsMixed_hom_phiMixed T a).symm
  mem_span Y := (unitsMixed T).hom_mem _ (fun q x y => by
    rcases q with k | p | i
    · show (partialR (psi₁ T)).U k x y ∈ _
      exact span_psi_le T (psi₁ T) (fun b => ⟨(b, 0, 0), rfl⟩) (partialR_mem_span (psi₁ T) k x y)
    · show psiPart (psi₂ T) p.1.2 (unitC p.1.1 x y) ∈ _
      exact span_psi_le T (psi₂ T) (fun b => ⟨(0, b, 0), rfl⟩) (psiPart_mem_span (psi₂ T) _ _)
    · show UH (psi₃ T) i x y ∈ _
      exact span_psi_le T (psi₃ T) (fun b => ⟨(0, 0, b), rfl⟩) (UH_mem_span (psi₃ T) i x y)) Y

/-- The irreducible representations of a mixed algebra have positive dimension. -/
instance neZero_dMixed [∀ i, NeZero (n₁ i)] [∀ i, NeZero (n₂ i)] [∀ i, NeZero (n₃ i)]
    (q : ι₁ ⊕ (BlocksP (psi₂ T) ⊕ ι₃)) : NeZero (Sum.elim n₁ (dMixed T) q) := by
  rcases q with k | p | i
  · exact (inferInstance : NeZero (n₁ k))
  · exact (inferInstance : NeZero (n₂ p.1.1))
  · exact (inferInstance : NeZero (n₃ i * 2))

/-- **Uniqueness for a mixed algebra** (Krajewski, Section 2, p. 2, Section 3.1, p. 10, with Section 3.2, p. 13): a real
finite spectral triple over `⊕ Mₙ(ℝ) × ⊕ Mₙ(ℂ) × ⊕ Mₙ(ℍ)` is unitarily equivalent to the model of the multiplicity
matrix of its complexification, indexed by the irreducible representations that occur: the fundamental ones of the
real and quaternionic summands, and the fundamental and conjugate ones of the complex summands. -/
theorem exists_unitary_mixed [∀ i, NeZero (n₁ i)] [∀ i, NeZero (n₂ i)] [∀ i, NeZero (n₃ i)] (R : RealStructure T) :
    ∃ U : H ≃ₗᵢ[ℂ] HK (Sum.elim n₁ (dMixed T))
        (fun p q => multiplicity ((mixedComplexification T).realStructure R) p q),
      (∀ a x, U (T.π a x) = piK (phiMixed T a) (U x)) ∧
        ∀ x, U (R.J x) = JK (multiplicity_symm ((mixedComplexification T).realStructure R)) (U x) :=
  (mixedComplexification T).exists_unitary R

end Mixed


end

end Lightlike.NCG
