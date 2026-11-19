import Lightlike.NCG.MatrixUnits
import Lightlike.NCG.ComplexSplitting
import Lightlike.NCG.RealSummands

/-!
# Complex summands `Mₙ(ℂ)` acting real-linearly

T. Krajewski, arXiv:hep-th/9701081, Section 3.1, p. 10 (read): "`Mₙ(ℂ)` has two inequivalent irreducible
representations, the fundamental one and its complex conjugate". For a real-linear `π` of `⊕ Mₙᵢ(ℂ)`, `u = i · 1` is
central with `u² = -1` and `u* = -u`, so `Q₊ = (1 - i π(u))/2` and `Q₋ = (1 + i π(u))/2` are complementary orthogonal
projections commuting with `π` (`ComplexSplitting.lean`). The units `Q± π(E^i_{αβ})` of the blocks `(i, ±)` with
`Q± π(1ᵢ) ≠ 0` are a system of matrix units, and with `φ(a) = (aᵢ, āᵢ)` they form a complexification: `π` is
complex-linear on `Q₊ H` (the fundamental representations) and antilinear on `Q₋ H` (the conjugate ones).

* `uC`, `uC_mul`, `star_uC`, `uC_comm`; `Qb`, `Qb_mul_Qb`, `Qb_mul_Qb_ne`, `star_Qb`, `pi_comm_Qb`, `Qb_true_add_false`;
* `unitC_mul_same`, `unitC_mul_ne`, `star_unitC`;
* `Blocks`, `UC`, `Qb_pi_mul_Qb_pi`, `Qb_pi_mem_span`, `blockC`, `sum_UC`, `sum_blocks`, `UC_zero`, `unitsC`: the units of the
  nonzero blocks;
* `sum_smul_unitC`, `phiCAll`, `phiCFun`, `phiC`, `Qb_true_pi_smul`, `Qb_false_pi_smul`, `GC`, `GC_zero`, `unitsC_hom_phiC`: `φ(a) = (aᵢ, āᵢ)`
  and `σ ∘ φ = π`;
* `complexComplexification`, `exists_unitary_complexSummands`: uniqueness for complex summands acting real-linearly.
-/

namespace Lightlike.NCG

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

/-- `u = i · 1`, central in `⊕ Mₙᵢ(ℂ)`. -/
def uC : MatSum n := Complex.I • 1

/-- `u² = -1`. -/
lemma uC_mul : (uC : MatSum n) * uC = -1 := by
  rw [uC, smul_one_mul, smul_smul, Complex.I_mul_I, neg_one_smul]

/-- `u* = -u`. -/
lemma star_uC : star (uC : MatSum n) = -uC := by
  rw [uC, star_smul, star_one, Complex.star_def, Complex.conj_I, neg_smul]

/-- `u` is central. -/
lemma uC_comm (b : MatSum n) : uC * b = b * uC := by
  rw [uC, smul_one_mul, mul_smul_one]

/-- `E^i_{αβ} E^i_{γδ} = δ_βγ E^i_{αδ}`. -/
lemma unitC_mul_same (i : ι) (α β γ δ : Fin (n i)) :
    unitC i α β * unitC i γ δ = if β = γ then unitC i α δ else 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    by_cases hβ : β = γ
    · subst hβ
      simp [unitC, Matrix.single_mul_single_same]
    · simp [unitC, hβ, Matrix.single_mul_single_of_ne (h := hβ)]
  · split_ifs <;> simp [unitC, Pi.single_eq_of_ne hk]

/-- Units of different summands multiply to `0`. -/
lemma unitC_mul_ne (i j : ι) (hij : i ≠ j) (α β : Fin (n i)) (γ δ : Fin (n j)) :
    unitC i α β * unitC j γ δ = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [unitC, Pi.single_eq_of_ne hij]
  · simp [unitC, Pi.single_eq_of_ne hk]

/-- `(E^i_{αβ})* = E^i_{βα}`. -/
lemma star_unitC (i : ι) (α β : Fin (n i)) : star (unitC i α β) = unitC (n := n) i β α := by
  funext k
  by_cases hk : k = i
  · subst hk
    refine Matrix.ext fun γ δ => ?_
    by_cases h1 : α = δ <;> by_cases h2 : β = γ <;> simp [unitC, Matrix.star_apply, Matrix.single_apply, h1, h2]
  · simp [unitC, Pi.single_eq_of_ne hk]

/-- `∑_α E^i_{αα} = 1ᵢ`. -/
lemma sum_unitC_block (i : ι) : ∑ α, unitC (n := n) i α α = Pi.single i 1 := by
  funext k
  rw [Finset.sum_apply]
  by_cases hk : k = i
  · subst hk
    simp only [unitC, Pi.single_eq_same, Matrix.sum_single_one]
  · simp only [unitC, Pi.single_eq_of_ne hk, Finset.sum_const_zero]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable (T : FiniteSpectralTriple (MatSum n) H)

/-- `Q₊` for `true`, `Q₋` for `false`. -/
def Qb (b : Bool) : H →L[ℂ] H := if b then Qp T uC else Qm T uC

/-- `Q_b` is idempotent. -/
lemma Qb_mul_Qb (b : Bool) : Qb T b * Qb T b = Qb T b := by
  cases b
  · exact Qm_mul_Qm T uC_mul
  · exact Qp_mul_Qp T uC_mul

/-- `Q₊ Q₋ = Q₋ Q₊ = 0`. -/
lemma Qb_mul_Qb_ne (b c : Bool) (h : b ≠ c) : Qb T b * Qb T c = 0 := by
  cases b <;> cases c
  · exact absurd rfl h
  · exact Qm_mul_Qp T uC_mul
  · exact Qp_mul_Qm T uC_mul
  · exact absurd rfl h

/-- `Q_b` is self-adjoint. -/
lemma star_Qb (b : Bool) : star (Qb T b) = Qb T b := by
  cases b
  · exact star_Qm T star_uC
  · exact star_Qp T star_uC

/-- `Q_b` commutes with `π`. -/
lemma pi_comm_Qb (b : Bool) (a : MatSum n) : T.π a * Qb T b = Qb T b * T.π a := by
  cases b
  · exact pi_comm_Qm T uC_comm a
  · exact pi_comm_Qp T uC_comm a

/-- `Q₊ + Q₋ = 1`. -/
lemma Qb_true_add_false : Qb T true + Qb T false = 1 := Qp_add_Qm T uC

/-- **The blocks that act nontrivially**: `(i, b)` with `Q_b π(1ᵢ) ≠ 0`. -/
abbrev Blocks := {p : ι × Bool // Qb T p.2 * T.π (Pi.single p.1 1) ≠ 0}

/-- The blocks form a finite type. -/
noncomputable instance blocksFintype : Fintype (Blocks T) :=
  @Subtype.fintype _ _ (Classical.decPred _) _

/-- **The units** `Q_b π(E^i_{αβ})` of a block `(i, b)`. -/
def UC (p : Blocks T) (x y : Fin (n p.1.1)) : H →L[ℂ] H := Qb T p.1.2 * T.π (unitC p.1.1 x y)

/-- `Q_b π(a) Q_c π(a') = Q_b Q_c π(a a')`. -/
lemma Qb_pi_mul_Qb_pi (b c : Bool) (a a' : MatSum n) :
    Qb T b * T.π a * (Qb T c * T.π a') = Qb T b * Qb T c * T.π (a * a') := by
  simp only [map_mul, mul_assoc]
  rw [← mul_assoc (T.π a) (Qb T c), pi_comm_Qb, mul_assoc]

/-- `Q_b π(a)` lies in the complex span of `π(A)`. -/
lemma Qb_pi_mem_span (b : Bool) (a : MatSum n) : Qb T b * T.π a ∈ Submodule.span ℂ (Set.range T.π) := by
  have h1 : T.π a ∈ Submodule.span ℂ (Set.range T.π) := Submodule.subset_span ⟨a, rfl⟩
  have h2 : T.π uC * T.π a ∈ Submodule.span ℂ (Set.range T.π) := by
    rw [← map_mul]; exact Submodule.subset_span ⟨_, rfl⟩
  cases b
  · show (1 / 2 : ℂ) • (1 + Complex.I • T.π uC) * T.π a ∈ _
    rw [smul_mul_assoc, add_mul, one_mul, smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2))
  · show (1 / 2 : ℂ) • (1 - Complex.I • T.π uC) * T.π a ∈ _
    rw [smul_mul_assoc, sub_mul, one_mul, smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2))

/-- The block unit `Q_b π(1ᵢ)`. -/
def blockC (p : ι × Bool) : H →L[ℂ] H := Qb T p.2 * T.π (Pi.single p.1 1)

/-- `∑_α Q_b π(E^i_{αα}) = Q_b π(1ᵢ)`. -/
lemma sum_UC (p : Blocks T) : ∑ x, UC T p x x = blockC T p.1 := by
  simp only [UC, blockC, ← Finset.mul_sum, ← map_sum, sum_unitC_block]

/-- A sum over the nonzero blocks is the sum over all blocks of a function vanishing on the zero ones. -/
lemma sum_blocks {M : Type*} [AddCommMonoid M] (G : ι × Bool → M) (hG : ∀ p, blockC T p = 0 → G p = 0) :
    ∑ p : Blocks T, G p.1 = ∑ p, G p := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun p => blockC T p ≠ 0) (fun p => by rw [Finset.mem_filter]; simp [blockC]) G]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun p _ hp => hG p ?_
  simpa using hp

/-- `Q_b π(E^i_{αβ}) = 0` on a zero block. -/
lemma UC_zero (p : ι × Bool) (hp : blockC T p = 0) (x y : Fin (n p.1)) : Qb T p.2 * T.π (unitC p.1 x y) = 0 := by
  have h : unitC p.1 x y = Pi.single p.1 1 * unitC p.1 x y := by
    funext k
    by_cases hk : k = p.1
    · subst hk; simp [unitC]
    · simp [unitC, Pi.single_eq_of_ne hk]
  rw [h, map_mul, ← mul_assoc]
  rw [show Qb T p.2 * T.π (Pi.single p.1 1) = blockC T p from rfl, hp, zero_mul]

/-- **The units of a complex triple acting real-linearly.** -/
def unitsC : MatrixUnits (fun p : Blocks T => n p.1.1) H where
  U := UC T
  mul_same p x y z w := by
    rw [UC, UC, Qb_pi_mul_Qb_pi, Qb_mul_Qb, unitC_mul_same]
    by_cases hyz : y = z
    · rw [if_pos hyz, if_pos hyz, UC]
    · rw [if_neg hyz, if_neg hyz, map_zero, mul_zero]
  mul_ne p q hpq x y z w := by
    rw [UC, UC, Qb_pi_mul_Qb_pi]
    by_cases hb : p.1.2 = q.1.2
    · have hi : p.1.1 ≠ q.1.1 := fun hi => hpq (Subtype.ext (Prod.ext hi hb))
      rw [unitC_mul_ne _ _ hi, map_zero, mul_zero]
    · rw [Qb_mul_Qb_ne T _ _ hb, zero_mul]
  star_U p x y := by
    rw [UC, UC, star_mul, ← map_star, star_unitC, star_Qb, pi_comm_Qb]
  sum_U := by
    simp only [sum_UC]
    rw [sum_blocks T (blockC T) (fun p hp => hp), Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, blockC, ← add_mul]
    rw [Qb_true_add_false]
    simp only [one_mul]
    rw [← map_sum, Finset.univ_sum_single (fun i => (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ))]
    exact map_one T.π
/-- `∑_{xy} a^i_{xy} E^i_{xy} = aᵢ`, in summand `i`. -/
lemma sum_smul_unitC (a : MatSum n) (i : ι) : ∑ x, ∑ y, a i x y • unitC (n := n) i x y = Pi.single i (a i) := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply]
  by_cases hk : k = i
  · subst hk
    simp only [unitC, Pi.single_eq_same, Matrix.smul_single, smul_eq_mul, mul_one]
    exact (Matrix.matrix_eq_sum_single _).symm
  · simp only [unitC, Pi.single_eq_of_ne hk, smul_zero, Finset.sum_const_zero]

/-- `φ(a)` on the block `(i, b)`: `aᵢ` for `b = true`, `āᵢ` for `b = false`. -/
def phiCAll (a : MatSum n) (q : ι × Bool) : Matrix (Fin (n q.1)) (Fin (n q.1)) ℂ :=
  if q.2 then a q.1 else (a q.1).map (starRingEnd ℂ)

/-- `φ(a) = (aᵢ, āᵢ)` on the nonzero blocks. -/
def phiCFun (a : MatSum n) : MatSum (fun p : Blocks T => n p.1.1) := fun p => phiCAll a p.1

/-- **`⊕ Mₙᵢ(ℂ) → ⊕ M_{n_{i}}(ℂ)` over the nonzero blocks**, a real `*`-homomorphism (antilinear on the conjugate
blocks). -/
def phiC : MatSum n →⋆ₐ[ℝ] MatSum (fun p : Blocks T => n p.1.1) where
  toFun := phiCFun T
  map_one' := by
    funext p
    by_cases hb : p.1.2 = true <;> simp [phiCFun, phiCAll, hb]
  map_mul' a b := by
    funext p
    by_cases hb : p.1.2 = true <;> simp [phiCFun, phiCAll, hb, Matrix.map_mul]
  map_zero' := by
    funext p
    by_cases hb : p.1.2 = true <;> simp [phiCFun, phiCAll, hb]
  map_add' a b := by
    funext p
    by_cases hb : p.1.2 = true <;> simp [phiCFun, phiCAll, hb, Matrix.map_add]
  commutes' r := by
    show phiCFun T (algebraMap ℝ (MatSum n) r) = algebraMap ℝ _ r
    funext p
    refine Matrix.ext fun x y => ?_
    by_cases hb : p.1.2 = true <;> by_cases hxy : x = y <;>
      simp [phiCFun, phiCAll, hb, hxy, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
  map_star' a := by
    funext p
    refine Matrix.ext fun x y => ?_
    by_cases hb : p.1.2 = true <;> simp [phiCFun, phiCAll, hb, Matrix.star_apply]

/-- `phiC` is `phiCFun`. -/
lemma phiC_apply (a : MatSum n) : phiC T a = phiCFun T a := rfl

/-- `c Q₊ π(b) = Q₊ π(c b)`. -/
lemma Qb_true_pi_smul (c : ℂ) (b : MatSum n) : c • (Qb T true * T.π b) = Qb T true * T.π (c • b) :=
  (Qp_pi_smul T c b).symm

/-- `c̄ Q₋ π(b) = Q₋ π(c b)`. -/
lemma Qb_false_pi_smul (c : ℂ) (b : MatSum n) :
    starRingEnd ℂ c • (Qb T false * T.π b) = Qb T false * T.π (c • b) :=
  (Qm_pi_smul T c b).symm

/-- The contribution `∑_{xy} φ(a)_{xy} Q_b π(E^i_{xy})` of a block `(i, b)`. -/
def GC (a : MatSum n) (q : ι × Bool) : H →L[ℂ] H :=
  ∑ x, ∑ y, phiCAll a q x y • (Qb T q.2 * T.π (unitC q.1 x y))

/-- A zero block contributes nothing. -/
lemma GC_zero (a : MatSum n) (q : ι × Bool) (hq : blockC T q = 0) : GC T a q = 0 :=
  Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by rw [UC_zero T q hq x y, smul_zero]

/-- **`σ ∘ φ = π`**: on summand `i`, `Q₊ π(aᵢ) + Q₋ π(aᵢ) = π(aᵢ)`, the zero blocks contributing nothing. -/
lemma unitsC_hom_phiC (a : MatSum n) : (unitsC T).hom (phiC T a) = T.π a := by
  rw [MatrixUnits.hom_apply]
  change ∑ p : Blocks T, GC T a p.1 = _
  rw [sum_blocks T (GC T a) (GC_zero T a), Fintype.sum_prod_type]
  simp only [GC]
  simp only [Fintype.sum_bool, phiCAll, if_true, Bool.false_eq_true, if_false, Matrix.map_apply, Qb_true_pi_smul,
    Qb_false_pi_smul, ← Finset.mul_sum, ← map_sum, sum_smul_unitC, ← add_mul, Qb_true_add_false, one_mul]
  rw [Finset.univ_sum_single]

/-- **The complexification of a triple over `⊕ Mₙᵢ(ℂ)` acting real-linearly**: the fundamental and the conjugate
representations of each summand that occur in `H`. -/
def complexComplexification : Complexification T (fun p : Blocks T => n p.1.1) where
  σ := (unitsC T).hom
  injective_σ := (unitsC T).hom_injective_of_block fun p => by
    rw [show ∑ x, (unitsC T).U p x x = ∑ x, UC T p x x from rfl, sum_UC]
    exact p.2
  φ := phiC T
  pi_eq a := (unitsC_hom_phiC T a).symm
  mem_span Y := (unitsC T).hom_mem _ (fun p x y => Qb_pi_mem_span T _ _) Y

/-- **Uniqueness for complex summands acting real-linearly** (Krajewski, Section 3.1, p. 10, with Section 3.2, p. 13):
a real finite spectral triple over `⊕ Mₙᵢ(ℂ)` is unitarily equivalent to the model of the multiplicity matrix of its
complexification, indexed by the fundamental and conjugate representations `(i, ±)` that occur, with `π(a)` acting as
`aᵢ` on the fundamental ones and as `āᵢ` on the conjugate ones. -/
theorem exists_unitary_complexSummands [∀ i, NeZero (n i)] (R : RealStructure T) :
    ∃ U : H ≃ₗᵢ[ℂ] HK (fun p : Blocks T => n p.1.1)
        (fun p q => multiplicity ((complexComplexification T).realStructure R) p q),
      (∀ a x, U (T.π a x) = piK (phiC T a) (U x)) ∧
        ∀ x, U (R.J x) = JK (multiplicity_symm ((complexComplexification T).realStructure R)) (U x) :=
  (complexComplexification T).exists_unitary R

end

end Lightlike.NCG
