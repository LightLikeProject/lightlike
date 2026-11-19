import Lightlike.FieldTheory.Gaussian.FeynmanGraphs
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Feynman graphs with `1/|Aut Γ|` for a general polynomial potential

Polyak, *Feynman diagrams for pedestrians and mathematicians*, arXiv:math/0406251v1, §2.8, Proposition 2.17, eq. (19),
p. 9, for `U = Σ_κ V_κ/d_κ!` with homogeneous parts `V_κ` of degrees `d_κ` (vertices of several valences).

* For multiplicities `mult : K → ℕ` of the vertex types, the legs are `TLegs = Σ_κ Fin (mult κ) × Fin (d κ)`, the
  vertex-preserving and type-preserving permutations are `TPerm = Π_κ S_{d κ} ≀ S_{mult κ}` (acting through
  `Equiv.sigmaCongrRight`), and `tgraphWeight` is invariant for symmetric coefficient tensors;
* `integral_prod_pow_graphs`: `E_S[∏_κ (V_κ/d_κ!)^{mult κ}]/∏_κ (mult κ)! = Σ_Γ W(Γ)/|Aut Γ|` over the Feynman graphs
  with `mult κ` vertices of type `κ`;
* `integral_polyPot_pow_graphs`: `E_S[U^m]/m! = Σ_{mult, Σ mult = m} Σ_Γ W(Γ)/|Aut Γ|`, the coefficient of `ħ^m` in
  (19), by the multinomial theorem.

Differences from the source: (convention) the `1/k!` normalisation of the potential, as for `FeynmanGraphs`;
(representation) symmetric coefficient tensors, moments of the normalised measure, graphs as orbits of leg pairings,
graded by the numbers of vertices of each type; Polyak's restriction to valences `≥ 3` is replaced by `d κ > 0`.
-/

namespace Lightlike.FieldTheory

open Finset MulAction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The pairing sum through an equivalence** of the positions with `Fin n`. -/
theorem pairSum_comp_equiv (S : Matrix ι ι ℝ) (hS : S.IsSymm) {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (e : α ≃ Fin n) (x : α → ι) [Fintype {f : α → α // Function.Involutive f ∧ ∀ h, f h ≠ h}] :
    pairSum S (x ∘ e.symm) = ∑ f : {f : α → α // Function.Involutive f ∧ ∀ h, f h ≠ h},
      ∏ s ∈ edges f.1, edgeWeight S hS x s := by
  classical
  rw [pairSum_eq_sum_involutions S hS]
  refine Fintype.sum_equiv (pairingCongr e).symm _ _ fun f => ?_
  have hf : f.1 = e ∘ ((pairingCongr e).symm f).1 ∘ e.symm := by
    funext k
    show f.1 k = e (e.symm (f.1 (e (e.symm k))))
    simp only [Equiv.apply_symm_apply]
  have hl : (x ∘ e.symm) ∘ e = x := by funext h; simp
  rw [hf, prod_edges_conj, hl]

/-- The vertex labels are invariant in the coefficient product, for a symmetric tensor. -/
lemma prod_relabel {m d : ℕ} {c : (Fin d → ι) → ℝ} (hc : ∀ (j : Fin d → ι) (τ : Equiv.Perm (Fin d)), c (j ∘ τ) = c j)
    (g : legPerm m d) (i : Fin m → Fin d → ι) : ∏ v, c (relabel g i v) = ∏ v, c (i v) := by
  have h1 : ∀ v, relabel g i v = i ((Classical.choose g.2) v) ∘ legPermAt g v := fun v => by
    funext a
    show i (g.1 (v, a)).1 (g.1 (v, a)).2 = i ((Classical.choose g.2) v) ((g.1 (v, a)).2)
    rw [legPerm_fst]
  simp_rw [h1, hc]
  exact Equiv.prod_comp (Classical.choose g.2) (fun v => c (i v))

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The legs of `mult κ` vertices of each type `κ`, of degree `d κ`. -/
abbrev TLegs (mult d : K → ℕ) : Type _ := Σ κ : K, Fin (mult κ) × Fin (d κ)

/-- The pairings of the legs. -/
abbrev TPairing (mult d : K → ℕ) : Type _ :=
  {f : TLegs mult d → TLegs mult d // Function.Involutive f ∧ ∀ h, f h ≠ h}

noncomputable instance (mult d : K → ℕ) : Fintype (TPairing mult d) := Fintype.ofFinite _

/-- The type-preserving, vertex-preserving permutations `Π_κ S_{d κ} ≀ S_{mult κ}`. -/
abbrev TPerm (mult d : K → ℕ) : Type _ := (κ : K) → legPerm (mult κ) (d κ)

/-- The permutation of the legs made by `g`. -/
def tperm {mult d : K → ℕ} (g : TPerm mult d) : Equiv.Perm (TLegs mult d) :=
  Equiv.sigmaCongrRight fun κ => (g κ).1

instance (mult d : K → ℕ) : MulAction (TPerm mult d) (TPairing mult d) where
  smul g f := ⟨tperm g ∘ f.1 ∘ (tperm g).symm, fun h => by
      simp only [Function.comp_apply, Equiv.symm_apply_apply, f.2.1 ((tperm g).symm h), Equiv.apply_symm_apply],
    fun h hh => by
      apply f.2.2 ((tperm g).symm h)
      have := congrArg (tperm g).symm hh
      simpa using this⟩
  one_smul _ := by apply Subtype.ext; rfl
  mul_smul _ _ _ := by apply Subtype.ext; rfl

/-- **The order of the type-graded wreath product**: `|Π_κ S_{d κ} ≀ S_{mult κ}| = ∏_κ (d κ!)^{mult κ} (mult κ)!`. -/
lemma card_tperm {mult d : K → ℕ} (hd : ∀ κ, 0 < d κ) :
    Nat.card (TPerm mult d) = ∏ κ, (d κ).factorial ^ mult κ * (mult κ).factorial := by
  rw [Nat.card_pi]
  exact Finset.prod_congr rfl fun κ _ => card_legPerm (hd κ)

/-- The leg labels of a labelling of the vertices of every type. -/
def legLabT {mult d : K → ℕ} (i : (κ : K) → Fin (mult κ) → Fin (d κ) → ι) (h : TLegs mult d) : ι :=
  i h.1 h.2.1 h.2.2

/-- **The graph weight** for vertices of several types. -/
def tgraphWeight (S : Matrix ι ι ℝ) (hS : S.IsSymm) {mult d : K → ℕ} (c : (κ : K) → (Fin (d κ) → ι) → ℝ)
    (f : TPairing mult d) : ℝ :=
  ∑ i : (κ : K) → Fin (mult κ) → Fin (d κ) → ι,
    (∏ κ, ∏ v, c κ (i κ v)) * ∏ e ∈ edges f.1, edgeWeight S hS (legLabT i) e

/-- **The graph weight is invariant**, for symmetric coefficient tensors. -/
theorem tgraphWeight_smul (S : Matrix ι ι ℝ) (hS : S.IsSymm) {mult d : K → ℕ}
    {c : (κ : K) → (Fin (d κ) → ι) → ℝ} (hc : ∀ κ (j : Fin (d κ) → ι) (τ : Equiv.Perm (Fin (d κ))), c κ (j ∘ τ) = c κ j)
    (g : TPerm mult d) (f : TPairing mult d) : tgraphWeight S hS c (g • f) = tgraphWeight S hS c f := by
  unfold tgraphWeight
  let R : ((κ : K) → Fin (mult κ) → Fin (d κ) → ι) ≃ ((κ : K) → Fin (mult κ) → Fin (d κ) → ι) :=
    Equiv.piCongrRight fun κ => relabel (g κ)
  have hedge : ∀ i, ∏ e ∈ edges (g • f).1, edgeWeight S hS (legLabT i) e =
      ∏ e ∈ edges f.1, edgeWeight S hS (legLabT (R i)) e := fun i => by
    rw [show (g • f).1 = tperm g ∘ f.1 ∘ (tperm g).symm from rfl, prod_edges_conj]
    rfl
  have hcoef : ∀ i, ∏ κ, ∏ v, c κ (R i κ v) = ∏ κ, ∏ v, c κ (i κ v) := fun i =>
    Finset.prod_congr rfl fun κ _ => prod_relabel (hc κ) (g κ) (i κ)
  simp_rw [hedge]
  refine Fintype.sum_equiv R _ _ fun i => ?_
  rw [hcoef]

/-- `∏_κ V_κ^{mult κ}` as a sum over the labellings. -/
lemma prod_homogPoly_pow {mult d : K → ℕ} (c : (κ : K) → (Fin (d κ) → ι) → ℝ) (x : EuclideanSpace ℝ ι) :
    ∏ κ, homogPoly (c κ) x ^ mult κ = ∑ i : (κ : K) → Fin (mult κ) → Fin (d κ) → ι,
      (∏ κ, ∏ v, c κ (i κ v)) * ∏ h : TLegs mult d, x (legLabT i h) := by
  simp_rw [homogPoly_pow, mono_ofFn, prod_legLabels]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun κ _ => ?_
  rw [← Fintype.prod_prod_type']
  rfl

/-- **Feynman graphs for vertices of several types** (Polyak, Proposition 2.17, eq. (19), p. 9): for symmetric
coefficient tensors, `E_S[∏_κ (V_κ/d_κ!)^{mult κ}]/∏_κ (mult κ)! = Σ_Γ W(Γ)/|Aut Γ|`. -/
theorem integral_prod_pow_graphs {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (hSym : S.IsSymm) {d : K → ℕ}
    (hd : ∀ κ, 0 < d κ) {c : (κ : K) → (Fin (d κ) → ι) → ℝ}
    (hc : ∀ κ (j : Fin (d κ) → ι) (τ : Equiv.Perm (Fin (d κ))), c κ (j ∘ τ) = c κ j) (mult : K → ℕ)
    [Fintype (Quotient (orbitRel (TPerm mult d) (TPairing mult d)))] :
    (∫ x, ∏ κ, (homogPoly (c κ) x / (d κ).factorial) ^ mult κ
        ∂(ProbabilityTheory.multivariateGaussian 0 S)) / ∏ κ, ((mult κ).factorial : ℝ) =
      ∑ Γ : Quotient (orbitRel (TPerm mult d) (TPairing mult d)),
        tgraphWeight S hSym c Γ.out / Nat.card (stabilizer (TPerm mult d) Γ.out) := by
  classical
  let eL := Fintype.equivFin (TLegs mult d)
  have hmono : ∀ (i : (κ : K) → Fin (mult κ) → Fin (d κ) → ι) (x : EuclideanSpace ℝ ι),
      ∏ h : TLegs mult d, x (legLabT i h) = mono (List.ofFn (legLabT i ∘ eL.symm)) x := fun i x => by
    rw [mono_ofFn]
    exact (Fintype.prod_equiv eL _ _ fun h => by simp).trans rfl
  have h1 : ∫ x, ∏ κ, (homogPoly (c κ) x / (d κ).factorial) ^ mult κ
      ∂(ProbabilityTheory.multivariateGaussian 0 S) =
      (∑ f : TPairing mult d, tgraphWeight S hSym c f) / ∏ κ, ((d κ).factorial : ℝ) ^ mult κ := by
    simp_rw [div_pow, Finset.prod_div_distrib, prod_homogPoly_pow, hmono]
    rw [MeasureTheory.integral_div,
      MeasureTheory.integral_finsetSum _ fun i _ => (integrable_mono S _).const_mul _]
    congr 1
    have hmom : ∀ l : List ι, ∫ x, mono l x ∂(ProbabilityTheory.multivariateGaussian 0 S) = moment S l :=
      fun _ => rfl
    simp_rw [MeasureTheory.integral_const_mul, hmom, moment_ofFn_eq_pairSum_of_posSemidef hS,
      pairSum_comp_equiv S hSym eL, Finset.mul_sum]
    rw [Finset.sum_comm]
    rfl
  rw [h1, sum_eq_sum_orbits _ (tgraphWeight_smul S hSym hc), card_tperm hd, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun Γ _ => ?_
  have hf : ∏ κ, ((d κ).factorial : ℝ) ^ mult κ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun κ _ => pow_ne_zero _ (by positivity)
  have hm : ∏ κ, ((mult κ).factorial : ℝ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun κ _ => by positivity
  push_cast
  rw [Finset.prod_mul_distrib]
  field_simp


/-- `∏_κ (V_κ/d_κ!)^{mult κ}` is integrable (a polynomial). -/
lemma integrable_prod_pow (S : Matrix ι ι ℝ) {d : K → ℕ} (c : (κ : K) → (Fin (d κ) → ι) → ℝ) (mult : K → ℕ) :
    MeasureTheory.Integrable (fun x => ∏ κ, (homogPoly (c κ) x / (d κ).factorial) ^ mult κ)
      (ProbabilityTheory.multivariateGaussian 0 S) := by
  classical
  let eL := Fintype.equivFin (TLegs mult d)
  have he : (fun x => ∏ κ, (homogPoly (c κ) x / (d κ).factorial) ^ mult κ) = fun x =>
      (∑ i : (κ : K) → Fin (mult κ) → Fin (d κ) → ι, (∏ κ, ∏ v, c κ (i κ v)) *
        mono (List.ofFn (legLabT i ∘ eL.symm)) x) / ∏ κ, ((d κ).factorial : ℝ) ^ mult κ := by
    funext x
    simp_rw [div_pow, Finset.prod_div_distrib, prod_homogPoly_pow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mono_ofFn]
    exact congrArg _ ((Fintype.prod_equiv eL _ _ fun h => by simp).trans rfl)
  rw [he]
  exact (MeasureTheory.integrable_finset_sum _ fun i _ => (integrable_mono S _).const_mul _).div_const _

/-- **The Feynman graph expansion for a polynomial potential** (Polyak, Proposition 2.17, eq. (19), p. 9): for
`U = Σ_κ V_κ/d_κ!` with symmetric coefficient tensors, `E_S[U^m]/m! = Σ_{mult, Σ_κ mult κ = m} Σ_Γ W(Γ)/|Aut Γ|`,
the sum over the Feynman graphs with `m` vertices, `mult κ` of them of type `κ`. -/
theorem integral_polyPot_pow_graphs {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (hSym : S.IsSymm) {d : K → ℕ}
    (hd : ∀ κ, 0 < d κ) {c : (κ : K) → (Fin (d κ) → ι) → ℝ}
    (hc : ∀ κ (j : Fin (d κ) → ι) (τ : Equiv.Perm (Fin (d κ))), c κ (j ∘ τ) = c κ j) (m : ℕ)
    [∀ mult : K → ℕ, Fintype (Quotient (orbitRel (TPerm mult d) (TPairing mult d)))] :
    (∫ x, (∑ κ, homogPoly (c κ) x / (d κ).factorial) ^ m ∂(ProbabilityTheory.multivariateGaussian 0 S)) /
        m.factorial =
      ∑ mult ∈ piAntidiag univ m, ∑ Γ : Quotient (orbitRel (TPerm mult d) (TPairing mult d)),
        tgraphWeight S hSym c Γ.out / Nat.card (stabilizer (TPerm mult d) Γ.out) := by
  classical
  have hpow : ∀ x : EuclideanSpace ℝ ι, (∑ κ, homogPoly (c κ) x / (d κ).factorial) ^ m / m.factorial =
      ∑ mult ∈ piAntidiag univ m,
        (∏ κ, (homogPoly (c κ) x / (d κ).factorial) ^ mult κ) / ∏ κ, ((mult κ).factorial : ℝ) := by
    intro x
    rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_div]
    refine Finset.sum_congr rfl fun mult hmult => ?_
    rw [mem_piAntidiag] at hmult
    have hspec := Nat.multinomial_spec univ mult
    rw [hmult.1] at hspec
    have hspecR : (∏ κ, ((mult κ).factorial : ℝ)) * (Nat.multinomial univ mult : ℝ) = m.factorial := by
      exact_mod_cast hspec
    have hprod : (∏ κ, ((mult κ).factorial : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun κ _ => by positivity
    have hm : (m.factorial : ℝ) ≠ 0 := by positivity
    rw [div_eq_div_iff hm hprod, ← hspecR]
    ring
  rw [← MeasureTheory.integral_div]
  simp_rw [hpow]
  rw [MeasureTheory.integral_finsetSum _ fun mult _ => (integrable_prod_pow S c mult).div_const _]
  refine Finset.sum_congr rfl fun mult _ => ?_
  rw [MeasureTheory.integral_div, integral_prod_pow_graphs hS hSym hd hc mult]

end Lightlike.FieldTheory
