module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The spin representations of `SU(2)` and their irreducibility

For every `n : ℕ` (twice the spin, `n = 2j`) we construct a unitary representation of
`SU(2) = Matrix.specialUnitaryGroup (Fin 2) ℂ` on `ℂ^{n+1}`, as the symmetric part of the `n`-th
tensor power of the standard representation, and prove that it is irreducible.

## Main definitions

* `SU2Spin.kron n g`: the `n`-fold Kronecker power `g^{⊗n}` of a `2 × 2` matrix, on `ℂ^{Str n}`.
* `SU2Spin.emb n`: the isometry `ℂ^{n+1} → ℂ^{Str n}` onto the permutation-symmetric vectors.
* `SU2Spin.spinMat n g = embᴴ · g^{⊗n} · emb`.
* `SU2Spin.spinRep n : SU(2) →* unitaryGroup (Fin (n+1)) ℂ` and
  `SU2Spin.spinRepresentation n : Representation ℂ SU(2) (Fin (n+1) → ℂ)`.

## Main results

* `SU2Spin.spinMat_mul`, `SU2Spin.spinMat_one`, `SU2Spin.spinMat_mem_unitaryGroup`: it is a unitary
  representation.
* `SU2Spin.continuous_spinMat`, `SU2Spin.continuous_spinMat_comp`: continuity (polynomial entries).
* `SU2Spin.kron_mul_emb`, `SU2Spin.finrank_symSubspace`: `spinMat n` is `g^{⊗n}` restricted to the
  symmetric subspace, which has dimension `n + 1`.
* `SU2Spin.spinMat_torus_exp`: the weights `m = j, …, -j`; `SU2Spin.spinMat_negOne`: `-1 ↦ (-1)^n`.
* `SU2Spin.spinRepresentation_isIrreducible`: the spin-`n/2` representation is irreducible.

## Implementation notes

Irreducibility: an invariant subspace averaged over a finite cyclic subgroup of the diagonal torus
(the `n+1` weights are distinct `(2n+1)`-th roots of unity) contains a basis vector; the rotation
by `π/2` about the `y`-axis, whose spin matrix has nowhere-vanishing last row and column, then
produces all basis vectors.

## References

* [Hall, *Lie Groups, Lie Algebras, and Representations*, Ch. 4][hall-2015]
-/

@[expose] public section

open Matrix Finset

namespace SU2Spin

/-- The group `SU(2)`, as Mathlib's special unitary group of `2 × 2` complex matrices. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- Basis labels of `(ℂ²)^{⊗n}`: strings of `n` one-spin labels (`0` = up, `1` = down). -/
abbrev Str (n : ℕ) := Fin n → Fin 2

variable {n : ℕ}

/-! ### Strings and their number of down labels -/

/-- The number of down labels (`1`s) in a string. -/
def downs (s : Str n) : ℕ := #(univ.filter fun i => s i = 1)

lemma downs_le (s : Str n) : downs s ≤ n :=
  (card_filter_le _ _).trans (by simp)

lemma downs_comp (s : Str n) (σ : Equiv.Perm (Fin n)) : downs (s ∘ σ) = downs s :=
  card_equiv σ (by simp)

/-- The fibre sizes of a string over `0` and `1` are `n - downs s` and `downs s`. -/
lemma card_fiber (s : Str n) (c : Fin 2) :
    Fintype.card {i // s i = c} = if c = 1 then downs s else n - downs s := by
  have h1 : Fintype.card {i // s i = 1} = downs s := by
    rw [Fintype.card_subtype]; rfl
  have hc : ∀ x : Fin 2, x = 0 ↔ ¬ x = 1 := by decide
  fin_cases c
  · simp only [Fin.zero_eta, Fin.isValue, zero_ne_one, ↓reduceIte]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight fun i => hc (s i)),
      Fintype.card_subtype_compl, Fintype.card_fin, h1]
  · simpa using h1

/-- Two strings with the same number of down labels differ by a permutation of the slots. -/
lemma exists_perm_of_downs_eq {s t : Str n} (h : downs s = downs t) :
    ∃ σ : Equiv.Perm (Fin n), s = t ∘ σ := by
  have e : ∀ c, {i // s i = c} ≃ {i // t i = c} := fun c =>
    Fintype.equivOfCardEq (by rw [card_fiber, card_fiber, h])
  exact ⟨Equiv.ofFiberEquiv e, funext fun a => (Equiv.ofFiberEquiv_map e a).symm⟩

/-- A vector on strings is *symmetric* if it is invariant under all permutations of the slots. -/
def IsSym (v : Str n → ℂ) : Prop := ∀ (σ : Equiv.Perm (Fin n)) (s : Str n), v (s ∘ σ) = v s

/-- A symmetric vector depends only on the number of down labels. -/
lemma IsSym.eq_of_downs_eq {v : Str n → ℂ} (hv : IsSym v) {s t : Str n}
    (h : downs s = downs t) : v s = v t := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_downs_eq h
  exact hv σ t

/-! ### The Kronecker power `g^{⊗n}` -/

/-- The `n`-fold Kronecker power of a `2 × 2` matrix: `(g^{⊗n})_{s t} = ∏ᵢ g (s i) (t i)`. -/
def kron (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Str n) (Str n) ℂ :=
  Matrix.of fun s t => ∏ i, g (s i) (t i)

lemma kron_apply (g : Matrix (Fin 2) (Fin 2) ℂ) (s t : Str n) :
    kron n g s t = ∏ i, g (s i) (t i) := rfl

theorem kron_mul (g h : Matrix (Fin 2) (Fin 2) ℂ) : kron n (g * h) = kron n g * kron n h := by
  ext s u
  simp only [kron_apply, mul_apply]
  rw [prod_univ_sum, Fintype.piFinset_univ]
  simp [prod_mul_distrib]

theorem kron_one : kron n (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext s t
  simp only [kron_apply, one_apply]
  by_cases hst : s = t
  · subst hst; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hst
    simp only [hst, ↓reduceIte]
    exact prod_eq_zero (mem_univ i) (by simp [hi])

theorem kron_conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ) : (kron n g)ᴴ = kron n gᴴ := by
  ext s t
  simp [kron_apply, conjTranspose_apply, star_prod]

/-- Permuting the slots, as a bijection of strings: `t ↦ t ∘ σ`. -/
def permStr (σ : Equiv.Perm (Fin n)) : Str n ≃ Str n where
  toFun t := t ∘ σ
  invFun t := t ∘ σ.symm
  left_inv t := by ext; simp
  right_inv t := by ext; simp

@[simp] lemma permStr_apply (σ : Equiv.Perm (Fin n)) (t : Str n) : permStr σ t = t ∘ σ := rfl

/-- `g^{⊗n}` maps symmetric vectors to symmetric vectors. -/
lemma isSym_kron_mulVec (g : Matrix (Fin 2) (Fin 2) ℂ) {v : Str n → ℂ} (hv : IsSym v) :
    IsSym (kron n g *ᵥ v) := by
  intro σ s
  simp only [mulVec, dotProduct, kron_apply]
  rw [← Equiv.sum_comp (permStr σ)]
  refine sum_congr rfl fun t _ => ?_
  rw [permStr_apply, hv σ t]
  congr 1
  exact Equiv.prod_comp σ (fun i => g (s i) (t i))

/-! ### The isometric embedding of `ℂ^{n+1}` onto the symmetric vectors -/

/-- The strings with exactly `k` down labels. -/
def cls (n k : ℕ) : Finset (Str n) := univ.filter fun s => downs s = k

/-- The number of strings with exactly `k` down labels (it is `n.choose k`; not needed here). -/
def clsCard (n k : ℕ) : ℕ := #(cls n k)

lemma clsCard_pos {k : ℕ} (hk : k ≤ n) : 0 < clsCard n k := by
  refine card_pos.mpr ⟨fun i => if (i : ℕ) < k then 1 else 0, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  show #(univ.filter fun i : Fin n => (if (i : ℕ) < k then (1 : Fin 2) else 0) = 1) = k
  have : (univ.filter fun i : Fin n => (if (i : ℕ) < k then (1 : Fin 2) else 0) = 1) =
      univ.filter fun i : Fin n => (i : ℕ) < k := by
    ext i; by_cases h : (i : ℕ) < k <;> simp [h]
  rw [this, Fin.card_filter_val_lt, min_eq_right hk]

/-- The normalisation `1/√(clsCard n k)` of the `k`-th symmetric basis vector. -/
noncomputable def nrm (n k : ℕ) : ℂ := ((Real.sqrt (clsCard n k))⁻¹ : ℝ)

lemma star_nrm (n k : ℕ) : star (nrm n k) = nrm n k := by
  simp [nrm]

lemma nrm_mul_nrm {k : ℕ} (hk : k ≤ n) : nrm n k * nrm n k * clsCard n k = 1 := by
  have hpos : (0 : ℝ) < clsCard n k := by exact_mod_cast clsCard_pos hk
  simp only [nrm, ← Complex.ofReal_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
  rw [← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  simp

lemma nrm_ne_zero {k : ℕ} (hk : k ≤ n) : nrm n k ≠ 0 := by
  have hpos : (0 : ℝ) < clsCard n k := by exact_mod_cast clsCard_pos hk
  simp [nrm, hpos.ne']

/-- Column `k`: the normalised indicator of the strings with `k` down labels. -/
noncomputable def emb (n : ℕ) : Matrix (Str n) (Fin (n + 1)) ℂ :=
  Matrix.of fun s k => if downs s = k then nrm n k else 0

lemma emb_apply (s : Str n) (k : Fin (n + 1)) :
    emb n s k = if downs s = k then nrm n k else 0 := rfl

/-- The columns of `emb` are symmetric. -/
lemma isSym_emb (k : Fin (n + 1)) : IsSym fun s => emb n s k := by
  intro σ s
  simp only [emb_apply, downs_comp]

/-- `emb` is an isometry: its columns are orthonormal. -/
theorem emb_conjTranspose_mul_emb : (emb n)ᴴ * emb n = 1 := by
  ext j k
  simp only [mul_apply, conjTranspose_apply, emb_apply, one_apply]
  by_cases hjk : j = k
  · subst hjk
    simp only [↓reduceIte]
    have : ∀ s : Str n, star (if downs s = (j : ℕ) then nrm n j else 0) *
        (if downs s = (j : ℕ) then nrm n j else 0) =
        if s ∈ cls n j then nrm n j * nrm n j else 0 := by
      intro s; by_cases h : downs s = j <;> simp [cls, h, star_nrm]
    simp only [this, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    rw [← nrm_mul_nrm (Nat.lt_succ_iff.mp j.2)]
    simp [clsCard]; ring
  · simp only [hjk, ↓reduceIte]
    refine sum_eq_zero fun s _ => ?_
    by_cases h : downs s = j
    · have : ¬ downs s = k := fun h' => hjk (Fin.ext (h.symm.trans h'))
      simp [this]
    · simp [h]

/-- `emb · embᴴ` is the orthogonal projection onto symmetric vectors, entrywise. -/
lemma emb_mul_conjTranspose_apply (s t : Str n) :
    (emb n * (emb n)ᴴ) s t =
      if downs t = downs s then nrm n (downs s) * nrm n (downs s) else 0 := by
  simp only [mul_apply, conjTranspose_apply, emb_apply]
  rw [sum_eq_single ⟨downs s, Nat.lt_succ_of_le (downs_le s)⟩]
  · by_cases h : downs t = downs s <;> simp [h, star_nrm]
  · intro k _ hk
    have : ¬ downs s = k := fun h => hk (Fin.ext h.symm)
    simp [this]
  · simp

/-- On a matrix with symmetric columns, `emb · embᴴ` acts as the identity. -/
theorem emb_mul_conjTranspose_mul_of_isSym {ι : Type*} (X : Matrix (Str n) ι ℂ)
    (hX : ∀ k, IsSym fun s => X s k) : emb n * (emb n)ᴴ * X = X := by
  ext s k
  rw [mul_apply]
  simp only [emb_mul_conjTranspose_apply]
  have : ∀ t : Str n, (if downs t = downs s then nrm n (downs s) * nrm n (downs s) else 0) *
      X t k = if t ∈ cls n (downs s) then nrm n (downs s) * nrm n (downs s) * X s k else 0 := by
    intro t
    by_cases h : downs t = downs s
    · simp [cls, h, (hX k).eq_of_downs_eq h]
    · simp [cls, h]
  simp only [this, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  have h1 := nrm_mul_nrm (downs_le s)
  simp only [clsCard] at h1
  linear_combination X s k * h1

/-! ### The spin-`n/2` matrices: a unitary representation -/

/-- The spin-`n/2` matrix of `g`: the compression of `g^{⊗n}` to the symmetric subspace. -/
noncomputable def spinMat (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (emb n)ᴴ * kron n g * emb n

/-- `g^{⊗n} · emb` has symmetric columns, so `emb · embᴴ` fixes it. -/
lemma emb_mul_conjTranspose_mul_kron_mul_emb (g : Matrix (Fin 2) (Fin 2) ℂ) :
    emb n * (emb n)ᴴ * (kron n g * emb n) = kron n g * emb n := by
  refine emb_mul_conjTranspose_mul_of_isSym _ fun k => ?_
  have := isSym_kron_mulVec g (isSym_emb (n := n) k)
  intro σ s
  simpa [mulVec, dotProduct, mul_apply] using this σ s

/-- `spinMat n` is multiplicative: `spinMat n (g h) = spinMat n g · spinMat n h`. -/
theorem spinMat_mul (g h : Matrix (Fin 2) (Fin 2) ℂ) :
    spinMat n (g * h) = spinMat n g * spinMat n h := by
  have key := emb_mul_conjTranspose_mul_kron_mul_emb (n := n) h
  simp only [spinMat, kron_mul]
  calc (emb n)ᴴ * (kron n g * kron n h) * emb n
      = (emb n)ᴴ * kron n g * (kron n h * emb n) := by simp only [Matrix.mul_assoc]
    _ = (emb n)ᴴ * kron n g * (emb n * (emb n)ᴴ * (kron n h * emb n)) := by rw [key]
    _ = (emb n)ᴴ * kron n g * emb n * ((emb n)ᴴ * kron n h * emb n) := by
        simp only [Matrix.mul_assoc]

theorem spinMat_one : spinMat n 1 = 1 := by
  simp [spinMat, kron_one, emb_conjTranspose_mul_emb]

theorem spinMat_conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinMat n g)ᴴ = spinMat n gᴴ := by
  simp [spinMat, conjTranspose_mul, kron_conjTranspose, Matrix.mul_assoc]

/-- Unitary `g` gives a unitary spin matrix. -/
theorem spinMat_mem_unitaryGroup {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    spinMat n g ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, spinMat_conjTranspose, ← spinMat_mul,
    ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp hg, spinMat_one]

/-- **The spin-`n/2` unitary representation of the group SU(2)** on `ℂ^{n+1}`. -/
noncomputable def spinRep (n : ℕ) : SU2 →* Matrix.unitaryGroup (Fin (n + 1)) ℂ where
  toFun g := ⟨spinMat n g, spinMat_mem_unitaryGroup (specialUnitaryGroup_le_unitaryGroup g.2)⟩
  map_one' := Subtype.ext spinMat_one
  map_mul' g h := Subtype.ext (spinMat_mul (g : Matrix (Fin 2) (Fin 2) ℂ) h)

@[simp] lemma spinRep_apply (g : SU2) : (spinRep n g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
    spinMat n g := rfl

/-- **Continuity.** `g ↦ spinMat n g` is continuous (its entries are polynomials in those of `g`). -/
theorem continuous_spinMat :
    Continuous fun g : Matrix (Fin 2) (Fin 2) ℂ => spinMat n g := by
  have hk : Continuous fun g : Matrix (Fin 2) (Fin 2) ℂ => kron n g :=
    continuous_matrix fun s t => by
      simp only [kron_apply]
      exact continuous_finsetProd _ fun i _ => continuous_id.matrix_elem (s i) (t i)
  exact (continuous_const.matrix_mul hk).matrix_mul continuous_const

/-- `spinMat n` composed with any continuous family of `2 × 2` matrices on any topological space
is continuous. -/
theorem continuous_spinMat_comp {X : Type*} [TopologicalSpace X]
    {f : X → Matrix (Fin 2) (Fin 2) ℂ} (hf : Continuous f) :
    Continuous fun x => spinMat n (f x) :=
  continuous_spinMat.comp hf

/-- The spin-`n/2` representation is a continuous homomorphism `SU(2) → U(n+1)`. -/
theorem continuous_spinRep :
    Continuous fun g : SU2 => (spinRep n g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
  continuous_spinMat_comp continuous_subtype_val

/-- The same representation in Mathlib's `Representation` form (acting on `Fin (n+1) → ℂ`). -/
noncomputable def spinRepresentation (n : ℕ) : Representation ℂ SU2 (Fin (n + 1) → ℂ) where
  toFun g := Matrix.toLin' (spinMat n g)
  map_one' := by simp [spinMat_one]; rfl
  map_mul' g h := by
    simp only [Submonoid.coe_mul, spinMat_mul, Matrix.toLin'_mul]; rfl

lemma spinRepresentation_apply (g : SU2) (v : Fin (n + 1) → ℂ) :
    spinRepresentation n g v = spinMat n g *ᵥ v := rfl

/-- `g^{⊗n}` restricted to the symmetric subspace *is* the spin matrix:
`g^{⊗n} · emb = emb · spinMat n g`. -/
theorem kron_mul_emb (g : Matrix (Fin 2) (Fin 2) ℂ) :
    kron n g * emb n = emb n * spinMat n g := by
  rw [← emb_mul_conjTranspose_mul_kron_mul_emb g, spinMat]
  simp only [Matrix.mul_assoc]

/-! ### The symmetric subspace and the dimension `2j + 1 = n + 1` -/

/-- The permutation-symmetric subspace of `(ℂ²)^{⊗n}`. -/
def symSubspace (n : ℕ) : Submodule ℂ (Str n → ℂ) where
  carrier := {v | IsSym v}
  add_mem' {v w} hv hw σ s := by simp [hv σ s, hw σ s]
  zero_mem' σ s := rfl
  smul_mem' c v hv σ s := by simp [hv σ s]

/-- `embᴴ` is a left inverse of `emb`, so `emb` is injective. -/
lemma emb_injective : Function.Injective (Matrix.toLin' (emb n)) := by
  intro x y hxy
  have := congrArg (Matrix.toLin' (emb n)ᴴ) hxy
  simpa [← Matrix.toLin'_mul_apply, emb_conjTranspose_mul_emb] using this

/-- The symmetric subspace is exactly the range of `emb`. -/
theorem symSubspace_eq_range : symSubspace n = LinearMap.range (Matrix.toLin' (emb n)) := by
  ext v
  constructor
  · intro hv
    refine ⟨(emb n)ᴴ *ᵥ v, ?_⟩
    let X : Matrix (Str n) Unit ℂ := Matrix.of fun s _ => v s
    have hX := emb_mul_conjTranspose_mul_of_isSym X (fun _ => hv)
    ext s
    have := congrFun (congrFun hX s) ()
    simpa [X, mul_apply, mulVec, dotProduct, Matrix.toLin'_apply, Finset.mul_sum,
      Matrix.mul_assoc, mul_comm, mul_left_comm, Finset.sum_comm (γ := Fin (n + 1))] using this
  · rintro ⟨c, rfl⟩ σ s
    simp [Matrix.toLin'_apply, mulVec, dotProduct, emb_apply, downs_comp]

/-- **Dimension**: the spin-`n/2` space (symmetric part of `n` spins ½) has dimension `n + 1`,
i.e. `2j + 1`. -/
theorem finrank_symSubspace : Module.finrank ℂ (symSubspace n) = n + 1 := by
  rw [symSubspace_eq_range, LinearMap.finrank_range_of_inj emb_injective, Module.finrank_fin_fun]

/-! ### Weights: the diagonal subgroup and the centre -/

/-- `∏ᵢ f (s i) = f 0 ^ (n - downs s) · f 1 ^ downs s`. -/
lemma prod_fin_two (f : Fin 2 → ℂ) (s : Str n) :
    ∏ i, f (s i) = f 0 ^ (n - downs s) * f 1 ^ downs s := by
  have hc : ∀ x : Fin 2, ¬ x = 1 → x = 0 := by decide
  rw [← prod_filter_mul_prod_filter_not univ (fun i => s i = 1)]
  have h1 : ∏ i ∈ univ.filter (fun i => s i = 1), f (s i) = f 1 ^ downs s := by
    rw [prod_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2]), prod_const]; rfl
  have h0 : ∏ i ∈ univ.filter (fun i => ¬ s i = 1), f (s i) = f 0 ^ (n - downs s) := by
    rw [prod_congr rfl (fun i hi => by rw [hc _ (mem_filter.mp hi).2]), prod_const]
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (p := fun i => s i = 1)
    simp only [card_univ, Fintype.card_fin] at this
    unfold downs; congr 1; omega
  rw [h1, h0, mul_comm]

lemma kron_diagonal (d : Fin 2 → ℂ) :
    kron n (diagonal d) = diagonal fun s => d 0 ^ (n - downs s) * d 1 ^ downs s := by
  ext s t
  by_cases hst : s = t
  · subst hst; simp [kron_apply, prod_fin_two (f := d)]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hst
    rw [diagonal_apply_ne _ hst, kron_apply]
    exact prod_eq_zero (mem_univ i) (diagonal_apply_ne _ hi)

/-- **Weights.** A diagonal matrix `diag(a, b)` acts diagonally in the symmetric basis: the
`k`-th basis vector (`k` spins down) gets `a^(n-k) b^k`. -/
theorem spinMat_diagonal (d : Fin 2 → ℂ) :
    spinMat n (diagonal d) = diagonal fun k : Fin (n + 1) => d 0 ^ (n - k) * d 1 ^ (k : ℕ) := by
  have hcomm : diagonal (fun s : Str n => d 0 ^ (n - downs s) * d 1 ^ downs s) * emb n =
      emb n * diagonal fun k : Fin (n + 1) => d 0 ^ (n - k) * d 1 ^ (k : ℕ) := by
    ext s k
    simp only [diagonal_mul, mul_diagonal, emb_apply]
    by_cases h : downs s = k <;> simp [h, mul_comm]
  rw [spinMat, kron_diagonal, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc,
    emb_conjTranspose_mul_emb, Matrix.one_mul]

/-- The diagonal element `diag(z, z̄)` of SU(2), for `|z| = 1`. -/
def torus (z : ℂ) (hz : z * star z = 1) : SU2 :=
  ⟨diagonal ![z, star z], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose,
      diagonal_conjTranspose, diagonal_mul_diagonal, det_diagonal]
    have hzc : z * (starRingEnd ℂ) z = 1 := hz
    have hzc' : (starRingEnd ℂ) z * z = 1 := by rw [mul_comm, hzc]
    refine ⟨?_, by simp [Fin.prod_univ_two, hzc]⟩
    rw [← diagonal_one]
    congr 1
    ext i; fin_cases i <;> simp [hzc, hzc']⟩

/-- **Spin `j` has weights `m = j, j-1, …, -j`.** The rotation `diag(e^{iθ}, e^{-iθ})` acts on the
`k`-th basis vector by `e^{i(n-2k)θ} = e^{2imθ}` with `m = n/2 - k`. -/
theorem spinMat_torus_exp (θ : ℝ) :
    spinMat n (torus (Complex.exp (θ * Complex.I)) (by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]; simp [Complex.conj_ofReal])) =
      diagonal fun k : Fin (n + 1) =>
        Complex.exp ((((n : ℝ) - 2 * (k : ℕ)) * θ : ℝ) * Complex.I) := by
  rw [torus, spinMat_diagonal]
  congr 1; ext k
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast [Nat.cast_sub hk]
  ring

/-- The central element `-1 ∈ SU(2)`. -/
def negOne : SU2 := torus (-1) (by simp)

lemma negOne_coe : (negOne : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [negOne, torus]

/-- **Integer vs half-integer spin.** `-1 ∈ SU(2)` acts as `(-1)^n = (-1)^{2j}`: trivially for
integer spin, as `-1` for half-integer spin (so only integer spins descend to SO(3)). -/
theorem spinMat_negOne :
    spinMat n negOne = (-1 : ℂ) ^ n • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  rw [negOne, torus, spinMat_diagonal]
  ext j k
  have hk : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.2
  by_cases hjk : j = k
  · subst hjk
    rw [diagonal_apply_eq, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, star_neg, star_one]
    rw [← pow_add, Nat.sub_add_cancel hk]
  · simp [diagonal_apply_ne _ hjk, one_apply_ne hjk, Matrix.smul_apply]

/-! ### Irreducibility -/

/-- A subspace of `ℂ^{n+1}` invariant under the whole spin-`n/2` representation. -/
def IsInvariant (n : ℕ) (W : Submodule ℂ (Fin (n + 1) → ℂ)) : Prop :=
  ∀ g : SU2, ∀ v ∈ W, spinMat n g *ᵥ v ∈ W

/-- Torus averaging: an invariant subspace contains the `k`-th coordinate vector of each of its
elements. (Average `v` against the characters of the cyclic subgroup of order `2n+1`; the
`n + 1` weights are distinct there.) -/
lemma single_mem_of_isInvariant {W : Submodule ℂ (Fin (n + 1) → ℂ)} (hW : IsInvariant n W)
    {v : Fin (n + 1) → ℂ} (hv : v ∈ W) {k : Fin (n + 1)} (hk : v k ≠ 0) :
    Pi.single k 1 ∈ W := by
  set M := 2 * n + 1 with hM
  have hM0 : M ≠ 0 := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / M) with hζdef
  have hζ : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M hM0
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hM0
  have hζs : ζ * star ζ = 1 := by
    rw [Complex.star_def, Complex.mul_conj', hnorm]; simp
  have hζs' : star ζ * ζ = 1 := by rw [mul_comm, hζs]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM0
  -- weights of the cyclic subgroup
  let w : Fin (n + 1) → ℂ := fun j => ζ ^ (n - (j : ℕ)) * (star ζ) ^ (j : ℕ)
  have hzm : ∀ m : ℕ, ζ ^ m * star (ζ ^ m) = 1 := fun m => by
    rw [star_pow, ← mul_pow, hζs, one_pow]
  have hspin : ∀ m : ℕ, spinMat n (torus (ζ ^ m) (hzm m)) = diagonal fun j => w j ^ m := by
    intro m
    rw [torus, spinMat_diagonal]
    congr 1; ext j
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, w, star_pow,
      mul_pow, ← pow_mul, mul_comm m]
  have hwM : ∀ j, w j ^ M = 1 := by
    intro j
    have h1 : (ζ ^ (n - (j : ℕ))) ^ M = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h2 : (star ζ ^ (j : ℕ)) ^ M = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← star_pow, hζ.pow_eq_one, star_one, one_pow]
    simp only [w, mul_pow, h1, h2, mul_one]
  have hwk : ∀ j : Fin (n + 1), w j * ζ ^ (j : ℕ) = ζ ^ (n - (j : ℕ)) := by
    intro j
    simp only [w, mul_assoc, ← mul_pow, hζs', one_pow, mul_one]
  have hwinj : ∀ i j : Fin (n + 1), i < j → w i ≠ w j := by
    intro i j hij heq
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.2
    have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.2
    have hij' : (i : ℕ) < j := hij
    have h1 : ζ ^ (n - (i : ℕ) + j) = ζ ^ (n - (j : ℕ) + i) := by
      rw [pow_add, pow_add, ← hwk i, ← hwk j, heq]; ring
    have h2 : ζ ^ (n - (i : ℕ) + j) = ζ ^ (n - (j : ℕ) + i) * ζ ^ (2 * ((j : ℕ) - i)) := by
      rw [← pow_add]; congr 1; omega
    rw [h2] at h1
    have h3 : ζ ^ (2 * ((j : ℕ) - i)) = 1 :=
      mul_left_cancel₀ (pow_ne_zero _ hζ0) (h1.trans (mul_one _).symm)
    exact hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega) h3
  have hstar_w : star (w k) * w k = 1 := by
    have : star (w k) * w k = (star ζ * ζ) ^ (n - (k : ℕ)) * (ζ * star ζ) ^ (k : ℕ) := by
      simp only [w, star_mul, star_pow, star_star]; ring
    rw [this, hζs, hζs']; simp
  -- the average
  let u : Fin (n + 1) → ℂ :=
    ∑ m ∈ range M, (star (w k)) ^ m • (spinMat n (torus (ζ ^ m) (hzm m)) *ᵥ v)
  have hu : u ∈ W := sum_mem fun m _ => W.smul_mem _ (hW _ v hv)
  have hu_eq : u = ((M : ℂ) * v k) • Pi.single k 1 := by
    ext j
    simp only [u, Finset.sum_apply, Pi.smul_apply, hspin, mulVec_diagonal, smul_eq_mul]
    have : ∀ m ∈ range M, star (w k) ^ m * (w j ^ m * v j) = (star (w k) * w j) ^ m * v j :=
      fun m _ => by ring
    rw [sum_congr rfl this, ← sum_mul]
    by_cases hjk : j = k
    · subst hjk
      rw [hstar_w]
      simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, Pi.single_eq_same]
    · have hx : star (w k) * w j ≠ 1 := by
        intro h1
        have : w j = w k := by
          have := congrArg (w k * ·) h1
          simp only [← mul_assoc, mul_one] at this
          rw [mul_comm (w k), hstar_w, one_mul] at this
          exact this
        rcases lt_or_gt_of_ne hjk with h | h
        · exact hwinj j k h this
        · exact hwinj k j h this.symm
      have hxM : (star (w k) * w j) ^ M = 1 := by
        rw [mul_pow, ← star_pow, hwM, hwM, star_one, one_mul]
      rw [geom_sum_eq hx, hxM, sub_self, zero_div, zero_mul]
      simp [hjk]
  have hcoef : ((M : ℂ) * v k) ≠ 0 := mul_ne_zero (by exact_mod_cast hM0) hk
  have := W.smul_mem ((M : ℂ) * v k)⁻¹ (hu_eq ▸ hu)
  rwa [smul_smul, inv_mul_cancel₀ hcoef, one_smul] at this

/-- The strings with `n` down labels: only the all-down string. -/
lemma downs_eq_self_iff (s : Str n) : downs s = n ↔ s = fun _ => 1 := by
  unfold downs
  constructor
  · intro h
    have := (card_filter_eq_iff (s := (univ : Finset (Fin n))) (p := fun i => s i = 1)).mp
      (by simpa using h)
    exact funext fun i => this i (mem_univ i)
  · rintro rfl; simp

/-- **Last row of a spin matrix**: `(spinMat n g)_{n,k} = c · g₁₀^{n-k} g₁₁^k` with `c ≠ 0`. -/
lemma spinMat_last_row (g : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin (n + 1)) :
    ∃ c : ℂ, c ≠ 0 ∧ spinMat n g (Fin.last n) k = c * (g 1 0 ^ (n - k) * g 1 1 ^ (k : ℕ)) := by
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
  refine ⟨star (nrm n n) * (clsCard n k * nrm n k), ?_, ?_⟩
  · refine mul_ne_zero (by rw [star_nrm]; exact nrm_ne_zero le_rfl)
      (mul_ne_zero (by exact_mod_cast (clsCard_pos hk).ne') (nrm_ne_zero hk))
  rw [spinMat, Matrix.mul_assoc, mul_apply,
    sum_eq_single (fun _ => (1 : Fin 2))]
  · rw [conjTranspose_apply, emb_apply,
      ite_eq_left_of_eq_true _ _ (eq_true (by simp [downs_eq_self_iff])), mul_apply]
    have : ∀ t : Str n, kron n g (fun _ => 1) t * emb n t k =
        if t ∈ cls n k then g 1 0 ^ (n - k) * g 1 1 ^ (k : ℕ) * nrm n k else 0 := by
      intro t
      rw [kron_apply, prod_fin_two (f := g 1), emb_apply]
      by_cases h : downs t = k <;> simp [cls, h]
    simp only [this, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, clsCard]
    simp only [Fin.val_last]
    ring
  · intro s _ hs
    rw [conjTranspose_apply, emb_apply,
      ite_eq_right_of_eq_false _ _ (eq_false (by simpa [downs_eq_self_iff] using hs))]
    simp
  · simp

/-- `1/√2`. -/
noncomputable def c2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma c2_mul_self : c2 * c2 = 1 / 2 := by
  rw [c2, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma star_c2 : star c2 = c2 := by simp [c2]

lemma conj_c2 : (starRingEnd ℂ) c2 = c2 := star_c2

lemma c2_ne_zero : c2 ≠ 0 := by simp [c2]

/-- The rotation by `π/2` about the `y`-axis: `(1/√2) [[1, -1], [1, 1]]`, all entries nonzero. -/
noncomputable def rotY : SU2 :=
  ⟨!![c2, -c2; c2, c2], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [mul_apply, Fin.sum_univ_two, conjTranspose_apply, conj_c2] <;>
        linear_combination 2 * c2_mul_self
    · rw [det_fin_two_of]
      linear_combination 2 * c2_mul_self⟩

lemma rotY_ne_zero (i j : Fin 2) : (rotY : Matrix (Fin 2) (Fin 2) ℂ) i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> simp [rotY, c2_ne_zero]

/-- **Irreducibility (submodule form).** A subspace invariant under the spin-`n/2` representation
is `0` or everything. -/
theorem isInvariant_eq_bot_or_eq_top {W : Submodule ℂ (Fin (n + 1) → ℂ)} (hW : IsInvariant n W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv0
  have hek := single_mem_of_isInvariant hW hv hk
  -- `rotY` moves `e_k` to a vector with nonzero last component, so `e_last ∈ W`
  have h1 := hW rotY _ hek
  obtain ⟨c, hc, hrow⟩ := spinMat_last_row (n := n) rotY k
  have hlast := single_mem_of_isInvariant hW h1 (k := Fin.last n) (by
    rw [mulVec_single_one, col_apply, hrow]
    exact mul_ne_zero hc (mul_ne_zero (pow_ne_zero _ (rotY_ne_zero 1 0))
      (pow_ne_zero _ (rotY_ne_zero 1 1))))
  -- `rotY` moves `e_last` to a vector with all components nonzero (use the last row of `rotYᴴ`)
  have h2 := hW rotY _ hlast
  have hall : ∀ j, Pi.single j 1 ∈ W := by
    intro j
    refine single_mem_of_isInvariant hW h2 (k := j) ?_
    rw [mulVec_single_one, col_apply]
    have hstar : spinMat n (rotY : Matrix (Fin 2) (Fin 2) ℂ) j (Fin.last n) =
        star (spinMat n (rotY : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (Fin.last n) j) := by
      rw [← spinMat_conjTranspose, conjTranspose_apply, star_star]
    obtain ⟨c', hc', hrow'⟩ := spinMat_last_row (n := n) (rotY : Matrix (Fin 2) (Fin 2) ℂ)ᴴ j
    rw [hstar, hrow', star_ne_zero]
    refine mul_ne_zero hc' (mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)) <;>
      simp only [conjTranspose_apply, star_ne_zero] <;> exact rotY_ne_zero _ _
  rw [eq_top_iff]
  intro u _
  rw [← Finset.univ_sum_single u]
  refine sum_mem fun j _ => ?_
  rw [show Pi.single j (u j) = u j • Pi.single j (1 : ℂ) by simp [← Pi.single_smul]]
  exact W.smul_mem _ (hall j)

/-- **Irreducibility** of the spin-`n/2` representation, in Mathlib's sense
(`Representation.IsIrreducible`: the lattice of subrepresentations is `{⊥, ⊤}`). -/
theorem spinRepresentation_isIrreducible : (spinRepresentation n).IsIrreducible := by
  have : Nontrivial (Subrepresentation (spinRepresentation n)) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  refine { eq_bot_or_eq_top := fun W => ?_ }
  rcases isInvariant_eq_bot_or_eq_top (n := n) (W := W.toSubmodule)
      (fun g v hv => W.apply_mem_toSubmodule g hv) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end SU2Spin
