import Lightlike.SpinFoam.BarrettCrane
import Lightlike.Asymptotics.Racah
import Lightlike.Recoupling.Simplex

/-!
# Exact values of the Barrett–Crane vertex

`bcVertex_eq_vertexQ`: the Barrett–Crane vertex `bcVertex j` is the rational number `vertexQ j`,
for all spins. It is computed from Racah's formula (`sixJSym_eq_racahW`) and the reduction of the
4-simplex contraction to the 15j symbol (`fifteenJSimplex_eq`).

In each term of the 15j sum, the five triangle coefficients that contain the summed spin `x`
appear twice, so the square of the 15j symbol is rational (`fifteenJ_sq`). `vertexQ` is a
rational-valued copy of the resulting formula, written to be cheap to evaluate in the kernel.

## Published values

The tests compare with the Riemannian 10j symbols computed by Christensen with the Christensen–Egan
algorithm (table at `jdc.math.uwo.ca/spin-foams/10j-samples/riemannian`) and their exact rational
forms by Egan (`gregegan.net/SCIENCE/tenJ/tenJ.html`). All ten spins `½` give `7/18`
(`Tests.bcVertex_half`), and all ten spins `1` give `307/1500` (`Tests.bcVertex_one`). The mixed
spins `1` on the edges `(i, i+1)` and `½` on the edges `(i, i+2)` give `-163/1728` in the
Baez–Christensen sign convention (`Tests.bcVertexBC_mixed`); the table prints
`-0.0943287037037036923959`.

## References

* J. D. Christensen, G. Egan, *An efficient algorithm for the Riemannian 10j symbols*,
  Class. Quantum Grav. 19 (2002) 1185, arXiv:gr-qc/0110045, §2 (the 10j symbol, the edge labels
  `j_{1,i}`, `j_{2,i}`) and §3.
* `baez-christensen-2002`: the sign of the Riemannian 10j symbol.
-/

open Finset PhyslibAlpha.Sl2 Lightlike.Pentagon Lightlike.Asymptotics Lightlike.Recoupling

namespace Lightlike.SpinFoam.BC

/-! ## Racah's formula with the triangle coefficients split off -/

/-- Racah's 6j expression without its four triangle coefficients: the alternating sum on admissible
spins, `0` otherwise. -/
noncomputable def racahRest (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℝ :=
  if Adm6 j₁ j₂ j₃ j₄ j₅ j₆ then rsum (faceD j₁ j₂ j₃ j₄ j₅ j₆) (quadD j₁ j₂ j₃ j₄ j₅ j₆) else 0

lemma racahW_eq_mul (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racahW j₁ j₂ j₃ j₄ j₅ j₆ = triD j₁ j₂ j₃ * triD j₁ j₅ j₆ * triD j₄ j₂ j₆ * triD j₄ j₅ j₃ *
      racahRest j₁ j₂ j₃ j₄ j₅ j₆ := by
  by_cases h : Adm6 j₁ j₂ j₃ j₄ j₅ j₆
  · rw [racahW_of_adm h, racahRest, ite_eq_left h]
  · rw [racahW_of_not h, racahRest, ite_eq_right h, mul_zero]

/-! ## The square of the 15j symbol is rational -/

/-- The term `x` of the 15j sum with the triangle coefficients independent of `x` removed: five
squared triangle coefficients `Δ(a_t b_t x)²` and five Racah sums. -/
noncomputable def ladderTerm (a b c : Fin 5 → ℕ) (x : ℕ) : ℝ :=
  triSq (a 0) (b 0) x * racahRest (a 0) (b 0) x (b 1) (a 1) (c 0) *
    (triSq (a 1) (b 1) x * racahRest (a 1) (b 1) x (b 2) (a 2) (c 1)) *
    (triSq (a 2) (b 2) x * racahRest (a 2) (b 2) x (b 3) (a 3) (c 2)) *
    (triSq (a 3) (b 3) x * racahRest (a 3) (b 3) x (b 4) (a 4) (c 3)) *
    (triSq (a 4) (b 4) x * racahRest (a 4) (b 4) x (a 0) (b 0) (c 4))

/-- The 15j sum with the triangle coefficients independent of `x` removed. -/
noncomputable def ladder (a b c : Fin 5 → ℕ) : ℝ :=
  ∑ x ∈ range (a 0 + b 0 + 1), ((x : ℝ) + 1) * ladderTerm a b c x

/-- The ten triangle coefficients of the 15j symbol that do not contain the summed spin. -/
noncomputable def outerD (a b c : Fin 5 → ℕ) : ℝ :=
  triD (a 0) (a 1) (c 0) * triD (b 1) (b 0) (c 0) * (triD (a 1) (a 2) (c 1) * triD (b 2) (b 1) (c 1)) *
    (triD (a 2) (a 3) (c 2) * triD (b 3) (b 2) (c 2)) *
    (triD (a 3) (a 4) (c 3) * triD (b 4) (b 3) (c 3)) *
    (triD (a 4) (b 0) (c 4) * triD (a 0) (b 4) (c 4))

/-- The square of `outerD`, a product of ten squared triangle coefficients. -/
noncomputable def outerSq (a b c : Fin 5 → ℕ) : ℝ :=
  triSq (a 0) (a 1) (c 0) * triSq (b 1) (b 0) (c 0) * (triSq (a 1) (a 2) (c 1) * triSq (b 2) (b 1) (c 1)) *
    (triSq (a 2) (a 3) (c 2) * triSq (b 3) (b 2) (c 2)) *
    (triSq (a 3) (a 4) (c 3) * triSq (b 4) (b 3) (c 3)) *
    (triSq (a 4) (b 0) (c 4) * triSq (a 0) (b 4) (c 4))

/-- The product of the five 6j symbols of a term of the 15j sum: the triangle coefficients with the
summed spin `x` pair up. -/
lemma sixJ_prod (a b c : Fin 5 → ℕ) (x : ℕ) :
    sixJSym (a 0) (b 0) x (b 1) (a 1) (c 0) * sixJSym (a 1) (b 1) x (b 2) (a 2) (c 1) *
        sixJSym (a 2) (b 2) x (b 3) (a 3) (c 2) * sixJSym (a 3) (b 3) x (b 4) (a 4) (c 3) *
          sixJSym (a 4) (b 4) x (a 0) (b 0) (c 4) =
      outerD a b c * ladderTerm a b c x := by
  simp only [sixJSym_eq_racahW, racahW_eq_mul]
  rw [triD_swap12 (a 1) (b 1) x, triD_swap12 (a 2) (b 2) x, triD_swap12 (a 3) (b 3) x,
    triD_swap12 (a 4) (b 4) x]
  simp only [ladderTerm, outerD, ← triD_mul_self]
  ring

lemma outerD_sq (a b c : Fin 5 → ℕ) : outerD a b c ^ 2 = outerSq a b c := by
  simp only [outerD, outerSq, ← triD_mul_self]
  ring

/-- **The square of the 15j symbol is rational**: `{15j}² = outerSq · ladder²`. -/
theorem fifteenJ_sq (a b c : Fin 5 → ℕ) : fifteenJ a b c ^ 2 = outerSq a b c * ladder a b c ^ 2 := by
  have h : fifteenJ a b c =
      (-1) ^ ((∑ t, (a t + b t + c t)) / 2) * (outerD a b c * ladder a b c) := by
    unfold fifteenJ ladder
    congr 1
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [sixJ_prod]
    ring
  rw [h, mul_pow, mul_pow, outerD_sq, ← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow,
    one_mul]

/-! ## The vertex as a sum of rational terms -/

/-- The three rows of the 15j symbol of the vertex with edge spins `j` and virtual spins `P`
(`fifteenJSimplex_eq`). -/
def rowA (j : Fin 10 → ℕ) (P : Fin 5 → ℕ) : Fin 5 → ℕ := ![P 0, j 1, P 2, j 8, P 4]

/-- The second row of the 15j symbol of the vertex. -/
def rowB (j : Fin 10 → ℕ) (P : Fin 5 → ℕ) : Fin 5 → ℕ := ![j 6, P 1, j 5, P 3, j 2]

/-- The third row of the 15j symbol of the vertex. -/
def rowC (j : Fin 10 → ℕ) : Fin 5 → ℕ := ![j 0, j 4, j 7, j 9, j 3]

/-- The term of the vertex with virtual spins `P`. -/
noncomputable def vTerm (j : Fin 10 → ℕ) (P : Fin 5 → ℕ) : ℝ :=
  ((P 0 : ℝ) + 1) * ((P 1 : ℝ) + 1) * ((P 2 : ℝ) + 1) * ((P 3 : ℝ) + 1) * ((P 4 : ℝ) + 1) *
    (outerSq (rowA j P) (rowB j P) (rowC j) * ladder (rowA j P) (rowB j P) (rowC j) ^ 2)

/-- **The vertex as a real sum**: `A_v(j) = Σ_P Π_a (P_a + 1) · outerSq · ladder²`. -/
theorem bcVertex_eq_sum_vTerm (j : Fin 10 → ℕ) :
    bcVertex j = ((∑ P ∈ Fintype.piFinset (nodeChans j), vTerm j P : ℝ) : ℂ) := by
  rw [bcVertex_eq_sum, Complex.ofReal_sum]
  refine sum_congr rfl fun P _ => ?_
  rw [← Complex.ofReal_pow]
  congr 1
  rw [fifteenJSimplex_eq, mul_pow, Real.sq_sqrt (by positivity), fifteenJ_sq]
  rfl

/-! ## A rational copy, cheap to evaluate in the kernel -/

/-- The factorial by direct recursion (`factR_eq`), which the kernel evaluates cheaply. -/
def factR (n : ℕ) : ℕ := Nat.rec 1 (fun k r => (k + 1) * r) n

lemma factR_eq (n : ℕ) : factR n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => show (n + 1) * factR n = _; rw [ih, Nat.factorial_succ]

/-- `1/u!` for `u ≥ 0`, `0` otherwise, in `ℚ`. -/
def invFactQ (u : ℤ) : ℚ := if 0 ≤ u then ((factR u.toNat : ℚ))⁻¹ else 0

/-- `(-1)^t` in `ℚ`. -/
def sgnQ (t : ℕ) : ℚ := if t % 2 = 0 then 1 else -1

/-- A term of Racah's sum in `ℚ`. -/
def rtermQ (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) (t : ℕ) : ℚ :=
  sgnQ t * (factR (t + 1) : ℚ) * (invFactQ ((t : ℤ) - A 0) * invFactQ ((t : ℤ) - A 1) *
    invFactQ ((t : ℤ) - A 2) * invFactQ ((t : ℤ) - A 3) *
    (invFactQ (B 0 - t) * invFactQ (B 1 - t) * invFactQ (B 2 - t)))

/-- Racah's sum in `ℚ`. -/
def rsumQ (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) : ℚ :=
  ∑ t ∈ range ((B 0 + B 1 + B 2).toNat + 1), rtermQ A B t

/-- The squared triangle coefficient in `ℚ`. -/
def triSqQ (x y z : ℕ) : ℚ :=
  ((factR ((x + y - z) / 2) * factR ((x + z - y) / 2) * factR ((y + z - x) / 2) : ℕ) : ℚ) /
    (factR ((x + y + z) / 2 + 1) : ℚ)

/-- `racahRest` in `ℚ`. -/
def restQ (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℚ :=
  if Adm6 j₁ j₂ j₃ j₄ j₅ j₆ then rsumQ (faceD j₁ j₂ j₃ j₄ j₅ j₆) (quadD j₁ j₂ j₃ j₄ j₅ j₆) else 0

/-- `ladder` in `ℚ`. -/
def ladderQ (a b c : Fin 5 → ℕ) : ℚ :=
  ∑ x ∈ range (a 0 + b 0 + 1), ((x : ℚ) + 1) *
    (triSqQ (a 0) (b 0) x * restQ (a 0) (b 0) x (b 1) (a 1) (c 0) *
      (triSqQ (a 1) (b 1) x * restQ (a 1) (b 1) x (b 2) (a 2) (c 1)) *
      (triSqQ (a 2) (b 2) x * restQ (a 2) (b 2) x (b 3) (a 3) (c 2)) *
      (triSqQ (a 3) (b 3) x * restQ (a 3) (b 3) x (b 4) (a 4) (c 3)) *
      (triSqQ (a 4) (b 4) x * restQ (a 4) (b 4) x (a 0) (b 0) (c 4)))

/-- `outerSq` in `ℚ`. -/
def outerQ (a b c : Fin 5 → ℕ) : ℚ :=
  triSqQ (a 0) (a 1) (c 0) * triSqQ (b 1) (b 0) (c 0) *
    (triSqQ (a 1) (a 2) (c 1) * triSqQ (b 2) (b 1) (c 1)) *
    (triSqQ (a 2) (a 3) (c 2) * triSqQ (b 3) (b 2) (c 2)) *
    (triSqQ (a 3) (a 4) (c 3) * triSqQ (b 4) (b 3) (c 3)) *
    (triSqQ (a 4) (b 0) (c 4) * triSqQ (a 0) (b 4) (c 4))

/-- `vTerm` in `ℚ`. -/
def vTermQ (j : Fin 10 → ℕ) (P : Fin 5 → ℕ) : ℚ :=
  ((P 0 : ℚ) + 1) * ((P 1 : ℚ) + 1) * ((P 2 : ℚ) + 1) * ((P 3 : ℚ) + 1) * ((P 4 : ℚ) + 1) *
    (outerQ (rowA j P) (rowB j P) (rowC j) * ladderQ (rowA j P) (rowB j P) (rowC j) ^ 2)

/-- **The Barrett–Crane vertex as a rational number** (`bcVertex_eq_vertexQ`). -/
def vertexQ (j : Fin 10 → ℕ) : ℚ := ∑ P ∈ Fintype.piFinset (nodeChans j), vTermQ j P

lemma invFactQ_cast (u : ℤ) : ((invFactQ u : ℚ) : ℝ) = invFact u := by
  unfold invFactQ invFact
  by_cases h : 0 ≤ u
  · rw [ite_eq_left h, ite_eq_left h]; push_cast [factR_eq]; rfl
  · rw [ite_eq_right h, ite_eq_right h, Rat.cast_zero]

lemma sgnQ_cast (t : ℕ) : ((sgnQ t : ℚ) : ℝ) = (-1) ^ t := by
  unfold sgnQ
  by_cases h : t % 2 = 0
  · rw [ite_eq_left h, Rat.cast_one, Even.neg_one_pow (Nat.even_iff.2 h)]
  · rw [ite_eq_right h, Rat.cast_neg, Rat.cast_one,
      Odd.neg_one_pow (Nat.odd_iff.2 (by omega))]

lemma rsumQ_cast (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) : ((rsumQ A B : ℚ) : ℝ) = rsum A B := by
  unfold rsumQ rsum
  rw [Fin.sum_univ_three, Rat.cast_sum]
  refine sum_congr rfl fun t _ => ?_
  unfold rtermQ rterm
  rw [Fin.prod_univ_four, Fin.prod_univ_three]
  push_cast [invFactQ_cast, sgnQ_cast, factR_eq]
  ring

lemma triSqQ_cast (x y z : ℕ) : ((triSqQ x y z : ℚ) : ℝ) = triSq x y z := by
  unfold triSqQ triSq
  push_cast [factR_eq]
  rfl

lemma restQ_cast (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    ((restQ j₁ j₂ j₃ j₄ j₅ j₆ : ℚ) : ℝ) = racahRest j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold restQ racahRest
  by_cases h : Adm6 j₁ j₂ j₃ j₄ j₅ j₆
  · rw [ite_eq_left h, ite_eq_left h, rsumQ_cast]
  · rw [ite_eq_right h, ite_eq_right h, Rat.cast_zero]

lemma vTermQ_cast (j : Fin 10 → ℕ) (P : Fin 5 → ℕ) : ((vTermQ j P : ℚ) : ℝ) = vTerm j P := by
  unfold vTermQ vTerm outerQ ladderQ outerSq ladder ladderTerm
  push_cast [triSqQ_cast, restQ_cast]
  rfl

/-- **The Barrett–Crane vertex is the rational number `vertexQ j`**, for all spins. -/
theorem bcVertex_eq_vertexQ (j : Fin 10 → ℕ) : bcVertex j = (((vertexQ j : ℚ) : ℝ) : ℂ) := by
  rw [bcVertex_eq_sum_vTerm, vertexQ, Rat.cast_sum]
  simp only [vTermQ_cast]

/-- The vertex sum split by the virtual spins of the first two nodes. -/
def chunkQ (j : Fin 10 → ℕ) (p₀ p₁ : ℕ) : ℚ :=
  ∑ p₂ ∈ nodeChans j 2, ∑ p₃ ∈ nodeChans j 3, ∑ p₄ ∈ nodeChans j 4, vTermQ j ![p₀, p₁, p₂, p₃, p₄]

/-- A sum over virtual spins of `n + 1` nodes splits off the first node. -/
lemma sum_piFinset_succQ {n : ℕ} (B : Fin (n + 1) → Finset ℕ) (f : (Fin (n + 1) → ℕ) → ℚ) :
    ∑ μ ∈ Fintype.piFinset B, f μ =
      ∑ a ∈ B 0, ∑ μ ∈ Fintype.piFinset (fun i => B i.succ), f (Fin.cons a μ) := by
  rw [← sum_product']
  apply sum_nbij' (fun μ => (μ 0, Fin.tail μ)) (fun p => Fin.cons p.1 p.2)
  · intro μ hμ
    simp only [mem_product, Fintype.mem_piFinset] at hμ ⊢
    exact ⟨hμ 0, fun i => hμ i.succ⟩
  · rintro ⟨a, μ⟩ h
    simp only [mem_product, Fintype.mem_piFinset] at h ⊢
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h.1
    · simpa using h.2 i
  · intro μ _; exact Fin.cons_self_tail μ
  · rintro ⟨a, μ⟩ _; simp
  · intro μ _; rw [Fin.cons_self_tail]

/-- A sum over the virtual spins of no nodes is the value at the empty assignment. -/
lemma sum_piFinset_zeroQ (B : Fin 0 → Finset ℕ) (f : (Fin 0 → ℕ) → ℚ) :
    ∑ μ ∈ Fintype.piFinset B, f μ = f Fin.elim0 := by
  have : Fintype.piFinset B = {Fin.elim0} := by
    ext μ
    simp only [Fintype.mem_piFinset, IsEmpty.forall_iff, mem_singleton, true_iff]
    funext i; exact i.elim0
  rw [this, sum_singleton]

lemma vertexQ_eq_chunks (j : Fin 10 → ℕ) :
    vertexQ j = ∑ p₀ ∈ nodeChans j 0, ∑ p₁ ∈ nodeChans j 1, chunkQ j p₀ p₁ := by
  unfold vertexQ chunkQ
  rw [sum_piFinset_succQ]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_piFinset_succQ]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_piFinset_succQ]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_piFinset_succQ]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_piFinset_succQ]
  refine sum_congr rfl fun e _ => ?_
  rw [sum_piFinset_zeroQ]
  congr 1

/-! ## Published values -/

namespace Tests

/-- The ten spins of the mixed Christensen–Egan sample, doubled: spin `1` on the edges `(i, i+1)`
(edges `0, 4, 7, 9, 3` of `k5Spins`), spin `½` on the edges `(i, i+2)` (edges `1, 5, 8, 2, 6`). -/
def mixedSpins : Fin 10 → ℕ := ![2, 1, 1, 2, 2, 1, 1, 2, 1, 2]

set_option maxRecDepth 100000 in
/-- The rational vertex at ten spins `½`. -/
theorem vertexQ_half : vertexQ (fun _ => 1) = 7 / 18 := by decide +kernel

set_option maxRecDepth 100000 in
/-- A ninth of the spin-1 vertex, by kernel evaluation. -/
theorem chunk_one_00 : chunkQ (fun _ => 2) 0 0 = 23 / 1215 := by decide +kernel

set_option maxRecDepth 100000 in
/-- A ninth of the spin-1 vertex, by kernel evaluation. -/
theorem chunk_one_02 : chunkQ (fun _ => 2) 0 2 = 19 / 810 := by decide +kernel

set_option maxRecDepth 100000 in
/-- A ninth of the spin-1 vertex, by kernel evaluation. -/
theorem chunk_one_04 : chunkQ (fun _ => 2) 0 4 = 349 / 12150 := by decide +kernel

set_option maxRecDepth 100000 in
/-- A ninth of the spin-1 vertex, by kernel evaluation. -/
theorem chunk_one_20 : chunkQ (fun _ => 2) 2 0 = 19 / 810 := by decide +kernel

set_option maxRecDepth 100000 in
/-- A ninth of the spin-1 vertex, by kernel evaluation. -/
theorem chunk_one_22 : chunkQ (fun _ => 2) 2 2 = 19 / 1080 := by decide +kernel

set_option maxRecDepth 100000 in
/-- A ninth of the spin-1 vertex, by kernel evaluation. -/
theorem chunk_one_24 : chunkQ (fun _ => 2) 2 4 = 37 / 1620 := by decide +kernel

set_option maxRecDepth 100000 in
/-- A ninth of the spin-1 vertex, by kernel evaluation. -/
theorem chunk_one_40 : chunkQ (fun _ => 2) 4 0 = 349 / 12150 := by decide +kernel

set_option maxRecDepth 100000 in
/-- A ninth of the spin-1 vertex, by kernel evaluation. -/
theorem chunk_one_42 : chunkQ (fun _ => 2) 4 2 = 37 / 1620 := by decide +kernel

set_option maxRecDepth 100000 in
/-- A ninth of the spin-1 vertex, by kernel evaluation. -/
theorem chunk_one_44 : chunkQ (fun _ => 2) 4 4 = 4399 / 243000 := by decide +kernel

lemma nodeChans_one : nodeChans (fun _ => 2) = fun _ => {0, 2, 4} := by
  funext a; fin_cases a <;> decide

/-- The rational vertex at ten spins `1`. -/
theorem vertexQ_one : vertexQ (fun _ => 2) = 307 / 1500 := by
  rw [vertexQ_eq_chunks, nodeChans_one]
  simp only [sum_insert (show (0 : ℕ) ∉ ({2, 4} : Finset ℕ) by decide),
    sum_insert (show (2 : ℕ) ∉ ({4} : Finset ℕ) by decide), sum_singleton]
  rw [chunk_one_00, chunk_one_02, chunk_one_04, chunk_one_20, chunk_one_22, chunk_one_24,
    chunk_one_40, chunk_one_42, chunk_one_44]
  norm_num

set_option maxRecDepth 100000 in
/-- The rational vertex at the mixed spins. -/
theorem vertexQ_mixed : vertexQ mixedSpins = 163 / 1728 := by decide +kernel

/-- **Published value: ten spins `½`.** The Barrett–Crane vertex with spin `½` on every edge is
`7/18`, the regular Riemannian 10j symbol of Christensen's table (`0.388888…`) and Egan's exact
value `7 / 18`. -/
theorem bcVertex_half : bcVertex (fun _ => 1) = (((7 / 18 : ℝ)) : ℂ) := by
  rw [bcVertex_eq_vertexQ, vertexQ_half]; push_cast; rfl

/-- **Published value: ten spins `1`.** The vertex with spin `1` on every edge is `307/1500`,
Christensen's `0.204666…` and Egan's exact `307 / 1 500`. -/
theorem bcVertex_one : bcVertex (fun _ => 2) = (((307 / 1500 : ℝ)) : ℂ) := by
  rw [bcVertex_eq_vertexQ, vertexQ_one]; push_cast; rfl

/-- In the Baez–Christensen sign convention, which the published table uses, the two equal-spin
values are unchanged (the doubled spins sum to `10` and `20`). -/
theorem bcVertexBC_half : bcVertexBC (fun _ => 1) = 7 / 18 := by
  rw [bcVertexBC, bcSign, bcVertex_half, Complex.ofReal_re]
  simp [Fin.sum_univ_succ]; norm_num

theorem bcVertexBC_one : bcVertexBC (fun _ => 2) = 307 / 1500 := by
  rw [bcVertexBC, bcSign, bcVertex_one, Complex.ofReal_re]
  simp [Fin.sum_univ_succ]; norm_num

/-- **Published value with a negative sign.** Spin `1` on the edges `(i, i+1)` and `½` on the edges
`(i, i+2)` (Christensen–Egan labels `j_{1,i}`, `j_{2,i}`) give `-163/1728` in the
Baez–Christensen sign convention; Christensen's table prints `-0.0943287037037036923959`, whose
digits agree with `163/1728 = 0.0943287037037037…` to the sixteen places of a double. -/
theorem bcVertexBC_mixed : bcVertexBC mixedSpins = -(163 / 1728) := by
  rw [bcVertexBC, bcSign, bcVertex_eq_vertexQ, vertexQ_mixed]
  simp [mixedSpins, Fin.sum_univ_succ]; norm_num

end Tests

end Lightlike.SpinFoam.BC
