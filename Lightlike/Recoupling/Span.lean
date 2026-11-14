import Lightlike.Recoupling.Network
import Lightlike.Recoupling.ThreeJInvariance
import Lightlike.Recoupling.Symmetry

/-!
# Invariant tensors are spanned by intertwiners

The 4-valent intertwiners `fourJ j₁ j₂ j₃ j₄ k` are orthonormal (`sum_fourJ_mul_fourJ`). This file
proves that they span the invariant tensors with four incoming legs: **every invariant tensor is
the sum of its components along the intertwiners** (`eq_sum_fourJ`). With it, the sum over the
virtual spin `Σ_k ι_k ⊗ ι_k` acts as the identity on invariant tensors, which is how the internal
tetrahedra of a spin foam drop out of the Pachner moves.

## Main results

* `isInv_fourJT`: the intertwiner `fourJ` is an invariant tensor (a network of two 3j symbols).
* `IsInv.contr3j`: contracting two incoming legs of an invariant tensor with a 3j symbol gives an
  invariant tensor, with the third leg of the 3j symbol outgoing.
* `factor_eq`: the completeness of the 3j symbols factors any tensor through these contractions.
* `eq_sum_fourJ`: the spanning statement above.

## References

- P. Martin-Dussaud, *A primer of group theory for loop quantum gravity and spin-foams*,
  Gen. Relativ. Gravit. 51, 110 (2019), arXiv:1902.08439, §5.4: the 4jm symbols as an orthonormal
  basis of the invariant subspace of four spins.
- A. R. Edmonds, *Angular Momentum in Quantum Mechanics* (Princeton, 1957), §3.7: the
  orthogonality relations of the 3j symbols.
-/

open Finset PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.Recoupling

/-! ## Sums over boxes of projections -/

/-- A sum over the projections of one leg (`Unit`) is a sum over one integer. -/
lemma sum_piFinset_unit (B : Unit → Finset ℤ) (f : (Unit → ℤ) → ℝ) :
    ∑ μ ∈ Fintype.piFinset B, f μ = ∑ a ∈ B (), f (fun _ => a) := by
  apply sum_nbij' (fun μ => μ ()) (fun a _ => a)
  · intro μ hμ; exact (Fintype.mem_piFinset.mp hμ) ()
  · intro a ha; exact Fintype.mem_piFinset.mpr fun _ => ha
  · intro μ _; funext u; rfl
  · intro a _; rfl
  · intro μ _; rfl

/-- A sum over the projections of two legs (`Bool`) is a double sum. -/
lemma sum_piFinset_bool (B : Bool → Finset ℤ) (f : (Bool → ℤ) → ℝ) :
    ∑ μ ∈ Fintype.piFinset B, f μ =
      ∑ a ∈ B false, ∑ b ∈ B true, f (fun c => if c then b else a) := by
  rw [← sum_product']
  apply sum_nbij' (fun μ => (μ false, μ true)) (fun p c => if c then p.2 else p.1)
  · intro μ hμ
    simp only [mem_product]
    exact ⟨(Fintype.mem_piFinset.mp hμ) false, (Fintype.mem_piFinset.mp hμ) true⟩
  · rintro ⟨a, b⟩ h
    simp only [mem_product] at h
    exact Fintype.mem_piFinset.mpr fun c => by cases c <;> simp [h.1, h.2]
  · intro μ _; funext c; cases c <;> rfl
  · rintro ⟨a, b⟩ _; rfl
  · intro μ _
    congr 1
    funext c; cases c <;> rfl

/-- A sum over the projections of `n + 1` legs splits off the first leg. -/
lemma sum_piFinset_fin_succ {n : ℕ} (B : Fin (n + 1) → Finset ℤ) (f : (Fin (n + 1) → ℤ) → ℝ) :
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

/-- A sum over the projections of no legs is the value at the empty assignment. -/
lemma sum_piFinset_fin_zero (B : Fin 0 → Finset ℤ) (f : (Fin 0 → ℤ) → ℝ) :
    ∑ μ ∈ Fintype.piFinset B, f μ = f Fin.elim0 := by
  have : Fintype.piFinset B = {Fin.elim0} := by
    ext μ
    simp only [Fintype.mem_piFinset, IsEmpty.forall_iff, mem_singleton, true_iff]
    funext i; exact i.elim0
  rw [this, sum_singleton]

/-- A sum over the projections of four legs is a fourfold sum. -/
lemma sum_piFinset_four (B : Fin 4 → Finset ℤ) (f : (Fin 4 → ℤ) → ℝ) :
    ∑ μ ∈ Fintype.piFinset B, f μ =
      ∑ a ∈ B 0, ∑ b ∈ B 1, ∑ c ∈ B 2, ∑ d ∈ B 3, f ![a, b, c, d] := by
  rw [sum_piFinset_fin_succ]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_piFinset_fin_succ]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_piFinset_fin_succ]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_piFinset_fin_succ]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_piFinset_fin_zero]
  congr 1

/-! ## The intertwiners are invariant -/

/-- The intertwiner `fourJ j₁ j₂ j₃ j₄ k` as a tensor with four legs. -/
noncomputable def fourJT (j₁ j₂ j₃ j₄ k : ℕ) (m : Fin 4 → ℤ) : ℝ :=
  fourJ j₁ j₂ j₃ j₄ k (m 0) (m 1) (m 2) (m 3)

/-- The leg-ends of the intertwiner as a network of two 3j symbols joined by one edge: the third leg
of the first 3j symbol (turned around) is the outgoing end, the first leg of the second the
incoming end. -/
def fourJLegs (l : Σ _ : Fin 2, Fin 3) : Fin 4 ⊕ (Unit × Bool) :=
  if l.1 = 0 then (![.inl 0, .inl 1, .inr ((), true)] : Fin 3 → Fin 4 ⊕ (Unit × Bool)) l.2
  else (![.inr ((), false), .inl 2, .inl 3] : Fin 3 → Fin 4 ⊕ (Unit × Bool)) l.2

/-- `fourJLegs` as an equivalence. -/
noncomputable def fourJLegsEquiv : (Σ _ : Fin 2, Fin 3) ≃ Fin 4 ⊕ (Unit × Bool) :=
  Equiv.ofBijective fourJLegs (by decide)

/-- **The intertwiner `fourJ` is an invariant tensor** with four incoming legs. -/
theorem isInv_fourJT (j₁ j₂ j₃ j₄ k : ℕ) :
    IsInv ![j₁, j₂, j₃, j₄] ![false, false, false, false] (fourJT j₁ j₂ j₃ j₄ k) := by
  set T : Fin 2 → (Fin 3 → ℤ) → ℝ :=
    fun n => if n = 0 then flipAt k 2 (threeJT j₁ j₂ k) else threeJT k j₃ j₄ with hT
  set J : Fin 2 → Fin 3 → ℕ := fun n => if n = 0 then ![j₁, j₂, k] else ![k, j₃, j₄] with hJ
  set D : Fin 2 → Fin 3 → Bool :=
    fun n => if n = 0 then ![false, false, true] else ![false, false, false] with hD
  have hTi : ∀ n, IsInv (J n) (D n) (T n) := by
    intro n
    fin_cases n
    · have h := (isInv_threeJT j₁ j₂ k).flip 2
      have e : Function.update ![false, false, false] 2 (!(![false, false, false] : Fin 3 → Bool) 2)
          = ![false, false, true] := by decide
      rw [e] at h
      exact h
    · exact isInv_threeJT k j₃ j₄
  have hnet := isInv_netEval (Λ := fun _ : Fin 2 => Fin 3) fourJLegsEquiv (jO := ![j₁, j₂, j₃, j₄])
    (dO := ![false, false, false, false]) (fun _ => k) hTi
    (by rintro ⟨n, l⟩; fin_cases n <;> fin_cases l <;> rfl)
    (by rintro ⟨n, l⟩; fin_cases n <;> fin_cases l <;> rfl)
  refine (hnet.smul (Real.sqrt ((k : ℝ) + 1))).congr fun m => ?_
  unfold fourJT fourJ netEval
  rw [sum_piFinset_unit, sum_Icc_neg]
  simp only [Finset.mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [Fin.prod_univ_two]
  simp only [hT, legVal, fourJLegsEquiv, Equiv.ofBijective_apply, fourJLegs]
  congr 1
  unfold flipAt threeJT
  simp [Function.update, sub_neg_eq_add]

/-! ## Contraction with a 3j symbol, and factorization -/

section Factor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Contracting the two legs `inr false`, `inr true` (spins `a`, `b`) of `X` with the 3j symbol
`(a b x)`: the third leg of the 3j symbol becomes the new leg `inr ()`. -/
noncomputable def contr3j (a b x : ℕ) (X : (ι ⊕ Bool → ℤ) → ℝ) (m : ι ⊕ Unit → ℤ) : ℝ :=
  ∑ p ∈ Icc (-(a : ℤ)) a, ∑ q ∈ Icc (-(b : ℤ)) b,
    X (Sum.elim (m ∘ Sum.inl) (fun c => if c then q else p)) * threeJ a b x p q (m (Sum.inr ()))

/-- The leg bookkeeping of `contr3j`: the new legs and the two contracted pairs, as legs of `X`
and of the 3j symbol. -/
def contr3jEquiv : ((ι ⊕ Unit) ⊕ Bool) ⊕ Bool ≃ (ι ⊕ Bool) ⊕ Fin 3 where
  toFun
    | .inl (.inl (.inl i)) => .inl (.inl i)
    | .inl (.inl (.inr _)) => .inr 2
    | .inl (.inr false) => .inl (.inr false)
    | .inl (.inr true) => .inr 0
    | .inr false => .inl (.inr true)
    | .inr true => .inr 1
  invFun
    | .inl (.inl i) => .inl (.inl (.inl i))
    | .inl (.inr false) => .inl (.inr false)
    | .inl (.inr true) => .inr false
    | .inr t => (![.inl (.inr true), .inr true, .inl (.inl (.inr ()))] : Fin 3 → _) t
  left_inv := by
    rintro ((( i | u) | b) | b)
    · rfl
    · rfl
    · cases b <;> rfl
    · cases b <;> rfl
  right_inv := by
    rintro ((i | b) | t)
    · rfl
    · cases b <;> rfl
    · fin_cases t <;> rfl

/-- **Contracting two incoming legs with a 3j symbol keeps a tensor invariant**; the new leg (the
third leg of the 3j symbol) is outgoing. -/
theorem IsInv.contr3j {j : ι ⊕ Bool → ℕ} {d : ι ⊕ Bool → Bool} {X : (ι ⊕ Bool → ℤ) → ℝ}
    (hX : IsInv j d X) (hp : d (Sum.inr false) = false) (hq : d (Sum.inr true) = false) (x : ℕ) :
    IsInv (Sum.elim (j ∘ Sum.inl) (fun _ => x)) (Sum.elim (d ∘ Sum.inl) (fun _ => true))
      (Lightlike.Recoupling.contr3j (j (Sum.inr false)) (j (Sum.inr true)) x X) := by
  set a := j (Sum.inr false)
  set b := j (Sum.inr true)
  have h3 := (isInv_threeJT a b x).dual
  have hP := (hX.mul h3).reindex contr3jEquiv
  have h1 := hP.contr (by rfl) (by simp [contr3jEquiv, hq])
  have h2 := h1.contr (by rfl) (by simp [contr3jEquiv, hp])
  have hj' : ((Sum.elim j ![a, b, x] ∘ contr3jEquiv) ∘ Sum.inl) ∘ Sum.inl =
      Sum.elim (j ∘ Sum.inl) (fun _ => x) := by
    funext y; rcases y with i | u <;> rfl
  have hd' : (((Sum.elim d fun i => !(![false, false, false] : Fin 3 → Bool) i) ∘ contr3jEquiv) ∘
      Sum.inl) ∘ Sum.inl = Sum.elim (d ∘ Sum.inl) (fun _ => true) := by
    funext y; rcases y with i | u <;> rfl
  rw [hj', hd'] at h2
  refine h2.congr fun m => ?_
  · unfold Lightlike.Recoupling.contr3j Lightlike.Recoupling.contr
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    simp only [Function.comp_def, contr3jEquiv, Equiv.coe_fn_symm_mk]
    congr 1
    · congr 1
      funext y; rcases y with i | c
      · rfl
      · cases c <;> rfl

/-- **Factorization through a 3j symbol** (the completeness of the 3j symbols): for admissible
projections `p`, `q` of the legs `inr false`, `inr true`,
`X(m, p, q) = Σ_x (x + 1) Σ_ξ (a b x; p q ξ) (contr3j a b x X)(m, ξ)`. The identity holds for
every tensor `X`; the unused hypothesis `_hX` only lets call sites infer `j`, `d` and `X`. -/
theorem factor_eq {j : ι ⊕ Bool → ℕ} {d : ι ⊕ Bool → Bool} {X : (ι ⊕ Bool → ℤ) → ℝ}
    (_hX : IsInv j d X) (m : ι → ℤ) {p q : ℤ} (hp : AdmProj (j (Sum.inr false)) p)
    (hq : AdmProj (j (Sum.inr true)) q) :
    X (Sum.elim m fun c => if c then q else p) =
      ∑ x ∈ range (j (Sum.inr false) + j (Sum.inr true) + 1), ((x : ℝ) + 1) *
        ∑ ξ ∈ Icc (-(x : ℤ)) x, threeJ (j (Sum.inr false)) (j (Sum.inr true)) x p q ξ *
          contr3j (j (Sum.inr false)) (j (Sum.inr true)) x X (Sum.elim m fun _ => ξ) := by
  set a := j (Sum.inr false)
  set b := j (Sum.inr true)
  unfold contr3j
  simp only [Sum.elim_comp_inl, Sum.elim_inr]
  have hterm : ∀ x : ℕ, ∀ ξ : ℤ, ((x : ℝ) + 1) * (threeJ a b x p q ξ *
      ∑ p' ∈ Icc (-(a : ℤ)) a, ∑ q' ∈ Icc (-(b : ℤ)) b,
        X (Sum.elim m fun c => if c then q' else p') * threeJ a b x p' q' ξ) =
      ∑ p' ∈ Icc (-(a : ℤ)) a, ∑ q' ∈ Icc (-(b : ℤ)) b,
        X (Sum.elim m fun c => if c then q' else p') *
          (((x : ℝ) + 1) * (threeJ a b x p q ξ * threeJ a b x p' q' ξ)) := by
    intro x ξ
    rw [Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun p' _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun q' _ => ?_
    ring
  symm
  calc _ = ∑ x ∈ range (a + b + 1), ∑ ξ ∈ Icc (-(x : ℤ)) x, ∑ p' ∈ Icc (-(a : ℤ)) a,
        ∑ q' ∈ Icc (-(b : ℤ)) b, X (Sum.elim m fun c => if c then q' else p') *
          (((x : ℝ) + 1) * (threeJ a b x p q ξ * threeJ a b x p' q' ξ)) := by
        refine sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact sum_congr rfl fun ξ _ => hterm x ξ
    _ = ∑ p' ∈ Icc (-(a : ℤ)) a, ∑ q' ∈ Icc (-(b : ℤ)) b,
        X (Sum.elim m fun c => if c then q' else p') *
          ∑ x ∈ range (a + b + 1), ∑ ξ ∈ Icc (-(x : ℤ)) x,
            ((x : ℝ) + 1) * (threeJ a b x p q ξ * threeJ a b x p' q' ξ) := by
        set G : ℕ → ℤ → ℤ → ℤ → ℝ := fun x ξ p' q' =>
          X (Sum.elim m fun c => if c then q' else p') *
            (((x : ℝ) + 1) * (threeJ a b x p q ξ * threeJ a b x p' q' ξ)) with hG
        have e1 : ∀ x ∈ range (a + b + 1), (∑ ξ ∈ Icc (-(x : ℤ)) x, ∑ p' ∈ Icc (-(a : ℤ)) a,
            ∑ q' ∈ Icc (-(b : ℤ)) b, G x ξ p' q') =
            ∑ p' ∈ Icc (-(a : ℤ)) a, ∑ q' ∈ Icc (-(b : ℤ)) b, ∑ ξ ∈ Icc (-(x : ℤ)) x,
              G x ξ p' q' := fun x _ => by
          rw [sum_comm]
          exact sum_congr rfl fun p' _ => sum_comm
        rw [sum_congr rfl e1, sum_comm]
        refine sum_congr rfl fun p' _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun q' _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ = X (Sum.elim m fun c => if c then q else p) := by
        simp only [sum_threeJ_complete a b hp hq, mul_ite, mul_one, mul_zero]
        have hpI : p ∈ Icc (-(a : ℤ)) a := mem_Icc.mpr ⟨hp.1, hp.2.1⟩
        have hqI : q ∈ Icc (-(b : ℤ)) b := mem_Icc.mpr ⟨hq.1, hq.2.1⟩
        rw [sum_eq_single p (fun p' _ hp' => sum_eq_zero fun q' _ => by
          rw [ite_eq_right (fun h => hp' h.1.symm)]) (fun h => absurd hpI h)]
        rw [sum_eq_single q (fun q' _ hq' => by rw [ite_eq_right (fun h => hq' h.2.symm)])
          (fun h => absurd hqI h)]
        simp

end Factor

/-! ## The intertwiners span the invariant tensors -/

/-- Legs `2, 3` of a four-leg tensor as `inl 0, inl 1`, legs `0, 1` as `inr false, inr true`. -/
def legs01 : Fin 2 ⊕ Bool ≃ Fin 4 where
  toFun
    | .inl i => (![2, 3] : Fin 2 → Fin 4) i
    | .inr false => 0
    | .inr true => 1
  invFun i := (![.inr false, .inr true, .inl 0, .inl 1] : Fin 4 → Fin 2 ⊕ Bool) i
  left_inv := by
    rintro (i | b)
    · fin_cases i <;> rfl
    · cases b <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- The new leg `inr ()` as `inl ()`, the legs `inl 0, inl 1` as `inr false, inr true`. -/
def legs23 : Unit ⊕ Bool ≃ Fin 2 ⊕ Unit where
  toFun
    | .inl _ => .inr ()
    | .inr false => .inl 0
    | .inr true => .inl 1
  invFun
    | .inl i => (![.inr false, .inr true] : Fin 2 → Unit ⊕ Bool) i
    | .inr _ => .inl ()
  left_inv := by
    rintro (u | b)
    · rfl
    · cases b <;> rfl
  right_inv := by
    rintro (i | u)
    · fin_cases i <;> rfl
    · rfl

/-- Two legs `inl (), inr ()` as `0, 1`. -/
def legs2 : Fin 2 ≃ Unit ⊕ Unit where
  toFun i := (![.inl (), .inr ()] : Fin 2 → Unit ⊕ Unit) i
  invFun
    | .inl _ => 0
    | .inr _ => 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by rintro (u | u) <;> rfl

/-- Schur's lemma with the spins and directions given as equations. -/
lemma schur' {a b : ℕ} {j : Fin 2 → ℕ} {d : Fin 2 → Bool} {X : (Fin 2 → ℤ) → ℝ} (hX : IsInv j d X)
    (hj : j = ![a, b]) (hd : d = ![false, true]) (m : Fin 2 → ℤ) :
    X m = if a = b then X ![(a : ℤ), a] * idT a m else 0 := by
  subst hj hd
  exact schur hX m

/-- `((-1)^k)² = 1` for an integer exponent. -/
lemma neg_one_zpow_mul_self (k : ℤ) : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by
  rw [← mul_zpow]; norm_num

/-- **Every invariant tensor with four incoming legs is a combination of the intertwiners**
`fourJ j₁ j₂ j₃ j₄ x`. -/
theorem exists_span_fourJ {j₁ j₂ j₃ j₄ : ℕ} {X : (Fin 4 → ℤ) → ℝ}
    (hX : IsInv ![j₁, j₂, j₃, j₄] ![false, false, false, false] X) :
    ∃ a : ℕ → ℝ, ∀ m, X m = ∑ x ∈ range (j₁ + j₂ + 1), a x * fourJT j₁ j₂ j₃ j₄ x m := by
  have h1 := hX.reindex legs01
  set X1 : (Fin 2 ⊕ Bool → ℤ) → ℝ := fun w => X (w ∘ legs01.symm) with hX1
  -- the first factorization, on legs `0, 1`
  have hY := fun x : ℕ => h1.contr3j rfl rfl x
  have h2 := fun x : ℕ => (hY x).reindex legs23
  have hZ := fun x y : ℕ => (h2 x).contr3j rfl rfl y
  have hW := fun x y : ℕ => ((hZ x y).reindex legs2).flip 0
  -- Schur: the two-leg tensors
  set Zf : ℕ → ℕ → (Unit ⊕ Unit → ℤ) → ℝ := fun x y =>
    contr3j j₃ j₄ y (fun w => contr3j j₁ j₂ x X1 (w ∘ legs23.symm)) with hZf
  have hsch : ∀ x y : ℕ, ∀ ξ η : ℤ, Zf x y (Sum.elim (fun _ => ξ) (fun _ => η)) =
      (-1) ^ (((x : ℤ) - ξ) / 2) * (if x = y then
        flipAt x 0 (fun n => Zf x x (n ∘ legs2.symm)) ![(x : ℤ), x] * idT x ![-ξ, η] else 0) := by
    intro x y ξ η
    have h0 := schur' (hW x y) (a := x) (b := y) (by funext i; fin_cases i <;> rfl)
      (by funext i; fin_cases i <;> rfl) ![-ξ, η]
    have h : flipAt x 0 (fun n => Zf x y (n ∘ legs2.symm)) ![-ξ, η] =
        if x = y then flipAt x 0 (fun n => Zf x y (n ∘ legs2.symm)) ![(x : ℤ), x] *
          idT x ![-ξ, η] else 0 := h0
    have e1 : Function.update ![-ξ, η] 0 (-((![-ξ, η] : Fin 2 → ℤ) 0)) = ![ξ, η] := by
      rw [update_vec0]; simp
    have e2 : (![ξ, η] : Fin 2 → ℤ) ∘ legs2.symm = Sum.elim (fun _ => ξ) (fun _ => η) := by
      funext u; rcases u with u | u <;> rfl
    have e3 : ((x : ℤ) + (![-ξ, η] : Fin 2 → ℤ) 0) / 2 = ((x : ℤ) - ξ) / 2 := by
      simp [sub_eq_add_neg]
    have hv : flipAt x 0 (fun n => Zf x y (n ∘ legs2.symm)) ![-ξ, η] =
        (-1) ^ (((x : ℤ) - ξ) / 2) * Zf x y (Sum.elim (fun _ => ξ) (fun _ => η)) := by
      show (-1 : ℝ) ^ (((x : ℤ) + (![-ξ, η] : Fin 2 → ℤ) 0) / 2) *
        Zf x y ((Function.update ![-ξ, η] 0 (-((![-ξ, η] : Fin 2 → ℤ) 0))) ∘ legs2.symm) = _
      rw [e1, e2, e3]
    rw [hv] at h
    rw [← mul_left_cancel_iff_of_pos (show (0 : ℝ) < 1 by norm_num)]
    calc 1 * Zf x y (Sum.elim (fun _ => ξ) (fun _ => η))
        = ((-1) ^ (((x : ℤ) - ξ) / 2) * (-1) ^ (((x : ℤ) - ξ) / 2)) *
            Zf x y (Sum.elim (fun _ => ξ) (fun _ => η)) := by rw [neg_one_zpow_mul_self]
      _ = (-1) ^ (((x : ℤ) - ξ) / 2) * ((-1) ^ (((x : ℤ) - ξ) / 2) *
            Zf x y (Sum.elim (fun _ => ξ) (fun _ => η))) := by ring
      _ = 1 * ((-1) ^ (((x : ℤ) - ξ) / 2) * (if x = y then
            flipAt x 0 (fun n => Zf x x (n ∘ legs2.symm)) ![(x : ℤ), x] * idT x ![-ξ, η]
            else 0)) := by
          rw [h, one_mul]
          by_cases hxy : x = y
          · subst hxy; rfl
          · rw [ite_eq_right hxy, ite_eq_right hxy]
  -- the two factorizations
  have hfac : ∀ m : Fin 4 → ℤ, (∀ i, AdmProj (![j₁, j₂, j₃, j₄] i) (m i)) →
      X m = ∑ x ∈ range (j₁ + j₂ + 1), ((x : ℝ) + 1) * ∑ ξ ∈ Icc (-(x : ℤ)) x,
        threeJ j₁ j₂ x (m 0) (m 1) ξ * ∑ y ∈ range (j₃ + j₄ + 1), ((y : ℝ) + 1) *
          ∑ η ∈ Icc (-(y : ℤ)) y, threeJ j₃ j₄ y (m 2) (m 3) η *
            Zf x y (Sum.elim (fun _ => ξ) (fun _ => η)) := by
    intro m hm
    have hXm : X m = X1 (Sum.elim ![m 2, m 3] fun c => if c then m 1 else m 0) := by
      simp only [hX1]
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [hXm, factor_eq h1 ![m 2, m 3] (hm 0) (hm 1)]
    refine sum_congr rfl fun x _ => ?_
    congr 1
    refine sum_congr rfl fun ξ _ => ?_
    congr 1
    change contr3j j₁ j₂ x X1 (Sum.elim ![m 2, m 3] fun _ => ξ) = _
    have hY' : contr3j j₁ j₂ x X1 (Sum.elim ![m 2, m 3] fun _ => ξ) =
        (fun w => contr3j j₁ j₂ x X1 (w ∘ legs23.symm))
          (Sum.elim (fun _ => ξ) fun c => if c then m 3 else m 2) := by
      congr 1
      funext i
      rcases i with i | u
      · fin_cases i <;> rfl
      · rfl
    exact hY'.trans (factor_eq (h2 x) (fun _ => ξ) (hm 2) (hm 3))
  -- the coefficients
  set c : ℕ → ℝ := fun x => flipAt x 0 (fun n => Zf x x (n ∘ legs2.symm)) ![(x : ℤ), x] with hc
  have hinner : ∀ (m : Fin 4 → ℤ) (x : ℕ) (ξ : ℤ),
      ∑ y ∈ range (j₃ + j₄ + 1), ((y : ℝ) + 1) * ∑ η ∈ Icc (-(y : ℤ)) y,
        threeJ j₃ j₄ y (m 2) (m 3) η * Zf x y (Sum.elim (fun _ => ξ) (fun _ => η)) =
      ((x : ℝ) + 1) * (-1) ^ (((x : ℤ) - ξ) / 2) * c x *
        (if AdmProj x ξ then threeJ j₃ j₄ x (m 2) (m 3) (-ξ) else 0) := by
    intro m x ξ
    simp only [hsch]
    by_cases hx : x ∈ range (j₃ + j₄ + 1)
    · rw [sum_eq_single x (fun y _ hy => by
        rw [sum_eq_zero fun η _ => by rw [ite_eq_right (Ne.symm hy)]; ring, mul_zero])
        (fun h => absurd hx h)]
      simp only [ite_true]
      by_cases ha : AdmProj x ξ
      · have hI : -ξ ∈ Icc (-(x : ℤ)) x := by unfold AdmProj at ha; exact mem_Icc.mpr ⟨by omega, by omega⟩
        rw [sum_eq_single (-ξ) (fun η _ hη => by
          rw [idT, ite_eq_right (fun h => hη (by simpa using h.2))]; ring)
          (fun h => absurd hI h)]
        rw [ite_eq_left ha, idT, ite_eq_left ⟨by simpa [admProj_neg] using ha, by simp⟩]
        ring
      · rw [sum_eq_zero fun η _ => by
          rw [idT, ite_eq_right (fun h => ha (admProj_neg.mp (by simpa using h.1)))]; ring,
          ite_eq_right ha]
        ring
    · rw [sum_eq_zero fun y hy => by
        rw [sum_eq_zero fun η _ => by
          rw [ite_eq_right (fun (h : x = y) => hx (by rw [h]; exact hy))]; ring, mul_zero]]
      have h0 : threeJ j₃ j₄ x (m 2) (m 3) (-ξ) = 0 :=
        threeJ_eq_zero_of_not fun h => hx (mem_range.mpr (by unfold Tri at h; omega))
      simp [h0]
  refine ⟨fun x => ((x : ℝ) + 1) * Real.sqrt ((x : ℝ) + 1) * c x, fun m => ?_⟩
  by_cases hm : ∀ i, AdmProj (![j₁, j₂, j₃, j₄] i) (m i)
  · rw [hfac m hm]
    refine sum_congr rfl fun x _ => ?_
    simp only [hinner]
    unfold fourJT fourJ
    have hs : Real.sqrt ((x : ℝ) + 1) * Real.sqrt ((x : ℝ) + 1) = (x : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    simp only [Finset.mul_sum]
    refine sum_congr rfl fun ξ _ => ?_
    by_cases ha : AdmProj x ξ
    · rw [ite_eq_left ha, ← threeJ_cycle x j₃ j₄ (-ξ) (m 2) (m 3)]
      linear_combination (-((x : ℝ) + 1) * c x * (-1) ^ (((x : ℤ) - ξ) / 2) *
        threeJ j₁ j₂ x (m 0) (m 1) ξ * threeJ j₃ j₄ x (m 2) (m 3) (-ξ)) * hs
    · have h0 : threeJ j₁ j₂ x (m 0) (m 1) ξ = 0 := threeJ_eq_zero_of_not fun h => ha h.2
      rw [ite_eq_right ha, h0]
      ring
  · obtain ⟨i, hi⟩ := not_forall.mp hm
    rw [hX.eq_zero hi]
    symm
    refine sum_eq_zero fun x _ => ?_
    have : fourJT j₁ j₂ j₃ j₄ x m = 0 := by
      by_contra h
      have := admProj_of_fourJ_ne_zero h
      fin_cases i <;> simp_all
    rw [this, mul_zero]

/-- An intertwiner vanishes unless its two triads are admissible. -/
lemma fourJ_eq_zero_of_not_adm {j₁ j₂ j₃ j₄ k : ℕ} (h : ¬(Tri j₁ j₂ k ∧ Tri k j₃ j₄))
    (m₁ m₂ m₃ m₄ : ℤ) : fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = 0 := by
  by_contra h'
  unfold fourJ at h'
  obtain ⟨μ, -, hμ⟩ := exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h')
  exact h ⟨(tri_admProj_of_threeJ_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul hμ))).1,
    by
      have := adm3_of_threeJ_ne_zero (right_ne_zero_of_mul hμ)
      unfold Tri; omega⟩

/-- The box of projections of four legs with spins `j`. -/
def box4 (j₁ j₂ j₃ j₄ : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun i => Icc (-((![j₁, j₂, j₃, j₄] i : ℕ) : ℤ)) (![j₁, j₂, j₃, j₄] i)

/-- Orthonormality of the intertwiners, as a sum over `box4`. -/
lemma sum_box4_fourJT (j₁ j₂ j₃ j₄ k k' : ℕ) :
    ∑ n ∈ box4 j₁ j₂ j₃ j₄, fourJT j₁ j₂ j₃ j₄ k n * fourJT j₁ j₂ j₃ j₄ k' n =
      if k = k' ∧ Tri j₁ j₂ k ∧ Tri k j₃ j₄ then 1 else 0 := by
  rw [box4, sum_piFinset_four]
  exact sum_fourJ_mul_fourJ j₁ j₂ j₃ j₄ k k'

/-- **The intertwiners span the invariant tensors**: an invariant tensor with four incoming legs is
the sum of its components along the orthonormal intertwiners,
`X = Σ_k ⟨ι^{(k)}, X⟩ ι^{(k)}`. Equivalently, the operator `Σ_k ι^{(k)} ⊗ ι^{(k)}` acts as the
identity on invariant tensors. -/
theorem eq_sum_fourJ {j₁ j₂ j₃ j₄ : ℕ} {X : (Fin 4 → ℤ) → ℝ}
    (hX : IsInv ![j₁, j₂, j₃, j₄] ![false, false, false, false] X) (m : Fin 4 → ℤ) :
    X m = ∑ k ∈ range (j₁ + j₂ + 1),
      (∑ n ∈ box4 j₁ j₂ j₃ j₄, fourJT j₁ j₂ j₃ j₄ k n * X n) * fourJT j₁ j₂ j₃ j₄ k m := by
  obtain ⟨a, ha⟩ := exists_span_fourJ hX
  have hc : ∀ k ∈ range (j₁ + j₂ + 1), ∑ n ∈ box4 j₁ j₂ j₃ j₄, fourJT j₁ j₂ j₃ j₄ k n * X n =
      if Tri j₁ j₂ k ∧ Tri k j₃ j₄ then a k else 0 := by
    intro k hk
    simp only [ha, Finset.mul_sum]
    rw [sum_comm]
    simp only [← Finset.mul_sum, mul_left_comm (fourJT j₁ j₂ j₃ j₄ k _) (a _)]
    simp only [sum_box4_fourJT]
    rw [sum_eq_single k (fun x _ hx => by rw [ite_eq_right (fun h => hx h.1.symm), mul_zero])
      (fun h => absurd hk h)]
    by_cases ht : Tri j₁ j₂ k ∧ Tri k j₃ j₄
    · simp [ht]
    · simp [ht]
  rw [ha m]
  refine sum_congr rfl fun k hk => ?_
  rw [hc k hk]
  by_cases ht : Tri j₁ j₂ k ∧ Tri k j₃ j₄
  · rw [ite_eq_left ht]
  · rw [ite_eq_right ht, fourJT, fourJ_eq_zero_of_not_adm ht]; ring

end Lightlike.Recoupling
