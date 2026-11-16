import Lightlike.Recoupling.FifteenJ

/-!
# Orthogonality of the 15j symbols

The 15j symbol of the first kind is a recoupling coefficient: up to normalisation, the overlap of
two bases of invariant tensors, one coupling along the rail `a₀, a₁, …, a₄, b₀` of its Möbius
ladder and one along the rail `b₀, b₁, …, b₄, a₀`, with the rungs `c₀ … c₄` as the shared legs. So
it satisfies an orthogonality relation (`sum_fifteenJ_mul_fifteenJ`, doubled units):

`Σ_{a₁ … a₄} Π_t (2a_t + 1) {15j}(a, b, c) {15j}(a, b', c) = δ_{bb'} / Π_{t=1}^{4} (2b_t + 1)`

for `a₀, b₀, c` fixed and `b`, `b'` with admissible vertices `(b_t c_t b_{t+1})`, `b₅ = a₀`.

## Implementation notes

The closed Möbius ladder (`Ladder.lean`) of five rungs is the 15j symbol up to the sign `(-1)^{b₀}`
(`fifteenJ_eq_mobius`). Started from a point `(α, β)`, a ladder factorises into its two rails,
`chainA` and `chainB` (`ladder_factor`, from `rung_factor`). Then:

- **completeness of the first rails** (`ctrA_parseval`): summed over the inner spins and the end
  spin of the first rail with weights `2x + 1`, the contractions `ctrA` of the first rails with two
  functions give their plain inner product. Each of the five steps is 3j completeness
  (`sum_railStep_complete`);
- **orthonormality of the second rails** (`gramB_eq`): their Gram matrix is diagonal, with the
  value `Π_t 1/(2b_{t+1} + 1)`. Each step is 3j orthogonality (`sum_orth_step`);
- **the open ladder** (`ladder_open`, `ctrA_chainB`): contracting a first rail with end spin `J`
  and a second rail started at `β` gives zero unless `J = b₀` and the end projection is `β`, and
  then the closed ladder divided by `2b₀ + 1`.

Inserting the completeness of the first rails into the inner product of two second rails, the open
ladder formula collapses the sums over the end spin, and orthonormality gives the result
(`sum_mobius_mul_mobius`).

## Main results

- `ladder_factor`, `ctrA_parseval`, `gramB_eq`.
- `sum_mobius_mul_mobius`: orthogonality of the closed ladders of five rungs.
- `sum_fifteenJ_mul_fifteenJ`: **orthogonality of the 15j symbols of the first kind.**

## References

- A. P. Yutsis, I. B. Levinson, V. V. Vanagas, *Mathematical Apparatus of the Theory of Angular
  Momentum*, Israel Program for Scientific Translations (1962): 3nj symbols as recoupling
  coefficients.
-/

open PhyslibAlpha.Sl2 Finset Lightlike.Pentagon

namespace Lightlike.Recoupling

/-- One step along a rail: carries a function of the projection of the rail spin `s` across the
vertex `(s s' r)` with rung projection `c`, contracting with the sign `(-1)^{s - m}`. -/
noncomputable def railStep (s s' r : ℕ) (c : ℤ) (f : ℤ → ℝ) (M : ℤ) : ℝ :=
  ∑ m ∈ Icc (-(s : ℤ)) s, f m * edgeSign s m * threeJ s s' r (-m) M c

/-- The point function at `α`. -/
def pointFn (α m : ℤ) : ℝ := if m = α then 1 else 0

/-- Reversing the order of four nested finite sums. -/
lemma sum_four_rev {α β γ δ : Type*} (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d = ∑ d ∈ D, ∑ c ∈ C, ∑ b ∈ B, ∑ a ∈ A, f a b c d := by
  simp only [sum_comm (s := C) (t := D), sum_comm (s := B) (t := D), sum_comm (s := A) (t := D)]
  refine sum_congr rfl fun d _ => ?_
  simp only [sum_comm (s := B) (t := C), sum_comm (s := A) (t := C)]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_comm]

/-- Exchanging two pairs of nested finite sums. -/
lemma sum_four_swap {α β γ δ : Type*} (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d = ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  simp only [sum_comm (s := B) (t := C), sum_comm (s := A) (t := C)]
  refine sum_congr rfl fun c _ => ?_
  simp only [sum_comm (s := B) (t := D), sum_comm (s := A) (t := D)]

/-- Moving three nested finite sums outside two others. -/
lemma sum_five_swap {α β γ δ ε : Type*} (A : Finset α) (B : Finset β) (C : Finset γ)
    (D : Finset δ) (E : Finset ε) (f : α → β → γ → δ → ε → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, f a b c d e =
      ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, ∑ a ∈ A, ∑ b ∈ B, f a b c d e := by
  simp only [sum_comm (s := B) (t := C), sum_comm (s := A) (t := C)]
  refine sum_congr rfl fun c _ => ?_
  simp only [sum_comm (s := B) (t := D), sum_comm (s := A) (t := D)]
  refine sum_congr rfl fun d _ => ?_
  simp only [sum_comm (s := B) (t := E), sum_comm (s := A) (t := E)]

/-- **A rung factorises into its two rails**: carried across a rung, a sum of products of a
function of the first rail projection and a function of the second becomes such a sum again, with
one more summation over the rung projection. -/
lemma rung_factor {γ : Type*} (S : Finset γ) (u v : γ → ℤ → ℝ) (a a' b b' c : ℕ) (q : ℤ × ℤ) :
    rung a a' b b' c (fun p => ∑ g ∈ S, u g p.1 * v g p.2) q =
      ∑ h ∈ S ×ˢ Icc (-(c : ℤ)) c, railStep a a' c h.2 (u h.1) q.1 *
        (edgeSign c h.2 * railStep b b' c (-h.2) (v h.1) q.2) := by
  unfold rung rungKernel railStep pairBox
  rw [sum_product, sum_product]
  simp only [sum_mul, mul_sum]
  rw [sum_four_rev]
  refine sum_congr rfl fun g _ => sum_congr rfl fun c' _ => sum_congr rfl fun n _ =>
    sum_congr rfl fun m _ => ?_
  ring

/-- The rung projections `(c₀, …, c_{n-1})` of `n` rungs, as a nested product. -/
@[reducible] def ChainIdx : ℕ → Type
  | 0 => Unit
  | n + 1 => ChainIdx n × ℤ

instance : (n : ℕ) → DecidableEq (ChainIdx n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => @instDecidableEqProd _ _ (instDecidableEqChainIdx n) _

/-- The box `|c_t| ≤ C t` of rung projections. -/
def chainBox (C : ℕ → ℕ) : (n : ℕ) → Finset (ChainIdx n)
  | 0 => {()}
  | n + 1 => chainBox C n ×ˢ Icc (-(C n : ℤ)) (C n)

/-- The first rail of a ladder from the projection `α` of `A 0`: `n` rail steps with the rung
projections `h`. -/
noncomputable def chainA (A C : ℕ → ℕ) (α : ℤ) : (n : ℕ) → ChainIdx n → ℤ → ℝ
  | 0, _, m => pointFn α m
  | n + 1, h, m => railStep (A n) (A (n + 1)) (C n) h.2 (chainA A C α n h.1) m

/-- The second rail of a ladder from the projection `β` of `B 0`, with the opposite rung
projections and the rung signs `(-1)^{c - m_c}`. -/
noncomputable def chainB (B C : ℕ → ℕ) (β : ℤ) : (n : ℕ) → ChainIdx n → ℤ → ℝ
  | 0, _, m => pointFn β m
  | n + 1, h, m => edgeSign (C n) h.2 * railStep (B n) (B (n + 1)) (C n) (-h.2) (chainB B C β n h.1) m

/-- **A ladder from a point is a sum over rung projections of products of its two rails.** -/
theorem ladder_factor (A B C : ℕ → ℕ) (α β : ℤ) (n : ℕ) :
    ladder A B C n (pairDelta (α, β)) =
      fun q => ∑ h ∈ chainBox C n, chainA A C α n h q.1 * chainB B C β n h q.2 := by
  induction n with
  | zero =>
    funext q
    show pairDelta (α, β) q = ∑ h ∈ ({()} : Finset (ChainIdx 0)), pointFn α q.1 * pointFn β q.2
    rw [sum_const, show ({()} : Finset (ChainIdx 0)).card = 1 from rfl, one_smul]
    simp only [pairDelta, pointFn, Prod.ext_iff]
    split_ifs <;> simp_all
  | succ n ih =>
    funext q
    simp only [ladder]
    rw [ih, rung_factor]
    rfl

/-! ## Completeness of the first rail -/

/-- Rails that agree up to `n` give the same first-rail chain of length `n`. -/
lemma chainA_congr {A A' : ℕ → ℕ} (C : ℕ → ℕ) (α : ℤ) (n : ℕ) (h : ∀ t ≤ n, A t = A' t) :
    chainA A C α n = chainA A' C α n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext g m
    simp only [chainA]
    rw [ih (fun t ht => h t (by omega)), h n (by omega), h (n + 1) le_rfl]

/-- The contraction `Σ_α Σ_h chainA α n h M · F α h` of the first rail with a function of its
start projection and its rung projections. -/
noncomputable def ctrA (A C : ℕ → ℕ) (n : ℕ) (F : ℤ → ChainIdx n → ℝ) (M : ℤ) : ℝ :=
  ∑ α ∈ Icc (-(A 0 : ℤ)) (A 0), ∑ h ∈ chainBox C n, chainA A C α n h M * F α h

/-- Peeling the last rail step off a contraction. -/
lemma ctrA_succ (A C : ℕ → ℕ) (n : ℕ) (F : ℤ → ChainIdx (n + 1) → ℝ) (M : ℤ) :
    ctrA A C (n + 1) F M = ∑ c ∈ Icc (-(C n : ℤ)) (C n), ∑ m ∈ Icc (-(A n : ℤ)) (A n),
      ctrA A C n (fun α g => F α (g, c)) m * edgeSign (A n) m * threeJ (A n) (A (n + 1)) (C n) (-m) M c := by
  unfold ctrA
  simp only [chainBox, chainA, railStep]
  simp only [sum_product, sum_mul]
  rw [sum_four_swap]
  refine sum_congr rfl fun c _ => sum_congr rfl fun m _ => sum_congr rfl fun α _ =>
    sum_congr rfl fun g _ => ?_
  ring

/-- **One step of completeness along a rail**: summed over the next rail spin `J` and its
projection `M` with weight `2J + 1`, two rail steps contract to the identity in the previous
projection and the rung projection. -/
lemma sum_railStep_complete (s r : ℕ) (P Q : ℤ → ℤ → ℝ)
    (hP : ∀ m c, ¬(AdmProj s m ∧ AdmProj r c) → P m c = 0) :
    ∑ J ∈ range (s + r + 1), ∑ M ∈ Icc (-(J : ℤ)) J, ((J : ℝ) + 1) *
      (∑ c ∈ Icc (-(r : ℤ)) r, ∑ m ∈ Icc (-(s : ℤ)) s, P m c * edgeSign s m * threeJ s J r (-m) M c) *
      (∑ c ∈ Icc (-(r : ℤ)) r, ∑ m ∈ Icc (-(s : ℤ)) s, Q m c * edgeSign s m * threeJ s J r (-m) M c) =
    ∑ c ∈ Icc (-(r : ℤ)) r, ∑ m ∈ Icc (-(s : ℤ)) s, P m c * Q m c := by
  set U := Icc (-(r : ℤ)) r ×ˢ Icc (-(s : ℤ)) s with hU
  -- the double sums as sums over pairs `u = (c, m)`
  have hflat : ∀ F : ℤ → ℤ → ℝ, ∑ c ∈ Icc (-(r : ℤ)) r, ∑ m ∈ Icc (-(s : ℤ)) s, F m c =
      ∑ u ∈ U, F u.2 u.1 := fun F => by rw [hU, sum_product]
  simp only [hflat, mul_sum, sum_mul]
  -- move the sums over `u` and `w` outside the sums over `J` and `M`
  have hswap : ∀ G : ℕ → ℤ → (ℤ × ℤ) → (ℤ × ℤ) → ℝ,
      ∑ J ∈ range (s + r + 1), ∑ M ∈ Icc (-(J : ℤ)) J, ∑ u ∈ U, ∑ w ∈ U, G J M u w =
        ∑ u ∈ U, ∑ w ∈ U, ∑ J ∈ range (s + r + 1), ∑ M ∈ Icc (-(J : ℤ)) J, G J M u w := by
    intro G
    rw [sum_congr rfl fun J _ => sum_comm, sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_congr rfl fun J _ => sum_comm, sum_comm]
  rw [hswap]
  -- 3j completeness in the sums over `J` and `M`
  have hterm : ∀ u w : ℤ × ℤ, ∑ J ∈ range (s + r + 1), ∑ M ∈ Icc (-(J : ℤ)) J,
      ((J : ℝ) + 1) * (P u.2 u.1 * edgeSign s u.2 * threeJ s J r (-u.2) M u.1) *
        (Q w.2 w.1 * edgeSign s w.2 * threeJ s J r (-w.2) M w.1) =
      if u = w then P u.2 u.1 * Q u.2 u.1 else 0 := by
    intro u w
    by_cases hadm : AdmProj s u.2 ∧ AdmProj r u.1
    · have hm : AdmProj s (-u.2) := by
        obtain ⟨⟨h1, h2, h3⟩, -⟩ := hadm; exact ⟨by omega, by omega, by omega⟩
      have hc := sum_threeJ_complete s r hm hadm.2 (-w.2) w.1
      have hsw : ∀ (J : ℕ) (m M c : ℤ), threeJ s J r (-m) M c =
          (-1) ^ ((s + r + J) / 2) * threeJ s r J (-m) c M := fun J m M c =>
        threeJ_swap₂₃ s r J (-m) c M
      calc _ = P u.2 u.1 * Q w.2 w.1 * edgeSign s u.2 * edgeSign s w.2 *
            ∑ J ∈ range (s + r + 1), ∑ M ∈ Icc (-(J : ℤ)) J, ((J : ℝ) + 1) *
              (threeJ s r J (-u.2) u.1 M * threeJ s r J (-w.2) w.1 M) := by
            rw [mul_sum]
            refine sum_congr rfl fun J _ => ?_
            rw [mul_sum]
            refine sum_congr rfl fun M _ => ?_
            rw [hsw J u.2 M u.1, hsw J w.2 M w.1]
            have h2 : ((-1 : ℝ) ^ ((s + r + J) / 2)) * (-1) ^ ((s + r + J) / 2) = 1 := by
              rw [← mul_pow]; norm_num
            linear_combination (P u.2 u.1 * Q w.2 w.1 * edgeSign s u.2 * edgeSign s w.2 *
              ((J : ℝ) + 1) * threeJ s r J (-u.2) u.1 M * threeJ s r J (-w.2) w.1 M) * h2
        _ = _ := by
            rw [hc]
            by_cases huw : u = w
            · subst huw
              rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_left rfl]
              have he : edgeSign s u.2 * edgeSign s u.2 = 1 := by
                unfold edgeSign; rw [← mul_zpow]; norm_num
              linear_combination (P u.2 u.1 * Q u.2 u.1) * he
            · rw [ite_eq_right (fun h => huw (Prod.ext h.2 (by linarith [h.1]))), ite_eq_right huw]
              ring
    · have h0 := hP u.2 u.1 hadm
      simp only [h0, zero_mul, mul_zero, sum_const_zero]
      split_ifs <;> ring
  simp only [hterm]
  refine sum_congr rfl fun u hu => ?_
  rw [sum_ite_eq', ite_eq_left hu]

/-- Rails that agree up to `n` give the same contraction of length `n`. -/
lemma ctrA_congr {A A' : ℕ → ℕ} (C : ℕ → ℕ) (n : ℕ) (h : ∀ t ≤ n, A t = A' t)
    (F : ℤ → ChainIdx n → ℝ) : ctrA A C n F = ctrA A' C n F := by
  funext M
  unfold ctrA
  rw [h 0 (Nat.zero_le _)]
  simp only [chainA_congr C _ n h]

/-- **Completeness step for contractions**: summing over the new end spin `J` of the rail (the rails
`R J` agree with `A` up to `n` and end in `J`) peels one rail step off both contractions. -/
lemma ctrA_complete_step (A C : ℕ → ℕ) (R : ℕ → ℕ → ℕ) (n : ℕ) (hR1 : ∀ J, R J (n + 1) = J)
    (hR2 : ∀ J, ∀ t ≤ n, R J t = A t) (F G : ℤ → ChainIdx (n + 1) → ℝ)
    (hF : ∀ m c, ¬(AdmProj (A n) m ∧ AdmProj (C n) c) →
      ctrA A C n (fun α g => F α (g, c)) m = 0) :
    ∑ J ∈ range (A n + C n + 1), ∑ M ∈ Icc (-(J : ℤ)) J,
      ((J : ℝ) + 1) * (ctrA (R J) C (n + 1) F M * ctrA (R J) C (n + 1) G M) =
    ∑ c ∈ Icc (-(C n : ℤ)) (C n), ∑ m ∈ Icc (-(A n : ℤ)) (A n),
      ctrA A C n (fun α g => F α (g, c)) m * ctrA A C n (fun α g => G α (g, c)) m := by
  rw [← sum_railStep_complete (A n) (C n) _ _ hF]
  refine sum_congr rfl fun J _ => sum_congr rfl fun M _ => ?_
  rw [ctrA_succ, ctrA_succ, hR2 J n le_rfl, hR1 J]
  simp only [ctrA_congr C n (hR2 J)]
  ring

/-- A rail step vanishes at an inadmissible end projection. -/
lemma railStep_eq_zero {s s' r : ℕ} {c : ℤ} {f : ℤ → ℝ} {M : ℤ} (h : ¬AdmProj s' M) :
    railStep s s' r c f M = 0 := by
  unfold railStep
  refine sum_eq_zero fun m _ => ?_
  rw [threeJ_of_not (fun hA => h (by
    obtain ⟨-, -, -, h4, h5, -, -, -, h9, -⟩ := hA; exact ⟨h4, h5, h9⟩)), mul_zero]

/-- A rail step vanishes at an inadmissible rung projection. -/
lemma railStep_eq_zero_of_rung {s s' r : ℕ} {c : ℤ} {f : ℤ → ℝ} (h : ¬AdmProj r c) (M : ℤ) :
    railStep s s' r c f M = 0 := by
  unfold railStep
  refine sum_eq_zero fun m _ => ?_
  rw [threeJ_of_not (fun hA => h (by
    obtain ⟨-, -, -, -, -, h6, h7, -, -, h10, -⟩ := hA; exact ⟨h6, h7, h10⟩)), mul_zero]

/-- A rail step of the zero function is zero. -/
lemma railStep_zero {s s' r : ℕ} {c : ℤ} {f : ℤ → ℝ} (h : ∀ m, f m = 0) (M : ℤ) :
    railStep s s' r c f M = 0 := by
  unfold railStep
  simp [h]

/-! ## Orthonormality of the second rail -/

/-- The Gram matrix `Σ_β Σ_h chainB β n h q · chainB' β n h q'` of the second rails of two ladders
with rails `B`, `B'` (summed over the start projection `β` of `B 0` and the rung projections). -/
noncomputable def gramB (B B' C : ℕ → ℕ) (n : ℕ) (q q' : ℤ) : ℝ :=
  ∑ β ∈ Icc (-(B 0 : ℤ)) (B 0), ∑ h ∈ chainBox C n, chainB B C β n h q * chainB B' C β n h q'

/-- One step of the Gram matrix. -/
lemma gramB_succ_eq (B B' C : ℕ → ℕ) (n : ℕ) (q q' : ℤ) :
    gramB B B' C (n + 1) q q' = ∑ c ∈ Icc (-(C n : ℤ)) (C n), ∑ m ∈ Icc (-(B n : ℤ)) (B n),
      ∑ m' ∈ Icc (-(B' n : ℤ)) (B' n), gramB B B' C n m m' *
        (edgeSign (B n) m * threeJ (B n) (B (n + 1)) (C n) (-m) q (-c)) *
        (edgeSign (B' n) m' * threeJ (B' n) (B' (n + 1)) (C n) (-m') q' (-c)) := by
  unfold gramB
  simp only [chainBox, chainB, railStep]
  simp only [sum_product, mul_sum, sum_mul]
  rw [sum_five_swap]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun m _ => sum_congr rfl fun m' _ =>
    sum_congr rfl fun β _ => sum_congr rfl fun g _ => ?_
  have he : edgeSign (C n) c * edgeSign (C n) c = 1 := by
    unfold edgeSign; rw [← mul_zpow]; norm_num
  linear_combination (chainB B C β n g m * edgeSign (B n) m * threeJ (B n) (B (n + 1)) (C n) (-m) q (-c) *
    (chainB B' C β n g m' * edgeSign (B' n) m' * threeJ (B' n) (B' (n + 1)) (C n) (-m') q' (-c))) * he

/-- **One step of orthogonality along a rail**: a diagonal Gram matrix `κ δ_{mm'}` carried across
the vertices `(s s₁ r)` and `(s s₁' r)` and summed over the rung projection stays diagonal, with
`κ / (2s₁ + 1)` for `s₁ = s₁'`. -/
lemma sum_orth_step (s s1 s1' r : ℕ) (Γ : ℤ → ℤ → ℝ) (κ : ℝ)
    (hΓ : ∀ m m', AdmProj s m → AdmProj s m' → Γ m m' = if m = m' then κ else 0) (q q' : ℤ) :
    ∑ c ∈ Icc (-(r : ℤ)) r, ∑ m ∈ Icc (-(s : ℤ)) s, ∑ m' ∈ Icc (-(s : ℤ)) s, Γ m m' *
        (edgeSign s m * threeJ s s1 r (-m) q (-c)) * (edgeSign s m' * threeJ s s1' r (-m') q' (-c)) =
      if s1 = s1' ∧ q = q' ∧ Tri s r s1 ∧ AdmProj s1 q then κ / ((s1 : ℝ) + 1) else 0 := by
  -- the inner sum over `m'` collapses to `m' = m`
  have hinner : ∀ c m, m ∈ Icc (-(s : ℤ)) s → ∑ m' ∈ Icc (-(s : ℤ)) s, Γ m m' *
      (edgeSign s m * threeJ s s1 r (-m) q (-c)) * (edgeSign s m' * threeJ s s1' r (-m') q' (-c)) =
      κ * (threeJ s s1 r (-m) q (-c) * threeJ s s1' r (-m) q' (-c)) := by
    intro c m hm
    by_cases hadm : AdmProj s m
    · rw [sum_eq_single m (fun m' _ hne => ?_) (fun h => absurd hm h)]
      · rw [hΓ m m hadm hadm, ite_eq_left rfl]
        have he : edgeSign s m * edgeSign s m = 1 := by
          unfold edgeSign; rw [← mul_zpow]; norm_num
        linear_combination (κ * threeJ s s1 r (-m) q (-c) * threeJ s s1' r (-m) q' (-c)) * he
      · by_cases hadm' : AdmProj s m'
        · rw [hΓ m m' hadm hadm', ite_eq_right (Ne.symm hne)]; ring
        · rw [threeJ_of_not (j₁ := s) (j₂ := s1') (j₃ := r) (m₁ := -m') (m₂ := q') (m₃ := -c)
            (fun h => hadm' (by obtain ⟨-, h1, h2, -, -, -, -, h7, -⟩ := h
                                exact ⟨by omega, by omega, by omega⟩))]
          ring
    · have h0 : threeJ s s1 r (-m) q (-c) = 0 := threeJ_of_not (fun h => hadm (by
        obtain ⟨-, h1, h2, -, -, -, -, h7, -⟩ := h; exact ⟨by omega, by omega, by omega⟩))
      simp [h0]
  rw [sum_congr rfl fun c _ => sum_congr rfl fun m hm => hinner c m hm]
  simp only [← mul_sum]
  -- 3j orthogonality over the first and third columns
  have hsw : ∀ (s₁ : ℕ) (m c : ℤ) (q : ℤ), threeJ s s₁ r (-m) q (-c) =
      (-1) ^ ((s + r + s₁) / 2) * threeJ s r s₁ (-m) (-c) q := fun s₁ m c q =>
    threeJ_swap₂₃ s r s₁ (-m) (-c) q
  have horth : ∑ c ∈ Icc (-(r : ℤ)) r, ∑ m ∈ Icc (-(s : ℤ)) s,
      threeJ s s1 r (-m) q (-c) * threeJ s s1' r (-m) q' (-c) =
      (-1) ^ ((s + r + s1) / 2) * (-1) ^ ((s + r + s1') / 2) *
        (if s1 = s1' ∧ q = q' ∧ Tri s r s1 ∧ AdmProj s1 q then 1 / ((s1 : ℝ) + 1) else 0) := by
    rw [← sum_threeJ_mul_threeJ, sum_comm, sum_Icc_neg s, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_Icc_neg r, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [hsw s1, hsw s1', neg_neg, neg_neg]
    ring
  rw [horth]
  by_cases hc : s1 = s1' ∧ q = q' ∧ Tri s r s1 ∧ AdmProj s1 q
  · rw [ite_eq_left hc, ite_eq_left hc]
    obtain ⟨rfl, -⟩ := hc
    have h2 : ((-1 : ℝ) ^ ((s + r + s1) / 2)) * (-1) ^ ((s + r + s1) / 2) = 1 := by
      rw [← mul_pow]; norm_num
    rw [h2]; ring
  · rw [ite_eq_right hc, ite_eq_right hc]; ring

/-- **Orthonormality of the second rails**: the Gram matrix of `n + 1` rail steps is
`δ_{BB'} δ_{qq'} Π_t 1/(2B_{t+1} + 1)` when the rails agree and all vertices are admissible, and `0`
otherwise (doubled units). -/
theorem gramB_eq (B B' C : ℕ → ℕ) (h0 : B 0 = B' 0) (n : ℕ) (q q' : ℤ) :
    gramB B B' C (n + 1) q q' =
      if (∀ t ≤ n + 1, B t = B' t) ∧ (∀ t ≤ n, Tri (B t) (C t) (B (t + 1))) ∧ q = q' ∧
          AdmProj (B (n + 1)) q then
        ∏ t ∈ range (n + 1), 1 / ((B (t + 1) : ℝ) + 1)
      else 0 := by
  induction n generalizing q q' with
  | zero =>
    rw [gramB_succ_eq, ← h0]
    have hΓ : ∀ m m', AdmProj (B 0) m → AdmProj (B 0) m' →
        gramB B B' C 0 m m' = if m = m' then 1 else 0 := by
      intro m m' hm hm'
      unfold gramB
      simp only [chainBox, chainB, sum_singleton, pointFn]
      obtain ⟨h1, h2, -⟩ := hm
      rw [sum_eq_single m]
      · by_cases h : m = m' <;> simp [h, Ne.symm]
      · intro β _ hβ; simp [Ne.symm hβ]
      · intro h; exact absurd (mem_Icc.mpr ⟨h1, h2⟩) h
    rw [sum_orth_step (B 0) (B 1) (B' 1) (C 0) _ 1 hΓ]
    simp only [zero_add, range_one, prod_singleton]
    by_cases hc : B 1 = B' 1 ∧ q = q' ∧ Tri (B 0) (C 0) (B 1) ∧ AdmProj (B 1) q
    · rw [ite_eq_left hc, ite_eq_left ⟨fun t ht => by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
        · exact h0
        · exact hc.1, fun t ht => by rw [Nat.le_zero.mp ht]; exact hc.2.2.1, hc.2.1, hc.2.2.2⟩]
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1 1 le_rfl, h.2.2.1, h.2.1 0 le_rfl,
        h.2.2.2⟩)]
  | succ n ih =>
    rw [gramB_succ_eq]
    by_cases hG : (∀ t ≤ n + 1, B t = B' t) ∧ (∀ t ≤ n, Tri (B t) (C t) (B (t + 1)))
    · have hB : B' (n + 1) = B (n + 1) := (hG.1 (n + 1) le_rfl).symm
      rw [hB]
      have hΓ : ∀ m m', AdmProj (B (n + 1)) m → AdmProj (B (n + 1)) m' →
          gramB B B' C (n + 1) m m' = if m = m' then ∏ t ∈ range (n + 1), 1 / ((B (t + 1) : ℝ) + 1)
            else 0 := by
        intro m m' hm _
        rw [ih]
        by_cases h : m = m'
        · rw [ite_eq_left ⟨hG.1, hG.2, h, hm⟩, ite_eq_left h]
        · rw [ite_eq_right (fun h' => h h'.2.2.1), ite_eq_right h]
      rw [sum_orth_step (B (n + 1)) (B (n + 2)) (B' (n + 2)) (C (n + 1)) _ _ hΓ]
      by_cases hc : B (n + 2) = B' (n + 2) ∧ q = q' ∧ Tri (B (n + 1)) (C (n + 1)) (B (n + 2)) ∧
          AdmProj (B (n + 2)) q
      · rw [ite_eq_left hc, ite_eq_left ⟨fun t ht => by
          rcases Nat.lt_or_ge t (n + 2) with h | h
          · exact hG.1 t (by omega)
          · rw [show t = n + 2 by omega]; exact hc.1,
          fun t ht => by
            rcases Nat.lt_or_ge t (n + 1) with h | h
            · exact hG.2 t (by omega)
            · rw [show t = n + 1 by omega]; exact hc.2.2.1, hc.2.1, hc.2.2.2⟩]
        rw [prod_range_succ _ (n + 1)]
        ring
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1 (n + 2) le_rfl, h.2.2.1,
          h.2.1 (n + 1) le_rfl, h.2.2.2⟩)]
    · have h0' : ∀ m m', gramB B B' C (n + 1) m m' = 0 := fun m m' => by
        rw [ih, ite_eq_right (fun h => hG ⟨h.1, h.2.1⟩)]
      simp only [h0', zero_mul, sum_const_zero]
      rw [ite_eq_right (fun h => hG ⟨fun t ht => h.1 t (by omega), fun t ht => h.2.1 t (by omega)⟩)]

/-! ## The 15j symbols as recoupling coefficients: orthogonality -/

/-- The rail `x₀, x₁, x₂, x₃, x₄, x₅` (constant `x₅` from `5` on). -/
def rail6 (x0 x1 x2 x3 x4 x5 : ℕ) : ℕ → ℕ
  | 0 => x0
  | 1 => x1
  | 2 => x2
  | 3 => x3
  | 4 => x4
  | _ => x5

/-- The contraction of the first rail (end spin `J`, end projection `M`) with the second rail of a
Möbius ladder, started at the projection `β` of `b₀`, is the open ladder: zero unless `J = b₀` and
`M = β`, and then `1/(b₀ + 1)` times the closed ladder. -/
lemma ctrA_chainB (a0 x1 x2 x3 x4 J b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 : ℕ) {β : ℤ}
    (hβ : AdmProj b0 β) (M : ℤ) :
    ctrA (rail6 a0 x1 x2 x3 x4 J) (rail6 c0 c1 c2 c3 c4 0) 5
        (fun α h => chainB (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) β 5 h α) M =
      if J = b0 ∧ M = β then
        mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) /
          ((b0 : ℝ) + 1)
      else 0 := by
  have h := ladder_open 4 (rail6 a0 x1 x2 x3 x4 J) (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0)
    rfl hβ M
  simp only [ladder_factor] at h
  unfold ctrA
  refine h.trans ?_
  by_cases hc : J = b0 ∧ M = β
  · obtain ⟨rfl, rfl⟩ := hc
    rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_left ⟨rfl, rfl⟩, mobius_eq 4 _ _ _ rfl rfl]
    rfl
  · rw [ite_eq_right (show ¬(rail6 a0 x1 x2 x3 x4 J (4 + 1) = rail6 b0 b1 b2 b3 b4 a0 0 ∧ M = β)
      from hc), ite_eq_right hc]

/-- All rung projections of `h` are admissible. -/
def ChainAdm (C : ℕ → ℕ) : (n : ℕ) → ChainIdx n → Prop
  | 0, _ => True
  | n + 1, h => ChainAdm C n h.1 ∧ AdmProj (C n) h.2

/-- The second rail vanishes at inadmissible rung projections. -/
lemma chainB_eq_zero_of_not_adm (B C : ℕ → ℕ) (β : ℤ) (n : ℕ) (h : ChainIdx n)
    (hh : ¬ChainAdm C n h) (m : ℤ) : chainB B C β n h m = 0 := by
  induction n generalizing m with
  | zero => exact absurd trivial hh
  | succ n ih =>
    simp only [chainB]
    by_cases hc : AdmProj (C n) h.2
    · have h1 : ¬ChainAdm C n h.1 := fun h' => hh ⟨h', hc⟩
      rw [railStep_zero (fun m' => ih h.1 h1 m'), mul_zero]
    · rw [railStep_eq_zero_of_rung (fun h' => hc (by
        obtain ⟨h1, h2, h3⟩ := h'; exact ⟨by omega, by omega, by omega⟩)), mul_zero]

/-- The second rail of `n + 1` steps vanishes at an inadmissible end projection. -/
lemma chainB_eq_zero_of_end (B C : ℕ → ℕ) (β : ℤ) (n : ℕ) (h : ChainIdx (n + 1)) {m : ℤ}
    (hm : ¬AdmProj (B (n + 1)) m) : chainB B C β (n + 1) h m = 0 := by
  simp only [chainB]
  rw [railStep_eq_zero hm, mul_zero]

/-- A contraction of length `n + 1` vanishes at an inadmissible end projection. -/
lemma ctrA_eq_zero_of_end (A C : ℕ → ℕ) (n : ℕ) (F : ℤ → ChainIdx (n + 1) → ℝ) {m : ℤ}
    (hm : ¬AdmProj (A (n + 1)) m) : ctrA A C (n + 1) F m = 0 := by
  unfold ctrA
  refine sum_eq_zero fun α _ => sum_eq_zero fun h _ => ?_
  simp only [chainA]
  rw [railStep_eq_zero hm, zero_mul]

/-- A weighted sum moved inside one spectator sum. -/
lemma sum_swap1 {ι κ : Type*} (X : Finset ℕ) (w : ℕ → ℝ) (S : Finset ι) (T : ℕ → Finset κ)
    (f : ℕ → ι → κ → ℝ) :
    ∑ x ∈ X, w x * ∑ c ∈ S, ∑ m ∈ T x, f x c m = ∑ c ∈ S, ∑ x ∈ X, ∑ m ∈ T x, w x * f x c m := by
  simp only [mul_sum]
  rw [sum_comm]

/-- A weighted sum moved inside two spectator sums. -/
lemma sum_swap2 {ι₁ ι₂ κ : Type*} (X : Finset ℕ) (w : ℕ → ℝ) (S₁ : Finset ι₁) (S₂ : Finset ι₂)
    (T : ℕ → Finset κ) (f : ℕ → ι₁ → ι₂ → κ → ℝ) :
    ∑ x ∈ X, w x * ∑ c ∈ S₁, ∑ d ∈ S₂, ∑ m ∈ T x, f x c d m =
      ∑ c ∈ S₁, ∑ d ∈ S₂, ∑ x ∈ X, ∑ m ∈ T x, w x * f x c d m := by
  rw [sum_swap1]
  refine sum_congr rfl fun c _ => ?_
  simp only [mul_sum]
  rw [sum_comm]

/-- A weighted sum moved inside three spectator sums. -/
lemma sum_swap3 {ι₁ ι₂ ι₃ κ : Type*} (X : Finset ℕ) (w : ℕ → ℝ) (S₁ : Finset ι₁)
    (S₂ : Finset ι₂) (S₃ : Finset ι₃) (T : ℕ → Finset κ) (f : ℕ → ι₁ → ι₂ → ι₃ → κ → ℝ) :
    ∑ x ∈ X, w x * ∑ c ∈ S₁, ∑ d ∈ S₂, ∑ e ∈ S₃, ∑ m ∈ T x, f x c d e m =
      ∑ c ∈ S₁, ∑ d ∈ S₂, ∑ e ∈ S₃, ∑ x ∈ X, ∑ m ∈ T x, w x * f x c d e m := by
  rw [sum_swap2]
  refine sum_congr rfl fun c _ => sum_congr rfl fun d _ => ?_
  simp only [mul_sum]
  rw [sum_comm]

/-- A weighted sum moved inside four spectator sums. -/
lemma sum_swap4 {ι₁ ι₂ ι₃ ι₄ κ : Type*} (X : Finset ℕ) (w : ℕ → ℝ) (S₁ : Finset ι₁)
    (S₂ : Finset ι₂) (S₃ : Finset ι₃) (S₄ : Finset ι₄) (T : ℕ → Finset κ)
    (f : ℕ → ι₁ → ι₂ → ι₃ → ι₄ → κ → ℝ) :
    ∑ x ∈ X, w x * ∑ c ∈ S₁, ∑ d ∈ S₂, ∑ e ∈ S₃, ∑ g ∈ S₄, ∑ m ∈ T x, f x c d e g m =
      ∑ c ∈ S₁, ∑ d ∈ S₂, ∑ e ∈ S₃, ∑ g ∈ S₄, ∑ x ∈ X, ∑ m ∈ T x, w x * f x c d e g m := by
  rw [sum_swap3]
  refine sum_congr rfl fun c _ => sum_congr rfl fun d _ => sum_congr rfl fun e _ => ?_
  simp only [mul_sum]
  rw [sum_comm]

/-- A contraction of length `0` is the function itself. -/
lemma ctrA_zero (A C : ℕ → ℕ) (F : ℤ → ChainIdx 0 → ℝ) {m : ℤ} (hm : m ∈ Icc (-(A 0 : ℤ)) (A 0)) :
    ctrA A C 0 F m = F m () := by
  unfold ctrA
  simp only [chainA, pointFn]
  rw [sum_eq_single m]
  · rw [show chainBox C 0 = {()} from rfl, sum_singleton, ite_eq_left rfl, one_mul]
  · intro α _ hα
    exact sum_eq_zero fun h _ => by rw [ite_eq_right (Ne.symm hα), zero_mul]
  · intro h; exact absurd hm h

set_option maxHeartbeats 4000000 in
/-- **Completeness of the first rails** (a Parseval identity): summed over the four inner spins
`x₁ … x₄`, the end spin `J` and its projection, with weights `Π (2x + 1)`, two contractions of the
first rail give the plain inner product of the contracted functions. The functions must vanish at
inadmissible start and rung projections. -/
theorem ctrA_parseval (a0 c0 c1 c2 c3 c4 : ℕ) (F G : ℤ → ChainIdx 5 → ℝ)
    (hFα : ∀ α h, ¬AdmProj a0 α → F α h = 0)
    (hFc : ∀ α h, ¬ChainAdm (rail6 c0 c1 c2 c3 c4 0) 5 h → F α h = 0) :
    ∑ x1 ∈ range (a0 + c0 + 1), ((x1 : ℝ) + 1) * ∑ x2 ∈ range (x1 + c1 + 1), ((x2 : ℝ) + 1) *
      ∑ x3 ∈ range (x2 + c2 + 1), ((x3 : ℝ) + 1) * ∑ x4 ∈ range (x3 + c3 + 1), ((x4 : ℝ) + 1) *
        ∑ J ∈ range (x4 + c4 + 1), ∑ M ∈ Icc (-(J : ℤ)) J, ((J : ℝ) + 1) *
          (ctrA (rail6 a0 x1 x2 x3 x4 J) (rail6 c0 c1 c2 c3 c4 0) 5 F M * ctrA (rail6 a0 x1 x2 x3 x4 J) (rail6 c0 c1 c2 c3 c4 0) 5 G M) =
    ∑ k4 ∈ Icc (-(c4 : ℤ)) c4, ∑ k3 ∈ Icc (-(c3 : ℤ)) c3, ∑ k2 ∈ Icc (-(c2 : ℤ)) c2, ∑ k1 ∈ Icc (-(c1 : ℤ)) c1, ∑ k0 ∈ Icc (-(c0 : ℤ)) c0,
      ∑ m ∈ Icc (-(a0 : ℤ)) a0, F m ((((((), k0), k1), k2), k3), k4) * G m ((((((), k0), k1), k2), k3), k4) := by
  have H5 : ∀ x1 x2 x3 x4 : ℕ, ∑ J ∈ range (x4 + c4 + 1), ∑ M ∈ Icc (-(J : ℤ)) J, ((J : ℝ) + 1) *
      (ctrA (rail6 a0 x1 x2 x3 x4 J) (rail6 c0 c1 c2 c3 c4 0) 5 F M * ctrA (rail6 a0 x1 x2 x3 x4 J) (rail6 c0 c1 c2 c3 c4 0) 5 G M) =
      ∑ k4 ∈ Icc (-(c4 : ℤ)) c4, ∑ m ∈ Icc (-(x4 : ℤ)) x4,
        ctrA (rail6 a0 x1 x2 x3 x4 0) (rail6 c0 c1 c2 c3 c4 0) 4 (fun α g => F α (g, k4)) m *
          ctrA (rail6 a0 x1 x2 x3 x4 0) (rail6 c0 c1 c2 c3 c4 0) 4 (fun α g => G α (g, k4)) m := fun x1 x2 x3 x4 =>
    ctrA_complete_step (rail6 a0 x1 x2 x3 x4 0) (rail6 c0 c1 c2 c3 c4 0) (fun J => rail6 a0 x1 x2 x3 x4 J) 4
      (fun J => rfl) (fun J t ht => by interval_cases t <;> rfl) F G (fun m c hmc => by
        by_cases hm : AdmProj x4 m
        · have hc : ¬AdmProj c4 c := fun hc => hmc ⟨hm, hc⟩
          unfold ctrA
          refine sum_eq_zero fun α _ => sum_eq_zero fun g _ => ?_
          beta_reduce
          rw [hFc α (g, c) (fun h => hc h.2), mul_zero]
        · exact ctrA_eq_zero_of_end _ _ 3 _ hm)
  have H4 : ∀ (x1 x2 x3 : ℕ) (k4 : ℤ), ∑ x4 ∈ range (x3 + c3 + 1), ∑ m ∈ Icc (-(x4 : ℤ)) x4, ((x4 : ℝ) + 1) *
      (ctrA (rail6 a0 x1 x2 x3 x4 0) (rail6 c0 c1 c2 c3 c4 0) 4 (fun α g => F α (g, k4)) m *
        ctrA (rail6 a0 x1 x2 x3 x4 0) (rail6 c0 c1 c2 c3 c4 0) 4 (fun α g => G α (g, k4)) m) =
      ∑ k3 ∈ Icc (-(c3 : ℤ)) c3, ∑ m ∈ Icc (-(x3 : ℤ)) x3,
        ctrA (rail6 a0 x1 x2 x3 0 0) (rail6 c0 c1 c2 c3 c4 0) 3 (fun α g => F α ((g, k3), k4)) m *
          ctrA (rail6 a0 x1 x2 x3 0 0) (rail6 c0 c1 c2 c3 c4 0) 3 (fun α g => G α ((g, k3), k4)) m := fun x1 x2 x3 k4 =>
    ctrA_complete_step (rail6 a0 x1 x2 x3 0 0) (rail6 c0 c1 c2 c3 c4 0) (fun J => rail6 a0 x1 x2 x3 J 0) 3
      (fun J => rfl) (fun J t ht => by interval_cases t <;> rfl) _ _ (fun m c hmc => by
        by_cases hm : AdmProj x3 m
        · have hc : ¬AdmProj c3 c := fun hc => hmc ⟨hm, hc⟩
          unfold ctrA
          refine sum_eq_zero fun α _ => sum_eq_zero fun g _ => ?_
          beta_reduce
          rw [hFc α ((g, c), k4) (fun h => hc h.1.2), mul_zero]
        · exact ctrA_eq_zero_of_end _ _ 2 _ hm)
  have H3 : ∀ (x1 x2 : ℕ) (k4 k3 : ℤ), ∑ x3 ∈ range (x2 + c2 + 1), ∑ m ∈ Icc (-(x3 : ℤ)) x3, ((x3 : ℝ) + 1) *
      (ctrA (rail6 a0 x1 x2 x3 0 0) (rail6 c0 c1 c2 c3 c4 0) 3 (fun α g => F α ((g, k3), k4)) m *
        ctrA (rail6 a0 x1 x2 x3 0 0) (rail6 c0 c1 c2 c3 c4 0) 3 (fun α g => G α ((g, k3), k4)) m) =
      ∑ k2 ∈ Icc (-(c2 : ℤ)) c2, ∑ m ∈ Icc (-(x2 : ℤ)) x2,
        ctrA (rail6 a0 x1 x2 0 0 0) (rail6 c0 c1 c2 c3 c4 0) 2 (fun α g => F α (((g, k2), k3), k4)) m *
          ctrA (rail6 a0 x1 x2 0 0 0) (rail6 c0 c1 c2 c3 c4 0) 2 (fun α g => G α (((g, k2), k3), k4)) m :=
    fun x1 x2 k4 k3 =>
    ctrA_complete_step (rail6 a0 x1 x2 0 0 0) (rail6 c0 c1 c2 c3 c4 0) (fun J => rail6 a0 x1 x2 J 0 0) 2
      (fun J => rfl) (fun J t ht => by interval_cases t <;> rfl) _ _ (fun m c hmc => by
        by_cases hm : AdmProj x2 m
        · have hc : ¬AdmProj c2 c := fun hc => hmc ⟨hm, hc⟩
          unfold ctrA
          refine sum_eq_zero fun α _ => sum_eq_zero fun g _ => ?_
          beta_reduce
          rw [hFc α (((g, c), k3), k4) (fun h => hc h.1.1.2), mul_zero]
        · exact ctrA_eq_zero_of_end _ _ 1 _ hm)
  have H2 : ∀ (x1 : ℕ) (k4 k3 k2 : ℤ), ∑ x2 ∈ range (x1 + c1 + 1), ∑ m ∈ Icc (-(x2 : ℤ)) x2, ((x2 : ℝ) + 1) *
      (ctrA (rail6 a0 x1 x2 0 0 0) (rail6 c0 c1 c2 c3 c4 0) 2 (fun α g => F α (((g, k2), k3), k4)) m *
        ctrA (rail6 a0 x1 x2 0 0 0) (rail6 c0 c1 c2 c3 c4 0) 2 (fun α g => G α (((g, k2), k3), k4)) m) =
      ∑ k1 ∈ Icc (-(c1 : ℤ)) c1, ∑ m ∈ Icc (-(x1 : ℤ)) x1,
        ctrA (rail6 a0 x1 0 0 0 0) (rail6 c0 c1 c2 c3 c4 0) 1 (fun α g => F α ((((g, k1), k2), k3), k4)) m *
          ctrA (rail6 a0 x1 0 0 0 0) (rail6 c0 c1 c2 c3 c4 0) 1 (fun α g => G α ((((g, k1), k2), k3), k4)) m :=
    fun x1 k4 k3 k2 =>
    ctrA_complete_step (rail6 a0 x1 0 0 0 0) (rail6 c0 c1 c2 c3 c4 0) (fun J => rail6 a0 x1 J 0 0 0) 1
      (fun J => rfl) (fun J t ht => by interval_cases t <;> rfl) _ _ (fun m c hmc => by
        by_cases hm : AdmProj x1 m
        · have hc : ¬AdmProj c1 c := fun hc => hmc ⟨hm, hc⟩
          unfold ctrA
          refine sum_eq_zero fun α _ => sum_eq_zero fun g _ => ?_
          beta_reduce
          rw [hFc α ((((g, c), k2), k3), k4) (fun h => hc h.1.1.1.2), mul_zero]
        · exact ctrA_eq_zero_of_end _ _ 0 _ hm)
  have H1 : ∀ (k4 k3 k2 k1 : ℤ), ∑ x1 ∈ range (a0 + c0 + 1), ∑ m ∈ Icc (-(x1 : ℤ)) x1, ((x1 : ℝ) + 1) *
      (ctrA (rail6 a0 x1 0 0 0 0) (rail6 c0 c1 c2 c3 c4 0) 1 (fun α g => F α ((((g, k1), k2), k3), k4)) m *
        ctrA (rail6 a0 x1 0 0 0 0) (rail6 c0 c1 c2 c3 c4 0) 1 (fun α g => G α ((((g, k1), k2), k3), k4)) m) =
      ∑ k0 ∈ Icc (-(c0 : ℤ)) c0, ∑ m ∈ Icc (-(a0 : ℤ)) a0,
        ctrA (rail6 a0 0 0 0 0 0) (rail6 c0 c1 c2 c3 c4 0) 0 (fun α g => F α (((((g, k0), k1), k2), k3), k4)) m *
          ctrA (rail6 a0 0 0 0 0 0) (rail6 c0 c1 c2 c3 c4 0) 0 (fun α g => G α (((((g, k0), k1), k2), k3), k4)) m :=
    fun k4 k3 k2 k1 =>
    ctrA_complete_step (rail6 a0 0 0 0 0 0) (rail6 c0 c1 c2 c3 c4 0) (fun J => rail6 a0 J 0 0 0 0) 0
      (fun J => rfl) (fun J t ht => by interval_cases t; rfl) _ _ (fun m c hmc => by
        unfold ctrA
        refine sum_eq_zero fun α _ => sum_eq_zero fun g _ => ?_
        beta_reduce
        simp only [chainA, pointFn]
        by_cases hmα : m = α
        · subst hmα
          by_cases hm : AdmProj a0 m
          · have hc : ¬AdmProj c0 c := fun hc => hmc ⟨hm, hc⟩
            rw [hFc m (((((g, c), k1), k2), k3), k4) (fun h => hc h.1.1.1.1.2), mul_zero]
          · rw [hFα m _ hm, mul_zero]
        · rw [ite_eq_right hmα, zero_mul])
  rw [sum_congr rfl fun x1 _ => congrArg _ <| sum_congr rfl fun x2 _ => congrArg _ <|
    sum_congr rfl fun x3 _ => congrArg _ <| sum_congr rfl fun x4 _ => congrArg _ (H5 x1 x2 x3 x4)]
  rw [sum_congr rfl fun x1 _ => congrArg _ <| sum_congr rfl fun x2 _ => congrArg _ <|
    sum_congr rfl fun x3 _ => congrArg _ <| (sum_swap1 _ _ _ _ _).trans
      (sum_congr rfl fun k4 _ => H4 x1 x2 x3 k4)]
  rw [sum_congr rfl fun x1 _ => congrArg _ <| sum_congr rfl fun x2 _ => congrArg _ <|
    (sum_swap2 _ _ _ _ _ _).trans (sum_congr rfl fun k4 _ => sum_congr rfl fun k3 _ =>
      H3 x1 x2 k4 k3)]
  rw [sum_congr rfl fun x1 _ => congrArg _ <| (sum_swap3 _ _ _ _ _ _ _).trans
    (sum_congr rfl fun k4 _ => sum_congr rfl fun k3 _ => sum_congr rfl fun k2 _ => H2 x1 k4 k3 k2)]
  rw [sum_swap4]
  refine sum_congr rfl fun k4 _ => sum_congr rfl fun k3 _ => sum_congr rfl fun k2 _ =>
    sum_congr rfl fun k1 _ => ?_
  rw [H1 k4 k3 k2 k1]
  refine sum_congr rfl fun k0 _ => sum_congr rfl fun m hm => ?_
  rw [ctrA_zero _ _ _ hm, ctrA_zero _ _ _ hm]

/-- There are `j + 1` admissible projections of a doubled spin `j`. -/
lemma sum_admProj (j : ℕ) : ∑ μ ∈ Icc (-(j : ℤ)) j, (if AdmProj j μ then (1 : ℝ) else 0) = j + 1 := by
  rw [sum_Icc_parity j _ (fun μ hμ => ite_eq_right (fun h => hμ h.2.2))]
  have h1 : ∀ α ∈ range (j + 1), (if AdmProj j ((j : ℤ) - 2 * (α : ℤ)) then (1 : ℝ) else 0) = 1 :=
    fun α hα => ite_eq_left (by simp only [mem_range] at hα; exact ⟨by omega, by omega, by omega⟩)
  rw [sum_congr rfl h1]
  simp

/-- The second rail vanishes from an inadmissible start projection. -/
lemma chainB_eq_zero_of_start (B C : ℕ → ℕ) {β : ℤ} (hβ : ¬AdmProj (B 0) β) (n : ℕ)
    (h : ChainIdx (n + 1)) (m : ℤ) : chainB B C β (n + 1) h m = 0 := by
  induction n generalizing m with
  | zero =>
    simp only [chainB, railStep, pointFn]
    rw [sum_eq_zero fun m' _ => ?_, mul_zero]
    by_cases hm : m' = β
    · subst hm
      rw [threeJ_of_not (fun h' => hβ (by
        obtain ⟨-, h1, h2, -, -, -, -, h7, -⟩ := h'; exact ⟨by omega, by omega, by omega⟩)), mul_zero]
    · rw [ite_eq_right hm, zero_mul, zero_mul]
  | succ n ih =>
    show edgeSign (C (n + 1)) h.2 * railStep (B (n + 1)) (B (n + 1 + 1)) (C (n + 1)) (-h.2)
      (chainB B C β (n + 1) h.1) m = 0
    rw [railStep_zero (fun m' => ih h.1 m'), mul_zero]

/-- The closed ladder of the 15j symbol vanishes when its last vertex `(x₄ b₀ c₄)` is not a
triad. -/
lemma mobius_rail6_eq_zero (a0 x1 x2 x3 x4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 : ℕ)
    (h : ¬b0 ≤ x4 + c4) :
    mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) = 0 := by
  rw [mobius_eq 4 _ _ _ rfl rfl]
  refine sum_eq_zero fun x _ => ?_
  rw [prod_range_succ]
  have h6 : sixJSym x4 b4 x a0 b0 c4 = 0 := by
    by_contra h'
    obtain ⟨-, ⟨-, -, -, t⟩, -⟩ := tri_of_sixJSym_ne_zero h'
    exact h t
  simp only [rungFactor]
  rw [show sixJSym (rail6 a0 x1 x2 x3 x4 b0 4) (rail6 b0 b1 b2 b3 b4 a0 4) x
    (rail6 b0 b1 b2 b3 b4 a0 (4 + 1)) (rail6 a0 x1 x2 x3 x4 b0 (4 + 1)) (rail6 c0 c1 c2 c3 c4 0 4) =
    sixJSym x4 b4 x a0 b0 c4 from rfl, h6]
  ring

/-- The sum over the end spin and its projection in the Parseval identity, for the contractions
with the second rails of two ladders. -/
lemma sum_JM_ctrA_chainB (a0 x1 x2 x3 x4 b0 b1 b2 b3 b4 b1' b2' b3' b4' c0 c1 c2 c3 c4 : ℕ)
    {β : ℤ} (hβ : AdmProj b0 β) :
    ∑ J ∈ range (x4 + c4 + 1), ∑ M ∈ Icc (-(J : ℤ)) J, ((J : ℝ) + 1) *
      (ctrA (rail6 a0 x1 x2 x3 x4 J) (rail6 c0 c1 c2 c3 c4 0) 5
          (fun α h => chainB (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) β 5 h α) M *
        ctrA (rail6 a0 x1 x2 x3 x4 J) (rail6 c0 c1 c2 c3 c4 0) 5
          (fun α h => chainB (rail6 b0 b1' b2' b3' b4' a0) (rail6 c0 c1 c2 c3 c4 0) β 5 h α) M) =
    mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) *
      mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1' b2' b3' b4' a0) (rail6 c0 c1 c2 c3 c4 0) /
        ((b0 : ℝ) + 1) := by
  simp only [ctrA_chainB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hβ]
  have hb1 : ((b0 : ℝ) + 1) ≠ 0 := by positivity
  by_cases hb : b0 ≤ x4 + c4
  · rw [sum_eq_single b0 (fun J _ hJ => sum_eq_zero fun M _ => by
        rw [ite_eq_right (fun h => hJ h.1), zero_mul, mul_zero])
      (fun h => absurd (mem_range.mpr (by omega)) h)]
    obtain ⟨h1, h2, -⟩ := hβ
    rw [sum_eq_single β (fun M _ hM => by rw [ite_eq_right (fun h => hM h.2), zero_mul, mul_zero])
      (fun h => absurd (mem_Icc.mpr ⟨h1, h2⟩) h), ite_eq_left ⟨rfl, rfl⟩, ite_eq_left ⟨rfl, rfl⟩]
    field_simp
  · rw [mobius_rail6_eq_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb, zero_mul, zero_div]
    refine sum_eq_zero fun J hJ => sum_eq_zero fun M _ => ?_
    have : J ≠ b0 := fun h => hb (by simp only [mem_range] at hJ; omega)
    rw [ite_eq_right (fun h => this h.1), zero_mul, mul_zero]

set_option maxHeartbeats 4000000 in
/-- For an admissible start projection `β` of `b₀`: the weighted sum over the inner spins `x₁ … x₄`
of the first rail of two closed ladders (second rails `b`, `b'`), divided by `2b₀ + 1`, is the
inner product of the two second rails. -/
lemma sum_mobius_beta (a0 b0 b1 b2 b3 b4 b1' b2' b3' b4' c0 c1 c2 c3 c4 : ℕ) {β : ℤ}
    (hβ : AdmProj b0 β) :
    ∑ x1 ∈ range (a0 + c0 + 1), ((x1 : ℝ) + 1) * ∑ x2 ∈ range (x1 + c1 + 1), ((x2 : ℝ) + 1) *
      ∑ x3 ∈ range (x2 + c2 + 1), ((x3 : ℝ) + 1) * ∑ x4 ∈ range (x3 + c3 + 1), ((x4 : ℝ) + 1) *
        (mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) *
          mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1' b2' b3' b4' a0) (rail6 c0 c1 c2 c3 c4 0) /
            ((b0 : ℝ) + 1)) =
    ∑ k4 ∈ Icc (-(c4 : ℤ)) c4, ∑ k3 ∈ Icc (-(c3 : ℤ)) c3, ∑ k2 ∈ Icc (-(c2 : ℤ)) c2,
      ∑ k1 ∈ Icc (-(c1 : ℤ)) c1, ∑ k0 ∈ Icc (-(c0 : ℤ)) c0, ∑ m ∈ Icc (-(a0 : ℤ)) a0,
        chainB (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) β 5 ((((((), k0), k1), k2), k3), k4) m *
          chainB (rail6 b0 b1' b2' b3' b4' a0) (rail6 c0 c1 c2 c3 c4 0) β 5
            ((((((), k0), k1), k2), k3), k4) m := by
  have hP := ctrA_parseval a0 c0 c1 c2 c3 c4
    (fun α h => chainB (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) β 5 h α)
    (fun α h => chainB (rail6 b0 b1' b2' b3' b4' a0) (rail6 c0 c1 c2 c3 c4 0) β 5 h α)
    (fun α h hα => chainB_eq_zero_of_end _ _ β 4 h hα)
    (fun α h hh => chainB_eq_zero_of_not_adm _ _ β 5 h hh α)
  simp only [sum_JM_ctrA_chainB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hβ] at hP
  exact hP

/-- Reversing the order of five nested finite sums. -/
lemma sum_five_rev {α β γ δ ε : Type*} (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (E : Finset ε) (f : α → β → γ → δ → ε → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, f a b c d e =
      ∑ e ∈ E, ∑ d ∈ D, ∑ c ∈ C, ∑ b ∈ B, ∑ a ∈ A, f a b c d e := by
  simp only [sum_comm (s := D) (t := E), sum_comm (s := C) (t := E), sum_comm (s := B) (t := E),
    sum_comm (s := A) (t := E)]
  refine sum_congr rfl fun e _ => ?_
  exact sum_four_rev A B C D (fun a b c d => f a b c d e)

/-- Moving an outer finite sum inside five others. -/
lemma sum_move_in5 {μ α β γ δ ε : Type*} (M : Finset μ) (A : Finset α) (B : Finset β)
    (C : Finset γ) (D : Finset δ) (E : Finset ε) (f : μ → α → β → γ → δ → ε → ℝ) :
    ∑ m ∈ M, ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, f m a b c d e =
      ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, ∑ m ∈ M, f m a b c d e := by
  simp only [sum_comm (s := M) (t := A), sum_comm (s := M) (t := B), sum_comm (s := M) (t := C),
    sum_comm (s := M) (t := D), sum_comm (s := M) (t := E)]

/-- A sum over the rung projections of five rungs, written out. -/
lemma sum_chainBox_five (C : ℕ → ℕ) (f : ChainIdx (4 + 1) → ℝ) :
    ∑ h ∈ chainBox C (4 + 1), f h =
      ∑ k4 ∈ Icc (-(C 4 : ℤ)) (C 4), ∑ k3 ∈ Icc (-(C 3 : ℤ)) (C 3), ∑ k2 ∈ Icc (-(C 2 : ℤ)) (C 2),
        ∑ k1 ∈ Icc (-(C 1 : ℤ)) (C 1), ∑ k0 ∈ Icc (-(C 0 : ℤ)) (C 0),
          f ((((((), k0), k1), k2), k3), k4) := by
  simp only [chainBox, sum_product]
  rw [show ({()} : Finset Unit) = {()} from rfl, sum_singleton]
  exact sum_five_rev _ _ _ _ _ _

/-- The conditions of `gramB_eq` for the second rails of the 15j symbol, written out. -/
lemma rail6_conds (a0 b0 b1 b2 b3 b4 b1' b2' b3' b4' c0 c1 c2 c3 c4 : ℕ) :
    ((∀ t ≤ 4 + 1, rail6 b0 b1 b2 b3 b4 a0 t = rail6 b0 b1' b2' b3' b4' a0 t) ∧
      ∀ t ≤ 4, Tri (rail6 b0 b1 b2 b3 b4 a0 t) (rail6 c0 c1 c2 c3 c4 0 t)
        (rail6 b0 b1 b2 b3 b4 a0 (t + 1))) ↔
    (b1 = b1' ∧ b2 = b2' ∧ b3 = b3' ∧ b4 = b4') ∧ Tri b0 c0 b1 ∧ Tri b1 c1 b2 ∧ Tri b2 c2 b3 ∧
      Tri b3 c3 b4 ∧ Tri b4 c4 a0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1 1 (by omega), h1 2 (by omega), h1 3 (by omega), h1 4 (by omega)⟩,
      h2 0 (by omega), h2 1 (by omega), h2 2 (by omega), h2 3 (by omega), h2 4 (by omega)⟩
  · rintro ⟨⟨e1, e2, e3, e4⟩, t0, t1, t2, t3, t4⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · interval_cases t <;> simp [rail6, e1, e2, e3, e4]
    · interval_cases t <;> assumption

set_option maxHeartbeats 4000000 in
/-- **Orthogonality of the Möbius ladders of the 15j symbol** (doubled units): summed over the inner
spins `x₁ … x₄` of the first rail with weights `Π (2x + 1)`, the product of two closed ladders with
second rails `b` and `b'` is `δ_{bb'} / Π_{t=1}^{4} (2b_t + 1)` when the second rail's vertices are
admissible, and `0` otherwise. -/
theorem sum_mobius_mul_mobius (a0 b0 b1 b2 b3 b4 b1' b2' b3' b4' c0 c1 c2 c3 c4 : ℕ) :
    ∑ x1 ∈ range (a0 + c0 + 1), ((x1 : ℝ) + 1) * ∑ x2 ∈ range (x1 + c1 + 1), ((x2 : ℝ) + 1) *
      ∑ x3 ∈ range (x2 + c2 + 1), ((x3 : ℝ) + 1) * ∑ x4 ∈ range (x3 + c3 + 1), ((x4 : ℝ) + 1) *
        (mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) *
          mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1' b2' b3' b4' a0) (rail6 c0 c1 c2 c3 c4 0)) =
    if (b1 = b1' ∧ b2 = b2' ∧ b3 = b3' ∧ b4 = b4') ∧ Tri b0 c0 b1 ∧ Tri b1 c1 b2 ∧ Tri b2 c2 b3 ∧
        Tri b3 c3 b4 ∧ Tri b4 c4 a0 then
      1 / (((b1 : ℝ) + 1) * ((b2 : ℝ) + 1) * ((b3 : ℝ) + 1) * ((b4 : ℝ) + 1))
    else 0 := by
  set L := ∑ x1 ∈ range (a0 + c0 + 1), ((x1 : ℝ) + 1) * ∑ x2 ∈ range (x1 + c1 + 1), ((x2 : ℝ) + 1) *
      ∑ x3 ∈ range (x2 + c2 + 1), ((x3 : ℝ) + 1) * ∑ x4 ∈ range (x3 + c3 + 1), ((x4 : ℝ) + 1) *
        (mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) *
          mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1' b2' b3' b4' a0) (rail6 c0 c1 c2 c3 c4 0))
    with hL
  have hb1 : ((b0 : ℝ) + 1) ≠ 0 := by positivity
  -- the division by `2b₀ + 1` comes out of the nested sums
  have hdiv : ∀ d : ℝ, ∑ x1 ∈ range (a0 + c0 + 1), ((x1 : ℝ) + 1) * ∑ x2 ∈ range (x1 + c1 + 1),
      ((x2 : ℝ) + 1) * ∑ x3 ∈ range (x2 + c2 + 1), ((x3 : ℝ) + 1) * ∑ x4 ∈ range (x3 + c3 + 1),
        ((x4 : ℝ) + 1) *
        (mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) *
          mobius 5 (rail6 a0 x1 x2 x3 x4 b0) (rail6 b0 b1' b2' b3' b4' a0) (rail6 c0 c1 c2 c3 c4 0) /
            d) = L / d := by
    intro d
    rw [hL, div_eq_mul_inv]
    simp only [div_eq_mul_inv, mul_sum, sum_mul]
    refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
      sum_congr rfl fun _ _ => ?_
    ring
  -- for every admissible `β`, `L / (2b₀+1)` is the inner product of the second rails
  set R : ℤ → ℝ := fun β => ∑ k4 ∈ Icc (-(c4 : ℤ)) c4, ∑ k3 ∈ Icc (-(c3 : ℤ)) c3,
      ∑ k2 ∈ Icc (-(c2 : ℤ)) c2, ∑ k1 ∈ Icc (-(c1 : ℤ)) c1, ∑ k0 ∈ Icc (-(c0 : ℤ)) c0,
        ∑ m ∈ Icc (-(a0 : ℤ)) a0,
          chainB (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) β 5 ((((((), k0), k1), k2), k3), k4) m *
            chainB (rail6 b0 b1' b2' b3' b4' a0) (rail6 c0 c1 c2 c3 c4 0) β 5
              ((((((), k0), k1), k2), k3), k4) m with hR
  have hβ : ∀ β, AdmProj b0 β → L / ((b0 : ℝ) + 1) = R β := fun β hβ => by
    rw [← hdiv, hR]
    exact sum_mobius_beta a0 b0 b1 b2 b3 b4 b1' b2' b3' b4' c0 c1 c2 c3 c4 hβ
  have hβ0 : ∀ β, ¬AdmProj b0 β → R β = 0 := fun β hβ => by
    rw [hR]
    refine sum_eq_zero fun _ _ => sum_eq_zero fun _ _ => sum_eq_zero fun _ _ =>
      sum_eq_zero fun _ _ => sum_eq_zero fun _ _ => sum_eq_zero fun _ _ => ?_
    rw [chainB_eq_zero_of_start _ _ hβ 4, zero_mul]
  -- summing over `β`
  have hsum : L = ∑ β ∈ Icc (-(b0 : ℤ)) b0, R β := by
    have h1 : ∑ β ∈ Icc (-(b0 : ℤ)) b0, (if AdmProj b0 β then (1 : ℝ) else 0) * (L / ((b0 : ℝ) + 1)) =
        L := by
      rw [← sum_mul, sum_admProj]; field_simp
    rw [← h1]
    refine sum_congr rfl fun β _ => ?_
    by_cases h : AdmProj b0 β
    · rw [ite_eq_left h, one_mul, hβ β h]
    · rw [ite_eq_right h, zero_mul, hβ0 β h]
  -- the inner products are the Gram matrix of the second rails
  have hgram : ∑ β ∈ Icc (-(b0 : ℤ)) b0, R β = ∑ m ∈ Icc (-(a0 : ℤ)) a0,
      gramB (rail6 b0 b1 b2 b3 b4 a0) (rail6 b0 b1' b2' b3' b4' a0) (rail6 c0 c1 c2 c3 c4 0) (4 + 1)
        m m := by
    unfold gramB
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun β _ => ?_
    refine Eq.trans ?_ (sum_congr rfl fun m _ => (sum_chainBox_five (rail6 c0 c1 c2 c3 c4 0)
      (fun h => chainB (rail6 b0 b1 b2 b3 b4 a0) (rail6 c0 c1 c2 c3 c4 0) β (4 + 1) h m *
        chainB (rail6 b0 b1' b2' b3' b4' a0) (rail6 c0 c1 c2 c3 c4 0) β (4 + 1) h m)).symm)
    exact (sum_move_in5 _ _ _ _ _ _ _).symm
  rw [hsum, hgram]
  simp only [gramB_eq (rail6 b0 b1 b2 b3 b4 a0) (rail6 b0 b1' b2' b3' b4' a0)
    (rail6 c0 c1 c2 c3 c4 0) rfl 4]
  have hconds := rail6_conds a0 b0 b1 b2 b3 b4 b1' b2' b3' b4' c0 c1 c2 c3 c4
  by_cases hc : (b1 = b1' ∧ b2 = b2' ∧ b3 = b3' ∧ b4 = b4') ∧ Tri b0 c0 b1 ∧ Tri b1 c1 b2 ∧
      Tri b2 c2 b3 ∧ Tri b3 c3 b4 ∧ Tri b4 c4 a0
  · obtain ⟨g1, g2⟩ := hconds.mpr hc
    rw [ite_eq_left hc]
    have hP : ∏ t ∈ range (4 + 1), 1 / ((rail6 b0 b1 b2 b3 b4 a0 (t + 1) : ℝ) + 1) =
        1 / (((b1 : ℝ) + 1) * ((b2 : ℝ) + 1) * ((b3 : ℝ) + 1) * ((b4 : ℝ) + 1)) * (1 / ((a0 : ℝ) + 1)) := by
      simp only [prod_range_succ, prod_range_zero]
      simp only [rail6]
      field_simp
    simp only [and_iff_right g1, and_iff_right g2, true_and, hP]
    rw [show rail6 b0 b1 b2 b3 b4 a0 (4 + 1) = a0 from rfl]
    have hite : ∀ m : ℤ, (if AdmProj a0 m then 1 / (((b1 : ℝ) + 1) * ((b2 : ℝ) + 1) * ((b3 : ℝ) + 1) *
        ((b4 : ℝ) + 1)) * (1 / ((a0 : ℝ) + 1)) else 0) = (if AdmProj a0 m then (1 : ℝ) else 0) *
          (1 / (((b1 : ℝ) + 1) * ((b2 : ℝ) + 1) * ((b3 : ℝ) + 1) * ((b4 : ℝ) + 1)) *
            (1 / ((a0 : ℝ) + 1))) := fun m => by split_ifs <;> ring
    rw [sum_congr rfl fun m _ => hite m, ← sum_mul, sum_admProj]
    field_simp
  · rw [ite_eq_right hc]
    refine sum_eq_zero fun m _ => ite_eq_right fun h => hc (hconds.mp ⟨h.1, h.2.1⟩)

/-- The rails of `fifteenJ` written as explicit rails. -/
lemma railA_vec (a0 x1 x2 x3 x4 b0 b1 b2 b3 b4 : ℕ) :
    railA ![a0, x1, x2, x3, x4] ![b0, b1, b2, b3, b4] = rail6 a0 x1 x2 x3 x4 b0 := by
  funext t
  rcases t with _ | _ | _ | _ | _ | t <;> rfl

/-- The rails of `fifteenJ` written as explicit rails. -/
lemma railB_vec (a0 x1 x2 x3 x4 b0 b1 b2 b3 b4 : ℕ) :
    railB ![a0, x1, x2, x3, x4] ![b0, b1, b2, b3, b4] = rail6 b0 b1 b2 b3 b4 a0 := by
  funext t
  rcases t with _ | _ | _ | _ | _ | t <;> rfl

/-- The rungs of `fifteenJ` written as explicit rails. -/
lemma railC_vec (c0 c1 c2 c3 c4 : ℕ) :
    railC ![c0, c1, c2, c3, c4] = rail6 c0 c1 c2 c3 c4 0 := by
  funext t
  rcases t with _ | _ | _ | _ | _ | t <;> rfl

/-- **Orthogonality of the 15j symbols of the first kind** (doubled units): for fixed `a₀`, `b₀`
and rungs `c`, summed over the spins `a₁ … a₄` with weights `Π (2a_t + 1)`,
`Σ_a Π(2a+1) {15j}(a, b, c) {15j}(a, b', c) = δ_{bb'} / Π_{t=1}^{4} (2b_t + 1)`
when the vertices `(b₀ c₀ b₁), (b₁ c₁ b₂), (b₂ c₂ b₃), (b₃ c₃ b₄), (b₄ c₄ a₀)` are admissible, and `0`
otherwise. The 15j symbol is the recoupling coefficient between the bases of a chain coupling
along the rail `a` and along the rail `b`; the sum over `a_t` runs over `a_t ≤ a_{t-1} + c_{t-1}`,
outside which the terms vanish. -/
theorem sum_fifteenJ_mul_fifteenJ (a0 b0 b1 b2 b3 b4 b1' b2' b3' b4' c0 c1 c2 c3 c4 : ℕ) :
    ∑ x1 ∈ range (a0 + c0 + 1), ((x1 : ℝ) + 1) * ∑ x2 ∈ range (x1 + c1 + 1), ((x2 : ℝ) + 1) *
      ∑ x3 ∈ range (x2 + c2 + 1), ((x3 : ℝ) + 1) * ∑ x4 ∈ range (x3 + c3 + 1), ((x4 : ℝ) + 1) *
        (fifteenJ ![a0, x1, x2, x3, x4] ![b0, b1, b2, b3, b4] ![c0, c1, c2, c3, c4] *
          fifteenJ ![a0, x1, x2, x3, x4] ![b0, b1', b2', b3', b4'] ![c0, c1, c2, c3, c4]) =
    if (b1 = b1' ∧ b2 = b2' ∧ b3 = b3' ∧ b4 = b4') ∧ Tri b0 c0 b1 ∧ Tri b1 c1 b2 ∧ Tri b2 c2 b3 ∧
        Tri b3 c3 b4 ∧ Tri b4 c4 a0 then
      1 / (((b1 : ℝ) + 1) * ((b2 : ℝ) + 1) * ((b3 : ℝ) + 1) * ((b4 : ℝ) + 1))
    else 0 := by
  rw [← sum_mobius_mul_mobius]
  simp only [fifteenJ_eq_mobius, railA_vec, railB_vec, railC_vec, Matrix.cons_val_zero]
  have hs : ∀ X Y : ℝ, (-1) ^ b0 * X * ((-1) ^ b0 * Y) = X * Y := fun X Y => by
    have h2 : ((-1 : ℝ) ^ b0) * (-1) ^ b0 = 1 := by rw [← mul_pow]; norm_num
    linear_combination X * Y * h2
  simp only [hs]

end Lightlike.Recoupling
