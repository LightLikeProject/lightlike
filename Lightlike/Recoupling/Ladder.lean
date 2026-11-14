import Lightlike.Recoupling.Intertwiner

/-!
# Ladders of 3j symbols and the 3nj symbols of the first kind

A 3nj symbol of the first kind is the value of a *Möbius ladder*: two rails of spins
`a₀, a₁, …` and `b₀, b₁, …` joined by rungs `c₀, c₁, …`, with the trivalent vertices
`(a_t a_{t+1} c_t)` and `(b_t b_{t+1} c_t)`, closed with a twist (`a_n = b₀`, `b_n = a₀`). This
file evaluates such ladders with a transfer-operator method.

## The rung operator

A function `f : ℤ × ℤ → ℝ` of the projections `(m_a, m_b)` of two rail spins `a, b` is carried
across one rung by `rung a a' b b' c`:

`(rung f)(q) = Σ_p f(p) (-1)^{a-p₁} (-1)^{b-p₂} Σ_{m_c} (-1)^{c-m_c}
  (a a' c; -p₁ q₁ m_c) (b b' c; -p₂ q₂ -m_c)`,

contracting each edge with the sign `(-1)^{j-m}` of the invariant bilinear form (`edgeSign`).

The key fact (`rung_coupled`) is that the coupled vectors `(a b x; m_a m_b ξ)` are eigenvectors:

`rung (a b x; · · ξ) = (-1)^{2x + a'+b+c+x} {a b x; b' a' c} (a' b' x; · · ξ)`.

It is the change of channel of the 4-valent intertwiners (`fourJ_eq_sum_fourRecoupling`), followed
by 3j orthogonality.

## Main results

- `rung_coupled`: the eigenvector property of the rung operator.
- `ladder`, `ladder_coupled`: `n` rungs in a row act on coupled vectors by a product of `n` 6j
  symbols.
- `mobius`, `mobius_eq`: the closed Möbius ladder is
  `Σ_x (2x + 1) (-1)^{a₀+b₀+x} Π_t (-1)^{…} {a_t b_t x; b_{t+1} a_{t+1} c_t}`.
- `ladder_open`: the open ladder, with the end of the first rail left free, vanishes unless that
  end matches the start of the second rail (used for the orthogonality of the 15j symbols).

## References

- A. P. Yutsis, I. B. Levinson, V. V. Vanagas, *Mathematical Apparatus of the Theory of Angular
  Momentum* (Israel Program for Scientific Translations, 1962): the 3nj symbols of the first kind
  as the graphs of Möbius ladders, and their expression as one sum of products of 6j symbols.
- D. A. Varshalovich, A. N. Moskalev, V. K. Khersonskii, *Quantum Theory of Angular Momentum*
  (World Scientific, 1988), Ch. 10: 3nj symbols and their sum rules.

The evaluation by transfer operators (rungs acting diagonally on coupled vectors) is the
graphical reduction of these references written as linear algebra on the components.
-/

open PhyslibAlpha.Sl2 Finset Lightlike.Pentagon

namespace Lightlike.Recoupling

/-- The sign `(-1)^(j - m)` of the invariant bilinear form contracting a projection `m` with `-m`
along an edge of spin `j` (doubled units). For `j - m` odd the integer division rounds down, so the
value there is a junk sign; this is harmless because every tensor it multiplies (3j symbols,
`fourJ`) vanishes at projections of the wrong parity. -/
noncomputable def edgeSign (j : ℕ) (m : ℤ) : ℝ := (-1) ^ (((j : ℤ) - m) / 2)

/-- The projections `|m_a| ≤ a`, `|m_b| ≤ b` of two rail spins. -/
def pairBox (a b : ℕ) : Finset (ℤ × ℤ) := Icc (-(a : ℤ)) a ×ˢ Icc (-(b : ℤ)) b

/-- The coupled vector `(m_a, m_b) ↦ (a b x; m_a m_b ξ)`. -/
noncomputable def coupled (a b x : ℕ) (ξ : ℤ) (p : ℤ × ℤ) : ℝ := threeJ a b x p.1 p.2 ξ

/-- The kernel of one rung `c` between the rail spins `(a, b)` and `(a', b')`:
`Σ_{m_c} (-1)^{c - m_c} (a a' c; -p₁ q₁ m_c) (b b' c; -p₂ q₂ -m_c)`. -/
noncomputable def rungKernel (a a' b b' c : ℕ) (p q : ℤ × ℤ) : ℝ :=
  ∑ mc ∈ Icc (-(c : ℤ)) c,
    edgeSign c mc * threeJ a a' c (-p.1) q.1 mc * threeJ b b' c (-p.2) q.2 (-mc)

/-- The **rung operator**: carries a function of the projections of the rail spins `(a, b)` across
the rung `c` to a function of the projections of `(a', b')`, contracting the rails with the signs
`(-1)^{a - m_a} (-1)^{b - m_b}`. -/
noncomputable def rung (a a' b b' c : ℕ) (f : ℤ × ℤ → ℝ) (q : ℤ × ℤ) : ℝ :=
  ∑ p ∈ pairBox a b, f p * (edgeSign a p.1 * edgeSign b p.2) * rungKernel a a' b b' c p q

/-- A rung is a 4-valent intertwiner with virtual spin `c`, up to its normalisation. -/
lemma fourJ_eq_rungKernel (a a' b b' c : ℕ) (p q : ℤ × ℤ) :
    fourJ a a' b b' c (-p.1) q.1 (-p.2) q.2 =
      Real.sqrt ((c : ℝ) + 1) * rungKernel a a' b b' c p q := by
  unfold fourJ rungKernel edgeSign
  congr 1
  refine sum_congr rfl fun μ _ => ?_
  rw [threeJ_cycle c b b' (-μ) (-p.2) q.2]

/-- Contracting a coupled vector of `(a, b)` with a 3j symbol of the same two spins:
`Σ_p (a b x; p ξ) (-1)^{a-p₁} (-1)^{b-p₂} (a b l; -p₁ -p₂ ν) =
δ_{xl} δ_{ξ,-ν} (-1)^{(a+b+ξ)/2} (-1)^{(a+b+l)/2} / (x + 1)` for admissible `(x, ξ)`. -/
lemma sum_coupled_mul_threeJ (a b x l : ℕ) (ξ ν : ℤ) :
    ∑ p ∈ pairBox a b, coupled a b x ξ p * (edgeSign a p.1 * edgeSign b p.2) *
        threeJ a b l (-p.1) (-p.2) ν =
      if x = l ∧ ξ = -ν ∧ Tri a b x ∧ AdmProj x ξ then
        (-1 : ℝ) ^ (((a : ℤ) + b + ξ) / 2) * (-1) ^ ((a + b + l) / 2) / ((x : ℝ) + 1)
      else 0 := by
  have hterm : ∀ p : ℤ × ℤ, coupled a b x ξ p * (edgeSign a p.1 * edgeSign b p.2) *
      threeJ a b l (-p.1) (-p.2) ν =
      (-1 : ℝ) ^ (((a : ℤ) + b + ξ) / 2) * (-1) ^ ((a + b + l) / 2) *
        (threeJ a b x p.1 p.2 ξ * threeJ a b l p.1 p.2 (-ν)) := by
    intro p
    have e : threeJ a b l (-p.1) (-p.2) ν = (-1) ^ ((a + b + l) / 2) * threeJ a b l p.1 p.2 (-ν) := by
      have h := threeJ_neg a b l p.1 p.2 (-ν)
      rwa [neg_neg] at h
    unfold coupled
    rw [e]
    by_cases h0 : threeJ a b x p.1 p.2 ξ = 0
    · rw [h0]; ring
    obtain ⟨s, -, -, -, -, -, -, p1, p2, -⟩ := adm3_of_threeJ_ne_zero h0
    have hs : edgeSign a p.1 * edgeSign b p.2 = (-1 : ℝ) ^ (((a : ℤ) + b + ξ) / 2) := by
      unfold edgeSign
      rw [← zpow_add₀ (by norm_num)]
      congr 1
      omega
    rw [hs]; ring
  rw [sum_congr rfl fun p _ => hterm p, ← mul_sum, pairBox, sum_product]
  simp only
  rw [sum_threeJ_mul_threeJ]
  split_ifs <;> ring

/-- **The coupled vectors are eigenvectors of a rung** (doubled units):
`rung (a b x; · · ξ) = (-1)^{x + (a'+b+c+x)/2} {a b x; b' a' c} (a' b' x; · · ξ)`, for all spins.
The rung kernel is a 4-valent intertwiner in the channel `(a a')(b b')`; its change to the channel
`(a b)(a' b')` (`fourJ_eq_sum_fourRecoupling`) and 3j orthogonality pick out the virtual spin `x`. -/
theorem rung_coupled (a a' b b' c x : ℕ) (ξ : ℤ) (q : ℤ × ℤ) :
    rung a a' b b' c (coupled a b x ξ) q =
      (-1) ^ (x + (a' + b + c + x) / 2) * sixJSym a b x b' a' c * coupled a' b' x ξ q := by
  have hc : 0 < Real.sqrt ((c : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  set C := (Real.sqrt ((c : ℝ) + 1))⁻¹ with hC
  -- the kernel through the change of channel
  have hK : ∀ p : ℤ × ℤ, rungKernel a a' b b' c p q = C *
      ∑ l ∈ range (a + b + 1), fourRecoupling a a' b b' c l *
        (Real.sqrt ((l : ℝ) + 1) * ∑ ν ∈ Icc (-(l : ℤ)) l,
          (-1 : ℝ) ^ (((l : ℤ) - ν) / 2) * threeJ a b l (-p.1) (-p.2) ν *
            threeJ l a' b' (-ν) q.1 q.2) := by
    intro p
    rw [hC, eq_inv_mul_iff_mul_eq₀ hc.ne', ← fourJ_eq_rungKernel, fourJ_eq_sum_fourRecoupling]
    rfl
  unfold rung
  simp only [hK]
  -- move the sums over `l` and `ν` outside the sum over `p`
  have hreorg : ∑ p ∈ pairBox a b, coupled a b x ξ p * (edgeSign a p.1 * edgeSign b p.2) *
      (C * ∑ l ∈ range (a + b + 1), fourRecoupling a a' b b' c l *
        (Real.sqrt ((l : ℝ) + 1) * ∑ ν ∈ Icc (-(l : ℤ)) l,
          (-1 : ℝ) ^ (((l : ℤ) - ν) / 2) * threeJ a b l (-p.1) (-p.2) ν *
            threeJ l a' b' (-ν) q.1 q.2)) =
      ∑ l ∈ range (a + b + 1), ∑ ν ∈ Icc (-(l : ℤ)) l,
        C * fourRecoupling a a' b b' c l * Real.sqrt ((l : ℝ) + 1) *
          (-1 : ℝ) ^ (((l : ℤ) - ν) / 2) * threeJ l a' b' (-ν) q.1 q.2 *
          ∑ p ∈ pairBox a b, coupled a b x ξ p * (edgeSign a p.1 * edgeSign b p.2) *
            threeJ a b l (-p.1) (-p.2) ν := by
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun ν _ => sum_congr rfl fun p _ => ?_
    ring
  rw [hreorg]
  simp only [sum_coupled_mul_threeJ]
  by_cases hadm : Tri a b x ∧ AdmProj x ξ
  swap
  · rw [sum_eq_zero fun l _ => sum_eq_zero fun ν _ => by
      rw [ite_eq_right (fun h => hadm ⟨h.2.2.1, h.2.2.2⟩), mul_zero]]
    by_cases ht : Tri a b x
    · have h0 : coupled a' b' x ξ q = 0 := threeJ_eq_zero_of_not (fun h => hadm ⟨ht, h.2⟩)
      rw [h0, mul_zero]
    · have h0 : sixJSym a b x b' a' c = 0 := by
        by_contra h
        exact ht (tri_of_sixJSym_ne_zero h).1
      rw [h0, mul_zero, zero_mul]
  obtain ⟨ht, hξ1, hξ2, hξ3⟩ := hadm
  have hx : x ∈ range (a + b + 1) := mem_range.mpr (by unfold Tri at ht; omega)
  rw [sum_eq_single x (fun l _ hl => sum_eq_zero fun ν _ => by
      rw [ite_eq_right (fun h => hl h.1.symm), mul_zero]) (fun h => absurd hx h)]
  have hν : -ξ ∈ Icc (-(x : ℤ)) x := mem_Icc.mpr ⟨by omega, by omega⟩
  rw [sum_eq_single (-ξ) (fun ν _ hν' => by
      rw [ite_eq_right (fun h => hν' (by rw [h.2.1, neg_neg])), mul_zero]) (fun h => absurd hν h),
    ite_eq_left ⟨rfl, (neg_neg ξ).symm, ht, hξ1, hξ2, hξ3⟩, neg_neg]
  -- algebra: normalisations, 6j and 3j symmetries, signs
  unfold fourRecoupling
  rw [sixJSym_flip₂₃ a a' c b' b x, ← threeJ_cycle x a' b' ξ q.1 q.2,
    Real.sqrt_mul (by positivity)]
  have hx1 : (0 : ℝ) < (x : ℝ) + 1 := by positivity
  have hsign : (-1 : ℝ) ^ ((a' + b + c + x) / 2) * (-1 : ℝ) ^ (((x : ℤ) - -ξ) / 2) *
      ((-1 : ℝ) ^ (((a : ℤ) + b + ξ) / 2) * (-1) ^ ((a + b + x) / 2)) =
      (-1) ^ (x + (a' + b + c + x) / 2) := by
    unfold Tri at ht
    rw [← zpow_natCast, ← zpow_natCast (n := (a + b + x) / 2), ← zpow_natCast,
      ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
    apply neg_one_zpow_congr
    push_cast
    omega
  unfold coupled
  rw [← hsign, hC]
  field_simp
  rw [Real.sq_sqrt hx1.le]

/-! ## Ladders -/

/-- `n` rungs in a row: rung `t` joins the rail spins `(a t, b t)` to `(a (t+1), b (t+1))` through
the rung spin `c t`. -/
noncomputable def ladder (a b c : ℕ → ℕ) : ℕ → (ℤ × ℤ → ℝ) → ℤ × ℤ → ℝ
  | 0, f => f
  | n + 1, f => rung (a n) (a (n + 1)) (b n) (b (n + 1)) (c n) (ladder a b c n f)

/-- The rung operator is linear: sums. -/
lemma rung_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ × ℤ → ℝ) (a a' b b' c : ℕ) (q : ℤ × ℤ) :
    rung a a' b b' c (fun p => ∑ i ∈ s, f i p) q = ∑ i ∈ s, rung a a' b b' c (f i) q := by
  unfold rung
  simp only [sum_mul]
  rw [sum_comm]

/-- The rung operator is linear: scalars. -/
lemma rung_smul (w : ℝ) (f : ℤ × ℤ → ℝ) (a a' b b' c : ℕ) (q : ℤ × ℤ) :
    rung a a' b b' c (fun p => w * f p) q = w * rung a a' b b' c f q := by
  unfold rung
  rw [mul_sum]
  exact sum_congr rfl fun p _ => by ring

/-- A rung only sees its argument on admissible projections. -/
lemma rung_congr {a a' b b' c : ℕ} {f g : ℤ × ℤ → ℝ}
    (h : ∀ p : ℤ × ℤ, AdmProj a p.1 → AdmProj b p.2 → f p = g p) :
    rung a a' b b' c f = rung a a' b b' c g := by
  funext q
  unfold rung
  refine sum_congr rfl fun p _ => ?_
  by_cases hp : AdmProj a p.1 ∧ AdmProj b p.2
  · rw [h p hp.1 hp.2]
  · have hK : rungKernel a a' b b' c p q = 0 := by
      unfold rungKernel
      refine sum_eq_zero fun mc _ => ?_
      by_cases h1 : threeJ a a' c (-p.1) q.1 mc = 0
      · rw [h1]; ring
      by_cases h2 : threeJ b b' c (-p.2) q.2 (-mc) = 0
      · rw [h2]; ring
      exfalso
      obtain ⟨-, a1, a2, -, -, -, -, a7, -⟩ := adm3_of_threeJ_ne_zero h1
      obtain ⟨-, b1, b2, -, -, -, -, b7, -⟩ := adm3_of_threeJ_ne_zero h2
      exact hp ⟨⟨by omega, by omega, by omega⟩, by omega, by omega, by omega⟩
    rw [hK, mul_zero, mul_zero]

/-- Ladders are linear: sums. -/
lemma ladder_sum {ι : Type*} (a b c : ℕ → ℕ) (n : ℕ) (s : Finset ι) (f : ι → ℤ × ℤ → ℝ) :
    ladder a b c n (fun p => ∑ i ∈ s, f i p) = fun q => ∑ i ∈ s, ladder a b c n (f i) q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext q
    simp only [ladder]
    rw [ih, rung_sum]

/-- Ladders are linear: scalars. -/
lemma ladder_smul (a b c : ℕ → ℕ) (n : ℕ) (w : ℝ) (f : ℤ × ℤ → ℝ) :
    ladder a b c n (fun p => w * f p) = fun q => w * ladder a b c n f q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext q
    simp only [ladder]
    rw [ih, rung_smul]

/-- A ladder of at least one rung only sees its argument on admissible projections. -/
lemma ladder_congr (a b c : ℕ → ℕ) (n : ℕ) {f g : ℤ × ℤ → ℝ}
    (h : ∀ p : ℤ × ℤ, AdmProj (a 0) p.1 → AdmProj (b 0) p.2 → f p = g p) :
    ladder a b c (n + 1) f = ladder a b c (n + 1) g := by
  induction n with
  | zero => exact rung_congr h
  | succ n ih =>
    simp only [ladder] at ih ⊢
    rw [ih]

/-- The eigenvalue of rung `t` on coupled vectors with intermediate spin `x`. -/
noncomputable def rungFactor (a b c : ℕ → ℕ) (x t : ℕ) : ℝ :=
  (-1) ^ (x + (a (t + 1) + b t + c t + x) / 2) * sixJSym (a t) (b t) x (b (t + 1)) (a (t + 1)) (c t)

/-- **`n` rungs act on coupled vectors by a product of 6j symbols.** -/
theorem ladder_coupled (a b c : ℕ → ℕ) (n x : ℕ) (ξ : ℤ) :
    ladder a b c n (coupled (a 0) (b 0) x ξ) =
      fun q => (∏ t ∈ range n, rungFactor a b c x t) * coupled (a n) (b n) x ξ q := by
  induction n with
  | zero => funext q; simp [ladder]
  | succ n ih =>
    funext q
    simp only [ladder]
    rw [ih, rung_smul, rung_coupled, prod_range_succ, rungFactor]
    ring

/-- The point function at `p`. -/
def pairDelta (p q : ℤ × ℤ) : ℝ := if q = p then 1 else 0

/-- The **closed Möbius ladder** of `n` rungs: the rails are closed with a twist, the end
`(a n, b n)` being glued to `(b 0, a 0)`. Its value is the 3nj symbol of the first kind up to
sign (`mobius_eq`). -/
noncomputable def mobius (n : ℕ) (a b c : ℕ → ℕ) : ℝ :=
  ∑ p ∈ pairBox (a 0) (b 0), ladder a b c n (pairDelta p) (p.2, p.1)

/-- `Σ_ξ Σ_{m₁ m₂} (a b x; m₁ m₂ ξ)² = 1` for an admissible triad, `0` otherwise. -/
lemma sum_coupled_sq (a b x : ℕ) :
    ∑ ξ ∈ Icc (-(x : ℤ)) x, ∑ p ∈ pairBox a b, coupled a b x ξ p * coupled a b x ξ p =
      if Tri a b x then 1 else 0 := by
  rw [← sum_threeJ_sq a b x]
  simp only [pairBox, sum_product, coupled, sq]
  rw [sum_comm]
  refine sum_congr rfl fun m₁ _ => ?_
  rw [sum_comm]

/-- **The Möbius ladder is a sum over one spin of a product of 6j symbols** (doubled units):
`Σ_x (x + 1) (-1)^{(a₀+b₀+x)/2} [(a₀ b₀ x) admissible] Π_t rungFactor t`, for `n ≥ 1` rungs
closed with the twist `a n = b 0`, `b n = a 0`. -/
theorem mobius_eq (n : ℕ) (a b c : ℕ → ℕ) (ha : a (n + 1) = b 0) (hb : b (n + 1) = a 0) :
    mobius (n + 1) a b c = ∑ x ∈ range (a 0 + b 0 + 1), ((x : ℝ) + 1) *
      (if Tri (a 0) (b 0) x then (-1 : ℝ) ^ ((a 0 + b 0 + x) / 2) else 0) *
        ∏ t ∈ range (n + 1), rungFactor a b c x t := by
  unfold mobius
  -- expand the point functions by completeness
  have hexp : ∀ p : ℤ × ℤ, ladder a b c (n + 1) (pairDelta p) =
      ladder a b c (n + 1) (fun q => ∑ x ∈ range (a 0 + b 0 + 1), ∑ ξ ∈ Icc (-(x : ℤ)) x,
        ((x : ℝ) + 1) * coupled (a 0) (b 0) x ξ p * coupled (a 0) (b 0) x ξ q) := by
    intro p
    refine ladder_congr a b c n fun q hq1 hq2 => ?_
    have h := sum_threeJ_complete (a 0) (b 0) hq1 hq2 p.1 p.2
    unfold pairDelta coupled
    rw [show (if q = p then (1 : ℝ) else 0) = if q.1 = p.1 ∧ q.2 = p.2 then 1 else 0 by
      simp only [Prod.ext_iff], ← h]
    refine sum_congr rfl fun x _ => sum_congr rfl fun ξ _ => ?_
    ring
  simp only [hexp, ladder_sum, ladder_smul, ladder_coupled, ha, hb]
  -- the glued end is the coupled vector with its columns exchanged
  have hswap : ∀ (x : ℕ) (ξ : ℤ) (p : ℤ × ℤ), coupled (b 0) (a 0) x ξ (p.2, p.1) =
      (-1) ^ ((a 0 + b 0 + x) / 2) * coupled (a 0) (b 0) x ξ p := fun x ξ p =>
    threeJ_swap (a 0) (b 0) x p.1 p.2 ξ
  simp only [hswap]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  have h := sum_coupled_sq (a 0) (b 0) x
  calc _ = ((x : ℝ) + 1) * (-1) ^ ((a 0 + b 0 + x) / 2) * (∏ t ∈ range (n + 1), rungFactor a b c x t) *
        ∑ ξ ∈ Icc (-(x : ℤ)) x, ∑ p ∈ pairBox (a 0) (b 0),
          coupled (a 0) (b 0) x ξ p * coupled (a 0) (b 0) x ξ p := by
        rw [mul_sum]
        refine sum_congr rfl fun ξ _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun p _ => by ring
    _ = _ := by
        rw [h]
        split_ifs <;> ring

/-- **The open Möbius ladder** (doubled units): with the second rail closed onto the first
(`b (n+1) = a 0`) but the end `(a (n+1), M)` of the first rail left open, summing over the
projection `α` of `a 0` gives zero unless `a (n+1) = b 0` and `M = β`, and then `1/(b₀ + 1)` times
the closed ladder of `mobius_eq`. -/
theorem ladder_open (n : ℕ) (a b c : ℕ → ℕ) (hb : b (n + 1) = a 0) {β : ℤ} (hβ : AdmProj (b 0) β)
    (M : ℤ) :
    ∑ α ∈ Icc (-(a 0 : ℤ)) (a 0), ladder a b c (n + 1) (pairDelta (α, β)) (M, α) =
      if a (n + 1) = b 0 ∧ M = β then
        (∑ x ∈ range (a 0 + b 0 + 1), ((x : ℝ) + 1) *
          (if Tri (a 0) (b 0) x then (-1 : ℝ) ^ ((a 0 + b 0 + x) / 2) else 0) *
            ∏ t ∈ range (n + 1), rungFactor a b c x t) / ((b 0 : ℝ) + 1)
      else 0 := by
  have hexp : ∀ p : ℤ × ℤ, ladder a b c (n + 1) (pairDelta p) =
      ladder a b c (n + 1) (fun q => ∑ x ∈ range (a 0 + b 0 + 1), ∑ ξ ∈ Icc (-(x : ℤ)) x,
        ((x : ℝ) + 1) * coupled (a 0) (b 0) x ξ p * coupled (a 0) (b 0) x ξ q) := by
    intro p
    refine ladder_congr a b c n fun q hq1 hq2 => ?_
    have h := sum_threeJ_complete (a 0) (b 0) hq1 hq2 p.1 p.2
    unfold pairDelta coupled
    rw [show (if q = p then (1 : ℝ) else 0) = if q.1 = p.1 ∧ q.2 = p.2 then 1 else 0 by
      simp only [Prod.ext_iff], ← h]
    refine sum_congr rfl fun x _ => sum_congr rfl fun ξ _ => ?_
    ring
  simp only [hexp, ladder_sum, ladder_smul, ladder_coupled, hb]
  -- the sum over `α` is 3j orthogonality
  have horth : ∀ x : ℕ, ∑ ξ ∈ Icc (-(x : ℤ)) x, ∑ α ∈ Icc (-(a 0 : ℤ)) (a 0),
      coupled (a 0) (b 0) x ξ (α, β) * coupled (a (n + 1)) (a 0) x ξ (M, α) =
      (-1) ^ ((a 0 + a (n + 1) + x) / 2) *
        (if b 0 = a (n + 1) ∧ β = M ∧ Tri x (a 0) (b 0) ∧ AdmProj (b 0) β then
          1 / ((b 0 : ℝ) + 1) else 0) := by
    intro x
    rw [← sum_threeJ_mul_threeJ, mul_sum]
    refine sum_congr rfl fun ξ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun α _ => ?_
    unfold coupled
    rw [threeJ_swap (a 0) (a (n + 1)) x α M ξ, ← threeJ_cycle x (a 0) (b 0) ξ α β,
      ← threeJ_cycle x (a 0) (a (n + 1)) ξ α M]
    ring
  rw [sum_comm]
  calc _ = ∑ x ∈ range (a 0 + b 0 + 1), ((x : ℝ) + 1) *
        (∏ t ∈ range (n + 1), rungFactor a b c x t) *
        ∑ ξ ∈ Icc (-(x : ℤ)) x, ∑ α ∈ Icc (-(a 0 : ℤ)) (a 0),
          coupled (a 0) (b 0) x ξ (α, β) * coupled (a (n + 1)) (a 0) x ξ (M, α) := by
        refine sum_congr rfl fun x _ => ?_
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun ξ _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun α _ => by ring
    _ = _ := by
        simp only [horth]
        by_cases hc : a (n + 1) = b 0 ∧ M = β
        · obtain ⟨h1, rfl⟩ := hc
          have hb1 : ((b 0 : ℝ) + 1) ≠ 0 := by positivity
          rw [ite_eq_left ⟨h1, rfl⟩, eq_div_iff hb1, sum_mul]
          refine sum_congr rfl fun x _ => ?_
          rw [h1]
          by_cases ht : Tri (a 0) (b 0) x
          · rw [ite_eq_left ⟨rfl, rfl, by unfold Tri at *; omega, hβ⟩, ite_eq_left ht]
            field_simp
          · rw [ite_eq_right (fun h => ht (by unfold Tri at *; omega)), ite_eq_right ht]
            ring
        · rw [ite_eq_right hc]
          refine sum_eq_zero fun x _ => ?_
          rw [ite_eq_right (fun h => hc ⟨h.1.symm, h.2.1.symm⟩)]
          ring

end Lightlike.Recoupling
