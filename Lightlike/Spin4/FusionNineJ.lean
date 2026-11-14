import Lightlike.Spin4.Fusion
import Lightlike.Recoupling.NineJ

/-!
# The fusion coefficients as 9j symbols

The EPRL recoupling coefficient `λ` of two links (`eprlRecoupling`, `Lightlike/Spin4/Fusion.lean`)
compares the coupling `((n₁ n₂) x, (m₁ m₂) y) z` of four spins with `(Y₁ ⊗ Y₂)((J₁ J₂) z)`, where
`Jᵢ = nᵢ + mᵢ` and `Yᵢ` is the EPRL map. It is a recoupling coefficient of four angular momenta,
hence a 9j symbol. In doubled spins, for admissible triads,

`λ = √((x+1)(y+1)(J₁+1)(J₂+1)) {n₁ n₂ x; m₁ m₂ y; J₁ J₂ z}`,

with Physlib's `nineJSym` (`eprlRecoupling_eq_nineJSym`). With the factorisation `fusion_eq`, the
fusion coefficients of a 4-valent node are the product of two 9j symbols
(`fusion_eq_nineJSym`):

`f(z; x, y) = √((x+1)(y+1)(z+1) Π_a (J_a+1))
  {n₁ n₂ x; m₁ m₂ y; J₁ J₂ z} {n₃ n₄ x; m₃ m₄ y; J₃ J₄ z}`.

This is the formula of Alesci, Bianchi, Magliaro and Perini (2010, eqs. (7)–(8)), whose 9j symbol
has its rows and columns permuted; with their phase conventions it carries the extra sign
`(-1)^{j₁-j₂+j₃-j₄}` (numerical evidence: `scripts/spin4/eprl_check.py`).

The proof writes every Clebsch–Gordan coefficient as a 3j symbol (`cgz_eq_threeJ`), so that `λ`
becomes a sum of products of six 3j symbols, and matches it term by term with the row/column form
of the 9j symbol (`Lightlike.Recoupling.nineJSym_eq_sum_threeJ`). The six Clebsch–Gordan phases and the
two 3j reflections combine to `+1` on the support.

## Main results

- `eprlRecoupling_eq_nineJSym`: `λ` as a 9j symbol.
- `fusion_eq_nineJSym`: the fusion coefficients as two 9j symbols.
- `nineJSym_singlet`: the 9j symbol `{n n 0; m m 0; J J 0}` in closed form, as a consequence.

## References

- E. Alesci, E. Bianchi, E. Magliaro, C. Perini, *Asymptotics of LQG fusion coefficients*,
  Class. Quantum Grav. 27 (2010) 095016, arXiv:0809.3718, eqs. (7)–(9).
- DLMF, §34.6.
-/

open Matrix Finset PhyslibAlpha.Sl2 Lightlike.Pentagon
open scoped Kronecker

namespace Lightlike.Spin4

variable {n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ x y z : ℕ}

/-- The EPRL map `Y` is the coupling map to the top spin `n + m`. -/
lemma eprlMap_eq_cgz (n m : ℕ) : eprlMap n m = cgz n m (n + m) := by
  exact (cgz_sub (n := n) (m := m) (k := 0) (by omega)).symm

/-- A Clebsch–Gordan coefficient as a 3j symbol, in the indexing of `cgz`. -/
lemma cgCoefficient_eq_threeJ_of_tri {n m z a b l : ℕ} (h : Tri n m z) (ha : a ≤ n)
    (hb : b ≤ m) (hl : l ≤ z) :
    cgCoefficient n m ((n + m - z) / 2) l a b = (-1 : ℝ) ^ (n + (n + m - z) / 2 + l) *
      Real.sqrt ((z : ℝ) + 1) * threeJ n m z ((n : ℤ) - 2 * a) ((m : ℤ) - 2 * b)
        (-((z : ℤ) - 2 * l)) := by
  have e := cgz_eq_threeJ h ((⟨a, by omega⟩, ⟨b, by omega⟩) : Idx n m)
    (⟨l, by omega⟩ : Fin (z + 1))
  simp only [cgz, of_apply] at e
  exact_mod_cast e

/-- One term of `λ`: the product of the six Clebsch–Gordan coefficients is `(z+1)` times the
dimension factors times one term of the row/column form of the 9j symbol. -/
lemma cg_term_eq (hx : Tri n₁ n₂ x) (hy : Tri m₁ m₂ y) (hz : Tri (n₁ + m₁) (n₂ + m₂) z)
    (hxyz : Tri x y z) {ζ ξ η c₁ c₂ a₁ a₂ b₁ b₂ : ℕ} (hζ : ζ ≤ z) (hξ : ξ ≤ x) (hη : η ≤ y)
    (hc₁ : c₁ ≤ n₁ + m₁) (hc₂ : c₂ ≤ n₂ + m₂) (ha₁ : a₁ ≤ n₁) (ha₂ : a₂ ≤ n₂) (hb₁ : b₁ ≤ m₁)
    (hb₂ : b₂ ≤ m₂) :
    cgCoefficient x y ((x + y - z) / 2) ζ ξ η *
      (cgCoefficient n₁ n₂ ((n₁ + n₂ - x) / 2) ξ a₁ a₂ *
        cgCoefficient m₁ m₂ ((m₁ + m₂ - y) / 2) η b₁ b₂ *
        (cgCoefficient n₁ m₁ ((n₁ + m₁ - (n₁ + m₁)) / 2) c₁ a₁ b₁ *
          cgCoefficient n₂ m₂ ((n₂ + m₂ - (n₂ + m₂)) / 2) c₂ a₂ b₂) *
        cgCoefficient (n₁ + m₁) (n₂ + m₂) ((n₁ + m₁ + (n₂ + m₂) - z) / 2) ζ c₁ c₂) =
    ((z : ℝ) + 1) * (Real.sqrt ((x : ℝ) + 1) * Real.sqrt ((y : ℝ) + 1) *
      Real.sqrt (((n₁ + m₁ : ℕ) : ℝ) + 1) * Real.sqrt (((n₂ + m₂ : ℕ) : ℝ) + 1)) *
      (threeJ n₁ n₂ x ((n₁ : ℤ) - 2 * a₁) ((n₂ : ℤ) - 2 * a₂) (-((x : ℤ) - 2 * ξ)) *
        threeJ m₁ m₂ y ((m₁ : ℤ) - 2 * b₁) ((m₂ : ℤ) - 2 * b₂) (-((y : ℤ) - 2 * η)) *
        threeJ (n₁ + m₁) (n₂ + m₂) z (-(((n₁ + m₁ : ℕ) : ℤ) - 2 * c₁))
          (-(((n₂ + m₂ : ℕ) : ℤ) - 2 * c₂)) ((z : ℤ) - 2 * ζ) *
        (threeJ n₁ m₁ (n₁ + m₁) ((n₁ : ℤ) - 2 * a₁) ((m₁ : ℤ) - 2 * b₁)
            (-(((n₁ + m₁ : ℕ) : ℤ) - 2 * c₁)) *
          threeJ n₂ m₂ (n₂ + m₂) ((n₂ : ℤ) - 2 * a₂) ((m₂ : ℤ) - 2 * b₂)
            (-(((n₂ + m₂ : ℕ) : ℤ) - 2 * c₂)) *
          threeJ x y z (-((x : ℤ) - 2 * ξ)) (-((y : ℤ) - 2 * η)) ((z : ℤ) - 2 * ζ))) := by
  have t₁ : Tri n₁ m₁ (n₁ + m₁) := by unfold Tri; omega
  have t₂ : Tri n₂ m₂ (n₂ + m₂) := by unfold Tri; omega
  rw [cgCoefficient_eq_threeJ_of_tri hxyz hξ hη hζ, cgCoefficient_eq_threeJ_of_tri hx ha₁ ha₂ hξ,
    cgCoefficient_eq_threeJ_of_tri hy hb₁ hb₂ hη, cgCoefficient_eq_threeJ_of_tri t₁ ha₁ hb₁ hc₁,
    cgCoefficient_eq_threeJ_of_tri t₂ ha₂ hb₂ hc₂, cgCoefficient_eq_threeJ_of_tri hz hc₁ hc₂ hζ]
  have e₃ := threeJ_neg (n₁ + m₁) (n₂ + m₂) z (((n₁ + m₁ : ℕ) : ℤ) - 2 * c₁)
    (((n₂ + m₂ : ℕ) : ℤ) - 2 * c₂) (-((z : ℤ) - 2 * ζ))
  have e₆ := threeJ_neg x y z ((x : ℤ) - 2 * ξ) ((y : ℤ) - 2 * η) (-((z : ℤ) - 2 * ζ))
  simp only [neg_neg] at e₃ e₆
  rw [e₃, e₆]
  set T₁ := threeJ n₁ n₂ x ((n₁ : ℤ) - 2 * a₁) ((n₂ : ℤ) - 2 * a₂) (-((x : ℤ) - 2 * ξ))
  set T₂ := threeJ m₁ m₂ y ((m₁ : ℤ) - 2 * b₁) ((m₂ : ℤ) - 2 * b₂) (-((y : ℤ) - 2 * η))
  set T₃ := threeJ (n₁ + m₁) (n₂ + m₂) z (((n₁ + m₁ : ℕ) : ℤ) - 2 * c₁)
    (((n₂ + m₂ : ℕ) : ℤ) - 2 * c₂) (-((z : ℤ) - 2 * ζ))
  set T₄ := threeJ n₁ m₁ (n₁ + m₁) ((n₁ : ℤ) - 2 * a₁) ((m₁ : ℤ) - 2 * b₁)
    (-(((n₁ + m₁ : ℕ) : ℤ) - 2 * c₁))
  set T₅ := threeJ n₂ m₂ (n₂ + m₂) ((n₂ : ℤ) - 2 * a₂) ((m₂ : ℤ) - 2 * b₂)
    (-(((n₂ + m₂ : ℕ) : ℤ) - 2 * c₂))
  set T₆ := threeJ x y z ((x : ℤ) - 2 * ξ) ((y : ℤ) - 2 * η) (-((z : ℤ) - 2 * ζ))
  by_cases h₁ : T₁ = 0
  · simp [h₁]
  by_cases h₂ : T₂ = 0
  · simp [h₂]
  by_cases h₃ : T₃ = 0
  · simp [h₃]
  by_cases h₄ : T₄ = 0
  · simp [h₄]
  by_cases h₅ : T₅ = 0
  · simp [h₅]
  by_cases h₆ : T₆ = 0
  · simp [h₆]
  obtain ⟨s₁, -⟩ := adm3_of_threeJ_ne_zero h₁
  obtain ⟨s₂, -⟩ := adm3_of_threeJ_ne_zero h₂
  obtain ⟨s₃, -⟩ := adm3_of_threeJ_ne_zero h₃
  obtain ⟨s₄, -⟩ := adm3_of_threeJ_ne_zero h₄
  obtain ⟨s₅, -⟩ := adm3_of_threeJ_ne_zero h₅
  obtain ⟨s₆, -⟩ := adm3_of_threeJ_ne_zero h₆
  have key : (-1 : ℝ) ^ (x + (x + y - z) / 2 + ζ) * (-1) ^ (n₁ + (n₁ + n₂ - x) / 2 + ξ) *
      (-1) ^ (m₁ + (m₁ + m₂ - y) / 2 + η) * (-1) ^ (n₁ + (n₁ + m₁ - (n₁ + m₁)) / 2 + c₁) *
      (-1) ^ (n₂ + (n₂ + m₂ - (n₂ + m₂)) / 2 + c₂) *
      (-1) ^ (n₁ + m₁ + (n₁ + m₁ + (n₂ + m₂) - z) / 2 + ζ) =
      (-1) ^ ((n₁ + m₁ + (n₂ + m₂) + z) / 2) * (-1) ^ ((x + y + z) / 2) := by
    simp only [← pow_add, Nat.sub_self, Nat.zero_div, add_zero]
    apply Lightlike.Recoupling.neg_one_pow_congr_mod
    unfold Tri at hx hy hz hxyz
    obtain ⟨k₁, e₁, f₁⟩ : ∃ k, (x + y - z) / 2 = k ∧ 2 * k + z = x + y := ⟨_, rfl, by omega⟩
    obtain ⟨k₂, e₂, f₂⟩ : ∃ k, (n₁ + n₂ - x) / 2 = k ∧ 2 * k + x = n₁ + n₂ := ⟨_, rfl, by omega⟩
    obtain ⟨k₃, e₃, f₃⟩ : ∃ k, (m₁ + m₂ - y) / 2 = k ∧ 2 * k + y = m₁ + m₂ := ⟨_, rfl, by omega⟩
    obtain ⟨k₄, e₄, f₄⟩ : ∃ k, (n₁ + m₁ + (n₂ + m₂) - z) / 2 = k ∧
      2 * k + z = n₁ + m₁ + (n₂ + m₂) := ⟨_, rfl, by omega⟩
    obtain ⟨k₅, e₅, f₅⟩ : ∃ k, (n₁ + m₁ + (n₂ + m₂) + z) / 2 = k ∧
      2 * k = n₁ + m₁ + (n₂ + m₂) + z := ⟨_, rfl, by omega⟩
    obtain ⟨k₆, e₆, f₆⟩ : ∃ k, (x + y + z) / 2 = k ∧ 2 * k = x + y + z := ⟨_, rfl, by omega⟩
    rw [e₁, e₂, e₃, e₄, e₅, e₆]
    push_cast at s₁ s₂ s₃ s₄ s₅ s₆
    clear e₁ e₂ e₃ e₄ e₅ e₆ hx hy hz hxyz
    omega
  have hsq : Real.sqrt ((z : ℝ) + 1) * Real.sqrt ((z : ℝ) + 1) = (z : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  linear_combination (Real.sqrt ((x : ℝ) + 1) * Real.sqrt ((y : ℝ) + 1) *
      Real.sqrt (((n₁ + m₁ : ℕ) : ℝ) + 1) * Real.sqrt (((n₂ + m₂ : ℕ) : ℝ) + 1) *
      (T₁ * T₂ * T₃ * T₄ * T₅ * T₆)) *
    (((-1 : ℝ) ^ (x + (x + y - z) / 2 + ζ) * (-1) ^ (n₁ + (n₁ + n₂ - x) / 2 + ξ) *
      (-1) ^ (m₁ + (m₁ + m₂ - y) / 2 + η) * (-1) ^ (n₁ + (n₁ + m₁ - (n₁ + m₁)) / 2 + c₁) *
      (-1) ^ (n₂ + (n₂ + m₂ - (n₂ + m₂)) / 2 + c₂) *
      (-1) ^ (n₁ + m₁ + (n₁ + m₁ + (n₂ + m₂) - z) / 2 + ζ)) * hsq +
      ((z : ℝ) + 1) * key)

/-- `λ` as a 9j symbol, for an admissible triad `(x y z)`. -/
lemma eprlRecoupling_eq_nineJSym_of_tri (hx : Tri n₁ n₂ x) (hy : Tri m₁ m₂ y)
    (hz : Tri (n₁ + m₁) (n₂ + m₂) z) (hxyz : Tri x y z) :
    eprlRecoupling n₁ m₁ n₂ m₂ x y z =
      ((Real.sqrt (((x : ℝ) + 1) * ((y : ℝ) + 1) * (((n₁ + m₁ : ℕ) : ℝ) + 1) *
        (((n₂ + m₂ : ℕ) : ℝ) + 1)) * nineJSym n₁ n₂ x m₁ m₂ y (n₁ + m₁) (n₂ + m₂) z : ℝ) : ℂ) := by
  simp only [eprlRecoupling, recoupMat, eprlMap_eq_cgz, trace, Matrix.diag, mul_apply,
    conjTranspose_apply, kroneckerMap_apply, eprlPair_apply, Fintype.sum_prod_type, sum_mul,
    mul_sum, cgz, of_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
    ← Complex.ofReal_div]
  rw [Complex.ofReal_inj, Lightlike.Recoupling.nineJSym_eq_sum_threeJ, Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    div_eq_iff (by positivity : (z : ℝ) + 1 ≠ 0)]
  simp only [← sum_product']
  rw [mul_sum, sum_mul]
  refine sum_of_injOn (fun t => ((n₁ : ℤ) - 2 * (t.2.2.2.2.2.1 : ℕ),
      (n₂ : ℤ) - 2 * (t.2.2.2.2.2.2.1 : ℕ), -((x : ℤ) - 2 * (t.2.1 : ℕ)),
      (m₁ : ℤ) - 2 * (t.2.2.2.2.2.2.2.1 : ℕ), (m₂ : ℤ) - 2 * (t.2.2.2.2.2.2.2.2 : ℕ),
      -((y : ℤ) - 2 * (t.2.2.1 : ℕ)), -(((n₁ + m₁ : ℕ) : ℤ) - 2 * (t.2.2.2.1 : ℕ)),
      -(((n₂ + m₂ : ℕ) : ℤ) - 2 * (t.2.2.2.2.1 : ℕ)), (z : ℤ) - 2 * (t.1 : ℕ))) ?_ ?_ ?_ ?_
  · rintro ⟨⟨ζ, hζ⟩, ⟨ξ, hξ⟩, ⟨η, hη⟩, ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩, ⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ⟨b₁, hb₁⟩,
      ⟨b₂, hb₂⟩⟩ - ⟨⟨ζ', hζ'⟩, ⟨ξ', hξ'⟩, ⟨η', hη'⟩, ⟨c₁', hc₁'⟩, ⟨c₂', hc₂'⟩, ⟨a₁', ha₁'⟩,
      ⟨a₂', ha₂'⟩, ⟨b₁', hb₁'⟩, ⟨b₂', hb₂'⟩⟩ - h
    simp only [Prod.mk.injEq] at h
    simp only [Prod.mk.injEq, Fin.mk.injEq]
    omega
  · rintro ⟨⟨ζ, hζ⟩, ⟨ξ, hξ⟩, ⟨η, hη⟩, ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩, ⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ⟨b₁, hb₁⟩,
      ⟨b₂, hb₂⟩⟩ -
    simp only [mem_coe, mem_product, mem_Icc]
    omega
  · rintro ⟨μ₁₁, μ₁₂, μ₁₃, μ₂₁, μ₂₂, μ₂₃, μ₃₁, μ₃₂, μ₃₃⟩ hμ hni
    by_contra hne
    apply hni
    have r₁ : threeJ n₁ n₂ x μ₁₁ μ₁₂ μ₁₃ ≠ 0 := fun h => hne (by simp [h])
    have r₂ : threeJ m₁ m₂ y μ₂₁ μ₂₂ μ₂₃ ≠ 0 := fun h => hne (by simp [h])
    have r₃ : threeJ (n₁ + m₁) (n₂ + m₂) z μ₃₁ μ₃₂ μ₃₃ ≠ 0 := fun h => hne (by simp [h])
    obtain ⟨-, -, -, -, -, -, -, p₁₁, p₁₂, p₁₃, -⟩ := adm3_of_threeJ_ne_zero r₁
    obtain ⟨-, -, -, -, -, -, -, p₂₁, p₂₂, p₂₃, -⟩ := adm3_of_threeJ_ne_zero r₂
    obtain ⟨-, -, -, -, -, -, -, p₃₁, p₃₂, p₃₃, -⟩ := adm3_of_threeJ_ne_zero r₃
    simp only [mem_product, mem_Icc] at hμ
    refine ⟨(⟨((z - μ₃₃) / 2).toNat, by omega⟩, ⟨((x + μ₁₃) / 2).toNat, by omega⟩,
      ⟨((y + μ₂₃) / 2).toNat, by omega⟩, ⟨((((n₁ + m₁ : ℕ) : ℤ) + μ₃₁) / 2).toNat, by omega⟩,
      ⟨((((n₂ + m₂ : ℕ) : ℤ) + μ₃₂) / 2).toNat, by omega⟩, ⟨((n₁ - μ₁₁) / 2).toNat, by omega⟩,
      ⟨((n₂ - μ₁₂) / 2).toNat, by omega⟩, ⟨((m₁ - μ₂₁) / 2).toNat, by omega⟩,
      ⟨((m₂ - μ₂₂) / 2).toNat, by omega⟩), by simp, ?_⟩
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨⟨ζ, hζ⟩, ⟨ξ, hξ⟩, ⟨η, hη⟩, ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩, ⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ⟨b₁, hb₁⟩,
      ⟨b₂, hb₂⟩⟩ -
    dsimp only
    rw [cg_term_eq hx hy hz hxyz (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    ring

/-- **The EPRL recoupling coefficients are 9j symbols**: for admissible triads `(n₁ n₂ x)`,
`(m₁ m₂ y)` and `(J₁ J₂ z)` with `Jᵢ = nᵢ + mᵢ`,
`λ = √((x+1)(y+1)(J₁+1)(J₂+1)) {n₁ n₂ x; m₁ m₂ y; J₁ J₂ z}` in doubled spins. Both sides vanish
unless `(x y z)` is admissible. -/
theorem eprlRecoupling_eq_nineJSym (hx : Tri n₁ n₂ x) (hy : Tri m₁ m₂ y)
    (hz : Tri (n₁ + m₁) (n₂ + m₂) z) :
    eprlRecoupling n₁ m₁ n₂ m₂ x y z =
      ((Real.sqrt (((x : ℝ) + 1) * ((y : ℝ) + 1) * (((n₁ + m₁ : ℕ) : ℝ) + 1) *
        (((n₂ + m₂ : ℕ) : ℝ) + 1)) * nineJSym n₁ n₂ x m₁ m₂ y (n₁ + m₁) (n₂ + m₂) z : ℝ) : ℂ) := by
  by_cases hxyz : Tri x y z
  · exact eprlRecoupling_eq_nineJSym_of_tri hx hy hz hxyz
  · rw [eprlRecoupling, recoupMat_eq_zero hx hy hz hxyz,
      Lightlike.Recoupling.nineJSym_eq_zero_of_not_tri₃ _ _ _ _ _ _ _ _ _ hxyz]
    simp

/-- **The fusion coefficients as two 9j symbols** (Alesci–Bianchi–Magliaro–Perini 2010,
eqs. (7)–(8), up to their phase conventions): for `x`, `y`, `z` in their channels,
`f(z; x, y) = √((x+1)(y+1)(z+1)(J₁+1)(J₂+1)(J₃+1)(J₄+1))
  {n₁ n₂ x; m₁ m₂ y; J₁ J₂ z} {n₃ n₄ x; m₃ m₄ y; J₃ J₄ z}`
in doubled spins, with `J_a = n_a + m_a`. -/
theorem fusion_eq_nineJSym (hx : x ∈ channel n₁ n₂ n₃ n₄) (hy : y ∈ channel m₁ m₂ m₃ m₄)
    (hz : z ∈ channel (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄)) :
    fusion n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ z x y =
      ((Real.sqrt (((x : ℝ) + 1) * ((y : ℝ) + 1) * ((z : ℝ) + 1) *
          (((n₁ + m₁ : ℕ) : ℝ) + 1) * (((n₂ + m₂ : ℕ) : ℝ) + 1) * (((n₃ + m₃ : ℕ) : ℝ) + 1) *
          (((n₄ + m₄ : ℕ) : ℝ) + 1)) *
        nineJSym n₁ n₂ x m₁ m₂ y (n₁ + m₁) (n₂ + m₂) z *
        nineJSym n₃ n₄ x m₃ m₄ y (n₃ + m₃) (n₄ + m₄) z : ℝ) : ℂ) := by
  rw [fusion_eq hx hy hz]
  by_cases hxyz : Tri x y z
  · rw [ite_eq_left hxyz]
    rw [mem_channel] at hx hy hz
    rw [eprlRecoupling_eq_nineJSym hx.1 hy.1 hz.1, eprlRecoupling_eq_nineJSym hx.2 hy.2 hz.2,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_inj, fusionScale]
    simp (disch := positivity) only [Real.sqrt_mul]
    have hsx : Real.sqrt ((x : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hsy : Real.sqrt ((y : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
  · rw [ite_eq_right hxyz, Lightlike.Recoupling.nineJSym_eq_zero_of_not_tri₃ _ _ _ _ _ _ _ _ _ hxyz]
    simp

/-- **A 9j symbol with a zero column**, read off from the singlet recoupling coefficient
(`eprlRecoupling_singlet`): `{n n 0; m m 0; J J 0} = 1/√((n+1)(m+1)(J+1))` for `J = n + m`, in
doubled spins. This is the closed form of the literature (Edmonds, eqs. (6.4.14) and (6.3.2)). -/
theorem nineJSym_singlet (n m : ℕ) :
    nineJSym n n 0 m m 0 (n + m) (n + m) 0 = 1 / (Real.sqrt ((n : ℝ) + 1) *
      Real.sqrt ((m : ℝ) + 1) * Real.sqrt (((n + m : ℕ) : ℝ) + 1)) := by
  have h := eprlRecoupling_eq_nineJSym (n₁ := n) (m₁ := m) (n₂ := n) (m₂ := m) (x := 0) (y := 0)
    (z := 0) (by unfold Tri; omega) (by unfold Tri; omega) (by unfold Tri; omega)
  rw [eprlRecoupling_singlet, Complex.ofReal_inj] at h
  simp only [Nat.cast_zero, zero_add, one_mul] at h
  set a := Real.sqrt ((n : ℝ) + 1)
  set b := Real.sqrt ((m : ℝ) + 1)
  set s := Real.sqrt (((n + m : ℕ) : ℝ) + 1) with hs
  have hss : s * s = ((n + m : ℕ) : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  have hs2 : Real.sqrt ((((n + m : ℕ) : ℝ) + 1) * (((n + m : ℕ) : ℝ) + 1)) = s * s := by
    rw [Real.sqrt_mul_self (by positivity), hss]
  rw [hs2] at h
  have ha : a ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hb : b ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [div_eq_iff (mul_ne_zero ha hb)] at h
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero ha hb) hs0)]
  apply mul_left_cancel₀ hs0
  linear_combination -h

end Lightlike.Spin4
