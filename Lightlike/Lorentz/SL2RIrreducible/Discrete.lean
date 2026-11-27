module

public import Lightlike.Lorentz.SL2RIrreducible.Criterion
public import Lightlike.Lorentz.SL2RPlancherel.DiscreteCoherent

/-!
# Irreducibility of the discrete series `D_n⁺` and `D_n⁻` of `SL(2,ℝ)`

For every `n ≥ 2` the holomorphic discrete series `discreteSeries n` (`D_n⁺`, the representation on
the weighted Bergman space `A²_n`) is topologically irreducible (`discreteSeries_isIrreducible`),
and so is the antiholomorphic discrete series `discreteSeriesMinus n` (`D_n⁻`), which is `D_n⁺`
composed with the outer automorphism `g ↦ J g J`, `J = diag(1, -1)`, of `SL(2,ℝ)`
(`discreteSeriesMinus_isIrreducible`). These are all the discrete series of `SL(2,ℝ)`: `D_n^±` for
`n ≥ 2`; the representations with `n = 1` are the two halves of the odd principal series at
`ν = 0`, which is reducible (Kitaev, arXiv:1711.08169, §3.1: `F_{1/2}^{1/2}` splits into `F_{1/2}^±`).

## The argument

Kitaev, *Notes on `SL(2,ℝ)` representations*, arXiv:1711.08169, Eq. (11) and (15): the unitary
discrete series `D_λ⁺` has the `K`-weight basis `|m⟩`, `m = λ, λ+1, …`, joined by the ladder
operators `L_{±1}`; here the weight vectors are `e_k = (z - i)^k (z + i)^{-(n+k)}` of weight
`n + 2k` (`kClass`, `discreteAction_rot_kClass`), an orthogonal Hilbert basis of `A²_n`
(`kClass_orthogonal`, `kClass_complete`), and the graph of the criterion
`isTopologicallyIrreducible_of_weights` is joined through the lowest weight vector `e₀`: for the
diagonal element `g_A = diag(A, A⁻¹)`, `⟪e_k, D_n(g_A) e₀⟫ = γ_A β_k (-t_A)^k ‖e_k‖²`
(`inner_kClass_diag_lowest`) with `γ_A = (2/(A + A⁻¹))^n`, `β_k = C(n-1+k, n-1)` and
`t_A = (A - A⁻¹)/(A + A⁻¹) ≠ 0` for `A = 2`, all nonzero. The criterion replaces Kitaev's algebraic
"invariant subspaces have homogeneous bases" by the corresponding statement for closed invariant
subspaces of the Hilbert space (orthogonal projection onto the weight lines).

The comparison with Knapp, *Representation Theory of Semisimple Groups* (1986), II.5, and Lang,
*SL₂(ℝ)* (1985), IX.2 (irreducibility of `D_n^±`), is pending: those books were not read.
-/

@[expose] public section

open scoped InnerProductSpace
open Lightlike.Lorentz Lightlike.Lorentz.SL2R Lightlike.Lorentz.SL2RPlancherel

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- The `K`-weight vector `e_k` of the weighted Bergman space, as an element of `A²_n`. -/
def bergmanWeightVec {n : ℕ} (hn : 2 ≤ n) (k : ℕ) : holoSubmodule n :=
  ⟨kClass hn k, kClass_mem hn k⟩

/-- **The holomorphic discrete series `D_n⁺` is irreducible** for every `n ≥ 2`: the only closed
`SL(2,ℝ)`-invariant subspaces of the weighted Bergman space `A²_n` are `0` and `A²_n`. -/
theorem discreteSeries_isIrreducible {n : ℕ} (hn : 2 ≤ n) :
    IsTopologicallyIrreducible (discreteSeries n) := by
  refine isTopologicallyIrreducible_of_weights (discreteSeries n) (discreteSeries_inner n) rot
    (bergmanWeightVec hn) (fun k θ => Complex.exp (-(((n + 2 * k : ℕ) : ℂ) * (θ : ℂ) * Complex.I)))
    ?_ ?_ ?_ ?_ ?_
  · intro k h
    exact (norm_kClass_pos hn k).ne' (by simpa [bergmanWeightVec] using congrArg Subtype.val h)
  · intro k θ
    apply Subtype.ext
    simp only [bergmanWeightVec, coe_discreteSeries]
    exact discreteAction_rot_kClass hn k θ
  · intro j k hjk
    have : ((n + 2 * j : ℕ) : ℝ) ≠ ((n + 2 * k : ℕ) : ℝ) := by
      intro h
      exact hjk (by have := Nat.cast_injective h; omega)
    obtain ⟨θ, hθ⟩ := exists_exp_ne this
    exact ⟨θ, by simpa using hθ⟩
  · intro v hv
    refine Subtype.ext (kClass_complete hn v.2 fun k => ?_)
    simpa [bergmanWeightVec] using hv k
  · -- every weight vector is linked to `e₀`, and linking is symmetric
    have hlink0 : ∀ k, ∃ g, ⟪bergmanWeightVec hn k, discreteSeries n g (bergmanWeightVec hn 0)⟫_ℂ ≠ 0 := by
      intro k
      refine ⟨diagSL 2 two_ne_zero, ?_⟩
      have h := inner_kClass_diag_lowest hn (A := 2) two_pos k
      rw [Submodule.coe_inner]
      simp only [coe_discreteSeries, bergmanWeightVec, kClass_zero]
      rw [h]
      have h1 : (gam n 2 : ℂ) ≠ 0 := by
        have : (0 : ℝ) < gam n 2 := by unfold gam; positivity
        exact_mod_cast this.ne'
      have h2 : ((Nat.choose (n - 1 + k) (n - 1) : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
      have h3 : (tpar 2 : ℂ) ≠ 0 := by
        have : tpar 2 ≠ 0 := by unfold tpar; norm_num
        exact_mod_cast this
      have h4 : ((‖kClass hn k‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
        have := (norm_kClass_pos hn k).ne'
        exact_mod_cast pow_ne_zero 2 this
      exact mul_ne_zero (mul_ne_zero h1 (mul_ne_zero h2 (pow_ne_zero _ (neg_ne_zero.mpr h3)))) h4
    intro i j
    have hi := hlink0 i
    have hj := linked_symm (discreteSeries n) (discreteSeries_inner n) (bergmanWeightVec hn) (hlink0 j)
    exact (Relation.ReflTransGen.single hi).tail hj

/-! ## The antiholomorphic series `D_n⁻` -/

/-- The matrix `J g J`, `J = diag(1, -1)`: `[[a, b], [c, d]] ↦ [[a, -b], [-c, d]]`. -/
def flipSL (g : SL2R) : SL2R :=
  mk (g 0 0) (-g 0 1) (-g 1 0) (g 1 1) (by rw [neg_mul_neg]; exact det_eq g)

@[simp] lemma coe_flipSL (g : SL2R) :
    (flipSL g : Matrix (Fin 2) (Fin 2) ℝ) = !![g 0 0, -g 0 1; -g 1 0, g 1 1] := rfl

/-- **The outer automorphism `g ↦ J g J` of `SL(2,ℝ)`**, `J = diag(1, -1)`. It is an involution that
sends the rotation `k_θ` to `k_{-θ}` (`flipHom_rot`). -/
def flipHom : SL2R →* SL2R where
  toFun := flipSL
  map_one' := by
    apply ext_of_entries <;> simp
  map_mul' g h := by
    apply ext_of_entries <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma flipHom_flipHom (g : SL2R) : flipHom (flipHom g) = g := by
  apply ext_of_entries <;> simp [flipHom]

lemma flipHom_rot (θ : ℝ) : flipHom (rot θ) = rot (-θ) := by
  apply ext_of_entries <;> simp [flipHom]

/-- **The antiholomorphic discrete series `D_n⁻`**: `D_n⁺` composed with the outer automorphism
`g ↦ J g J` (`flipHom`). It acts on the same Bergman space `A²_n`; the `K`-weights are negated
(`discreteSeriesMinus_rot`), which is the characterisation of `D_n⁻` as the lowest/highest weight
module with weights `-n, -n-2, …`. The equivalence with the complex conjugate of `D_n⁺` is not
proved here. -/
def discreteSeriesMinus (n : ℕ) : ContRepresentation ℂ SL2R (holoSubmodule n) :=
  .ofMonoidHom ((discreteSeries n).toMonoidHom.comp flipHom)

lemma discreteSeriesMinus_apply (n : ℕ) (g : SL2R) (f : holoSubmodule n) :
    discreteSeriesMinus n g f = discreteSeries n (flipHom g) f := rfl

/-- **`D_n⁻` is unitary.** -/
theorem discreteSeriesMinus_inner (n : ℕ) (g : SL2R) (f f' : holoSubmodule n) :
    ⟪discreteSeriesMinus n g f, discreteSeriesMinus n g f'⟫_ℂ = ⟪f, f'⟫_ℂ :=
  discreteSeries_inner n (flipHom g) f f'

/-- **The `K`-weights of `D_n⁻` are the negatives of those of `D_n⁺`**: the rotation `k_θ` acts on
`e_k` by `exp(+i(n + 2k)θ)`. -/
theorem discreteSeriesMinus_rot {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (θ : ℝ) :
    discreteSeriesMinus n (rot θ) (bergmanWeightVec hn k) =
      Complex.exp (((n + 2 * k : ℕ) : ℂ) * (θ : ℂ) * Complex.I) • bergmanWeightVec hn k := by
  rw [discreteSeriesMinus_apply, flipHom_rot]
  apply Subtype.ext
  simp only [bergmanWeightVec, coe_discreteSeries]
  rw [discreteAction_rot_kClass hn k (-θ)]
  simp

/-- **The antiholomorphic discrete series `D_n⁻` is irreducible** for every `n ≥ 2`. -/
theorem discreteSeriesMinus_isIrreducible {n : ℕ} (hn : 2 ≤ n) :
    IsTopologicallyIrreducible (discreteSeriesMinus n) :=
  isTopologicallyIrreducible_comp (discreteSeries n) flipHom
    (fun g => ⟨flipHom g, flipHom_flipHom g⟩) (discreteSeries_isIrreducible hn)

end Lightlike.Lorentz.SL2R
