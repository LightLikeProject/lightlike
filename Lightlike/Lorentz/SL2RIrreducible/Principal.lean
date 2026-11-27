module

public import Lightlike.Lorentz.SL2RIrreducible.PrincipalLadder
public import Lightlike.Lorentz.SL2RIrreducible.PrincipalComplete

/-!
# Irreducibility of the principal series of `SL(2,ℝ)`, even and odd

`principalSeries_isIrreducible`: for every integer `ε` and real `ν` with `ε` even or `ν ≠ 0`, the
unitary principal series `P^{ε,iν}` on `L²(ℝ)` (multiplier `|t|^{iν-1} sgn(t)^ε`) is topologically
irreducible: the only closed `SL(2,ℝ)`-invariant subspaces are `0` and `L²(ℝ)`. The even principal
series (`ε` even) is irreducible for **every** real `ν`, including `ν = 0`; the odd one (`ε` odd) for
every `ν ≠ 0`. The single excluded point, the odd principal series at `ν = 0`, is exactly where the
argument breaks: `weightExp_sub_eq_zero_iff` says `s - k = 0` iff `ν = 0` and `1 + ε + 2k = 0`, which
has a solution `k` exactly when `ε` is odd, and there the weight vectors `e_k`, `k ≥ -(1+ε)/2`, and
`k < -(1+ε)/2` are not linked: the representation splits into the two halves (the limits of the
discrete series `D_1^±`).

## The argument (sources)

* The weight vectors `e_k` of weight `2k + ε` and the ladder relation
  `x e_k' - w e_k = ((s - k)/2) e_{k+1} + ((s + k + ε)/2) e_{k-1}` (`ladder_weightVec`) are the explicit
  form of Kitaev, *Notes on `SL(2,ℝ)` representations*, arXiv:1711.08169, Eq. (8), (9), (11), (15),
  with `m = k + ε/2` and `λ = 1/2 + iν/2`; the irreducibility statement is §3.2, items 1–2 there
  (`F_λ^μ` is irreducible unless `λ ∈ μ + ℤ` or `-λ ∈ μ + ℤ`, which for `λ = 1/2 + iν/2` and
  `μ = ε/2` is `ν = 0` and `ε` odd), and the splitting of the odd point at `ν = 0` is the remark on
  `F_{1/2}^{1/2}` in §3.1.
* Kitaev argues with algebraic `K`-finite vectors ("any invariant subspace has a homogeneous
  basis"). The closed-subspace version used here (`isTopologicallyIrreducible_of_weights`) needs the
  completeness of the weight vectors in `L²(ℝ)` (`weightL2_complete`, Fourier analysis on the circle)
  and the non-vanishing of the matrix coefficient `⟪e_{k+1}, π(exp tH) e_k⟫` for some `t`
  (`exists_inner_ne_zero`, from its derivative `(s - k) ‖e_{k+1}‖²` at `t = 0`).
* The comparison with Knapp, *Representation Theory of Semisimple Groups* (1986), II.5, and Lang,
  *SL₂(ℝ)* (1985), VII–VIII, is pending: those books were not read.
-/

@[expose] public section

open scoped InnerProductSpace
open Complex

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- A symmetric relation on `ℤ` that links every `k` to `k + 1` links any two integers. -/
lemma reflTransGen_int {R : ℤ → ℤ → Prop} (hsucc : ∀ k, R k (k + 1))
    (hsymm : ∀ a b, R a b → R b a) : ∀ i j, Relation.ReflTransGen R i j := by
  have hrev : ∀ a b, Relation.ReflTransGen R a b → Relation.ReflTransGen R b a := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih
  have h0 : ∀ j, Relation.ReflTransGen R 0 j := by
    intro j
    induction j using Int.induction_on with
    | zero => exact Relation.ReflTransGen.refl
    | succ i ih => exact ih.tail (hsucc _)
    | pred i ih =>
      refine ih.tail ?_
      have := hsymm _ _ (hsucc (-(i : ℤ) - 1))
      simpa using this
  intro i j
  exact (hrev _ _ (h0 i)).trans (h0 j)

variable (ε : ℤ) (ν : ℝ)

lemma weightExp_re : (weightExp ε ν).re = (-1 - ε) / 2 := by
  simp [weightExp, Complex.div_ofNat_re]

lemma weightExp_im : (weightExp ε ν).im = ν / 2 := by
  simp [weightExp, Complex.div_ofNat_im]

/-- **`s - k = 0` exactly at the reducible point**: `ν = 0` and `1 + ε + 2k = 0`. -/
theorem weightExp_sub_eq_zero_iff (k : ℤ) :
    weightExp ε ν - k = 0 ↔ ν = 0 ∧ 1 + ε + 2 * k = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [Complex.sub_re, Complex.sub_im, weightExp_re, weightExp_im, Complex.intCast_re,
      Complex.intCast_im, Complex.zero_re, Complex.zero_im] at hre him
    refine ⟨by linarith, ?_⟩
    have : ((1 + ε + 2 * k : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this
  · rintro ⟨hν, hk⟩
    apply Complex.ext
    · simp only [Complex.sub_re, weightExp_re, Complex.intCast_re, Complex.zero_re]
      have : (ε : ℝ) = -1 - 2 * k := by
        have : ((1 + ε + 2 * k : ℤ) : ℝ) = 0 := by exact_mod_cast hk
        push_cast at this; linarith
      rw [this]; ring
    · simp only [Complex.sub_im, weightExp_im, Complex.intCast_im, Complex.zero_im, hν]
      ring

/-- **The excluded point is where the hypothesis fails**: for odd `ε` and `ν = 0` some neighbouring
weights are not linked (`s - k = 0` for `k = -(1+ε)/2`), and for even `ε` or `ν ≠ 0` it never
happens. -/
theorem exists_weightExp_sub_eq_zero_iff : (∃ k : ℤ, weightExp ε ν - k = 0) ↔ (Odd ε ∧ ν = 0) := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨hν, hk⟩ := (weightExp_sub_eq_zero_iff ε ν k).mp hk
    exact ⟨⟨-(1 + k), by omega⟩, hν⟩
  · rintro ⟨⟨r, hr⟩, hν⟩
    exact ⟨-(1 + r), (weightExp_sub_eq_zero_iff ε ν _).mpr ⟨hν, by omega⟩⟩

/-- **The principal series of `SL(2,ℝ)` is irreducible**, for every parity `ε` and every real `ν`
except the odd series at `ν = 0` (which is reducible): the only closed invariant subspaces of
`L²(ℝ)` are `0` and `L²(ℝ)`. -/
theorem principalSeries_isIrreducible (h : Even ε ∨ ν ≠ 0) :
    IsTopologicallyIrreducible (principalSeries ε ν) := by
  have hnz : ∀ k : ℤ, weightExp ε ν - k ≠ 0 := by
    intro k hk
    obtain ⟨hν, hk'⟩ := (weightExp_sub_eq_zero_iff ε ν k).mp hk
    rcases h with ⟨r, hr⟩ | hν'
    · omega
    · exact hν' hν
  have hunit := principalSeries_inner ε ν
  have hR : ∀ k : ℤ, ∃ g, ⟪weightL2 ε ν k, principalSeries ε ν g (weightL2 ε ν (k + 1))⟫_ℂ ≠ 0 :=
    fun k => linked_symm (principalSeries ε ν) hunit (weightL2 ε ν)
      (exists_inner_ne_zero ε ν k (hnz k))
  refine isTopologicallyIrreducible_of_weights (principalSeries ε ν) hunit rot (weightL2 ε ν)
    (principalChar ε) (weightL2_ne_zero ε ν)
    (fun i θ => principalSeries_rot_weightL2 ε ν i θ) (fun _ _ hij => principalChar_ne ε hij)
    (fun v hv => weightL2_complete ε ν hv) ?_
  exact reflTransGen_int hR (fun a b hab => linked_symm (principalSeries ε ν) hunit (weightL2 ε ν) hab)

/-! ### Non-vacuity -/

/-- The corner cases of the theorem: the even series at `ν = 0` and a generic odd one. -/
example : IsTopologicallyIrreducible (principalSeries 0 0) :=
  principalSeries_isIrreducible 0 0 (Or.inl ⟨0, by norm_num⟩)

example : IsTopologicallyIrreducible (principalSeries 1 1) :=
  principalSeries_isIrreducible 1 1 (Or.inr one_ne_zero)

/-- At the excluded point the hypothesis of the linking argument fails: `s - k = 0` for `k = -1`. -/
example : weightExp 1 0 - ((-1 : ℤ) : ℂ) = 0 :=
  (weightExp_sub_eq_zero_iff 1 0 (-1)).mpr ⟨rfl, by norm_num⟩

end Lightlike.Lorentz.SL2R
