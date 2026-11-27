module

public import Mathlib

/-!
# Topological irreducibility from a complete family of weight vectors

For a unitary representation `π` of a group on a Hilbert space `H`, *irreducible* means that `H` is
nonzero and the only closed invariant subspaces are `0` and `H` (`IsTopologicallyIrreducible`).
Mathlib's `Representation.IsIrreducible` is the algebraic notion (`IsSimpleModule`), which is the
wrong one for the infinite-dimensional unitary representations of `SL(2,ℝ)`: the span of an orbit of
a `K`-finite vector is invariant and, in general, not everything.

## The criterion

`isTopologicallyIrreducible_of_weights` is the argument of Kitaev, *Notes on `SL(2,ℝ)`
representations*, arXiv:1711.08169, §3.1 (after Eq. (17)): "Any invariant subspace has a
homogeneous basis, that is, the basis vectors are eigenvectors of `L₀`", combined with the ladder
relations (15) which say which basis vectors are connected by the group. In the closed setting it
reads:

* `e : ι → H` is a family of nonzero vectors, **complete** (nothing is orthogonal to all of them),
  and every `e i` is a common eigenvector, with character `χ i : κ → ℂ`, of the group elements
  `r t` (`t ∈ κ`; for `SL(2,ℝ)` the rotations `k_θ`), with pairwise **distinct** characters
  (`hdist`);
* two indices `a`, `b` are **linked** when some `π g` has a nonzero matrix coefficient
  `⟪e a, π g (e b)⟫`; the **linking graph is connected** (`hlink`).

Then every closed invariant subspace `W` is `0` or `H`. The proof: the complement `Wᗮ` is invariant
as well (`orthogonal_invariant`), so `e i = w + w'` with `w ∈ W`, `w' ∈ Wᗮ`, and both parts are
eigenvectors of all `r t` with the character `χ i`; a common eigenvector with the character `χ i`
is a multiple of `e i` (`eq_smul_of_eigen`, using completeness and the distinct characters), so each `e i`
lies in `W` or in `Wᗮ` (`mem_or_mem_orthogonal`); linked vectors lie on the same side
(`linked_iff`), hence all of them do; completeness finishes.

Nothing here is specific to `SL(2,ℝ)`. The instances are `discreteSeries_isIrreducible` and
`discreteSeriesMinus_isIrreducible` (`Discrete.lean`); the principal series is in progress
(`PrincipalWeights.lean`, `PrincipalLadder.lean`).
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- **Topological irreducibility** of a continuous representation on a Hilbert space: the space is
nonzero and every closed invariant subspace is `0` or everything. -/
def IsTopologicallyIrreducible {G H : Type*} [Monoid G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (π : ContRepresentation ℂ G H) : Prop :=
  Nontrivial H ∧ ∀ W : Submodule ℂ H, IsClosed (W : Set H) → (∀ g, ∀ v ∈ W, π g v ∈ W) →
    W = ⊥ ∨ W = ⊤

section Criterion

variable {G H ι κ : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `π g⁻¹` undoes `π g`. -/
lemma rep_inv_apply (π : ContRepresentation ℂ G H) (g : G) (v : H) : π g⁻¹ (π g v) = v := by
  have h : π g⁻¹ * π g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  exact congrArg (fun A : H →L[ℂ] H => A v) h

/-- **The orthogonal complement of an invariant subspace of a unitary representation is
invariant.** -/
lemma orthogonal_invariant (π : ContRepresentation ℂ G H)
    (hunit : ∀ g u v, ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ) {W : Submodule ℂ H}
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) (g : G) {v : H} (hv : v ∈ Wᗮ) : π g v ∈ Wᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  have h := hunit g⁻¹ u (π g v)
  rw [rep_inv_apply] at h
  rw [← h]
  exact Submodule.inner_right_of_mem_orthogonal (hW g⁻¹ u hu) hv

variable (π : ContRepresentation ℂ G H) (hunit : ∀ g u v, ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ)
  (r : κ → G) (e : ι → H) (χ : ι → κ → ℂ) (he0 : ∀ i, e i ≠ 0)
  (heig : ∀ i t, π (r t) (e i) = χ i t • e i)
  (hdist : ∀ i j, i ≠ j → ∃ t, χ i t ≠ χ j t)

include hunit he0 heig in
/-- The characters of the weight vectors have absolute value one. -/
lemma norm_char_eq_one (i : ι) (t : κ) : ‖χ i t‖ = 1 := by
  have h1 := hunit (r t) (e i) (e i)
  rw [heig i t, inner_smul_left, inner_smul_right, ← mul_assoc, inner_self_eq_norm_sq_to_K,
    Complex.conj_mul'] at h1
  have h2 : (‖χ i t‖ : ℂ) ^ 2 * (‖e i‖ : ℂ) ^ 2 = (‖e i‖ : ℂ) ^ 2 := by
    simpa [← mul_pow] using h1
  have hn : (‖e i‖ : ℂ) ^ 2 ≠ 0 := by
    have : ‖e i‖ ≠ 0 := norm_ne_zero_iff.mpr (he0 i)
    exact pow_ne_zero 2 (by exact_mod_cast this)
  have h3 : (‖χ i t‖ : ℂ) ^ 2 = 1 := mul_right_cancel₀ hn (by rw [h2, one_mul])
  have h4 : ‖χ i t‖ ^ 2 = 1 := by exact_mod_cast h3
  have h5 := norm_nonneg (χ i t)
  nlinarith

include hunit he0 heig hdist in
/-- A vector on which the `r t` act by the character `χ k` is orthogonal to every other weight vector. -/
lemma inner_eq_zero_of_eigen {k j : ι} (hjk : j ≠ k) {w : H}
    (hw : ∀ t, π (r t) w = χ k t • w) : ⟪e j, w⟫_ℂ = 0 := by
  obtain ⟨t, hne⟩ := hdist j k hjk
  have h1 := hunit (r t) (e j) w
  rw [heig j t, hw t, inner_smul_left, inner_smul_right] at h1
  have hχ : conj (χ j t) * χ j t = 1 := by
    rw [Complex.conj_mul', norm_char_eq_one π hunit r e χ he0 heig j t]; simp
  have h2 : (conj (χ j t) * χ k t - 1) * ⟪e j, w⟫_ℂ = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (by linear_combination (-(χ j t)) * h3 + χ k t * hχ) hne
  · exact h3

variable (hcomplete : ∀ v, (∀ i, ⟪e i, v⟫_ℂ = 0) → v = 0)

include hunit he0 heig hdist hcomplete in
/-- **An eigenvector of all `r t` with the character `χ k` is a multiple of `e k`.** -/
lemma eq_smul_of_eigen {k : ι} {w : H} (hw : ∀ t, π (r t) w = χ k t • w) :
    ∃ c : ℂ, w = c • e k := by
  have hek : ∀ j, j ≠ k → ⟪e j, e k⟫_ℂ = 0 := fun j hj =>
    inner_eq_zero_of_eigen π hunit r e χ he0 heig hdist hj (heig k)
  have hkk : ⟪e k, e k⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr (he0 k)
  refine ⟨⟪e k, w⟫_ℂ / ⟪e k, e k⟫_ℂ, ?_⟩
  have h0 : w - (⟪e k, w⟫_ℂ / ⟪e k, e k⟫_ℂ) • e k = 0 := by
    apply hcomplete
    intro j
    rw [inner_sub_right, inner_smul_right]
    by_cases hj : j = k
    · subst hj
      field_simp
      ring
    · rw [inner_eq_zero_of_eigen π hunit r e χ he0 heig hdist hj hw, hek j hj]; simp
  exact sub_eq_zero.mp h0

include hunit he0 heig hdist hcomplete in
/-- **Every weight vector lies in a closed invariant subspace or in its orthogonal complement.** -/
lemma mem_or_mem_orthogonal {W : Submodule ℂ H} (hW : IsClosed (W : Set H))
    (hinv : ∀ g, ∀ v ∈ W, π g v ∈ W) (i : ι) [CompleteSpace H] : e i ∈ W ∨ e i ∈ Wᗮ := by
  have : CompleteSpace W := hW.completeSpace_coe
  have hsup : e i ∈ W ⊔ Wᗮ := by
    rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; exact Submodule.mem_top
  obtain ⟨w, hwW, w', hwW', hsum⟩ := Submodule.mem_sup.mp hsup
  have hinv' := orthogonal_invariant π hunit hinv
  have hw : ∀ t, π (r t) w = χ i t • w := by
    intro t
    have h1 : π (r t) w + π (r t) w' = χ i t • w + χ i t • w' := by
      rw [← map_add, hsum, heig i t, ← smul_add, hsum]
    have h2 : π (r t) w - χ i t • w ∈ W := W.sub_mem (hinv (r t) w hwW) (W.smul_mem _ hwW)
    have h3 : π (r t) w - χ i t • w ∈ Wᗮ := by
      have : π (r t) w - χ i t • w = -(π (r t) w' - χ i t • w') := by
        rw [neg_sub]; linear_combination (norm := abel) h1
      rw [this]
      exact Wᗮ.neg_mem (Wᗮ.sub_mem (hinv' (r t) hwW') (Wᗮ.smul_mem _ hwW'))
    have h4 : π (r t) w - χ i t • w ∈ W ⊓ Wᗮ := ⟨h2, h3⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h4
    exact sub_eq_zero.mp (Submodule.mem_bot ℂ |>.mp h4)
  obtain ⟨c, hc⟩ := eq_smul_of_eigen π hunit r e χ he0 heig hdist hcomplete hw
  have hw' : w' = (1 - c) • e i := by
    have : w' = e i - w := by rw [← hsum]; abel
    rw [this, hc, sub_smul, one_smul]
  have horth : ⟪w, w'⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hwW hwW'
  rw [hc, hw', inner_smul_left, inner_smul_right] at horth
  have hkk : ⟪e i, e i⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr (he0 i)
  have h5 : conj c * ((1 - c) * ⟪e i, e i⟫_ℂ) = 0 := horth
  rcases mul_eq_zero.mp h5 with h6 | h6
  · right
    have hc0 : c = 0 := by simpa using h6
    rw [hc0, zero_smul] at hc
    have : w' = e i := by rw [← hsum, hc, zero_add]
    rw [← this]; exact hwW'
  · rcases mul_eq_zero.mp h6 with h7 | h7
    · left
      have hc1 : c = 1 := by linear_combination -h7
      rw [hc1, one_smul] at hc
      rw [← hc]; exact hwW
    · exact absurd h7 hkk

variable (hlink : ∀ i j, Relation.ReflTransGen (fun a b => ∃ g, ⟪e a, π g (e b)⟫_ℂ ≠ 0) i j)

include hunit he0 heig hdist hcomplete in
/-- **Linked weight vectors lie on the same side**: `e a ∈ W ↔ e b ∈ W` when some `π g` has a
nonzero matrix coefficient `⟪e a, π g (e b)⟫`. -/
lemma linked_iff [CompleteSpace H] {W : Submodule ℂ H} (hW : IsClosed (W : Set H))
    (hinv : ∀ g, ∀ v ∈ W, π g v ∈ W) {a b : ι} (hab : ∃ g, ⟪e a, π g (e b)⟫_ℂ ≠ 0) :
    e a ∈ W ↔ e b ∈ W := by
  obtain ⟨g, hg⟩ := hab
  have hinv' := orthogonal_invariant π hunit hinv
  constructor
  · intro ha
    by_contra hb
    have hb' := (mem_or_mem_orthogonal π hunit r e χ he0 heig hdist hcomplete hW hinv b).resolve_left hb
    exact hg (Submodule.inner_right_of_mem_orthogonal ha (hinv' g hb'))
  · intro hb
    by_contra ha
    have ha' := (mem_or_mem_orthogonal π hunit r e χ he0 heig hdist hcomplete hW hinv a).resolve_left ha
    exact hg (Submodule.inner_left_of_mem_orthogonal (hinv g _ hb) ha')

include hunit he0 heig hdist hcomplete hlink in
/-- **The criterion.** A unitary representation with a complete family of nonzero weight vectors,
pairwise distinct characters of the `r t`, and a connected linking graph is topologically irreducible. -/
theorem isTopologicallyIrreducible_of_weights [CompleteSpace H] [Nonempty ι] :
    IsTopologicallyIrreducible π := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨nontrivial_of_ne (e i₀) 0 (he0 i₀), fun W hW hinv => ?_⟩
  have : CompleteSpace W := hW.completeSpace_coe
  have hsame : ∀ j, e j ∈ W ↔ e i₀ ∈ W := by
    intro j
    have : ∀ a b, Relation.ReflTransGen (fun a b => ∃ g, ⟪e a, π g (e b)⟫_ℂ ≠ 0) a b →
        (e a ∈ W ↔ e b ∈ W) := by
      intro a b hab
      induction hab with
      | refl => exact Iff.rfl
      | tail _ hbc ih => exact ih.trans (linked_iff π hunit r e χ he0 heig hdist hcomplete hW hinv hbc)
    exact this j i₀ (hlink j i₀)
  by_cases h0 : e i₀ ∈ W
  · right
    rw [← Submodule.orthogonal_eq_bot_iff]
    refine (Submodule.eq_bot_iff _).mpr fun v hv => hcomplete v fun i => ?_
    exact Submodule.inner_right_of_mem_orthogonal ((hsame i).mpr h0) hv
  · left
    refine (Submodule.eq_bot_iff _).mpr fun w hw => hcomplete w fun i => ?_
    have hi : e i ∉ W := fun h => h0 ((hsame i).mp h)
    have := (mem_or_mem_orthogonal π hunit r e χ he0 heig hdist hcomplete hW hinv i).resolve_left hi
    exact Submodule.inner_left_of_mem_orthogonal hw this

include hunit in
/-- **Linking is symmetric**: if `⟪e a, π g (e b)⟫ ≠ 0` for some `g`, then `⟪e b, π g' (e a)⟫ ≠ 0` for
some `g'` (take `g' = g⁻¹`). -/
lemma linked_symm (e : ι → H) {a b : ι} (h : ∃ g, ⟪e a, π g (e b)⟫_ℂ ≠ 0) :
    ∃ g, ⟪e b, π g (e a)⟫_ℂ ≠ 0 := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, fun h0 => hg ?_⟩
  have h1 := hunit g (e b) (π g⁻¹ (e a))
  have h2 : π g (π g⁻¹ (e a)) = e a := by simpa using rep_inv_apply π g⁻¹ (e a)
  rw [h2, h0] at h1
  rw [← inner_conj_symm, h1]; simp

end Criterion

/-- Two different real weights give different characters of the rotation group: for `a ≠ b` there is
an angle `θ` with `exp(-i a θ) ≠ exp(-i b θ)` (take `θ = π / (a - b)`, where the two differ by the
factor `exp(-iπ) = -1`). -/
lemma exists_exp_ne {a b : ℝ} (h : a ≠ b) :
    ∃ θ : ℝ, Complex.exp (-((a : ℂ) * (θ : ℂ) * Complex.I)) ≠
      Complex.exp (-((b : ℂ) * (θ : ℂ) * Complex.I)) := by
  have hab : (a : ℂ) - b ≠ 0 := by exact_mod_cast sub_ne_zero.mpr h
  refine ⟨Real.pi / (a - b), fun heq => ?_⟩
  have h1 : Complex.exp (-((a : ℂ) * ((Real.pi / (a - b) : ℝ) : ℂ) * Complex.I)) =
      -Complex.exp (-((b : ℂ) * ((Real.pi / (a - b) : ℝ) : ℂ) * Complex.I)) := by
    have : -((a : ℂ) * ((Real.pi / (a - b) : ℝ) : ℂ) * Complex.I) =
        -((b : ℂ) * ((Real.pi / (a - b) : ℝ) : ℂ) * Complex.I) - (Real.pi : ℂ) * Complex.I := by
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_sub, Complex.exp_pi_mul_I, div_neg, div_one]
  rw [h1] at heq
  have h2 : Complex.exp (-((b : ℂ) * ((Real.pi / (a - b) : ℝ) : ℂ) * Complex.I)) = 0 := by
    linear_combination (-1 / 2 : ℂ) * heq
  exact Complex.exp_ne_zero _ h2

/-- **Irreducibility is inherited along a surjective homomorphism**: if `π` is irreducible and
`φ : G' →* G` is onto, then `π ∘ φ` is irreducible, since it has the same invariant subspaces. -/
theorem isTopologicallyIrreducible_comp {G G' H : Type*} [Monoid G] [Monoid G']
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : ContRepresentation ℂ G H) (φ : G' →* G)
    (hφ : Function.Surjective φ) (hπ : IsTopologicallyIrreducible π) :
    IsTopologicallyIrreducible (ContRepresentation.ofMonoidHom (π.toMonoidHom.comp φ)) := by
  refine ⟨hπ.1, fun W hW hinv => hπ.2 W hW fun g v hv => ?_⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact hinv g' v hv

end Lightlike.Lorentz.SL2R
