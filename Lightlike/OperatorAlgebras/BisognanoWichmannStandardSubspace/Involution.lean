import Mathlib.Analysis.InnerProductSpace.StandardSubspace

/-!
# Standard subspaces from closed densely defined antilinear involutions

Row G1-054 (Bisognano–Wichmann in the standard-subspace form of Brunetti–Guido–Longo).

R. Longo, "Lectures on Conformal Nets, Part I", Section 2.1, Lemma 2.1.1 (as recorded in
`docs/notes/op3-finite.md`): the fixed points of a closed densely defined antilinear involution `S`
form a standard subspace `H = ker (1 - S)`, and `H + iH = Dom S`.

Here this is proved for any complex inner product space, with `S` given as a total function that
is only constrained on a dense complex subspace `dom` (`TomitaData`). The finite-dimensional case
of `Lightlike/OperatorAlgebras/FiniteStandard.lean` is the special case `dom = ⊤`; the case used
for the wedge is `S = J Δ^{1/2}` (later files of this row).

## Main definitions

* `TomitaData 𝓗` — a dense subspace with a closed antilinear involution of it.
* `TomitaData.standardSubspace` — its fixed points, as Mathlib's `StandardSubspace`.
-/

open Filter Topology Complex

namespace Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]

/-- A closed, densely defined antilinear involution `S` of a complex inner product space: a dense
complex subspace `dom`, a map `op` (only its values on `dom` matter) which is additive and
conjugate-homogeneous on `dom`, maps `dom` into itself, squares to the identity there, and has a
closed graph. -/
structure TomitaData (𝓗 : Type*) [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] where
  /-- The domain of `S`. -/
  dom : Submodule ℂ 𝓗
  /-- The operator `S`, meaningful on `dom`. -/
  op : 𝓗 → 𝓗
  op_add : ∀ x ∈ dom, ∀ y ∈ dom, op (x + y) = op x + op y
  op_smul : ∀ (c : ℂ), ∀ x ∈ dom, op (c • x) = starRingEnd ℂ c • op x
  op_mem : ∀ x ∈ dom, op x ∈ dom
  op_op : ∀ x ∈ dom, op (op x) = x
  dense : Dense (dom : Set 𝓗)
  closed : ∀ u : ℕ → 𝓗, (∀ n, u n ∈ dom) → ∀ x y : 𝓗, Tendsto u atTop (𝓝 x) →
    Tendsto (fun n => op (u n)) atTop (𝓝 y) → x ∈ dom ∧ op x = y

namespace TomitaData

variable (T : TomitaData 𝓗)

lemma op_zero : T.op 0 = 0 := by
  have := T.op_smul 0 0 T.dom.zero_mem
  simpa using this

lemma op_neg {x : 𝓗} (hx : x ∈ T.dom) : T.op (-x) = -T.op x := by
  have := T.op_smul (-1) x hx
  simpa using this

lemma op_sub {x y : 𝓗} (hx : x ∈ T.dom) (hy : y ∈ T.dom) : T.op (x - y) = T.op x - T.op y := by
  rw [sub_eq_add_neg, T.op_add x hx (-y) (T.dom.neg_mem hy), T.op_neg hy, sub_eq_add_neg]

/-- The fixed points of `S`, a real subspace. -/
def fixedSubmodule : Submodule ℝ 𝓗 where
  carrier := {ξ | ξ ∈ T.dom ∧ T.op ξ = ξ}
  add_mem' := fun ⟨h1, h2⟩ ⟨h3, h4⟩ =>
    ⟨T.dom.add_mem h1 h3, by rw [T.op_add _ h1 _ h3, h2, h4]⟩
  zero_mem' := ⟨T.dom.zero_mem, T.op_zero⟩
  smul_mem' r ξ hξ := by
    obtain ⟨h1, h2⟩ := hξ
    have e : r • ξ = (r : ℂ) • ξ := RCLike.real_smul_eq_coe_smul r ξ
    refine ⟨?_, ?_⟩
    · rw [e]; exact T.dom.smul_mem _ h1
    · show T.op (r • ξ) = r • ξ
      rw [e, T.op_smul _ _ h1, h2, Complex.conj_ofReal]

lemma mem_fixedSubmodule_iff (ξ : 𝓗) : ξ ∈ T.fixedSubmodule ↔ ξ ∈ T.dom ∧ T.op ξ = ξ := Iff.rfl

/-- The fixed-point subspace is closed, because the graph of `S` is closed. -/
lemma isClosed_fixed : IsClosed (T.fixedSubmodule : Set 𝓗) := by
  refine isSeqClosed_iff_isClosed.mp fun u x hu hx => ?_
  have h := T.closed u (fun n => (hu n).1) x x hx (hx.congr fun n => ((hu n).2).symm)
  exact h

/-- The fixed points of `S` as a closed real subspace. -/
def fixedClosed : ClosedSubmodule ℝ 𝓗 := ⟨T.fixedSubmodule, T.isClosed_fixed⟩

lemma mem_fixedClosed_iff (ξ : 𝓗) : ξ ∈ T.fixedClosed ↔ ξ ∈ T.dom ∧ T.op ξ = ξ := Iff.rfl

open ClosedSubmodule in
lemma mem_mulI_iff (ξ : 𝓗) :
    ξ ∈ T.fixedClosed.mulI ↔ (-Complex.I) • ξ ∈ T.dom ∧ T.op ((-Complex.I) • ξ) = (-Complex.I) • ξ := by
  rw [ClosedSubmodule.mem_mapEquiv_iff, scalarSMulCLE_symm_apply]
  rfl

lemma separating : T.fixedClosed ⊓ T.fixedClosed.mulI = ⊥ := by
  refine eq_bot_iff.mpr fun ξ hξ => ?_
  obtain ⟨h1, h2⟩ := ClosedSubmodule.mem_inf.mp hξ
  obtain ⟨hd, hS⟩ := (T.mem_fixedClosed_iff ξ).mp h1
  obtain ⟨-, h3⟩ := (T.mem_mulI_iff ξ).mp h2
  rw [T.op_smul _ _ hd, hS, map_neg, Complex.conj_I, neg_neg] at h3
  have h4 : (Complex.I - -Complex.I) • ξ = 0 := by rw [sub_smul, h3, sub_self]
  have hne : Complex.I - -Complex.I ≠ 0 := by
    rw [sub_neg_eq_add, ← two_mul]; exact mul_ne_zero two_ne_zero Complex.I_ne_zero
  rw [(smul_eq_zero.mp h4).resolve_left hne]
  exact zero_mem _

/-- Every vector of `dom` is a sum `a + i b` of fixed vectors (`a = (ξ + Sξ)/2`,
`b = (ξ - Sξ)/(2i)`), so `H + iH ⊇ Dom S`. -/
lemma dom_subset_sup {ξ : 𝓗} (hξ : ξ ∈ T.dom) :
    ξ ∈ (T.fixedClosed.toSubmodule ⊔ T.fixedClosed.mulI.toSubmodule : Submodule ℝ 𝓗) := by
  have hSξ := T.op_mem ξ hξ
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  refine Submodule.mem_sup.mpr ⟨(1 / 2 : ℂ) • (ξ + T.op ξ), ?_, (1 / 2 : ℂ) • (ξ - T.op ξ), ?_, ?_⟩
  · refine (T.mem_fixedClosed_iff _).mpr ⟨T.dom.smul_mem _ (T.dom.add_mem hξ hSξ), ?_⟩
    rw [T.op_smul _ _ (T.dom.add_mem hξ hSξ), T.op_add _ hξ _ hSξ, T.op_op _ hξ, hhalf, add_comm]
  · refine (T.mem_mulI_iff _).mpr ⟨T.dom.smul_mem _ (T.dom.smul_mem _ (T.dom.sub_mem hξ hSξ)), ?_⟩
    have hw := T.dom.sub_mem hξ hSξ
    rw [T.op_smul _ _ (T.dom.smul_mem _ hw), T.op_smul _ _ hw, T.op_sub hξ hSξ, T.op_op _ hξ,
      hhalf, map_neg, Complex.conj_I, smul_smul, smul_smul]
    rw [show -(-Complex.I) * (1 / 2 : ℂ) = (-Complex.I * (1 / 2)) * (-1) by ring, mul_smul,
      neg_one_smul, neg_sub]
  · rw [← smul_add]
    rw [show ξ + T.op ξ + (ξ - T.op ξ) = (2 : ℂ) • ξ by rw [two_smul]; abel, smul_smul]
    norm_num

lemma cyclic : T.fixedClosed ⊔ T.fixedClosed.mulI = ⊤ := by
  refine eq_top_iff.mpr fun ξ _ => ?_
  rw [ClosedSubmodule.mem_sup]
  have hsub : (T.dom : Set 𝓗) ⊆
      (T.fixedClosed.toSubmodule ⊔ T.fixedClosed.mulI.toSubmodule).carrier :=
    fun x hx => T.dom_subset_sup hx
  have := closure_mono hsub
  rw [T.dense.closure_eq] at this
  exact this (Set.mem_univ ξ)

/-- **Longo, Lemma 2.1.1.** The fixed points of a closed densely defined antilinear involution form
a standard subspace of Mathlib's `StandardSubspace`. -/
def standardSubspace : StandardSubspace 𝓗 where
  toClosedSubmodule := T.fixedClosed
  IsSeparating := T.separating
  IsCyclic := T.cyclic

lemma mem_standardSubspace_iff (ξ : 𝓗) :
    ξ ∈ T.standardSubspace.toClosedSubmodule ↔ ξ ∈ T.dom ∧ T.op ξ = ξ := Iff.rfl

end TomitaData

end Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.closed := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.closed
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.cyclic := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.cyclic
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.dense := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.dense
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.dom := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.dom
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.dom_subset_sup := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.dom_subset_sup
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.fixedClosed := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.fixedClosed
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.fixedSubmodule := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.fixedSubmodule
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.isClosed_fixed := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.isClosed_fixed
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.mem_fixedClosed_iff := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.mem_fixedClosed_iff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.mem_fixedSubmodule_iff := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.mem_fixedSubmodule_iff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.mem_mulI_iff := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.mem_mulI_iff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.mem_standardSubspace_iff := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.mem_standardSubspace_iff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.op := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.op
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.op_add := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.op_add
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.op_mem := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.op_mem
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.op_neg := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.op_neg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.op_op := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.op_op
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.op_smul := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.op_smul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.op_sub := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.op_sub
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.op_zero := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.op_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.separating := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.separating
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.TomitaData.standardSubspace := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.TomitaData.standardSubspace
