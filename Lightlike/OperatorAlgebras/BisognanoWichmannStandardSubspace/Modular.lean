import Lightlike.OperatorAlgebras.Spectral.Unbounded.Basic
import Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.Involution

/-!
# The Tomita involution `S = J D` of a modular pair

Row G1-054 (Bisognano–Wichmann in the standard-subspace form of Brunetti–Guido–Longo).

A *modular pair* is a self-adjoint operator `D` (playing the role of `Δ^{1/2}`) and an antiunitary
involution `J` such that `J D J = D⁻¹` in the form: for `ξ ∈ Dom D`, `J D ξ ∈ Dom D` and
`D (J D ξ) = J ξ`. Then `S = J D` is a closed densely defined antilinear involution
(`ModularPair.tomita`), so by `TomitaData.standardSubspace` its fixed points form a standard
subspace `H(D, J)`. This is the standard subspace whose modular objects are `(D², J)`
(uniqueness is a later file).

## Main definitions

* `ModularPair` — the data `(D, J)` with the relation `J D J = D⁻¹`.
* `ModularPair.op` — the antilinear operator `S = J D` (total function, `0` off `Dom D`).
* `ModularPair.tomita` — `S` as a `TomitaData`.
* `ModularPair.subspace` — the standard subspace `H(D, J)`.
-/

open Filter Topology Complex
open scoped LinearPMap

namespace Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-- A modular pair `(D, J)`: `D` self-adjoint (the role of `Δ^{1/2}`), `J` an antiunitary
involution, and `J D J = D⁻¹` in the form `D (J D ξ) = J ξ` for `ξ ∈ Dom D` (with `J D ξ ∈ Dom D`). -/
structure ModularPair (𝓗 : Type*) [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]
    [CompleteSpace 𝓗] where
  /-- The operator `D`, playing the role of `Δ^{1/2}`. -/
  D : 𝓗 →ₗ.[ℂ] 𝓗
  /-- The antiunitary `J`. -/
  J : 𝓗 ≃ₗᵢ⋆[ℂ] 𝓗
  selfAdjoint : IsSelfAdjoint D
  J_J : ∀ x, J (J x) = x
  intertwine : ∀ (ξ : 𝓗) (hξ : ξ ∈ D.domain),
    ∃ h : J (D ⟨ξ, hξ⟩) ∈ D.domain, D ⟨J (D ⟨ξ, hξ⟩), h⟩ = J ξ

namespace ModularPair

variable (P : ModularPair 𝓗)

/-- The antilinear operator `S = J D`, as a total function (`0` outside `Dom D`). -/
noncomputable def op (x : 𝓗) : 𝓗 :=
  open scoped Classical in
  if h : x ∈ P.D.domain then P.J (P.D ⟨x, h⟩) else 0

lemma op_of_mem {x : 𝓗} (hx : x ∈ P.D.domain) : P.op x = P.J (P.D ⟨x, hx⟩) := by
  simp [op, hx]

lemma op_mem {x : 𝓗} (hx : x ∈ P.D.domain) : P.op x ∈ P.D.domain := by
  rw [P.op_of_mem hx]; exact (P.intertwine x hx).1

lemma op_op {x : 𝓗} (hx : x ∈ P.D.domain) : P.op (P.op x) = x := by
  obtain ⟨h, e⟩ := P.intertwine x hx
  have h1 : P.op x ∈ P.D.domain := P.op_mem hx
  rw [P.op_of_mem h1]
  have : P.D ⟨P.op x, h1⟩ = P.J x := by
    have hh : (⟨P.op x, h1⟩ : P.D.domain) = ⟨P.J (P.D ⟨x, hx⟩), h⟩ := by
      apply Subtype.ext; exact P.op_of_mem hx
    rw [hh]; exact e
  rw [this, P.J_J]

lemma op_add {x : 𝓗} (hx : x ∈ P.D.domain) {y : 𝓗} (hy : y ∈ P.D.domain) :
    P.op (x + y) = P.op x + P.op y := by
  have hxy : x + y ∈ P.D.domain := P.D.domain.add_mem hx hy
  rw [P.op_of_mem hxy, P.op_of_mem hx, P.op_of_mem hy, ← map_add]
  congr 1
  exact P.D.map_add ⟨x, hx⟩ ⟨y, hy⟩

lemma op_smul (c : ℂ) {x : 𝓗} (hx : x ∈ P.D.domain) :
    P.op (c • x) = starRingEnd ℂ c • P.op x := by
  have hcx : c • x ∈ P.D.domain := P.D.domain.smul_mem c hx
  rw [P.op_of_mem hcx, P.op_of_mem hx, ← map_smulₛₗ]
  congr 1
  exact P.D.map_smul c ⟨x, hx⟩

/-- `S = J D` is a closed densely defined antilinear involution. -/
noncomputable def tomita : TomitaData 𝓗 where
  dom := P.D.domain
  op := P.op
  op_add := fun _ hx _ hy => P.op_add hx hy
  op_smul := fun c _ hx => P.op_smul c hx
  op_mem := fun _ hx => P.op_mem hx
  op_op := fun _ hx => P.op_op hx
  dense := P.selfAdjoint.dense_domain
  closed := by
    intro u hu x y hux hy
    have hcl := P.selfAdjoint.isClosed
    rw [Lightlike.OperatorAlgebras.Spectral.Unbounded.isClosed_iff_forall_tendsto] at hcl
    have hD : Tendsto (fun n => P.D (⟨u n, hu n⟩ : P.D.domain)) atTop (𝓝 (P.J y)) := by
      have h1 := (P.J.continuous.tendsto y).comp hy
      refine h1.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [P.op_of_mem (hu n), P.J_J]
    obtain ⟨hx, e⟩ := hcl (fun n => ⟨u n, hu n⟩) x (P.J y) hux hD
    refine ⟨hx, ?_⟩
    rw [P.op_of_mem hx, e, P.J_J]

/-- The standard subspace `H(D, J)` of the modular pair: the fixed points of `S = J D`. -/
noncomputable def subspace : StandardSubspace 𝓗 := P.tomita.standardSubspace

lemma mem_subspace_iff (ξ : 𝓗) :
    ξ ∈ P.subspace.toClosedSubmodule ↔ ∃ h : ξ ∈ P.D.domain, P.J (P.D ⟨ξ, h⟩) = ξ := by
  rw [subspace, TomitaData.mem_standardSubspace_iff]
  constructor
  · rintro ⟨h, e⟩
    exact ⟨h, by rw [← P.op_of_mem h]; exact (e : P.op ξ = ξ)⟩
  · rintro ⟨h, e⟩
    exact ⟨h, by show P.op ξ = ξ; rw [P.op_of_mem h]; exact e⟩

end ModularPair

end Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.D := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.D
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.J := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.J
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.J_J := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.J_J
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.intertwine := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.intertwine
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.mem_subspace_iff := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.mem_subspace_iff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.op := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.op
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.op_add := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.op_add
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.op_mem := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.op_mem
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.op_of_mem := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.op_of_mem
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.op_op := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.op_op
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.op_smul := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.op_smul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.selfAdjoint := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.selfAdjoint
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.subspace := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.subspace
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.ModularPair.tomita := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.ModularPair.tomita
