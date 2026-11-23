import Lightlike.Rows.G1_054.Modular
import Lightlike.Rows.G1_054.BoundedTransform
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Uniqueness of the modular objects of a standard subspace

Row G1-054 (Bisognano–Wichmann in the standard-subspace form of Brunetti–Guido–Longo).

Two *positive* modular pairs `(D, J)`, `(D', J')` (`D ≥ 0`) with the same domain and the same
Tomita operator `S = J D = J' D'` on it are equal: `D = D'` and `J = J'`. This is the uniqueness
of the polar decomposition `S = J Δ^{1/2}`, proved here without the spectral theorem:

* `‖D x‖ = ‖S x‖ = ‖D' x‖`, so by polarization the forms `⟪D x, D z⟫` and `⟪D' x, D' z⟫` agree,
  hence the weak solutions of `(1 + D²) x = y` agree (`solMap`);
* the bounded operators `A = D (1 + D²)⁻¹`, `A' = D' (1 + D'²)⁻¹` are positive with `A² = A'²`
  (matrix elements `⟪D x, D z⟫`), so `A = A'` by uniqueness of the positive square root
  (`CFC.sq_eq_sq_iff`);
* the range of `A` is dense (`D` is injective), and `J = J'` on it, so `J = J'`, then `D = D'`.

## Main results

* `ModularPair.IsPositive` — `D ≥ 0`.
* `ModularPair.ext_of_op` — the uniqueness theorem.
-/

open Filter Topology Complex
open scoped LinearPMap InnerProductSpace

set_option linter.unusedSectionVars false

namespace Lightlike.Rows.G1_054

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-- Polarization: the inner product of the images under a linear map is determined by the norms. -/
lemma inner_eq_of_norm_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (f g : M →ₗ[ℂ] 𝓗)
    (h : ∀ w, ‖f w‖ = ‖g w‖) (x z : M) : ⟪f x, f z⟫_ℂ = ⟪g x, g z⟫_ℂ := by
  rw [inner_eq_sum_norm_sq_div_four (f x) (f z), inner_eq_sum_norm_sq_div_four (g x) (g z)]
  have e1 : ‖f x + f z‖ = ‖g x + g z‖ := by rw [← map_add, ← map_add]; exact h _
  have e2 : ‖f x - f z‖ = ‖g x - g z‖ := by rw [← map_sub, ← map_sub]; exact h _
  have e3 : ‖f x - (RCLike.I : ℂ) • f z‖ = ‖g x - (RCLike.I : ℂ) • g z‖ := by
    rw [← map_smul, ← map_smul, ← map_sub, ← map_sub]; exact h _
  have e4 : ‖f x + (RCLike.I : ℂ) • f z‖ = ‖g x + (RCLike.I : ℂ) • g z‖ := by
    rw [← map_smul, ← map_smul, ← map_add, ← map_add]; exact h _
  rw [e1, e2, e3, e4]

/-- The restriction of `tot D` to a submodule of the domain, as a linear map. -/
noncomputable def totLin (D : 𝓗 →ₗ.[ℂ] 𝓗) (M : Submodule ℂ 𝓗) (hM : ∀ x ∈ M, x ∈ D.domain) :
    M →ₗ[ℂ] 𝓗 where
  toFun x := tot D x
  map_add' x y := tot_add D (hM _ x.2) (hM _ y.2)
  map_smul' c x := tot_smul D c (hM _ x.2)

variable {D : 𝓗 →ₗ.[ℂ] 𝓗}

/-- The weak solution `x = (1 + D²)⁻¹ y` (a chosen one; unique by `IsSol.unique`). -/
noncomputable def solMap (hD : IsSelfAdjoint D) (y : 𝓗) : 𝓗 := Classical.choose (exists_isSol hD y)

lemma isSol_solMap (hD : IsSelfAdjoint D) (y : 𝓗) : IsSol D y (solMap hD y) :=
  Classical.choose_spec (exists_isSol hD y)

lemma solMap_eq (hD : IsSelfAdjoint D) {y x : 𝓗} (h : IsSol D y x) : solMap hD y = x :=
  (isSol_solMap hD y).unique h

/-- The bounded operator `A = D (1 + D²)⁻¹`. -/
noncomputable def Amap (hD : IsSelfAdjoint D) : 𝓗 →L[ℂ] 𝓗 :=
  LinearMap.mkContinuous
    { toFun := fun y => tot D (solMap hD y)
      map_add' := fun y1 y2 => by
        have h := (isSol_solMap hD y1).add (isSol_solMap hD y2)
        rw [solMap_eq hD h]
        exact tot_add D (isSol_solMap hD y1).1 (isSol_solMap hD y2).1
      map_smul' := fun c y => by
        have h := (isSol_solMap hD y).smul c
        simp only [RingHom.id_apply]
        rw [solMap_eq hD h]
        exact tot_smul D c (isSol_solMap hD y).1 }
    1 (fun y => by rw [one_mul]; exact (isSol_solMap hD y).norm_apply_le)

lemma Amap_apply (hD : IsSelfAdjoint D) (y : 𝓗) : Amap hD y = tot D (solMap hD y) := rfl

lemma Amap_symm (hD : IsSelfAdjoint D) (y1 y2 : 𝓗) :
    ⟪Amap hD y1, y2⟫_ℂ = ⟪y1, Amap hD y2⟫_ℂ := by
  have hs1 := isSol_solMap hD y1
  have hs2 := isSol_solMap hD y2
  rw [Amap_apply, Amap_apply]
  obtain ⟨m1, d1⟩ := hs1.apply_mem hD
  obtain ⟨m2, d2⟩ := hs2.apply_mem hD
  generalize solMap hD y1 = x1 at hs1 m1 d1 ⊢
  generalize solMap hD y2 = x2 at hs2 m2 d2 ⊢
  have ey1 : y1 = x1 + tot D (tot D x1) := by rw [d1]; abel
  have ey2 : y2 = x2 + tot D (tot D x2) := by rw [d2]; abel
  rw [ey1, ey2, inner_add_right, inner_add_left, sa_inner hD hs1.1 hs2.1, sa_inner hD m1 m2]

/-- Matrix elements of `A²`: `⟪A² y₁, y₂⟫ = ⟪D x₁, D x₂⟫` with `x_i = (1 + D²)⁻¹ y_i`. -/
lemma Amap_sq_inner (hD : IsSelfAdjoint D) (y1 y2 : 𝓗) :
    ⟪(Amap hD ^ 2) y1, y2⟫_ℂ = ⟪tot D (solMap hD y1), tot D (solMap hD y2)⟫_ℂ := by
  rw [pow_two]
  show ⟪Amap hD (Amap hD y1), y2⟫_ℂ = _
  rw [Amap_symm]
  rfl

/-- `A ≥ 0` if `D ≥ 0`. -/
lemma Amap_isPositive (hD : IsSelfAdjoint D)
    (hpos : ∀ x ∈ D.domain, 0 ≤ (⟪x, tot D x⟫_ℂ).re) : (Amap hD).IsPositive := by
  refine ContinuousLinearMap.isPositive_def.mpr ⟨fun y1 y2 => Amap_symm hD y1 y2, fun y => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  have hs := isSol_solMap hD y
  obtain ⟨m, d⟩ := hs.apply_mem hD
  rw [Amap_apply]
  generalize solMap hD y = x at hs m d ⊢
  have ey : y = x + tot D (tot D x) := by rw [d]; abel
  have e : ⟪tot D x, y⟫_ℂ = ⟪x, tot D x⟫_ℂ + ⟪tot D x, tot D (tot D x)⟫_ℂ := by
    rw [ey, inner_add_right, sa_inner hD hs.1 hs.1]
  show 0 ≤ (⟪tot D x, y⟫_ℂ).re
  rw [e, Complex.add_re]
  exact add_nonneg (hpos x hs.1) (hpos _ m)

/-- The range of `A` is dense, if `D` is injective. -/
lemma dense_range_Amap (hD : IsSelfAdjoint D) (hinj : ∀ x ∈ D.domain, tot D x = 0 → x = 0) :
    Dense (Set.range (Amap hD)) := by
  have hK : (LinearMap.range (Amap hD : 𝓗 →ₗ[ℂ] 𝓗)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_orthogonal] at hv
    have h1 : Amap hD v = 0 := by
      have h2 : ⟪Amap hD v, Amap hD v⟫_ℂ = 0 := by
        have := hv (Amap hD (Amap hD v)) ⟨Amap hD v, rfl⟩
        rwa [Amap_symm] at this
      exact inner_self_eq_zero.mp h2
    have h1' : tot D (solMap hD v) = 0 := h1
    have hx0 : solMap hD v = 0 := hinj _ (isSol_solMap hD v).1 h1'
    obtain ⟨-, d⟩ := (isSol_solMap hD v).apply_mem hD
    have z0 : tot D 0 = 0 := by
      rw [tot_of_mem D D.domain.zero_mem]; exact D.toFun.map_zero
    rw [h1', hx0, z0, sub_zero] at d
    exact d.symm
  have hc : closure (Set.range (Amap hD)) = Set.univ := by
    have e : Set.range (Amap hD) = (LinearMap.range (Amap hD : 𝓗 →ₗ[ℂ] 𝓗) : Set 𝓗) :=
      (LinearMap.coe_range _).symm
    rw [e, ← Submodule.topologicalClosure_coe, hK]
    rfl
  exact dense_iff_closure_eq.mpr hc

namespace ModularPair

variable (P : ModularPair 𝓗)

/-- Positivity of the modular operator: `0 ≤ re ⟪x, D x⟫` on the domain. -/
def IsPositive : Prop := ∀ x ∈ P.D.domain, 0 ≤ (⟪x, tot P.D x⟫_ℂ).re

lemma op_eq {x : 𝓗} (hx : x ∈ P.D.domain) : P.op x = P.J (tot P.D x) := by
  rw [P.op_of_mem hx, tot_of_mem _ hx]

lemma tot_eq_J_op {x : 𝓗} (hx : x ∈ P.D.domain) : tot P.D x = P.J (P.op x) := by
  rw [P.op_eq hx, P.J_J]

lemma norm_tot {x : 𝓗} (hx : x ∈ P.D.domain) : ‖tot P.D x‖ = ‖P.op x‖ := by
  rw [P.op_eq hx]; exact (P.J.norm_map _).symm

lemma tot_op {x : 𝓗} (hx : x ∈ P.D.domain) : tot P.D (P.op x) = P.J x := by
  obtain ⟨h, e⟩ := P.intertwine x hx
  have h1 := P.op_mem hx
  rw [tot_of_mem _ h1]
  have hh : (⟨P.op x, h1⟩ : P.D.domain) = ⟨P.J (P.D ⟨x, hx⟩), h⟩ :=
    Subtype.ext (P.op_of_mem hx)
  rw [hh]; exact e

/-- `D` is injective on its domain (a consequence of `J D J = D⁻¹`). -/
lemma tot_eq_zero {x : 𝓗} (hx : x ∈ P.D.domain) (h : tot P.D x = 0) : x = 0 := by
  have h1 : P.op x = 0 := by rw [P.op_eq hx, h, map_zero]
  have h2 := P.tot_op hx
  have z0 : tot P.D 0 = 0 := by
    rw [tot_of_mem _ P.D.domain.zero_mem]; exact P.D.toFun.map_zero
  rw [h1, z0] at h2
  exact P.J.injective (h2.symm.trans (map_zero P.J).symm)

end ModularPair

/-- **Uniqueness of the modular objects.** Two positive modular pairs with the same domain and
the same Tomita operator `S = J D` on it coincide: `D = D'` and `J = J'`. -/
theorem ModularPair.ext_of_op {P Q : ModularPair 𝓗} (hP : P.IsPositive) (hQ : Q.IsPositive)
    (hdom : P.D.domain = Q.D.domain) (hop : ∀ x ∈ P.D.domain, P.op x = Q.op x) :
    P.D = Q.D ∧ P.J = Q.J := by
  have memQ : ∀ x, x ∈ P.D.domain → x ∈ Q.D.domain := fun x hx => hdom ▸ hx
  have memP : ∀ x, x ∈ Q.D.domain → x ∈ P.D.domain := fun x hx => hdom.symm ▸ hx
  have hinner : ∀ x ∈ P.D.domain, ∀ z ∈ P.D.domain,
      ⟪tot P.D x, tot P.D z⟫_ℂ = ⟪tot Q.D x, tot Q.D z⟫_ℂ := by
    intro x hx z hz
    exact inner_eq_of_norm_eq (totLin P.D P.D.domain (fun _ h => h))
      (totLin Q.D P.D.domain memQ)
      (fun w => by
        show ‖tot P.D w‖ = ‖tot Q.D w‖
        rw [P.norm_tot w.2, Q.norm_tot (memQ _ w.2), hop _ w.2]) ⟨x, hx⟩ ⟨z, hz⟩
  have transfer : ∀ {y x : 𝓗}, IsSol P.D y x → IsSol Q.D y x := fun h =>
    ⟨memQ _ h.1, fun z hz => by
      have := h.2 z (memP _ hz)
      rwa [hinner _ h.1 _ (memP _ hz)] at this⟩
  have hsol : ∀ y, solMap Q.selfAdjoint y = solMap P.selfAdjoint y := fun y =>
    solMap_eq Q.selfAdjoint (transfer (isSol_solMap P.selfAdjoint y))
  have hsq : Amap P.selfAdjoint ^ 2 = Amap Q.selfAdjoint ^ 2 := by
    refine ContinuousLinearMap.ext fun y => ext_inner_right ℂ fun z => ?_
    rw [Amap_sq_inner, Amap_sq_inner, hsol, hsol]
    exact hinner _ (isSol_solMap _ y).1 _ (isSol_solMap _ z).1
  have hA : Amap P.selfAdjoint = Amap Q.selfAdjoint := by
    have a1 : 0 ≤ Amap P.selfAdjoint :=
      ContinuousLinearMap.nonneg_iff_isPositive.mpr (Amap_isPositive _ hP)
    have a2 : 0 ≤ Amap Q.selfAdjoint :=
      ContinuousLinearMap.nonneg_iff_isPositive.mpr (Amap_isPositive _ hQ)
    exact (CFC.sq_eq_sq_iff _ _ a1 a2).mp hsq
  have hJA : ∀ y, P.J (Amap P.selfAdjoint y) = Q.J (Amap P.selfAdjoint y) := by
    intro y
    have hx := (isSol_solMap P.selfAdjoint y).1
    have hAy := DFunLike.congr_fun hA y
    rw [Amap_apply, Amap_apply, hsol] at hAy
    rw [Amap_apply, ← P.op_eq hx, hop _ hx, Q.op_eq (memQ _ hx), hAy]
  have hJ : P.J = Q.J := by
    have hc : IsClosed {v : 𝓗 | P.J v = Q.J v} := isClosed_eq P.J.continuous Q.J.continuous
    have hsub : Set.range (Amap P.selfAdjoint) ⊆ {v | P.J v = Q.J v} := by
      rintro _ ⟨y, rfl⟩; exact hJA y
    have := closure_minimal hsub hc
    rw [(dense_range_Amap P.selfAdjoint fun x hx h => P.tot_eq_zero hx h).closure_eq] at this
    exact LinearIsometryEquiv.ext fun v => this (Set.mem_univ v)
  refine ⟨LinearPMap.ext hdom ?_, hJ⟩
  intro x hx hy
  rw [← tot_of_mem _ hx, ← tot_of_mem _ hy, P.tot_eq_J_op hx, Q.tot_eq_J_op hy, hop _ hx, hJ]

end Lightlike.Rows.G1_054
