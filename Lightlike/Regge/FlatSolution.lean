import Lightlike.Regge.Embedded
import Lightlike.Regge.ReggeEquations

/-!
# Flat space solves Regge's equations

A geometric triangulation of a region of 3-space (`IsGeometric`) induces edge lengths, and Regge's
equations (`Lightlike/Regge/ReggeEquations.lean`) need those lengths to be non-degenerate
(`LengthsNondeg`: positive lengths, face areas and volumes). This file shows that they are, through
Gram determinants: for a triangle with edge vectors `u, w` from one vertex,
`16 · area² = 4 det Gram(u, w)`, and for a tetrahedron with edge vectors `u, v, w`,
`V² = det Gram(u, v, w) / 36`. Affine independence makes the edge vectors linearly independent, so
the Gram determinants are positive (`Matrix.posDef_gram_of_linearIndependent`).

## Main results

* `IsGeometric.lengthsNondeg`: the edge lengths of a geometric triangulation are non-degenerate.
* `IsGeometric.reggeAction_stationary`: **flat space solves Regge's equations**. For a geometric
  triangulation of a region of 3-space that is an edge-manifold, the Regge action of the induced
  lengths is stationary under every variation of the lengths that keeps the boundary lengths
  fixed.
-/

open Real Finset InnerProductSpace Module Matrix

namespace Lightlike.Regge

open Lightlike.PR (Complex3 vol2)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A squared distance through inner products of the vectors from a base point `o`. -/
theorem dist_sq_eq_inner (a b o : E) :
    dist a b ^ 2 = ⟪a - o, a - o⟫_ℝ - 2 * ⟪a - o, b - o⟫_ℝ + ⟪b - o, b - o⟫_ℝ := by
  rw [dist_eq_norm, ← sub_sub_sub_cancel_right a b o, norm_sub_sq_real,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- **A triangle's area from its Gram determinant**: for vertices `P₀, P₁, P₂` with
`u = P₁ - P₀`, `w = P₂ - P₀`, `heron = 4 (⟪u,u⟫⟪w,w⟫ - ⟪u,w⟫²)`. -/
theorem heron_dist_eq (P₀ P₁ P₂ : E) :
    heron (dist P₀ P₁) (dist P₁ P₂) (dist P₂ P₀) =
      4 * (⟪P₁ - P₀, P₁ - P₀⟫_ℝ * ⟪P₂ - P₀, P₂ - P₀⟫_ℝ - ⟪P₁ - P₀, P₂ - P₀⟫_ℝ ^ 2) := by
  have h : ∀ a b c : ℝ, heron a b c =
      2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - ((a ^ 2) ^ 2 + (b ^ 2) ^ 2 + (c ^ 2) ^ 2) :=
    fun a b c => by unfold heron; ring
  rw [h, dist_sq_eq_inner P₀ P₁ P₀, dist_sq_eq_inner P₁ P₂ P₀, dist_sq_eq_inner P₂ P₀ P₀]
  simp only [sub_self, inner_zero_left, inner_zero_right]
  ring

/-- **A tetrahedron's volume from its Gram determinant**: for vertices `p, q, r, s` with
`u = q - p`, `v = r - p`, `w = s - p`, `V² = det Gram(u, v, w) / 36` (`Lightlike.PR.vol2`, labelled
`A, B, C, D = p, q, r, s`). -/
theorem vol2_dist_eq (p q r s : E) :
    vol2 (dist p q) (dist q r) (dist r p) (dist r s) (dist p s) (dist q s) =
      (gram ℝ ![q - p, r - p, s - p]).det / 36 := by
  unfold vol2
  rw [dist_sq_eq_inner p q p, dist_sq_eq_inner q r p, dist_sq_eq_inner r p p,
    dist_sq_eq_inner r s p, dist_sq_eq_inner p s p, dist_sq_eq_inner q s p, det_fin_three]
  simp only [gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sub_self, inner_zero_left, inner_zero_right,
    real_inner_comm (q - p) (r - p), real_inner_comm (q - p) (s - p),
    real_inner_comm (r - p) (s - p)]
  ring

/-- Three labelled points are affinely independent iff their two edge vectors from the first are
linearly independent. -/
theorem affIndep_three_iff (P₀ P₁ P₂ : E) :
    AffineIndependent ℝ ![P₀, P₁, P₂] ↔ LinearIndependent ℝ ![P₁ - P₀, P₂ - P₀] := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin 3),
    ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
  have : ((fun i : {x : Fin 3 // x ≠ 0} => ![P₀, P₁, P₂] ↑i -ᵥ ![P₀, P₁, P₂] 0) ∘
      finSuccAboveEquiv (0 : Fin 3)) = ![P₁ - P₀, P₂ - P₀] := by
    ext i
    fin_cases i <;> simp [finSuccAboveEquiv, vsub_eq_sub]
  rw [this]

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- A face of a non-degenerate tetrahedron is non-degenerate: affine independence of the vertex
set `t` gives linear independence of the two edge vectors of any three distinct vertices of `t`. -/
theorem linIndep_face (x : V → E) {t : Finset V} (h : AffineIndependent ℝ fun v : t => x v)
    {a b c : V} (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearIndependent ℝ ![x b - x a, x c - x a] := by
  let f : Fin 3 → t := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff, hab.symm, hac.symm, hbc.symm]
  have h3 : AffineIndependent ℝ ![x a, x b, x c] := by
    have := h.comp_embedding ⟨f, hf⟩
    convert this using 1
    ext i
    fin_cases i <;> rfl
  exact (affIndep_three_iff _ _ _).mp h3

/-- **The edge lengths of a geometric triangulation are non-degenerate**: positive lengths, face
areas and volumes. -/
theorem IsGeometric.lengthsNondeg {K : Complex3 V} {x : V → E} (hK : IsGeometric K x) :
    LengthsNondeg K (ofDist fun u v => dist (x u) (x v)) := by
  have hℓ : ∀ u v, u ≠ v → ofDist (fun u v => dist (x u) (x v)) {u, v} = dist (x u) (x v) :=
    fun u v h => ofDist_pair (d := fun u v => dist (x u) (x v)) (fun u => dist_self (x u))
      (fun u v => dist_comm (x u) (x v)) h
  intro t ht
  have hA := hK.nondeg t ht
  have hinj := hA.injective
  have hx : ∀ {a b : V}, a ∈ t → b ∈ t → a ≠ b → x a ≠ x b := fun ha hb hab hx =>
    hab (congrArg Subtype.val (@hinj ⟨_, ha⟩ ⟨_, hb⟩ hx))
  refine ⟨fun e he => ?_, fun f hf => ?_, ?_⟩
  · obtain ⟨hs, h2⟩ := mem_powersetCard.mp he
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp h2
    rw [hℓ a b hab]
    exact dist_pos.mpr (hx (hs (by simp)) (hs (by simp)) hab)
  · obtain ⟨hs, h3⟩ := mem_powersetCard.mp hf
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp h3
    have ha := hs (by simp : a ∈ ({a, b, c} : Finset V))
    have hb := hs (by simp : b ∈ ({a, b, c} : Finset V))
    have hc := hs (by simp : c ∈ ({a, b, c} : Finset V))
    rw [triH_eq _ hab hac hbc, hℓ a b hab, hℓ b c hbc, hℓ c a hac.symm, heron_dist_eq]
    have := (posDef_gram_of_linearIndependent (linIndep_face x hA ha hb hc hab hac hbc)).det_pos
    rw [det_fin_two] at this
    simp only [gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      real_inner_comm (x b - x a) (x c - x a)] at this
    nlinarith
  · obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ := exists_label ht
    rw [tetV2_eq _ hpq hpr hps hqr hqs hrs, hℓ p q hpq, hℓ q r hqr, hℓ r p hpr.symm,
      hℓ r s hrs, hℓ p s hps, hℓ q s hqs, vol2_dist_eq]
    have := (posDef_gram_of_linearIndependent
      (linIndep_of_affIndep x hpq hpr hps hqr hqs hrs hA)).det_pos
    positivity

/-- **Flat space solves Regge's equations.** Let `K` be an edge-manifold and `x` a geometric
triangulation of a region of a 3-dimensional real inner product space, with the induced edge
lengths. Then the Regge action is stationary under every variation of the edge lengths that keeps
the boundary lengths fixed: the derivative along `ℓ + τ v` at `τ = 0` is zero. -/
theorem IsGeometric.reggeAction_stationary [FiniteDimensional ℝ E] (hE : finrank ℝ E = 3)
    {K : Complex3 V} {x : V → E} (hK : IsGeometric K x) (hM : IsEdgeManifold K)
    (v : Finset V → ℝ) (hv : ∀ e ∈ bdryEdges K, v e = 0) :
    HasDerivAt (fun τ => reggeAction K fun e => ofDist (fun u v => dist (x u) (x v)) e + τ * v e)
      0 0 :=
  (reggeAction_stationary_iff hK.lengthsNondeg).mpr (fun _ he => hK.deficit_eq_zero hE hM he) v hv

end Lightlike.Regge
