import Lightlike.OperatorAlgebras.SecondQuantFinite
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NoncommRing

/-!
# `dΓ` of finite-rank operators on any inner product space

J. Dereziński, arXiv:math-ph/0511030, Theorem 17, p. 22 (the CCR and the CAR for `a(w)`, `a*(w)`) and Theorem 18 (2),
(4), p. 22 (`[dΓ(h), a(w)] = -a(h* w)`, `[dΓ(h), a*(w)] = a*(hw)`) (read), basis-free: `Z` is any complex inner product
space, `a* : Z → R` is linear and `a : Z → R` antilinear with `a(w) a*(v) = ⟪w, v⟫ + ε a*(v) a(w)`, and for a
finite-rank `h = ∑ₖ |uₖ⟩⟨vₖ|` (`h w = ∑ₖ ⟪vₖ, w⟫ uₖ`, `h* w = ∑ₖ ⟪uₖ, w⟫ vₖ`), `dΓ(h) = ∑ₖ a*(uₖ) a(vₖ)`.

* `IsFieldAlgebra ε cre ann`;
* `rankOp u v`, `rankOpAdj u v`, `dGammaRank cre ann u v`;
* `dGammaRank_commutator_creation`: `[dΓ(h), a*(w)] = a*(h w)`;
* `dGammaRank_commutator_annihilation`: `[dΓ(h), a(w)] = -a(h* w)`;
* `compLeft`, `rankOp_comp`, `dGammaRank_commutator`: `[dΓ(h), dΓ(h')] = dΓ(h h') - dΓ(h' h)` (Theorem 13 (1), p. 19).
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.SecondQuantFinite

variable {R : Type*} [Ring R] [Algebra ℂ R] {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]

/-- **A field algebra** with sign `ε` over `Z` (Dereziński, Theorem 17, p. 22): a linear `a*`, an antilinear `a`,
`ε² = 1`, `a(w) a*(v) = ⟪w, v⟫ + ε a*(v) a(w)`, `a*(v) a*(u) = ε a*(u) a*(v)`, `a(v) a(u) = ε a(u) a(v)`. -/
structure IsFieldAlgebra (ε : ℂ) (cre : Z →ₗ[ℂ] R) (ann : Z →ₗ⋆[ℂ] R) : Prop where
  /-- `ε² = 1`. -/
  eps_sq : ε * ε = 1
  /-- `a(w) a*(v) = ⟪w, v⟫ + ε a*(v) a(w)`. -/
  ann_cre : ∀ w v, ann w * cre v = algebraMap ℂ R ⟪w, v⟫_ℂ + ε • (cre v * ann w)
  /-- `a*(v) a*(u) = ε a*(u) a*(v)`. -/
  cre_cre : ∀ u v, cre v * cre u = ε • (cre u * cre v)
  /-- `a(v) a(u) = ε a(u) a(v)`. -/
  ann_ann : ∀ u v, ann v * ann u = ε • (ann u * ann v)

variable {κ : Type*} [Fintype κ]

/-- The finite-rank operator `h = ∑ₖ |uₖ⟩⟨vₖ|`, `h w = ∑ₖ ⟪vₖ, w⟫ uₖ`. -/
def rankOp (u v : κ → Z) (w : Z) : Z := ∑ k, ⟪v k, w⟫_ℂ • u k

/-- Its adjoint `h* w = ∑ₖ ⟪uₖ, w⟫ vₖ`. -/
def rankOpAdj (u v : κ → Z) (w : Z) : Z := ∑ k, ⟪u k, w⟫_ℂ • v k

/-- **`dΓ(h) = ∑ₖ a*(uₖ) a(vₖ)`** for `h = ∑ₖ |uₖ⟩⟨vₖ|`. -/
def dGammaRank (cre : Z →ₗ[ℂ] R) (ann : Z →ₗ⋆[ℂ] R) (u v : κ → Z) : R := ∑ k, cre (u k) * ann (v k)

variable {ε : ℂ} {cre : Z →ₗ[ℂ] R} {ann : Z →ₗ⋆[ℂ] R}

/-- **Dereziński, Theorem 18 (4)** for finite-rank `h` on any `Z`: `[dΓ(h), a*(w)] = a*(h w)`. -/
theorem dGammaRank_commutator_creation (hf : IsFieldAlgebra ε cre ann) (u v : κ → Z) (w : Z) :
    dGammaRank cre ann u v * cre w - cre w * dGammaRank cre ann u v = cre (rankOp u v w) := by
  have hmono : ∀ k, cre (u k) * ann (v k) * cre w - cre w * (cre (u k) * ann (v k)) =
      ⟪v k, w⟫_ℂ • cre (u k) := by
    intro k
    rw [mul_assoc, hf.ann_cre, ← mul_assoc (cre w), hf.cre_cre (u k) w, mul_add, ← Algebra.commutes,
      ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc (cre (u k)) (cre w)]
    abel
  simp only [dGammaRank, rankOp, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, hmono, map_sum,
    map_smul]

/-- **Dereziński, Theorem 18 (2)** for finite-rank `h` on any `Z`: `[dΓ(h), a(w)] = -a(h* w)`. -/
theorem dGammaRank_commutator_annihilation (hf : IsFieldAlgebra ε cre ann) (u v : κ → Z) (w : Z) :
    dGammaRank cre ann u v * ann w - ann w * dGammaRank cre ann u v = -ann (rankOpAdj u v w) := by
  have hmono : ∀ k, cre (u k) * ann (v k) * ann w - ann w * (cre (u k) * ann (v k)) =
      -(⟪w, u k⟫_ℂ • ann (v k)) := by
    intro k
    rw [← mul_assoc (ann w), hf.ann_cre w (u k), add_mul, ← Algebra.smul_def, smul_mul_assoc,
      mul_assoc (cre (u k)) (ann w), hf.ann_ann (v k) w, mul_smul_comm, smul_smul, hf.eps_sq, one_smul,
      mul_assoc (cre (u k)) (ann (v k))]
    abel
  simp only [dGammaRank, rankOpAdj, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, hmono, map_sum,
    LinearMap.map_smulₛₗ, inner_conj_symm, Finset.sum_neg_distrib]

variable {κ' : Type*} [Fintype κ']

/-- The factors of `h h' = ∑ₖₘ ⟪vₖ, u'ₘ⟫ |uₖ⟩⟨v'ₘ|`. -/
def compLeft (u v : κ → Z) (u' : κ' → Z) (p : κ × κ') : Z := ⟪v p.1, u' p.2⟫_ℂ • u p.1

/-- `∑ₖₘ ⟪vₖ, u'ₘ⟫ |uₖ⟩⟨v'ₘ|` is `h h'`. -/
lemma rankOp_comp (u v : κ → Z) (u' v' : κ' → Z) (w : Z) :
    rankOp (compLeft u v u') (fun p : κ × κ' => v' p.2) w = rankOp u v (rankOp u' v' w) := by
  simp only [rankOp, compLeft, Fintype.sum_prod_type, inner_sum, inner_smul_right, Finset.sum_smul, smul_smul]

/-- **Dereziński, Theorem 13 (1)** for finite-rank `h`, `h'` on any `Z`: `[dΓ(h), dΓ(h')] = dΓ(h h') - dΓ(h' h)`. -/
theorem dGammaRank_commutator (hf : IsFieldAlgebra ε cre ann) (u v : κ → Z) (u' v' : κ' → Z) :
    dGammaRank cre ann u v * dGammaRank cre ann u' v' - dGammaRank cre ann u' v' * dGammaRank cre ann u v =
      dGammaRank cre ann (compLeft u v u') (fun p : κ × κ' => v' p.2) -
        dGammaRank cre ann (compLeft u' v' u) (fun p : κ' × κ => v p.2) := by
  set D := dGammaRank cre ann u v with hD
  have hc : ∀ m, D * (cre (u' m) * ann (v' m)) - cre (u' m) * ann (v' m) * D =
      cre (rankOp u v (u' m)) * ann (v' m) - cre (u' m) * ann (rankOpAdj u v (v' m)) := by
    intro m
    rw [show D * (cre (u' m) * ann (v' m)) - cre (u' m) * ann (v' m) * D =
        (D * cre (u' m) - cre (u' m) * D) * ann (v' m) + cre (u' m) * (D * ann (v' m) - ann (v' m) * D) by
          noncomm_ring,
      hD, dGammaRank_commutator_creation hf, dGammaRank_commutator_annihilation hf, mul_neg, ← sub_eq_add_neg]
  have hexp : D * dGammaRank cre ann u' v' - dGammaRank cre ann u' v' * D =
      ∑ m, (D * (cre (u' m) * ann (v' m)) - cre (u' m) * ann (v' m) * D) := by
    simp only [dGammaRank, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  rw [hexp]
  simp only [hc, Finset.sum_sub_distrib]
  congr 1
  · simp only [dGammaRank, compLeft, rankOp, map_sum, map_smul, Finset.sum_mul, smul_mul_assoc,
      Fintype.sum_prod_type]
    exact Finset.sum_comm
  · simp only [dGammaRank, compLeft, rankOpAdj, map_sum, LinearMap.map_smulₛₗ, inner_conj_symm, Finset.mul_sum,
      mul_smul_comm, map_smul, smul_mul_assoc, Fintype.sum_prod_type]

end Lightlike.OperatorAlgebras.SecondQuantFinite
