import Lightlike.FieldTheory.ZeroDim.GraphIso
import Lightlike.FieldTheory.ZeroDim.Components
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The algebra of graphs (Borinsky §2.4, eqs. (2.4.5)-(2.4.7), pp. 17-18)

Borinsky, *Graphs in perturbation theory*, arXiv:1807.02046v1, §2.4.2: the graphs span an algebra `G` whose product is
the disjoint union; `X = Σ_Γ Γ/|Aut Γ|` (eq. (2.4.5)) and `X_c` the same sum over the connected graphs (eq. (2.4.6))
converge in the product topology, finite in each grade of half-edges and vertices; Theorem 2.4.1: `X = e^{X_c}`.

Here:
* `union`: the disjoint union of labelled graphs (half-edges `Fin (n₁ + n₂)`, vertices `Fin (k₁ + k₂)`);
  `union_smul`: relabellings of the factors are relabellings of the union, so `unionC` is the disjoint union of
  isomorphism classes;
* `GAlg = AnyClass → ℚ`: the formal sums of isomorphism classes of graphs of any size (the completion of `G`);
  `mul`: the product, `(a * b)(Γ) = Σ_{Γ₁ ⊔ Γ₂ = Γ} a(Γ₁) b(Γ₂)`, a finite sum over the grades below that of `Γ`;
* `X`, `Xc`: eqs. (2.4.5), (2.4.6); `expTrunc`: `e^{X_c}` at a graph with `k` vertices is `Σ_{m ≤ k} X_c^m/m!`
  (`X_c` has no empty graph, so the higher powers vanish there).
-/

open MulAction Function Finset

noncomputable section

namespace Lightlike.FieldTheory.GraphAlg

/-- The relabelling group `S_n × S_k`. -/
abbrev Relabel (n k : ℕ) := Equiv.Perm (Fin n) × Equiv.Perm (Fin k)

/-- The isomorphism classes of graphs with `n` half-edges and `k` vertices. -/
abbrev GClass (n k : ℕ) := Quotient (orbitRel (Relabel n k) (LGraph n k))

noncomputable instance (n k : ℕ) : Fintype (GClass n k) := Fintype.ofFinite _

/-- An isomorphism class of graphs of any size, with its grade `(half-edges, vertices)`. -/
abbrev AnyClass := Σ p : ℕ × ℕ, GClass p.1 p.2

/-- The **disjoint union** of labelled graphs. -/
def union {n₁ k₁ n₂ k₂ : ℕ} (Γ₁ : LGraph n₁ k₁) (Γ₂ : LGraph n₂ k₂) : LGraph (n₁ + n₂) (k₁ + k₂) where
  att h := Sum.elim (fun a => Fin.castAdd k₂ (Γ₁.att a)) (fun b => Fin.natAdd k₁ (Γ₂.att b)) (finSumFinEquiv.symm h)
  inv h := finSumFinEquiv (Sum.map Γ₁.inv Γ₂.inv (finSumFinEquiv.symm h))
  invol h := by
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective h
    simp only [Equiv.symm_apply_apply]
    cases x <;> simp [Γ₁.invol _, Γ₂.invol _]

/-- The relabelling of a union by relabellings of the parts. -/
def sumRelabel {n₁ k₁ n₂ k₂ : ℕ} (g₁ : Relabel n₁ k₁) (g₂ : Relabel n₂ k₂) : Relabel (n₁ + n₂) (k₁ + k₂) :=
  (finSumFinEquiv.symm.trans ((Equiv.sumCongr g₁.1 g₂.1).trans finSumFinEquiv),
    finSumFinEquiv.symm.trans ((Equiv.sumCongr g₁.2 g₂.2).trans finSumFinEquiv))

/-- **Relabelling the parts relabels the union.** -/
theorem union_smul {n₁ k₁ n₂ k₂ : ℕ} (g₁ : Relabel n₁ k₁) (g₂ : Relabel n₂ k₂) (Γ₁ : LGraph n₁ k₁)
    (Γ₂ : LGraph n₂ k₂) : union (g₁ • Γ₁) (g₂ • Γ₂) = sumRelabel g₁ g₂ • union Γ₁ Γ₂ := by
  refine LGraph.ext (funext fun h => ?_) (funext fun h => ?_)
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective h
    cases x <;> simp [union, sumRelabel, smul_att]
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective h
    cases x <;> simp [union, sumRelabel, smul_inv]

/-- The **disjoint union of isomorphism classes**. -/
noncomputable def unionC {n₁ k₁ n₂ k₂ : ℕ} : GClass n₁ k₁ → GClass n₂ k₂ → GClass (n₁ + n₂) (k₁ + k₂) :=
  Quotient.map₂ union fun Γ₁ Γ₁' h₁ Γ₂ Γ₂' h₂ => by
    obtain ⟨g₁, rfl⟩ := h₁
    obtain ⟨g₂, rfl⟩ := h₂
    exact ⟨sumRelabel g₁ g₂, (union_smul g₁ g₂ Γ₁' Γ₂').symm⟩

/-- **Formal sums of graphs**: a coefficient for every isomorphism class (the completion of Borinsky's `G`). -/
abbrev GAlg := AnyClass → ℚ

open Classical in
/-- **The product of formal sums** (disjoint union): `(a * b)(Γ) = Σ_{Γ₁ ⊔ Γ₂ = Γ} a(Γ₁) b(Γ₂)`. -/
noncomputable def mul (a b : GAlg) : GAlg := fun c =>
  ∑ p ∈ antidiagonal c.1.1, ∑ q ∈ antidiagonal c.1.2, ∑ c₁ : GClass p.1 q.1, ∑ c₂ : GClass p.2 q.2,
    if (⟨(p.1 + p.2, q.1 + q.2), unionC c₁ c₂⟩ : AnyClass) = c then a ⟨(p.1, q.1), c₁⟩ * b ⟨(p.2, q.2), c₂⟩ else 0

/-- The unit: the empty graph. -/
def one : GAlg := fun c => if c.1 = (0, 0) then 1 else 0

/-- Powers of a formal sum. -/
noncomputable def pow (a : GAlg) : ℕ → GAlg
  | 0 => one
  | m + 1 => mul a (pow a m)

/-- The automorphism group of a class, through a representative. -/
abbrev autCard (c : AnyClass) : ℕ := Nat.card (stabilizer (Relabel c.1.1 c.1.2) c.2.out)

/-- A labelled graph is **connected** if its vertex set has no closed subsets but `∅` and itself. -/
def IsConnected {n k : ℕ} (Γ : LGraph n k) : Prop := HalfEdge.ConnOn Γ.att Γ.inv Finset.univ

/-- **`X = Σ_Γ Γ/|Aut Γ|`** (Borinsky eq. (2.4.5)). -/
noncomputable def X : GAlg := fun c => 1 / autCard c

open Classical in
/-- **`X_c`**, the connected graphs (Borinsky eq. (2.4.6)). -/
noncomputable def Xc : GAlg := fun c => if IsConnected c.2.out then 1 / autCard c else 0

/-- **`e^{X_c}`** at a graph with `k` vertices: `Σ_{m ≤ k} X_c^m / m!`. -/
noncomputable def expXc : GAlg := fun c => ∑ m ∈ range (c.1.2 + 1), pow Xc m c / m.factorial

end Lightlike.FieldTheory.GraphAlg
