import Lightlike.Canonical.HolonomyCommon

/-!
# Uniform refinement of holonomies (row G2-007)

`ALGraph.hol_of_le` (`Lightlike/Canonical/HolonomyALOrder.lean`) states, for a fixed connection `A`, that the
holonomy along each edge of `α` is an ordered product of holonomies along edges of `α'` or their inverses. For
cylindrical functions (Ashtekar–Lewandowski, arXiv:gr-qc/0404018, p. 35) the word of the product must not depend on
`A`: the map `SU(2)^{m'} → SU(2)^m` that re-expresses the holonomies along `α` must be one continuous map for all
connections. The proof of `hol_of_le` already chooses the word from the order data `α ≤ α'` before it uses `A`;
`hol_of_le_uniform` restates it with the word chosen first, and repeats that proof.
-/

open Matrix Set Filter
open scoped ContDiff Topology NNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace Lightlike.Canonical.UniformHolonomyRefinement

open Lightlike.Canonical

variable {n : ℕ}

/-- **Uniform holonomies under refinement.** If `α ≤ α'`, each edge `i` of `α` has a word `c` in the edges of `α'`
(with orientations) such that for every continuous connection `A` the holonomy along `i` is the ordered product of the
holonomies along the edges of `c` or their inverses (Ashtekar–Lewandowski, p. 35). The word does not depend on `A`. -/
theorem hol_of_le_uniform {α α' : ALGraph} (h : α.Le α') (i : Fin α.m) :
    ∃ (K : ℕ) (c : Fin K → Fin α'.m × Bool), ∀ A : MatConn n, (∀ a, Continuous fun x => A x a) →
      (α.edge i).hol A = (List.ofFn fun l => if (c l).2 then (α'.edge (c l).1).hol A
        else ((α'.edge (c l).1).hol A)⁻¹).reverse.prod := by
  obtain ⟨K, s, c, hs, hs0, hsK, hφ⟩ := h i
  refine ⟨K, c, fun A hA => ?_⟩
  set e := α.edge i
  set f : Fin K → Matrix (Fin n) (Fin n) ℂ := fun l =>
    if (c l).2 then (α'.edge (c l).1).hol A else ((α'.edge (c l).1).hol A)⁻¹ with hf
  obtain ⟨W, ⟨hW0, hWc, hWd⟩, hWe⟩ := e.exists_isRightTransport hA
  obtain ⟨C, hC⟩ := e.exists_bound_rCoeff hA
  have hsub : ∀ l : Fin K, Icc (s l.castSucc) (s l.succ) ⊆ Icc e.t₀ e.t₁ := fun l =>
    Icc_subset_Icc (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsK ▸ hs.monotone (Fin.le_last _))
  -- the transport across the `l`-th part
  have hstep : ∀ l : Fin K, W (s l.succ) = f l * W (s l.castSucc) := fun l => by
    obtain ⟨φ, hφc, hφm, hφ0, hφ1, hφe⟩ := hφ l
    have hlt : s l.castSucc < s l.succ := hs (Fin.castSucc_lt_succ)
    have hmaps : MapsTo φ (Icc (s l.castSucc) (s l.succ))
        (Icc ((α'.edge (c l).1).orient (c l).2).t₀ ((α'.edge (c l).1).orient (c l).2).t₁) := fun x hx =>
      ⟨hφ0 ▸ hφm ⟨le_rfl, hlt.le⟩ hx hx.1, hφ1 ▸ hφm hx ⟨hlt.le, le_rfl⟩ hx.2⟩
    have hφr := ALEdge.rightDeriv_of_comp hφc hφm hmaps hφe fun x hx =>
      ⟨_, e.hasDerivWithinAt_path_Ici ⟨(hsub l (Ico_subset_Icc_self hx)).1,
        lt_of_lt_of_le hx.2 (hsub l ⟨hlt.le, le_rfl⟩).2⟩⟩
    choose! φ' hφ' using hφr
    obtain ⟨U, ⟨hU0, hUc, hUd⟩, hUe⟩ := ALEdge.isRightTransport_comp hA hlt hφc hφ' hφm hφ0 hφ1 hφe
    have hV : ∀ τ ∈ Ico (s l.castSucc) (s l.succ),
        HasDerivWithinAt (fun σ => U σ * W (s l.castSucc)) (-(rCoeff A e.path τ * (U τ * W (s l.castSucc))))
          (Ici τ) τ := fun τ hτ => by
      have := (hUd τ hτ).mul_const (W (s l.castSucc))
      rwa [Matrix.neg_mul, Matrix.mul_assoc] at this
    have heq := eqOn_of_right_deriv (M := rCoeff A e.path) (C := C)
      (fun τ hτ => hC τ ⟨(hsub l (Ico_subset_Icc_self hτ)).1,
        lt_of_lt_of_le hτ.2 (hsub l ⟨hlt.le, le_rfl⟩).2⟩)
      (hWc.mono (hsub l))
      (fun τ hτ => hWd τ ⟨(hsub l (Ico_subset_Icc_self hτ)).1, lt_of_lt_of_le hτ.2 (hsub l ⟨hlt.le, le_rfl⟩).2⟩)
      (hUc.mul continuousOn_const) hV (by simp [hU0]) ⟨hlt.le, le_rfl⟩
    rw [heq, Pi.mul_apply, hUe, ALEdge.hol_orient hA]
  -- by induction on the parts
  have hind : ∀ l (hl : l ≤ K), W (s ⟨l, Nat.lt_succ_of_le hl⟩) = ((List.ofFn f).take l).reverse.prod := by
    intro l
    induction l with
    | zero => intro _; simp [show (⟨0, _⟩ : Fin (K + 1)) = 0 from rfl, hs0, hW0]
    | succ l ih =>
      intro hl
      have := hstep ⟨l, hl⟩
      simp only [Fin.succ_mk, Fin.castSucc_mk] at this
      rw [this, ih (Nat.le_of_succ_le hl), List.take_add_one, List.getElem?_ofFn,
        dite_eq_left (Nat.lt_of_succ_le hl)]
      simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.prod_cons]
  have := hind K le_rfl
  rw [show (⟨K, Nat.lt_succ_self K⟩ : Fin (K + 1)) = Fin.last K from rfl, hsK, hWe,
    List.take_of_length_le (by simp)] at this
  exact this

end Lightlike.Canonical.UniformHolonomyRefinement

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_007.hol_of_le_uniform := _root_.Lightlike.Canonical.UniformHolonomyRefinement.hol_of_le_uniform
