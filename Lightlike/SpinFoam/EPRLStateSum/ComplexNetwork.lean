import Lightlike.SpinFoam.EPRLStateSum.SortedVertex
import Lightlike.SpinFoam.EPRLStateSum.ComplexLabelSum

/-!
# The tetrahedron-label sum of a closed complex as a network of the sorted-leg intertwiners

For a closed complex `K` with an incidence bijection `e`, the sum over the sorted labels of the tetrahedra of the product of the
intrinsic vertices (`tetSumTerm`) is the sum over the families `M s : Fin 10 → ℤ` of the edge projections of the 4-simplices of the product of
the edge weights `edgeW` of the simplices times, for each tetrahedron `t`, the kernel `Σ_k ι_k(μ) ι_k(μ')` of the sorted-leg intertwiners read by
the two 4-simplices containing `t` (`tetSum_network`). The sum over the label `k` of `t` is the projector of the legs of `t`; it does not
depend on the order of the legs.
-/

open Finset Lightlike.FourD Lightlike.Recoupling

namespace Lightlike.SpinFoam.EPRLStateSum

section Abstract

variable {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]

/-- **The sum over the labels of a product over the incidences** is the product over the tetrahedra of the sums, over the label, of the products
of the factors of the incidences in the fibre of the tetrahedron. -/
theorem sum_prod_fibre (τ : X → T) (B : T → Finset ℕ) (F : X → ℕ → ℝ) :
    ∑ i ∈ Fintype.piFinset B, ∏ x : X, F x (i (τ x)) =
      ∏ t : T, ∑ k ∈ B t, ∏ x ∈ univ.filter (fun x => τ x = t), F x k := by
  have h1 : ∀ i : T → ℕ, ∏ x : X, F x (i (τ x)) = ∏ t : T, ∏ x ∈ univ.filter (fun x => τ x = t), F x (i t) := by
    intro i
    rw [← Finset.prod_fiberwise univ τ (fun x => F x (i (τ x)))]
    refine Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]
  simp_rw [h1]
  rw [Finset.prod_univ_sum (t := B) (f := fun t k => ∏ x ∈ univ.filter (fun x => τ x = t), F x k)]

end Abstract

section Complex

variable {V : Type*} [LinearOrder V]

/-- The box of the edge projections of the 4-simplex `s`: `|m_e| ≤ J_e`. -/
noncomputable def projBox (K : Complex4 V) (col : Finset V → ℕ) (s : K.simps) : Finset (Fin 10 → ℤ) :=
  Fintype.piFinset (fun e : Fin 10 => Icc (-(jE (complexJ K col s) e : ℤ)) (jE (complexJ K col s) e))

/-- The weight of the ten edges of a 4-simplex: `Π_e edgeSign (J_e) (m_e)`. -/
noncomputable def edgeW (J : Fin 5 → Fin 5 → ℕ) (m : Fin 10 → ℤ) : ℝ := ∏ e : Fin 10, edgeSign (jE J e) (m e)

/-- The factor of the node `x.2` of the 4-simplex `x.1` with the virtual spin `k`, for the edge projections `m`. -/
noncomputable def nodeF (K : Complex4 V) (col : Finset V → ℕ) (x : K.simps × Fin 5) (m : Fin 10 → ℤ) (k : ℕ) : ℝ :=
  sortT (complexJ K col x.1) (fun _ => k) x.2 (legProj m x.2)

/-- The incidences of a tetrahedron: the pairs (4-simplex, position of an omitted vertex) whose tetrahedron is `t`. -/
noncomputable def fiberOf (K : Complex4 V) (t : K.tets) : Finset (K.simps × Fin 5) :=
  univ.filter (fun x => incTet K x = t)

/-- **The tetrahedron-label sum of a complex is a network**: the sum over the families `M s` of the edge projections of the 4-simplices
of the product of the edge weights times, for each tetrahedron, the sum over its label of the product of the node factors of its incidences. -/
theorem tetSum_network (K : Complex4 V) (col : Finset V → ℕ) :
    ∑ i ∈ Fintype.piFinset (tetBoxI K col), tetSumTerm K col i =
      ∑ M ∈ Fintype.piFinset (fun s : K.simps => projBox K col s),
        (∏ s : K.simps, edgeW (complexJ K col s) (M s)) *
          ∏ t : K.tets, ∑ k ∈ tetBoxI K col t, ∏ x ∈ fiberOf K t, nodeF K col x (M x.1) k := by
  classical
  have hJ : ∀ s : K.simps, ∀ p q, complexJ K col s p q = complexJ K col s q p :=
    fun s => simplexJ_symm s.1 (K.card_eq _ s.2) col
  have h1 : ∀ i : K.tets → ℕ, tetSumTerm K col i =
      ∑ M ∈ Fintype.piFinset (fun s : K.simps => projBox K col s), ∏ s : K.simps,
        (edgeW (complexJ K col s) (M s) * ∏ a : Fin 5, nodeF K col (s, a) (M s) (i (incTet K (s, a)))) := by
    intro i
    unfold tetSumTerm
    rw [Finset.prod_congr rfl fun s _ => simpEIAux_eq_contract5 (complexJ K col s) (hJ s) _]
    have h0 : ∏ s : K.simps, contract5 (complexJ K col s)
          (sortT (complexJ K col s) (fun a => i (incTet K (s, a)))) =
        ∏ s : K.simps, ∑ m ∈ projBox K col s,
          edgeW (complexJ K col s) m * ∏ a : Fin 5, nodeF K col (s, a) m (i (incTet K (s, a))) := rfl
    rw [h0, Finset.prod_univ_sum (t := fun s : K.simps => projBox K col s)
      (f := fun s m => edgeW (complexJ K col s) m * ∏ a : Fin 5, nodeF K col (s, a) m (i (incTet K (s, a))))]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun M _ => ?_
  have h2 : ∀ i : K.tets → ℕ, ∏ s : K.simps,
      (edgeW (complexJ K col s) (M s) * ∏ a : Fin 5, nodeF K col (s, a) (M s) (i (incTet K (s, a)))) =
      (∏ s : K.simps, edgeW (complexJ K col s) (M s)) *
        ∏ x : K.simps × Fin 5, nodeF K col x (M x.1) (i (incTet K x)) := by
    intro i
    rw [Finset.prod_mul_distrib, Fintype.prod_prod_type]
  simp_rw [h2]
  rw [← Finset.mul_sum, sum_prod_fibre (incTet K) (tetBoxI K col) (fun x k => nodeF K col x (M x.1) k)]
  rfl

end Complex

end Lightlike.SpinFoam.EPRLStateSum
