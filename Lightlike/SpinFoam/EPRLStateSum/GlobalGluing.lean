import Lightlike.SpinFoam.EPRLStateSum.NodePairGluing

/-!
# Global gluing: the abstract sum over tetrahedron labels of a closed 4-complex

In a closed 4-complex the incidences `(s, a)` (simplex `s`, position `a ∈ Fin 5` of one of its
tetrahedra) are in bijection with `T × Bool`, `T` the set of tetrahedra: each tetrahedron lies in
exactly two simplices. This file proves, for an abstract such incidence structure, the step that
turns the sum over the tetrahedron labels `i_t` into a constraint between the virtual spins `l` of the
two incidences of each tetrahedron:

* `prod_incidence_eq`: a product over the incidences `Π_s Π_a h s a` is the product over the
  tetrahedra of the product of the two incidences of each (`e : T × Bool ≃ S × Fin 5`);
* `global_gluing`: if the node matrices `N (s, a) i l` of the two incidences of every tetrahedron
  satisfy the orthogonality `Σ_i N p i l · N q i l' = δ_t l l'`, then
  `Σ_i Π_s Σ_{l_s} (Π_a N (s,a) (i_{t(s,a)}) (l_s a)) · F_s l_s = Σ_l (Π_t δ_t (l p_t) (l q_t)) Π_s F_s l_s`.

The orthogonality is `sum_nodeI_mul_left` (`NodePairGluing.lean`) for the intrinsic node matrices
`nodeI`; the incidence bijection `e` is the combinatorial input of the closed complex (open).
-/

open Finset

namespace Lightlike.SpinFoam.EPRLStateSum

variable {S T : Type*} [Fintype S] [Fintype T]

/-- A product over the incidences of simplices and positions, regrouped by tetrahedra. -/
theorem prod_incidence_eq (e : T × Bool ≃ S × Fin 5) (h : S → Fin 5 → ℝ) :
    ∏ s, ∏ a, h s a =
      ∏ t, (h (e (t, false)).1 (e (t, false)).2 * h (e (t, true)).1 (e (t, true)).2) := by
  calc ∏ s, ∏ a, h s a = ∏ p : S × Fin 5, h p.1 p.2 :=
        (Fintype.prod_prod_type (fun p : S × Fin 5 => h p.1 p.2)).symm
    _ = ∏ q : T × Bool, h (e q).1 (e q).2 :=
        (e.prod_comp (fun p : S × Fin 5 => h p.1 p.2)).symm
    _ = ∏ t, ∏ b : Bool, h (e (t, b)).1 (e (t, b)).2 :=
        Fintype.prod_prod_type (fun q : T × Bool => h (e q).1 (e q).2)
    _ = _ := by
        refine Finset.prod_congr rfl fun t _ => ?_
        rw [Fintype.prod_bool, mul_comm]

/-- **Sum over the tetrahedron labels of a closed complex.** With the incidence bijection
`e : T × Bool ≃ S × Fin 5` (`ι s a = t` iff `e (t, b) = (s, a)` for some `b`), node matrices `N`
that are orthogonal at each tetrahedron (`hortho`), the sum over the labels `i : T → ℕ` of the
product over simplices of `Σ_{l_s} (Π_a N (s, a) (i (ι s a)) (l_s a)) F_s l_s` is the sum over the
global virtual spins `l : S → Fin 5 → ℕ`, with the gluing constraints `δ_t`. -/
theorem global_gluing [DecidableEq S] [DecidableEq T] (ι : S → Fin 5 → T) (e : T × Bool ≃ S × Fin 5)
    (he : ∀ t b, ι (e (t, b)).1 (e (t, b)).2 = t)
    (N : S → Fin 5 → ℕ → ℕ → ℝ) (A : S → Finset (Fin 5 → ℕ)) (Ri : T → Finset ℕ)
    (F : S → (Fin 5 → ℕ) → ℝ) (δ : T → ℕ → ℕ → ℝ)
    (hortho : ∀ t l l', ∑ i ∈ Ri t,
      N (e (t, false)).1 (e (t, false)).2 i l * N (e (t, true)).1 (e (t, true)).2 i l' = δ t l l') :
    ∑ i ∈ Fintype.piFinset Ri, ∏ s, ∑ l ∈ A s, (∏ a, N s a (i (ι s a)) (l a)) * F s l =
      ∑ l ∈ Fintype.piFinset A,
        (∏ t, δ t (l (e (t, false)).1 (e (t, false)).2) (l (e (t, true)).1 (e (t, true)).2)) *
          ∏ s, F s (l s) := by
  have key : ∀ l : S → Fin 5 → ℕ,
      ∑ i ∈ Fintype.piFinset Ri, ∏ s, ∏ a, N s a (i (ι s a)) (l s a) =
        ∏ t, δ t (l (e (t, false)).1 (e (t, false)).2) (l (e (t, true)).1 (e (t, true)).2) := by
    intro l
    have h1 : ∀ i : T → ℕ, ∏ s, ∏ a, N s a (i (ι s a)) (l s a) =
        ∏ t, (N (e (t, false)).1 (e (t, false)).2 (i t) (l (e (t, false)).1 (e (t, false)).2) *
          N (e (t, true)).1 (e (t, true)).2 (i t) (l (e (t, true)).1 (e (t, true)).2)) := by
      intro i
      rw [prod_incidence_eq e (fun s a => N s a (i (ι s a)) (l s a))]
      simp only [he]
    simp only [h1]
    rw [← Finset.prod_univ_sum Ri (fun t x =>
      N (e (t, false)).1 (e (t, false)).2 x (l (e (t, false)).1 (e (t, false)).2) *
        N (e (t, true)).1 (e (t, true)).2 x (l (e (t, true)).1 (e (t, true)).2))]
    exact Finset.prod_congr rfl fun t _ => hortho t _ _
  simp only [Finset.prod_univ_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Finset.prod_mul_distrib]
  rw [← Finset.sum_mul, key]

/-- **Global gluing for the intrinsic node matrices `nodeI`.** If at every tetrahedron the four
sorted leg spins of its two incidences agree (`hleg`), the sum over the tetrahedron labels
`i_t ∈ [0, t₀ + t₁]` (the legs `t₀, t₁` of the first incidence) of the product over simplices of the
node-matrix sums is the sum over the global virtual spins `l` with the constraint that `l` agrees on
the two incidences of each tetrahedron and is admissible there (`Pentagon.Tri`). -/
theorem global_gluing_nodeI [DecidableEq S] [DecidableEq T] (ι : S → Fin 5 → T)
    (e : T × Bool ≃ S × Fin 5) (he : ∀ t b, ι (e (t, b)).1 (e (t, b)).2 = t)
    (J : S → Fin 5 → Fin 5 → ℕ) (A : S → Finset (Fin 5 → ℕ)) (F : S → (Fin 5 → ℕ) → ℝ)
    (hleg : ∀ t (k : Fin 4),
      J (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove k) =
        J (e (t, true)).1 (e (t, true)).2 ((e (t, true)).2.succAbove k)) :
    ∑ i ∈ Fintype.piFinset (fun t => range (J (e (t, false)).1 (e (t, false)).2
        ((e (t, false)).2.succAbove 0) + J (e (t, false)).1 (e (t, false)).2
        ((e (t, false)).2.succAbove 1) + 1)),
      ∏ s, ∑ l ∈ A s, (∏ a, nodeI (J s) a (i (ι s a)) (l a)) * F s l =
      ∑ l ∈ Fintype.piFinset A,
        (∏ t, if l (e (t, false)).1 (e (t, false)).2 = l (e (t, true)).1 (e (t, true)).2 ∧
            Lightlike.Pentagon.Tri
              (J (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
              (J (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2))
              (l (e (t, false)).1 (e (t, false)).2) ∧
            Lightlike.Pentagon.Tri (l (e (t, false)).1 (e (t, false)).2)
              (J (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
              (J (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3))
          then (1 : ℝ) else 0) *
          ∏ s, F s (l s) := by
  refine global_gluing ι e he (fun s a => nodeI (J s) a) A _ F
    (fun t l l' => if l = l' ∧ Lightlike.Pentagon.Tri
              (J (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
              (J (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2)) l ∧
            Lightlike.Pentagon.Tri l
              (J (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
              (J (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3))
          then (1 : ℝ) else 0) ?_
  intro t l l'
  exact sum_nodeI_mul_left (J (e (t, false)).1) (J (e (t, true)).1) (e (t, false)).2
    (e (t, true)).2 (hleg t 0) (hleg t 1) (hleg t 2) (hleg t 3) l l'

end Lightlike.SpinFoam.EPRLStateSum
