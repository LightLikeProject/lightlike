import Lightlike.SpinFoam.EPRLStateSum.IntrinsicVertex
import Lightlike.Recoupling.NineJSwap

/-!
# The EPRL state sum does not depend on the orientation of ℝ⁴

The two factors of `Spin(4) = SU(2) × SU(2)` are the self-dual and the anti-self-dual one for the
orientation `(1, i, j, k)` of `ℝ⁴ = ℍ`; the opposite orientation exchanges them
(`Lightlike/Spin4/SelfDual.lean`). On the EPRL labels this is `(n, m) ↦ (m, n)`, i.e.
`(j⁺, j⁻) = (|1+γ| j/2, |1-γ| j/2) ↦ (|1-γ| j/2, |1+γ| j/2)`, the labels of `-γ`
(`EPRL.eprlN_neg`). This file proves that the vertex and the state sum are unchanged:

* `nodeFusionNineJ_swap`: exchanging the two factors multiplies the 9j fusion coefficient of a node
  by `(-1)^(J₁+J₂+J₃+J₄)` (two 9j symbols with two rows exchanged, `nineJSym_swapRows`);
* `vertexNineJ_swap`, `eprlVertex_swap`: **the EPRL vertex is symmetric under `(n, m) ↦ (m, n)`**
  on an admissible boundary; the node signs cancel because every edge of `K₅` meets two nodes;
* `simpEL_neg`, `vertexI_neg`, `faceAmp_neg`: the vertex, the sorted-basis vertex and the face
  amplitude at `-γ` are those at `γ`;
* `amplitudeI_neg`: **`amplitudeI (-γ) K cut = amplitudeI γ K cut`** for every complex and cutoff.

The orientation of `K₅` used inside `fifteenJSimplex` (edges from the smaller to the larger
position) is a convention of the vertex order, not the orientation of ℝ⁴; its dependence is
part of the dependence on the vertex order.
-/

open Finset Lightlike.Recoupling Lightlike.Spin4 Lightlike.FourD Lightlike.SpinFoam
  Lightlike.Pentagon PhyslibAlpha.Sl2

namespace Lightlike.SpinFoam.EPRLStateSum

/-- `(-1)^C` squares to `1`. -/
lemma neg_one_pow_sq_eq_one (C : ℕ) : ((-1 : ℝ) ^ C) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

/-- **The 9j fusion coefficient under the exchange of the two factors of Spin(4).** -/
theorem nodeFusionNineJ_swap (n m : Fin 4 → ℕ) (z x y : ℕ) :
    nodeFusionNineJ m n (n + m) z y x =
      (-1) ^ (n 0 + m 0 + (n 1 + m 1) + (n 2 + m 2) + (n 3 + m 3)) *
        nodeFusionNineJ n m (n + m) z x y := by
  unfold nodeFusionNineJ
  simp only [Pi.add_apply]
  rw [nineJSym_swapRows (n 0) (n 1) x (m 0) (m 1) y, nineJSym_swapRows (n 2) (n 3) x (m 2) (m 3) y]
  have e1 : (n 0 + m 0 + (n 0 + m 0)) / 2 = n 0 + m 0 := by omega
  have e2 : (n 1 + m 1 + (n 1 + m 1)) / 2 = n 1 + m 1 := by omega
  have e3 : (n 2 + m 2 + (n 2 + m 2)) / 2 = n 2 + m 2 := by omega
  have e4 : (n 3 + m 3 + (n 3 + m 3)) / 2 = n 3 + m 3 := by omega
  rw [e1, e2, e3, e4,
    show ((y : ℝ) + 1) * ((x : ℝ) + 1) = ((x : ℝ) + 1) * ((y : ℝ) + 1) from mul_comm _ _]
  have hC := neg_one_pow_sq_eq_one ((x + y + z) / 2)
  simp only [pow_add]
  linear_combination
    ((-1 : ℝ) ^ (n 0 + m 0) * (-1) ^ (n 1 + m 1) * (-1) ^ (n 2 + m 2) * (-1) ^ (n 3 + m 3) *
      (Real.sqrt (((x : ℝ) + 1) * ((y : ℝ) + 1) * ((z : ℝ) + 1) * ((n 0 + m 0 : ℕ) + 1) *
        ((n 1 + m 1 : ℕ) + 1) * ((n 2 + m 2 : ℕ) + 1) * ((n 3 + m 3 : ℕ) + 1))) *
      nineJSym (n 0) (n 1) x (m 0) (m 1) y (n 0 + m 0) (n 1 + m 1) z *
      nineJSym (n 2) (n 3) x (m 2) (m 3) y (n 2 + m 2) (n 3 + m 3) z) * hC

/-- Every edge of `K₅` is a leg of two nodes. -/
lemma sum_k5Spins (j : Fin 10 → ℕ) : ∑ a, ∑ k, k5Spins j a k = 2 * ∑ e, j e := by
  simp only [k5Spins, Fin.sum_univ_five, Fin.sum_univ_four, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  ring

/-- **The 9j form of the vertex is symmetric under the exchange of the two factors.** -/
theorem vertexNineJ_swap (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ) :
    vertexNineJ m n (m + n) z = vertexNineJ n m (n + m) z := by
  rw [add_comm m n]
  unfold vertexNineJ
  refine Finset.sum_nbij' (fun P a => (P a).swap) (fun P a => (P a).swap) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    simp only [Fintype.mem_piFinset, nodeChannel4, channel4, mem_product] at hP ⊢
    exact fun a => ⟨(hP a).2, (hP a).1⟩
  · intro P hP
    simp only [Fintype.mem_piFinset, nodeChannel4, channel4, mem_product] at hP ⊢
    exact fun a => ⟨(hP a).2, (hP a).1⟩
  · intro P _; rfl
  · intro P _; rfl
  · intro P _
    simp only [Prod.fst_swap, Prod.snd_swap]
    have hf : ∀ a, nodeFusionNineJ (k5Spins m a) (k5Spins n a) (k5Spins (n + m) a) (z a)
        (P a).1 (P a).2 =
        (-1) ^ (∑ k, k5Spins (n + m) a k) *
          nodeFusionNineJ (k5Spins n a) (k5Spins m a) (k5Spins (n + m) a) (z a) (P a).2 (P a).1 := by
      intro a
      rw [k5Spins_add, nodeFusionNineJ_swap]
      simp only [Fin.sum_univ_four, Pi.add_apply]
    rw [Finset.prod_congr rfl fun a _ => hf a, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      sum_k5Spins, pow_mul, neg_one_sq, one_pow, one_mul]
    ring

/-- **The EPRL vertex is symmetric under `(n, m) ↦ (m, n)`** on an admissible boundary. -/
theorem eprlVertex_swap (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ) (hz : IsVertexBoundary n m z) :
    eprlVertex m n z = eprlVertex n m z := by
  have hz' : IsVertexBoundary m n z := by
    unfold IsVertexBoundary at hz ⊢
    rwa [add_comm m n]
  rw [eprlVertex_eq_vertexNineJ _ _ _ hz', eprlVertex_eq_vertexNineJ _ _ _ hz, vertexNineJ_swap]

namespace EPRL

/-- At `-γ` the self-dual label is the anti-self-dual label at `γ`. -/
theorem eprlN_neg (γ : ℝ) (J : ℕ) : Lightlike.SpinFoam.EPRL.eprlN (-γ) J =
    Lightlike.SpinFoam.EPRL.eprlM γ J := by
  simp only [Lightlike.SpinFoam.EPRL.eprlN, Lightlike.SpinFoam.EPRL.eprlM, ← sub_eq_add_neg]

/-- At `-γ` the anti-self-dual label is the self-dual label at `γ`. -/
theorem eprlM_neg (γ : ℝ) (J : ℕ) : Lightlike.SpinFoam.EPRL.eprlM (-γ) J =
    Lightlike.SpinFoam.EPRL.eprlN γ J := by
  simp only [Lightlike.SpinFoam.EPRL.eprlN, Lightlike.SpinFoam.EPRL.eprlM, sub_neg_eq_add]

/-- A spin is EPRL-admissible at `-γ` iff it is at `γ`. -/
theorem eprlAdmissible_neg (γ : ℝ) (J : ℕ) : EPRLAdmissible (-γ) J ↔ EPRLAdmissible γ J := by
  unfold EPRLAdmissible jPlus jMinus
  rw [← sub_eq_add_neg, sub_neg_eq_add, and_comm]

/-- The face amplitude at `-γ` is the one at `γ`. -/
theorem faceAmp_neg (γ : ℝ) (J : ℕ) :
    Lightlike.SpinFoam.EPRL.faceAmp (-γ) J = Lightlike.SpinFoam.EPRL.faceAmp γ J := by
  unfold Lightlike.SpinFoam.EPRL.faceAmp
  rw [eprlN_neg, eprlM_neg, mul_comm]

end EPRL

/-- **The SF6 vertex at `-γ` is the vertex at `γ`.** -/
theorem simpEL_neg (γ : ℝ) (Jt : Fin 10 → ℕ) (z : Fin 5 → ℕ) :
    simpEL (-γ) Jt z = simpEL γ Jt z := by
  have hN : (fun e => Lightlike.SpinFoam.EPRL.eprlN (-γ) (Jt e)) =
      fun e => Lightlike.SpinFoam.EPRL.eprlM γ (Jt e) := funext fun e => EPRL.eprlN_neg γ _
  have hM : (fun e => Lightlike.SpinFoam.EPRL.eprlM (-γ) (Jt e)) =
      fun e => Lightlike.SpinFoam.EPRL.eprlN γ (Jt e) := funext fun e => EPRL.eprlM_neg γ _
  have hA : (∀ e, EPRLAdmissible (-γ) (Jt e)) ↔ ∀ e, EPRLAdmissible γ (Jt e) :=
    forall_congr' fun e => EPRL.eprlAdmissible_neg γ _
  set N := fun e => Lightlike.SpinFoam.EPRL.eprlN γ (Jt e)
  set M := fun e => Lightlike.SpinFoam.EPRL.eprlM γ (Jt e)
  have hB : IsVertexBoundary M N z ↔ IsVertexBoundary N M z := by
    unfold IsVertexBoundary; rw [add_comm M N]
  unfold simpEL
  rw [hN, hM]
  by_cases h : (∀ e, EPRLAdmissible γ (Jt e)) ∧ IsVertexBoundary N M z
  · rw [if_pos (show (∀ e, EPRLAdmissible (-γ) (Jt e)) ∧ IsVertexBoundary M N z from
      ⟨hA.mpr h.1, hB.mpr h.2⟩), if_pos h, eprlVertex_swap N M z h.2]
  · rw [if_neg (show ¬ ((∀ e, EPRLAdmissible (-γ) (Jt e)) ∧ IsVertexBoundary M N z) from
      fun h' => h ⟨hA.mp h'.1, hB.mp h'.2⟩), if_neg h]

variable {V : Type*} [LinearOrder V]

/-- The sorted-basis vertex at `-γ` is the one at `γ`. -/
theorem vertexI_neg (γ : ℝ) (K : Complex4 V) (col : Finset V → ℕ) (i : K.tets → ℕ)
    (s : K.simps) : vertexI (-γ) K col i s = vertexI γ K col i s := by
  unfold vertexI
  simp only [simpEL_neg]

/-- **The EPRL state sum is independent of the orientation of ℝ⁴.** The opposite orientation
exchanges the self-dual and the anti-self-dual factor of Spin(4), `(n, m) ↦ (m, n)`, which on the
EPRL labels is `γ ↦ -γ`; the state sum is unchanged, on every complex and for every cutoff. -/
theorem amplitudeI_neg (γ : ℝ) (K : Complex4 V) (cut : Finset V → ℕ) :
    amplitudeI (-γ) K cut = amplitudeI γ K cut := by
  unfold amplitudeI
  simp only [EPRL.faceAmp_neg, vertexI_neg]

end Lightlike.SpinFoam.EPRLStateSum
