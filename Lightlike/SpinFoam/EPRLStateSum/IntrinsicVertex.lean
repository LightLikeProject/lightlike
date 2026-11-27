import Lightlike.SpinFoam.EPRLStateSum.ComplexIntrinsicAmp
import Lightlike.SpinFoam.EPRLStateSum.SignedVertex

/-!
# The intrinsic EPRL vertex is the SF6 vertex in the sorted basis of the tetrahedra

The EPRL vertex `EPRL.simpE` (the vertex amplitude `eprlVertex` of `Lightlike/Spin4/Vertex.lean`)
labels the tetrahedron `s∖{s_a}` of a 4-simplex by a virtual spin `i_a` in the *positional* channel
of `fifteenJSimplex`: the legs of the node `a` in the cyclic order `a+1, a+2, a+3, a+4` (mod 5) and
the pair `(a+1, a+2)` coupled (`NodeBasis.lean`). That basis depends on the position `a`, so a
tetrahedron shared by two 4-simplices at positions of different parity is labelled in two different
bases (`positional_gluing_ne_intrinsic`).

The intrinsic vertex `simpEI` of `SimplexIntrinsic.lean` uses the sorted legs of the tetrahedron
(`nodeI`), the same basis from both sides. Its definition there is a sum over the Ooguri virtual
spins. This file proves that it *is* the SF6 vertex, with every positional label rewritten in the
sorted basis by the change of basis between the two orthonormal intertwiner bases:

* `nodeP J a i l`: the positional recoupling matrix of the node `a` (from the channel
  `(a+1, a+2)(a+3, a+4)` to `(a+1, a+3)(a+2, a+4)`), the matrices of `fifteenJSimplex_eq_sum_ampP`;
* `nodeT J a z i = Σ_m nodeI J a z m · nodeP J a i m`: the transition from the sorted label `z` to
  the positional label `i`;
* `posF_eq_fifteenJ`: `posF J i = Σ_l Π_a nodeP J a (i a) (l a) · vertexP J l` is the 15j symbol
  with positional labels `i`;
* `simpEIAux_eq_sum_nodeT`: **`simpEIAux J z = Σ_i Π_a nodeT J a (z a) (i a) · posF J i`**, by
  the orthogonality of the positional matrices (`sum_nodeP_mul`) and the triangle conditions of a
  non-zero Ooguri vertex (`tri_of_ampP_ne_zero`).
-/

open Finset Lightlike.Recoupling Lightlike.Spin4 Lightlike.FourD Lightlike.SpinFoam
  Lightlike.Pentagon PhyslibAlpha.Sl2

namespace Lightlike.SpinFoam.EPRLStateSum

/-- **The positional node matrix** of the node `a` of a 4-simplex with triangle spins `J`: the
recoupling matrix `fourRecoupling` of the legs `a+1, a+2, a+3, a+4` (mod 5) in this cyclic order,
from the channel `(a+1, a+2)(a+3, a+4)` of `fifteenJSimplex` to `(a+1, a+3)(a+2, a+4)`. -/
noncomputable def nodeP (J : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (i l : ℕ) : ℝ :=
  fourRecoupling (J a (a + 1)) (J a (a + 2)) (J a (a + 3)) (J a (a + 4)) i l

/-- The box of the positional labels: `i_a ≤ J a (a+1) + J a (a+2)`. -/
def posBox (J : Fin 5 → Fin 5 → ℕ) : Fin 5 → Finset ℕ :=
  fun a => range (J a (a + 1) + J a (a + 2) + 1)

/-- **The sign between the channel tensors of the sorted and of the cyclic leg order** at the node `a`: the intertwiners of the
channel `(0 2 | 1 3)` with the legs read in the sorted order and in the cyclic order `a+1, …, a+4` differ by the sign
`(-1)^(tetSignExp a t₀ t₁ t₂ t₃ m)` (`fourJ_swap₁₂`, `fourJ_swap₃₄`, `fourJ_swapPairs`), trivial at the nodes `0` and `4`. -/
def nodeEta (J : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (m : ℕ) : ℝ :=
  (-1) ^ tetSignExp a (J a (a.succAbove 0)) (J a (a.succAbove 1)) (J a (a.succAbove 2)) (J a (a.succAbove 3)) m

/-- **The transition matrix** at the node `a` from the sorted (intrinsic) label `z` to the
positional label `i`: `Σ_m ⟨z | m⟩_sorted η_a(m) ⟨i | m⟩_positional` over the common pairing basis `m`. It is the overlap of
the two orthonormal bases of the invariant space of the node: the sorted-leg intertwiner and the cyclic-leg intertwiner. -/
noncomputable def nodeT (J : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (z i : ℕ) : ℝ :=
  ∑ m ∈ simpBox J a, nodeI J a z m * nodeEta J a m * nodeP J a i m

/-- The 4-simplex contraction with positional labels `i`, expanded in the Ooguri virtual spins. -/
noncomputable def posF (J : Fin 5 → Fin 5 → ℕ) (i : Fin 5 → ℕ) : ℝ :=
  ∑ l ∈ Fintype.piFinset (simpBox J), (∏ a, nodeP J a (i a) (l a)) * vertexP J l

/-- `Tri` is symmetric in its three arguments. -/
lemma tri_perm₁ {x y z : ℕ} (h : Tri x y z) : Tri y x z := by unfold Tri at *; omega

lemma tri_perm₂ {x y z : ℕ} (h : Tri x y z) : Tri z x y := by unfold Tri at *; omega

lemma tri_perm₃ {x y z : ℕ} (h : Tri x y z) : Tri x z y := by unfold Tri at *; omega

/-- **Orthogonality of the positional matrix** in its first label: summing the positional label
`i` over its box gives `δ_{ml}` on the admissible pairing labels. -/
theorem sum_nodeP_mul (J : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (m l : ℕ) :
    ∑ i ∈ posBox J a, nodeP J a i m * nodeP J a i l =
      if m = l ∧ Tri (J a (a + 1)) (J a (a + 3)) m ∧ Tri m (J a (a + 2)) (J a (a + 4))
      then 1 else 0 :=
  sum_fourRecoupling_mul_left _ _ _ _ m l

/-- **The positional expansion is the 15j symbol**: for symmetric `J`, `posF J i` is
`fifteenJSimplex` of the triangle spins and the positional labels `i`. -/
theorem posF_eq_fifteenJ (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (i : Fin 5 → ℕ) :
    posF J i =
      fifteenJSimplex (J 0 1) (J 0 2) (J 0 3) (J 0 4) (J 1 2) (J 1 3) (J 1 4) (J 2 3) (J 2 4)
        (J 3 4) (i 0) (i 1) (i 2) (i 3) (i 4) := by
  rw [fifteenJSimplex_eq_sum_ampP J (i 0) (i 1) (i 2) (i 3) (i 4), posF, sum_piFinset_five]
  refine Finset.sum_congr rfl fun l₀ _ => Finset.sum_congr rfl fun l₁ _ =>
    Finset.sum_congr rfl fun l₂ _ => Finset.sum_congr rfl fun l₃ _ =>
    Finset.sum_congr rfl fun l₄ _ => ?_
  simp only [Fin.prod_univ_five, nodeP, vertexP]
  have e1 : J 1 (1 + 4) = J 0 1 := hJ 1 0
  have e2 : J 2 (2 + 3) = J 0 2 := hJ 2 0
  have e3 : J 2 (2 + 4) = J 1 2 := hJ 2 1
  have e4 : J 3 (3 + 2) = J 0 3 := hJ 3 0
  have e5 : J 3 (3 + 3) = J 1 3 := hJ 3 1
  have e6 : J 3 (3 + 4) = J 2 3 := hJ 3 2
  have e7 : J 4 (4 + 1) = J 0 4 := hJ 4 0
  have e8 : J 4 (4 + 2) = J 1 4 := hJ 4 1
  have e9 : J 4 (4 + 3) = J 2 4 := hJ 4 2
  have e10 : J 4 (4 + 4) = J 3 4 := hJ 4 3
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  simp

/-- The admissibility of the pairing label `m` at the positional node `a` (the right side of
`sum_nodeP_mul` on the diagonal). -/
def AdmP (J : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (m : ℕ) : Prop :=
  Tri (J a (a + 1)) (J a (a + 3)) m ∧ Tri m (J a (a + 2)) (J a (a + 4))

/-- **A non-zero Ooguri vertex amplitude has admissible virtual spins at every node.** -/
theorem admP_of_ampP_ne_zero (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p)
    (l : Fin 5 → ℕ) (hA : ampP J l ≠ 0) (a : Fin 5) : AdmP J a (l a) := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, ⟨f1, f2⟩⟩ := tri_of_ampP_ne_zero hA
  have h10 := hJ 1 0
  have h20 := hJ 2 0
  have h21 := hJ 2 1
  have h30 := hJ 3 0
  have h31 := hJ 3 1
  have h32 := hJ 3 2
  have h40 := hJ 4 0
  have h41 := hJ 4 1
  have h42 := hJ 4 2
  have h43 := hJ 4 3
  have p0 := tri_perm₁ a1
  have p1 := tri_perm₂ a1
  have p2 := tri_perm₃ a1
  have p3 := tri_perm₁ a2
  have p4 := tri_perm₂ a2
  have p5 := tri_perm₃ a2
  have q0 := tri_perm₁ b1
  have q1 := tri_perm₂ b1
  have q2 := tri_perm₃ b1
  have q3 := tri_perm₁ b2
  have q4 := tri_perm₂ b2
  have q5 := tri_perm₃ b2
  have r0 := tri_perm₁ c1
  have r1 := tri_perm₂ c1
  have r2 := tri_perm₃ c1
  have r3 := tri_perm₁ c2
  have r4 := tri_perm₂ c2
  have r5 := tri_perm₃ c2
  have s0 := tri_perm₁ d1
  have s1 := tri_perm₂ d1
  have s2 := tri_perm₃ d1
  have s3 := tri_perm₁ d2
  have s4 := tri_perm₂ d2
  have s5 := tri_perm₃ d2
  have u0 := tri_perm₁ f1
  have u1 := tri_perm₂ f1
  have u2 := tri_perm₃ f1
  have u3 := tri_perm₁ f2
  have u4 := tri_perm₂ f2
  have u5 := tri_perm₃ f2
  have v0 := tri_perm₂ (tri_perm₂ a1)
  have v1 := tri_perm₂ (tri_perm₂ a2)
  have v2 := tri_perm₂ (tri_perm₂ b1)
  have v3 := tri_perm₂ (tri_perm₂ b2)
  have v4 := tri_perm₂ (tri_perm₂ c1)
  have v5 := tri_perm₂ (tri_perm₂ c2)
  have v6 := tri_perm₂ (tri_perm₂ d1)
  have v7 := tri_perm₂ (tri_perm₂ d2)
  have v8 := tri_perm₂ (tri_perm₂ f1)
  have v9 := tri_perm₂ (tri_perm₂ f2)
  unfold AdmP
  fin_cases a <;> simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd] <;>
    (try simp only [h10, h20, h21, h30, h31, h32, h40, h41, h42, h43]) <;>
    exact ⟨by assumption, by assumption⟩

/-- `(-1)^n * (-1)^n = 1`. -/
lemma neg_one_pow_mul_self (n : ℕ) : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow]; norm_num

/-- **The tetrahedron signs cancel between the positional and the sorted weight**: for symmetric `J`,
`(Π_a η_a(l_a)) · vertexP J l = vertexF J l`. -/
theorem prod_nodeEta_mul_vertexP (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (l : Fin 5 → ℕ) :
    (∏ a, nodeEta J a (l a)) * vertexP J l = vertexF J l := by
  have h := recoupSign_mul_ampP_eq J hJ l
  have hη : ∏ a, nodeEta J a (l a) =
      (-1) ^ nodeExp J l 0 * (-1) ^ nodeExp J l 1 * (-1) ^ nodeExp J l 2 * (-1) ^ nodeExp J l 3 *
        (-1) ^ nodeExp J l 4 := by
    simp only [Fin.prod_univ_five, nodeEta, nodeExp]
  have hsq : ((-1 : ℝ) ^ nodeExp J l 0 * (-1) ^ nodeExp J l 1 * (-1) ^ nodeExp J l 2 * (-1) ^ nodeExp J l 3 *
        (-1) ^ nodeExp J l 4) * ((-1) ^ nodeExp J l 0 * (-1) ^ nodeExp J l 1 * (-1) ^ nodeExp J l 2 *
        (-1) ^ nodeExp J l 3 * (-1) ^ nodeExp J l 4) = 1 := by
    calc _ = ((-1 : ℝ) ^ nodeExp J l 0 * (-1) ^ nodeExp J l 0) * ((-1) ^ nodeExp J l 1 * (-1) ^ nodeExp J l 1) *
          ((-1) ^ nodeExp J l 2 * (-1) ^ nodeExp J l 2) * ((-1) ^ nodeExp J l 3 * (-1) ^ nodeExp J l 3) *
          ((-1) ^ nodeExp J l 4 * (-1) ^ nodeExp J l 4) := by ring
      _ = 1 := by simp only [neg_one_pow_mul_self, mul_one]
  unfold vertexP vertexF
  rw [hη, h]
  linear_combination ((-1) ^ triPart J * ampP J l) * hsq

/-- **The intrinsic vertex sum in terms of the positional one.** For symmetric `J`, the intrinsic
vertex sum `simpEIAux J z` (sorted labels `z`) is the positional expansion `posF J i` summed over
the positional labels `i` with the transition matrices `nodeT`. -/
theorem simpEIAux_eq_sum_nodeT (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p)
    (z : Fin 5 → ℕ) :
    simpEIAux J z =
      ∑ i ∈ Fintype.piFinset (posBox J), (∏ a, nodeT J a (z a) (i a)) * posF J i := by
  classical
  -- expand the transition matrices and the positional expansion
  have step1 : ∀ i : Fin 5 → ℕ, (∏ a, nodeT J a (z a) (i a)) * posF J i =
      ∑ m ∈ Fintype.piFinset (simpBox J), ∑ l ∈ Fintype.piFinset (simpBox J),
        (((∏ a, nodeI J a (z a) (m a)) * ∏ a, nodeEta J a (m a)) * vertexP J l) *
          ∏ a, (nodeP J a (i a) (m a) * nodeP J a (i a) (l a)) := by
    intro i
    simp only [nodeT]
    rw [Finset.prod_univ_sum, posF, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl fun i _ => step1 i, Finset.sum_comm]
  -- sum the positional labels: orthogonality at each node
  have step2 : ∀ m l : Fin 5 → ℕ,
      ∑ i ∈ Fintype.piFinset (posBox J),
          (((∏ a, nodeI J a (z a) (m a)) * ∏ a, nodeEta J a (m a)) * vertexP J l) *
          ∏ a, (nodeP J a (i a) (m a) * nodeP J a (i a) (l a)) =
        (((∏ a, nodeI J a (z a) (m a)) * ∏ a, nodeEta J a (m a)) * vertexP J l) *
          ∏ a, (if m a = l a ∧ AdmP J a (m a) then (1 : ℝ) else 0) := by
    intro m l
    rw [← Finset.mul_sum]
    congr 1
    rw [(Finset.prod_univ_sum (t := posBox J)
      (f := fun a k => nodeP J a k (m a) * nodeP J a k (l a))).symm]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [sum_nodeP_mul]
    exact if_congr Iff.rfl rfl rfl
  have step3 : ∀ m : Fin 5 → ℕ, ∑ i ∈ Fintype.piFinset (posBox J),
      ∑ l ∈ Fintype.piFinset (simpBox J),
        (((∏ a, nodeI J a (z a) (m a)) * ∏ a, nodeEta J a (m a)) * vertexP J l) *
          ∏ a, (nodeP J a (i a) (m a) * nodeP J a (i a) (l a)) =
      ∑ l ∈ Fintype.piFinset (simpBox J),
        (((∏ a, nodeI J a (z a) (m a)) * ∏ a, nodeEta J a (m a)) * vertexP J l) *
          ∏ a, (if m a = l a ∧ AdmP J a (m a) then (1 : ℝ) else 0) := by
    intro m
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => step2 m l
  rw [Finset.sum_congr rfl fun m _ => step3 m]
  -- collapse the diagonal
  rw [simpEIAux_eq_sum_box]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdiag : ((∏ a, nodeI J a (z a) (m a)) * ∏ a, nodeEta J a (m a)) * vertexP J m =
      (∏ a, nodeI J a (z a) (m a)) * vertexF J m := by
    rw [mul_assoc, prod_nodeEta_mul_vertexP J hJ m]
  rw [Finset.sum_eq_single_of_mem m hm]
  · by_cases hA : ampP J m = 0
    · have h1 : vertexP J m = 0 := by rw [vertexP, hA, mul_zero]
      have h2 : vertexF J m = 0 := by rw [vertexF, hA, mul_zero]
      rw [h1, h2]; simp
    · have hprod : (∏ a, (if m a = m a ∧ AdmP J a (m a) then (1 : ℝ) else 0)) = 1 :=
        Finset.prod_eq_one fun a _ => by
          rw [ite_eq_left_iff.mpr fun h => absurd ⟨rfl, admP_of_ampP_ne_zero J hJ m hA a⟩ h]
      rw [hprod, mul_one, hdiag]
  · intro l _ hlm
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hlm
    rw [Finset.prod_eq_zero (s := univ)
      (f := fun a => if m a = l a ∧ AdmP J a (m a) then (1 : ℝ) else 0) (Finset.mem_univ a)
      (ite_eq_right_iff.mpr fun (h : m a = l a ∧ AdmP J a (m a)) => absurd h.1.symm ha), mul_zero]

/-! ## The SF6 vertex with explicit tetrahedron labels -/

open scoped Classical in
/-- The EPRL vertex of a 4-simplex with triangle spins `Jt` (in the order of `epair`) and
tetrahedron labels `z` in the positional channels of `eprlVertex`: the body of `simpE`. -/
noncomputable def simpEL (γ : ℝ) (Jt : Fin 10 → ℕ) (z : Fin 5 → ℕ) : ℂ :=
  if (∀ e, EPRLAdmissible γ (Jt e)) ∧
      IsVertexBoundary (fun e => EPRL.eprlN γ (Jt e)) (fun e => EPRL.eprlM γ (Jt e)) z then
    eprlVertex (fun e => EPRL.eprlN γ (Jt e)) (fun e => EPRL.eprlM γ (Jt e)) z
  else 0

/-- `simpE` is `simpEL` of the triangle spins and the tetrahedron labels of the colouring. -/
theorem simpE_eq_simpEL (γ : ℝ) {V : Type*} [LinearOrder V] {s : Finset V} (hs : #s = 5)
    (col : Finset V → ℕ) :
    EPRL.simpE γ col s = simpEL γ (EPRL.triSpins s hs col) (EPRL.tetLabels s hs col) := by
  unfold EPRL.simpE simpEL
  rw [dite_eq_left hs]

/-- The triangle spins of a symmetric `J` in the order `epair` of `eprlVertex`. -/
def edgeSpins (J : Fin 5 → Fin 5 → ℕ) : Fin 10 → ℕ := fun e => J (EPRL.epair e).1 (EPRL.epair e).2

/-- The legs of the node `a` of `fifteenJSimplex` (`k5Spins`) are the cyclic legs of `nodeP`. -/
lemma k5Spins_edgeSpins (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (a : Fin 5) :
    k5Spins (edgeSpins J) a 0 = J a (a + 1) ∧ k5Spins (edgeSpins J) a 1 = J a (a + 2) ∧
      k5Spins (edgeSpins J) a 2 = J a (a + 3) ∧ k5Spins (edgeSpins J) a 3 = J a (a + 4) := by
  have h10 := hJ 1 0
  have h20 := hJ 2 0
  have h21 := hJ 2 1
  have h30 := hJ 3 0
  have h31 := hJ 3 1
  have h32 := hJ 3 2
  have h40 := hJ 4 0
  have h41 := hJ 4 1
  have h42 := hJ 4 2
  have h43 := hJ 4 3
  fin_cases a <;> simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd] <;>
    (try simp only [h10, h20, h21, h30, h31, h32, h40, h41, h42, h43]) <;>
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A positional label outside the channel of its node kills the positional matrix. -/
lemma nodeP_eq_zero_of_not_mem (J : Fin 5 → Fin 5 → ℕ) (a : Fin 5) {z : ℕ}
    (hz : z ∉ channel (J a (a + 1)) (J a (a + 2)) (J a (a + 3)) (J a (a + 4))) (m : ℕ) :
    nodeP J a z m = 0 := by
  unfold nodeP fourRecoupling
  by_cases h6 : sixJSym (J a (a + 1)) (J a (a + 2)) z (J a (a + 4)) (J a (a + 3)) m = 0
  · rw [h6, mul_zero]
  · exfalso
    obtain ⟨t1, -, -, t4⟩ := tri_of_sixJSym_ne_zero h6
    apply hz
    rw [mem_channel]
    refine ⟨t1, ?_⟩
    unfold Tri at *; omega

/-- **The EPRL vertex at `γ = 1` with positional labels is the positional expansion.** -/
theorem simpEL_one (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (z : Fin 5 → ℕ) :
    simpEL 1 (edgeSpins J) z = (posF J z : ℂ) := by
  have hN : (fun e => EPRL.eprlN 1 (edgeSpins J e)) = edgeSpins J := by
    funext e; exact EPRL.eprlN_one _
  have hM : (fun e => EPRL.eprlM 1 (edgeSpins J e)) = 0 := by
    funext e; exact EPRL.eprlM_one _
  unfold simpEL
  rw [hN, hM]
  split_ifs with h
  · rw [eprlVertex_zero_right _ _ h.2, posF_eq_fifteenJ J hJ z]
    rfl
  · have hb : ¬ IsVertexBoundary (edgeSpins J) 0 z :=
      fun hb => h ⟨fun e => EPRL.eprlAdmissible_one _, hb⟩
    unfold IsVertexBoundary at hb
    simp only [add_zero, not_forall] at hb
    obtain ⟨a, ha⟩ := hb
    obtain ⟨k0, k1, k2, k3⟩ := k5Spins_edgeSpins J hJ a
    rw [k0, k1, k2, k3] at ha
    have : posF J z = 0 := by
      unfold posF
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (nodeP_eq_zero_of_not_mem J a ha _), zero_mul]
    rw [this, Complex.ofReal_zero]

/-- **The intrinsic EPRL vertex at `γ = 1` is the SF6 vertex in the sorted basis.** On a
4-simplex `s`, `simpEI col s` (sorted tetrahedron labels `tetLabels`) is the sum over the positional
labels `i` of the transition matrices `nodeT` times the SF6 vertex `simpEL 1` (the body of
`EPRL.simpE 1`, `simpE_eq_simpEL`) with labels `i`. -/
theorem simpEI_eq_sum_simpE {V : Type*} [LinearOrder V] {s : Finset V} (hs : #s = 5)
    (col : Finset V → ℕ) :
    simpEI col s =
      ∑ i ∈ Fintype.piFinset (posBox (simplexJ s hs col)),
        (∏ a, (nodeT (simplexJ s hs col) a (EPRL.tetLabels s hs col a) (i a) : ℂ)) *
          simpEL 1 (EPRL.triSpins s hs col) i := by
  have hJ := simplexJ_symm s hs col
  have ht : EPRL.triSpins s hs col = edgeSpins (simplexJ s hs col) := rfl
  rw [simpEI_of_card hs, simpEIAux_eq_sum_nodeT _ hJ, ht, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [simpEL_one _ hJ, Complex.ofReal_mul, Complex.ofReal_prod]

/-! ## The EPRL state sum in the sorted basis of the tetrahedra -/

variable {V : Type*} [LinearOrder V]

/-- The `k`-th leg spin of a tetrahedron `t` of `K` in its own sorted order: the colour of the
triangle `t∖{t_k}`. -/
noncomputable def tetLeg (K : Complex4 V) (col : Finset V → ℕ) (t : K.tets) (k : Fin 4) : ℕ :=
  col (t.1.erase (t.1.orderEmbOfFin (Complex4.card_of_mem_faces t.2) k))

/-- The box of the sorted label of a tetrahedron: `z ≤ leg₀ + leg₁`, the channel `(01)(23)`. -/
noncomputable def tetBoxI (K : Complex4 V) (col : Finset V → ℕ) (t : K.tets) : Finset ℕ :=
  range (tetLeg K col t 0 + tetLeg K col t 1 + 1)

/-- The leg `succAbove k` of the 4-simplex `s` at the position `a` is the `k`-th sorted leg of the
tetrahedron `incTet K (s, a)`. -/
theorem complexJ_succAbove (K : Complex4 V) (col : Finset V → ℕ) (s : K.simps) (a : Fin 5)
    (k : Fin 4) : complexJ K col s a (a.succAbove k) = tetLeg K col (incTet K (s, a)) k := by
  unfold complexJ tetLeg incTet incSet
  rw [simplexJ_succAbove s.1 (K.card_eq _ s.2) col a
    (Complex4.card_of_mem_faces (incSet_mem_tets K (s, a))) k]

/-- **The EPRL vertex of the 4-simplex `s` of `K` in the sorted basis**: the SF6 vertex
`simpEL γ` with positional labels `x`, summed against the transition matrices `nodeT` from the
sorted labels `i (incTet K (s, a))` of the five tetrahedra. -/
noncomputable def vertexI (γ : ℝ) (K : Complex4 V) (col : Finset V → ℕ) (i : K.tets → ℕ)
    (s : K.simps) : ℂ :=
  ∑ x ∈ Fintype.piFinset (posBox (complexJ K col s)),
    (∏ a, (nodeT (complexJ K col s) a (i (incTet K (s, a))) (x a) : ℂ)) *
      simpEL γ (edgeSpins (complexJ K col s)) x

/-- **The EPRL state sum in the sorted basis of the tetrahedra.** The sum over the triangle
colourings `col ≤ cut` of the face amplitudes `(n+1)(m+1)`, the edge amplitudes `1` and the sum over
the sorted labels `i` of the tetrahedra (each in its channel box) of the product of the vertices
`vertexI`. A tetrahedron shared by two 4-simplices carries one label in one basis. -/
noncomputable def amplitudeI (γ : ℝ) (K : Complex4 V) (cut : Finset V → ℕ) : ℂ :=
  ∑ c ∈ K.tris.pi (fun f => range (cut f + 1)),
    (∏ f ∈ K.tris, (EPRL.faceAmp γ (Lightlike.PR.extS K.tris c f) : ℂ)) *
      (∏ _t ∈ K.tets, (EPRL.edgeAmp : ℂ)) *
      ∑ i ∈ Fintype.piFinset (tetBoxI K (Lightlike.PR.extS K.tris c)),
        ∏ s : K.simps, vertexI γ K (Lightlike.PR.extS K.tris c) i s

/-- At `γ = 1` the sorted-basis vertex is the intrinsic vertex sum `simpEIAux`. -/
theorem vertexI_one (K : Complex4 V) (col : Finset V → ℕ) (i : K.tets → ℕ) (s : K.simps) :
    vertexI 1 K col i s =
      (simpEIAux (complexJ K col s) (fun a => i (incTet K (s, a))) : ℂ) := by
  have hJ : ∀ p q, complexJ K col s p q = complexJ K col s q p :=
    simplexJ_symm s.1 (K.card_eq _ s.2) col
  rw [simpEIAux_eq_sum_nodeT _ hJ, Complex.ofReal_sum]
  unfold vertexI
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [simpEL_one _ hJ, Complex.ofReal_mul, Complex.ofReal_prod]

/-- **At `γ = 1` the sorted-basis EPRL state sum is the intrinsic amplitude** `eprlIntrinsicAmp`,
for every incidence bijection of a closed complex. -/
theorem amplitudeI_one_eq_eprlIntrinsicAmp (K : Complex4 V) (cut : Finset V → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t) :
    amplitudeI 1 K cut = (eprlIntrinsicAmp K cut e : ℂ) := by
  unfold amplitudeI eprlIntrinsicAmp
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hbox : tetBoxI K (Lightlike.PR.extS K.tris c) = fun t =>
      range (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
          ((e (t, false)).2.succAbove 0) +
        complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
          ((e (t, false)).2.succAbove 1) + 1) := by
    funext t
    rw [complexJ_succAbove, complexJ_succAbove, he t false]
    rfl
  rw [hbox, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sum]
  simp only [EPRL.faceAmp_one, EPRL.edgeAmp, Nat.cast_one, Finset.prod_const_one, mul_one,
    Nat.cast_add]
  push_cast
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  unfold tetSumTerm
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun s _ => vertexI_one K _ i s

/-- **The EPRL state sum at the BF point `γ = 1` on a closed 4-complex is the Ooguri state sum with the sign
of the link orientations.** For an incidence bijection `e` of the tetrahedra (it exists for every
closed complex, `amplitudeI_one_closed`), `amplitudeI 1 K cut` is the sum over the triangle
colourings `col ≤ cut` and the virtual spins `L` of the tetrahedra (in their boxes) of the
triangle constraints, the sign `linkSign K col = (-1)^(Σ_s triPart J_s)` (a function of the colouring
only, `ComplexSignedOoguri.lean`) and the Ooguri weight `Lightlike.SpinFoam.weight` of the coloured
complex `(col, L)`. -/
theorem amplitudeI_one_eq_signed_ooguri (K : Complex4 V) (cut : Finset V → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t) :
    amplitudeI 1 K cut =
      ((∑ c ∈ K.tris.pi (fun f => range (cut f + 1)),
        ∑ L ∈ Fintype.piFinset (fun t : K.tets =>
            simpBox (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1) (e (t, false)).2 ∩
              simpBox (complexJ K (Lightlike.PR.extS K.tris c) (e (t, true)).1) (e (t, true)).2),
          (∏ t : K.tets, if
              Tri
                (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
                  ((e (t, false)).2.succAbove 0))
                (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
                  ((e (t, false)).2.succAbove 2))
                (L t) ∧
              Tri (L t)
                (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
                  ((e (t, false)).2.succAbove 1))
                (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
                  ((e (t, false)).2.succAbove 3))
            then (1 : ℝ) else 0) *
            (linkSign K (Lightlike.PR.extS K.tris c) *
              Lightlike.SpinFoam.weight K (extL K (Lightlike.PR.extS K.tris c) L)) : ℝ) : ℂ) := by
  rw [amplitudeI_one_eq_eprlIntrinsicAmp K cut e he, eprlIntrinsicAmp_eq_signed_ooguri K cut e he]

/-- On a closed 4-complex an incidence bijection exists, so the equality with the Ooguri sum holds. -/
theorem amplitudeI_one_closed (K : Complex4 V) (hK : K.IsClosed4) (cut : Finset V → ℕ) :
    ∃ e : K.tets × Bool ≃ K.simps × Fin 5, (∀ t b, incTet K (e (t, b)) = t) ∧
      amplitudeI 1 K cut = (eprlIntrinsicAmp K cut e : ℂ) := by
  obtain ⟨e, he⟩ := exists_complex_incidence K hK
  exact ⟨e, he, amplitudeI_one_eq_eprlIntrinsicAmp K cut e he⟩

end Lightlike.SpinFoam.EPRLStateSum
