import Lightlike.Spin4.FusionNineJ
import Lightlike.Recoupling.FifteenJ

/-!
# The Euclidean EPRL vertex amplitude

The vertex amplitude of the Euclidean Engle–Pereira–Rovelli–Livine (EPRL) spin foam model with
Immirzi parameter `γ < 1` (EPRL 2008, arXiv:0711.0146, eq. (31)), built on the EPRL map of
`Lightlike/Spin4/EPRL.lean` and `Lightlike/Spin4/Fusion.lean` (SF5c). Doubled spins throughout.

A 4-simplex is dual to the complete graph `K₅`: five nodes (the tetrahedra) and ten edges (the
triangles) `01, 02, 03, 04, 12, 13, 14, 23, 24, 34`. Edge `e` carries a Spin(4) spin
`(n e, m e) = (2j⁺, 2j⁻)` and the SU(2) spin `J e = n e + m e`; node `a` carries an SU(2) intertwiner
`ι_{z a}` of its four legs, in the recoupling basis `(J₁ J₂) z (J₃ J₄)`. The EPRL map sends it to
the Spin(4) intertwiner `Φ(ι_z) = P (Y₁ ⊗ Y₂) ι_z (Y₃ ⊗ Y₄)ᴴ`, and the vertex amplitude is the
contraction of the five tensors `Φ(ι_{z a})` along the edges of `K₅` (`eprlVertex`).

## Main results

* `eprlVertex`: the definition, as the `K₅` contraction `k5Contract4` of the EPRL node tensors
  `eprlNode` (which are the matrices `Φ(ι_z)` of SF5c, `eprlNode_eq_eprlIntertwiner`).
* `eprlVertex_eq_fifteenJ`: the spin-network form of EPRL eq. (31),
  `A_v = Σ_{x,y} Π_a f_a(z_a; x_a, y_a) {15j}(n; x) {15j}(m; y)`, with the 4-simplex
  contraction `Lightlike.Recoupling.fifteenJSimplex` (`fifteenJSimplex_eq_k5Contract`).
* `eprlVertex_eq_vertexNineJ`: on an admissible boundary, the same with the fusion coefficients as
  products of two 9j symbols (Alesci–Bianchi–Magliaro–Perini, arXiv:0809.3718, eq. (7)); hence the
  amplitude is real (`eprlVertex_im`).
* Selection rules: the amplitude vanishes unless the self-dual and the anti-self-dual spins at
  every node add up to even numbers (`eprlVertex_eq_zero_of_not_even_left`, `_right`).
* `eprlVertex_zero`: the value `1` at zero spins.
* `eprlVertex_zero_right`: with trivial anti-self-dual spins (`m = 0`, formally `γ = 1`) the
  amplitude is the SU(2) BF (Ooguri) 4-simplex amplitude `fifteenJSimplex` of the same spins and
  intertwiners.

`vertexNineJ` takes the SU(2) spins `J` as a separate argument, so that a wrong simplicity
constraint (`J ≠ n + m`) can be evaluated and shown to change the amplitude
(`Lightlike/Spin4/VertexTests.lean`).

## Conventions

The amplitude is defined for all labels; `IsEPRLVertexLabel γ n m` states that they are EPRL
labels of `γ` (`n - m = γ (n + m)`). For a node label `z a` outside the admissible channel,
`ι_{z a}` is not an intertwiner and `eprlVertex` is a junk value, so every value theorem assumes
`IsVertexBoundary n m z`. Edge and face amplitudes, and the normalisation of the boundary
intertwiners beyond that of the recoupling basis, are not part of the vertex.
-/

open Matrix Finset PhyslibAlpha.Sl2 Lightlike.Pentagon Lightlike.Recoupling
open scoped Kronecker

namespace Lightlike.Spin4

/-! ## The contraction of five 4-valent nodes along the edges of `K₅` -/

/-- The projections at the four legs of each node of `K₅`, given the projections `μ` of the ten
edges `01, 02, 03, 04, 12, 13, 14, 23, 24, 34` (in this order). Each edge `ab`, `a < b`, leaves
node `a` with projection `μ` and enters node `b` with projection `-μ`; the legs of node `a` are
ordered as in `Lightlike.Recoupling.fifteenJSimplex`. -/
def k5Legs (μ : Fin 10 → ℤ) : Fin 5 → Fin 4 → ℤ :=
  ![![μ 0, μ 1, μ 2, μ 3], ![μ 4, μ 5, μ 6, -μ 0], ![μ 7, μ 8, -μ 1, -μ 4],
    ![μ 9, -μ 2, -μ 5, -μ 7], ![-μ 3, -μ 6, -μ 8, -μ 9]]

/-- The spins at the four legs of each node of `K₅`, given the spins `j` of the ten edges, in the
leg order of `k5Legs`. -/
def k5Spins (j : Fin 10 → ℕ) : Fin 5 → Fin 4 → ℕ :=
  ![![j 0, j 1, j 2, j 3], ![j 4, j 5, j 6, j 0], ![j 7, j 8, j 1, j 4],
    ![j 9, j 2, j 5, j 7], ![j 3, j 6, j 8, j 9]]

/-- The projections of the ten edges, `|μ_e| ≤ j_e` (doubled units). -/
def k5Box (j : Fin 10 → ℕ) : Finset (Fin 10 → ℤ) :=
  Fintype.piFinset fun e => Icc (-(j e : ℤ)) (j e)

/-- **The SU(2) contraction of five 4-valent tensors along `K₅`**: each edge carries the invariant
form `ε(μ, -μ) = (-1)^{(j-μ)/2}` (`Lightlike.Recoupling.edgeSign`), and the tensors `T a` sit at the
nodes, with their legs as in `k5Legs`. -/
noncomputable def k5Contract (j : Fin 10 → ℕ) (T : Fin 5 → (Fin 4 → ℤ) → ℂ) : ℂ :=
  ∑ μ ∈ k5Box j, (∏ e, (edgeSign (j e) (μ e) : ℂ)) * ∏ a, T a (k5Legs μ a)

/-- **The Spin(4) contraction of five 4-valent tensors along `K₅`**: an edge labelled by the
Spin(4) representation `(n, m)` (doubled spins) carries the projections `(μ, ν)` of
`V_{n/2} ⊗ V_{m/2}` and the invariant form `ε_n ⊗ ε_m`. The node tensors take the self-dual and
the anti-self-dual projections of their four legs. -/
noncomputable def k5Contract4 (n m : Fin 10 → ℕ)
    (T : Fin 5 → (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℂ) : ℂ :=
  ∑ μ ∈ k5Box n, ∑ ν ∈ k5Box m,
    (∏ e, ((edgeSign (n e) (μ e) * edgeSign (m e) (ν e) : ℝ) : ℂ)) *
      ∏ a, T a (k5Legs μ a) (k5Legs ν a)

/-- **The Spin(4) contraction factorises on product tensors**: if every node tensor is a product
of a self-dual and an anti-self-dual tensor, the contraction is the product of the two SU(2)
contractions. -/
theorem k5Contract4_mul (n m : Fin 10 → ℕ) (A B : Fin 5 → (Fin 4 → ℤ) → ℂ) :
    k5Contract4 n m (fun a μ ν => A a μ * B a ν) = k5Contract n A * k5Contract m B := by
  unfold k5Contract4 k5Contract
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  simp only [Complex.ofReal_mul, prod_mul_distrib]
  ring

/-- **The contraction is multilinear in the five nodes**: a sum at every node expands into the
sum over all choices `P a ∈ s a`. -/
theorem k5Contract4_sum {ι : Type*} (n m : Fin 10 → ℕ) (s : Fin 5 → Finset ι)
    (c : Fin 5 → ι → ℂ) (T : Fin 5 → ι → (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℂ) :
    k5Contract4 n m (fun a μ ν => ∑ p ∈ s a, c a p * T a p μ ν) =
      ∑ P ∈ Fintype.piFinset s, (∏ a, c a (P a)) * k5Contract4 n m (fun a => T a (P a)) := by
  unfold k5Contract4
  simp only [Finset.prod_univ_sum, Finset.mul_sum]
  conv_lhs => arg 2; ext μ; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ν _ => ?_
  rw [prod_mul_distrib]
  ring

/-- A sum over the tuples `x ∈ Π_i S i` splits off the first entry. -/
lemma sum_piFinset_cons {k : ℕ} (S : Fin (k + 1) → Finset ℤ) (f : (Fin (k + 1) → ℤ) → ℂ) :
    ∑ x ∈ Fintype.piFinset S, f x =
      ∑ a ∈ S 0, ∑ x ∈ Fintype.piFinset (Fin.tail S), f (Matrix.vecCons a x) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => (x 0, Fin.tail x)) (fun p => Matrix.vecCons p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact mem_product.mpr ((Fin.mem_piFinset_iff_zero_tail).mp hx)
  · intro p hp
    rw [mem_product] at hp
    rw [Fin.mem_piFinset_iff_zero_tail]
    exact ⟨hp.1, hp.2⟩
  · intro x _
    exact Fin.cons_self_tail x
  · intro p _
    exact Prod.ext rfl (Fin.tail_cons (α := fun _ => ℤ) p.1 p.2)
  · intro x _
    show f x = f (Fin.cons (x 0) (Fin.tail x))
    rw [Fin.cons_self_tail]

/-- A sum over the single tuple of length zero. -/
lemma sum_piFinset_zero (S : Fin 0 → Finset ℤ) (f : (Fin 0 → ℤ) → ℂ) :
    ∑ x ∈ Fintype.piFinset S, f x = f ![] := by
  rw [Fintype.piFinset_of_isEmpty, Finset.univ_unique, Finset.sum_singleton]
  congr 1

/-- The SU(2) node tensor `ι^{(i)}_{μ₁μ₂μ₃μ₄}` of `Lightlike.Recoupling.fourJ`, for leg spins `j`. -/
noncomputable def fourJNode (j : Fin 4 → ℕ) (i : ℕ) (μ : Fin 4 → ℤ) : ℂ :=
  (fourJ (j 0) (j 1) (j 2) (j 3) i (μ 0) (μ 1) (μ 2) (μ 3) : ℂ)

/-- **The 4-simplex contraction `fifteenJSimplex` is the `K₅` contraction of five `fourJ` tensors**:
`Lightlike.Recoupling.fifteenJSimplex` is `k5Contract` with the node tensors `ι^{(i_a)}`. -/
theorem fifteenJSimplex_eq_k5Contract (j : Fin 10 → ℕ) (i : Fin 5 → ℕ) :
    (fifteenJSimplex (j 0) (j 1) (j 2) (j 3) (j 4) (j 5) (j 6) (j 7) (j 8) (j 9)
        (i 0) (i 1) (i 2) (i 3) (i 4) : ℂ) =
      k5Contract j (fun a => fourJNode (k5Spins j a) (i a)) := by
  unfold k5Contract k5Box fifteenJSimplex
  push_cast
  iterate 10 (rw [sum_piFinset_cons]; refine Finset.sum_congr rfl fun _ _ => ?_)
  rw [sum_piFinset_zero]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    k5Legs, k5Spins, fourJNode, Fin.reduceSucc, Matrix.cons_val, Fin.succ_zero_eq_one]
  ring

/-! ## The EPRL node tensor -/

/-- The labels `(x, y)` of the Spin(4) intertwiners `ι⁺_x ⊗ ι⁻_y` of a node whose legs carry the
Spin(4) spins `(n k, m k)` (`channel4`). -/
def nodeChannel4 (n m : Fin 4 → ℕ) : Finset (ℕ × ℕ) :=
  channel4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)

/-- The fusion coefficients `f(z; x, y)` of a node whose legs carry the Spin(4) spins
`(n k, m k)` (`fusion`). -/
noncomputable def nodeFusion (n m : Fin 4 → ℕ) (z x y : ℕ) : ℂ :=
  fusion (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) z x y

/-- **The EPRL node tensor** of the SU(2) intertwiner `ι_z`: the image `Φ(ι_z)` under the EPRL map,
`Σ_{x,y} f(z; x, y) ι⁺_x ⊗ ι⁻_y` (`eprlIntertwiner_ivec`), with all four legs outgoing, as a
function of the self-dual projections `μ` and the anti-self-dual projections `ν` of its legs
(`eprlNode_eq_eprlIntertwiner`). -/
noncomputable def eprlNode (n m : Fin 4 → ℕ) (z : ℕ) (μ ν : Fin 4 → ℤ) : ℂ :=
  ∑ p ∈ nodeChannel4 n m, nodeFusion n m z p.1 p.2 * (fourJNode n p.1 μ * fourJNode m p.2 ν)

/-- **The node tensor is `Φ(ι_z)`**: at the projections `μ_k = n_k - 2a_k` of the outgoing legs and
`μ_k = -(n_k - 2b_k)` of the incoming ones (and likewise for `ν`), the node tensor is the matrix
entry `Φ(ι_z)((a, a'), (b, b'))` of the EPRL map of SF5c, up to the sign of the invariant forms that
turn the two incoming legs into outgoing ones (`fourJ_eq_ivec`). -/
theorem eprlNode_eq_eprlIntertwiner {n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ : ℕ} (z : ℕ)
    (P : Idx n₁ n₂ × Idx m₁ m₂) (Q : Idx n₃ n₄ × Idx m₃ m₄) :
    eprlNode ![n₁, n₂, n₃, n₄] ![m₁, m₂, m₃, m₄] z
        ![(n₁ : ℤ) - 2 * (P.1.1 : ℕ), (n₂ : ℤ) - 2 * (P.1.2 : ℕ), 2 * (Q.1.1 : ℕ) - n₃,
          2 * (Q.1.2 : ℕ) - n₄]
        ![(m₁ : ℤ) - 2 * (P.2.1 : ℕ), (m₂ : ℤ) - 2 * (P.2.2 : ℕ), 2 * (Q.2.1 : ℕ) - m₃,
          2 * (Q.2.2 : ℕ) - m₄] =
      (-1 : ℂ) ^ (n₂ + n₄ + (P.1.1 : ℕ) + P.1.2) * (-1 : ℂ) ^ (m₂ + m₄ + (P.2.1 : ℕ) + P.2.2) *
        eprlIntertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄
          (ivec (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) z) P Q := by
  rw [eprlIntertwiner_ivec, Matrix.sum_apply, Finset.mul_sum]
  simp only [eprlNode, nodeChannel4, nodeFusion, fourJNode, Matrix.cons_val]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hx, hy⟩ := mem_product.mp hp
  rw [fourJ_eq_ivec hx P.1 Q.1, fourJ_eq_ivec hy P.2 Q.2]
  simp only [Matrix.smul_apply, ivec4, kroneckerMap_apply, smul_eq_mul]
  ring

/-! ## The vertex amplitude -/

/-- **The Euclidean EPRL vertex amplitude** (Engle–Pereira–Rovelli–Livine 2008, `γ < 1`): the
Spin(4) contraction along `K₅` of the five EPRL node tensors `Φ(ι_{z_a})`. The ten edges carry the
Spin(4) spins `(n e, m e)` (doubled), the SU(2) boundary spins are `J e = n e + m e`, and node `a`
carries the SU(2) intertwiner `ι_{z a}` of its legs `k5Spins J a`, coupled as `(J₁ J₂) z (J₃ J₄)`.
For the EPRL model the labels satisfy `n - m = γ (n + m)` (`IsEPRLLabel`); the amplitude itself is
defined for all labels. -/
noncomputable def eprlVertex (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ) : ℂ :=
  k5Contract4 n m fun a => eprlNode (k5Spins n a) (k5Spins m a) (z a)

/-- **An admissible boundary**: every node label `z a` lies in the channel `(J₁ J₂) z (J₃ J₄)` of
the SU(2) spins `J = n + m` of its legs, so that `ι_{z a}` is an intertwiner (`ivec_isIntertwiner`).
For other labels `ι_{z a}` is not an intertwiner and `eprlVertex` has no meaning; every value
theorem below assumes this condition. -/
def IsVertexBoundary (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ) : Prop :=
  ∀ a, z a ∈ channel (k5Spins (n + m) a 0) (k5Spins (n + m) a 1) (k5Spins (n + m) a 2)
    (k5Spins (n + m) a 3)

instance (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ) : Decidable (IsVertexBoundary n m z) := by
  unfold IsVertexBoundary; infer_instance

/-- **EPRL labels on the ten edges**: `(n e, m e)` are the doubled EPRL labels `(2j⁺, 2j⁻)` of the
SU(2) spin `J e = n e + m e` for the Immirzi parameter `γ` (`IsEPRLLabel`). -/
def IsEPRLVertexLabel (γ : ℝ) (n m : Fin 10 → ℕ) : Prop :=
  ∀ e, IsEPRLLabel γ (n e + m e) (n e) (m e)

/-- **The vertex as a sum over Spin(4) intertwiners**: expanding every node tensor `Φ(ι_{z_a})` in
the basis `ι⁺_x ⊗ ι⁻_y`, the vertex is `Σ_{x,y} Π_a f_a(z_a; x_a, y_a)` times the product of a
self-dual and an anti-self-dual SU(2) contraction. -/
theorem eprlVertex_eq_sum (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ) :
    eprlVertex n m z =
      ∑ P ∈ Fintype.piFinset (fun a => nodeChannel4 (k5Spins n a) (k5Spins m a)),
        (∏ a, nodeFusion (k5Spins n a) (k5Spins m a) (z a) (P a).1 (P a).2) *
          k5Contract n (fun a => fourJNode (k5Spins n a) (P a).1) *
          k5Contract m (fun a => fourJNode (k5Spins m a) (P a).2) := by
  unfold eprlVertex eprlNode
  rw [k5Contract4_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [k5Contract4_mul, mul_assoc]

/-- **The EPRL vertex in the spin-network form** (Engle–Pereira–Rovelli–Livine 2008, eq. (31)):
`A_v = Σ_{x,y} Π_a f_a(z_a; x_a, y_a) {15j}(n; x) {15j}(m; y)`, with the 4-simplex contraction
`Lightlike.Recoupling.fifteenJSimplex` on the self-dual and on the anti-self-dual spins. -/
theorem eprlVertex_eq_fifteenJ (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ) :
    eprlVertex n m z =
      ∑ P ∈ Fintype.piFinset (fun a => nodeChannel4 (k5Spins n a) (k5Spins m a)),
        (∏ a, nodeFusion (k5Spins n a) (k5Spins m a) (z a) (P a).1 (P a).2) *
          (fifteenJSimplex (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) (n 9)
            (P 0).1 (P 1).1 (P 2).1 (P 3).1 (P 4).1 : ℂ) *
          (fifteenJSimplex (m 0) (m 1) (m 2) (m 3) (m 4) (m 5) (m 6) (m 7) (m 8) (m 9)
            (P 0).2 (P 1).2 (P 2).2 (P 3).2 (P 4).2 : ℂ) := by
  rw [eprlVertex_eq_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [fifteenJSimplex_eq_k5Contract n (fun a => (P a).1),
    fifteenJSimplex_eq_k5Contract m (fun a => (P a).2)]

/-! ## Basic properties -/

/-- **Selection rule**: the vertex vanishes unless the self-dual spins at every node add up to an
even number (`channel_eq_empty_of_not_even`). -/
theorem eprlVertex_eq_zero_of_not_even_left (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ) (a : Fin 5)
    (h : ¬ Even (∑ k, k5Spins n a k)) : eprlVertex n m z = 0 := by
  rw [eprlVertex_eq_sum]
  have he : Fintype.piFinset (fun a => nodeChannel4 (k5Spins n a) (k5Spins m a)) = ∅ := by
    refine Fintype.piFinset_eq_empty.mpr ⟨a, ?_⟩
    rw [Fin.sum_univ_four] at h
    rw [nodeChannel4, channel4, channel_eq_empty_of_not_even h, empty_product]
  rw [he, sum_empty]

/-- **Selection rule**: the vertex vanishes unless the anti-self-dual spins at every node add up
to an even number. -/
theorem eprlVertex_eq_zero_of_not_even_right (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ) (a : Fin 5)
    (h : ¬ Even (∑ k, k5Spins m a k)) : eprlVertex n m z = 0 := by
  rw [eprlVertex_eq_sum]
  have he : Fintype.piFinset (fun a => nodeChannel4 (k5Spins n a) (k5Spins m a)) = ∅ := by
    refine Fintype.piFinset_eq_empty.mpr ⟨a, ?_⟩
    rw [Fin.sum_univ_four] at h
    rw [nodeChannel4, channel4, channel_eq_empty_of_not_even h, product_empty]
  rw [he, sum_empty]

/-- The leg spins of the zero labelling are zero. -/
lemma k5Spins_zero (a : Fin 5) : k5Spins 0 a = 0 := by
  ext k
  fin_cases a <;> fin_cases k <;> rfl

/-- The leg spins of a sum of labellings. -/
lemma k5Spins_add (n m : Fin 10 → ℕ) (a : Fin 5) :
    k5Spins (n + m) a = k5Spins n a + k5Spins m a := by
  ext k
  fin_cases a <;> fin_cases k <;> rfl

/-- **Value check.** With all spins zero the vertex is `1`. -/
theorem eprlVertex_zero : eprlVertex 0 0 0 = 1 := by
  rw [eprlVertex_eq_fifteenJ]
  simp only [k5Spins_zero, Pi.zero_apply]
  have hc : nodeChannel4 0 0 = {(0, 0)} := by
    simp [nodeChannel4, channel4, channel_zero 0]
  rw [show (fun _ : Fin 5 => nodeChannel4 0 0) = fun _ => {(0, 0)} from funext fun _ => hc,
    Fintype.piFinset_singleton, sum_singleton]
  have hf : nodeFusion 0 0 0 0 0 = 1 := by
    rw [nodeFusion]
    simpa using fusion_two_valent 0 0
  simp [hf, fifteenJSimplex_zero]

/-! ## The self-dual sector: the vertex at `m = 0` is the SU(2) 15j symbol -/

/-- With trivial anti-self-dual spin the EPRL map is the identity:
`Y e_c = e_c ⊗ e_0`, i.e. `⟨e_a ⊗ e_0 | Y e_c⟩ = δ_{ac}`. -/
lemma eprlMap_zero_right (n : ℕ) (p : Idx n 0) (c : Fin (n + 0 + 1)) :
    eprlMap n 0 p c = if (p.1 : ℕ) = c then 1 else 0 := by
  rw [eprlMap_apply]
  have hp2 : (p.2 : ℕ) = 0 := by have := p.2.isLt; omega
  simp only [hp2, add_zero, Nat.choose_zero_right, mul_one]
  split_ifs with h
  · rw [← h, div_self, Real.sqrt_one, Complex.ofReal_one]
    have := Nat.choose_pos (Nat.lt_succ_iff.mp p.1.isLt)
    positivity
  · rfl

/-- With trivial anti-self-dual spins the lifted intertwiner is the intertwiner itself:
`(Y₁ ⊗ Y₂) T (Y₃ ⊗ Y₄)ᴴ = T ⊗ 1`. -/
lemma eprlLift_zero_right {n₁ n₂ n₃ n₄ : ℕ}
    (T : Matrix (Idx (n₁ + 0) (n₂ + 0)) (Idx (n₃ + 0) (n₄ + 0)) ℂ)
    (P : Idx n₁ n₂ × Idx 0 0) (Q : Idx n₃ n₄ × Idx 0 0) :
    eprlLift n₁ n₂ n₃ n₄ 0 0 0 0 T P Q = T P.1 Q.1 := by
  simp only [eprlLift, mul_apply, conjTranspose_apply, eprlPair_apply, eprlMap_zero_right]
  rw [Finset.sum_eq_single (Q.1 : Idx (n₃ + 0) (n₄ + 0))]
  · rw [Finset.sum_eq_single (P.1 : Idx (n₁ + 0) (n₂ + 0))]
    · simp
    · intro c _ hc
      have : (P.1.1 : ℕ) ≠ c.1 ∨ (P.1.2 : ℕ) ≠ c.2 := by
        by_contra h
        simp only [not_or, not_not] at h
        exact hc (Prod.ext (Fin.ext h.1.symm) (Fin.ext h.2.symm))
      rcases this with h | h <;> simp [h]
    · simp
  · intro d _ hd
    have : (Q.1.1 : ℕ) ≠ d.1 ∨ (Q.1.2 : ℕ) ≠ d.2 := by
      by_contra h
      simp only [not_or, not_not] at h
      exact hd (Prod.ext (Fin.ext h.1.symm) (Fin.ext h.2.symm))
    rcases this with h | h <;> simp [h]
  · simp

/-- The intertwiner of four spins `0` is `1`. -/
lemma ivec_zero_apply (p q : Idx 0 0) : ivec 0 0 0 0 0 p q = 1 := by
  have h := cgCoefficient_singlet (n := 0) (a := 0) le_rfl
  simp only [Nat.sub_self, pow_zero, Nat.cast_zero, zero_add, Real.sqrt_one, div_one] at h
  simp [ivec, cgz, mul_apply, h]

/-- **The self-dual fusion coefficients**: with trivial anti-self-dual spins,
`f(z; x, 0) = δ_{xz}`. -/
theorem fusion_zero_right {n₁ n₂ n₃ n₄ x z : ℕ} (hx : x ∈ channel n₁ n₂ n₃ n₄)
    (hz : z ∈ channel n₁ n₂ n₃ n₄) :
    fusion n₁ n₂ n₃ n₄ 0 0 0 0 z x 0 = if x = z then 1 else 0 := by
  rw [← hsInner_ivec hx hz, fusion, hsInner, hsInner]
  simp only [eprlLift_zero_right, ivec4, kroneckerMap_apply, ivec_zero_apply, mul_one,
    Fintype.sum_prod_type]
  simp

/-- **The vertex with trivial anti-self-dual spins is the SU(2) 15j symbol**: for `m = 0`
(formally `γ = 1`, `j⁻ = 0`) the EPRL vertex is the 4-simplex contraction `fifteenJSimplex` of SU(2)
BF theory (Ooguri's model) with the same spins and intertwiners. -/
theorem eprlVertex_zero_right (n : Fin 10 → ℕ) (z : Fin 5 → ℕ) (hz : IsVertexBoundary n 0 z) :
    eprlVertex n 0 z =
      (fifteenJSimplex (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) (n 9)
        (z 0) (z 1) (z 2) (z 3) (z 4) : ℂ) := by
  simp only [IsVertexBoundary, add_zero] at hz
  have h0 : (0 : ℕ) ∈ channel 0 0 0 0 := zero_mem_channel 0 0
  rw [eprlVertex_eq_fifteenJ, Finset.sum_eq_single_of_mem (fun a => (z a, 0))]
  · have hf : ∀ a, nodeFusion (k5Spins n a) (k5Spins 0 a) (z a) (z a) 0 = 1 := fun a => by
      rw [nodeFusion, k5Spins_zero]
      exact (fusion_zero_right (hz a) (hz a)).trans (ite_eq_left rfl)
    simp only [hf, prod_const_one, one_mul, Pi.zero_apply, fifteenJSimplex_zero,
      Complex.ofReal_one, mul_one]
  · refine Fintype.mem_piFinset.mpr fun a => ?_
    rw [nodeChannel4, channel4, k5Spins_zero, mem_product]
    exact ⟨hz a, h0⟩
  · intro P hP hne
    obtain ⟨a, ha⟩ : ∃ a, P a ≠ (z a, 0) := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hne (funext h)
    have hPa := Fintype.mem_piFinset.mp hP a
    rw [nodeChannel4, channel4, k5Spins_zero, mem_product] at hPa
    have h2 : (P a).2 = 0 := by
      have := hPa.2
      simp only [Pi.zero_apply] at this
      rw [channel_zero 0, mem_singleton] at this
      exact this
    have h1 : (P a).1 ≠ z a := fun h => ha (Prod.ext h h2)
    have hf : nodeFusion (k5Spins n a) (k5Spins 0 a) (z a) (P a).1 (P a).2 = 0 := by
      rw [nodeFusion, k5Spins_zero, h2]
      exact (fusion_zero_right hPa.1 (hz a)).trans (ite_eq_right h1)
    rw [Finset.prod_eq_zero (mem_univ a) hf, zero_mul, zero_mul]

/-! ## The 9j form: the vertex is real -/

/-- The fusion coefficient of a node in 9j form (Alesci–Bianchi–Magliaro–Perini 2010, eq. (7)),
`√((x+1)(y+1)(z+1) Π_k (J_k+1)) {n₁ n₂ x; m₁ m₂ y; J₁ J₂ z} {n₃ n₄ x; m₃ m₄ y; J₃ J₄ z}`, with the
SU(2) spins `J` of the legs a separate argument. For the EPRL map `J = n + m`
(`fusion_eq_nineJSym`); other choices of `J` model other simplicity constraints. -/
noncomputable def nodeFusionNineJ (n m J : Fin 4 → ℕ) (z x y : ℕ) : ℝ :=
  Real.sqrt (((x : ℝ) + 1) * ((y : ℝ) + 1) * ((z : ℝ) + 1) * ((J 0 : ℝ) + 1) * ((J 1 : ℝ) + 1) *
      ((J 2 : ℝ) + 1) * ((J 3 : ℝ) + 1)) *
    nineJSym (n 0) (n 1) x (m 0) (m 1) y (J 0) (J 1) z *
    nineJSym (n 2) (n 3) x (m 2) (m 3) y (J 2) (J 3) z

/-- **The vertex in 9j form**, `Σ_{x,y} Π_a f_a(z_a; x_a, y_a) {15j}(n; x) {15j}(m; y)` with the
fusion coefficients `nodeFusionNineJ` of SU(2) spins `J`; a real number. For `J = n + m` it is the
EPRL vertex (`eprlVertex_eq_vertexNineJ`). -/
noncomputable def vertexNineJ (n m J : Fin 10 → ℕ) (z : Fin 5 → ℕ) : ℝ :=
  ∑ P ∈ Fintype.piFinset (fun a => nodeChannel4 (k5Spins n a) (k5Spins m a)),
    (∏ a, nodeFusionNineJ (k5Spins n a) (k5Spins m a) (k5Spins J a) (z a) (P a).1 (P a).2) *
      fifteenJSimplex (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) (n 9)
        (P 0).1 (P 1).1 (P 2).1 (P 3).1 (P 4).1 *
      fifteenJSimplex (m 0) (m 1) (m 2) (m 3) (m 4) (m 5) (m 6) (m 7) (m 8) (m 9)
        (P 0).2 (P 1).2 (P 2).2 (P 3).2 (P 4).2

/-- **The EPRL vertex in 9j form**: on an admissible boundary,
`A_v = Σ_{x,y} Π_a f_a {15j}(n; x) {15j}(m; y)` with the fusion coefficients as products of two 9j
symbols of SU(2) spins `J = n + m`. -/
theorem eprlVertex_eq_vertexNineJ (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ)
    (hz : IsVertexBoundary n m z) : eprlVertex n m z = (vertexNineJ n m (n + m) z : ℂ) := by
  rw [eprlVertex_eq_fifteenJ, vertexNineJ]
  push_cast
  refine Finset.sum_congr rfl fun P hP => ?_
  congr 2
  refine Finset.prod_congr rfl fun a _ => ?_
  have hPa := mem_product.mp (Fintype.mem_piFinset.mp hP a)
  have hza := hz a
  simp only [k5Spins_add, Pi.add_apply] at hza
  rw [nodeFusion, fusion_eq_nineJSym hPa.1 hPa.2 hza, nodeFusionNineJ]
  simp only [k5Spins_add, Pi.add_apply]

/-- **The EPRL vertex is real** on an admissible boundary. -/
theorem eprlVertex_im (n m : Fin 10 → ℕ) (z : Fin 5 → ℕ) (hz : IsVertexBoundary n m z) :
    (eprlVertex n m z).im = 0 := by
  rw [eprlVertex_eq_vertexNineJ n m z hz, Complex.ofReal_im]

end Lightlike.Spin4
