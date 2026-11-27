import Lightlike.SpinFoam.EPRLStateSum.RelabelComplex
import Lightlike.SpinFoam.EPRLStateSum.ContractPerm
import Lightlike.Recoupling.Loop

/-!
# The network of a relabelled complex

The 4-simplices, the nodes (a 4-simplex with the position of an omitted vertex) and the tetrahedra of `relabelComplex K σ` correspond to
those of `K`: `fwd`, `theta`, with the position permutations `phi`.
-/

open Finset Lightlike.FourD Lightlike.Recoupling

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V] (K : Complex4 V) (σ : V ≃ V)

/-- The 4-simplex `σ s` of the relabelled complex. -/
def fwd (s : K.simps) : (relabelComplex K σ).simps :=
  ⟨s.1.map σ.toEmbedding, (mem_relabel_simps K σ _).2 (by rw [map_map_symm]; exact s.2)⟩

/-- The 4-simplex `σ⁻¹ s'` of `K`. -/
def bwd (s' : (relabelComplex K σ).simps) : K.simps :=
  ⟨s'.1.map σ.symm.toEmbedding, (mem_relabel_simps K σ _).1 s'.2⟩

lemma bwd_fwd (s : K.simps) : bwd K σ (fwd K σ s) = s := Subtype.ext (map_map_symm σ s.1)

lemma fwd_bwd (s' : (relabelComplex K σ).simps) : fwd K σ (bwd K σ s') = s' := Subtype.ext (map_symm_map σ s'.1)

/-- The position permutation of the 4-simplex `s`. -/
noncomputable def phi (s : K.simps) : Equiv.Perm (Fin 5) := posPerm σ s.1 (K.card_eq _ s.2)

/-- The node `(σ s, φ_s⁻¹ a)` of the relabelled complex of the node `(s, a)`. -/
noncomputable def theta (x : K.simps × Fin 5) : (relabelComplex K σ).simps × Fin 5 :=
  (fwd K σ x.1, (phi K σ x.1).symm x.2)

/-- The inverse of `theta`. -/
noncomputable def thetaInv (x' : (relabelComplex K σ).simps × Fin 5) : K.simps × Fin 5 :=
  (bwd K σ x'.1, phi K σ (bwd K σ x'.1) x'.2)

lemma phi_fwd (s : K.simps) : phi K σ (bwd K σ (fwd K σ s)) = phi K σ s := by rw [bwd_fwd]

lemma thetaInv_theta (x : K.simps × Fin 5) : thetaInv K σ (theta K σ x) = x := by
  obtain ⟨s, a⟩ := x
  unfold theta thetaInv
  simp only [bwd_fwd, Prod.mk.injEq, true_and]
  simp

lemma theta_thetaInv (x' : (relabelComplex K σ).simps × Fin 5) : theta K σ (thetaInv K σ x') = x' := by
  obtain ⟨s', a'⟩ := x'
  unfold theta thetaInv
  simp only [fwd_bwd, Prod.mk.injEq, true_and]
  have : phi K σ (bwd K σ s') = phi K σ (bwd K σ s') := rfl
  simp

/-- The nodes of a relabelled complex are the nodes of `K`. -/
noncomputable def thetaEquiv : K.simps × Fin 5 ≃ (relabelComplex K σ).simps × Fin 5 where
  toFun := theta K σ
  invFun := thetaInv K σ
  left_inv := thetaInv_theta K σ
  right_inv := theta_thetaInv K σ

lemma orderEmb_congr {s t : Finset V} {n : ℕ} (hs : #s = n) (ht : #t = n) (h : s = t) (i : Fin n) :
    s.orderEmbOfFin hs i = t.orderEmbOfFin ht i := by
  subst h; rfl

/-- The tetrahedron of the relabelled node is the relabelled tetrahedron. -/
lemma incSet_theta (x : K.simps × Fin 5) :
    incSet (relabelComplex K σ) (theta K σ x) = (incSet K x).map σ.toEmbedding := by
  obtain ⟨s, a⟩ := x
  unfold incSet theta
  simp only
  have hs := K.card_eq _ s.2
  have hs' : #((fwd K σ s).1) = 5 := (relabelComplex K σ).card_eq _ (fwd K σ s).2
  have h1 : ((fwd K σ s).1).orderEmbOfFin hs' ((phi K σ s).symm a) = σ (s.1.orderEmbOfFin hs a) := by
    have := orderEmb_relabel σ s.1 hs ((phi K σ s).symm a)
    have e : s.1.orderEmbOfFin hs (posPerm σ s.1 hs ((phi K σ s).symm a)) = s.1.orderEmbOfFin hs a := by
      show s.1.orderEmbOfFin hs ((phi K σ s) ((phi K σ s).symm a)) = _
      rw [Equiv.apply_symm_apply]
    unfold fwd
    simp only
    rw [this]
    show σ (s.1.orderEmbOfFin hs ((phi K σ s) ((phi K σ s).symm a))) = _
    rw [Equiv.apply_symm_apply]
  unfold fwd at h1 ⊢
  simp only at h1 ⊢
  rw [h1]
  exact (Finset.map_erase σ.toEmbedding s.1 _).symm

/-- The tetrahedron `σ t` of the relabelled complex. -/
def tetFwd (t : K.tets) : (relabelComplex K σ).tets :=
  ⟨t.1.map σ.toEmbedding, (mem_relabel_faces K σ 3 _).2 (by rw [map_map_symm]; exact t.2)⟩

lemma tetFwd_injective : Function.Injective (tetFwd K σ) := by
  intro t1 t2 h
  apply Subtype.ext
  have := congrArg (fun t : (relabelComplex K σ).tets => t.1.map σ.symm.toEmbedding) h
  simpa [tetFwd, map_map_symm] using this

lemma incTet_theta (x : K.simps × Fin 5) :
    incTet (relabelComplex K σ) (theta K σ x) = tetFwd K σ (incTet K x) :=
  Subtype.ext (incSet_theta K σ x)

lemma theta_injective : Function.Injective (theta K σ) :=
  fun x y h => by simpa [thetaInv_theta] using congrArg (thetaInv K σ) h

/-- **The fibre of a relabelled tetrahedron** is the image of the fibre. -/
lemma fiberOf_tetFwd (t : K.tets) :
    fiberOf (relabelComplex K σ) (tetFwd K σ t) = (fiberOf K t).image (theta K σ) := by
  classical
  ext x'
  simp only [fiberOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    refine ⟨thetaInv K σ x', ?_, theta_thetaInv K σ x'⟩
    have h2 := incTet_theta K σ (thetaInv K σ x')
    rw [theta_thetaInv] at h2
    rw [h2] at h
    exact tetFwd_injective K σ h
  · rintro ⟨x, hx, rfl⟩
    rw [incTet_theta, hx]

/-- The sorted legs of the relabelled tetrahedron are the old legs permuted by `ordPerm`. -/
lemma tetLeg_relabel (col : Finset V → ℕ) (t : K.tets) (i : Fin 4) :
    tetLeg (relabelComplex K σ) (relabelCol σ col) (tetFwd K σ t) i =
      tetLeg K col t (ordPerm σ t.1 4 (Complex4.card_of_mem_faces t.2) i) := by
  have ht := Complex4.card_of_mem_faces t.2
  unfold tetLeg relabelCol tetFwd
  simp only
  have h1 : (t.1.map σ.toEmbedding).orderEmbOfFin (Complex4.card_of_mem_faces ((tetFwd K σ t).2)) i =
      σ (t.1.orderEmbOfFin ht (ordPerm σ t.1 4 ht i)) := by
    rw [← orderEmb_relabel_ord σ t.1 4 ht i]
  rw [h1]
  congr 1
  rw [show (t.1.map σ.toEmbedding).erase (σ (t.1.orderEmbOfFin ht (ordPerm σ t.1 4 ht i))) =
      (t.1.erase (t.1.orderEmbOfFin ht (ordPerm σ t.1 4 ht i))).map σ.toEmbedding from
      (Finset.map_erase σ.toEmbedding t.1 _).symm, map_map_symm]

/-- The permutation of the four sorted legs of the tetrahedron of a node. -/
noncomputable def legPerm (x : K.simps × Fin 5) : Equiv.Perm (Fin 4) :=
  ordPerm σ (incSet K x) 4 (incSet_card K x)

/-- **The slot permutation of a node**: the sorted neighbours of the relabelled node are the sorted neighbours of the node, permuted by `legPerm`. -/
lemma phi_succAbove (x : K.simps × Fin 5) (i : Fin 4) :
    phi K σ x.1 (((phi K σ x.1).symm x.2).succAbove i) = x.2.succAbove (legPerm K σ x i) := by
  obtain ⟨s, a⟩ := x
  have hs := K.card_eq _ s.2
  apply (s.1.orderEmbOfFin hs).injective
  -- the right side
  have hR : s.1.orderEmbOfFin hs (a.succAbove (legPerm K σ (s, a) i)) =
      (incSet K (s, a)).orderEmbOfFin (incSet_card K (s, a)) (legPerm K σ (s, a) i) := by
    unfold incSet
    exact (orderEmbOfFin_erase hs a _ _).symm
  -- the left side
  have hL : s.1.orderEmbOfFin hs (phi K σ s (((phi K σ s).symm a).succAbove i)) =
      (incSet K (s, a)).orderEmbOfFin (incSet_card K (s, a)) (legPerm K σ (s, a) i) := by
    have h1 : s.1.orderEmbOfFin hs (phi K σ s (((phi K σ s).symm a).succAbove i)) =
        σ.symm ((fwd K σ s).1.orderEmbOfFin ((relabelComplex K σ).card_eq _ (fwd K σ s).2)
          (((phi K σ s).symm a).succAbove i)) :=
      orderEmb_posPerm σ s.1 hs _
    have h2 : (fwd K σ s).1.orderEmbOfFin ((relabelComplex K σ).card_eq _ (fwd K σ s).2)
        (((phi K σ s).symm a).succAbove i) =
        (incSet (relabelComplex K σ) (theta K σ (s, a))).orderEmbOfFin
          (incSet_card (relabelComplex K σ) (theta K σ (s, a))) i := by
      unfold incSet theta
      exact (orderEmbOfFin_erase _ _ _ _).symm
    have h3 : (incSet (relabelComplex K σ) (theta K σ (s, a))).orderEmbOfFin
          (incSet_card (relabelComplex K σ) (theta K σ (s, a))) i =
        ((incSet K (s, a)).map σ.toEmbedding).orderEmbOfFin
          (by rw [Finset.card_map]; exact incSet_card K (s, a)) i :=
      orderEmb_congr _ _ (incSet_theta K σ (s, a)) i
    have h4 : ((incSet K (s, a)).map σ.toEmbedding).orderEmbOfFin
          (by rw [Finset.card_map]; exact incSet_card K (s, a)) i =
        σ ((incSet K (s, a)).orderEmbOfFin (incSet_card K (s, a)) (legPerm K σ (s, a) i)) :=
      orderEmb_relabel_ord σ (incSet K (s, a)) 4 (incSet_card K (s, a)) i
    rw [h1, h2, h3, h4]
    simp
  rw [hR, hL]

/-- The four leg spins of the node `x`, in the sorted order. -/
noncomputable def legSpins (col : Finset V → ℕ) (x : K.simps × Fin 5) : Fin 4 → ℕ :=
  fun i => complexJ K col x.1 x.2 (x.2.succAbove i)

/-- The four leg projections read by the node `x`, in the sorted order. -/
def legReads (x : K.simps × Fin 5) (m : Fin 10 → ℤ) : Fin 4 → ℤ := fun i => legProj m x.2 (x.2.succAbove i)

lemma nodeF_eq_fourJT (col : Finset V → ℕ) (x : K.simps × Fin 5) (m : Fin 10 → ℤ) (k : ℕ) :
    nodeF K col x m k = fourJT (legSpins K col x 0) (legSpins K col x 1) (legSpins K col x 2) (legSpins K col x 3) k
      (legReads K x m) := rfl

/-- **The node factor of the relabelled node** is the old one with the legs permuted by `legPerm`. -/
lemma nodeF_theta (col : Finset V → ℕ) (x : K.simps × Fin 5) (m : Fin 10 → ℤ) (k : ℕ) :
    nodeF (relabelComplex K σ) (relabelCol σ col) (theta K σ x) (permProj (phi K σ x.1) m) k =
      fourJP (legSpins K col x) (legPerm K σ x) k (legReads K x m) := by
  obtain ⟨s, a⟩ := x
  have hphi : phi K σ s ((phi K σ s).symm a) = a := Equiv.apply_symm_apply _ _
  have hJ : ∀ i : Fin 4, complexJ (relabelComplex K σ) (relabelCol σ col) (fwd K σ s) ((phi K σ s).symm a)
      (((phi K σ s).symm a).succAbove i) = legSpins K col (s, a) (legPerm K σ (s, a) i) := by
    intro i
    rw [complexJ_relabel K σ col s (fwd K σ s) rfl]
    show complexJ K col s (phi K σ s ((phi K σ s).symm a))
      (phi K σ s (((phi K σ s).symm a).succAbove i)) = _
    rw [hphi, phi_succAbove K σ (s, a) i]
    rfl
  have hR : ∀ i : Fin 4, legProj (permProj (phi K σ s) m) ((phi K σ s).symm a) (((phi K σ s).symm a).succAbove i) =
      legReads K (s, a) m (legPerm K σ (s, a) i) := by
    intro i
    rw [legProj_permProj, hphi, phi_succAbove K σ (s, a) i]
    rfl
  unfold nodeF sortT theta fourJP fourJT
  simp only [Function.comp]
  rw [hJ 0, hJ 1, hJ 2, hJ 3, hR 0, hR 1, hR 2, hR 3]

lemma legSpins_eq_tetLeg (col : Finset V → ℕ) (x : K.simps × Fin 5) (i : Fin 4) :
    legSpins K col x i = tetLeg K col (incTet K x) i := by
  obtain ⟨s, a⟩ := x
  exact complexJ_succAbove K col s a i

lemma ordPerm_congr {s t : Finset V} {n : ℕ} (h : s = t) (hs : #s = n) (ht : #t = n) :
    ordPerm σ s n hs = ordPerm σ t n ht := by
  subst h; rfl

lemma legPerm_eq (x y : K.simps × Fin 5) (h : incTet K x = incTet K y) : legPerm K σ x = legPerm K σ y :=
  ordPerm_congr σ (congrArg Subtype.val h) _ _

/-- **The kernel of a tetrahedron is unchanged by a relabelling**: for the two nodes `x₁, x₂` of a tetrahedron `t`, the sum over the label of the product
of the two relabelled node factors is the old one (the projector `Σ_k ι_k ⊗ ι_k` does not depend on the order of the legs). -/
theorem kernel_relabel (col : Finset V → ℕ) (x₁ x₂ : K.simps × Fin 5) (h : incTet K x₁ = incTet K x₂)
    (m₁ m₂ : Fin 10 → ℤ) :
    ∑ k ∈ tetBoxI (relabelComplex K σ) (relabelCol σ col) (tetFwd K σ (incTet K x₁)),
        nodeF (relabelComplex K σ) (relabelCol σ col) (theta K σ x₁) (permProj (phi K σ x₁.1) m₁) k *
          nodeF (relabelComplex K σ) (relabelCol σ col) (theta K σ x₂) (permProj (phi K σ x₂.1) m₂) k =
      ∑ k ∈ tetBoxI K col (incTet K x₁), nodeF K col x₁ m₁ k * nodeF K col x₂ m₂ k := by
  rw [Finset.sum_congr rfl fun k _ => by rw [nodeF_theta K σ col x₁ m₁ k, nodeF_theta K σ col x₂ m₂ k]]
  simp only [nodeF_eq_fourJT K col]
  have hj : legSpins K col x₂ = legSpins K col x₁ := by
    funext i; rw [legSpins_eq_tetLeg, legSpins_eq_tetLeg, h]
  have hp : legPerm K σ x₂ = legPerm K σ x₁ := (legPerm_eq K σ x₁ x₂ h).symm
  rw [hj, hp]
  have hbox : tetBoxI (relabelComplex K σ) (relabelCol σ col) (tetFwd K σ (incTet K x₁)) =
      range (legSpins K col x₁ (legPerm K σ x₁ 0) + legSpins K col x₁ (legPerm K σ x₁ 1) + 1) := by
    unfold tetBoxI
    rw [tetLeg_relabel, tetLeg_relabel, legSpins_eq_tetLeg, legSpins_eq_tetLeg]
    rfl
  have hbox' : tetBoxI K col (incTet K x₁) = range (legSpins K col x₁ 0 + legSpins K col x₁ 1 + 1) := by
    unfold tetBoxI
    rw [legSpins_eq_tetLeg, legSpins_eq_tetLeg]
  rw [hbox, hbox']
  exact (sum_fourJT_mul_perm (legSpins K col x₁) (legPerm K σ x₁) (legReads K x₁ m₁) (legReads K x₂ m₂)).symm

/-- The summand of the network. -/
noncomputable def netTerm (K : Complex4 V) (col : Finset V → ℕ) (M : K.simps → Fin 10 → ℤ) : ℝ :=
  (∏ s : K.simps, edgeW (complexJ K col s) (M s)) *
    ∏ t : K.tets, ∑ k ∈ tetBoxI K col t, ∏ x ∈ fiberOf K t, nodeF K col x (M x.1) k

/-- **The network of a complex**: the sum of `netTerm` over the families of edge projections. -/
noncomputable def Znet (K : Complex4 V) (col : Finset V → ℕ) : ℝ :=
  ∑ M ∈ Fintype.piFinset (fun s : K.simps => projBox K col s), netTerm K col M

/-- A node whose factor vanishes for every label kills the summand. -/
lemma netTerm_eq_zero_of_node (K : Complex4 V) (col : Finset V → ℕ) (M : K.simps → Fin 10 → ℤ)
    (x : K.simps × Fin 5) (h : ∀ k, nodeF K col x (M x.1) k = 0) : netTerm K col M = 0 := by
  unfold netTerm
  rw [mul_eq_zero]
  right
  refine Finset.prod_eq_zero (Finset.mem_univ (incTet K x)) ?_
  refine Finset.sum_eq_zero fun k _ => ?_
  exact Finset.prod_eq_zero (i := x) (by simp [fiberOf]) (h k)

/-- The node factor vanishes if one of its legs reads a non-admissible projection. -/
lemma nodeF_eq_zero_of_not_adm (K : Complex4 V) (col : Finset V → ℕ) (x : K.simps × Fin 5) (m : Fin 10 → ℤ) (k : ℕ)
    (i : Fin 4) (h : ¬ AdmProj (legSpins K col x i) (legReads K x m i)) : nodeF K col x m k = 0 := by
  rw [nodeF_eq_fourJT]
  have hI := isInv_fourJT (legSpins K col x 0) (legSpins K col x 1) (legSpins K col x 2) (legSpins K col x 3) k
  refine hI.eq_zero (i := i) ?_
  fin_cases i <;> simpa using h

/-- The tetrahedron `σ⁻¹ t'` of `K`. -/
def tetBwd (t' : (relabelComplex K σ).tets) : K.tets :=
  ⟨t'.1.map σ.symm.toEmbedding, (mem_relabel_faces K σ 3 _).1 t'.2⟩

/-- The tetrahedra of a relabelled complex are those of `K`. -/
def tetEquiv : K.tets ≃ (relabelComplex K σ).tets where
  toFun := tetFwd K σ
  invFun := tetBwd K σ
  left_inv t := Subtype.ext (map_map_symm σ t.1)
  right_inv t' := Subtype.ext (map_symm_map σ t'.1)

/-- The 4-simplices of a relabelled complex are those of `K`. -/
def fwdEquiv : K.simps ≃ (relabelComplex K σ).simps where
  toFun := fwd K σ
  invFun := bwd K σ
  left_inv := bwd_fwd K σ
  right_inv := fwd_bwd K σ

/-- **Every tetrahedron of a closed complex has two incidences.** -/
lemma fiberOf_card (hK : K.IsClosed4) (t : K.tets) : (fiberOf K t).card = 2 := by
  classical
  have h := card_incFiber K t
  rw [Fintype.card_subtype] at h
  have h2 := hK t.1 t.2
  unfold fiberOf
  rw [h]
  exact h2

lemma fiberOf_eq_pair (hK : K.IsClosed4) (t : K.tets) :
    ∃ x₁ x₂, x₁ ≠ x₂ ∧ fiberOf K t = {x₁, x₂} := by
  obtain ⟨x₁, x₂, hne, h⟩ := Finset.card_eq_two.1 (fiberOf_card K hK t)
  exact ⟨x₁, x₂, hne, h⟩

/-- The reparametrisation of the families of edge projections of `K` as families of `relabelComplex K σ`. -/
noncomputable def projRelabel (M : K.simps → Fin 10 → ℤ) : (relabelComplex K σ).simps → Fin 10 → ℤ :=
  fun s' => permProj (phi K σ (bwd K σ s')) (M (bwd K σ s'))

lemma projRelabel_fwd (M : K.simps → Fin 10 → ℤ) (s : K.simps) :
    projRelabel K σ M (fwd K σ s) = permProj (phi K σ s) (M s) := by
  unfold projRelabel
  simp only [bwd_fwd]

/-- Every leg of every node reads an admissible projection. -/
def Good (col : Finset V → ℕ) (M : K.simps → Fin 10 → ℤ) : Prop :=
  ∀ (x : K.simps × Fin 5) (i : Fin 4), AdmProj (legSpins K col x i) (legReads K x (M x.1) i)

lemma Good.parity {col : Finset V → ℕ} {M : K.simps → Fin 10 → ℤ} (hg : Good K col M) (s : K.simps) (e : Fin 10) :
    ((jE (complexJ K col s) e : ℤ) - M s e) % 2 = 0 := by
  have hlt := epr_lt e
  obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq (x := (epr e).2) (y := (epr e).1) (ne_of_gt hlt)
  have h := (hg (s, (epr e).1) i).2.2
  unfold legSpins legReads at h
  simp only [hi, legProj_epr] at h
  exact h

/-- **The summand of the network of a relabelled complex**: the old summand times `(-1)` to the number of reversed links (on a closed complex). -/
theorem netTerm_relabel (hK : K.IsClosed4) (col : Finset V → ℕ) (M : K.simps → Fin 10 → ℤ) :
    netTerm (relabelComplex K σ) (relabelCol σ col) (projRelabel K σ M) =
      (-1 : ℝ) ^ (∑ s : K.simps, invSum (complexJ K col s) (phi K σ s)) * netTerm K col M := by
  by_cases hg : Good K col M
  · unfold netTerm
    have hE : ∏ s' : (relabelComplex K σ).simps,
        edgeW (complexJ (relabelComplex K σ) (relabelCol σ col) s') (projRelabel K σ M s') =
        (-1 : ℝ) ^ (∑ s : K.simps, invSum (complexJ K col s) (phi K σ s)) *
          ∏ s : K.simps, edgeW (complexJ K col s) (M s) := by
      rw [← Equiv.prod_comp (fwdEquiv K σ)]
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s _ => ?_
      show edgeW (complexJ (relabelComplex K σ) (relabelCol σ col) (fwd K σ s)) (projRelabel K σ M (fwd K σ s)) = _
      rw [projRelabel_fwd]
      have hJfun : complexJ (relabelComplex K σ) (relabelCol σ col) (fwd K σ s) =
          fun a b => complexJ K col s (phi K σ s a) (phi K σ s b) := by
        funext a b
        exact complexJ_relabel K σ col s (fwd K σ s) rfl a b
      rw [hJfun]
      unfold edgeW
      exact edgeW_permProj (complexJ K col s) (simplexJ_symm s.1 (K.card_eq _ s.2) col) (phi K σ s) (M s)
        (hg.parity K s)
    have hN : ∏ t' : (relabelComplex K σ).tets, ∑ k ∈ tetBoxI (relabelComplex K σ) (relabelCol σ col) t',
        ∏ x' ∈ fiberOf (relabelComplex K σ) t',
          nodeF (relabelComplex K σ) (relabelCol σ col) x' (projRelabel K σ M x'.1) k =
        ∏ t : K.tets, ∑ k ∈ tetBoxI K col t, ∏ x ∈ fiberOf K t, nodeF K col x (M x.1) k := by
      rw [← Equiv.prod_comp (tetEquiv K σ)]
      refine Finset.prod_congr rfl fun t _ => ?_
      show ∑ k ∈ tetBoxI (relabelComplex K σ) (relabelCol σ col) (tetFwd K σ t),
          ∏ x' ∈ fiberOf (relabelComplex K σ) (tetFwd K σ t),
            nodeF (relabelComplex K σ) (relabelCol σ col) x' (projRelabel K σ M x'.1) k = _
      obtain ⟨x₁, x₂, hne, hfib⟩ := fiberOf_eq_pair K hK t
      have h1 : incTet K x₁ = t := by
        have : x₁ ∈ fiberOf K t := by rw [hfib]; simp
        simpa [fiberOf] using this
      have h2 : incTet K x₂ = t := by
        have : x₂ ∈ fiberOf K t := by rw [hfib]; simp
        simpa [fiberOf] using this
      have hne' : theta K σ x₁ ≠ theta K σ x₂ := fun h => hne (theta_injective K σ h)
      rw [fiberOf_tetFwd, hfib, Finset.image_insert, Finset.image_singleton]
      simp only [Finset.prod_pair hne', Finset.prod_pair hne]
      have := kernel_relabel K σ col x₁ x₂ (h1.trans h2.symm) (M x₁.1) (M x₂.1)
      rw [h1] at this
      subst h1
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      show nodeF (relabelComplex K σ) (relabelCol σ col) (theta K σ x₁) (projRelabel K σ M (fwd K σ x₁.1)) k *
          nodeF (relabelComplex K σ) (relabelCol σ col) (theta K σ x₂) (projRelabel K σ M (fwd K σ x₂.1)) k = _
      rw [projRelabel_fwd, projRelabel_fwd]
    rw [hE, hN]
    ring
  · obtain ⟨x, i, hbad⟩ : ∃ (x : K.simps × Fin 5) (i : Fin 4),
        ¬ AdmProj (legSpins K col x i) (legReads K x (M x.1) i) := by
      by_contra h
      exact hg fun x i => by_contra fun h' => h ⟨x, i, h'⟩
    have h0 : netTerm K col M = 0 :=
      netTerm_eq_zero_of_node K col M x fun k => nodeF_eq_zero_of_not_adm K col x (M x.1) k i hbad
    have h1 : netTerm (relabelComplex K σ) (relabelCol σ col) (projRelabel K σ M) = 0 := by
      refine netTerm_eq_zero_of_node _ _ _ (theta K σ x) fun k => ?_
      show nodeF (relabelComplex K σ) (relabelCol σ col) (theta K σ x) (projRelabel K σ M (fwd K σ x.1)) k = 0
      rw [projRelabel_fwd, nodeF_theta]
      exact (isInv_fourJP (legSpins K col x) (legPerm K σ x) k).eq_zero (i := i) hbad
    rw [h0, h1, mul_zero]

lemma projRelabel_mem (col : Finset V → ℕ) {M : K.simps → Fin 10 → ℤ}
    (hM : M ∈ Fintype.piFinset (fun s : K.simps => projBox K col s)) :
    projRelabel K σ M ∈ Fintype.piFinset
      (fun s' : (relabelComplex K σ).simps => projBox (relabelComplex K σ) (relabelCol σ col) s') := by
  refine Fintype.mem_piFinset.2 fun s' => ?_
  obtain ⟨s, rfl⟩ : ∃ s, s' = fwd K σ s := ⟨bwd K σ s', (fwd_bwd K σ s').symm⟩
  rw [projRelabel_fwd]
  have hMs := Fintype.mem_piFinset.1 hM s
  have hsymm : ∀ p q, complexJ K col s p q = complexJ K col s q p := simplexJ_symm s.1 (K.card_eq _ s.2) col
  refine Fintype.mem_piFinset.2 fun e => ?_
  have h := legProj_mem (complexJ K col s) hsymm (M s) hMs (phi K σ s (epr e).1) (phi K σ s (epr e).2)
  have hJ := complexJ_relabel K σ col s (fwd K σ s) rfl (epr e).1 (epr e).2
  unfold jE
  rw [hJ]
  exact h

lemma projRelabel_symm_mem (col : Finset V → ℕ) {M' : (relabelComplex K σ).simps → Fin 10 → ℤ}
    (hM : M' ∈ Fintype.piFinset
      (fun s' : (relabelComplex K σ).simps => projBox (relabelComplex K σ) (relabelCol σ col) s')) :
    (fun s : K.simps => permProj (phi K σ s).symm (M' (fwd K σ s))) ∈
      Fintype.piFinset (fun s : K.simps => projBox K col s) := by
  refine Fintype.mem_piFinset.2 fun s => ?_
  have hMs := Fintype.mem_piFinset.1 hM (fwd K σ s)
  have hsymm : ∀ p q, complexJ (relabelComplex K σ) (relabelCol σ col) (fwd K σ s) p q =
      complexJ (relabelComplex K σ) (relabelCol σ col) (fwd K σ s) q p :=
    simplexJ_symm _ ((relabelComplex K σ).card_eq _ (fwd K σ s).2) _
  refine Fintype.mem_piFinset.2 fun e => ?_
  have h := legProj_mem _ hsymm (M' (fwd K σ s)) hMs ((phi K σ s).symm (epr e).1) ((phi K σ s).symm (epr e).2)
  have hJ : complexJ (relabelComplex K σ) (relabelCol σ col) (fwd K σ s) ((phi K σ s).symm (epr e).1)
      ((phi K σ s).symm (epr e).2) =
      complexJ K col s (phi K σ s ((phi K σ s).symm (epr e).1)) (phi K σ s ((phi K σ s).symm (epr e).2)) :=
    complexJ_relabel K σ col s (fwd K σ s) rfl _ _
  rw [hJ, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h

/-- **The network of a relabelled closed complex**: the sign `(-1)^(number of reversed links)` times the network of `K`. -/
theorem Znet_relabel (hK : K.IsClosed4) (col : Finset V → ℕ) :
    Znet (relabelComplex K σ) (relabelCol σ col) =
      (-1 : ℝ) ^ (∑ s : K.simps, invSum (complexJ K col s) (phi K σ s)) * Znet K col := by
  unfold Znet
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun M' s => permProj (phi K σ s).symm (M' (fwd K σ s))) (projRelabel K σ)
    ?_ ?_ ?_ ?_ ?_
  · intro M' hM'
    exact projRelabel_symm_mem K σ col hM'
  · intro M hM
    exact projRelabel_mem K σ col hM
  · intro M' _
    funext s'
    obtain ⟨s, rfl⟩ : ∃ s, s' = fwd K σ s := ⟨bwd K σ s', (fwd_bwd K σ s').symm⟩
    rw [projRelabel_fwd]
    simp only [permProj_permProj_symm]
  · intro M _
    funext s
    rw [show M s = M s from rfl]
    simp only [projRelabel_fwd, permProj_symm_permProj]
  · intro M' hM'
    have hM := projRelabel_symm_mem K σ col hM'
    have h := netTerm_relabel K σ hK col (fun s => permProj (phi K σ s).symm (M' (fwd K σ s)))
    have hM'eq : projRelabel K σ (fun s => permProj (phi K σ s).symm (M' (fwd K σ s))) = M' := by
      funext s'
      obtain ⟨s, rfl⟩ : ∃ s, s' = fwd K σ s := ⟨bwd K σ s', (fwd_bwd K σ s').symm⟩
      rw [projRelabel_fwd]
      simp only [permProj_permProj_symm]
    rw [hM'eq] at h
    exact h

/-- The inversion exponent counted on the old positions: the pairs `q < p` of old positions whose new order is `q` after `p`. -/
lemma invSum_eq (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (π : Equiv.Perm (Fin 5)) :
    invSum J π = ∑ e : Fin 10, if π.symm (epr e).2 < π.symm (epr e).1 then jE J e else 0 := by
  unfold invSum
  rw [← Equiv.sum_comp (Equiv.ofBijective (edgeMap π) (edgeMap_injective π).bijective_of_finite)
    (fun e => if π.symm (epr e).2 < π.symm (epr e).1 then jE J e else 0)]
  refine Finset.sum_congr rfl fun e' _ => ?_
  have hr := epr_edgeMap π e'
  have hlt := epr_lt e'
  have hne : π (epr e').1 ≠ π (epr e').2 := fun h => by
    have := π.injective h
    simp_all
  show _ = if π.symm (epr (edgeMap π e')).2 < π.symm (epr (edgeMap π e')).1 then jE J (edgeMap π e') else 0
  by_cases hc : π (epr e').1 < π (epr e').2
  · simp only [hc, if_true] at hr
    rw [hr]
    simp only [Equiv.symm_apply_apply]
    rw [if_neg (not_lt_of_gt hlt), if_neg (not_lt_of_gt hc)]
  · have hc' : π (epr e').2 < π (epr e').1 := lt_of_le_of_ne (not_lt.1 hc) (Ne.symm hne)
    simp only [hc, if_false] at hr
    rw [hr]
    simp only [Equiv.symm_apply_apply]
    rw [if_pos hlt, if_pos hc']
    unfold jE
    rw [hr]
    exact hJ _ _

end Lightlike.SpinFoam.EPRLStateSum
