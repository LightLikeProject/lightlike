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

end Lightlike.SpinFoam.EPRLStateSum
