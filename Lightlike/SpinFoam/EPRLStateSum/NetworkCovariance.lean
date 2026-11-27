import Lightlike.SpinFoam.EPRLStateSum.RelabelComplex
import Lightlike.SpinFoam.EPRLStateSum.ContractPerm

/-!
# The network of a relabelled complex

The 4-simplices, the nodes (a 4-simplex with the position of an omitted vertex) and the tetrahedra of `relabelComplex K σ` correspond to
those of `K`: `fwd`, `theta`, with the position permutations `phi`.
-/

open Finset Lightlike.FourD

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

end Lightlike.SpinFoam.EPRLStateSum
