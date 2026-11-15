import Lightlike.Spin4.CoherentIntertwiner
import Lightlike.SpinFoam.IntertwinerCount
import Lightlike.SpinFoam.Tetrahedron
import Lightlike.Asymptotics.EPRL.Amplitude
import Lightlike.Spin4.Vertex
import Lightlike.Asymptotics.EPRL.EdgeBridge

/-!
# The coherent intertwiner as a Haar integral

`Lightlike.Spin4.cohInt` is defined through the projector `P = ∫ ρ(g) dg` (`avgP`). This file
writes its components as a single Haar integral over `SU(2)`, the form in which the node
tensors of the `K₅` contraction multiply into the coherent `15j` integral, and computes the
edge pairing of two coherent states: `u ⬝ᵥ (W v) = ((Aᵀ w B)₀₀)^n`.
-/

open Matrix MeasureTheory
open scoped BigOperators

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SpinFoam Lightlike.SU2 Lightlike.Recoupling

variable {N : ℕ} (J : Fin N → ℕ)

/-- **The coherent intertwiner is a Haar integral.** For every component `k`,
`ι(g⃗)_k = ∫ (ρ(X) ⊗_a |J_a/2, g_a⟩)_k dX`, with `ρ = rhoN J` and the Haar probability measure
on `SU(2)`. -/
theorem cohInt_apply_eq_integral (g : Fin N → SU2) (k : LIdx J) :
    cohInt J g k =
      ∫ X : SU2, (rhoN J (X : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        prodVec J fun a => cohState (J a) (g a)) k ∂haarSU2 := by
  rw [cohInt, avgP, matInt_mulVec _ _ continuous_rhoN_apply]



/-- **The edge pairing of two coherent states**: `⟨cohState A, W cohState B⟩ = ((Aᵀ w B)₀₀)^n`
(bilinear, no complex conjugation), with `W = Wm n` and `w = wM`. -/
theorem cohState_pair (n : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    cohState n A ⬝ᵥ (Wm n *ᵥ cohState n B) = ((Aᵀ * wM * B) 0 0) ^ n := by
  rw [cohState, cohState, Wm, mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec,
    mulVec_mulVec, spinMat_transpose, ← spinMat_mul, ← spinMat_mul, ← spinMat_zero_zero]
  simp [dotProduct, mulVec, Pi.single_apply, Matrix.mul_assoc]

/-- For `M ∈ SU(2)`, `εᴴ Mᴴ = Mᵀ w`: the antilinear structure map turns the adjoint into the
transpose. -/
theorem epsMat_mul_conjTranspose (M : SU2) :
    epsMatᴴ * (M : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (M : Matrix (Fin 2) (Fin 2) ℂ)ᵀ * wM := by
  obtain ⟨h11, h01, -⟩ := su2_entries M
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [epsMat, wM, mul_apply, Fin.sum_univ_two, conjTranspose_apply, h11, h01]

/-- **The propagator is the coherent-state pairing**: for `X_a, X_b, g_ab, g_ba ∈ SU(2)`,
`prop = ((X_a g_ab)ᵀ w (X_b g_ba))₀₀`. -/
theorem prop_eq_pair (g0 g1 Xa Xb : SU2) :
    ((g0 * epsMat : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (Xa : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
        (Xb : Matrix (Fin 2) (Fin 2) ℂ) * (g1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 =
      (((Xa * g0 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ * wM *
        ((Xb * g1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 := by
  rw [← epsMat_mul_conjTranspose (Xa * g0)]
  simp only [Submonoid.coe_mul, conjTranspose_mul, Matrix.mul_assoc]

/-- The node (`edgeSrc`) end of the edge `e` of `K₅`, as a leg of the node. -/
def srcLeg : Fin 10 → Fin 4 := ![0, 1, 2, 3, 0, 1, 2, 0, 1, 0]

/-- The target end of the edge `e` of `K₅`, as a leg of the node `edgeTgt e`. -/
def tgtLeg : Fin 10 → Fin 4 := ![3, 2, 1, 0, 3, 2, 1, 3, 2, 3]

/-- **Regrouping the `K₅` contraction by edges.** If the node tensors are products
`T_a(κ) = Π_l f_{a,l}(κ_l)` over their legs, the contraction is the product over the ten edges
of the edge pairings `Σ_μ ε(μ) f_{src}(μ) f_{tgt}(-μ)`. -/
theorem k5Contract_prod (j : Fin 10 → ℕ) (f : Fin 5 → Fin 4 → ℤ → ℂ) :
    k5Contract j (fun a κ => ∏ l, f a l (κ l)) =
      ∏ e : Fin 10, ∑ μ ∈ Finset.Icc (-(j e : ℤ)) (j e),
        (edgeSign (j e) μ : ℂ) * f (edgeSrc e) (srcLeg e) μ * f (edgeTgt e) (tgtLeg e) (-μ) := by
  unfold k5Contract k5Box
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Finset.prod_mul_distrib]
  simp [Fin.prod_univ_succ, k5Legs, edgeSrc, srcLeg, tgtLeg, edgeTgt]
  ring


/-- **Fubini for the `K₅` contraction**: if the node tensors are Haar integrals
`T_a(κ) = ∫ G_a(X, κ) dX` of continuous functions, the contraction is the integral over
`SU(2)^5` of the contraction of the integrands at `(X_0, …, X_4)`. -/
theorem k5Contract_integral (j : Fin 10 → ℕ) (G : Fin 5 → SU2 → (Fin 4 → ℤ) → ℂ)
    (hG : ∀ a κ, Continuous fun X => G a X κ) :
    k5Contract j (fun a κ => ∫ X, G a X κ ∂haarSU2) =
      ∫ X : Fin 5 → SU2, k5Contract j (fun a κ => G a (X a) κ) ∂haarN 5 := by
  unfold k5Contract
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact (MeasureTheory.integral_fintype_prod_eq_prod (μ := fun _ : Fin 5 => haarSU2)
      (fun a X => G a X (k5Legs μ a))).symm
  · intro μ _
    refine (integrableN_of_continuous ?_).const_mul _
    exact continuous_finsetProd _ fun a _ => (hG a _).comp (continuous_apply a)


/-- The components of a coherent state `|n/2, X g⟩` are continuous in `X ∈ SU(2)`. -/
theorem continuous_cohState_apply (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin (n + 1)) :
    Continuous fun X : SU2 => cohState n ((X : Matrix (Fin 2) (Fin 2) ℂ) * g) a := by
  have : (fun X : SU2 => cohState n ((X : Matrix (Fin 2) (Fin 2) ℂ) * g) a) =
      fun X : SU2 => spinMat n ((X : Matrix (Fin 2) (Fin 2) ℂ) * g) a 0 := by
    funext X
    rw [cohState, mulVec_single_one]; rfl
  rw [this]
  exact (continuous_apply (0 : Fin (n + 1))).comp ((continuous_apply a).comp
    (continuous_spinMat.comp ((continuous_subtype_val.mul continuous_const))))

/-- `ρ(X)` acts on a product vector factor by factor. -/
theorem rhoN_mulVec_prodVec {N : ℕ} (J : Fin N → ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (a : Fin N) → Fin (J a + 1) → ℂ) (k : LIdx J) :
    (rhoN J X *ᵥ prodVec J v) k = ∏ a, (spinMat (J a) X *ᵥ v a) (k a) := by
  simp only [mulVec, dotProduct, rhoN, of_apply, prodVec, mulVec]
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun i _ => (Finset.prod_mul_distrib).symm


/-- **A node tensor on projections**: the components `T_k` of a vector on `LIdx J` placed at the
projections `κ_l = J_l - 2 k_l` of the four legs (`0` elsewhere). -/
noncomputable def projNode (J : Fin 4 → ℕ) (T : LIdx J → ℂ) (κ : Fin 4 → ℤ) : ℂ :=
  ∑ k : LIdx J, (∏ l, if κ l = (J l : ℤ) - 2 * ((k l : Fin (J l + 1)) : ℕ) then (1 : ℂ) else 0) * T k

/-- **The node tensor of a coherent intertwiner is a Haar integral of a product over the legs**:
`ι(g⃗)` on projections is `∫ Π_l projVec(|J_l/2, X g_l⟩)(κ_l) dX`. -/
theorem projNode_cohInt (J : Fin 4 → ℕ) (g : Fin 4 → SU2) (κ : Fin 4 → ℤ) :
    projNode J (cohInt J g) κ =
      ∫ X : SU2, ∏ l, projVec (J l) (cohState (J l) ((X : Matrix (Fin 2) (Fin 2) ℂ) * g l)) (κ l)
        ∂haarSU2 := by
  have hk : ∀ k : LIdx J, cohInt J g k =
      ∫ X : SU2, ∏ l, cohState (J l) ((X : Matrix (Fin 2) (Fin 2) ℂ) * g l) (k l) ∂haarSU2 := by
    intro k
    rw [cohInt_apply_eq_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show (rhoN J _ *ᵥ _) k = _
    rw [rhoN_mulVec_prodVec]
    simp only [spinMat_mulVec_cohState]
  have hcont : ∀ k : LIdx J, Continuous fun X : SU2 =>
      ∏ l, cohState (J l) ((X : Matrix (Fin 2) (Fin 2) ℂ) * g l) (k l) := fun k =>
    continuous_finsetProd _ fun l _ => continuous_cohState_apply _ _ _
  have hint : ∀ k : LIdx J, Integrable (fun X : SU2 =>
      (∏ l, if κ l = (J l : ℤ) - 2 * ((k l : Fin (J l + 1)) : ℕ) then (1 : ℂ) else 0) *
        ∏ l, cohState (J l) ((X : Matrix (Fin 2) (Fin 2) ℂ) * g l) (k l)) haarSU2 := fun k =>
    (integrable_of_continuous (hcont k)).const_mul _
  unfold projNode
  simp_rw [hk, ← integral_const_mul]
  rw [← integral_finsetSum _ fun k _ => hint k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [projVec]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun l _ => by split_ifs <;> simp


/-- **One edge**: the `edgeSign` pairing of the projection vectors of `|n/2, X_a g_ab⟩` and
`|n/2, X_b g_ba⟩` is the `n`-th power of the propagator. -/
theorem edge_pairing_eq_prop (n : ℕ) (g0 g1 Xa Xb : SU2) :
    ∑ μ ∈ Finset.Icc (-(n : ℤ)) n, (edgeSign n μ : ℂ) *
        projVec n (cohState n ((Xa : Matrix (Fin 2) (Fin 2) ℂ) * g0)) μ *
        projVec n (cohState n ((Xb : Matrix (Fin 2) (Fin 2) ℂ) * g1)) (-μ) =
      ((((g0 : Matrix (Fin 2) (Fin 2) ℂ) * epsMat)ᴴ * (Xa : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
        (Xb : Matrix (Fin 2) (Fin 2) ℂ) * (g1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0) ^ n := by
  rw [edgePair_eq, cohState_pair, prop_eq_pair]
  rfl

/-- The boundary matrices at the four legs of each node of `K₅`, in the leg order of `k5Legs`:
the edge `e` contributes `g e 0` at its source node and `g e 1` at its target node. -/
def nodeBdry (g : Fin 10 → Fin 2 → SU2) : Fin 5 → Fin 4 → SU2 :=
  ![![g 0 0, g 1 0, g 2 0, g 3 0], ![g 4 0, g 5 0, g 6 0, g 0 1], ![g 7 0, g 8 0, g 1 1, g 4 1],
    ![g 9 0, g 2 1, g 5 1, g 7 1], ![g 3 1, g 6 1, g 8 1, g 9 1]]


/-- The projection vector of `|n/2, X g⟩` is continuous in `X ∈ SU(2)`. -/
theorem continuous_projVec_cohState (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) (μ : ℤ) :
    Continuous fun X : SU2 => projVec n (cohState n ((X : Matrix (Fin 2) (Fin 2) ℂ) * g)) μ := by
  unfold projVec
  refine continuous_finsetSum _ fun a _ => ?_
  split_ifs
  · exact continuous_cohState_apply n g a
  · exact continuous_const


/-- **The coherent `15j` integral is the `K₅` contraction of the coherent intertwiners.** With the
node tensors `ι(g⃗_a)` of `cohInt`, placed on the projections of their legs, the contraction
`k5Contract` along the edge form `edgeSign` is exactly `coh15j`, with no extra sign: for SU(2)
boundary data `g`, `k5Contract n (ι(g⃗_a))_a = ∫ Π_e prop_e^{n_e} dX`. -/
theorem k5Contract_cohInt (n : Fin 10 → ℕ) (g : Fin 10 → Fin 2 → SU2) :
    k5Contract n (fun a => projNode (k5Spins n a) (cohInt (k5Spins n a) (nodeBdry g a))) =
      coh15j n (fun e s => (g e s : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have h1 : (fun a => projNode (k5Spins n a) (cohInt (k5Spins n a) (nodeBdry g a))) =
      fun a κ => ∫ X : SU2, ∏ l, projVec (k5Spins n a l)
        (cohState (k5Spins n a l) ((X : Matrix (Fin 2) (Fin 2) ℂ) * nodeBdry g a l)) (κ l)
        ∂haarSU2 := by
    funext a κ
    exact projNode_cohInt _ _ _
  rw [h1, k5Contract_integral _ (fun a X κ => ∏ l, projVec (k5Spins n a l)
    (cohState (k5Spins n a l) ((X : Matrix (Fin 2) (Fin 2) ℂ) * nodeBdry g a l)) (κ l))
    fun a κ => continuous_finsetProd _ fun l _ => continuous_projVec_cohState _ _ _]
  · unfold coh15j
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show _ = cohAmp n _ (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))
    beta_reduce
    rw [k5Contract_prod, cohAmp]
    refine Finset.prod_congr rfl fun e _ => ?_
    fin_cases e
    all_goals exact edge_pairing_eq_prop _ _ _ _ _

/-! ### Trust checks -/

/-- Control: the edge pairing sees the structure map. For `n = 1` and `A = B = 1` the pairing
`(Aᵀ w B)₀₀` is `0`, while the overlap `(Aᴴ B)₀₀` is `1`; the two forms are not interchangeable. -/
theorem pair_ne_overlap :
    (((1 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ * wM * (1 : Matrix (Fin 2) (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) 0 0) ≠
      (((1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (1 : Matrix (Fin 2) (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  simp [wM]

end Lightlike.Asymptotics.EPRL
