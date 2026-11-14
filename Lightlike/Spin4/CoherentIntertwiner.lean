import Lightlike.Spin4.Coherent
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Complex.Basic

/-!
# Livine–Speziale coherent intertwiners

A node of a spin network with `N` links of spins `J a / 2` (doubled, `a : Fin N`, all links
outgoing) carries the space `⊗_a V_{J_a/2}`, here the functions on `LIdx J = Π_a Fin (J a + 1)`,
with the diagonal action `ρ(g) = ⊗_a D^{J_a/2}(g)` (`rhoN`). Group averaging
`P = ∫ ρ(g) dg` (`avgP`) is the orthogonal projection onto the invariant subspace, and the
**Livine–Speziale coherent intertwiner** of the group elements `g_a` is the projection of the
product of coherent states,

`ι(g⃗) = P (⊗_a |J_a/2, g_a⟩)`  (`cohInt`).

## Main results

* `rhoN_mul`, `rhoN_unitary`: `ρ` is a unitary representation.
* `avgP_mulVec_of_invariant`, `rhoN_mul_avgP`, `avgP_conjTranspose`, `avgP_mul_avgP`: `P` fixes the
  invariant vectors, has invariant range, and is a Hermitian idempotent, i.e. the orthogonal
  projection onto the invariant subspace.
* `inner_cohInt`: **the overlap formula**
  `⟨ι(g⃗), ι(h⃗)⟩ = ∫ Π_a ((g_aᴴ k h_a)₀₀)^{J_a} dk`.
* `resolution_cohInt`: **resolution of the identity on the invariant subspace**
  `Π_a (J_a + 1) ∫ |ι(g⃗)⟩⟨ι(g⃗)| dg⃗ = P`.

## References

* E. R. Livine, S. Speziale, *A new spinfoam vertex for quantum gravity*, Phys. Rev. D 76 (2007)
  084028, arXiv:0705.0674.
* F. Conrady, L. Freidel, *Quantum geometry from phase space reduction*, J. Math. Phys. 50 (2009)
  123510, arXiv:0902.0351 (coherent intertwiners and their norm).
-/

open Matrix MeasureTheory Finset
open scoped Kronecker

namespace Lightlike.Spin4

open SU2

variable {N : ℕ} (J : Fin N → ℕ)

/-- The basis labels of `⊗_a V_{J_a/2}`. -/
abbrev LIdx := (a : Fin N) → Fin (J a + 1)

/-- **The diagonal action** `ρ(g) = ⊗_a D^{J_a/2}(g)` on `⊗_a V_{J_a/2}`. -/
noncomputable def rhoN (g : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (LIdx J) (LIdx J) ℂ :=
  Matrix.of fun k l => ∏ a, spinMat (J a) g (k a) (l a)

/-- The product vector `⊗_a v_a`. -/
def prodVec (v : (a : Fin N) → Fin (J a + 1) → ℂ) : LIdx J → ℂ := fun k => ∏ a, v a (k a)

variable {J}

/-- `ρ` is multiplicative. -/
theorem rhoN_mul (g h : Matrix (Fin 2) (Fin 2) ℂ) : rhoN J (g * h) = rhoN J g * rhoN J h := by
  ext k l
  simp only [rhoN, of_apply, mul_apply, spinMat_mul]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun x _ => Finset.prod_mul_distrib

lemma rhoN_one : rhoN J 1 = 1 := by
  ext k l
  simp only [rhoN, of_apply, spinMat_one, one_apply]
  by_cases h : k = l
  · subst h; simp
  · rw [ite_eq_right h]
    obtain ⟨a, ha⟩ : ∃ a, k a ≠ l a := not_forall.mp fun hc => h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

lemma rhoN_conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ) : (rhoN J g)ᴴ = rhoN J gᴴ := by
  ext k l
  simp only [rhoN, conjTranspose_apply, of_apply, star_prod, ← spinMat_conjTranspose]

/-- `ρ` is unitary on SU(2). -/
theorem rhoN_unitary (g : SU2) : (rhoN J g)ᴴ * rhoN J g = 1 := by
  have hu : ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * g = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
  rw [rhoN_conjTranspose, ← rhoN_mul, hu, rhoN_one]

/-- `ρ(g)` acts factorwise on product vectors. -/
theorem rhoN_mulVec_prodVec (g : Matrix (Fin 2) (Fin 2) ℂ) (v : (a : Fin N) → Fin (J a + 1) → ℂ) :
    rhoN J g *ᵥ prodVec J v = prodVec J fun a => spinMat (J a) g *ᵥ v a := by
  funext k
  simp only [mulVec, dotProduct, rhoN, of_apply, prodVec]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun l _ => (Finset.prod_mul_distrib).symm

/-- The inner product of product vectors is the product of the inner products. -/
theorem inner_prodVec (v w : (a : Fin N) → Fin (J a + 1) → ℂ) :
    star (prodVec J v) ⬝ᵥ prodVec J w = ∏ a, star (v a) ⬝ᵥ w a := by
  simp only [dotProduct, prodVec, Pi.star_apply, star_prod]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun l _ => (Finset.prod_mul_distrib).symm

/-! ## B. Group averaging: the projection onto the invariant subspace -/

lemma continuous_rhoN_apply (k l : LIdx J) : Continuous fun g : SU2 => rhoN J g k l := by
  show Continuous fun g : SU2 => ∏ a, spinMat (J a) (g : Matrix (Fin 2) (Fin 2) ℂ) (k a) (l a)
  exact continuous_finsetProd _ fun a _ => continuous_spinMat_apply (J a) (k a) (l a)

lemma continuous_rhoN_mulVec_apply (v : LIdx J → ℂ) (i : LIdx J) :
    Continuous fun g : SU2 => (rhoN J g *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => (continuous_rhoN_apply i j).mul continuous_const

lemma star_star_dotProduct {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    star (star a ⬝ᵥ b) = star b ⬝ᵥ a := by
  simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- An integral of matrices applied to a vector. -/
lemma matInt_mulVec {ι κ : Type*} [Fintype κ] (F : SU2 → Matrix ι κ ℂ) (v : κ → ℂ)
    (hF : ∀ i j, Continuous fun g => F g i j) :
    matInt F *ᵥ v = fun i => ∫ g, (F g *ᵥ v) i ∂haarSU2 := by
  funext i
  simp only [mulVec, dotProduct, matInt_apply]
  rw [integral_finsetSum _ fun j _ => (integrable_of_continuous (hF i j)).mul_const _]
  exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm

lemma dotProduct_integral {ι : Type*} [Fintype ι] (w : ι → ℂ) (f : SU2 → ι → ℂ)
    (hf : ∀ i, Continuous fun g => f g i) :
    w ⬝ᵥ (fun i => ∫ g, f g i ∂haarSU2) = ∫ g, w ⬝ᵥ f g ∂haarSU2 := by
  simp only [dotProduct]
  rw [integral_finsetSum _ fun i _ => (integrable_of_continuous (hf i)).const_mul _]
  exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm

variable (J) in
/-- **Group averaging** `P = ∫ ρ(g) dg`. -/
noncomputable def avgP : Matrix (LIdx J) (LIdx J) ℂ := matInt fun g : SU2 => rhoN J g

variable (J) in
/-- An invariant vector of `⊗_a V_{J_a/2}`. -/
def IsInvariantN (v : LIdx J → ℂ) : Prop := ∀ g : SU2, rhoN J g *ᵥ v = v

/-- `P` fixes the invariant vectors. -/
theorem avgP_mulVec_of_invariant {v : LIdx J → ℂ} (hv : IsInvariantN J v) : avgP J *ᵥ v = v := by
  rw [avgP, matInt_mulVec _ _ continuous_rhoN_apply]
  funext i
  have hv' : ∀ g : SU2, rhoN J g *ᵥ v = v := hv
  simp [hv']

/-- `ρ(h) P = P`. -/
theorem rhoN_mul_avgP (h : SU2) : rhoN J h * avgP J = avgP J := by
  have e := matInt_mul_mul (rhoN J h) (fun g : SU2 => rhoN J g)
    (1 : Matrix (LIdx J) (LIdx J) ℂ) continuous_rhoN_apply
  rw [Matrix.mul_one] at e
  rw [avgP, ← e]
  simp only [Matrix.mul_one]
  have : (fun g : SU2 => rhoN J h * rhoN J g) = fun g : SU2 => rhoN J ((h * g : SU2) :
      Matrix (Fin 2) (Fin 2) ℂ) := by
    funext g
    rw [show ((h * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = (h : Matrix (Fin 2) (Fin 2) ℂ) * g from
      rfl, rhoN_mul]
  rw [this]
  exact matInt_mul_left (fun g : SU2 => rhoN J g) h

/-- The range of `P` is invariant. -/
theorem isInvariantN_avgP_mulVec (v : LIdx J → ℂ) : IsInvariantN J (avgP J *ᵥ v) := fun h => by
  rw [mulVec_mulVec, rhoN_mul_avgP]

/-- `⟨w, P v⟩ = ⟨w, v⟩` for an invariant `w`. -/
theorem inner_avgP_of_invariant {w : LIdx J → ℂ} (hw : IsInvariantN J w) (v : LIdx J → ℂ) :
    star w ⬝ᵥ (avgP J *ᵥ v) = star w ⬝ᵥ v := by
  rw [avgP, matInt_mulVec _ _ continuous_rhoN_apply,
    dotProduct_integral _ (fun g : SU2 => rhoN J g *ᵥ v) (continuous_rhoN_mulVec_apply v)]
  have : ∀ g : SU2, star w ⬝ᵥ (rhoN J g *ᵥ v) = star w ⬝ᵥ v := fun g => by
    have hg := hw (star g)
    rw [show ((star g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ from
      rfl, ← rhoN_conjTranspose] at hg
    rw [dotProduct_mulVec, ← conjTranspose_conjTranspose (rhoN J g), ← star_mulVec, hg]
  simp [this]

/-- `⟨u, P v⟩ = ⟨P u, v⟩`. -/
lemma inner_avgP_symm (u v : LIdx J → ℂ) :
    star u ⬝ᵥ (avgP J *ᵥ v) = star (avgP J *ᵥ u) ⬝ᵥ v := by
  have h1 := inner_avgP_of_invariant (isInvariantN_avgP_mulVec u) v
  have h2 := congrArg star (inner_avgP_of_invariant (isInvariantN_avgP_mulVec v) u)
  rw [star_star_dotProduct, star_star_dotProduct] at h2
  rw [← h2, h1]

/-- `P` is Hermitian. -/
theorem avgP_conjTranspose : (avgP J)ᴴ = avgP J := by
  ext i j
  have h := inner_avgP_symm (J := J) (Pi.single i 1) (Pi.single j 1)
  have hs : star (Pi.single i (1 : ℂ) : LIdx J → ℂ) = Pi.single i 1 := by
    funext x; by_cases hx : x = i <;> simp [hx]
  have hl : star (Pi.single i (1 : ℂ) : LIdx J → ℂ) ⬝ᵥ (avgP J *ᵥ Pi.single j 1) = avgP J i j := by
    rw [hs, mulVec_single_one, single_one_dotProduct]; rfl
  have hr : star (avgP J *ᵥ Pi.single i (1 : ℂ)) ⬝ᵥ (Pi.single j 1 : LIdx J → ℂ) =
      star (avgP J j i) := by
    rw [mulVec_single_one, dotProduct_single_one]; rfl
  rw [conjTranspose_apply, ← hr, ← h, hl]

/-- `P` is idempotent. -/
theorem avgP_mul_avgP : avgP J * avgP J = avgP J := by
  refine matrix_eq_of_mulVec fun v => ?_
  rw [← mulVec_mulVec, avgP_mulVec_of_invariant (isInvariantN_avgP_mulVec v)]

/-! ## C. Coherent intertwiners and their overlaps -/

variable (J) in
/-- **The Livine–Speziale coherent intertwiner** `ι(g⃗) = P (⊗_a |J_a/2, g_a⟩)`. -/
noncomputable def cohInt (g : Fin N → SU2) : LIdx J → ℂ :=
  avgP J *ᵥ prodVec J fun a => cohState (J a) (g a)

/-- Coherent intertwiners are invariant. -/
theorem cohInt_isInvariantN (g : Fin N → SU2) : IsInvariantN J (cohInt J g) :=
  isInvariantN_avgP_mulVec _

lemma spinMat_mulVec_cohState (n : ℕ) (k h : Matrix (Fin 2) (Fin 2) ℂ) :
    spinMat n k *ᵥ cohState n h = cohState n (k * h) := by
  rw [cohState, cohState, mulVec_mulVec, spinMat_mul]

/-- `⟨P x, P y⟩ = ⟨x, P y⟩`. -/
lemma inner_avgP_avgP (x y : LIdx J → ℂ) :
    star (avgP J *ᵥ x) ⬝ᵥ (avgP J *ᵥ y) = star x ⬝ᵥ (avgP J *ᵥ y) := by
  rw [← inner_avgP_symm, avgP_mulVec_of_invariant (isInvariantN_avgP_mulVec y)]

/-- **The overlap formula** of coherent intertwiners:
`⟨ι(g⃗), ι(h⃗)⟩ = ∫ Π_a ((g_aᴴ k h_a)₀₀)^{J_a} dk`. -/
theorem inner_cohInt (g h : Fin N → SU2) :
    star (cohInt J g) ⬝ᵥ cohInt J h =
      ∫ k : SU2, ∏ a, ((((g a : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (k * h a)) 0 0) ^ (J a) ∂haarSU2 := by
  rw [cohInt, cohInt, inner_avgP_avgP, avgP, matInt_mulVec _ _ continuous_rhoN_apply,
    dotProduct_integral _ _ (continuous_rhoN_mulVec_apply _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only
  rw [rhoN_mulVec_prodVec, inner_prodVec]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [spinMat_mulVec_cohState, inner_cohState]

/-- The squared norm of a coherent intertwiner: `‖ι(g⃗)‖² = ∫ Π_a ((g_aᴴ k g_a)₀₀)^{J_a} dk`. -/
theorem norm_sq_cohInt (g : Fin N → SU2) :
    star (cohInt J g) ⬝ᵥ cohInt J g =
      ∫ k : SU2, ∏ a, ((((g a : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (k * g a)) 0 0) ^ (J a) ∂haarSU2 :=
  inner_cohInt g g

/-! ## D. Resolution of the identity on the invariant subspace -/

variable (N) in
/-- The normalised Haar measure on `SU(2)^N`. -/
noncomputable def haarN : Measure (Fin N → SU2) := Measure.pi fun _ => haarSU2

instance : IsProbabilityMeasure (haarN N) := by unfold haarN; infer_instance

/-- The integral over `SU(2)^N` of a matrix-valued function, entry by entry. -/
noncomputable def matIntN {ι κ : Type*} (F : (Fin N → SU2) → Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  Matrix.of fun i j => ∫ g, F g i j ∂haarN N

section Integrability

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology SU2 := TopologicalSpace.Subtype.secondCountableTopology _

lemma integrableN_of_continuous {f : (Fin N → SU2) → ℂ} (hf : Continuous f) :
    Integrable f (haarN N) := by
  unfold haarN
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end Integrability

lemma matIntN_mul_mul {ι κ μ ν : Type*} [Fintype κ] [Fintype μ] (A : Matrix ι κ ℂ)
    (F : (Fin N → SU2) → Matrix κ μ ℂ) (B : Matrix μ ν ℂ)
    (hF : ∀ k l, Continuous fun g => F g k l) :
    matIntN (fun g => A * F g * B) = A * matIntN F * B := by
  ext i j
  have hI : ∀ k l, Integrable (fun g => F g k l) (haarN N) := fun k l =>
    integrableN_of_continuous (hF k l)
  have hin : ∀ l, Integrable (fun g => ∑ k, A i k * F g k l) (haarN N) := fun l =>
    integrable_finsetSum _ fun k _ => (hI k l).const_mul _
  calc matIntN (fun g => A * F g * B) i j
      = ∫ g, ∑ l, (∑ k, A i k * F g k l) * B l j ∂haarN N := by
        simp only [matIntN, of_apply, mul_apply]
    _ = ∑ l, ∫ g, (∑ k, A i k * F g k l) * B l j ∂haarN N :=
        integral_finsetSum _ fun l _ => (hin l).mul_const _
    _ = ∑ l, (∑ k, A i k * ∫ g, F g k l ∂haarN N) * B l j := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [integral_mul_const, integral_finsetSum _ fun k _ => (hI k l).const_mul _]
        simp only [integral_const_mul]
    _ = (A * matIntN F * B) i j := by simp only [mul_apply, matIntN, of_apply]

lemma vecMulVec_mulVec {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x : ι → ℂ) :
    vecMulVec (A *ᵥ x) (star (A *ᵥ x)) = A * vecMulVec x (star x) * Aᴴ := by
  ext k l
  simp only [vecMulVec_apply, mul_apply, mulVec, dotProduct, conjTranspose_apply, Pi.star_apply,
    star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma continuous_cohState_apply (n : ℕ) (a : Fin N) (i : Fin (n + 1)) :
    Continuous fun g : Fin N → SU2 => cohState n (g a) i := by
  simp only [cohState, mulVec_single_one, Matrix.col_apply]
  exact (continuous_spinMat_apply n i 0).comp (continuous_apply a)

lemma continuous_prodVec_cohState (k : LIdx J) :
    Continuous fun g : Fin N → SU2 => prodVec J (fun a => cohState (J a) (g a)) k :=
  continuous_finsetProd _ fun a _ => continuous_cohState_apply (J a) a (k a)

/-- The entries of `∫ |j, g⟩⟨j, g| dg = 1/(2j+1)`. -/
lemma matInt_cohState_apply (n : ℕ) (i j : Fin (n + 1)) :
    matInt (fun g : SU2 => vecMulVec (cohState n g) (star (cohState n g))) i j =
      ((n : ℂ) + 1)⁻¹ * if i = j then 1 else 0 := by
  have h := congrFun (congrFun (resolution_cohState n) i) j
  rw [Matrix.smul_apply, smul_eq_mul, one_apply] at h
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- `Π_a (J_a + 1) ∫ |⊗ g_a⟩⟨⊗ g_a| dg⃗ = 1`. -/
lemma resolution_prodVec :
    (∏ a, ((J a : ℂ) + 1)) • matIntN (fun g : Fin N → SU2 =>
      vecMulVec (prodVec J fun a => cohState (J a) (g a))
        (star (prodVec J fun a => cohState (J a) (g a)))) = 1 := by
  ext k l
  rw [Matrix.smul_apply, smul_eq_mul, one_apply]
  have hentry : matIntN (fun g : Fin N → SU2 =>
      vecMulVec (prodVec J fun a => cohState (J a) (g a))
        (star (prodVec J fun a => cohState (J a) (g a)))) k l =
      ∏ a, (((J a : ℂ) + 1)⁻¹ * if k a = l a then 1 else 0) := by
    simp only [matIntN, of_apply, vecMulVec_apply, prodVec, Pi.star_apply, star_prod, haarN,
      ← Finset.prod_mul_distrib]
    rw [integral_fintype_prod_eq_prod (fun a (g : SU2) => cohState (J a) g (k a) *
      star (cohState (J a) g (l a)))]
    exact Finset.prod_congr rfl fun a _ => by
      rw [← matInt_cohState_apply]
      simp [matInt_apply, vecMulVec_apply]
  rw [hentry, ← Finset.prod_mul_distrib]
  have hcancel : ∀ a, ((J a : ℂ) + 1) * (((J a : ℂ) + 1)⁻¹ * if k a = l a then 1 else 0) =
      if k a = l a then 1 else 0 := fun a => by
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero (J a)), one_mul]
  simp only [hcancel]
  by_cases hkl : k = l
  · subst hkl; simp
  · rw [ite_eq_right hkl]
    obtain ⟨a, ha⟩ : ∃ a, k a ≠ l a := not_forall.mp fun hc => hkl (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

/-- **Resolution of the identity on the invariant subspace**:
`Π_a (J_a + 1) ∫ |ι(g⃗)⟩⟨ι(g⃗)| dg⃗ = P`, the orthogonal projection onto the invariants. -/
theorem resolution_cohInt :
    (∏ a, ((J a : ℂ) + 1)) •
      matIntN (fun g : Fin N → SU2 => vecMulVec (cohInt J g) (star (cohInt J g))) = avgP J := by
  simp only [cohInt, vecMulVec_mulVec]
  rw [matIntN_mul_mul _ _ _ fun k l => ?_, ← Matrix.smul_mul, ← Matrix.mul_smul,
    resolution_prodVec, Matrix.mul_one, avgP_conjTranspose, avgP_mul_avgP]
  simp only [vecMulVec_apply, Pi.star_apply]
  exact (continuous_prodVec_cohState k).mul
    (continuous_star.comp (continuous_prodVec_cohState l))

/-! ## E. Spin(4) coherent intertwiners -/

variable {K : Fin N → ℕ}

/-- **The Spin(4) coherent intertwiner** of self-dual labels `J`, anti-self-dual labels `K` and
group elements `(g₊, g₋)`: `ι⁺(g⃗₊) ⊗ ι⁻(g⃗₋)`, invariant under `ρ_J(g₊) ⊗ ρ_K(g₋)`. -/
noncomputable def cohInt4 (J K : Fin N → ℕ) (g : (Fin N → SU2) × (Fin N → SU2)) :
    LIdx J × LIdx K → ℂ :=
  fun p => cohInt J g.1 p.1 * cohInt K g.2 p.2

/-- The Spin(4) coherent intertwiners are invariant. -/
theorem cohInt4_invariant (g : (Fin N → SU2) × (Fin N → SU2)) (h : Spin4) :
    (rhoN J h.1 ⊗ₖ rhoN K h.2) *ᵥ cohInt4 J K g = cohInt4 J K g := by
  unfold cohInt4
  rw [kronecker_mulVec_prod, cohInt_isInvariantN g.1 h.1, cohInt_isInvariantN g.2 h.2]

/-- **The overlap of Spin(4) coherent intertwiners** is the product of the two SU(2) overlaps. -/
theorem inner_cohInt4 (g h : (Fin N → SU2) × (Fin N → SU2)) :
    star (cohInt4 J K g) ⬝ᵥ cohInt4 J K h =
      (star (cohInt J g.1) ⬝ᵥ cohInt J h.1) * (star (cohInt K g.2) ⬝ᵥ cohInt K h.2) := by
  simp only [cohInt4, dotProduct, Pi.star_apply, star_mul', Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Resolution of the identity on the Spin(4) invariant subspace**:
`Π_a (J_a+1)(K_a+1) ∫∫ |ι⁺ ⊗ ι⁻⟩⟨ι⁺ ⊗ ι⁻| = P_J ⊗ P_K`. -/
theorem resolution_cohInt4 :
    ((∏ a, ((J a : ℂ) + 1)) * ∏ a, ((K a : ℂ) + 1)) •
      (Matrix.of fun p q => ∫ g, vecMulVec (cohInt4 J K g) (star (cohInt4 J K g)) p q
        ∂(haarN N).prod (haarN N)) = avgP J ⊗ₖ avgP K := by
  have h : (Matrix.of fun p q => ∫ g, vecMulVec (cohInt4 J K g) (star (cohInt4 J K g)) p q
      ∂(haarN N).prod (haarN N)) =
        matIntN (fun g : Fin N → SU2 => vecMulVec (cohInt J g) (star (cohInt J g))) ⊗ₖ
          matIntN (fun g : Fin N → SU2 => vecMulVec (cohInt K g) (star (cohInt K g))) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [of_apply, kroneckerMap_apply, matIntN, vecMulVec_apply, cohInt4, Pi.star_apply,
      star_mul']
    rw [← integral_prod_mul (fun g : Fin N → SU2 => cohInt J g a * star (cohInt J g c))
      (fun g : Fin N → SU2 => cohInt K g b * star (cohInt K g d))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp only; ring)
  rw [h, ← resolution_cohInt (J := J), ← resolution_cohInt (J := K), smul_kronecker,
    kronecker_smul, smul_smul]

end Lightlike.Spin4
