import Mathlib

/-!
# Coordinate metrics on an open subset of `ℝⁿ`: the calculus needed for the distance expansion

This file is the foundation of the Mathlib-ready proof of the expansion of the squared Riemannian
distance to fifth order (`Lightlike/Upstream/GeodesicExpansion/`). It depends on Mathlib only.

A *coordinate metric* on an open `U ⊆ ℝⁿ` is a matrix-valued function `g` that is smooth, symmetric
and invertible on `U`. This file defines the partial derivative `pd`, the Christoffel symbols
(`christoffelFirst`, `christoffel`) and proves the facts about them that the expansion uses:
smoothness of `g⁻¹` and of the Christoffel symbols on `U`, symmetry of mixed partial derivatives,
and the lowering of the Christoffel index.

## Main definitions

* `pd k f x`: the partial derivative `∂_k f (x)` of a scalar function on `ℝⁿ`.
* `christoffelFirst g l j k`: Christoffel symbols of the first kind.
* `christoffel g i j k`: Christoffel symbols of the second kind.
* `IsCoordMetric g U`: `g` is smooth, symmetric and invertible on the open set `U`.

## Main results

* `contDiffOn_pd`, `pd_pd_comm`: partial derivatives of smooth functions are smooth and commute.
* `IsCoordMetric.contDiffOn_inv`, `IsCoordMetric.contDiffOn_christoffel`.
* `IsCoordMetric.lower_christoffel`: `g_{ρλ} Γ^λ_{νσ} = Γ_{ρνσ}`.
-/

open Matrix Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ}

/-! ## Partial derivatives -/

/-- The partial derivative `∂_k f (x)` of a scalar function on `ℝⁿ`. -/
def pd (k : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single k 1)

/-- `pd` only depends on the germ of the function. -/
lemma pd_congr {f₁ f₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : f₁ =ᶠ[𝓝 x] f₂) (k : Fin n) :
    pd k f₁ x = pd k f₂ x := by
  simp only [pd, h.fderiv_eq]

/-- Partial derivatives of a `C^∞` function on an open set are `C^∞` there. -/
lemma contDiffOn_pd {f : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) (k : Fin n) : ContDiffOn ℝ ∞ (pd k f) U := by
  have h := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hf).2
  exact h.clm_apply contDiffOn_const

/-- A `C^∞` function on an open set is differentiable at each of its points. -/
lemma differentiableAt_of_contDiffOn {U : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {x : Fin n → ℝ} (hx : x ∈ U) :
    DifferentiableAt ℝ f x :=
  (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

/-- **Mixed partial derivatives commute** for `C^∞` functions (via Mathlib's symmetry of the
second derivative). -/
lemma pd_pd_comm {f : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) {x : Fin n → ℝ} (hx : x ∈ U) (μ ν : Fin n) :
    pd μ (pd ν f) x = pd ν (pd μ f) x := by
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
  have hsym := hfx.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hfx.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have key : ∀ a b : Fin n,
      pd a (pd b f) x = fderiv ℝ (fderiv ℝ f) x (Pi.single a 1) (Pi.single b 1) := by
    intro a b
    show fderiv ℝ (fun y => fderiv ℝ f y (Pi.single b 1)) x (Pi.single a 1) = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key, hsym]

/-! ## Christoffel symbols -/

/-- Christoffel symbols of the first kind `Γ_{ljk} = ½(∂_j g_{lk} + ∂_k g_{lj} - ∂_l g_{jk})`. -/
def christoffelFirst (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l j k : Fin n)
    (y : Fin n → ℝ) : ℝ :=
  (1 / 2) * (pd j (fun z => g z l k) y + pd k (fun z => g z l j) y - pd l (fun z => g z j k) y)

/-- Christoffel symbols of the second kind
`Γ^i_{jk} = ½ gⁱˡ (∂_j g_{lk} + ∂_k g_{lj} − ∂_l g_{jk})`. -/
def christoffel (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ l, (g x)⁻¹ i l *
    (pd j (fun y => g y l k) x + pd k (fun y => g y l j) x - pd l (fun y => g y j k) x)

/-- Raising an index: `Γ^i_{jk} = gⁱˡ Γ_{ljk}`. -/
lemma christoffel_eq_sum (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n)
    (y : Fin n → ℝ) : christoffel g i j k y = ∑ l, (g y)⁻¹ i l * christoffelFirst g l j k y := by
  simp only [christoffel, christoffelFirst, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-! ## Coordinate metrics -/

/-- `g` is a **coordinate metric on the open set `U`**: smooth, symmetric and invertible on `U`. -/
structure IsCoordMetric (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ)) :
    Prop where
  /-- The domain is open. -/
  isOpen : IsOpen U
  /-- The matrix is symmetric on `U`. -/
  symm : ∀ x ∈ U, (g x)ᵀ = g x
  /-- The matrix is invertible on `U`. -/
  isUnit_det : ∀ x ∈ U, IsUnit (g x).det
  /-- The entries are `C^∞` on `U`. -/
  smooth : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The determinant of a matrix with `C^∞` entries is `C^∞`. -/
lemma contDiffOn_det_of_entries {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, ContDiffOn ℝ ∞ (fun y => M y i j) U) :
    ContDiffOn ℝ ∞ (fun y => (M y).det) U := by
  simp only [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hM _ _)

/-- Entries of `g⁻¹` are `C^∞` on `U` (adjugate formula; `det g ≠ 0` on `U`). -/
lemma IsCoordMetric.contDiffOn_inv (hg : IsCoordMetric g U) (a b : Fin n) :
    ContDiffOn ℝ ∞ (fun y => (g y)⁻¹ a b) U := by
  have hdet : ContDiffOn ℝ ∞ (fun y => (g y).det) U := contDiffOn_det_of_entries hg.smooth
  have hadj : ContDiffOn ℝ ∞ (fun y => (g y).adjugate a b) U := by
    simp only [Matrix.adjugate_apply]
    refine contDiffOn_det_of_entries fun i j => ?_
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiffOn_const
    · exact hg.smooth i j
  have hinv : ContDiffOn ℝ ∞ (fun y => ((g y).det)⁻¹) U :=
    hdet.inv fun y hy => (hg.isUnit_det y hy).ne_zero
  refine (hinv.mul hadj).congr fun y _ => ?_
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

/-- The partial derivatives of the entries of `g` are `C^∞` on `U`. -/
lemma IsCoordMetric.contDiffOn_pdg (hg : IsCoordMetric g U) (k i j : Fin n) :
    ContDiffOn ℝ ∞ (pd k (fun y => g y i j)) U :=
  contDiffOn_pd (hg.smooth i j) hg.isOpen k

/-- The Christoffel symbols of the first kind are `C^∞` on `U`. -/
lemma IsCoordMetric.contDiffOn_christoffelFirst (hg : IsCoordMetric g U) (l j k : Fin n) :
    ContDiffOn ℝ ∞ (christoffelFirst g l j k) U :=
  contDiffOn_const.mul (((hg.contDiffOn_pdg j l k).add (hg.contDiffOn_pdg k l j)).sub
    (hg.contDiffOn_pdg l j k))

/-- The Christoffel symbols of the second kind are `C^∞` on `U`. -/
lemma IsCoordMetric.contDiffOn_christoffel (hg : IsCoordMetric g U) (i j k : Fin n) :
    ContDiffOn ℝ ∞ (christoffel g i j k) U := by
  have : christoffel g i j k = fun y => ∑ l, (g y)⁻¹ i l * christoffelFirst g l j k y :=
    funext (christoffel_eq_sum g i j k)
  rw [this]
  exact ContDiffOn.sum fun l _ =>
    (hg.contDiffOn_inv i l).mul (hg.contDiffOn_christoffelFirst l j k)

/-! ## Pointwise identities on `U` -/

/-- `g` symmetric on the open set `U` ⇒ `g_{ab}` and `g_{ba}` agree near every point of `U`. -/
lemma IsCoordMetric.eventuallyEq_symm (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (a b : Fin n) : (fun y => g y a b) =ᶠ[𝓝 x] (fun y => g y b a) :=
  eventually_of_mem (hg.isOpen.mem_nhds hx) fun y hy => by
    show g y a b = g y b a
    rw [← Matrix.transpose_apply (g y) b a, hg.symm y hy]

/-- `∂_k g_{ab} = ∂_k g_{ba}` at the points of `U`. -/
lemma IsCoordMetric.pd_symm (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (k a b : Fin n) : pd k (fun y => g y a b) x = pd k (fun y => g y b a) x :=
  pd_congr (hg.eventuallyEq_symm hx a b) k

/-- `∂_ν g_{ab}` and `∂_ν g_{ba}` agree near every point of `U`. -/
lemma IsCoordMetric.eventuallyEq_pd_symm (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (k a b : Fin n) : pd k (fun y => g y a b) =ᶠ[𝓝 x] pd k (fun y => g y b a) :=
  eventually_of_mem (hg.isOpen.mem_nhds hx) fun _ hy => hg.pd_symm hy k a b

/-- Lowering an index: `g_{ρλ} Γ^λ_{νσ} = Γ_{ρνσ}` on `U`. -/
lemma IsCoordMetric.lower_christoffel (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
    (ρ ν σ : Fin n) : ∑ l, g y ρ l * christoffel g l ν σ y = christoffelFirst g ρ ν σ y := by
  simp only [christoffel_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h1 : g y * (g y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hg.isUnit_det y hy)
  calc ∑ b, ∑ l, g y ρ l * ((g y)⁻¹ l b * christoffelFirst g b ν σ y)
      = ∑ b, (g y * (g y)⁻¹) ρ b * christoffelFirst g b ν σ y := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = christoffelFirst g ρ ν σ y := by
        rw [h1]; simp [Matrix.one_apply]

/-- `(g⁻¹)ᵀ = g⁻¹` on `U`. -/
lemma IsCoordMetric.inv_symm (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U) (a b : Fin n) :
    (g y)⁻¹ a b = (g y)⁻¹ b a := by
  have : ((g y)⁻¹)ᵀ = (g y)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hg.symm y hy]
  conv_rhs => rw [← this]
  rfl

end Lightlike.Upstream.GeodesicExpansion
