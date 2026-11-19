module

public import Lightlike.Spacetime.RiemannSymmetry
public import Lightlike.Spacetime.CurvatureWithin

/-!
# Symmetries of the Riemann tensor within a set (GE11, corners)

The statements of `RiemannSymmetry.lean` for coordinate formulas whose derivatives are taken within a set `S` (`pdW S`, `christoffelW S`,
`riemannW S`) and a coordinate metric on a set `U` relatively open in `S` (`IsCoordMetricW S g U`); for a manifold with corners `S` is
`range I`. The proofs are those of the boundaryless file, with `fderivWithin` and `ContDiffWithinAt.isSymmSndFDerivWithinAt` (mixed
partial derivatives within `S` commute at points of the closure of the interior) in place of `fderiv` and the symmetry of the second
derivative on an open set.

* `riemannW_antisymm_last`, `IsCoordMetricW.bianchi_first_lower`, `IsCoordMetricW.riemannLowerW_antisymm_first`,
  `IsCoordMetricW.riemannLowerW_pair_symm` - the symmetries of `R_{ρσμν}`.

**Limits.** Boundaryless statements are `RiemannSymmetry.lean`, to which these reduce for `S = univ`.
-/

@[expose] public section

open Matrix Filter Set
open scoped ContDiff Topology Manifold Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-! ## Calculus of `pdW` -/

variable {S : Set (Fin n → ℝ)}

lemma pdW_congr {f₁ f₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hx : x ∈ S) (h : f₁ =ᶠ[𝓝[S] x] f₂) (k : Fin n) :
    pdW S k f₁ x = pdW S k f₂ x := by
  simp only [pdW, h.fderivWithin_eq (h.eq_of_nhdsWithin hx)]

lemma pdW_add (hS : UniqueDiffOn ℝ S) {f₁ f₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hx : x ∈ S)
    (h₁ : DifferentiableWithinAt ℝ f₁ S x) (h₂ : DifferentiableWithinAt ℝ f₂ S x) (k : Fin n) :
    pdW S k (fun y => f₁ y + f₂ y) x = pdW S k f₁ x + pdW S k f₂ x := by
  unfold pdW
  rw [show (fun y => f₁ y + f₂ y) = f₁ + f₂ from rfl,
    (h₁.hasFDerivWithinAt.add h₂.hasFDerivWithinAt).fderivWithin (hS x hx)]
  rfl

lemma pdW_sub (hS : UniqueDiffOn ℝ S) {f₁ f₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hx : x ∈ S)
    (h₁ : DifferentiableWithinAt ℝ f₁ S x) (h₂ : DifferentiableWithinAt ℝ f₂ S x) (k : Fin n) :
    pdW S k (fun y => f₁ y - f₂ y) x = pdW S k f₁ x - pdW S k f₂ x := by
  unfold pdW
  rw [show (fun y => f₁ y - f₂ y) = f₁ - f₂ from rfl,
    (h₁.hasFDerivWithinAt.sub h₂.hasFDerivWithinAt).fderivWithin (hS x hx)]
  rfl

lemma pdW_mul (hS : UniqueDiffOn ℝ S) {f₁ f₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hx : x ∈ S)
    (h₁ : DifferentiableWithinAt ℝ f₁ S x) (h₂ : DifferentiableWithinAt ℝ f₂ S x) (k : Fin n) :
    pdW S k (fun y => f₁ y * f₂ y) x = pdW S k f₁ x * f₂ x + f₁ x * pdW S k f₂ x := by
  unfold pdW
  rw [show (fun y => f₁ y * f₂ y) = f₁ * f₂ from rfl,
    (h₁.hasFDerivWithinAt.mul h₂.hasFDerivWithinAt).fderivWithin (hS x hx)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

lemma pdW_const_mul (hS : UniqueDiffOn ℝ S) (c : ℝ) {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hx : x ∈ S)
    (h : DifferentiableWithinAt ℝ f S x) (k : Fin n) : pdW S k (fun y => c * f y) x = c * pdW S k f x := by
  simp [pdW, (h.hasFDerivWithinAt.const_mul c).fderivWithin (hS x hx)]

lemma pdW_sum (hS : UniqueDiffOn ℝ S) {ι : Type*} {f : ι → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hx : x ∈ S) (s : Finset ι) (h : ∀ i ∈ s, DifferentiableWithinAt ℝ (f i) S x) (k : Fin n) :
    pdW S k (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, pdW S k (f i) x := by
  simp [pdW, (HasFDerivWithinAt.fun_sum (fun i hi => (h i hi).hasFDerivWithinAt)).fderivWithin (hS x hx)]

/-- Partial derivatives within `S` of a `C^∞` function on a relatively open `S ∩ V` are `C^∞` there. -/
lemma contDiffOn_pdW (hS : UniqueDiffOn ℝ S) {f : (Fin n → ℝ) → ℝ} {V : Set (Fin n → ℝ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f (S ∩ V)) (k : Fin n) : ContDiffOn ℝ ∞ (pdW S k f) (S ∩ V) := by
  have hU : UniqueDiffOn ℝ (S ∩ V) := hS.inter hV
  have h := hf.fderivWithin hU (m := ∞) (by simp)
  refine (h.clm_apply (contDiffOn_const (c := (Pi.single k 1 : Fin n → ℝ)))).congr fun x hx => ?_
  simp only [pdW]
  rw [fderivWithin_inter (hV.mem_nhds hx.2)]

/-- **Mixed partial derivatives within `S` commute** for `C^∞` functions on a relatively open set, at points of the closure of
the interior of `S`. -/
lemma pdW_pdW_comm (hS : UniqueDiffOn ℝ S) {f : (Fin n → ℝ) → ℝ} {V : Set (Fin n → ℝ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f (S ∩ V)) {x : Fin n → ℝ} (hx : x ∈ S ∩ V) (hcl : x ∈ closure (interior S))
    (μ ν : Fin n) : pdW S μ (pdW S ν f) x = pdW S ν (pdW S μ f) x := by
  have hfx : ContDiffWithinAt ℝ ∞ f S x := (hf.contDiffWithinAt hx).mono_of_mem_nhdsWithin
    (inter_mem_nhdsWithin S (hV.mem_nhds hx.2))
  have hsym := hfx.isSymmSndFDerivWithinAt (by simp [minSmoothness_of_isRCLikeNormedField]) hS hcl hx.1
  have hd : DifferentiableWithinAt ℝ (fderivWithin ℝ f S) S x :=
    (hfx.fderivWithin_right (m := 1) hS (by simp) hx.1).differentiableWithinAt (by simp)
  have key : ∀ a b : Fin n, pdW S a (pdW S b f) x =
      fderivWithin ℝ (fderivWithin ℝ f S) S x (Pi.single a 1) (Pi.single b 1) := by
    intro a b
    show fderivWithin ℝ (fun y => fderivWithin ℝ f S y (Pi.single b 1)) S x (Pi.single a 1) = _
    rw [fderivWithin_clm_apply (hS x hx.1) hd (differentiableWithinAt_const _)]
    simp
  rw [key, key, hsym]

/-! ## Smoothness of everything built from a coordinate metric -/

variable {S : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-! ## Basic facts on `IsCoordMetricW` -/


lemma IsCoordMetricW.subset (hg : IsCoordMetricW S g U) : U ⊆ S := by
  obtain ⟨V, -, rfl⟩ := hg.isRelOpen
  exact inter_subset_left

/-- `U` is a neighbourhood of each of its points within `S`. -/
lemma IsCoordMetricW.mem_nhdsWithin (hg : IsCoordMetricW S g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    U ∈ 𝓝[S] x := by
  obtain ⟨V, hV, rfl⟩ := hg.isRelOpen
  exact inter_mem_nhdsWithin S (hV.mem_nhds hx.2)

lemma differentiableWithinAt_of_contDiffOn (hg : IsCoordMetricW S g U) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {x : Fin n → ℝ} (hx : x ∈ U) : DifferentiableWithinAt ℝ f S x :=
  ((hf.contDiffWithinAt hx).mono_of_mem_nhdsWithin (hg.mem_nhdsWithin hx)).differentiableWithinAt (by simp)

lemma IsCoordMetricW.contDiffOn_pdW (hg : IsCoordMetricW S g U) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (k : Fin n) : ContDiffOn ℝ ∞ (pdW S k f) U := by
  obtain ⟨V, hV, hU⟩ := hg.isRelOpen
  subst hU
  exact _root_.Lightlike.contDiffOn_pdW hg.uniqueDiff hV hf k

/-- **Mixed partial derivatives within `S` commute** for a function `C^∞` on the domain `U` of a coordinate metric `IsCoordMetricW S g U`, at the points of `U`. -/
lemma IsCoordMetricW.pdW_pdW_comm (hg : IsCoordMetricW S g U) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {x : Fin n → ℝ} (hx : x ∈ U) (μ ν : Fin n) :
    pdW S μ (pdW S ν f) x = pdW S ν (pdW S μ f) x := by
  obtain ⟨V, hV, hU⟩ := hg.isRelOpen
  subst hU
  exact _root_.Lightlike.pdW_pdW_comm hg.uniqueDiff hV hf hx (hg.closure x hx.1) μ ν



/-- Entries of `g⁻¹` are `C^∞` on `U` (adjugate formula; `det g ≠ 0` on `U`). -/
lemma IsCoordMetricW.contDiffOn_inv (hg : IsCoordMetricW S g U) (a b : Fin n) :
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

/-- Christoffel symbols of the first kind `Γ_{ljk} = ½(∂_j g_{lk} + ∂_k g_{lj} - ∂_l g_{jk})`. -/
def christoffelFirstW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l j k : Fin n)
    (y : Fin n → ℝ) : ℝ :=
  (1 / 2) * (pdW S j (fun z => g z l k) y + pdW S k (fun z => g z l j) y - pdW S l (fun z => g z j k) y)

lemma christoffelW_eq_sum (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n)
    (y : Fin n → ℝ) : christoffelW S g i j k y = ∑ l, (g y)⁻¹ i l * christoffelFirstW S g l j k y := by
  simp only [christoffelW, christoffelFirstW, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

lemma IsCoordMetricW.contDiffOn_pdg (hg : IsCoordMetricW S g U) (k i j : Fin n) :
    ContDiffOn ℝ ∞ (pdW S k (fun y => g y i j)) U :=
  hg.contDiffOn_pdW (hg.smooth i j) k

lemma IsCoordMetricW.contDiffOn_christoffelFirst (hg : IsCoordMetricW S g U) (l j k : Fin n) :
    ContDiffOn ℝ ∞ (christoffelFirstW S g l j k) U :=
  contDiffOn_const.mul (((hg.contDiffOn_pdg j l k).add (hg.contDiffOn_pdg k l j)).sub
    (hg.contDiffOn_pdg l j k))

lemma IsCoordMetricW.contDiffOn_christoffel (hg : IsCoordMetricW S g U) (i j k : Fin n) :
    ContDiffOn ℝ ∞ (christoffelW S g i j k) U := by
  have : christoffelW S g i j k = fun y => ∑ l, (g y)⁻¹ i l * christoffelFirstW S g l j k y :=
    funext (christoffelW_eq_sum g i j k)
  rw [this]
  exact ContDiffOn.sum fun l _ => (hg.contDiffOn_inv i l).mul (hg.contDiffOn_christoffelFirst l j k)

/-! ## Pointwise identities on `U` -/

/-- `g` symmetric on the open set `U` ⇒ `g_{ab}` and `g_{ba}` agree near every point of `U`. -/
lemma IsCoordMetricW.eventuallyEq_symm (hg : IsCoordMetricW S g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (a b : Fin n) : (fun y => g y a b) =ᶠ[𝓝[S] x] (fun y => g y b a) :=
  eventually_of_mem (hg.mem_nhdsWithin hx) fun y hy => by
    show g y a b = g y b a
    rw [← Matrix.transpose_apply (g y) b a, hg.symm y hy]

lemma IsCoordMetricW.pdW_symm (hg : IsCoordMetricW S g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (k a b : Fin n) : pdW S k (fun y => g y a b) x = pdW S k (fun y => g y b a) x :=
  pdW_congr (hg.subset hx) (hg.eventuallyEq_symm hx a b) k

/-- `∂_ν g_{ab}` and `∂_ν g_{ba}` agree near every point of `U`. -/
lemma IsCoordMetricW.eventuallyEq_pd_symm (hg : IsCoordMetricW S g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (k a b : Fin n) : pdW S k (fun y => g y a b) =ᶠ[𝓝[S] x] pdW S k (fun y => g y b a) :=
  eventually_of_mem (hg.mem_nhdsWithin hx) fun _ hy => hg.pdW_symm hy k a b

/-- Lowering an index: `g_{ρλ} Γ^λ_{νσ} = Γ_{ρνσ}` on `U`. -/
lemma IsCoordMetricW.lower_christoffel (hg : IsCoordMetricW S g U) {y : Fin n → ℝ} (hy : y ∈ U)
    (ρ ν σ : Fin n) : ∑ l, g y ρ l * christoffelW S g l ν σ y = christoffelFirstW S g ρ ν σ y := by
  simp only [christoffelW_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h1 : g y * (g y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hg.isUnit_det y hy)
  calc ∑ b, ∑ l, g y ρ l * ((g y)⁻¹ l b * christoffelFirstW S g b ν σ y)
      = ∑ b, (g y * (g y)⁻¹) ρ b * christoffelFirstW S g b ν σ y := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = christoffelFirstW S g ρ ν σ y := by
        rw [h1]; simp [Matrix.one_apply]

/-- **Metric compatibility** in coordinates: `∂_μ g_{ρa} = Γ_{ρμa} + Γ_{aμρ}` on `U`. -/
lemma IsCoordMetricW.pdW_eq_christoffelFirst (hg : IsCoordMetricW S g U) {y : Fin n → ℝ} (hy : y ∈ U)
    (μ ρ a : Fin n) :
    pdW S μ (fun z => g z ρ a) y = christoffelFirstW S g ρ μ a y + christoffelFirstW S g a μ ρ y := by
  simp only [christoffelFirstW]
  rw [hg.pdW_symm hy μ a ρ, hg.pdW_symm hy ρ a μ, hg.pdW_symm hy a μ ρ]
  ring

/-- `(g⁻¹)ᵀ = g⁻¹` on `U`. -/
lemma IsCoordMetricW.inv_symm (hg : IsCoordMetricW S g U) {y : Fin n → ℝ} (hy : y ∈ U) (a b : Fin n) :
    (g y)⁻¹ a b = (g y)⁻¹ b a := by
  have : ((g y)⁻¹)ᵀ = (g y)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hg.symm y hy]
  conv_rhs => rw [← this]
  rfl

/-- Riemann tensor with the first index lowered, `R_{ρσμν} = g_{ρλ} R^λ_{σμν}`. -/
def riemannLowerW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ l, g x ρ l * riemannW S g l σ μ ν x

/-- Step 3: `R_{ρσμν} = ∂_μ Γ_{ρνσ} - ∂_ν Γ_{ρμσ} - Γ_{aμρ}Γ^a_{νσ} + Γ_{aνρ}Γ^a_{μσ}`. -/
lemma IsCoordMetricW.riemannLower_eq (hg : IsCoordMetricW S g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (ρ σ μ ν : Fin n) :
    riemannLowerW S g ρ σ μ ν x =
      pdW S μ (christoffelFirstW S g ρ ν σ) x - pdW S ν (christoffelFirstW S g ρ μ σ) x
        - ∑ a, christoffelFirstW S g a μ ρ x * christoffelW S g a ν σ x
        + ∑ a, christoffelFirstW S g a ν ρ x * christoffelW S g a μ σ x := by
  have hdg : ∀ i j, DifferentiableWithinAt ℝ (fun y => g y i j) S x := fun i j =>
    differentiableWithinAt_of_contDiffOn hg (hg.smooth i j) hx
  have hdΓ : ∀ i j k, DifferentiableWithinAt ℝ (christoffelW S g i j k) S x := fun i j k =>
    differentiableWithinAt_of_contDiffOn hg (hg.contDiffOn_christoffel i j k) hx
  -- differentiate the lowering identity `g_{ρλ}Γ^λ_{νσ} = Γ_{ρνσ}` (valid near `x`)
  have hlow : ∀ m a b, ∑ l, g x ρ l * pdW S m (christoffelW S g l a b) x =
      pdW S m (christoffelFirstW S g ρ a b) x -
        ∑ l, pdW S m (fun z => g z ρ l) x * christoffelW S g l a b x := by
    intro m a b
    have hev : (fun y => ∑ l, g y ρ l * christoffelW S g l a b y) =ᶠ[𝓝[S] x] christoffelFirstW S g ρ a b :=
      eventually_of_mem (hg.mem_nhdsWithin hx) fun y hy => hg.lower_christoffel hy ρ a b
    have h1 := pdW_congr (hg.subset hx) hev m
    have h2 : pdW S m (fun y => ∑ l, g y ρ l * christoffelW S g l a b y) x =
        ∑ l, (pdW S m (fun z => g z ρ l) x * christoffelW S g l a b x +
          g x ρ l * pdW S m (christoffelW S g l a b) x) := by
      rw [pdW_sum hg.uniqueDiff (hg.subset hx) (f := fun l y => g y ρ l * christoffelW S g l a b y) Finset.univ
        (fun l _ => (hdg ρ l).mul (hdΓ l a b))]
      exact Finset.sum_congr rfl fun l _ => pdW_mul hg.uniqueDiff (hg.subset hx) (hdg ρ l) (hdΓ l a b) m
    rw [h2, Finset.sum_add_distrib] at h1
    linarith
  -- quadratic terms: `g_{ρλ}Γ^λ_{μl} = Γ_{ρμl}`
  have hq : ∀ a b, ∑ l', g x ρ l' * (∑ l, (christoffelW S g l' a l x * christoffelW S g l b σ x)) =
      ∑ l, christoffelFirstW S g ρ a l x * christoffelW S g l b σ x := by
    intro a b
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hg.lower_christoffel hx ρ a l, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l' _ => by ring
  have hR : riemannLowerW S g ρ σ μ ν x =
      (∑ l, g x ρ l * pdW S μ (christoffelW S g l ν σ) x) - (∑ l, g x ρ l * pdW S ν (christoffelW S g l μ σ) x)
        + ∑ l', g x ρ l' * (∑ l, christoffelW S g l' μ l x * christoffelW S g l ν σ x)
        - ∑ l', g x ρ l' * (∑ l, christoffelW S g l' ν l x * christoffelW S g l μ σ x) := by
    simp only [riemannLowerW, riemannW, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  rw [hR, hlow, hlow, hq, hq]
  simp only [hg.pdW_eq_christoffelFirst hx, add_mul, Finset.sum_add_distrib]
  ring

/-- **Antisymmetry in the first index pair**: `R_{ρσμν} = -R_{σρμν}` for a coordinate metric. -/
theorem IsCoordMetricW.riemannLower_antisymm_first (hg : IsCoordMetricW S g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (ρ σ μ ν : Fin n) :
    riemannLowerW S g ρ σ μ ν x = -riemannLowerW S g σ ρ μ ν x := by
  have hdpd : ∀ k i j, DifferentiableWithinAt ℝ (pdW S k (fun y => g y i j)) S x := fun k i j =>
    differentiableWithinAt_of_contDiffOn hg (hg.contDiffOn_pdg k i j) hx
  -- derivative part: `∂_μ Γ_{ρνσ} + ∂_μ Γ_{σνρ} = ∂_μ ∂_ν g_{ρσ}`
  have hder : ∀ a b, pdW S a (christoffelFirstW S g ρ b σ) x + pdW S a (christoffelFirstW S g σ b ρ) x =
      pdW S a (pdW S b (fun y => g y ρ σ)) x := by
    intro a b
    have hdC : ∀ l j k, DifferentiableWithinAt ℝ (christoffelFirstW S g l j k) S x := fun l j k =>
      differentiableWithinAt_of_contDiffOn hg (hg.contDiffOn_christoffelFirst l j k) hx
    rw [← pdW_add hg.uniqueDiff (hg.subset hx) (hdC _ _ _) (hdC _ _ _)]
    refine pdW_congr (hg.subset hx) ?_ a
    filter_upwards [hg.eventuallyEq_pd_symm hx b σ ρ, hg.eventuallyEq_pd_symm hx σ b ρ,
      hg.eventuallyEq_pd_symm hx ρ b σ] with y h1 h2 h3
    simp only [christoffelFirstW]
    rw [h1, h2, h3]
    ring
  have hcomm := hg.pdW_pdW_comm (hg.smooth ρ σ) hx μ ν
  -- quadratic part cancels (uses `g⁻¹` symmetric)
  have hquad : ∀ a b c d : Fin n,
      ∑ i, christoffelFirstW S g i a b x * christoffelW S g i c d x =
        ∑ i, christoffelFirstW S g i c d x * christoffelW S g i a b x := by
    intro a b c d
    simp only [christoffelW_eq_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hg.inv_symm hx j i]; ring
  rw [hg.riemannLower_eq hx, hg.riemannLower_eq hx]
  have e1 := hder μ ν
  have e2 := hder ν μ
  have q1 := hquad μ ρ ν σ
  have q2 := hquad ν ρ μ σ
  linarith

/-! ## Algebraic symmetries -/

/-- Antisymmetry in the last pair `R^ρ_{σμν} = -R^ρ_{σνμ}` - a formula identity, true for every
input (no hypotheses needed, and no junk value can make it misleading). -/
theorem riemannW_antisymm_last (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n)
    (x : Fin n → ℝ) : riemannW S g ρ σ μ ν x = -riemannW S g ρ σ ν μ x := by
  simp only [riemannW, Finset.sum_sub_distrib]; ring

theorem riemannLowerW_antisymm_last (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (ρ σ μ ν : Fin n) (x : Fin n → ℝ) : riemannLowerW S g ρ σ μ ν x = -riemannLowerW S g ρ σ ν μ x := by
  simp only [riemannLowerW, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [riemannW_antisymm_last]; ring

/-- Christoffel symbols are symmetric in the lower indices near every point of `U`. -/
lemma IsCoordMetricW.eventuallyEq_christoffel_symm (hg : IsCoordMetricW S g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (i j k : Fin n) : christoffelW S g i j k =ᶠ[𝓝[S] x] christoffelW S g i k j := by
  filter_upwards [hg.mem_nhdsWithin hx] with y hy
  simp only [christoffelW]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hg.pdW_symm hy l j k]; ring

/-- **First Bianchi identity** `R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0` on `U`. -/
theorem IsCoordMetricW.bianchi_first (hg : IsCoordMetricW S g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (ρ σ μ ν : Fin n) :
    riemannW S g ρ σ μ ν x + riemannW S g ρ μ ν σ x + riemannW S g ρ ν σ μ x = 0 := by
  have hs := fun i j k => hg.eventuallyEq_christoffel_symm hx i j k
  have hp : ∀ m i j k, pdW S m (christoffelW S g i j k) x = pdW S m (christoffelW S g i k j) x :=
    fun m i j k => pdW_congr (hg.subset hx) (hs i j k) m
  have hv : ∀ i j k, christoffelW S g i j k x = christoffelW S g i k j x :=
    fun i j k => (hs i j k).eq_of_nhdsWithin (hg.subset hx)
  simp only [riemannW, Finset.sum_sub_distrib]
  rw [hp μ ρ σ ν, hp ν ρ μ σ, hp σ ρ ν μ]
  simp only [hv _ σ ν, hv _ μ σ, hv _ ν μ]
  ring

/-- **First Bianchi identity, lowered form**: `R_{ρσμν} + R_{ρμνσ} + R_{ρνσμ} = 0` at every point
of the domain of a coordinate metric. -/
theorem IsCoordMetricW.bianchi_first_lower (hg : IsCoordMetricW S g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (ρ σ μ ν : Fin n) :
    riemannLowerW S g ρ σ μ ν x + riemannLowerW S g ρ μ ν σ x + riemannLowerW S g ρ ν σ μ x = 0 := by
  simp only [riemannLowerW, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [← mul_add, ← mul_add, hg.bianchi_first hx, mul_zero]

/-- **Pair symmetry** `R_{ρσμν} = R_{μνρσ}` for a coordinate metric - now unconditional. -/
theorem IsCoordMetricW.riemannLower_pair_symm (hg : IsCoordMetricW S g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (ρ σ μ ν : Fin n) :
    riemannLowerW S g ρ σ μ ν x = riemannLowerW S g μ ν ρ σ x :=
  pair_symm_of_algebraic (fun a b c d => riemannLowerW S g a b c d x)
    (fun a b c d => hg.riemannLower_antisymm_first hx a b c d)
    (fun a b c d => riemannLowerW_antisymm_last g a b c d x)
    (fun a b c d => hg.bianchi_first_lower hx a b c d) ρ σ μ ν

end Lightlike
