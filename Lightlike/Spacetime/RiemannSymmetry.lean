module

public import Lightlike.Spacetime.Curvature

/-!
# Symmetries of the Riemann tensor

For a coordinate metric `g` on an open set `U` (`IsCoordMetric g U`: smooth, symmetric, invertible)
and `x ∈ U`, with `R_{ρσμν} = g_{ρλ} R^λ_{σμν}` (`riemannLower`):

* `riemann_antisymm_last` - `R^ρ_{σμν} = -R^ρ_{σνμ}` (for every input: a formula identity);
* `bianchi_first_lower` - `R_{ρσμν} + R_{ρμνσ} + R_{ρνσμ} = 0`;
* `riemannLower_antisymm_first` - `R_{ρσμν} = -R_{σρμν}`;
* `riemannLower_pair_symm` - `R_{ρσμν} = R_{μνρσ}`.

First-pair antisymmetry is the analytic one. In coordinates it reduces to
`∂_μ∂_ν g_{ρσ} = ∂_ν∂_μ g_{ρσ}` (mixed partials commute), which is only true for sufficiently
smooth `g` - this is where `IsCoordMetric` (`C^∞` on an open set) is essential. The proof:
1. lower the Christoffel symbols: `g_{ρλ}Γ^λ_{νσ} = Γ_{ρνσ} := ½(∂_ν g_{ρσ} + ∂_σ g_{ρν} - ∂_ρ g_{νσ})`
   (needs `g g⁻¹ = 1`);
2. differentiate this identity (product rule; needs smoothness of `g⁻¹`, via the adjugate formula);
3. metric compatibility `∂_μ g_{ρa} = Γ_{ρμa} + Γ_{aμρ}` gives
   `R_{ρσμν} = ∂_μ Γ_{ρνσ} - ∂_ν Γ_{ρμσ} - Γ_{aμρ}Γ^a_{νσ} + Γ_{aνρ}Γ^a_{μσ}`;
4. symmetrise in `ρσ`: the derivative terms give `∂_μ∂_ν g_{ρσ} - ∂_ν∂_μ g_{ρσ} = 0`
   (Mathlib's `ContDiffAt.isSymmSndFDerivAt`), the quadratic terms cancel using `g⁻¹` symmetric.

**References.** R. M. Wald, *General Relativity* (University of Chicago Press, 1984), ch. 3 (the symmetries of the Riemann tensor and the Bianchi identity); S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), ch. 3.
-/

@[expose] public section

open Matrix Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-! ## Calculus of `pd` -/

lemma pd_congr {f₁ f₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : f₁ =ᶠ[𝓝 x] f₂) (k : Fin n) :
    pd k f₁ x = pd k f₂ x := by
  simp only [pd, h.fderiv_eq]

lemma pd_add {f₁ f₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h₁ : DifferentiableAt ℝ f₁ x)
    (h₂ : DifferentiableAt ℝ f₂ x) (k : Fin n) :
    pd k (fun y => f₁ y + f₂ y) x = pd k f₁ x + pd k f₂ x := by
  unfold pd
  rw [show (fun y => f₁ y + f₂ y) = f₁ + f₂ from rfl, (h₁.hasFDerivAt.add h₂.hasFDerivAt).fderiv]
  rfl

lemma pd_sub {f₁ f₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h₁ : DifferentiableAt ℝ f₁ x)
    (h₂ : DifferentiableAt ℝ f₂ x) (k : Fin n) :
    pd k (fun y => f₁ y - f₂ y) x = pd k f₁ x - pd k f₂ x := by
  unfold pd
  rw [show (fun y => f₁ y - f₂ y) = f₁ - f₂ from rfl, (h₁.hasFDerivAt.sub h₂.hasFDerivAt).fderiv]
  rfl

lemma pd_mul {f₁ f₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h₁ : DifferentiableAt ℝ f₁ x)
    (h₂ : DifferentiableAt ℝ f₂ x) (k : Fin n) :
    pd k (fun y => f₁ y * f₂ y) x = pd k f₁ x * f₂ x + f₁ x * pd k f₂ x := by
  unfold pd
  rw [show (fun y => f₁ y * f₂ y) = f₁ * f₂ from rfl, (h₁.hasFDerivAt.mul h₂.hasFDerivAt).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

lemma pd_const_mul (c : ℝ) {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : DifferentiableAt ℝ f x)
    (k : Fin n) : pd k (fun y => c * f y) x = c * pd k f x := by
  simp [pd, (h.hasFDerivAt.const_mul c).fderiv]

lemma pd_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (k : Fin n) :
    pd k (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, pd k (f i) x := by
  simp [pd, (HasFDerivAt.fun_sum (fun i hi => (h i hi).hasFDerivAt)).fderiv]

/-- Partial derivatives of a `C^∞` function on an open set are `C^∞` there. -/
lemma contDiffOn_pd {f : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) (k : Fin n) : ContDiffOn ℝ ∞ (pd k f) U := by
  have h := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hf).2
  exact h.clm_apply contDiffOn_const

/-- **Mixed partial derivatives commute** for `C^∞` functions (via Mathlib's symmetry of the
second derivative). -/
lemma pd_pd_comm {f : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) {x : Fin n → ℝ} (hx : x ∈ U) (μ ν : Fin n) :
    pd μ (pd ν f) x = pd ν (pd μ f) x := by
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
  have hsym := hfx.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hfx.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have key : ∀ a b : Fin n, pd a (pd b f) x = fderiv ℝ (fderiv ℝ f) x (Pi.single a 1) (Pi.single b 1) := by
    intro a b
    show fderiv ℝ (fun y => fderiv ℝ f y (Pi.single b 1)) x (Pi.single a 1) = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key, hsym]

/-! ## Smoothness of everything built from a coordinate metric -/

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

lemma contDiffOn_det_of_entries {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, ContDiffOn ℝ ∞ (fun y => M y i j) U) : ContDiffOn ℝ ∞ (fun y => (M y).det) U := by
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

/-- Christoffel symbols of the first kind `Γ_{ljk} = ½(∂_j g_{lk} + ∂_k g_{lj} - ∂_l g_{jk})`. -/
def christoffelFirst (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l j k : Fin n)
    (y : Fin n → ℝ) : ℝ :=
  (1 / 2) * (pd j (fun z => g z l k) y + pd k (fun z => g z l j) y - pd l (fun z => g z j k) y)

lemma christoffel_eq_sum (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n)
    (y : Fin n → ℝ) : christoffel g i j k y = ∑ l, (g y)⁻¹ i l * christoffelFirst g l j k y := by
  simp only [christoffel, christoffelFirst, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

lemma IsCoordMetric.contDiffOn_pdg (hg : IsCoordMetric g U) (k i j : Fin n) :
    ContDiffOn ℝ ∞ (pd k (fun y => g y i j)) U :=
  contDiffOn_pd (hg.smooth i j) hg.isOpen k

lemma IsCoordMetric.contDiffOn_christoffelFirst (hg : IsCoordMetric g U) (l j k : Fin n) :
    ContDiffOn ℝ ∞ (christoffelFirst g l j k) U :=
  contDiffOn_const.mul (((hg.contDiffOn_pdg j l k).add (hg.contDiffOn_pdg k l j)).sub
    (hg.contDiffOn_pdg l j k))

lemma IsCoordMetric.contDiffOn_christoffel (hg : IsCoordMetric g U) (i j k : Fin n) :
    ContDiffOn ℝ ∞ (christoffel g i j k) U := by
  have : christoffel g i j k = fun y => ∑ l, (g y)⁻¹ i l * christoffelFirst g l j k y :=
    funext (christoffel_eq_sum g i j k)
  rw [this]
  exact ContDiffOn.sum fun l _ => (hg.contDiffOn_inv i l).mul (hg.contDiffOn_christoffelFirst l j k)

lemma differentiableAt_of_contDiffOn {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) {x : Fin n → ℝ} (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

/-! ## Pointwise identities on `U` -/

/-- `g` symmetric on the open set `U` ⇒ `g_{ab}` and `g_{ba}` agree near every point of `U`. -/
lemma IsCoordMetric.eventuallyEq_symm (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (a b : Fin n) : (fun y => g y a b) =ᶠ[𝓝 x] (fun y => g y b a) :=
  eventually_of_mem (hg.isOpen.mem_nhds hx) fun y hy => by
    show g y a b = g y b a
    rw [← Matrix.transpose_apply (g y) b a, hg.symm y hy]

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

/-- **Metric compatibility** in coordinates: `∂_μ g_{ρa} = Γ_{ρμa} + Γ_{aμρ}` on `U`. -/
lemma IsCoordMetric.pd_eq_christoffelFirst (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
    (μ ρ a : Fin n) :
    pd μ (fun z => g z ρ a) y = christoffelFirst g ρ μ a y + christoffelFirst g a μ ρ y := by
  simp only [christoffelFirst]
  rw [hg.pd_symm hy μ a ρ, hg.pd_symm hy ρ a μ, hg.pd_symm hy a μ ρ]
  ring

/-- `(g⁻¹)ᵀ = g⁻¹` on `U`. -/
lemma IsCoordMetric.inv_symm (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U) (a b : Fin n) :
    (g y)⁻¹ a b = (g y)⁻¹ b a := by
  have : ((g y)⁻¹)ᵀ = (g y)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hg.symm y hy]
  conv_rhs => rw [← this]
  rfl

/-- Riemann tensor with the first index lowered, `R_{ρσμν} = g_{ρλ} R^λ_{σμν}`. -/
def riemannLower (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ l, g x ρ l * riemann g l σ μ ν x

/-- Step 3: `R_{ρσμν} = ∂_μ Γ_{ρνσ} - ∂_ν Γ_{ρμσ} - Γ_{aμρ}Γ^a_{νσ} + Γ_{aνρ}Γ^a_{μσ}`. -/
lemma IsCoordMetric.riemannLower_eq (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (ρ σ μ ν : Fin n) :
    riemannLower g ρ σ μ ν x =
      pd μ (christoffelFirst g ρ ν σ) x - pd ν (christoffelFirst g ρ μ σ) x
        - ∑ a, christoffelFirst g a μ ρ x * christoffel g a ν σ x
        + ∑ a, christoffelFirst g a ν ρ x * christoffel g a μ σ x := by
  have hdg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x := fun i j =>
    differentiableAt_of_contDiffOn (hg.smooth i j) hg.isOpen hx
  have hdΓ : ∀ i j k, DifferentiableAt ℝ (christoffel g i j k) x := fun i j k =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_christoffel i j k) hg.isOpen hx
  -- differentiate the lowering identity `g_{ρλ}Γ^λ_{νσ} = Γ_{ρνσ}` (valid near `x`)
  have hlow : ∀ m a b, ∑ l, g x ρ l * pd m (christoffel g l a b) x =
      pd m (christoffelFirst g ρ a b) x -
        ∑ l, pd m (fun z => g z ρ l) x * christoffel g l a b x := by
    intro m a b
    have hev : (fun y => ∑ l, g y ρ l * christoffel g l a b y) =ᶠ[𝓝 x] christoffelFirst g ρ a b :=
      eventually_of_mem (hg.isOpen.mem_nhds hx) fun y hy => hg.lower_christoffel hy ρ a b
    have h1 := pd_congr hev m
    have h2 : pd m (fun y => ∑ l, g y ρ l * christoffel g l a b y) x =
        ∑ l, (pd m (fun z => g z ρ l) x * christoffel g l a b x +
          g x ρ l * pd m (christoffel g l a b) x) := by
      rw [pd_sum (f := fun l y => g y ρ l * christoffel g l a b y) Finset.univ
        (fun l _ => (hdg ρ l).mul (hdΓ l a b))]
      exact Finset.sum_congr rfl fun l _ => pd_mul (hdg ρ l) (hdΓ l a b) m
    rw [h2, Finset.sum_add_distrib] at h1
    linarith
  -- quadratic terms: `g_{ρλ}Γ^λ_{μl} = Γ_{ρμl}`
  have hq : ∀ a b, ∑ l', g x ρ l' * (∑ l, (christoffel g l' a l x * christoffel g l b σ x)) =
      ∑ l, christoffelFirst g ρ a l x * christoffel g l b σ x := by
    intro a b
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hg.lower_christoffel hx ρ a l, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l' _ => by ring
  have hR : riemannLower g ρ σ μ ν x =
      (∑ l, g x ρ l * pd μ (christoffel g l ν σ) x) - (∑ l, g x ρ l * pd ν (christoffel g l μ σ) x)
        + ∑ l', g x ρ l' * (∑ l, christoffel g l' μ l x * christoffel g l ν σ x)
        - ∑ l', g x ρ l' * (∑ l, christoffel g l' ν l x * christoffel g l μ σ x) := by
    simp only [riemannLower, riemann, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  rw [hR, hlow, hlow, hq, hq]
  simp only [hg.pd_eq_christoffelFirst hx, add_mul, Finset.sum_add_distrib]
  ring

/-- **Antisymmetry in the first index pair**: `R_{ρσμν} = -R_{σρμν}` for a coordinate metric. -/
theorem IsCoordMetric.riemannLower_antisymm_first (hg : IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (ρ σ μ ν : Fin n) :
    riemannLower g ρ σ μ ν x = -riemannLower g σ ρ μ ν x := by
  have hdpd : ∀ k i j, DifferentiableAt ℝ (pd k (fun y => g y i j)) x := fun k i j =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_pdg k i j) hg.isOpen hx
  -- derivative part: `∂_μ Γ_{ρνσ} + ∂_μ Γ_{σνρ} = ∂_μ ∂_ν g_{ρσ}`
  have hder : ∀ a b, pd a (christoffelFirst g ρ b σ) x + pd a (christoffelFirst g σ b ρ) x =
      pd a (pd b (fun y => g y ρ σ)) x := by
    intro a b
    have hdC : ∀ l j k, DifferentiableAt ℝ (christoffelFirst g l j k) x := fun l j k =>
      differentiableAt_of_contDiffOn (hg.contDiffOn_christoffelFirst l j k) hg.isOpen hx
    rw [← pd_add (hdC _ _ _) (hdC _ _ _)]
    refine pd_congr ?_ a
    filter_upwards [hg.eventuallyEq_pd_symm hx b σ ρ, hg.eventuallyEq_pd_symm hx σ b ρ,
      hg.eventuallyEq_pd_symm hx ρ b σ] with y h1 h2 h3
    simp only [christoffelFirst]
    rw [h1, h2, h3]
    ring
  have hcomm := pd_pd_comm (hg.smooth ρ σ) hg.isOpen hx μ ν
  -- quadratic part cancels (uses `g⁻¹` symmetric)
  have hquad : ∀ a b c d : Fin n,
      ∑ i, christoffelFirst g i a b x * christoffel g i c d x =
        ∑ i, christoffelFirst g i c d x * christoffel g i a b x := by
    intro a b c d
    simp only [christoffel_eq_sum, Finset.mul_sum]
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
theorem riemann_antisymm_last (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n)
    (x : Fin n → ℝ) : riemann g ρ σ μ ν x = -riemann g ρ σ ν μ x := by
  simp only [riemann, Finset.sum_sub_distrib]; ring

/-- Antisymmetry of the lowered Riemann tensor in the last pair, `R_{ρσμν} = -R_{ρσνμ}` - a formula
identity, true for every metric function and every point. -/
theorem riemannLower_antisymm_last (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (ρ σ μ ν : Fin n) (x : Fin n → ℝ) : riemannLower g ρ σ μ ν x = -riemannLower g ρ σ ν μ x := by
  simp only [riemannLower, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [riemann_antisymm_last]; ring

/-- Christoffel symbols are symmetric in the lower indices near every point of `U`. -/
lemma IsCoordMetric.eventuallyEq_christoffel_symm (hg : IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (i j k : Fin n) : christoffel g i j k =ᶠ[𝓝 x] christoffel g i k j := by
  filter_upwards [hg.isOpen.mem_nhds hx] with y hy
  simp only [christoffel]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hg.pd_symm hy l j k]; ring

/-- **First Bianchi identity** `R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0` on `U`. -/
theorem IsCoordMetric.bianchi_first (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (ρ σ μ ν : Fin n) :
    riemann g ρ σ μ ν x + riemann g ρ μ ν σ x + riemann g ρ ν σ μ x = 0 := by
  have hs := fun i j k => hg.eventuallyEq_christoffel_symm hx i j k
  have hp : ∀ m i j k, pd m (christoffel g i j k) x = pd m (christoffel g i k j) x :=
    fun m i j k => pd_congr (hs i j k) m
  have hv : ∀ i j k, christoffel g i j k x = christoffel g i k j x :=
    fun i j k => (hs i j k).eq_of_nhds
  simp only [riemann, Finset.sum_sub_distrib]
  rw [hp μ ρ σ ν, hp ν ρ μ σ, hp σ ρ ν μ]
  simp only [hv _ σ ν, hv _ μ σ, hv _ ν μ]
  ring

/-- **First Bianchi identity, lowered form**: `R_{ρσμν} + R_{ρμνσ} + R_{ρνσμ} = 0` at every point
of the domain of a coordinate metric. -/
theorem IsCoordMetric.bianchi_first_lower (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (ρ σ μ ν : Fin n) :
    riemannLower g ρ σ μ ν x + riemannLower g ρ μ ν σ x + riemannLower g ρ ν σ μ x = 0 := by
  simp only [riemannLower, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [← mul_add, ← mul_add, hg.bianchi_first hx, mul_zero]

/-- Pure algebra: two antisymmetries plus the first Bianchi identity imply pair symmetry. -/
theorem pair_symm_of_algebraic (T : Fin n → Fin n → Fin n → Fin n → ℝ)
    (A1 : ∀ a b c d, T a b c d = -T b a c d) (A2 : ∀ a b c d, T a b c d = -T a b d c)
    (B : ∀ a b c d, T a b c d + T a c d b + T a d b c = 0) (a b c d : Fin n) :
    T a b c d = T c d a b := by
  have := B a b c d; have := B b c d a; have := B c d a b; have := B d a b c
  have := A1 a b c d; have := A1 a c d b; have := A1 a d b c; have := A1 b c d a
  have := A1 b d a c; have := A1 c d a b; have := A1 c a b d; have := A1 d a b c
  have := A1 d b c a; have := A2 a c d b; have := A2 b d a c; have := A2 c a b d
  have := A2 d b c a; have := A2 a d b c; have := A2 c b d a; have := A1 c b d a
  have := A2 b c d a; have := A2 d c a b; have := A1 d c a b; have := A1 b a c d
  linarith

/-- **Pair symmetry** `R_{ρσμν} = R_{μνρσ}` for a coordinate metric - now unconditional. -/
theorem IsCoordMetric.riemannLower_pair_symm (hg : IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (ρ σ μ ν : Fin n) :
    riemannLower g ρ σ μ ν x = riemannLower g μ ν ρ σ x :=
  pair_symm_of_algebraic (fun a b c d => riemannLower g a b c d x)
    (fun a b c d => hg.riemannLower_antisymm_first hx a b c d)
    (fun a b c d => riemannLower_antisymm_last g a b c d x)
    (fun a b c d => hg.bianchi_first_lower hx a b c d) ρ σ μ ν

end Lightlike
