import Lightlike.Spacetime.VariationChristoffel
import Lightlike.Spacetime.Curvature

/-!
# Smoothness of the Christoffel family and exchange of derivatives (GE15, stage S2)

`hasDerivAt_fderiv_exchange`: for a function `φ (t, y)` that is `C²` near `(0, x)`, `d/dt (∂_v φ(t, ·)) = ∂_v (∂_t φ(0, ·))` at `t = 0`
(the symmetry of the second derivative); `contDiffAt_christoffel_family`: `(t, y) ↦ Γ(g + t h)(y)` is smooth near `(0, x)` when `g, h`
are smooth and `det g x ≠ 0`; `hasDerivAt_pd_christoffel`: `d/dt ∂_μ Γ^i_{jk}(g + t h) = ∂_μ (δΓ^i_{jk})` with `δΓ = dChristoffel`.

**Limits.** Smooth `g, h` on all of `ℝⁿ` (`C^∞`); stage S2 of the first variation of the Einstein-Hilbert action.
-/

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_prod_fin {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → F → ℝ) {m : ℕ∞}
    (h : ∀ i ∈ s, ContDiff ℝ m (g i)) : ContDiff ℝ m (fun y => ∏ i ∈ s, g i y) := by
  induction s using Finset.induction_on with
  | empty => simpa using contDiff_const (c := (1 : ℝ))
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem contDiff_det_of {f : F → Matrix (Fin n) (Fin n) ℝ} {m : ℕ∞}
    (hf : ∀ i j, ContDiff ℝ m (fun y => f y i j)) : ContDiff ℝ m (fun y => (f y).det) := by
  simp only [Matrix.det_apply]
  exact ContDiff.sum fun σ _ => (contDiff_prod_fin Finset.univ _ fun i _ => hf (σ i) i).const_smul _

theorem contDiff_adjugate_of {f : F → Matrix (Fin n) (Fin n) ℝ} {m : ℕ∞}
    (hf : ∀ i j, ContDiff ℝ m (fun y => f y i j)) (i j : Fin n) :
    ContDiff ℝ m (fun y => (f y).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det_of fun a b => ?_
  by_cases h : a = j
  · subst h
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne h]
    exact hf a b

theorem contDiffAt_inv_entry {f : F → Matrix (Fin n) (Fin n) ℝ} {x : F} {m : ℕ∞}
    (hf : ∀ i j, ContDiff ℝ m (fun y => f y i j)) (hx : (f x).det ≠ 0) (i j : Fin n) :
    ContDiffAt ℝ m (fun y => (f y)⁻¹ i j) x := by
  have hd := (contDiff_det_of hf).contDiffAt (x := x)
  have ha := (contDiff_adjugate_of hf i j).contDiffAt (x := x)
  have : (fun y => (f y)⁻¹ i j) = fun y => ((f y).det)⁻¹ * (f y).adjugate i j := by
    funext s
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (hd.inv hx).mul ha


variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Exchange of `∂_t` and a directional derivative** for a function that is `C²` near `(0, x)`:
`d/dt (∂_v φ(t, ·)) (x) = ∂_v (∂_t φ(0, ·)) (x)` at `t = 0`. -/
theorem hasDerivAt_fderiv_exchange {φ : ℝ × E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ (0, x)) (v : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ (fun y => φ (t, y)) x v)
      (fderiv ℝ (fun y => fderiv ℝ (fun t : ℝ => φ (t, y)) 0 1) x v) 0 := by
  set p₀ : ℝ × E := (0, x) with hp₀
  have hD : ContDiffAt ℝ 1 (fderiv ℝ φ) p₀ := hφ.fderiv_right (by norm_num)
  have hdiff : ∀ᶠ p in 𝓝 p₀, DifferentiableAt ℝ φ p := by
    have : ∀ᶠ p in 𝓝 p₀, ContDiffAt ℝ 2 φ p := hφ.eventually (by simp)
    filter_upwards [this] with p hp using hp.differentiableAt (by norm_num)
  have hDd : DifferentiableAt ℝ (fderiv ℝ φ) p₀ := hD.differentiableAt (by norm_num)
  set D' : ℝ × E →L[ℝ] (ℝ × E →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ φ) p₀ with hD'
  -- `Ψ t = D (t, x) (0, v)` near `t = 0`
  have hΨ : (fun t : ℝ => fderiv ℝ (fun y => φ (t, y)) x v) =ᶠ[𝓝 0] fun t => fderiv ℝ φ (t, x) (0, v) := by
    have hc : ContinuousAt (fun t : ℝ => (t, x)) 0 := by fun_prop
    filter_upwards [hc.eventually hdiff] with t ht
    have h1 : HasFDerivAt (fun y : E => (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x := hasFDerivAt_prodMk_right t x
    have h2 := ht.hasFDerivAt.comp x h1
    have : fderiv ℝ (fun y => φ (t, y)) x = (fderiv ℝ φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) := h2.fderiv
    rw [this]; simp
  have hline : HasDerivAt (fun t : ℝ => fderiv ℝ φ (t, x)) (D' (1, 0)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t, x)) ((1 : ℝ), (0 : E)) 0 := (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)
    exact (hDd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 rfl)
  have hLeft : HasDerivAt (fun t : ℝ => fderiv ℝ φ (t, x) (0, v)) (D' (1, 0) (0, v)) 0 := by
    have := (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), v)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline rfl
    exact this
  -- the right side
  have hχ : (fun y : E => fderiv ℝ (fun t : ℝ => φ (t, y)) 0 1) =ᶠ[𝓝 x] fun y => fderiv ℝ φ (0, y) (1, 0) := by
    have hc : ContinuousAt (fun y : E => ((0 : ℝ), y)) x := by fun_prop
    filter_upwards [hc.eventually hdiff] with y hy
    have h1 : HasFDerivAt (fun t : ℝ => (t, y)) (ContinuousLinearMap.inl ℝ ℝ E) 0 := hasFDerivAt_prodMk_left 0 y
    have h2 := hy.hasFDerivAt.comp (0 : ℝ) h1
    have : fderiv ℝ (fun t : ℝ => φ (t, y)) 0 = (fderiv ℝ φ (0, y)).comp (ContinuousLinearMap.inl ℝ ℝ E) := h2.fderiv
    rw [this]; simp
  have hline2 : HasFDerivAt (fun y : E => fderiv ℝ φ (0, y)) (D'.comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
    have h1 : HasFDerivAt (fun y : E => ((0 : ℝ), y)) (ContinuousLinearMap.inr ℝ ℝ E) x := hasFDerivAt_prodMk_right 0 x
    exact hDd.hasFDerivAt.comp x h1
  have hRight : HasFDerivAt (fun y : E => fderiv ℝ φ (0, y) (1, 0)) (((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).comp
      (D'.comp (ContinuousLinearMap.inr ℝ ℝ E)))) x :=
    (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).hasFDerivAt.comp x hline2
  have hsymm : D' (1, 0) (0, v) = D' (0, v) (1, 0) :=
    (hφ.isSymmSndFDerivAt (by simp [minSmoothness])) (1, 0) (0, v)
  rw [hχ.fderiv_eq, hRight.fderiv]
  have := hLeft
  refine (this.congr_of_eventuallyEq hΨ).congr_deriv ?_
  simp [hsymm]


theorem contDiff_pd {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin n) : ContDiff ℝ ∞ (fun y => pd j f y) := by
  unfold pd
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- **The Christoffel family is smooth** in `(t, y)` near `(t₀, x)` where `det (g x + t₀ h x) ≠ 0`. -/
theorem contDiffAt_christoffel_family_at (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (t₀ : ℝ) (x : Fin n → ℝ) (hx : (g x + t₀ • h x).det ≠ 0) (i j k : Fin n) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => christoffel (fun y => g y + p.1 • h y) i j k p.2) (t₀, x) := by
  have hform : ∀ p : ℝ × (Fin n → ℝ), christoffel (fun y => g y + p.1 • h y) i j k p.2 =
      (1 / 2) * ∑ l, ((g p.2 + p.1 • h p.2)⁻¹ i l *
        ((pd j (fun y => g y l k) p.2 + pd k (fun y => g y l j) p.2 - pd l (fun y => g y j k) p.2) +
          p.1 * (pd j (fun y => h y l k) p.2 + pd k (fun y => h y l j) p.2 - pd l (fun y => h y j k) p.2))) := by
    intro p
    unfold christoffel
    simp only [pd_add_smul g h p.1 _ _ _ p.2 ((hg _ _).differentiable (by simp) _) ((hh _ _).differentiable (by simp) _)]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hform]
  have hf : ∀ a b, ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => (g p.2 + p.1 • h p.2) a b) := by
    intro a b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((hg a b).comp contDiff_snd).add (contDiff_fst.mul ((hh a b).comp contDiff_snd))
  have hdet : ((g ((t₀, x) : ℝ × (Fin n → ℝ)).2 + ((t₀, x) : ℝ × (Fin n → ℝ)).1 • h ((t₀, x) : ℝ × (Fin n → ℝ)).2)).det ≠ 0 := hx
  have hA : ∀ a b c, ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => pd c (fun y => g y a b) p.2) :=
    fun a b c => (contDiff_pd (hg a b) c).comp contDiff_snd
  have hB : ∀ a b c, ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => pd c (fun y => h y a b) p.2) :=
    fun a b c => (contDiff_pd (hh a b) c).comp contDiff_snd
  refine contDiffAt_const.mul (ContDiffAt.sum fun l _ => ?_)
  refine (contDiffAt_inv_entry hf hdet i l).mul ?_
  exact ((((hA l k j).add (hA l j k)).sub (hA j k l)).add
    (contDiff_fst.mul (((hB l k j).add (hB l j k)).sub (hB j k l)))).contDiffAt


/-- **The Christoffel family is smooth** in `(t, y)` near `(0, x)`. -/
theorem contDiffAt_christoffel_family (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (x : Fin n → ℝ) (hx : (g x).det ≠ 0) (i j k : Fin n) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => christoffel (fun y => g y + p.1 • h y) i j k p.2) (0, x) := by
  simpa using contDiffAt_christoffel_family_at g h hg hh 0 x (by simpa using hx) i j k

/-- The first variation of the Christoffel symbols as a function of the point. -/
def dChristoffel (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n) (y : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ l, (-((g y)⁻¹ * h y * (g y)⁻¹) i l *
          (pd j (fun z => g z l k) y + pd k (fun z => g z l j) y - pd l (fun z => g z j k) y) +
        (g y)⁻¹ i l * (pd j (fun z => h z l k) y + pd k (fun z => h z l j) y - pd l (fun z => h z j k) y))

/-- **`d/dt ∂_μ Γ(g + t h) = ∂_μ δΓ`**. -/
theorem hasDerivAt_pd_christoffel (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (x : Fin n → ℝ) (hx : (g x).det ≠ 0) (i j k μ : Fin n) :
    HasDerivAt (fun t : ℝ => pd μ (fun y => christoffel (fun z => g z + t • h z) i j k y) x)
      (pd μ (dChristoffel g h i j k) x) 0 := by
  set φ : ℝ × (Fin n → ℝ) → ℝ := fun p => christoffel (fun y => g y + p.1 • h y) i j k p.2 with hφ
  have hsm : ContDiffAt ℝ 2 φ (0, x) :=
    (contDiffAt_christoffel_family g h hg hh x hx i j k).of_le (by simp)
  have hex := hasDerivAt_fderiv_exchange hsm (Pi.single μ (1 : ℝ) : Fin n → ℝ)
  have hnear : ∀ᶠ y in nhds x, (g y).det ≠ 0 :=
    (((contDiff_det_of hg).continuous.continuousAt (x := x)).eventually_ne hx)
  have hcongr : (fun y => fderiv ℝ (fun t : ℝ => φ (t, y)) 0 1) =ᶠ[nhds x] dChristoffel g h i j k := by
    filter_upwards [hnear] with y hy
    have hv := hasDerivAt_christoffel_add_smul g h y (fun l k => ((hg l k).differentiable (by simp)) y)
      (fun l k => ((hh l k).differentiable (by simp)) y) hy i j k
    have : fderiv ℝ (fun t : ℝ => φ (t, y)) 0 1 = deriv (fun t : ℝ => christoffel (fun z => g z + t • h z) i j k y) 0 := by
      rfl
    rw [this, hv.deriv]
    rfl
  unfold pd
  rw [← hcongr.fderiv_eq]
  exact hex

end Lightlike
