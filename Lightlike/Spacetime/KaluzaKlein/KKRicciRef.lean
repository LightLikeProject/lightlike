import Lightlike.Spacetime.KaluzaKlein.KKSmooth

/-!
# The Ricci tensor of the product metric `g ⊕ 1` (G1-044)

The Christoffel symbols of `kkRef g` are those of `g` (pulled back along `proj`) when the three indices are `< n`, and
`0` otherwise (`christoffel_kkRef_eq`).  Consequently the Ricci tensor of `kkRef g` at `x` is `ricci g (proj x)` on
the indices `< n` (`ricci_kkRef_cc`) and vanishes if one of the indices is the last one (`ricci_kkRef_last`).

Supporting file for the row G1-044 (Kaluza-Klein reduction).
-/

open Matrix Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

namespace KK

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {x : Fin (n + 1) → ℝ}

/-- The Christoffel symbols of the product metric: those of `g` on `proj` for indices `< n`, else `0`. -/
def cref (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin (n + 1)) (y : Fin (n + 1) → ℝ) : ℝ :=
  Fin.lastCases (motive := fun _ => ℝ) 0
    (fun c => Fin.lastCases (motive := fun _ => ℝ) 0
      (fun a => Fin.lastCases (motive := fun _ => ℝ) 0 (fun b => christoffel g c a b (proj y)) k) j) i

@[simp] theorem cref_cab (c a b : Fin n) (y : Fin (n + 1) → ℝ) :
    cref g c.castSucc a.castSucc b.castSucc y = christoffel g c a b (proj y) := by simp [cref]

@[simp] theorem cref_last_left (j k : Fin (n + 1)) (y : Fin (n + 1) → ℝ) : cref g (Fin.last n) j k y = 0 := by
  simp [cref]

@[simp] theorem cref_last_mid (c : Fin n) (k : Fin (n + 1)) (y : Fin (n + 1) → ℝ) :
    cref g c.castSucc (Fin.last n) k y = 0 := by simp [cref]

@[simp] theorem cref_last_right (c a : Fin n) (y : Fin (n + 1) → ℝ) :
    cref g c.castSucc a.castSucc (Fin.last n) y = 0 := by simp [cref]

/-- **Christoffel symbols of the product metric** at points over `U`. -/
theorem christoffel_kkRef_eq (hg : IsCoordMetric g U) (hgs : ∀ y a b, g y a b = g y b a) {y : Fin (n + 1) → ℝ}
    (hy : proj y ∈ U) (i j k : Fin (n + 1)) : christoffel (kkRef g) i j k y = cref g i j k y := by
  have h : KKReg g (fun _ _ => 0) (fun _ => 1) (proj y) :=
    kkReg_of_contDiffOn hg (fun _ => contDiffOn_const) contDiffOn_const (fun _ _ => one_ne_zero) hy
  have hs := christoffel_symm (kkRef g) (kkMetric_symm hgs)
  refine Fin.lastCases ?_ (fun c => ?_) i <;> refine Fin.lastCases ?_ (fun a => ?_) j <;>
    refine Fin.lastCases ?_ (fun b => ?_) k
  · simpa using kkRef_555 h
  · rw [hs]; simpa using kkRef_5a5 h b
  · simpa using kkRef_5a5 h a
  · simpa using kkRef_5ab h a b
  · rw [hs]; simpa using kkRef_c55 h c
  · rw [hs]; simpa using kkRef_ca5 h c b
  · simpa using kkRef_ca5 h c a
  · simpa using kkRef_cab h c a b

theorem eventuallyEq_christoffel_kkRef (hg : IsCoordMetric g U) (hgs : ∀ y a b, g y a b = g y b a)
    (hx : proj x ∈ U) (i j k : Fin (n + 1)) : christoffel (kkRef g) i j k =ᶠ[𝓝 x] cref g i j k := by
  filter_upwards [(isOpen_preimage_proj hg.isOpen).mem_nhds hx] with y hy
  exact christoffel_kkRef_eq hg hgs hy i j k

/-- The Riemann tensor of `kkRef g`, in terms of `cref`. -/
theorem riemann_kkRef_cref (hg : IsCoordMetric g U) (hgs : ∀ y a b, g y a b = g y b a) (hx : proj x ∈ U)
    (ρ σ μ ν : Fin (n + 1)) :
    riemann (kkRef g) ρ σ μ ν x = pd μ (cref g ρ ν σ) x - pd ν (cref g ρ μ σ) x +
      ∑ l, (cref g ρ μ l x * cref g l ν σ x - cref g ρ ν l x * cref g l μ σ x) := by
  have hp : ∀ μ i j k, pd μ (christoffel (kkRef g) i j k) x = pd μ (cref g i j k) x := fun μ i j k => by
    unfold pd
    rw [(eventuallyEq_christoffel_kkRef hg hgs hx i j k).fderiv_eq]
  have hc := fun i j k => christoffel_kkRef_eq hg hgs (y := x) hx i j k
  unfold riemann
  simp only [hp, hc]

@[simp] theorem pd_cref_last_left (μ j k : Fin (n + 1)) (y : Fin (n + 1) → ℝ) :
    pd μ (cref g (Fin.last n) j k) y = 0 := by
  have : cref g (Fin.last n) j k = fun _ => 0 := funext fun z => cref_last_left j k z
  rw [this, pd_const]

@[simp] theorem pd_cref_last_mid (μ : Fin (n + 1)) (c : Fin n) (k : Fin (n + 1)) (y : Fin (n + 1) → ℝ) :
    pd μ (cref g c.castSucc (Fin.last n) k) y = 0 := by
  have : cref g c.castSucc (Fin.last n) k = fun _ => 0 := funext fun z => cref_last_mid c k z
  rw [this, pd_const]

@[simp] theorem pd_cref_last_right (μ : Fin (n + 1)) (c a : Fin n) (y : Fin (n + 1) → ℝ) :
    pd μ (cref g c.castSucc a.castSucc (Fin.last n)) y = 0 := by
  have : cref g c.castSucc a.castSucc (Fin.last n) = fun _ => 0 := funext fun z => cref_last_right c a z
  rw [this, pd_const]

theorem cref_cab_fun (c a b : Fin n) :
    cref g c.castSucc a.castSucc b.castSucc = fun z => christoffel g c a b (proj z) :=
  funext fun z => cref_cab c a b z

/-- Tangential derivative of `cref`. -/
theorem pd_cref_cab {c a b : Fin n} (hd : DifferentiableAt ℝ (christoffel g c a b) (proj x)) (d : Fin n) :
    pd d.castSucc (cref g c.castSucc a.castSucc b.castSucc) x = pd d (christoffel g c a b) (proj x) := by
  rw [cref_cab_fun]
  exact pd_comp_proj _ x hd d

/-- The derivative of `cref` in the last direction vanishes. -/
theorem pd_cref_last_dir (hd : ∀ c a b, DifferentiableAt ℝ (christoffel g c a b) (proj x)) (i j k : Fin (n + 1)) :
    pd (Fin.last n) (cref g i j k) x = 0 := by
  refine Fin.lastCases ?_ (fun c => ?_) i
  · simp
  refine Fin.lastCases ?_ (fun a => ?_) j
  · simp
  refine Fin.lastCases ?_ (fun b => ?_) k
  · simp
  rw [cref_cab_fun]
  exact pd_last_comp_proj _ x (hd c a b)

/-- **The Ricci tensor of the product metric**, tangential components. -/
theorem ricci_kkRef_cc (hg : IsCoordMetric g U) (hgs : ∀ y a b, g y a b = g y b a) (hx : proj x ∈ U)
    (a b : Fin n) : ricci (kkRef g) a.castSucc b.castSucc x = ricci g a b (proj x) := by
  have hd : ∀ c a b, DifferentiableAt ℝ (christoffel g c a b) (proj x) := fun c a b =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_christoffel c a b) hg.isOpen hx
  unfold ricci
  rw [Fin.sum_univ_castSucc]
  simp only [riemann_kkRef_cref hg hgs hx]
  simp only [Fin.sum_univ_castSucc, pd_cref_last_left, cref_last_left,
    cref_last_mid, cref_last_right, pd_cref_cab (hd _ _ _), cref_cab]
  simp [riemann]

theorem cref_mid_last (i k : Fin (n + 1)) (y : Fin (n + 1) → ℝ) : cref g i (Fin.last n) k y = 0 := by
  refine Fin.lastCases (by simp) (fun c => by simp) i

theorem cref_right_last (i j : Fin (n + 1)) (y : Fin (n + 1) → ℝ) : cref g i j (Fin.last n) y = 0 := by
  refine Fin.lastCases (by simp) (fun c => ?_) i
  refine Fin.lastCases (by simp) (fun a => by simp) j

theorem pd_cref_mid_last (μ i k : Fin (n + 1)) (y : Fin (n + 1) → ℝ) :
    pd μ (cref g i (Fin.last n) k) y = 0 := by
  have : cref g i (Fin.last n) k = fun _ => 0 := funext fun z => cref_mid_last i k z
  rw [this, pd_const]

theorem pd_cref_right_last (μ i j : Fin (n + 1)) (y : Fin (n + 1) → ℝ) :
    pd μ (cref g i j (Fin.last n)) y = 0 := by
  have : cref g i j (Fin.last n) = fun _ => 0 := funext fun z => cref_right_last i j z
  rw [this, pd_const]

/-- **The Ricci tensor of the product metric** vanishes if one of the indices is the last one. -/
theorem ricci_kkRef_last (hg : IsCoordMetric g U) (hgs : ∀ y a b, g y a b = g y b a) (hx : proj x ∈ U)
    (σ ν : Fin (n + 1)) (h : σ = Fin.last n ∨ ν = Fin.last n) : ricci (kkRef g) σ ν x = 0 := by
  have hd : ∀ c a b, DifferentiableAt ℝ (christoffel g c a b) (proj x) := fun c a b =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_christoffel c a b) hg.isOpen hx
  refine Finset.sum_eq_zero fun ρ _ => ?_
  rw [riemann_kkRef_cref hg hgs hx]
  rcases h with rfl | rfl
  · simp [cref_right_last, pd_cref_right_last]
  · simp [cref_mid_last, pd_cref_mid_last, pd_cref_last_dir hd]

end KK

end Lightlike
