import Mathlib
import Lightlike.Canonical.ADM
import Lightlike.Canonical.LieAlgebra
import Lightlike.Spacetime.RiemannSymmetry

/-!
# The calculus of the Lie derivative of a tensor field

Smoothness of the Lie derivative `lieDeriv` and of the Lie bracket, the expansion of their partial
derivatives in terms of 2-jets (`pd_lieDeriv`), and the commutator identity
`ℒ_ξ ℒ_η h − ℒ_η ℒ_ξ h = ℒ_[ξ,η] h` for smooth fields (`lieDeriv_comm`).
-/

open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- A tensor field is smooth (`C^∞`) componentwise. -/
def SmoothTensor (h : TensorField d) : Prop := ∀ i j, ContDiff ℝ ∞ (fun y => h y i j)

/-- A vector field is smooth (`C^∞`) componentwise. -/
def SmoothVec (ξ : VectorField d) : Prop := ∀ k, ContDiff ℝ ∞ (fun y => ξ y k)

lemma smooth_pd {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (k : Fin d) :
    ContDiff ℝ ∞ (Lightlike.pd k f) :=
  contDiffOn_univ.mp (Lightlike.contDiffOn_pd hf.contDiffOn isOpen_univ k)

lemma diff_of_smooth {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (x : Fin d → ℝ) :
    DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x

lemma pd_comm_smooth {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (x : Fin d → ℝ) (a b : Fin d) :
    Lightlike.pd a (Lightlike.pd b f) x = Lightlike.pd b (Lightlike.pd a f) x :=
  Lightlike.pd_pd_comm hf.contDiffOn isOpen_univ (Set.mem_univ x) a b

/-- `ℒ_ξ h` is a smooth tensor field. -/
lemma smoothTensor_lieDeriv {h : TensorField d} {ξ : VectorField d} (hh : SmoothTensor h) (hξ : SmoothVec ξ) :
    SmoothTensor (fun y a b => lieDeriv ξ h a b y) := by
  intro i j
  unfold lieDeriv
  refine ((ContDiff.sum fun k _ => (hξ k).mul (smooth_pd (hh i j) k)).add
    (ContDiff.sum fun k _ => (hh k j).mul (smooth_pd (hξ k) i))).add
    (ContDiff.sum fun k _ => (hh i k).mul (smooth_pd (hξ k) j))

/-- The Lie bracket of smooth vector fields is smooth. -/
lemma smoothVec_lieBracket {ξ η : VectorField d} (hξ : SmoothVec ξ) (hη : SmoothVec η) :
    SmoothVec (fun y k => lieBracket ξ η y k) := by
  intro k
  unfold lieBracket
  exact ContDiff.sum fun j _ => ((hξ j).mul (smooth_pd (hη k) j)).sub ((hη j).mul (smooth_pd (hξ k) j))

/-- The 1-jet and 2-jet arrays of a tensor field at a point. -/
def jet1 (h : TensorField d) (x : Fin d → ℝ) : Fin d → Fin d → Fin d → ℝ :=
  fun k a b => Lightlike.pd k (fun y => h y a b) x

/-- The 2-jet array of a tensor field at a point. -/
def jet2 (h : TensorField d) (x : Fin d → ℝ) : Fin d → Fin d → Fin d → Fin d → ℝ :=
  fun k l a b => Lightlike.pd k (Lightlike.pd l (fun y => h y a b)) x

/-- The 1-jet of a vector field at a point, `ξ1 i k = ∂_i ξ^k`. -/
def vjet1 (ξ : VectorField d) (x : Fin d → ℝ) : Fin d → Fin d → ℝ :=
  fun i k => Lightlike.pd i (fun y => ξ y k) x

/-- The 2-jet of a vector field at a point, `ξ2 m i k = ∂_m ∂_i ξ^k`. -/
def vjet2 (ξ : VectorField d) (x : Fin d → ℝ) : Fin d → Fin d → Fin d → ℝ :=
  fun m i k => Lightlike.pd m (Lightlike.pd i (fun y => ξ y k)) x

lemma lieDeriv_eq_lie (ξ : VectorField d) (h : TensorField d) (i j : Fin d) (x : Fin d → ℝ) :
    lieDeriv ξ h i j x = LieAlgebra.lie (ξ x) (vjet1 ξ x) (h x) (jet1 h x) i j := rfl

/-- The partial derivative of `ℒ_η h` in terms of 2-jets. -/
lemma pd_lieDeriv {h : TensorField d} {η : VectorField d} (hh : SmoothTensor h) (hη : SmoothVec η)
    (m i j : Fin d) (x : Fin d → ℝ) :
    Lightlike.pd m (fun y => lieDeriv η h i j y) x =
      LieAlgebra.lie1 (η x) (vjet1 η x) (vjet2 η x) (h x) (jet1 h x) (jet2 h x) m i j := by
  have d1 : ∀ k, DifferentiableAt ℝ (fun y => η y k) x := fun k => diff_of_smooth (hη k) x
  have d2 : ∀ a b, DifferentiableAt ℝ (fun y => h y a b) x := fun a b => diff_of_smooth (hh a b) x
  have d3 : ∀ k, DifferentiableAt ℝ (fun y => Lightlike.pd k (fun y => h y i j) y) x :=
    fun k => diff_of_smooth (smooth_pd (hh i j) k) x
  unfold lieDeriv
  rw [Lightlike.pd_add, Lightlike.pd_add]
  · simp only [LieAlgebra.lie1, jet1, jet2, vjet1, vjet2]
    rw [Lightlike.pd_sum, Lightlike.pd_sum, Lightlike.pd_sum]
    · refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;>
        refine Finset.sum_congr rfl fun k _ => ?_
      · rw [Lightlike.pd_mul (d1 k) (d3 k)]
      · rw [Lightlike.pd_mul (d2 k j) (diff_of_smooth (smooth_pd (hη k) i) x)]
      · rw [Lightlike.pd_mul (d2 i k) (diff_of_smooth (smooth_pd (hη k) j) x)]
    all_goals first
      | (intro k _; exact diff_of_smooth ((hη k).mul (smooth_pd (hh i j) k)) x)
      | (intro k _; exact diff_of_smooth ((hh k j).mul (smooth_pd (hη k) i)) x)
      | (intro k _; exact diff_of_smooth ((hh i k).mul (smooth_pd (hη k) j)) x)
  all_goals first
    | exact diff_of_smooth (ContDiff.sum fun k _ => (hη k).mul (smooth_pd (hh i j) k)) x
    | exact diff_of_smooth (ContDiff.sum fun k _ => (hh k j).mul (smooth_pd (hη k) i)) x
    | exact diff_of_smooth (ContDiff.sum fun k _ => (hh i k).mul (smooth_pd (hη k) j)) x
    | exact diff_of_smooth ((ContDiff.sum fun k _ => (hη k).mul (smooth_pd (hh i j) k)).add
        (ContDiff.sum fun k _ => (hh k j).mul (smooth_pd (hη k) i))) x

/-- The partial derivative of the Lie bracket in terms of 2-jets. -/
lemma pd_lieBracket {ξ η : VectorField d} (hξ : SmoothVec ξ) (hη : SmoothVec η) (i k : Fin d)
    (x : Fin d → ℝ) :
    Lightlike.pd i (fun y => lieBracket ξ η y k) x =
      LieAlgebra.br1 (ξ x) (η x) (vjet1 ξ x) (vjet1 η x) (vjet2 ξ x) (vjet2 η x) i k := by
  unfold lieBracket
  have e : ∀ l, DifferentiableAt ℝ
      (fun y => ξ y l * Lightlike.pd l (fun y => η y k) y - η y l * Lightlike.pd l (fun y => ξ y k) y) x :=
    fun l => diff_of_smooth (((hξ l).mul (smooth_pd (hη k) l)).sub ((hη l).mul (smooth_pd (hξ k) l))) x
  rw [Lightlike.pd_sum _ (fun l _ => e l)]
  simp only [LieAlgebra.br1, vjet1, vjet2]
  refine Finset.sum_congr rfl fun l _ => ?_
  have da : DifferentiableAt ℝ (fun y => ξ y l * Lightlike.pd l (fun y => η y k) y) x :=
    diff_of_smooth ((hξ l).mul (smooth_pd (hη k) l)) x
  have db : DifferentiableAt ℝ (fun y => η y l * Lightlike.pd l (fun y => ξ y k) y) x :=
    diff_of_smooth ((hη l).mul (smooth_pd (hξ k) l)) x
  rw [Lightlike.pd_sub da db,
    Lightlike.pd_mul (diff_of_smooth (hξ l) x) (diff_of_smooth (smooth_pd (hη k) l) x),
    Lightlike.pd_mul (diff_of_smooth (hη l) x) (diff_of_smooth (smooth_pd (hξ k) l) x)]
  ring

/-- **The commutator of Lie derivatives**: `ℒ_ξ ℒ_η h − ℒ_η ℒ_ξ h = ℒ_[ξ,η] h` for smooth fields. -/
theorem lieDeriv_comm {h : TensorField d} {ξ η : VectorField d} (hh : SmoothTensor h) (hξ : SmoothVec ξ)
    (hη : SmoothVec η) (i j : Fin d) (x : Fin d → ℝ) :
    lieDeriv ξ (fun y a b => lieDeriv η h a b y) i j x - lieDeriv η (fun y a b => lieDeriv ξ h a b y) i j x =
      lieDeriv (fun y k => lieBracket ξ η y k) h i j x := by
  have hK : ∀ (ζ : VectorField d), SmoothVec ζ →
      jet1 (fun y a b => lieDeriv ζ h a b y) x =
        fun k a b => LieAlgebra.lie1 (ζ x) (vjet1 ζ x) (vjet2 ζ x) (h x) (jet1 h x) (jet2 h x) k a b := by
    intro ζ hζ; funext k a b; exact pd_lieDeriv hh hζ k a b x
  have hK0 : ∀ ζ : VectorField d,
      (fun a b => lieDeriv ζ h a b x) = LieAlgebra.lie (ζ x) (vjet1 ζ x) (h x) (jet1 h x) := by
    intro ζ; funext a b; rfl
  simp only [lieDeriv_eq_lie ξ (fun y a b => lieDeriv η h a b y),
    lieDeriv_eq_lie η (fun y a b => lieDeriv ξ h a b y), hK ξ hξ, hK η hη]
  have hb1 : vjet1 (fun y k => lieBracket ξ η y k) x = LieAlgebra.br1 (ξ x) (η x) (vjet1 ξ x) (vjet1 η x)
      (vjet2 ξ x) (vjet2 η x) := by
    funext a k; exact pd_lieBracket hξ hη a k x
  rw [lieDeriv_eq_lie, hb1]
  have := LieAlgebra.lie_lie_sub (ξ x) (η x) (vjet1 ξ x) (vjet1 η x) (vjet2 ξ x) (vjet2 η x) (h x) (jet1 h x)
    (jet2 h x) (fun m i k => pd_comm_smooth (hξ k) x m i) (fun m i k => pd_comm_smooth (hη k) x m i)
    (fun k l a b => pd_comm_smooth (hh a b) x k l) i j
  rw [hK0 η, hK0 ξ]
  exact this

end Lightlike.Canonical

end
