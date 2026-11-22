import Lightlike.Spacetime.GE3Row.Jacobi
import Lightlike.Spacetime.RicciContinuous

/-!
# Jacobi fields from variations through geodesics (row G1-006, GE3)

Algebra of the connection terms: the expansion of `R(J, w) w` in terms of `Γ` and `∂Γ`.
-/

open Set Filter Topology Matrix
open scoped ContDiff

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The directional derivative of the connection term: `(∂_y Γ)(x)(v, u)^i = Σ ∂_y Γ^i_{jk} v^j u^k`. -/
noncomputable def gammaDeriv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x y v u : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j, ∑ k, fderiv ℝ (Lightlike.christoffel g i j k) x y * v j * u k

/-- A directional derivative is the sum of the coordinate partial derivatives. -/
theorem fderiv_eq_sum_pd (f : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ m, v m * Lightlike.pd m f x := by
  have hv : v = ∑ m, v m • (Pi.single m (1 : ℝ) : Fin n → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, Lightlike.pd]

section sums

variable {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℝ)

theorem sum3_cyc : ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum3_rev : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, f a b c := Finset.sum_comm

variable (h : ι → ι → ι → ι → ℝ)

theorem sum4_bdca : ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ b, ∑ d, ∑ c, ∑ a, h a b c d := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => sum3_rev (fun a c d => h a b c d)

theorem sum4_cdba : ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ c, ∑ d, ∑ b, ∑ a, h a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ a, ∑ c, ∑ b, ∑ d, h a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, h a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, h a b c d :=
        Finset.sum_congr rfl fun c _ => sum3_rev (fun a b d => h a b c d)

end sums

/-- `R(J, w) w = (∂_J Γ)(w, w) - (∂_w Γ)(J, w) + Γ(J, Γ(w, w)) - Γ(w, Γ(J, w))`. -/
theorem riemannApply_eq (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w J : Fin n → ℝ) :
    riemannApply g x w J = gammaDeriv g x J w w - gammaDeriv g x w J w
      + gammaApply g x J (gammaApply g x w w) - gammaApply g x w (gammaApply g x J w) := by
  funext i
  simp only [riemannApply, gammaDeriv, gammaApply, Lightlike.riemann, Pi.add_apply, Pi.sub_apply,
    fderiv_eq_sum_pd, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  have e1 : ∑ s, ∑ m, ∑ v, Lightlike.pd m (Lightlike.christoffel g i v s) x * w s * J m * w v =
      ∑ j, ∑ k, ∑ m, J m * Lightlike.pd m (Lightlike.christoffel g i j k) x * w j * w k := by
    rw [sum3_cyc (fun j k m => J m * Lightlike.pd m (Lightlike.christoffel g i j k) x * w j * w k)]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ s, ∑ m, ∑ v, Lightlike.pd v (Lightlike.christoffel g i m s) x * w s * J m * w v =
      ∑ j, ∑ k, ∑ m, w m * Lightlike.pd m (Lightlike.christoffel g i j k) x * J j * w k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ s, ∑ m, ∑ v, ∑ l, Lightlike.christoffel g i m l x * Lightlike.christoffel g l v s x *
        w s * J m * w v =
      ∑ x_1, ∑ k, ∑ x_2, ∑ i_1, Lightlike.christoffel g i x_1 k x * J x_1 *
        (Lightlike.christoffel g k x_2 i_1 x * w x_2 * w i_1) := by
    rw [sum4_bdca (fun s m v l => Lightlike.christoffel g i m l x *
      Lightlike.christoffel g l v s x * w s * J m * w v)]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e4 : ∑ s, ∑ m, ∑ v, ∑ l, Lightlike.christoffel g i v l x * Lightlike.christoffel g l m s x *
        w s * J m * w v =
      ∑ x_1, ∑ k, ∑ x_2, ∑ i_1, Lightlike.christoffel g i x_1 k x * w x_1 *
        (Lightlike.christoffel g k x_2 i_1 x * J x_2 * w i_1) := by
    rw [sum4_cdba (fun s m v l => Lightlike.christoffel g i v l x *
      Lightlike.christoffel g l m s x * w s * J m * w v)]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, e3, e4]
  ring

/-- The Christoffel symbols of a coordinate metric are symmetric in the lower indices on `U`. -/
theorem christoffel_symm_of_mem (hg : Lightlike.IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
    (i j k : Fin n) :
    Lightlike.christoffel g i j k y = Lightlike.christoffel g i k j y := by
  have hs : ∀ a b, (fun z => g z a b) =ᶠ[𝓝 y] (fun z => g z b a) := fun a b =>
    Filter.eventuallyEq_of_mem (hg.isOpen.mem_nhds hy) fun z hz => by
      have := congrFun (congrFun (hg.symm z hz) b) a
      simpa using this
  unfold Lightlike.christoffel
  refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
  have h3 : Lightlike.pd l (fun z => g z j k) y = Lightlike.pd l (fun z => g z k j) y := by
    unfold Lightlike.pd
    rw [(hs j k).fderiv_eq]
  rw [h3]
  ring

/-- Symmetric lower indices: `Γ(v, u) = Γ(u, v)`. -/
theorem gammaApply_comm (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (v u : Fin n → ℝ) : gammaApply g x v u = gammaApply g x u v := by
  funext i
  simp only [gammaApply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [christoffel_symm_of_mem hg hx i k j]
  ring

/-- Symmetric lower indices: `(∂_y Γ)(v, u) = (∂_y Γ)(u, v)`. -/
theorem gammaDeriv_comm (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (y v u : Fin n → ℝ) : gammaDeriv g x y v u = gammaDeriv g x y u v := by
  funext i
  simp only [gammaDeriv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have : Lightlike.christoffel g i k j =ᶠ[𝓝 x] Lightlike.christoffel g i j k :=
    Filter.eventuallyEq_of_mem (hg.isOpen.mem_nhds hx) fun z hz =>
      christoffel_symm_of_mem hg hz i k j
  rw [this.fderiv_eq]
  ring

theorem gammaApply_add_right (x v u u' : Fin n → ℝ) :
    gammaApply g x v (u + u') = gammaApply g x v u + gammaApply g x v u' := by
  funext i
  simp [gammaApply, mul_add, Finset.sum_add_distrib]

theorem gammaApply_neg_left (x v u : Fin n → ℝ) :
    gammaApply g x (-v) u = -gammaApply g x v u := by
  funext i
  simp [gammaApply, Finset.sum_neg_distrib]

theorem accel_eq_neg_gammaApply (x v : Fin n → ℝ) : accel g x v = -gammaApply g x v v := by
  funext i
  simp [accel, gammaApply, mul_assoc]

/-- Product rule for the connection term along curves. -/
theorem hasDerivAt_gammaApply {γ w u : ℝ → Fin n → ℝ} {γ' w' u' : Fin n → ℝ} {t : ℝ}
    (hc : ∀ i j k, DifferentiableAt ℝ (Lightlike.christoffel g i j k) (γ t))
    (hγ : HasDerivAt γ γ' t) (hw : HasDerivAt w w' t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun r => gammaApply g (γ r) (w r) (u r))
      (gammaDeriv g (γ t) γ' (w t) (u t) + gammaApply g (γ t) w' (u t) +
        gammaApply g (γ t) (w t) u') t := by
  rw [hasDerivAt_pi]
  intro i
  have hj : ∀ j k, HasDerivAt (fun r => Lightlike.christoffel g i j k (γ r) * w r j * u r k)
      (fderiv ℝ (Lightlike.christoffel g i j k) (γ t) γ' * w t j * u t k +
        Lightlike.christoffel g i j k (γ t) * w' j * u t k +
        Lightlike.christoffel g i j k (γ t) * w t j * u' k) t := by
    intro j k
    have h1 : HasDerivAt (fun r => Lightlike.christoffel g i j k (γ r))
        (fderiv ℝ (Lightlike.christoffel g i j k) (γ t) γ') t :=
      (hc i j k).hasFDerivAt.comp_hasDerivAt t hγ
    have h2 : HasDerivAt (fun r => w r j) (w' j) t := (hasDerivAt_pi.mp hw) j
    have h3 : HasDerivAt (fun r => u r k) (u' k) t := (hasDerivAt_pi.mp hu) k
    have := (h1.mul h2).mul h3
    convert this using 1
    simp only [Pi.mul_apply]
    ring
  have := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hj j k
  refine HasDerivAt.congr_deriv this ?_
  simp only [Pi.add_apply, gammaDeriv, gammaApply, ← Finset.sum_add_distrib]

end Lightlike.Geodesic
