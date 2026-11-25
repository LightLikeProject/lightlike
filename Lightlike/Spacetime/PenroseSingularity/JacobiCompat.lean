import Lightlike.Spacetime.PenroseSingularity.JacobiIdentity
import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.Spacetime.RaychaudhuriFocusing

/-!
# Metric compatibility along a curve (G1-012, step D3b)

For a coordinate metric `g` on `U`, the covariant derivative along a curve `γ` of velocity `v`,
`D W = W' + Γ(v, W)`, satisfies `(g(W₁, W₂))' = g(D W₁, W₂) + g(W₁, D W₂)`.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The covariant derivative along a curve, in coordinates: `(D W)^a = W'^a + Γ^a_{bc} v^b W^c`. -/
def covDAlong (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x v W W' : Fin n → ℝ) (a : Fin n) : ℝ :=
  W' a + ∑ b, ∑ c, Lightlike.christoffel g a b c x * v b * W c

/-- The `g`-pairing of two vectors at a point. -/
def gpairAt (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (W₁ W₂ : Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, g x a b * W₁ a * W₂ b

/-- The pointwise algebra: `∂_d g_{ab} = Γ_{a d b} + Γ_{b d a}` makes the Christoffel terms of the two
covariant derivatives add up to the derivative of `g`. -/
theorem compat_algebra (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (v W₁ W₂ : Fin n → ℝ) :
    (∑ a, ∑ b, g x a b * (∑ d, ∑ c, Lightlike.christoffel g a d c x * v d * W₁ c) * W₂ b) +
      (∑ a, ∑ b, g x a b * W₁ a * (∑ d, ∑ c, Lightlike.christoffel g b d c x * v d * W₂ c)) =
    ∑ a, ∑ b, (∑ d, v d * Lightlike.pd d (fun y => g y a b) x) * W₁ a * W₂ b := by
  set Γf : Fin n → Fin n → Fin n → ℝ := fun a d c => Lightlike.christoffelFirst g a d c x with hΓf
  have hlow : ∀ b d c, ∑ a, g x b a * Lightlike.christoffel g a d c x = Γf b d c := fun b d c =>
    hg.lower_christoffel hx b d c
  have hsymm : ∀ a b, g x a b = g x b a := fun a b => by
    have := congrFun (congrFun (hg.symm x hx) a) b
    simp only [Matrix.transpose_apply] at this
    exact this.symm
  -- the first Christoffel term
  have hA : ∑ a, ∑ b, g x a b * (∑ d, ∑ c, Lightlike.christoffel g a d c x * v d * W₁ c) * W₂ b =
      ∑ a, ∑ b, ∑ d, v d * Γf b d a * W₁ a * W₂ b := by
    have h1 : ∀ a b, g x a b * (∑ d, ∑ c, Lightlike.christoffel g a d c x * v d * W₁ c) * W₂ b =
        ∑ d, ∑ c, g x a b * Lightlike.christoffel g a d c x * v d * W₁ c * W₂ b := fun a b => by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    simp only [h1]
    -- reorder the sums to `b d c a` and use the lowered symbol
    calc ∑ a, ∑ b, ∑ d, ∑ c, g x a b * Lightlike.christoffel g a d c x * v d * W₁ c * W₂ b
        = ∑ b, ∑ a, ∑ d, ∑ c, g x a b * Lightlike.christoffel g a d c x * v d * W₁ c * W₂ b :=
          Finset.sum_comm
      _ = ∑ b, ∑ d, ∑ c, ∑ a, g x a b * Lightlike.christoffel g a d c x * v d * W₁ c * W₂ b := by
          refine Finset.sum_congr rfl fun b _ => ?_
          calc ∑ a, ∑ d, ∑ c, g x a b * Lightlike.christoffel g a d c x * v d * W₁ c * W₂ b
              = ∑ d, ∑ a, ∑ c, g x a b * Lightlike.christoffel g a d c x * v d * W₁ c * W₂ b :=
                Finset.sum_comm
            _ = ∑ d, ∑ c, ∑ a, g x a b * Lightlike.christoffel g a d c x * v d * W₁ c * W₂ b :=
                Finset.sum_congr rfl fun d _ => Finset.sum_comm
      _ = ∑ b, ∑ d, ∑ c, Γf b d c * v d * W₁ c * W₂ b := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
            Finset.sum_congr rfl fun c _ => ?_
          rw [← hlow b d c]
          simp only [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by rw [hsymm a b]
      _ = ∑ a, ∑ b, ∑ d, v d * Γf b d a * W₁ a * W₂ b := by
          calc ∑ b, ∑ d, ∑ c, Γf b d c * v d * W₁ c * W₂ b
              = ∑ b, ∑ c, ∑ d, Γf b d c * v d * W₁ c * W₂ b :=
                Finset.sum_congr rfl fun b _ => Finset.sum_comm
            _ = ∑ c, ∑ b, ∑ d, Γf b d c * v d * W₁ c * W₂ b := Finset.sum_comm
            _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
                Finset.sum_congr rfl fun d _ => by ring
  -- the second Christoffel term
  have hB : ∑ a, ∑ b, g x a b * W₁ a * (∑ d, ∑ c, Lightlike.christoffel g b d c x * v d * W₂ c) =
      ∑ a, ∑ b, ∑ d, v d * Γf a d b * W₁ a * W₂ b := by
    have h1 : ∀ a b, g x a b * W₁ a * (∑ d, ∑ c, Lightlike.christoffel g b d c x * v d * W₂ c) =
        ∑ d, ∑ c, g x a b * Lightlike.christoffel g b d c x * v d * W₁ a * W₂ c := fun a b => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    simp only [h1]
    calc ∑ a, ∑ b, ∑ d, ∑ c, g x a b * Lightlike.christoffel g b d c x * v d * W₁ a * W₂ c
        = ∑ a, ∑ d, ∑ c, ∑ b, g x a b * Lightlike.christoffel g b d c x * v d * W₁ a * W₂ c := by
          refine Finset.sum_congr rfl fun a _ => ?_
          calc ∑ b, ∑ d, ∑ c, g x a b * Lightlike.christoffel g b d c x * v d * W₁ a * W₂ c
              = ∑ d, ∑ b, ∑ c, g x a b * Lightlike.christoffel g b d c x * v d * W₁ a * W₂ c :=
                Finset.sum_comm
            _ = ∑ d, ∑ c, ∑ b, g x a b * Lightlike.christoffel g b d c x * v d * W₁ a * W₂ c :=
                Finset.sum_congr rfl fun d _ => Finset.sum_comm
      _ = ∑ a, ∑ d, ∑ c, Γf a d c * v d * W₁ a * W₂ c := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ =>
            Finset.sum_congr rfl fun c _ => ?_
          rw [← hlow a d c]
          simp only [Finset.sum_mul]
      _ = ∑ a, ∑ b, ∑ d, v d * Γf a d b * W₁ a * W₂ b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          calc ∑ d, ∑ c, Γf a d c * v d * W₁ a * W₂ c
              = ∑ c, ∑ d, Γf a d c * v d * W₁ a * W₂ c := Finset.sum_comm
            _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [hA, hB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hg.pd_eq_christoffelFirst hx d a b]
  simp only [hΓf]
  ring

/-- **Metric compatibility along a curve.** -/
theorem hasDerivAt_gpair (hg : Lightlike.IsCoordMetric g U) {γ : ℝ → Fin n → ℝ} {v : Fin n → ℝ}
    {t : ℝ} (hγ : HasDerivAt γ v t) (hγU : γ t ∈ U) {W₁ W₂ : ℝ → Fin n → ℝ} {W₁' W₂' : Fin n → ℝ}
    (h₁ : HasDerivAt W₁ W₁' t) (h₂ : HasDerivAt W₂ W₂' t) :
    HasDerivAt (fun s => gpairAt g (γ s) (W₁ s) (W₂ s))
      (gpairAt g (γ t) (fun a => covDAlong g (γ t) v (W₁ t) W₁' a) (W₂ t) +
        gpairAt g (γ t) (W₁ t) (fun a => covDAlong g (γ t) v (W₂ t) W₂' a)) t := by
  have hgd : ∀ a b, HasDerivAt (fun s => g (γ s) a b)
      (∑ d, v d * Lightlike.pd d (fun y => g y a b) (γ t)) t := by
    intro a b
    have hdiff : DifferentiableAt ℝ (fun y => g y a b) (γ t) :=
      ((hg.smooth a b).contDiffAt (hg.isOpen.mem_nhds hγU)).differentiableAt (by simp)
    have := hdiff.hasFDerivAt.comp_hasDerivAt t hγ
    refine this.congr_deriv ?_
    rw [Lightlike.clm_apply_eq_sum]
    rfl
  have hprod : ∀ a b, HasDerivAt (fun s => g (γ s) a b * W₁ s a * W₂ s b)
      ((∑ d, v d * Lightlike.pd d (fun y => g y a b) (γ t)) * W₁ t a * W₂ t b +
        g (γ t) a b * W₁' a * W₂ t b + g (γ t) a b * W₁ t a * W₂' b) t := by
    intro a b
    have h1 : HasDerivAt (fun s => W₁ s a) (W₁' a) t := (hasDerivAt_pi.1 h₁) a
    have h2 : HasDerivAt (fun s => W₂ s b) (W₂' b) t := (hasDerivAt_pi.1 h₂) b
    exact (((hgd a b).mul h1).mul h2).congr_deriv (by simp only [Pi.mul_apply]; ring)
  have hsum := HasDerivAt.fun_sum fun a (_ : a ∈ Finset.univ) =>
    HasDerivAt.fun_sum fun b (_ : b ∈ Finset.univ) => hprod a b
  refine hsum.congr_deriv ?_
  have hc := compat_algebra hg hγU v (W₁ t) (W₂ t)
  unfold gpairAt covDAlong
  simp only [Finset.sum_add_distrib, mul_add, add_mul] at hc ⊢
  linear_combination (-1 : ℝ) * hc

end Lightlike.Penrose
