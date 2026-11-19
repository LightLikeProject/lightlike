import Lightlike.Spacetime.PoincareKilling
import Lightlike.Spacetime.LieMetric

/-!
# Homogeneity and isotropy give the flat FLRW form (G1-024, flat case)

On `ℝ⁴ = ℝ × ℝ³` (coordinate `0` is time), let `g` be a smooth metric of any signature for which the three spatial translations
`∂_k` and the three spatial rotations `x_i ∂_j - x_j ∂_i` are Killing fields (`lieDerivMetric g X = 0` on the basis fields).
Then `g_{00}`, `g_{0k}` and `g_{ij}` depend on the time `x⁰` only, `g_{0k} = 0` and `g_{ij} = a(x⁰) δ_{ij}`:
`g = b(t) dt² + a(t) δ`, the flat FLRW form (with lapse `b` and scale factor `a`, `b < 0 < a` for a Lorentzian metric).

* `lieDerivMetric_affField_basis`: the Lie derivative of the metric on the basis fields in coordinates;
* `spatial_const`: a function with vanishing spatial derivatives depends on the time only;
* `flat_flrw_of_killing`: the classification.

**Limits.** Only the flat case `k = 0` (translations and rotations of `ℝ³`); the curved cases `k ≠ 0` are
`Lightlike.curved_flrw_of_killing` (`HomogeneousIsotropicCurved.lean`). The classification of three-dimensional maximally
symmetric spaces (the step from abstract homogeneous and isotropic slices to these coordinates) is a follow-up task, as is the converse
(the FLRW metric has these Killing fields) and the statement for isometry groups acting (not only infinitesimally). The
smoothness of the components is a hypothesis (it holds for a smooth metric).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The standard basis vector as a constant field. -/
def basisField (n : ℕ) (μ : Fin n) : Π y : Fin n → ℝ, TangentSpace 𝓘(ℝ, Fin n → ℝ) y := fun _ => Pi.single μ 1

/-- The metric components `g(e_μ, e_ν)` as a function on `ℝⁿ`. -/
def metricComp (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)) (μ ν : Fin n) (y : Fin n → ℝ) : ℝ :=
  g.g y (Pi.single μ 1) (Pi.single ν 1)

theorem fderiv_basisField (μ : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ ((basisField n μ : Π y : Fin n → ℝ, TangentSpace 𝓘(ℝ, Fin n → ℝ) y) : (Fin n → ℝ) → (Fin n → ℝ)) x = 0 :=
  (hasFDerivAt_const (Pi.single μ (1 : ℝ) : Fin n → ℝ) x).fderiv

theorem g_zero_left (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)) (x w : Fin n → ℝ) :
    g.g x (0 : Fin n → ℝ) w = 0 := by
  have h := congrArg (fun L => L w) (map_zero (g.g x))
  exact h

theorem g_zero_right (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)) (x v : Fin n → ℝ) :
    g.g x v (0 : Fin n → ℝ) = 0 := map_zero (g.g x v)

theorem g_sub_left (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)) (x a b w : Fin n → ℝ) :
    g.g x (a - b) w = g.g x a w - g.g x b w := by
  have h := congrArg (fun L => L w) (map_sub (g.g x) a b)
  exact h

theorem g_sub_right (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)) (x v a b : Fin n → ℝ) :
    g.g x v (a - b) = g.g x v a - g.g x v b := map_sub (g.g x v) a b

theorem g_smul_left (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)) (x : Fin n → ℝ) (c : ℝ) (a w : Fin n → ℝ) :
    g.g x (c • a) w = c * g.g x a w := by
  have h := congrArg (fun L => L w) (map_smul (g.g x) c a)
  exact h

theorem g_smul_right (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ)) (x : Fin n → ℝ) (c : ℝ) (v a : Fin n → ℝ) :
    g.g x v (c • a) = c * g.g x v a := map_smul (g.g x v) c a

/-- **The Lie derivative of the metric on the basis fields in coordinates**:
`(L_X g)(e_μ, e_ν) = ∂_X g_{μν} + g(A e_μ, e_ν) + g(e_μ, A e_ν)` for an affine field `X = A y + c`. -/
theorem lieDerivMetric_affField_basis (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ))
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (c : Fin n → ℝ) (μ ν : Fin n) (x : Fin n → ℝ) :
    lieDerivMetric g (affField A c) (basisField n μ) (basisField n ν) x =
      fderiv ℝ (metricComp g μ ν) x (A x + c) + g.g x (A (Pi.single μ 1)) (Pi.single ν 1) +
        g.g x (Pi.single μ 1) (A (Pi.single ν 1)) := by
  unfold lieDerivMetric
  have h1 : ∀ κ : Fin n, mlieBracket 𝓘(ℝ, Fin n → ℝ) (affField A c) (basisField n κ) x = - A (Pi.single κ 1) := by
    intro κ
    rw [mlieBracket_flat, fderiv_affField, fderiv_basisField]
    change (0 : Fin n → ℝ) - A (Pi.single κ 1) = -A (Pi.single κ 1)
    exact zero_sub _
  have h3 : mvfderiv 𝓘(ℝ, Fin n → ℝ) (gpair g (basisField n μ) (basisField n ν)) x (affField A c x) =
      fderiv ℝ (metricComp g μ ν) x (A x + c) := by
    have : gpair g (basisField n μ) (basisField n ν) = metricComp g μ ν := rfl
    rw [this]
    unfold mvfderiv
    rw [mfderiv_eq_fderiv]
    rfl
  rw [h1 μ, h1 ν, h3]
  have e1 : (g.g x (-A (Pi.single μ 1))) (Pi.single ν 1) = -(g.g x (A (Pi.single μ 1))) (Pi.single ν 1) := by
    have := congrArg (fun L => L (Pi.single ν 1)) (map_neg (g.g x) (A (Pi.single μ 1) : TangentSpace 𝓘(ℝ, Fin n → ℝ) x))
    exact this
  have e2 : (g.g x (Pi.single μ 1)) (-A (Pi.single ν 1)) = -(g.g x (Pi.single μ 1)) (A (Pi.single ν 1)) := by
    exact map_neg ((g.g x) (Pi.single μ 1)) (A (Pi.single ν 1))
  show _ - (g.g x (-A (Pi.single μ 1))) (Pi.single ν 1) - (g.g x (Pi.single μ 1)) (-A (Pi.single ν 1)) = _
  rw [e1, e2]
  ring


/-- A function with vanishing spatial derivatives depends on the time only. -/
theorem spatial_const {m : ℕ} {f : (Fin (m + 1) → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (h : ∀ x, ∀ k : Fin (m + 1), k ≠ 0 → fderiv ℝ f x (Pi.single k 1) = 0) (x : Fin (m + 1) → ℝ) :
    f x = f (Pi.single 0 (x 0)) := by
  set y : Fin (m + 1) → ℝ := Pi.single 0 (x 0) with hy
  set d : Fin (m + 1) → ℝ := x - y with hd
  have hd0 : d 0 = 0 := by simp [hd, hy]
  have hdir : ∀ z : Fin (m + 1) → ℝ, fderiv ℝ f z d = 0 := by
    intro z
    have hdecomp : d = ∑ k, d k • (Pi.single k 1 : Fin (m + 1) → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [map_smul]
    by_cases hk : k = 0
    · subst hk; simp [hd0]
    · simp [h z k hk]
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (y + s • d)) 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => y + s • d) d s := by
      simpa using ((hasDerivAt_id s).smul_const d).const_add y
    have := (hf (y + s • d)).hasFDerivAt.comp_hasDerivAt s h1
    rw [hdir] at this
    exact this
  have hconst := is_const_of_deriv_eq_zero (f := fun s : ℝ => f (y + s • d))
    (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) 1 0
  simpa [hd, hy] using hconst

/-- The rotation `y ↦ y_i e_j - y_j e_i` of the coordinate plane `(i, j)`. -/
def rotCLM (i j : Fin n) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (Pi.single j (1 : ℝ) : Fin n → ℝ) -
    (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (Pi.single i (1 : ℝ) : Fin n → ℝ)

theorem rotCLM_apply (i j : Fin n) (y : Fin n → ℝ) :
    rotCLM i j y = y i • (Pi.single j (1 : ℝ) : Fin n → ℝ) - y j • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
  simp [rotCLM]

/-- **The flat FLRW form from the spatial translations and rotations as Killing fields.** -/
theorem flat_flrw_of_killing (g : NondegMetric 𝓘(ℝ, Fin 4 → ℝ) (Fin 4 → ℝ))
    (hdiff : ∀ μ ν, Differentiable ℝ (metricComp g μ ν))
    (htrans : ∀ k : Fin 4, k ≠ 0 → ∀ x μ ν,
      lieDerivMetric g (affField 0 (Pi.single k 1)) (basisField 4 μ) (basisField 4 ν) x = 0)
    (hrot : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ x μ ν,
      lieDerivMetric g (affField (rotCLM i j) 0) (basisField 4 μ) (basisField 4 ν) x = 0) :
    ∃ b a : ℝ → ℝ, ∀ x, metricComp g 0 0 x = b (x 0) ∧ (∀ k : Fin 4, k ≠ 0 → metricComp g 0 k x = 0) ∧
      (∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → metricComp g i j x = if i = j then a (x 0) else 0) := by
  have hsymm : ∀ μ ν x, metricComp g μ ν x = metricComp g ν μ x := fun μ ν x => g.symm x _ _
  have hA : ∀ μ ν x, ∀ k : Fin 4, k ≠ 0 → fderiv ℝ (metricComp g μ ν) x (Pi.single k 1) = 0 := by
    intro μ ν x k hk
    have := htrans k hk x μ ν
    rw [lieDerivMetric_affField_basis] at this
    simp only [ContinuousLinearMap.zero_apply, zero_add, g_zero_left, g_zero_right, add_zero] at this
    exact this
  have hB : ∀ μ ν x, metricComp g μ ν x = metricComp g μ ν (Pi.single 0 (x 0)) :=
    fun μ ν x => spatial_const (hdiff μ ν) (fun z k hk => hA μ ν z k hk) x
  -- the rotation relations at the point `(t, 0, 0, 0)`
  have hR : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ t μ ν,
      ((if i = μ then metricComp g j ν (Pi.single 0 t) else 0) - (if j = μ then metricComp g i ν (Pi.single 0 t) else 0)) +
      ((if i = ν then metricComp g μ j (Pi.single 0 t) else 0) - (if j = ν then metricComp g μ i (Pi.single 0 t) else 0)) = 0 := by
    intro i j hi hj hij t μ ν
    have h := hrot i j hi hj hij (Pi.single 0 t) μ ν
    rw [lieDerivMetric_affField_basis] at h
    have hz : rotCLM i j ((Pi.single 0 t : Fin 4 → ℝ)) = 0 := by
      rw [rotCLM_apply]; simp [Pi.single_apply, hi.symm, hj.symm]
    simp only [hz, zero_add, g_zero_left, g_zero_right, map_zero, ContinuousLinearMap.zero_apply] at h
    rw [rotCLM_apply, rotCLM_apply] at h
    simp only [g_sub_left, g_sub_right, g_smul_left, g_smul_right, Pi.single_apply] at h
    unfold metricComp
    split_ifs at h ⊢ <;> linarith
  -- consequences of the rotation relations
  have hdiag : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ t,
      metricComp g j j (Pi.single 0 t) = metricComp g i i (Pi.single 0 t) := by
    intro i j hi hj hij t
    have := hR i j hi hj hij t i j
    simp [hij, Ne.symm hij] at this
    linarith
  have hoff : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ t, metricComp g i j (Pi.single 0 t) = 0 := by
    intro i j hi hj hij t
    have := hR i j hi hj hij t i i
    simp [Ne.symm hij] at this
    have := hsymm j i (Pi.single 0 t)
    linarith
  have h0 : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ t, metricComp g 0 j (Pi.single 0 t) = 0 := by
    intro i j hi hj hij t
    have := hR i j hi hj hij t 0 i
    simp [hi, hj, hij, Ne.symm hij] at this
    exact this
  refine ⟨fun t => metricComp g 0 0 (Pi.single 0 t), fun t => metricComp g 1 1 (Pi.single 0 t), fun x => ?_⟩
  refine ⟨hB 0 0 x, fun k hk => ?_, fun i j hi hj => ?_⟩
  · rw [hB 0 k x]
    fin_cases k
    · exact absurd rfl hk
    · exact h0 2 1 (by decide) (by decide) (by decide) _
    · exact h0 1 2 (by decide) (by decide) (by decide) _
    · exact h0 1 3 (by decide) (by decide) (by decide) _
  · rw [hB i j x]
    fin_cases i <;> fin_cases j <;> simp at hi hj ⊢
    · exact hoff 1 2 (by decide) (by decide) (by decide) _
    · exact hoff 1 3 (by decide) (by decide) (by decide) _
    · exact hoff 2 1 (by decide) (by decide) (by decide) _
    · exact (hdiag 1 2 (by decide) (by decide) (by decide) _)
    · exact hoff 2 3 (by decide) (by decide) (by decide) _
    · exact hoff 3 1 (by decide) (by decide) (by decide) _
    · exact hoff 3 2 (by decide) (by decide) (by decide) _
    · exact (hdiag 1 3 (by decide) (by decide) (by decide) _)

end Lightlike
