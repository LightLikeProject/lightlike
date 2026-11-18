import Lightlike.OperatorAlgebras.ResolventIdentity
import Lightlike.OperatorAlgebras.BoundedGroup

/-!
# The strong limit of the approximating unitary groups

Helper lemmas for the task `T-OP1-P2` (Stone's theorem, existence). Let `A` be self-adjoint and
`U_n t = exp (i t A_n)` (`BoundedGroup.lean`) with the commuting bounded self-adjoint approximants `A_n`
(`Yosida.lean`). For `x` in the domain, `‖U_n t x - U_m t x‖ ≤ |t| ‖A_n x - A_m x‖`, and `A_n x` converges, so
`U_n t x` is Cauchy; by density and isometry `U_n t y` is Cauchy for every `y`, and its limit is a unitary
group `U t` with `‖U_n t x - U t x‖ ≤ |t| ‖A_n x - A x‖` on the domain.
-/

open scoped InnerProductSpace LinearPMap Topology
open Filter

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- The approximating unitary `U_n t = exp (i t A_n)`. -/
noncomputable def Un (hA : IsSelfAdjoint A) (n : ℕ) (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  bdUnitary (approx_isSelfAdjoint hA n) t

lemma Un_apply (hA : IsSelfAdjoint A) (n : ℕ) (t : ℝ) (y : H) :
    Un hA n t y = bdU (approx hA n) t y := rfl

/-- **The Cauchy estimate** for the approximating unitaries on the domain. -/
lemma Un_cauchy (hA : IsSelfAdjoint A) (n m : ℕ) (t : ℝ) (x : A.domain) :
    ‖Un hA n t (x : H) - Un hA m t (x : H)‖ ≤ |t| * ‖approx hA n (x : H) - approx hA m (x : H)‖ := by
  have := bdU_cauchy (approx_isSelfAdjoint hA n) (approx_isSelfAdjoint hA m) (approx_commute hA n m) t (x : H)
  simpa [Un_apply] using this

/-- For `x` in the domain, `U_n t x` is a Cauchy sequence. -/
lemma cauchySeq_Un_domain (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    CauchySeq fun n => Un hA n t (x : H) := by
  have hc : CauchySeq fun n => approx hA n (x : H) := (approx_tendsto hA x).cauchySeq
  rw [Metric.cauchySeq_iff] at hc ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε / (|t| + 1)) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := Un_cauchy hA m n t x
  have h2 : ‖approx hA m (x : H) - approx hA n (x : H)‖ < ε / (|t| + 1) := by
    have := hN m hm n hn
    rwa [dist_eq_norm] at this
  rw [dist_eq_norm]
  calc ‖Un hA m t (x : H) - Un hA n t (x : H)‖ ≤ |t| * ‖approx hA m (x : H) - approx hA n (x : H)‖ := h1
    _ ≤ |t| * (ε / (|t| + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg t]

/-- A sequence of isometries that is Cauchy on a dense set is Cauchy everywhere. -/
lemma cauchySeq_of_dense_isometries {V : ℕ → H ≃ₗᵢ[ℂ] H} {D : Set H} (hd : Dense D)
    (hD : ∀ y ∈ D, CauchySeq fun n => V n y) (y : H) : CauchySeq fun n => V n y := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨y', hy', hdist⟩ := hd.exists_dist_lt y (show 0 < ε / 3 by positivity)
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.1 (hD y' hy')) (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := hN m hm n hn
  have h2 : dist (V m y) (V m y') = dist y y' := (V m).dist_map y y'
  have h3 : dist (V n y') (V n y) = dist y' y := (V n).dist_map y' y
  have h4 := dist_triangle (V m y) (V m y') (V n y)
  have h5 := dist_triangle (V m y') (V n y') (V n y)
  rw [dist_comm y' y] at h3
  linarith

/-- For every `y`, `U_n t y` is a Cauchy sequence. -/
lemma cauchySeq_Un (hA : IsSelfAdjoint A) (t : ℝ) (y : H) : CauchySeq fun n => Un hA n t y :=
  cauchySeq_of_dense_isometries (V := fun n => Un hA n t) hA.dense_domain
    (fun w hw => cauchySeq_Un_domain hA t ⟨w, hw⟩) y

/-- **The limit of the approximating unitary groups**: `U t y = lim U_n t y`. -/
noncomputable def Ulim (hA : IsSelfAdjoint A) (t : ℝ) (y : H) : H :=
  Classical.choose (cauchySeq_tendsto_of_complete (cauchySeq_Un hA t y))

lemma tendsto_Ulim (hA : IsSelfAdjoint A) (t : ℝ) (y : H) :
    Tendsto (fun n => Un hA n t y) atTop (𝓝 (Ulim hA t y)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_Un hA t y))

lemma Ulim_zero (hA : IsSelfAdjoint A) (y : H) : Ulim hA 0 y = y := by
  have h := tendsto_Ulim hA 0 y
  have : (fun n => Un hA n 0 y) = fun _ => y := by
    funext n; simp [Un_apply, bdU_zero]
  rw [this] at h
  exact tendsto_nhds_unique h tendsto_const_nhds |>.symm ▸ rfl

lemma Ulim_add (hA : IsSelfAdjoint A) (t : ℝ) (y w : H) :
    Ulim hA t (y + w) = Ulim hA t y + Ulim hA t w := by
  have h := (tendsto_Ulim hA t y).add (tendsto_Ulim hA t w)
  have h2 := tendsto_Ulim hA t (y + w)
  simp only [map_add] at h2
  exact tendsto_nhds_unique h2 h

lemma Ulim_smul (hA : IsSelfAdjoint A) (t : ℝ) (c : ℂ) (y : H) :
    Ulim hA t (c • y) = c • Ulim hA t y := by
  have h := (tendsto_Ulim hA t y).const_smul c
  have h2 := tendsto_Ulim hA t (c • y)
  simp only [map_smul] at h2
  exact tendsto_nhds_unique h2 h

lemma norm_Ulim (hA : IsSelfAdjoint A) (t : ℝ) (y : H) : ‖Ulim hA t y‖ = ‖y‖ := by
  have h := (tendsto_Ulim hA t y).norm
  have : (fun n => ‖Un hA n t y‖) = fun _ => ‖y‖ := by
    funext n; exact (Un hA n t).norm_map y
  rw [this] at h
  exact (tendsto_nhds_unique h tendsto_const_nhds)

lemma Ulim_add_time (hA : IsSelfAdjoint A) (s t : ℝ) (y : H) :
    Ulim hA (s + t) y = Ulim hA s (Ulim hA t y) := by
  -- `U_n s (U_n t y) → U s (U t y)`
  have h1 : Tendsto (fun n => Un hA n (s + t) y) atTop (𝓝 (Ulim hA s (Ulim hA t y))) := by
    have e : ∀ n, Un hA n (s + t) y = Un hA n s (Un hA n t y) := fun n => by
      simp only [Un_apply, bdU_add, ContinuousLinearMap.mul_apply]
    simp only [e]
    -- split `U_n s (U_n t y) - U s (U t y) = U_n s (U_n t y - U t y) + (U_n s - U s) (U t y)`
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hA1 : Tendsto (fun n => ‖Un hA n t y - Ulim hA t y‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_Ulim hA t y)
    have hA2 : Tendsto (fun n => ‖Un hA n s (Ulim hA t y) - Ulim hA s (Ulim hA t y)‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_Ulim hA s (Ulim hA t y))
    have hsum := hA1.add hA2
    rw [add_zero] at hsum
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum
    have : Un hA n s (Un hA n t y) - Ulim hA s (Ulim hA t y) =
        Un hA n s (Un hA n t y - Ulim hA t y) + (Un hA n s (Ulim hA t y) - Ulim hA s (Ulim hA t y)) := by
      rw [map_sub]; abel
    rw [this]
    calc ‖Un hA n s (Un hA n t y - Ulim hA t y) + (Un hA n s (Ulim hA t y) - Ulim hA s (Ulim hA t y))‖
        ≤ ‖Un hA n s (Un hA n t y - Ulim hA t y)‖ + ‖Un hA n s (Ulim hA t y) - Ulim hA s (Ulim hA t y)‖ :=
          norm_add_le _ _
      _ = ‖Un hA n t y - Ulim hA t y‖ + ‖Un hA n s (Ulim hA t y) - Ulim hA s (Ulim hA t y)‖ := by
          rw [(Un hA n s).norm_map]
  exact tendsto_nhds_unique (tendsto_Ulim hA (s + t) y) h1

end Lightlike.OperatorAlgebras
