import Lightlike.Spacetime.PenroseSingularity.JacobiCompat
import Lightlike.Spacetime.PenroseSingularity.JacobiGeom
import Lightlike.Spacetime.PenroseSingularity.IndexForm
import Lightlike.Spacetime.PenroseSingularity.JacobiAffine

/-!
# The second-order start identity (G1-012, step D4)

Along a curve `x (s)` in a surface with a field `u (s)` normal to it (`g(x', u) = 0`), differentiating gives
`g(x'' + Γ(x', x'), u) = - g(x', u' + Γ(x', u))`.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **Differentiating the normality** `g(x', u) = 0`. -/
theorem start_identity (hg : Lightlike.IsCoordMetric g U) {x x1 u : ℝ → Fin n → ℝ} {x2 u1 : Fin n → ℝ}
    (hx : HasDerivAt x (x1 0) 0) (hx1 : HasDerivAt x1 x2 0) (hu : HasDerivAt u u1 0) (hxU : x 0 ∈ U)
    (hperp : ∀ᶠ s in 𝓝 (0 : ℝ), gpairAt g (x s) (x1 s) (u s) = 0) :
    gpairAt g (x 0) (x2 + Lightlike.Geodesic.gammaApply g (x 0) (x1 0) (x1 0)) (u 0) =
      -gpairAt g (x 0) (x1 0) (u1 + Lightlike.Geodesic.gammaApply g (x 0) (x1 0) (u 0)) := by
  have h := hasDerivAt_gpair hg hx hxU hx1 hu
  have h0 : HasDerivAt (fun s => gpairAt g (x s) (x1 s) (u s)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hperp
  have := h.unique h0
  rw [covDAlong_eq_add, covDAlong_eq_add] at this
  linarith

/-- The Christoffel contraction is linear in the second slot over finite combinations. -/
theorem gammaApply_sum_smul_right {m : ℕ} (x v : Fin n → ℝ) (c : Fin m → ℝ) (b : Fin m → Fin n → ℝ) :
    Lightlike.Geodesic.gammaApply g x v (∑ i, c i • b i) = ∑ i, c i • Lightlike.Geodesic.gammaApply g x v (b i) := by
  have key : ∀ s : Finset (Fin m), Lightlike.Geodesic.gammaApply g x v (∑ i ∈ s, c i • b i) =
      ∑ i ∈ s, c i • Lightlike.Geodesic.gammaApply g x v (b i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => funext j; simp [Lightlike.Geodesic.gammaApply]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Lightlike.Geodesic.gammaApply_add_right, ih,
        Lightlike.Penrose.gammaApply_smul_right]
  exact key _

variable {m : ℕ}

/-- The pairing of a combination in the left slot. -/
theorem gpairAt_sum_smul_left (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x a : Fin n → ℝ)
    (c : Fin m → ℝ) (b : Fin m → Fin n → ℝ) :
    gpairAt g x (∑ i, c i • b i) a = ∑ i, c i * gpairAt g x (b i) a := by
  have key : ∀ s : Finset (Fin m), gpairAt g x (∑ i ∈ s, c i • b i) a = ∑ i ∈ s, c i * gpairAt g x (b i) a := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [gpairAt]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, add_comm (c i • b i), gpairAt_add_smul_left, ih, add_comm]
  exact key _


/-- **The start identity for a chart family.** For a `C³` chart family `H (t, σ)` of null geodesics with
`g(∂_t H, ∂_σ H) = 0`, Jacobi fields `J_i = ∂_{σ_i} H (·, σ₀)` with covariant derivatives `P_i`, and any direction
`v`, the curve `x (s) = H (0, σ₀ + s v)` satisfies
`g(x'' + Γ(x', x'), ∂_t H) = - g(x', P_v)` at `s = 0`, where `P_v = Σ v_i P_i`. -/
theorem chartFamily_start (hg : Lightlike.IsCoordMetric g U) {H : ℝ × (Fin m → ℝ) → Fin n → ℝ}
    {W : Set (ℝ × (Fin m → ℝ))} (hWo : IsOpen W) (hH : ContDiffOn ℝ 3 H W) {σ₀ : Fin m → ℝ}
    (h0 : ((0 : ℝ), σ₀) ∈ W) (hUW : ∀ q ∈ W, H q ∈ U)
    (hω : ∀ q ∈ W, ∀ j : Fin m, gpairAt g (H q) (fderiv ℝ H q (1, 0)) (fderiv ℝ H q (0, Pi.single j 1)) = 0)
    {P : Fin m → ℝ → Fin n → ℝ} {I : Set ℝ} (hI : (0 : ℝ) ∈ I) (hIo : IsOpen I)
    (hJ : ∀ i, Lightlike.Geodesic.IsJacobiOn g (fun s => H (s, σ₀)) (fun s => fderiv ℝ H (s, σ₀) (1, 0))
      (fun s => fderiv ℝ H (s, σ₀) (0, Pi.single i 1)) (P i) I)
    (v : Fin m → ℝ) :
    gpairAt g (H (0, σ₀))
      (fderiv ℝ (fderiv ℝ H) (0, σ₀) (0, v) (0, v) +
        Lightlike.Geodesic.gammaApply g (H (0, σ₀)) (fderiv ℝ H (0, σ₀) (0, v)) (fderiv ℝ H (0, σ₀) (0, v)))
      (fderiv ℝ H (0, σ₀) (1, 0)) =
    -gpairAt g (H (0, σ₀)) (fderiv ℝ H (0, σ₀) (0, v)) (∑ i, v i • P i 0) := by
  set q₀ : ℝ × (Fin m → ℝ) := (0, σ₀) with hq₀
  have hC : ∀ q ∈ W, ContDiffAt ℝ 3 H q := fun q hq => hH.contDiffAt (hWo.mem_nhds hq)
  have hd0 : DifferentiableAt ℝ H q₀ := (hC q₀ h0).differentiableAt (by simp)
  have hd1 : DifferentiableAt ℝ (fderiv ℝ H) q₀ :=
    ((hC q₀ h0).fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp)
  have hcurve : ∀ s : ℝ, HasDerivAt (fun r : ℝ => ((0 : ℝ), σ₀ + r • v)) ((0 : ℝ), v) s := fun s => by
    refine (hasDerivAt_const s (0 : ℝ)).prodMk ?_
    simpa using ((hasDerivAt_id s).smul_const v).const_add σ₀
  have hmemW : ∀ᶠ s in 𝓝 (0 : ℝ), (((0 : ℝ), σ₀ + s • v) : ℝ × (Fin m → ℝ)) ∈ W := by
    have hc : Continuous (fun r : ℝ => (((0 : ℝ), σ₀ + r • v) : ℝ × (Fin m → ℝ))) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hWo.mem_nhds h0)
  set x : ℝ → Fin n → ℝ := fun s => H ((0 : ℝ), σ₀ + s • v) with hx
  set x1 : ℝ → Fin n → ℝ := fun s => fderiv ℝ H ((0 : ℝ), σ₀ + s • v) (0, v) with hx1
  set u : ℝ → Fin n → ℝ := fun s => fderiv ℝ H ((0 : ℝ), σ₀ + s • v) (1, 0) with hu
  have hq00 : (((0 : ℝ), σ₀ + (0 : ℝ) • v) : ℝ × (Fin m → ℝ)) = q₀ := by simp [hq₀]
  have hxd : HasDerivAt x (x1 0) 0 := by
    have := hd0.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hcurve 0) hq00.symm
    have e : x1 0 = fderiv ℝ H q₀ (0, v) := by simp [hx1, hq₀]
    rw [e]; exact this
  have hx1d : HasDerivAt x1 (fderiv ℝ (fderiv ℝ H) q₀ (0, v) (0, v)) 0 := by
    have := hasDerivAt_fderiv_comp' (f := H) (q := fun r : ℝ => (((0 : ℝ), σ₀ + r • v) : ℝ × (Fin m → ℝ)))
      (r := 0) (by simpa [hq00] using hd1) (hcurve 0) (0, v)
    simpa [hx1, hq00] using this
  have hud : HasDerivAt u (fderiv ℝ (fderiv ℝ H) q₀ (0, v) (1, 0)) 0 := by
    have := hasDerivAt_fderiv_comp' (f := H) (q := fun r : ℝ => (((0 : ℝ), σ₀ + r • v) : ℝ × (Fin m → ℝ)))
      (r := 0) (by simpa [hq00] using hd1) (hcurve 0) (1, 0)
    simpa [hu, hq00] using this
  have hv : ((0 : ℝ), v) = ∑ i, v i • (((0 : ℝ), (Pi.single i (1 : ℝ) : Fin m → ℝ)) : ℝ × (Fin m → ℝ)) := by
    ext j <;> simp [Finset.sum_apply, Prod.fst_sum, Prod.snd_sum, Pi.single_apply]
  have hperp : ∀ᶠ s in 𝓝 (0 : ℝ), gpairAt g (x s) (x1 s) (u s) = 0 := by
    filter_upwards [hmemW] with s hs
    have hsum : x1 s = ∑ j, v j • fderiv ℝ H ((0 : ℝ), σ₀ + s • v) (0, Pi.single j 1) := by
      simp only [hx1]
      conv_lhs => rw [hv]
      simp only [map_sum, map_smul]
    show gpairAt g (H ((0 : ℝ), σ₀ + s • v)) (x1 s) (u s) = 0
    rw [hsum, gpairAt_sum_smul_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [gpairAt_symm hg (hUW _ hs), hω _ hs j]
    ring
  have e0 : x 0 = H q₀ := by simp [hx, hq₀]
  have e1 : x1 0 = fderiv ℝ H q₀ (0, v) := by simp [hx1, hq₀]
  have e2 : u 0 = fderiv ℝ H q₀ (1, 0) := by simp [hu, hq₀]
  have hxU0 : x 0 ∈ U := by rw [e0]; exact hUW _ h0
  have hmain := start_identity hg hxd hx1d hud hxU0 hperp
  -- the Jacobi fields and the symmetry of the mixed second derivative
  have hH2 : ContDiffAt ℝ 2 H q₀ := (hC q₀ h0).of_le (by norm_num)
  have hsymm := hH2.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hcurveT : HasDerivAt (fun r : ℝ => ((r, σ₀) : ℝ × (Fin m → ℝ))) ((1 : ℝ), (0 : Fin m → ℝ)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) σ₀)
  have hPi : ∀ i, P i 0 = fderiv ℝ (fderiv ℝ H) q₀ (0, Pi.single i 1) (1, 0) +
      Lightlike.Geodesic.gammaApply g (H q₀) (fderiv ℝ H q₀ (1, 0)) (fderiv ℝ H q₀ (0, Pi.single i 1)) := by
    intro i
    have h1 := (hJ i).deriv_field 0 hI
    have h2 := hasDerivAt_fderiv_comp' (f := H) (q := fun r : ℝ => ((r, σ₀) : ℝ × (Fin m → ℝ))) (r := 0)
      (by simpa using hd1) hcurveT (0, Pi.single i 1)
    have h3 := h1.unique (by simpa using h2)
    have e3 : fderiv ℝ (fderiv ℝ H) q₀ (1, 0) (0, Pi.single i 1) =
        fderiv ℝ (fderiv ℝ H) q₀ (0, Pi.single i 1) (1, 0) := hsymm _ _
    rw [e3] at h3
    have h4 : P i 0 = fderiv ℝ (fderiv ℝ H) q₀ (0, Pi.single i 1) (1, 0) +
        Lightlike.Geodesic.gammaApply g (H (0, σ₀)) (fderiv ℝ H (0, σ₀) (1, 0))
          (fderiv ℝ H (0, σ₀) (0, Pi.single i 1)) := by
      rw [← h3]; abel
    exact h4
  have hJ0 : fderiv ℝ H q₀ (0, v) = ∑ i, v i • fderiv ℝ H q₀ (0, Pi.single i 1) := by
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul]
  have hU1 : fderiv ℝ (fderiv ℝ H) q₀ (0, v) (1, 0) =
      ∑ i, v i • fderiv ℝ (fderiv ℝ H) q₀ (0, Pi.single i 1) (1, 0) := by
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply]
  have hsumP : ∑ i, v i • P i 0 = fderiv ℝ (fderiv ℝ H) q₀ (0, v) (1, 0) +
      Lightlike.Geodesic.gammaApply g (H q₀) (fderiv ℝ H q₀ (1, 0)) (fderiv ℝ H q₀ (0, v)) := by
    simp only [hPi, smul_add, Finset.sum_add_distrib]
    rw [hU1, hJ0, gammaApply_sum_smul_right]
  have hcomm := Lightlike.Geodesic.gammaApply_comm hg (hUW _ h0) (fderiv ℝ H q₀ (0, v)) (fderiv ℝ H q₀ (1, 0))
  rw [e0, e1, e2] at hmain
  rw [hsumP, ← hcomm]
  exact hmain

end Lightlike.Penrose
