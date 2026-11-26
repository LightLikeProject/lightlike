import Lightlike.Spacetime.PenroseSingularity.JacobiUnique
import Lightlike.Spacetime.PenroseSingularity.StartIdentity

/-!
# The focal point in a chart (G1-012, step D4)

Chart-level facts about a family of Jacobi fields `J_i` along a null geodesic, orthogonal to its velocity: finite
combinations are Jacobi fields, their covariant derivatives are orthogonal to the velocity, and at a first
degenerate time the combination `P̂` has positive norm.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

open Lightlike.Geodesic

variable {n m : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The zero field is a Jacobi field. -/
theorem IsJacobiOn.zero {γ w : ℝ → Fin n → ℝ} {I : Set ℝ} (hγ : IsGeodesicOn g γ w I) :
    IsJacobiOn g γ w (fun _ => 0) (fun _ => 0) I where
  geodesic := hγ
  deriv_field t ht := by
    simpa [gammaApply_zero_right] using hasDerivAt_const t (0 : Fin n → ℝ)
  deriv_cov t ht := by
    have hr : riemannApply g (γ t) (w t) (0 : Fin n → ℝ) = 0 := by funext i; simp [riemannApply]
    simpa [gammaApply_zero_right, hr] using hasDerivAt_const t (0 : Fin n → ℝ)

/-- A finite combination of Jacobi fields is a Jacobi field. -/
theorem IsJacobiOn.sum_smul {γ w : ℝ → Fin n → ℝ} {I : Set ℝ} {J P : Fin m → ℝ → Fin n → ℝ}
    (hγ : IsGeodesicOn g γ w I) (h : ∀ i, IsJacobiOn g γ w (J i) (P i) I) (v : Fin m → ℝ) :
    IsJacobiOn g γ w (fun t => ∑ i, v i • J i t) (fun t => ∑ i, v i • P i t) I := by
  have key : ∀ s : Finset (Fin m), IsJacobiOn g γ w (fun t => ∑ i ∈ s, v i • J i t)
      (fun t => ∑ i ∈ s, v i • P i t) I := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using IsJacobiOn.zero hγ
    | insert i s hi ih =>
      have := IsJacobiOn.add (IsJacobiOn.smul (h i) (v i)) ih
      convert this using 1 <;> funext t <;> simp [Finset.sum_insert hi]
  exact key _

/-- **The covariant derivative of an orthogonal Jacobi field is orthogonal to the velocity.** -/
theorem IsJacobiOn.pair_P_w (hg : Lightlike.IsCoordMetric g U) {γ w J P : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hJ : IsJacobiOn g γ w J P I) (hIo : IsOpen I) (hγU : ∀ t ∈ I, γ t ∈ U)
    (hperp : ∀ t ∈ I, gpairAt g (γ t) (w t) (J t) = 0) {t : ℝ} (ht : t ∈ I) :
    gpairAt g (γ t) (P t) (w t) = 0 := by
  have hγ : HasDerivAt γ (w t) t := hJ.geodesic.1 t ht
  have hw : HasDerivAt w (accel g (γ t) (w t)) t := hJ.geodesic.2 t ht
  have h := hasDerivAt_gpair hg hγ (hγU t ht) hw (hJ.deriv_field t ht)
  have h0 : HasDerivAt (fun s => gpairAt g (γ s) (w s) (J s)) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
      (by filter_upwards [hIo.mem_nhds ht] with s hs using hperp s hs)
  have := h.unique h0
  rw [covDAlong_eq_add, covDAlong_eq_add, accel_eq_neg_gammaApply] at this
  have e1 : (-gammaApply g (γ t) (w t) (w t) + gammaApply g (γ t) (w t) (w t)) = 0 := by abel
  have e2 : (P t - gammaApply g (γ t) (w t) (J t) + gammaApply g (γ t) (w t) (J t)) = P t := by abel
  rw [e1, e2] at this
  have h3 : gpairAt g (γ t) 0 (J t) = 0 := by simp [gpairAt]
  rw [h3, zero_add] at this
  rw [gpairAt_symm hg (hγU t ht)]
  exact this

/-- **At a first degenerate time the corrected covariant derivative has positive norm.** -/
theorem chart_focal_pos (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hIo : IsOpen I) {a : ℝ} (ha : a ∈ I) (ha0 : 0 < a) (hγU : ∀ t ∈ I, γ t ∈ U)
    {J P : Fin m → ℝ → Fin n → ℝ} (hγ : IsGeodesicOn g γ w I)
    (hJ : ∀ i, IsJacobiOn g γ w (J i) (P i) I)
    (hnull : ∀ t ∈ I, gpairAt g (γ t) (w t) (w t) = 0)
    (hperp : ∀ t ∈ I, ∀ i, gpairAt g (γ t) (w t) (J i t) = 0)
    (hnn : ∀ z, gpairAt g (γ a) z (w a) = 0 → 0 ≤ gpairAt g (γ a) z z)
    (hpar : ∀ z, gpairAt g (γ a) z (w a) = 0 → gpairAt g (γ a) z z = 0 → ∃ c' : ℝ, z = c' • w a)
    (v : Fin m → ℝ) {c : ℝ} (hca : ∑ i, v i • J i a = c • w a)
    (hQpos : ∀ᶠ t in 𝓝[<] a, 0 < gpairAt g (γ t) (∑ i, v i • J i t) (∑ i, v i • J i t)) :
    0 < gpairAt g (γ a) (∑ i, v i • P i a - (c / a) • w a) (∑ i, v i • P i a - (c / a) • w a) := by
  have hxa := hγU a ha
  -- the combination is a Jacobi field orthogonal to the velocity
  have hsum := IsJacobiOn.sum_smul hγ hJ v
  have hperpv : ∀ t ∈ I, gpairAt g (γ t) (w t) (∑ i, v i • J i t) = 0 := by
    intro t ht
    have := gpairAt_sum_smul_left g (γ t) (w t) v (fun i => J i t)
    rw [gpairAt_symm hg (hγU t ht), this]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [gpairAt_symm hg (hγU t ht), hperp t ht i]; ring
  have hPw : gpairAt g (γ a) (∑ i, v i • P i a) (w a) = 0 := by
    have hs := IsJacobiOn.pair_P_w hg hsum hIo hγU hperpv ha
    simpa using hs
  have hPhat : gpairAt g (γ a) (∑ i, v i • P i a - (c / a) • w a) (w a) = 0 := by
    have hsm : gpairAt g (γ a) ((c / a) • w a) (w a) = (c / a) * gpairAt g (γ a) (w a) (w a) := by
      have h := gpairAt_add_smul_left g (γ a) 0 (w a) (w a) (c / a)
      have h0 : gpairAt g (γ a) 0 (w a) = 0 := by simp [gpairAt]
      simpa [h0] using h
    rw [gpairAt_sub_left, hsm, hPw, hnull a ha]; ring
  by_contra hcon
  have hle : gpairAt g (γ a) (∑ i, v i • P i a - (c / a) • w a) (∑ i, v i • P i a - (c / a) • w a) ≤ 0 :=
    not_lt.1 hcon
  have hzero := le_antisymm hle (hnn _ hPhat)
  obtain ⟨c', hc'⟩ := hpar _ hPhat hzero
  -- the corrected field is a Jacobi field vanishing at `a`
  have hE := IsJacobiOn.add hsum (IsJacobiOn.smul (IsJacobiOn.affine_w hγ 0 (c / a)) (-1))
  have hEa : (∑ i, v i • J i a) + (-1 : ℝ) • ((0 + c / a * a) • w a) = 0 := by
    rw [hca, show (0 : ℝ) + c / a * a = c by field_simp; ring, neg_one_smul]; abel
  have hPa : (∑ i, v i • P i a) + (-1 : ℝ) • ((c / a) • w a) = c' • w a := by
    rw [← hc']; simp [sub_eq_add_neg]
  have hE0 := IsJacobiOn.eventually_eq_smul_w hg (J := fun t => (∑ i, v i • J i t) +
      (-1 : ℝ) • ((0 + c / a * t) • w t)) hE hIo ha hγU hEa hPa
  have hnear : ∀ᶠ t in 𝓝 a, gpairAt g (γ t) (∑ i, v i • J i t) (∑ i, v i • J i t) = 0 := by
    filter_upwards [hE0, hIo.mem_nhds ha] with t ht htI
    have hJt : ∑ i, v i • J i t = ((0 + c / a * t) + c' * (t - a)) • w t := by
      have h1 : (∑ i, v i • J i t) + (-1 : ℝ) • ((0 + c / a * t) • w t) = (c' * (t - a)) • w t := ht
      have h2 : ∑ i, v i • J i t = (c' * (t - a)) • w t + (0 + c / a * t) • w t := by
        rw [← h1]; simp
      rw [h2, ← add_smul]; congr 1; ring
    have hsl : ∀ (r : ℝ) (u v : Fin n → ℝ), gpairAt g (γ t) (r • u) v = r * gpairAt g (γ t) u v := by
      intro r u v
      have h0 : gpairAt g (γ t) 0 v = 0 := by simp [gpairAt]
      have h1 := gpairAt_add_smul_left g (γ t) 0 u v r
      simpa [h0] using h1
    have hsm : ∀ r : ℝ, gpairAt g (γ t) (r • w t) (r • w t) = r * r * gpairAt g (γ t) (w t) (w t) := by
      intro r
      rw [hsl, gpairAt_symm hg (hγU t htI) (w t) (r • w t), hsl]; ring
    rw [hJt, hsm, hnull t htI]; ring
  obtain ⟨t, ht1, ht2⟩ := (hQpos.and (nhdsWithin_le_nhds hnear)).exists
  linarith

end Lightlike.Penrose
