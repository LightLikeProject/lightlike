import Lightlike.Cosmology.FLRW
import Lightlike.Spacetime.RiccatiFocusing

/-!
# The expansion of comoving congruences and the focusing of geodesics (GE3, coordinate stage)

Kar and SenGupta (gr-qc/0611123), eq. (12): for a timelike geodesic congruence `v` in dimension four with expansion
`Θ = ∇ₐvᵃ`, shear `σ` and rotation `ω`, `dΘ/dλ + Θ²/3 + σ² - ω² = -Rₐᵦ vᵃ vᵇ` (the Raychaudhuri equation), and
eq. (16): convergence occurs if `Rₐᵦ vᵃ vᵇ + σ² - ω² ≥ 0`.

* the focusing lemma `Lightlike.focusing` (`Lightlike/Spacetime/RiccatiFocusing.lean`): if `Θ' ≤ -Θ²/m` on `[0, L)` (`m > 0`) and
  `Θ(0) < 0`, then `L ≤ m/|Θ(0)|`: the expansion reaches `-∞` within affine time `m/|Θ(0)|` (with `m = 3`, `σ = ω = 0` and
  `Rₐᵦ vᵃ vᵇ ≥ 0` in (12));
* `flrw_comoving_covDeriv`, `flrw_comoving_geodesic`, `flrw_comoving_expansion`: for the comoving congruence `u = ∂_t` of
  the FLRW metric, `∇ⱼuⁱ = H δⁱⱼ` on spatial indices and `0` otherwise (no shear, no rotation), `∇ᵤu = 0`, and
  **`Θ = 3H = 3ȧ/a`** in closed form;
* `flrw_raychaudhuri`: along it `dΘ/dt + Θ²/3 = -R₀₀` (Raychaudhuri's equation with `σ = ω = 0`);
* `minkowski_comoving_expansion`: in Minkowski space (`a = 1`, `k = 0`) the expansion is `0`;
* `deSitter_expansion`, `deSitter_no_focusing`: for de Sitter (`a = e^{Ht}`) the expansion is the constant `3H`, never
  `-∞`, while `R₀₀ = -3H² < 0` violates the convergence condition: a congruence in a spacetime violating the energy
  condition that does not focus.

**Limits.** Coordinates on the FLRW chart and constant (comoving) fields; the Raychaudhuri equation for a general geodesic
congruence on a manifold, and the exponential map, are not here.
-/

open Set Filter Topology

namespace Lightlike
namespace Cosmology

/-- `∇ⱼ vⁱ = Σₗ Γⁱⱼₗ vˡ` for a constant field `v`. -/
noncomputable def covConst (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) (i j : Fin 4) (x : Fin 4 → ℝ) :
    ℝ :=
  ∑ l, christoffel g i j l x * v l

/-- The expansion `Θ = ∇ᵢ vⁱ` of a constant field `v`. -/
noncomputable def expansionConst (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ i, covConst g v i i x

section FLRW

variable {a : ℝ → ℝ} {k : ℝ} {x : Fin 4 → ℝ}

/-- **The comoving congruence of FLRW**: `∇ⱼ uⁱ = H δⁱⱼ` on spatial indices, `0` otherwise, for `u = ∂_t`. -/
theorem flrw_comoving_covDeriv (ha : DifferentiableAt ℝ a (x 0)) (hpos : a (x 0) ≠ 0) (hD : Dn k x ≠ 0)
    (i j : Fin 4) :
    covConst (flrwMetric a k) (Pi.single 0 1) i j x = if i ≠ 0 ∧ i = j then Hf a x else 0 := by
  unfold covConst
  rw [Finset.sum_eq_single 0 (fun l _ hl => by simp [hl]) (by simp)]
  rw [christoffel_flrw ha hpos hD]
  unfold Γf
  by_cases hi : i = 0
  · subst hi; simp
  · by_cases hj : j = 0
    · subst hj; simp [hi, Ne.symm hi]
    · simp [hi, hj, eq_comm]

/-- The comoving observers are geodesic: `uʲ ∇ⱼ uⁱ = 0`. -/
theorem flrw_comoving_geodesic (ha : DifferentiableAt ℝ a (x 0)) (hpos : a (x 0) ≠ 0) (hD : Dn k x ≠ 0)
    (i : Fin 4) : ∑ j, (Pi.single 0 1 : Fin 4 → ℝ) j * covConst (flrwMetric a k) (Pi.single 0 1) i j x = 0 := by
  rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (by simp)]
  rw [flrw_comoving_covDeriv ha hpos hD]
  simp

/-- **The expansion of the comoving congruence is `Θ = 3H = 3ȧ/a`.** -/
theorem flrw_comoving_expansion (ha : DifferentiableAt ℝ a (x 0)) (hpos : a (x 0) ≠ 0) (hD : Dn k x ≠ 0) :
    expansionConst (flrwMetric a k) (Pi.single 0 1) x = 3 * (deriv a (x 0) / a (x 0)) := by
  unfold expansionConst
  simp only [flrw_comoving_covDeriv ha hpos hD, Fin.sum_univ_four]
  simp [Hf]
  ring

/-- **Raychaudhuri's equation along the comoving congruence**: with `Θ(t) = 3ȧ/a`, `dΘ/dt + Θ²/3 = -R₀₀`. -/
theorem flrw_raychaudhuri
    (hnb : ∀ᶠ y in nhds x, DifferentiableAt ℝ a (y 0) ∧ a (y 0) ≠ 0 ∧ Dn k y ≠ 0)
    (ha' : DifferentiableAt ℝ (deriv a) (x 0)) :
    HasDerivAt (fun t => 3 * (deriv a t / a t))
        (3 * (deriv (deriv a) (x 0) / a (x 0) - (deriv a (x 0) / a (x 0)) ^ 2)) (x 0) ∧
      3 * (deriv (deriv a) (x 0) / a (x 0) - (deriv a (x 0) / a (x 0)) ^ 2) +
          (3 * (deriv a (x 0) / a (x 0))) ^ 2 / 3 = -ricci (flrwMetric a k) 0 0 x := by
  obtain ⟨ha, hpos, hD⟩ := hnb.self_of_nhds
  refine ⟨?_, ?_⟩
  · have h1 := (ha'.hasDerivAt.div ha.hasDerivAt hpos).const_mul 3
    convert h1 using 1
    field_simp
  · rw [ricci_flrw hnb ha' 0 0]
    simp
    field_simp
    ring

end FLRW

/-- **Minkowski space**: the expansion of the comoving congruence vanishes (`a = 1`, `k = 0`). -/
theorem minkowski_comoving_expansion (x : Fin 4 → ℝ) :
    expansionConst (flrwMetric (fun _ => 1) 0) (Pi.single 0 1) x = 0 := by
  rw [flrw_comoving_expansion (differentiableAt_const _) one_ne_zero (by simp [Dn])]
  simp

/-- **de Sitter does not focus**: for `a = e^{Ht}`, `k = 0`, the expansion of the comoving congruence is the constant `3H`
(never `-∞`), while `R₀₀ = -3H²`, so the convergence condition `R(u, u) ≥ 0` fails for `H ≠ 0`. -/
theorem deSitter_no_focusing (H : ℝ) (x : Fin 4 → ℝ) :
    expansionConst (flrwMetric (fun t => Real.exp (H * t)) 0) (Pi.single 0 1) x = 3 * H ∧
      ricci (flrwMetric (fun t => Real.exp (H * t)) 0) 0 0 x = -3 * H ^ 2 := by
  have hd : ∀ t, HasDerivAt (fun t => Real.exp (H * t)) (H * Real.exp (H * t)) t := fun t => by
    have := ((hasDerivAt_id t).const_mul H).exp
    convert this using 1
    all_goals first | rfl | (simp only [id]; ring)
  have hderiv : deriv (fun t => Real.exp (H * t)) = fun t => H * Real.exp (H * t) := funext fun t => (hd t).deriv
  have hD : ∀ y : Fin 4 → ℝ, Dn 0 y ≠ 0 := fun y => by simp [Dn]
  refine ⟨?_, ?_⟩
  · rw [flrw_comoving_expansion (hd _).differentiableAt (Real.exp_pos _).ne' (hD x), hderiv]
    field_simp
  · have hnb : ∀ᶠ y in nhds x, DifferentiableAt ℝ (fun t => Real.exp (H * t)) (y 0) ∧
        Real.exp (H * y 0) ≠ 0 ∧ Dn 0 y ≠ 0 :=
      Filter.Eventually.of_forall fun y => ⟨(hd _).differentiableAt, (Real.exp_pos _).ne', hD y⟩
    have hdd : HasDerivAt (fun t => H * Real.exp (H * t)) (H * (H * Real.exp (H * x 0))) (x 0) :=
      (hd (x 0)).const_mul H
    have ha' : DifferentiableAt ℝ (deriv fun t => Real.exp (H * t)) (x 0) := by
      rw [hderiv]; exact hdd.differentiableAt
    rw [ricci_flrw hnb ha' 0 0]
    simp only [and_self, ite_true]
    rw [hderiv, hdd.deriv]
    field_simp

end Cosmology
end Lightlike
