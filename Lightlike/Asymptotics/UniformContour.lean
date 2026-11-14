import Lightlike.Asymptotics.Level
import Lightlike.Asymptotics.Homogeneity

/-!
# Strict landings and continuity of the phase in the edge lengths

Two ingredients of the uniformity in `λ` of the steepest-descent proof of
`RacahSumAsymptotics`. For integer spins `j` the lengths are `ℓ = λ m_λ` with
`m_λ = j + 1/(2λ) → j` (`lengths_eq_smul`, `tendsto_lengthsDir`), and the exponent of Racah's
kernel is `λ ψ_{m_λ}` in the rescaled variable `x = σ/λ` (`phaseC_faceSum_smul`). The descent
contour is built once, for `j`, and used for every large `λ`.

**Strict landings.** The descent paths of `j` land on the real axis at points `x₁ ≤ A_max` and
`x₂ ≥ B_min` (`IsEuclid.landing_sides`). Both inequalities are in fact strict, and `x₁ > 0`
(`IsEuclid.landing_sides_strict`):

* at `A_max` and at `B_min`, `bdry` takes the values `π A_max` and `π B_min`, while the level
  lies strictly between them (`IsEuclid.pi_faceSum_lt_level`);
* on `(−∞, 0]`, `bdry u = π (Σᵢ Aᵢ − 2u) ≥ π Σᵢ Aᵢ` (`bdry_of_nonpos`), and `Σᵢ Aᵢ = Σₖ Bₖ`
  exceeds `B_min`, so no landing lies there.

This is what the rescaled contour needs. In the variable `z = λx − 3/2` of Racah's kernel, the
contour identity (`racahSum_eq_im_primitive`) needs end points left of a face sum `aᵢ = λAᵢ(j)`
and right of a quadrilateral sum `bₖ = λBₖ(j)`, and the kernel bound
(`exists_norm_racahKernel_le_kernelExp`) holds near the real axis where
`−3/2 ≤ Re z ≤ aᵢ − ½` or `Re z ≥ bₖ + ½`. Near `x₁ ∈ (0, A_max)` and `x₂ > B_min` both hold for
all large `λ`.

**Continuity in the lengths.** The map `(m, z) ↦ ψ_m(z) = phaseC (faceSum m) (quadSum m) z` is
continuous on `ℝ⁶ × H̄`, with `H̄` the closed upper half-plane (`continuousOn_phaseC_lengths`).
Hence `ψ_m → ψ_j` uniformly on every compact subset of `H̄` as `m → j`
(`eventually_norm_phaseC_sub_lt`), in particular along `m = m_λ`
(`eventually_norm_phaseC_lengthsDir_sub_lt`). The saddle point `s_m` depends continuously on
`m` on the open set of Euclidean tetrahedra (`continuousOn_saddle`), and so does `ψ_m(s_m)`,
whose real part is the exponential rate `D(m)` and whose imaginary part is the Regge action
(`continuousOn_phaseC_saddle`, `tendsto_phaseC_saddle_lengthsDir`).

## Main results

* `bdry_of_nonpos`, `pos_lt_of_bdry_eq`, `lt_of_bdry_eq_right`: the real-axis facts.
* `IsEuclid.landing_strict_left`, `IsEuclid.landing_strict_right`,
  `IsEuclid.landing_sides_strict`: the strict landings.
* `continuousOn_phaseC_lengths`, `eventually_norm_phaseC_sub_lt`,
  `eventually_norm_phaseC_lengthsDir_sub_lt`: joint continuity and uniform convergence.
* `continuousOn_saddle`, `continuousOn_phaseC_saddle`, `tendsto_saddle_lengthsDir`,
  `tendsto_phaseC_saddle_lengthsDir`: continuity of the saddle data.

## References

* G. Ponzano, T. Regge, *Semiclassical limit of Racah coefficients*, in *Spectroscopic and
  group theoretical methods in physics*, North-Holland (1968), 1–58.
* J. Roberts, *Classical 6j-symbols and the tetrahedron*, Geom. Topol. 3 (1999) 21–66.
-/

open Set Filter Topology Complex
open scoped Real

namespace Lightlike.Asymptotics

/-! ## Strict landings -/

section Strict

variable {A : Fin 4 → ℝ} {B : Fin 3 → ℝ}

/-- `k ≠ k + 1` in `Fin 3`. -/
lemma fin3_ne_add_one (k : Fin 3) : k ≠ k + 1 := by
  fin_cases k <;> decide

/-- `bdry` left of `0`: `π (Σᵢ Aᵢ − 2u)`. -/
lemma bdry_of_nonpos (hA : ∀ i, 0 < A i) (hAB : ∀ i k, A i < B k) {u : ℝ} (hu : u ≤ 0) :
    bdry A B u = π * (∑ i, A i - 2 * u) := by
  rw [bdry_of_le fun k => hu.trans ((hA 0).trans (hAB 0 k)).le]
  have he : ∀ i, max (A i - u) 0 = A i - u := fun i => max_eq_left (by linarith [hA i])
  simp only [he, min_eq_left hu, Fin.sum_univ_four]
  ring

/-- **Strict left landing.** Let `Aᵢ₀` be a largest face sum and `Bₖ₀` a smallest
quadrilateral sum, with `Σᵢ Aᵢ = Σₖ Bₖ`. A point `u ≤ Aᵢ₀` at a level `κ` with
`π Aᵢ₀ < κ < π Bₖ₀` lies in the open interval `(0, Aᵢ₀)`. -/
theorem pos_lt_of_bdry_eq (hA : ∀ i, 0 < A i) (hAB : ∀ i k, A i < B k)
    (hsum : ∑ i, A i = ∑ k, B k) {i₀ : Fin 4} {k₀ : Fin 3} (hi₀ : ∀ i, A i ≤ A i₀)
    (hk₀ : ∀ k, B k₀ ≤ B k) {u κ : ℝ} (hu : u ≤ A i₀) (hlo : π * A i₀ < κ)
    (hhi : κ < π * B k₀) (hb : bdry A B u = κ) : 0 < u ∧ u < A i₀ := by
  refine ⟨?_, lt_of_le_of_ne hu fun h => ?_⟩
  · by_contra h0
    rw [not_lt] at h0
    rw [bdry_of_nonpos hA hAB h0] at hb
    have hBpos : ∀ k, 0 < B k := fun k => (hA 0).trans (hAB 0 k)
    have h2 : B k₀ + B (k₀ + 1) ≤ ∑ k, B k :=
      Finset.add_le_sum (fun k _ => (hBpos k).le) (Finset.mem_univ _) (Finset.mem_univ _)
        (fin3_ne_add_one k₀)
    have h3 : π * B k₀ < π * (∑ i, A i - 2 * u) :=
      mul_lt_mul_of_pos_left (by linarith [hBpos (k₀ + 1)]) Real.pi_pos
    linarith
  · rw [h, bdry_mid hA hi₀ hk₀ le_rfl (hAB i₀ k₀).le] at hb
    linarith

/-- **Strict right landing.** Let `Aᵢ₀` be a largest face sum and `Bₖ₀` a smallest
quadrilateral sum. A point `u ≥ Bₖ₀` at a level `κ < π Bₖ₀` lies strictly right of `Bₖ₀`. -/
theorem lt_of_bdry_eq_right (hA : ∀ i, 0 < A i) (hAB : ∀ i k, A i < B k) {i₀ : Fin 4}
    {k₀ : Fin 3} (hi₀ : ∀ i, A i ≤ A i₀) (hk₀ : ∀ k, B k₀ ≤ B k) {u κ : ℝ} (hu : B k₀ ≤ u)
    (hhi : κ < π * B k₀) (hb : bdry A B u = κ) : B k₀ < u := by
  refine lt_of_le_of_ne hu fun h => ?_
  rw [← h, bdry_mid hA hi₀ hk₀ (hAB i₀ k₀).le le_rfl] at hb
  linarith

end Strict

/-- **Strict left landing of a Euclidean tetrahedron.** A real point `x` at or left of some
face sum, at a level `κ'` strictly between every `π Aᵢ` and every `π Bₖ`, satisfies `x > 0` and
lies strictly left of some face sum. -/
theorem IsEuclid.landing_strict_left {l : Fin 6 → ℝ} (h : IsEuclid l) {κ' x : ℝ}
    (hlo : ∀ i, π * faceSum l i < κ') (hhi : ∀ k, κ' < π * quadSum l k)
    (hb : bdry (faceSum l) (quadSum l) x = κ') (hx : ∃ i, x ≤ faceSum l i) :
    0 < x ∧ ∃ i, x < faceSum l i := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (faceSum l)
  obtain ⟨k₀, hk₀⟩ := Finite.exists_min (quadSum l)
  obtain ⟨i, hi⟩ := hx
  obtain ⟨h1, h2⟩ := pos_lt_of_bdry_eq h.faceSum_pos h.lt (sum_faceSum_eq_sum_quadSum l) hi₀
    hk₀ (hi.trans (hi₀ i)) (hlo i₀) (hhi k₀) hb
  exact ⟨h1, i₀, h2⟩

/-- **Strict right landing of a Euclidean tetrahedron.** A real point `x` at or right of some
quadrilateral sum, at a level `κ'` strictly below every `π Bₖ`, lies strictly right of some
quadrilateral sum. -/
theorem IsEuclid.landing_strict_right {l : Fin 6 → ℝ} (h : IsEuclid l) {κ' x : ℝ}
    (hhi : ∀ k, κ' < π * quadSum l k) (hb : bdry (faceSum l) (quadSum l) x = κ')
    (hx : ∃ k, quadSum l k ≤ x) : ∃ k, quadSum l k < x := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (faceSum l)
  obtain ⟨k₀, hk₀⟩ := Finite.exists_min (quadSum l)
  obtain ⟨k, hk⟩ := hx
  exact ⟨k₀, lt_of_bdry_eq_right h.faceSum_pos h.lt hi₀ hk₀ ((hk₀ k).trans hk) (hhi k₀) hb⟩

/-- **The descent paths land strictly inside the outer intervals.** With the valley data of
`IsEuclid.exists_valley` and end points `z₁`, `z₂` of valley rays in the two valleys at one
level `κ'` strictly between every `π Aᵢ` and every `π Bₖ`, the descent paths land at real points
`x₁`, `x₂` on that level, one in `(0, A_max)` (positive and strictly left of some face sum) and
the other strictly right of some quadrilateral sum. This strengthens `IsEuclid.landing_sides`. -/
theorem IsEuclid.landing_sides_strict {l : Fin 6 → ℝ} (h : IsEuclid l)
    {b u₀ : ℂ} {K r : ℝ} (hb0 : b ≠ 0) (hu : ‖u₀‖ = 1) (hbu : b * u₀ ^ 2 = -‖b‖)
    (hr : 0 < r)
    (hray : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
      0 < (saddle l + t * valleyDir u₀ ε τ).im ∧
      ‖phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ) -
          phaseC (faceSum l) (quadSum l) (saddle l) - b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤
        K * t ^ 3 ∧
      (phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ)).re ≤
        (phaseC (faceSum l) (quadSum l) (saddle l)).re - ‖b‖ / 4 * t ^ 2)
    {τ₁ τ₂ κ' : ℝ} (hτ₁ : |τ₁| ≤ 1 / 2) (hτ₂ : |τ₂| ≤ 1 / 2)
    (hl₁ : (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir u₀ 1 τ₁)).im = κ')
    (hl₂ : (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir u₀ (-1) τ₂)).im = κ')
    (hlo : ∀ i, π * faceSum l i < κ') (hhi : ∀ k, κ' < π * quadSum l k) :
    ∃ (T₁ T₂ : ℝ) (α₁ α₂ : ℝ → ℂ) (x₁ x₂ : ℝ),
      IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l)
        (saddle l + r * valleyDir u₀ 1 τ₁) T₁ α₁ ∧ Tendsto α₁ (𝓝[<] T₁) (𝓝 (x₁ : ℂ)) ∧
      IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l)
        (saddle l + r * valleyDir u₀ (-1) τ₂) T₂ α₂ ∧ Tendsto α₂ (𝓝[<] T₂) (𝓝 (x₂ : ℂ)) ∧
      bdry (faceSum l) (quadSum l) x₁ = κ' ∧ bdry (faceSum l) (quadSum l) x₂ = κ' ∧
      (((0 < x₁ ∧ ∃ i, x₁ < faceSum l i) ∧ ∃ k, quadSum l k < x₂) ∨
        ((0 < x₂ ∧ ∃ i, x₂ < faceSum l i) ∧ ∃ k, quadSum l k < x₁)) := by
  obtain ⟨T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, hb₁, hb₂, hs⟩ :=
    h.landing_sides hb0 hu hbu hr hray hτ₁ hτ₂ hl₁ hl₂ hlo hhi
  refine ⟨T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, hb₁, hb₂, ?_⟩
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h.landing_strict_left hlo hhi hb₁ h1, h.landing_strict_right hhi hb₂ h2⟩
  · exact Or.inr ⟨h.landing_strict_left hlo hhi hb₂ h1, h.landing_strict_right hhi hb₁ h2⟩

/-! ## Continuity in the edge lengths -/

/-- **Joint continuity of the phase.** `(m, z) ↦ ψ_m(z) = phaseC (faceSum m) (quadSum m) z` is
continuous on `ℝ⁶ × H̄`, with `H̄` the closed upper half-plane. -/
theorem continuousOn_phaseC_lengths :
    ContinuousOn (fun p : (Fin 6 → ℝ) × ℂ => phaseC (faceSum p.1) (quadSum p.1) p.2)
      (univ ×ˢ {z : ℂ | 0 ≤ z.im}) := by
  have hsh : ∀ g : (Fin 6 → ℝ) → ℝ, Continuous g →
      ContinuousOn (fun p : (Fin 6 → ℝ) × ℂ => xlog (p.2 - g p.1))
        (univ ×ˢ {z : ℂ | 0 ≤ z.im}) := fun g hg =>
    continuousOn_xlog.comp (by fun_prop) fun p hp => by simpa using hp.2
  have hx : ContinuousOn (fun p : (Fin 6 → ℝ) × ℂ => xlog p.2) (univ ×ˢ {z : ℂ | 0 ≤ z.im}) :=
    continuousOn_xlog.comp continuous_snd.continuousOn fun p hp => hp.2
  unfold phaseC
  refine (((hx.sub (continuousOn_finsetSum _ fun i _ => hsh _ (continuous_faceSum i))).add
    (continuousOn_finsetSum _ fun k _ => hsh _ (continuous_quadSum k))).sub ?_).add ?_
  · exact continuousOn_const.mul continuous_snd.continuousOn
  · exact (continuous_const.mul (continuous_finsetSum _ fun k _ =>
      continuous_ofReal.comp ((continuous_quadSum k).comp continuous_fst))).continuousOn

/-- **Uniform convergence on compacts.** For a compact `K` in the closed upper half-plane and
edge lengths `m → j`, `ψ_m → ψ_j` uniformly on `K`. -/
theorem eventually_norm_phaseC_sub_lt {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ {z : ℂ | 0 ≤ z.im}) (j : Fin 6 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in 𝓝 j, ∀ z ∈ K,
      ‖phaseC (faceSum m) (quadSum m) z - phaseC (faceSum j) (quadSum j) z‖ < ε := by
  have hc : ContinuousOn
      (Function.uncurry fun (m : Fin 6 → ℝ) (z : ℂ) => phaseC (faceSum m) (quadSum m) z)
      (univ ×ˢ K) :=
    continuousOn_phaseC_lengths.mono (prod_mono subset_rfl hKH)
  obtain ⟨v, hv, hvK⟩ := hK.mem_uniformity_of_prod hc (mem_univ j) (Metric.dist_mem_uniformity hε)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with m hm z hz
  simpa [dist_eq_norm] using hvK m hm z hz

/-- Uniform convergence on compacts along `m_λ = j + 1/(2λ)`, for integer spins `j`. -/
theorem eventually_norm_phaseC_lengthsDir_sub_lt (j : Fin 6 → ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ {z : ℂ | 0 ≤ z.im}) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ lam : ℕ in atTop, ∀ z ∈ K,
      ‖phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam)) z -
        phaseC (faceSum fun e => (j e : ℝ)) (quadSum fun e => (j e : ℝ)) z‖ < ε :=
  tendsto_lengthsDir j (eventually_norm_phaseC_sub_lt hK hKH _ hε)

/-- `qa` is continuous in the edge lengths. -/
lemma continuous_qa : Continuous qa := by
  unfold qa
  fun_prop

/-- `qb` is continuous in the edge lengths. -/
lemma continuous_qb : Continuous qb := by
  have hA := continuous_faceSum
  have hB := continuous_quadSum
  unfold qb
  exact (((hB 0).mul (hB 1)).mul (hB 2)).sub
    (((((hA 0).mul (hA 1)).mul (hA 2)).add (((hA 0).mul (hA 1)).mul (hA 3))).add
      (((hA 0).mul (hA 2)).mul (hA 3)) |>.add (((hA 1).mul (hA 2)).mul (hA 3)))

/-- The saddle point, as the complex number `Re + i Im`. -/
lemma saddle_eq_re_add_im : saddle = fun l =>
    Complex.ofReal (-qb l / (2 * qa l)) + Complex.ofReal (12 * √(vol2l l) / qa l) * I := by
  funext l
  apply Complex.ext
  · simp only [saddle, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; ring
  · simp only [saddle, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]; ring

/-- **The saddle point depends continuously on the edge lengths** of a Euclidean tetrahedron. -/
theorem continuousOn_saddle : ContinuousOn saddle {l : Fin 6 → ℝ | IsEuclid l} := by
  have hq : ∀ l ∈ {l : Fin 6 → ℝ | IsEuclid l}, qa l ≠ 0 := fun l hl =>
    (IsEuclid.qa_pos hl).ne'
  rw [saddle_eq_re_add_im]
  refine ContinuousOn.add ?_ (ContinuousOn.mul ?_ continuousOn_const)
  · exact continuous_ofReal.comp_continuousOn (continuous_qb.neg.continuousOn.div
      (continuous_const.mul continuous_qa).continuousOn
      fun l hl => mul_ne_zero two_ne_zero (hq l hl))
  · exact continuous_ofReal.comp_continuousOn
      ((continuous_const.mul continuous_vol2l.sqrt).continuousOn.div continuous_qa.continuousOn hq)

/-- **The phase at the saddle depends continuously on the edge lengths** of a Euclidean
tetrahedron. Its real part is the exponential rate `D(m)` and its imaginary part the Regge
action. -/
theorem continuousOn_phaseC_saddle :
    ContinuousOn (fun m => phaseC (faceSum m) (quadSum m) (saddle m))
      {l : Fin 6 → ℝ | IsEuclid l} := by
  have hg : ContinuousOn (fun m : Fin 6 → ℝ => (m, saddle m)) {l : Fin 6 → ℝ | IsEuclid l} :=
    continuousOn_id.prodMk continuousOn_saddle
  have hmap : MapsTo (fun m : Fin 6 → ℝ => (m, saddle m)) {l : Fin 6 → ℝ | IsEuclid l}
      (univ ×ˢ {z : ℂ | 0 ≤ z.im}) := fun m hm =>
    mem_prod.2 ⟨mem_univ _, le_of_lt (IsEuclid.saddle_im_pos hm)⟩
  exact (continuousOn_phaseC_lengths.comp hg hmap).congr fun m _ => rfl

/-- For Euclidean integer spins `j`, the saddle of `m_λ = j + 1/(2λ)` tends to the saddle
of `j`. -/
theorem tendsto_saddle_lengthsDir {j : Fin 6 → ℕ} (h : IsEuclid fun e => (j e : ℝ)) :
    Tendsto (fun lam => saddle (lengthsDir j lam)) atTop (𝓝 (saddle fun e => (j e : ℝ))) :=
  ((continuousOn_saddle.continuousAt (isOpen_isEuclid.mem_nhds h)).tendsto).comp
    (tendsto_lengthsDir j)

/-- For Euclidean integer spins `j`, the phase of `m_λ = j + 1/(2λ)` at its saddle tends to
the phase of `j` at its saddle. -/
theorem tendsto_phaseC_saddle_lengthsDir {j : Fin 6 → ℕ} (h : IsEuclid fun e => (j e : ℝ)) :
    Tendsto (fun lam => phaseC (faceSum (lengthsDir j lam)) (quadSum (lengthsDir j lam))
        (saddle (lengthsDir j lam))) atTop
      (𝓝 (phaseC (faceSum fun e => (j e : ℝ)) (quadSum fun e => (j e : ℝ))
        (saddle fun e => (j e : ℝ)))) :=
  ((continuousOn_phaseC_saddle.continuousAt (isOpen_isEuclid.mem_nhds h)).tendsto).comp
    (tendsto_lengthsDir j)

end Lightlike.Asymptotics
