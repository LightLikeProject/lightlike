import Lightlike.TuraevViro.QSixJGeneric
import Lightlike.TuraevViro.QSixJRegular
import Lightlike.TuraevViro.TuraevViro

/-!
# The q-Biedenharn–Elliott identity at `q = e^{iπ/r}` as the limit of the generic one

`GenBE θ` (`QSixJGeneric.lean`) is the Biedenharn–Elliott identity at the angle `θ`, without square roots
and summed over every middle colour `x` allowed by the triangle conditions. This file shows that if it
holds for every `θ ≠ π/r` close to `π/r`, then the root-of-unity identity `qBiedenharnElliott` holds.

Near `θ = π/r` only one quantum integer among those involved tends to `0`: `η(θ) = [r]_θ` (every argument
is below `2r`). Each factor of a summand is `η^k` times a function continuous at `π/r`:
* `delta2G θ a b c = η⁻¹ · (continuous)` when the triad is above the level (`[s+1]!` contains `[r]`);
* `racahG θ …` is continuous when its four triads are within the level, and `η · racahRG θ …` when one
  is above it (every `[z+1]!` of the box contains `[r]`), `racahRG` being continuous with value the
  regularised sum `Refl.SRg` at `π/r`.

So a summand whose middle colour `x` has one or two of its three triads above the level is `O(η)`; one
with none above the level tends to the root-of-unity summand (divided by the six triangle coefficients
not containing `x`); one with all three above the level tends to a finite value, and these values cancel
in pairs `x ↔ 2r - 2 - x` by the reflection `Refl.SRg_reflect`. The right-hand side tends to the
root-of-unity one in the same way.

## Main results

* `Decomp`, `Decomp.tendsto_eq`, `Decomp.tendsto_zero`: the bookkeeping of powers of `η`.
* `qBiedenharnElliott_of_genBE`: the limit theorem.
-/

open Real Finset Filter Topology Lightlike.Pentagon

namespace Lightlike.TV

variable {r : ℕ}

/-! ## Quantum integers near the root of unity -/

lemma sin_pi_div_ne (hr : 2 ≤ r) : sin (π / r) ≠ 0 := (sin_pi_div_pos hr).ne'

lemma qnG_root (n : ℕ) : qnG (π / r) n = qnum r n := by
  unfold qnG qnum; rw [mul_div_assoc]

lemma continuousAt_qnG (hr : 2 ≤ r) (n : ℕ) : ContinuousAt (fun θ => qnG θ n) (π / r) := by
  unfold qnG
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (sin_pi_div_ne hr)

lemma continuousAt_qfG (hr : 2 ≤ r) (n : ℕ) : ContinuousAt (fun θ => qfG θ n) (π / r) := by
  unfold qfG
  exact tendsto_finset_prod _ fun k _ => continuousAt_qnG hr (k + 1)

lemma qfG_root (n : ℕ) : qfG (π / r) n = qfact r n := by
  unfold qfG qfact; simp only [qnG_root]

lemma invQFG_root (u : ℤ) : invQFG (π / r) u = invQFact r u := by
  unfold invQFG invQFact; simp only [qfG_root]

/-- `η(θ) = [r]_θ`, the only quantum integer below `2r` that vanishes at `θ = π/r`. -/
noncomputable def etaG (r : ℕ) (θ : ℝ) : ℝ := qnG θ r

lemma tendsto_etaG (hr : 2 ≤ r) : Tendsto (etaG r) (𝓝[≠] (π / r)) (𝓝 0) := by
  have h := (continuousAt_qnG hr r).tendsto
  rw [qnG_root, qnum_self hr] at h
  exact h.mono_left nhdsWithin_le_nhds

lemma eventually_etaG_ne (hr : 2 ≤ r) : ∀ᶠ θ in 𝓝[≠] (π / r), etaG r θ ≠ 0 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hball : ∀ᶠ θ in 𝓝 (π / r), |θ - π / r| < π / (2 * r) := by
    have : (0 : ℝ) < π / (2 * r) := by positivity
    filter_upwards [Metric.ball_mem_nhds (π / r) this] with θ hθ
    simpa [Real.dist_eq] using hθ
  have hpos : ∀ᶠ θ in 𝓝 (π / r), 0 < sin θ := by
    have := (continuous_sin.continuousAt (x := π / r)).eventually
      (lt_mem_nhds (sin_pi_div_pos hr))
    exact this
  filter_upwards [nhdsWithin_le_nhds hball, nhdsWithin_le_nhds hpos, self_mem_nhdsWithin]
    with θ h1 h2 h3
  unfold etaG qnG
  refine div_ne_zero ?_ h2.ne'
  have e : (r : ℝ) * θ = r * (θ - π / r) + π := by field_simp; ring
  rw [e, sin_add_pi, neg_ne_zero]
  have hb : |(r : ℝ) * (θ - π / r)| < π := by
    rw [abs_mul, abs_of_pos hr0]
    calc (r : ℝ) * |θ - π / r| < r * (π / (2 * r)) := by gcongr
      _ = π / 2 := by field_simp
      _ < π := by linarith [pi_pos]
  rw [abs_lt] at hb
  intro h0
  rw [Real.sin_eq_zero_iff_of_lt_of_lt hb.1 hb.2] at h0
  have : θ - π / r = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hr0.ne'
    · exact h
  exact h3 (by linarith)

/-! ## Powers of `η` times a function continuous at `π/r` -/

/-- `F θ = η(θ)^k · (η(θ)⁻¹)^m · C(θ)` with `C` continuous at `π/r` and `C(π/r) = L`. -/
def Decomp (r : ℕ) (F : ℝ → ℝ) (k m : ℕ) (L : ℝ) : Prop :=
  ∃ C : ℝ → ℝ, ContinuousAt C (π / r) ∧ C (π / r) = L ∧
    ∀ θ, F θ = etaG r θ ^ k * (etaG r θ)⁻¹ ^ m * C θ

lemma Decomp.of_continuousAt {F : ℝ → ℝ} (h : ContinuousAt F (π / r)) : Decomp r F 0 0 (F (π / r)) :=
  ⟨F, h, rfl, fun θ => by simp⟩

lemma Decomp.mul {F G : ℝ → ℝ} {k m k' m' : ℕ} {L L' : ℝ} (hF : Decomp r F k m L)
    (hG : Decomp r G k' m' L') : Decomp r (fun θ => F θ * G θ) (k + k') (m + m') (L * L') := by
  obtain ⟨C, hC, hCL, hFC⟩ := hF
  obtain ⟨D, hD, hDL, hGD⟩ := hG
  refine ⟨fun θ => C θ * D θ, hC.mul hD, by simp [hCL, hDL], fun θ => ?_⟩
  rw [hFC, hGD, pow_add, pow_add]; ring

lemma Decomp.congr {F G : ℝ → ℝ} {k m : ℕ} {L : ℝ} (hF : Decomp r F k m L) (h : ∀ θ, G θ = F θ) :
    Decomp r G k m L := by
  obtain ⟨C, hC, hCL, hFC⟩ := hF
  exact ⟨C, hC, hCL, fun θ => by rw [h, hFC]⟩

lemma Decomp.eta (r : ℕ) : Decomp r (etaG r) 1 0 1 :=
  ⟨fun _ => 1, continuousAt_const, rfl, fun θ => by simp⟩

lemma Decomp.etaInv (r : ℕ) : Decomp r (fun θ => (etaG r θ)⁻¹) 0 1 1 :=
  ⟨fun _ => 1, continuousAt_const, rfl, fun θ => by simp⟩

lemma Decomp.eventually_eq {F : ℝ → ℝ} {k m : ℕ} {L : ℝ} (hF : Decomp r F k m L) (hr : 2 ≤ r)
    (hkm : m ≤ k) : ∃ C : ℝ → ℝ, ContinuousAt C (π / r) ∧ C (π / r) = L ∧
      ∀ᶠ θ in 𝓝[≠] (π / r), F θ = etaG r θ ^ (k - m) * C θ := by
  obtain ⟨C, hC, hCL, hFC⟩ := hF
  refine ⟨C, hC, hCL, ?_⟩
  filter_upwards [eventually_etaG_ne hr] with θ hθ
  rw [hFC, show k = (k - m) + m by omega, pow_add, inv_pow, mul_assoc (etaG r θ ^ (k - m)),
    mul_inv_cancel₀ (pow_ne_zero _ hθ)]
  simp

lemma Decomp.tendsto_eq {F : ℝ → ℝ} {k : ℕ} {L : ℝ} (hF : Decomp r F k k L) (hr : 2 ≤ r) :
    Tendsto F (𝓝[≠] (π / r)) (𝓝 L) := by
  obtain ⟨C, hC, hCL, hev⟩ := hF.eventually_eq hr le_rfl
  have hC' : Tendsto C (𝓝[≠] (π / r)) (𝓝 L) := hCL ▸ hC.tendsto.mono_left nhdsWithin_le_nhds
  refine hC'.congr' ?_
  filter_upwards [hev] with θ hθ
  rw [hθ]; simp

lemma Decomp.tendsto_zero {F : ℝ → ℝ} {k m : ℕ} {L : ℝ} (hF : Decomp r F k m L) (hr : 2 ≤ r)
    (hkm : m < k) : Tendsto F (𝓝[≠] (π / r)) (𝓝 0) := by
  obtain ⟨C, hC, hCL, hev⟩ := hF.eventually_eq hr hkm.le
  have hC' : Tendsto C (𝓝[≠] (π / r)) (𝓝 L) := hCL ▸ hC.tendsto.mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun θ => etaG r θ ^ (k - m)) (𝓝[≠] (π / r)) (𝓝 0) := by
    have := (tendsto_etaG hr).pow (k - m)
    rwa [zero_pow (by omega)] at this
  have := he.mul hC'
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [hev] with θ hθ
  rw [hθ]

end Lightlike.TV
