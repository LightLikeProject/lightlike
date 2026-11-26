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
  exact h3 (show θ = π / r by linarith)

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
  show F θ * G θ = _
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

/-! ## The regularised quantum factorial near the root of unity -/

/-- `[n]_θ!` with the factor `[r]_θ` left out. -/
noncomputable def qfRegG (r : ℕ) (θ : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ range n, if k + 1 = r then 1 else qnG θ (k + 1)

lemma qfRegG_succ (r : ℕ) (θ : ℝ) (n : ℕ) :
    qfRegG r θ (n + 1) = qfRegG r θ n * (if n + 1 = r then 1 else qnG θ (n + 1)) := by
  unfold qfRegG; rw [prod_range_succ]

/-- `[n]_θ! = η(θ) · (regularised)` above the level, `= (regularised)` below it. -/
lemma qfG_eq_reg (r : ℕ) (θ : ℝ) (n : ℕ) :
    qfG θ n = (if r ≤ n ∧ 1 ≤ r then etaG r θ else 1) * qfRegG r θ n := by
  induction n with
  | zero =>
    simp only [qfG, qfRegG, range_zero, prod_empty, mul_one]
    rw [if_neg (by omega)]
  | succ n ih =>
    rw [qfG, prod_range_succ, ← qfG, ih, qfRegG_succ]
    by_cases h : n + 1 = r
    · subst h
      rw [if_neg (by omega), if_pos (by omega), if_pos rfl, etaG]
      ring
    · rw [if_neg h]
      by_cases h' : r ≤ n ∧ 1 ≤ r
      · rw [if_pos h', if_pos (by omega)]; ring
      · rw [if_neg h', if_neg (by omega)]; ring

lemma continuousAt_qfRegG (hr : 2 ≤ r) (n : ℕ) : ContinuousAt (fun θ => qfRegG r θ n) (π / r) := by
  unfold qfRegG
  refine tendsto_finset_prod _ fun k _ => ?_
  by_cases h : k + 1 = r
  · simp only [if_pos h]; exact continuousAt_const
  · simp only [if_neg h]; exact continuousAt_qnG hr (k + 1)

lemma qfRegG_root (n : ℕ) : qfRegG r (π / r) n = Refl.qfactReg r n := by
  unfold qfRegG Refl.qfactReg; simp only [qnG_root]

/-- `[n] ≠ 0` at `q = e^{iπ/r}` for `0 < n < 2r`, `n ≠ r`. -/
lemma qnum_ne_zero_of_lt_two_mul (hr : 2 ≤ r) {n : ℕ} (h0 : 0 < n) (hn : n < 2 * r) (hnr : n ≠ r) :
    qnum r n ≠ 0 := by
  rcases lt_or_gt_of_ne hnr with h | h
  · exact (qnum_pos hr h0 h).ne'
  · obtain ⟨j, rfl⟩ : ∃ j, n = r + j := ⟨n - r, by omega⟩
    rw [Refl.qnum_add_self hr, neg_ne_zero]
    exact (qnum_pos hr (by omega) (by omega)).ne'

lemma qfactReg_ne_zero (hr : 2 ≤ r) {n : ℕ} (hn : n ≤ 2 * r - 1) : Refl.qfactReg r n ≠ 0 := by
  unfold Refl.qfactReg
  refine prod_ne_zero_iff.mpr fun k hk => ?_
  rw [mem_range] at hk
  by_cases h : k + 1 = r
  · rw [if_pos h]; exact one_ne_zero
  · rw [if_neg h]; exact qnum_ne_zero_of_lt_two_mul hr (by omega) (by omega) h

lemma qfact_ne_zero_of_lt (hr : 2 ≤ r) {n : ℕ} (hn : n < r) : qfact r n ≠ 0 := (qfact_pos hr hn).ne'

/-! ## The squared triangle coefficient near the root of unity -/

/-- The limit value of `delta2G` with the factor `[r]` taken out: `[s-u]! [s-v]! [s-w]! / [s+1]!_reg`. -/
noncomputable def delta2Reg (r u v w : ℕ) : ℝ :=
  qfact r ((u + v + w) / 2 - u) * qfact r ((u + v + w) / 2 - v) * qfact r ((u + v + w) / 2 - w) /
    Refl.qfactReg r ((u + v + w) / 2 + 1)

/-- `delta2G = (η⁻¹)^m · C` with `C → delta2Reg`, `m = 1` above the level and `0` within it. -/
lemma decomp_delta2G (hr : 2 ≤ r) (u v w : ℕ) (hs : (u + v + w) / 2 + 1 ≤ 2 * r - 1) :
    Decomp r (fun θ => delta2G θ u v w) 0 (if r ≤ (u + v + w) / 2 + 1 then 1 else 0)
      (delta2Reg r u v w) := by
  set S := (u + v + w) / 2
  refine ⟨fun θ => qfG θ (S - u) * qfG θ (S - v) * qfG θ (S - w) / qfRegG r θ (S + 1), ?_, ?_, ?_⟩
  · refine ContinuousAt.div (by
      exact ((continuousAt_qfG hr _).mul (continuousAt_qfG hr _)).mul (continuousAt_qfG hr _))
      (continuousAt_qfRegG hr _) ?_
    rw [qfRegG_root]; exact qfactReg_ne_zero hr (by omega)
  · simp only [qfG_root, qfRegG_root, delta2Reg, S]
  · intro θ
    simp only [delta2G, qfG_eq_reg r θ (S + 1), pow_zero, one_mul, S]
    by_cases h : r ≤ (u + v + w) / 2 + 1
    · rw [if_pos ⟨h, by omega⟩, if_pos h, pow_one, mul_comm (etaG r θ), div_mul_eq_div_div,
        div_eq_inv_mul (_ / _) (etaG r θ)]
    · rw [if_neg (by omega), if_neg h, pow_zero, one_mul, one_mul]

lemma delta2Reg_of_lt (hr : 2 ≤ r) {u v w : ℕ} (hs : (u + v + w) / 2 + 1 < r) :
    delta2Reg r u v w = qDelta r u v w ^ 2 := by
  unfold delta2Reg qDelta
  rw [Refl.qfactReg_of_lt hs, Real.sq_sqrt]
  have := qfact_pos hr (n := (u + v + w) / 2 - u) (by omega)
  have := qfact_pos hr (n := (u + v + w) / 2 - v) (by omega)
  have := qfact_pos hr (n := (u + v + w) / 2 - w) (by omega)
  have := qfact_pos hr hs
  positivity

/-! ## The q-Racah sum near the root of unity -/

lemma continuousAt_invQFG (hr : 2 ≤ r) {u : ℤ} (hu : u < r) :
    ContinuousAt (fun θ => invQFG θ u) (π / r) := by
  unfold invQFG
  by_cases h : 0 ≤ u
  · simp only [if_pos h]
    refine (continuousAt_qfG hr _).inv₀ ?_
    rw [qfG_root]; exact qfact_ne_zero_of_lt hr (by omega)
  · simp only [if_neg h]; exact continuousAt_const

/-- The in-box condition of a q-Racah summand. -/
def InBox (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) (z : ℕ) : Prop :=
  α₁ ≤ z ∧ α₂ ≤ z ∧ α₃ ≤ z ∧ α₄ ≤ z ∧ (z : ℤ) ≤ β₁ ∧ (z : ℤ) ≤ β₂ ∧ (z : ℤ) ≤ β₃

/-- Out of the box, one factor `1/[u]!` has `u < 0`, so the summand vanishes identically. -/
lemma racahTermG_out {α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ} {z : ℕ} (h : ¬ InBox α₁ α₂ α₃ α₄ β₁ β₂ β₃ z)
    (θ : ℝ) : racahTermG θ α₁ α₂ α₃ α₄ β₁ β₂ β₃ z = 0 := by
  unfold InBox at h
  unfold racahTermG
  simp only [not_and_or, not_le] at h
  rcases h with h | h | h | h | h | h | h <;>
    simp [invQFG, show ¬ (0 : ℤ) ≤ _ from not_le.mpr (sub_neg.mpr h)]

lemma continuousAt_racahTermG (hr : 2 ≤ r) {α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ} {z : ℕ}
    (H : InBox α₁ α₂ α₃ α₄ β₁ β₂ β₃ z → (z : ℤ) - α₁ < r ∧ (z : ℤ) - α₂ < r ∧ (z : ℤ) - α₃ < r ∧
      (z : ℤ) - α₄ < r ∧ β₁ - z < r ∧ β₂ - z < r ∧ β₃ - z < r) :
    ContinuousAt (fun θ => racahTermG θ α₁ α₂ α₃ α₄ β₁ β₂ β₃ z) (π / r) := by
  by_cases hb : InBox α₁ α₂ α₃ α₄ β₁ β₂ β₃ z
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H hb
    unfold racahTermG
    exact (continuousAt_const.mul (continuousAt_qfG hr _)).mul
      (((((continuousAt_invQFG hr h1).mul (continuousAt_invQFG hr h2)).mul
        (continuousAt_invQFG hr h3)).mul (continuousAt_invQFG hr h4)).mul
        (((continuousAt_invQFG hr h5).mul (continuousAt_invQFG hr h6)).mul (continuousAt_invQFG hr h7)))
  · exact continuousAt_const.congr (Filter.Eventually.of_forall fun θ => (racahTermG_out hb θ).symm)

lemma racahTermG_root (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) (z : ℕ) :
    racahTermG (π / r) α₁ α₂ α₃ α₄ β₁ β₂ β₃ z = qRacahTerm r α₁ α₂ α₃ α₄ β₁ β₂ β₃ z := by
  unfold racahTermG qRacahTerm; simp only [qfG_root, invQFG_root]

/-- The colour bounds under which `racahG` is continuous at `π/r`: every colour but the third `≤ r - 2`. -/
def RacahBound (r j₁ j₂ j₄ j₅ j₆ : ℕ) : Prop :=
  j₁ ≤ r - 2 ∧ j₂ ≤ r - 2 ∧ j₄ ≤ r - 2 ∧ j₅ ≤ r - 2 ∧ j₆ ≤ r - 2

lemma continuousAt_racahG (hr : 2 ≤ r) {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (hb : RacahBound r j₁ j₂ j₄ j₅ j₆) :
    ContinuousAt (fun θ => racahG θ j₁ j₂ j₃ j₄ j₅ j₆) (π / r) := by
  obtain ⟨b1, b2, b4, b5, b6⟩ := hb
  unfold racahG
  exact tendsto_finset_sum _ fun z _ => continuousAt_racahTermG hr fun h => by unfold InBox at h; omega

lemma racahG_root (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racahG (π / r) j₁ j₂ j₃ j₄ j₅ j₆ = qRacahSum r j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold racahG qRacahSum; simp only [racahTermG_root]

/-- The summand with `[z+1]!` regularised. -/
noncomputable def racahTermRG (r : ℕ) (θ : ℝ) (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) (z : ℕ) : ℝ :=
  (-1 : ℝ) ^ z * qfRegG r θ (z + 1) *
    (invQFG θ (z - α₁) * invQFG θ (z - α₂) * invQFG θ (z - α₃) * invQFG θ (z - α₄) *
      (invQFG θ (β₁ - z) * invQFG θ (β₂ - z) * invQFG θ (β₃ - z)))

/-- The regularised q-Racah sum at the angle `θ`. -/
noncomputable def racahRG (r : ℕ) (θ : ℝ) (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℝ :=
  ∑ z ∈ range (j₁ + j₂ + j₃ + j₄ + j₅ + j₆ + 1),
    racahTermRG r θ (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ)
      (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)
      (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ)
      (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ) z

lemma racahTermRG_out {α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ} {z : ℕ} (h : ¬ InBox α₁ α₂ α₃ α₄ β₁ β₂ β₃ z)
    (θ : ℝ) : racahTermRG r θ α₁ α₂ α₃ α₄ β₁ β₂ β₃ z = 0 := by
  unfold InBox at h
  unfold racahTermRG
  simp only [not_and_or, not_le] at h
  rcases h with h | h | h | h | h | h | h <;>
    simp [invQFG, show ¬ (0 : ℤ) ≤ _ from not_le.mpr (sub_neg.mpr h)]

/-- If one triad of the summation box is above the level (`α ≥ r - 1` for `α = α₁` or `α₄`), every summand
carries the factor `[r]`: `racahG = η · racahRG`. -/
lemma racahG_eq_eta_mul (θ : ℝ) {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ}
    (h : r - 1 ≤ (j₁ + j₂ + j₃) / 2 ∨ r - 1 ≤ (j₄ + j₅ + j₃) / 2) (hr : 1 ≤ r) :
    racahG θ j₁ j₂ j₃ j₄ j₅ j₆ = etaG r θ * racahRG r θ j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold racahG racahRG
  rw [mul_sum]
  refine sum_congr rfl fun z _ => ?_
  by_cases hb : InBox (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ)
      (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)
      (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ)
      (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ) z
  · have hz : r ≤ z + 1 := by unfold InBox at hb; omega
    unfold racahTermG racahTermRG
    rw [qfG_eq_reg r θ (z + 1), if_pos ⟨hz, hr⟩]
    ring
  · rw [racahTermG_out hb, racahTermRG_out hb, mul_zero]

end Lightlike.TV
