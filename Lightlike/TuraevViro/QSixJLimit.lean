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
  have hz : ∀ {u : ℤ}, u < 0 → invQFG θ u = 0 := fun hu => if_neg (not_le.mpr hu)
  unfold InBox at h
  unfold racahTermG
  simp only [not_and_or, not_le] at h
  rcases h with h | h | h | h | h | h | h
  · rw [hz (show (z : ℤ) - α₁ < 0 by omega)]; ring
  · rw [hz (show (z : ℤ) - α₂ < 0 by omega)]; ring
  · rw [hz (show (z : ℤ) - α₃ < 0 by omega)]; ring
  · rw [hz (show (z : ℤ) - α₄ < 0 by omega)]; ring
  · rw [hz (show β₁ - (z : ℤ) < 0 by omega)]; ring
  · rw [hz (show β₂ - (z : ℤ) < 0 by omega)]; ring
  · rw [hz (show β₃ - (z : ℤ) < 0 by omega)]; ring

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

/-- In the box, every factorial argument is below `R` once the six differences `β₁ - αₖ`, `β_l - α₁` are. -/
lemma box_lt {α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ} {z : ℕ} (hz : InBox α₁ α₂ α₃ α₄ β₁ β₂ β₃ z) {R : ℤ}
    (k1 : β₁ - α₁ < R) (k2 : β₁ - α₂ < R) (k3 : β₁ - α₃ < R) (k4 : β₁ - α₄ < R) (m2 : β₂ - α₁ < R)
    (m3 : β₃ - α₁ < R) :
    (z : ℤ) - α₁ < R ∧ (z : ℤ) - α₂ < R ∧ (z : ℤ) - α₃ < R ∧ (z : ℤ) - α₄ < R ∧ β₁ - z < R ∧
      β₂ - z < R ∧ β₃ - z < R := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The six differences of the Racah parameters are below `r` under `RacahBound`. -/
lemma racah_bounds (hr : 2 ≤ r) {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (hb : RacahBound r j₁ j₂ j₄ j₅ j₆) :
    (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) - (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) < r ∧
    (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) - (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ) < r ∧
    (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) - (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) < r ∧
    (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) - (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ) < r ∧
    (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ) - (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) < r ∧
    (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ) - (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) < r := by
  obtain ⟨b1, b2, b4, b5, b6⟩ := hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

lemma continuousAt_racahG (hr : 2 ≤ r) {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (hb : RacahBound r j₁ j₂ j₄ j₅ j₆) :
    ContinuousAt (fun θ => racahG θ j₁ j₂ j₃ j₄ j₅ j₆) (π / r) := by
  obtain ⟨b1, b2, b4, b5, b6⟩ := hb
  unfold racahG
  obtain ⟨k1, k2, k3, k4, m2, m3⟩ := racah_bounds hr (j₃ := j₃) ⟨b1, b2, b4, b5, b6⟩
  exact tendsto_finset_sum _ fun z _ => continuousAt_racahTermG hr fun h => box_lt h k1 k2 k3 k4 m2 m3

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
  have hz : ∀ {u : ℤ}, u < 0 → invQFG θ u = 0 := fun hu => if_neg (not_le.mpr hu)
  unfold InBox at h
  unfold racahTermRG
  simp only [not_and_or, not_le] at h
  rcases h with h | h | h | h | h | h | h
  · rw [hz (show (z : ℤ) - α₁ < 0 by omega)]; ring
  · rw [hz (show (z : ℤ) - α₂ < 0 by omega)]; ring
  · rw [hz (show (z : ℤ) - α₃ < 0 by omega)]; ring
  · rw [hz (show (z : ℤ) - α₄ < 0 by omega)]; ring
  · rw [hz (show β₁ - (z : ℤ) < 0 by omega)]; ring
  · rw [hz (show β₂ - (z : ℤ) < 0 by omega)]; ring
  · rw [hz (show β₃ - (z : ℤ) < 0 by omega)]; ring

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
  · have hz : r ≤ z + 1 := by
      obtain ⟨h1, -, -, h4, -⟩ := hb
      rcases h with h | h
      · have : (j₁ + j₂ + j₃) / 2 ≤ z := by exact_mod_cast h1
        omega
      · have : (j₄ + j₅ + j₃) / 2 ≤ z := by exact_mod_cast h4
        omega
    unfold racahTermG racahTermRG
    rw [qfG_eq_reg r θ (z + 1), if_pos ⟨hz, hr⟩]
    ring
  · rw [racahTermG_out hb, racahTermRG_out hb, mul_zero]

lemma continuousAt_racahRG (hr : 2 ≤ r) {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (hb : RacahBound r j₁ j₂ j₄ j₅ j₆) :
    ContinuousAt (fun θ => racahRG r θ j₁ j₂ j₃ j₄ j₅ j₆) (π / r) := by
  obtain ⟨b1, b2, b4, b5, b6⟩ := hb
  unfold racahRG
  refine tendsto_finset_sum _ fun z _ => ?_
  by_cases hbox : InBox (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ)
      (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)
      (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ)
      (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ) z
  · have H : ∀ u : ℤ, u < r → ContinuousAt (fun θ => invQFG θ u) (π / r) :=
      fun u hu => continuousAt_invQFG hr hu
    obtain ⟨k1, k2, k3, k4, m2, m3⟩ := racah_bounds hr (j₃ := j₃) ⟨b1, b2, b4, b5, b6⟩
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := box_lt hbox k1 k2 k3 k4 m2 m3
    unfold racahTermRG
    exact (continuousAt_const.mul (continuousAt_qfRegG hr _)).mul
      (((((H _ c1).mul (H _ c2)).mul (H _ c3)).mul (H _ c4)).mul (((H _ c5).mul (H _ c6)).mul (H _ c7)))
  · exact continuousAt_const.congr (Filter.Eventually.of_forall fun θ => (racahTermRG_out hbox θ).symm)

lemma racahTermRG_root (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) (z : ℕ) :
    racahTermRG r (π / r) α₁ α₂ α₃ α₄ β₁ β₂ β₃ z = Refl.regTerm r α₁ α₂ α₃ α₄ β₁ β₂ β₃ z := by
  unfold racahTermRG Refl.regTerm Refl.PnReg
  rw [if_pos (by omega), show ((z : ℤ) + 1).toNat = z + 1 by omega, qfRegG_root]
  simp only [invQFG_root]

/-- At `π/r` the regularised sum is the library's `Refl.SRg` of the Racah parameters. -/
lemma racahRG_root (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racahRG r (π / r) j₁ j₂ j₃ j₄ j₅ j₆ =
      Refl.SRg r (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ)
        (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)
        (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ)
        (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ) := by
  unfold racahRG Refl.SRg
  simp only [racahTermRG_root]
  symm
  have hP : (j₁ + j₂ + j₄ + j₅) / 2 ≤ j₁ + j₂ + j₃ + j₄ + j₅ + j₆ := by omega
  refine sum_subset (range_subset_range.2 ?_) fun z hz hz' => ?_
  · rw [Int.toNat_natCast]; omega
  rw [mem_range, Int.toNat_natCast] at hz'
  unfold Refl.regTerm
  rw [Refl.invQFact_neg (show (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) - z < 0 by omega)]
  ring

/-- `racahG = η^k · C`, `k = 1` when the first or the fourth triad is above the level (then `C → SRg`), else
`k = 0` (then `C = racahG`, continuous, `→ qRacahSum`). -/
lemma decomp_racahG (hr : 2 ≤ r) {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (hb : RacahBound r j₁ j₂ j₄ j₅ j₆) :
    Decomp r (fun θ => racahG θ j₁ j₂ j₃ j₄ j₅ j₆)
      (if r - 1 ≤ (j₁ + j₂ + j₃) / 2 ∨ r - 1 ≤ (j₄ + j₅ + j₃) / 2 then 1 else 0) 0
      (if r - 1 ≤ (j₁ + j₂ + j₃) / 2 ∨ r - 1 ≤ (j₄ + j₅ + j₃) / 2 then
        Refl.SRg r (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ)
          (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)
          (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ)
          (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ)
      else qRacahSum r j₁ j₂ j₃ j₄ j₅ j₆) := by
  by_cases h : r - 1 ≤ (j₁ + j₂ + j₃) / 2 ∨ r - 1 ≤ (j₄ + j₅ + j₃) / 2
  · simp only [if_pos h]
    exact ⟨fun θ => racahRG r θ j₁ j₂ j₃ j₄ j₅ j₆, continuousAt_racahRG hr hb, racahRG_root _ _ _ _ _ _,
      fun θ => by
        show racahG θ j₁ j₂ j₃ j₄ j₅ j₆ = etaG r θ ^ 1 * (etaG r θ)⁻¹ ^ 0 * racahRG r θ j₁ j₂ j₃ j₄ j₅ j₆
        rw [pow_one, pow_zero, mul_one]; exact racahG_eq_eta_mul θ h (by omega)⟩
  · simp only [if_neg h]
    have := Decomp.of_continuousAt (r := r) (continuousAt_racahG (j₃ := j₃) hr hb)
    rwa [racahG_root] at this

lemma decomp_qnG (hr : 2 ≤ r) (n : ℕ) : Decomp r (fun θ => qnG θ n) 0 0 (qnum r n) := by
  have := Decomp.of_continuousAt (r := r) (continuousAt_qnG hr n)
  rwa [qnG_root] at this

lemma decomp_const (c : ℝ) : Decomp r (fun _ => c) 0 0 c := Decomp.of_continuousAt continuousAt_const

/-! ## The pairing `x ↔ 2r - 2 - x` -/

/-- `E(u, v, x) = [s-u]! [s-v]! [s-x]! / ([r-1]! [s+1-r]!)`, `s = (u+v+x)/2`: the factor of the reflection
attached to the triad `(u, v, x)` above the level. -/
noncomputable def E3 (r u v x : ℕ) : ℝ :=
  qfact r ((u + v + x) / 2 - u) * qfact r ((u + v + x) / 2 - v) * qfact r ((u + v + x) / 2 - x) /
    (qfact r (r - 1) * qfact r ((u + v + x) / 2 + 1 - r))

lemma E3_swap (r u v x : ℕ) : E3 r v u x = E3 r u v x := by
  unfold E3; rw [show v + u + x = u + v + x by ring]; ring

lemma E3_ne_zero (hr : 2 ≤ r) {u v x : ℕ} (hu : u ≤ r - 2) (hv : v ≤ r - 2) (ht : Tri u v x)
    (hs : (u + v + x) / 2 ≤ 2 * r - 3) : E3 r u v x ≠ 0 := by
  unfold Tri at ht
  unfold E3
  refine div_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (mul_ne_zero ?_ ?_) <;>
    exact qfact_ne_zero_of_lt hr (by omega)

/-- Above the level, `delta2Reg = (-1)^(s+1-r) E`. -/
lemma delta2Reg_above (hr : 2 ≤ r) {u v x : ℕ} (hs : r - 1 ≤ (u + v + x) / 2) :
    delta2Reg r u v x = (-1) ^ ((u + v + x) / 2 + 1 - r) * E3 r u v x := by
  unfold delta2Reg E3
  rw [Refl.qfactReg_of_ge hr (by omega)]
  have h1 : ((-1 : ℝ) ^ ((u + v + x) / 2 + 1 - r))⁻¹ = (-1) ^ ((u + v + x) / 2 + 1 - r) := by
    rw [← inv_pow, inv_neg, inv_one]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  simp only [mul_inv]
  rw [h1, show (u + v + x) / 2 + 1 - r = (u + v + x) / 2 + 1 - r from rfl]
  ring

/-- `E(u, v, 2r-2-x) = E(u, v, x)⁻¹` (from `[r-1-k]! [k]! = [r-1]!`). -/
lemma E3_reflect (hr : 2 ≤ r) {u v x : ℕ} (hu : u ≤ r - 2) (hv : v ≤ r - 2) (ht : Tri u v x)
    (hs : r - 1 ≤ (u + v + x) / 2) : E3 r u v (2 * r - 2 - x) = (E3 r u v x)⁻¹ := by
  unfold Tri at ht
  have hx : x ≤ 2 * r - 2 := by omega
  set s := (u + v + x) / 2 with hsdef
  have e1 : (u + v + (2 * r - 2 - x)) / 2 - u = r - 1 - (s - v) := by omega
  have e2 : (u + v + (2 * r - 2 - x)) / 2 - v = r - 1 - (s - u) := by omega
  have e3 : (u + v + (2 * r - 2 - x)) / 2 - (2 * r - 2 - x) = s + 1 - r := by omega
  have e4 : (u + v + (2 * r - 2 - x)) / 2 + 1 - r = s - x := by omega
  have r1 := Refl.qfact_reflect hr (k := s - v) (by omega)
  have r2 := Refl.qfact_reflect hr (k := s - u) (by omega)
  have n1 := qfact_ne_zero_of_lt hr (n := s - u) (by omega)
  have n2 := qfact_ne_zero_of_lt hr (n := s - v) (by omega)
  have n3 := qfact_ne_zero_of_lt hr (n := s - x) (by omega)
  have n4 := qfact_ne_zero_of_lt hr (n := s + 1 - r) (by omega)
  have n5 := qfact_ne_zero_of_lt hr (n := r - 1) (by omega)
  unfold E3
  rw [e1, e2, e3, e4, ← hsdef]
  have r1' : qfact r (r - 1 - (s - v)) = qfact r (r - 1) / qfact r (s - v) := by
    rw [eq_div_iff n2, r1]
  have r2' : qfact r (r - 1 - (s - u)) = qfact r (r - 1) / qfact r (s - u) := by
    rw [eq_div_iff n1, r2]
  rw [r1', r2']
  field_simp

lemma SRg_swap12_34 (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) :
    Refl.SRg r a2 a1 a4 a3 b1 b2 b3 = Refl.SRg r a1 a2 a3 a4 b1 b2 b3 := by
  unfold Refl.SRg Refl.regTerm; refine sum_congr rfl fun z _ => ?_; ring

/-- The Racah parameters of `racahG θ j₁ … j₆` as a function of the third colour. -/
noncomputable def SRgAt (r j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℝ :=
  Refl.SRg r (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ)
    (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)
    (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ)
    (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ)

set_option maxHeartbeats 3000000 in
/-- **The reflection of the regularised sum in the colour `j₃`**: with the two triads through `j₃` above the
level and the other two within it, `j₃ ↦ 2r - 2 - j₃` multiplies it by `E(j₁,j₂,j₃) E(j₄,j₅,j₃)`. -/
theorem SRgAt_reflect (hr : 2 ≤ r) {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ}
    (t1 : Tri j₁ j₂ j₃) (t2 : Tri j₁ j₅ j₆) (t3 : Tri j₄ j₂ j₆) (t4 : Tri j₄ j₅ j₃)
    (l2 : (j₁ + j₅ + j₆) / 2 ≤ r - 2) (l3 : (j₄ + j₂ + j₆) / 2 ≤ r - 2)
    (h1 : r - 1 ≤ (j₁ + j₂ + j₃) / 2) (h4 : r - 1 ≤ (j₄ + j₅ + j₃) / 2) :
    SRgAt r j₁ j₂ (2 * r - 2 - j₃) j₄ j₅ j₆ = E3 r j₁ j₂ j₃ * E3 r j₄ j₅ j₃ * SRgAt r j₁ j₂ j₃ j₄ j₅ j₆ := by
  -- the half-sums are exact (parity), and become variables with linear defining equations
  obtain ⟨p1, t1a, t1b, t1c⟩ := t1
  obtain ⟨p2, t2a, t2b, t2c⟩ := t2
  obtain ⟨p3, t3a, t3b, t3c⟩ := t3
  obtain ⟨p4, t4a, t4b, t4c⟩ := t4
  have hj1 : j₁ ≤ r - 2 := by clear h1 h4 l3; omega
  have hj2 : j₂ ≤ r - 2 := by clear h1 h4 l2; omega
  have hX : j₃ ≤ 2 * r - 2 := by clear h1 h4 l2 l3; omega
  have mP : (j₁ + j₂ + j₄ + j₅) % 2 = 0 := by clear h1 h4 l2 l3; omega
  have mQ : (j₂ + j₃ + j₅ + j₆) % 2 = 0 := by clear h1 h4 l2 l3; omega
  have mR : (j₃ + j₁ + j₆ + j₄) % 2 = 0 := by clear h1 h4 l2 l3; omega
  have mA' : (j₁ + j₂ + (2 * r - 2 - j₃)) % 2 = 0 := by clear h1 h4 l2 l3; omega
  have mD' : (j₄ + j₅ + (2 * r - 2 - j₃)) % 2 = 0 := by clear h1 h4 l2 l3; omega
  have mQ' : (j₂ + (2 * r - 2 - j₃) + j₅ + j₆) % 2 = 0 := by clear h1 h4 l2 l3; omega
  have mR' : ((2 * r - 2 - j₃) + j₁ + j₆ + j₄) % 2 = 0 := by clear h1 h4 l2 l3; omega
  have eA := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero p1)
  have eB := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero p2)
  have eC := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero p3)
  have eD := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero p4)
  have eP := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero mP)
  have eQ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero mQ)
  have eR := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero mR)
  have eA' := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero mA')
  have eD' := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero mD')
  have eQ' := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero mQ')
  have eR' := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero mR')
  have eX : 2 * r - 2 - j₃ + j₃ + 2 = 2 * r := by clear h1 h4 l2 l3; omega
  have h1' : r ≤ (j₁ + j₂ + j₃) / 2 + 1 := by clear l2 l3 h4; omega
  have h4' : r ≤ (j₄ + j₅ + j₃) / 2 + 1 := by clear l2 l3 h1; omega
  have l2' : (j₁ + j₅ + j₆) / 2 + 2 ≤ r := by clear l3 h1 h4; omega
  have l3' : (j₄ + j₂ + j₆) / 2 + 2 ≤ r := by clear l2 h1 h4; omega
  clear p1 p2 p3 p4 mP mQ mR mA' mD' mQ' mR' h1 h4 l2 l3 hj1 hj2 hX
  unfold SRgAt E3
  generalize 2 * r - 2 - j₃ = X at *
  generalize (j₁ + j₂ + j₃) / 2 = A at *
  generalize (j₁ + j₅ + j₆) / 2 = B at *
  generalize (j₄ + j₂ + j₆) / 2 = C at *
  generalize (j₄ + j₅ + j₃) / 2 = D at *
  generalize (j₁ + j₂ + j₄ + j₅) / 2 = P at *
  generalize (j₂ + j₃ + j₅ + j₆) / 2 = Q at *
  generalize (j₃ + j₁ + j₆ + j₄) / 2 = R at *
  generalize (j₁ + j₂ + X) / 2 = A' at *
  generalize (j₄ + j₅ + X) / 2 = D' at *
  generalize (j₂ + X + j₅ + j₆) / 2 = Q' at *
  generalize (X + j₁ + j₆ + j₄) / 2 = R' at *
  have H : Refl.ReflHyp r (B : ℤ) (A : ℤ) (D : ℤ) (C : ℤ) (P : ℤ) (Q : ℤ) (R : ℤ) := by
    constructor <;> omega
  have hR := Refl.SRg_reflect hr H
  unfold Refl.ReflAt Refl.rd at hR
  rw [← SRg_swap12_34 r (A : ℤ), ← SRg_swap12_34 r (A' : ℤ)]
  have q1 : (A' : ℤ) = A + ((r : ℤ) - 1 - ((A : ℤ) + D - P)) := by omega
  have q2 : (D' : ℤ) = D + ((r : ℤ) - 1 - ((A : ℤ) + D - P)) := by omega
  have q3 : (Q' : ℤ) = Q + ((r : ℤ) - 1 - ((A : ℤ) + D - P)) := by omega
  have q4 : (R' : ℤ) = R + ((r : ℤ) - 1 - ((A : ℤ) + D - P)) := by omega
  rw [q1, q2, q3, q4, hR]
  congr 1
  unfold Refl.regFac
  have f1 : ((Q : ℤ) - B).toNat = A - j₁ := by omega
  have f2 : ((R : ℤ) - C).toNat = A - j₂ := by omega
  have f3 : ((P : ℤ) - D).toNat = A - j₃ := by omega
  have f4 : ((Q : ℤ) - C).toNat = D - j₄ := by omega
  have f5 : ((R : ℤ) - B).toNat = D - j₅ := by omega
  have f6 : ((P : ℤ) - A).toNat = D - j₃ := by omega
  have f7 : ((A : ℤ) - r + 1).toNat = A + 1 - r := by omega
  have f8 : ((D : ℤ) - r + 1).toNat = D + 1 - r := by omega
  rw [f1, f2, f3, f4, f5, f6, f7, f8]
  ring

/-! ## The pair cancellation of the limit terms -/

lemma neg_one_pow_of_mod {m n : ℕ} (h : m % 2 = n % 2) : (-1 : ℝ) ^ m = (-1) ^ n := by
  rw [← Nat.mod_add_div m 2, ← Nat.mod_add_div n 2, pow_add, pow_add, pow_mul, pow_mul, h]; simp

/-- `[2r - n] = -[n]` at `q = e^{iπ/r}`. -/
lemma qnum_two_mul_sub (hr : 2 ≤ r) {n : ℕ} (hn : n ≤ 2 * r) : qnum r (2 * r - n) = -qnum r n := by
  rcases le_total n r with h | h
  · rw [show 2 * r - n = r + (r - n) by omega, Refl.qnum_add_self hr, qnum_sub hr h]
  · rw [show n = r + (n - r) by omega, Refl.qnum_add_self hr, neg_neg,
      show 2 * r - (r + (n - r)) = r - (n - r) by omega, qnum_sub hr (by omega)]

/-- The limit at `θ = π/r` of the summand of the middle colour `x` whose three triads are above the level. -/
noncomputable def limTerm (r a b c d e f p q r' x : ℕ) : ℝ :=
  (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r' + x) / 2) * qnum r (x + 1) *
    (delta2Reg r a b x * delta2Reg r c d x * delta2Reg r e f x) *
    (SRgAt r a b x c d p * SRgAt r c d x e f q * SRgAt r e f x b a r')

/-- The algebra of the pair cancellation, on abstract factors. -/
lemma pair_algebra {s s' Q E1 E2 E3 S1 S2 S3 σ1 σ2 σ3 τ1 τ2 τ3 : ℝ} (h1 : E1 ≠ 0) (h2 : E2 ≠ 0)
    (h3 : E3 ≠ 0) (hs : s' * (τ1 * τ2 * τ3) = s * (σ1 * σ2 * σ3)) :
    s' * (-Q) * ((τ1 * E1⁻¹) * (τ2 * E2⁻¹) * (τ3 * E3⁻¹)) *
        ((E1 * E2 * S1) * (E2 * E3 * S2) * (E3 * E1 * S3)) =
      -(s * Q * ((σ1 * E1) * (σ2 * E2) * (σ3 * E3)) * (S1 * S2 * S3)) := by
  have : s' * (-Q) * ((τ1 * E1⁻¹) * (τ2 * E2⁻¹) * (τ3 * E3⁻¹)) *
      ((E1 * E2 * S1) * (E2 * E3 * S2) * (E3 * E1 * S3)) =
      -((s' * (τ1 * τ2 * τ3)) * Q * (E1 * E2 * E3) * (S1 * S2 * S3)) := by
    field_simp
  rw [this, hs]; ring

lemma qAdm_half {a b c : ℕ} (h : qAdm r a b c) : (a + b + c) / 2 ≤ r - 2 := by
  obtain ⟨-, h⟩ := h; omega

lemma qAdm_left {a b c : ℕ} (h : qAdm r a b c) : a ≤ r - 2 := by
  obtain ⟨⟨-, -, h1, -⟩, h⟩ := h; omega

lemma qAdm_mid {a b c : ℕ} (h : qAdm r a b c) : b ≤ r - 2 := by
  obtain ⟨⟨-, -, -, h1⟩, h⟩ := h; omega

lemma tri_swap {a b x : ℕ} (h : Tri a b x) : Tri b a x := by
  obtain ⟨h0, h1, h2, h3⟩ := h; exact ⟨by omega, by omega, by omega, by omega⟩

lemma tri_le_reflect {u v x : ℕ} (ht : Tri u v x) (hu : u ≤ r - 2) (hv : v ≤ r - 2) : x ≤ 2 * r - 2 := by
  obtain ⟨-, h1, -, -⟩ := ht; omega

lemma tri_above_reflect {u v x : ℕ} (ht : Tri u v x) (hu : u ≤ r - 2) (hv : v ≤ r - 2) :
    r - 1 ≤ (u + v + (2 * r - 2 - x)) / 2 := by
  obtain ⟨-, h1, -, -⟩ := ht; omega

lemma tri_half_le {u v x : ℕ} (ht : Tri u v x) (hu : u ≤ r - 2) (hv : v ≤ r - 2) :
    (u + v + x) / 2 ≤ 2 * r - 3 := by
  obtain ⟨-, h1, -, -⟩ := ht; omega

/-- The parity of the signs of the pair `x`, `2r - 2 - x`. -/
lemma limTerm_sign (hr : 2 ≤ r) {a b c d e f p q r' x : ℕ} (hx : x ≤ 2 * r - 2) (xab : x ≤ a + b) (xcd : x ≤ c + d) (xef : x ≤ e + f)
    (h1 : r - 1 ≤ (a + b + x) / 2) (h2 : r - 1 ≤ (c + d + x) / 2) (h3 : r - 1 ≤ (e + f + x) / 2) :
    ((a + b + c + d + e + f + p + q + r' + (2 * r - 2 - x)) / 2 +
        (((a + b + (2 * r - 2 - x)) / 2 + 1 - r) + ((c + d + (2 * r - 2 - x)) / 2 + 1 - r) +
          ((e + f + (2 * r - 2 - x)) / 2 + 1 - r))) % 2 =
      ((a + b + c + d + e + f + p + q + r' + x) / 2 +
        (((a + b + x) / 2 + 1 - r) + ((c + d + x) / 2 + 1 - r) + ((e + f + x) / 2 + 1 - r))) % 2 := by
  have eX : 2 * r - 2 - x + x + 2 = 2 * r := by omega
  generalize 2 * r - 2 - x = X at *
  clear hx
  omega

set_option maxHeartbeats 1000000 in
/-- **The limit terms cancel in pairs** `x ↔ 2r - 2 - x`. -/
theorem limTerm_reflect (hr : 2 ≤ r) {a b c d e f p q r' x : ℕ}
    (q1 : qAdm r a d p) (q2 : qAdm r c b p) (q3 : qAdm r c f q) (q4 : qAdm r e d q) (q5 : qAdm r e a r')
    (q6 : qAdm r b f r') (t1 : Tri a b x) (t2 : Tri c d x) (t3 : Tri e f x)
    (h1 : r - 1 ≤ (a + b + x) / 2) (h2 : r - 1 ≤ (c + d + x) / 2) (h3 : r - 1 ≤ (e + f + x) / 2) :
    limTerm r a b c d e f p q r' (2 * r - 2 - x) = -limTerm r a b c d e f p q r' x := by
  have ha := qAdm_left q1
  have hb := qAdm_mid q2
  have hc := qAdm_left q2
  have hd := qAdm_mid q1
  have he := qAdm_left q4
  have hf := qAdm_mid q3
  have h1' : r - 1 ≤ (b + a + x) / 2 := by rw [Nat.add_comm b a]; exact h1
  have R1 := SRgAt_reflect hr t1 q1.1 q2.1 t2 (qAdm_half q1) (qAdm_half q2) h1 h2
  have R2 := SRgAt_reflect hr t2 q3.1 q4.1 t3 (qAdm_half q3) (qAdm_half q4) h2 h3
  have R3 := SRgAt_reflect hr t3 q5.1 q6.1 (tri_swap t1) (qAdm_half q5) (qAdm_half q6) h3 h1'
  have D1' := delta2Reg_above hr (tri_above_reflect t1 ha hb)
  have D2' := delta2Reg_above hr (tri_above_reflect t2 hc hd)
  have D3' := delta2Reg_above hr (tri_above_reflect t3 he hf)
  rw [E3_reflect hr ha hb t1 h1] at D1'
  rw [E3_reflect hr hc hd t2 h2] at D2'
  rw [E3_reflect hr he hf t3 h3] at D3'
  have hx := tri_le_reflect t1 ha hb
  have hq : qnum r (2 * r - 2 - x + 1) = -qnum r (x + 1) := by
    rw [show 2 * r - 2 - x + 1 = 2 * r - (x + 1) by omega]; exact qnum_two_mul_sub hr (by omega)
  have hs : (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r' + (2 * r - 2 - x)) / 2) *
      ((-1) ^ ((a + b + (2 * r - 2 - x)) / 2 + 1 - r) * (-1) ^ ((c + d + (2 * r - 2 - x)) / 2 + 1 - r) *
        (-1) ^ ((e + f + (2 * r - 2 - x)) / 2 + 1 - r)) =
      (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r' + x) / 2) *
      ((-1) ^ ((a + b + x) / 2 + 1 - r) * (-1) ^ ((c + d + x) / 2 + 1 - r) * (-1) ^ ((e + f + x) / 2 + 1 - r)) := by
    simp only [← pow_add]
    exact neg_one_pow_of_mod (limTerm_sign hr hx t1.2.1 t2.2.1 t3.2.1 h1 h2 h3)
  unfold limTerm
  rw [hq, D1', D2', D3', R1, R2, R3, delta2Reg_above hr h1, delta2Reg_above hr h2, delta2Reg_above hr h3,
    E3_swap r a b x]
  exact pair_algebra (E3_ne_zero hr ha hb t1 (tri_half_le t1 ha hb)) (E3_ne_zero hr hc hd t2 (tri_half_le t2 hc hd))
    (E3_ne_zero hr he hf t3 (tri_half_le t3 he hf)) hs

end Lightlike.TV
