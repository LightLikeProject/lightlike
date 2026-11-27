import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.SphericalClean
import Lightlike.Lorentz.SL2ROddPlancherel.OddPolarized
import Lightlike.Lorentz.SL2ROddPlancherel.AbelMulVFourier
import Lightlike.Lorentz.SL2ROddPlancherel.OddContour

/-!
# The odd Plancherel identity in `G`-form

For `G` smooth with compact support, `g = 𝒜G` and `ĥ(ρ) = a(ρ - i/2) + a(ρ + i/2)`, `a = ftC g`,

  `2π² ∫_{v>1} (1 + v) ‖G(v)‖² dv = ¼ ∫_{ρ>0} ρ coth(πρ) ‖ĥ(ρ)‖² dρ`   (`odd_plancherel_G`).

The proof applies the contour identity `odd_density_contour` to `a` and `ã(z) = conj a(conj z)`; the two
terms with equal shifts give `2 ∫ ρ tanh(πρ) ‖a(ρ)‖²`, the even Plancherel integral of `G`
(`norm_sq_eq_sph`); the two mixed terms are, after complex conjugation, the integral of
`ρ tanh(πρ) conj a(ρ) · ρ-weighted transform of vG` (`ftC_abel_mul_v`), the polarised even integral
of the pair `(G, vG)` (`sph_polarized`). See `docs/notes/sl2r-odd-plancherel-route.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Lightlike.Lorentz.SL2ROddPlancherel

open Lightlike.Lorentz.SL2RPlancherel

/-- `∫_ℝ f = 2 ∫_{x>0} f` for an even integrable `f`. -/
lemma integral_eq_two_mul_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : ∀ x, f (-x) = f x) (hi : Integrable f) :
    ∫ x, f x = (2 : ℝ) • ∫ x in Ioi (0 : ℝ), f x := by
  have h1 := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hi
  have h2 := integral_comp_neg_Iic (0 : ℝ) f
  rw [compl_Ioi] at h1
  simp only [hf, neg_zero] at h2
  rw [← h1, h2, two_smul]

/-- The conjugate of the complexified Fourier transform. -/
lemma conj_ftC (g : ℝ → ℂ) (w : ℂ) :
    conj (ftC g w) = ftC (fun t => conj (g (-t))) (conj w) := by
  unfold ftC
  rw [← integral_conj]
  have h := integral_neg_eq_self (fun t : ℝ => Complex.exp (conj w * t * I) * conj (g (-t))) volume
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [map_mul, neg_neg, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_conj]
  congr 2
  push_cast
  ring

/-- For even `g`, `conj (a w) = ã (conj w)` with `ã = ftC (conj ∘ g)`. -/
lemma conj_ftC_even {g : ℝ → ℂ} (heven : ∀ t, g (-t) = g t) (w : ℂ) :
    conj (ftC g w) = ftC (fun t => conj (g t)) (conj w) := by
  rw [conj_ftC]; simp only [heven]

/-- The complexified Fourier transform of an even function is even. -/
lemma ftC_neg_of_even {g : ℝ → ℂ} (heven : ∀ t, g (-t) = g t) (z : ℂ) : ftC g (-z) = ftC g z := by
  unfold ftC
  have h := integral_neg_eq_self (fun t : ℝ => Complex.exp (z * t * I) * g t) volume
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [heven, Complex.ofReal_neg]
  congr 2
  ring

/-- `rhoCoth (x + s) P(x)` is integrable on the real axis for `s` on the imaginary axis, `|Im s| ≤ 1/2`, and
`P` continuous with decay `C/(1 + x²)²`. -/
lemma integrable_rhoCoth_shift_mul {P : ℝ → ℂ} (hP : Continuous P) {C : ℝ}
    (hb : ∀ x : ℝ, ‖P x‖ ≤ C / (1 + x ^ 2) ^ 2) {s : ℂ} (hs : |s.im| ≤ 1 / 2) (hre : s.re = 0) :
    Integrable fun x : ℝ => rhoCoth ((x : ℂ) + s) * P x := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_rhoCoth_le
  have hC : 0 ≤ C := by
    have := le_trans (norm_nonneg _) (hb 0)
    simpa using this
  have hcont : Continuous fun x : ℝ => rhoCoth ((x : ℂ) + s) :=
    differentiableOn_rhoCoth.continuousOn.comp_continuous (by fun_prop) fun x => by
      show |((x : ℂ) + s).im| < 1
      rw [Complex.add_im, Complex.ofReal_im, zero_add]
      exact lt_of_le_of_lt hs (by norm_num)
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * M * C))
    (hcont.mul hP).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have h1 := hM ((x : ℂ) + s) (by simpa using hs)
  simp only [Complex.add_re, Complex.ofReal_re, hre, add_zero] at h1
  rw [norm_mul]
  calc ‖rhoCoth ((x : ℂ) + s)‖ * ‖P x‖ ≤ (M * (1 + |x|)) * (C / (1 + x ^ 2) ^ 2) := by
        gcongr; exact hb x
    _ ≤ (M * (2 * (1 + x ^ 2))) * (C / (1 + x ^ 2) ^ 2) := by gcongr; exact one_add_abs_le x
    _ = 2 * M * C * (1 + x ^ 2)⁻¹ := by field_simp

/-- A decay bound for a product of two functions with `C/(1+x²)` decay. -/
lemma decay_mul {u v : ℝ → ℂ} {C D : ℝ} (hu : ∀ x, ‖u x‖ ≤ C / (1 + x ^ 2))
    (hv : ∀ x, ‖v x‖ ≤ D / (1 + x ^ 2)) (x : ℝ) : ‖u x * v x‖ ≤ (C * D) / (1 + x ^ 2) ^ 2 := by
  rw [norm_mul]
  have h0 : 0 ≤ C := by have := le_trans (norm_nonneg _) (hu 0); simpa using this
  have h1 : 0 ≤ D := by have := le_trans (norm_nonneg _) (hv 0); simpa using this
  calc ‖u x‖ * ‖v x‖ ≤ (C / (1 + x ^ 2)) * (D / (1 + x ^ 2)) := by
        gcongr
        · exact hu x
        · exact hv x
    _ = (C * D) / (1 + x ^ 2) ^ 2 := by rw [div_mul_div_comm, ← sq (1 + x ^ 2)]

/-- **The odd transform** `ĥ(ρ) = a(ρ - i/2) + a(ρ + i/2) = ∫ e^{iρt} 2cosh(t/2) g(t) dt`, `a = ftC g`. -/
def oddHat (g : ℝ → ℂ) (ρ : ℝ) : ℂ := ftC g ((ρ : ℂ) - I / 2) + ftC g ((ρ : ℂ) + I / 2)

lemma cast_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma contDiff_conj {g : ℝ → ℂ} {n : ℕ∞} (hg : ContDiff ℝ n g) : ContDiff ℝ n (fun t => conj (g t)) :=
  Complex.conjCLE.contDiff.comp hg

lemma hasCompactSupport_conj {g : ℝ → ℂ} (hc : HasCompactSupport g) :
    HasCompactSupport (fun t => conj (g t)) :=
  hc.comp_left (g := fun z : ℂ => conj z) (by simp)

/-- For even `g`, `‖ĥ(ρ)‖²` is the product of the two shifted pairs of the contour identity. -/
lemma cast_norm_sq_oddHat {g : ℝ → ℂ} (heven : ∀ t, g (-t) = g t) (ρ : ℝ) :
    ((‖oddHat g ρ‖ ^ 2 : ℝ) : ℂ) =
      (ftC g ((ρ : ℂ) - I / 2) + ftC g ((ρ : ℂ) + I / 2)) *
        (ftC (fun t => conj (g t)) ((ρ : ℂ) + I / 2) + ftC (fun t => conj (g t)) ((ρ : ℂ) - I / 2)) := by
  rw [cast_norm_sq]
  unfold oddHat
  rw [map_add, conj_ftC_even heven, conj_ftC_even heven]
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  have e1 : conj ((ρ : ℂ) - I / 2) = (ρ : ℂ) + I / 2 := by
    rw [map_sub, map_div₀, Complex.conj_ofReal, Complex.conj_I, h2]; ring
  have e2 : conj ((ρ : ℂ) + I / 2) = (ρ : ℂ) - I / 2 := by
    rw [map_add, map_div₀, Complex.conj_ofReal, Complex.conj_I, h2]; ring
  rw [e1, e2]

/-- **The contour identity applied to `a = ftC g` and `ã = ftC (conj g)`.** -/
theorem odd_norm_contour {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g)
    (heven : ∀ t, g (-t) = g t) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x y : ℝ, |y| ≤ 1 → ‖ftC g ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2)) ∧
      (∀ x y : ℝ, |y| ≤ 1 → ‖ftC (fun t => conj (g t)) ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2)) ∧
      ∫ ρ : ℝ, rhoCoth (ρ : ℂ) * ((‖oddHat g ρ‖ ^ 2 : ℝ) : ℂ) =
        (∫ x : ℝ, rhoCoth ((x : ℂ) + I / 2) * (ftC g x * ftC (fun t => conj (g t)) x)) +
        (∫ x : ℝ, rhoCoth ((x : ℂ) - I / 2) * (ftC g x * ftC (fun t => conj (g t)) x)) +
        (∫ x : ℝ, rhoCoth ((x : ℂ) + I / 2) * (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) + I))) +
        (∫ x : ℝ, rhoCoth ((x : ℂ) - I / 2) * (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) - I))) := by
  have hg' := contDiff_conj hg
  have hc' := hasCompactSupport_conj hc
  obtain ⟨C1, hC1, hb1⟩ := norm_ftC_le hg hc 1
  obtain ⟨C2, hC2, hb2⟩ := norm_ftC_le hg' hc' 1
  have hA : ∀ x y : ℝ, |y| ≤ 1 → ‖ftC g ((x : ℂ) + (y : ℂ) * I)‖ ≤ (C1 + C2) / (1 + x ^ 2) := by
    intro x y hy
    refine (hb1 x y hy).trans ?_
    gcongr
    linarith
  have hB : ∀ x y : ℝ, |y| ≤ 1 → ‖ftC (fun t => conj (g t)) ((x : ℂ) + (y : ℂ) * I)‖ ≤
      (C1 + C2) / (1 + x ^ 2) := by
    intro x y hy
    refine (hb2 x y hy).trans ?_
    gcongr
    linarith
  refine ⟨C1 + C2, by positivity, hA, hB, ?_⟩
  have h := odd_density_contour (differentiable_ftC hg.continuous hc)
    (differentiable_ftC hg'.continuous hc') hA hB
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun ρ => ?_)
  simp only
  rw [cast_norm_sq_oddHat heven]

/-- The two terms with equal shifts: `∫ rhoCoth(x + i/2) a ã + ∫ rhoCoth(x - i/2) a ã = 2 ∫ x tanh(πx) ‖a(x)‖²`. -/
lemma T12_eq {g : ℝ → ℂ} (hgc : Continuous g) (hc : HasCompactSupport g) (heven : ∀ t, g (-t) = g t) {C : ℝ}
    (hA : ∀ x y : ℝ, |y| ≤ 1 → ‖ftC g ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2))
    (hB : ∀ x y : ℝ, |y| ≤ 1 → ‖ftC (fun t => conj (g t)) ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2)) :
    (∫ x : ℝ, rhoCoth ((x : ℂ) + I / 2) * (ftC g x * ftC (fun t => conj (g t)) x)) +
      (∫ x : ℝ, rhoCoth ((x : ℂ) - I / 2) * (ftC g x * ftC (fun t => conj (g t)) x)) =
      ((2 * ∫ x : ℝ, x * Real.tanh (Real.pi * x) * ‖ftC g x‖ ^ 2 : ℝ) : ℂ) := by
  have hg' := hasCompactSupport_conj hc
  have hgc' : Continuous fun t => conj (g t) := Complex.continuous_conj.comp hgc
  have hP : Continuous fun x : ℝ => ftC g (x : ℂ) * ftC (fun t => conj (g t)) (x : ℂ) :=
    ((differentiable_ftC hgc hc).continuous.comp Complex.continuous_ofReal).mul
      ((differentiable_ftC hgc' hg').continuous.comp Complex.continuous_ofReal)
  have hA0 : ∀ x : ℝ, ‖ftC g (x : ℂ)‖ ≤ C / (1 + x ^ 2) := fun x => by simpa using hA x 0 (by simp)
  have hB0 : ∀ x : ℝ, ‖ftC (fun t => conj (g t)) (x : ℂ)‖ ≤ C / (1 + x ^ 2) := fun x => by
    simpa using hB x 0 (by simp)
  have hb : ∀ x : ℝ, ‖ftC g (x : ℂ) * ftC (fun t => conj (g t)) (x : ℂ)‖ ≤ (C * C) / (1 + x ^ 2) ^ 2 :=
    decay_mul hA0 hB0
  have i1 := integrable_rhoCoth_shift_mul hP hb (s := I / 2) (by simp) (by simp)
  have i2 := integrable_rhoCoth_shift_mul hP hb (s := -(I / 2)) (by simp) (by simp)
  have e2 : ∀ x : ℝ, rhoCoth ((x : ℂ) - I / 2) = rhoCoth ((x : ℂ) + -(I / 2)) := fun x => by ring_nf
  simp_rw [e2]
  rw [← integral_add i1 i2]
  have : ∀ x : ℝ, rhoCoth ((x : ℂ) + I / 2) * (ftC g x * ftC (fun t => conj (g t)) x) +
      rhoCoth ((x : ℂ) + -(I / 2)) * (ftC g x * ftC (fun t => conj (g t)) x) =
      ((2 * (x * Real.tanh (Real.pi * x) * ‖ftC g x‖ ^ 2) : ℝ) : ℂ) := by
    intro x
    have hx : ftC (fun t => conj (g t)) (x : ℂ) = conj (ftC g (x : ℂ)) := by
      rw [conj_ftC_even heven, Complex.conj_ofReal]
    rw [← sub_eq_add_neg (x : ℂ) (I / 2), rhoCoth_add_half, rhoCoth_sub_half, hx]
    have hn := cast_norm_sq (ftC g (x : ℂ))
    have ht : Complex.tanh ((Real.pi : ℂ) * x) = ((Real.tanh (Real.pi * x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tanh, Complex.ofReal_mul]
    rw [ht]
    push_cast at hn ⊢
    rw [← hn]
    ring
  simp_rw [this]
  rw [integral_complex_ofReal, integral_const_mul]

lemma conj_ftC_conj_even {g : ℝ → ℂ} (heven : ∀ t, g (-t) = g t) (w : ℂ) :
    conj (ftC (fun t => conj (g t)) w) = ftC g (conj w) := by
  rw [conj_ftC]; simp [heven]

/-- The two mixed terms are the complex conjugate of twice the polarised even integral: with
`c` any function satisfying `x c(x) = ½[(x - i/2) a(x - i) + (x + i/2) a(x + i)]`,
`∫ rhoCoth(x + i/2) a(x) ã(x + i) + ∫ rhoCoth(x - i/2) a(x) ã(x - i) = conj (2 ∫ x tanh(πx) conj a(x) c(x))`. -/
lemma T34_eq {g : ℝ → ℂ} (hgc : Continuous g) (hc : HasCompactSupport g) (heven : ∀ t, g (-t) = g t) {C : ℝ}
    (hA : ∀ x y : ℝ, |y| ≤ 1 → ‖ftC g ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2))
    (hB : ∀ x y : ℝ, |y| ≤ 1 → ‖ftC (fun t => conj (g t)) ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2))
    {c : ℂ → ℂ}
    (hcz : ∀ x : ℝ, (x : ℂ) * c x = (1 / 2 : ℂ) * (((x : ℂ) - I / 2) * ftC g ((x : ℂ) - I) +
      ((x : ℂ) + I / 2) * ftC g ((x : ℂ) + I))) :
    Integrable (fun x : ℝ => ((x * Real.tanh (Real.pi * x) : ℝ) : ℂ) * (conj (ftC g x) * c x)) ∧
    (∫ x : ℝ, rhoCoth ((x : ℂ) + I / 2) * (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) + I))) +
      (∫ x : ℝ, rhoCoth ((x : ℂ) - I / 2) * (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) - I))) =
      conj (2 * ∫ x : ℝ, ((x * Real.tanh (Real.pi * x) : ℝ) : ℂ) * (conj (ftC g x) * c x)) := by
  have hg' := hasCompactSupport_conj hc
  have hgc' : Continuous fun t => conj (g t) := Complex.continuous_conj.comp hgc
  have ha := differentiable_ftC hgc hc
  have hb := differentiable_ftC hgc' hg'
  have hA0 : ∀ x : ℝ, ‖ftC g (x : ℂ)‖ ≤ C / (1 + x ^ 2) := fun x => by simpa using hA x 0 (by simp)
  have hB1 : ∀ x : ℝ, ‖ftC (fun t => conj (g t)) ((x : ℂ) + I)‖ ≤ C / (1 + x ^ 2) := fun x => by
    simpa using hB x 1 (by simp)
  have hB2 : ∀ x : ℝ, ‖ftC (fun t => conj (g t)) ((x : ℂ) - I)‖ ≤ C / (1 + x ^ 2) := fun x => by
    have := hB x (-1) (by simp)
    rwa [show (x : ℂ) + ((-1 : ℝ) : ℂ) * I = (x : ℂ) - I by push_cast; ring] at this
  have hP3 : Continuous fun x : ℝ => ftC g (x : ℂ) * ftC (fun t => conj (g t)) ((x : ℂ) + I) :=
    (ha.continuous.comp Complex.continuous_ofReal).mul
      (hb.continuous.comp (Complex.continuous_ofReal.add continuous_const))
  have hP4 : Continuous fun x : ℝ => ftC g (x : ℂ) * ftC (fun t => conj (g t)) ((x : ℂ) - I) :=
    (ha.continuous.comp Complex.continuous_ofReal).mul
      (hb.continuous.comp (Complex.continuous_ofReal.sub continuous_const))
  have i3 := integrable_rhoCoth_shift_mul hP3 (fun x => decay_mul hA0 hB1 x) (s := I / 2) (by simp) (by simp)
  have i4 := integrable_rhoCoth_shift_mul hP4 (fun x => decay_mul hA0 hB2 x) (s := -(I / 2)) (by simp) (by simp)
  have e4 : ∀ x : ℝ, rhoCoth ((x : ℂ) - I / 2) = rhoCoth ((x : ℂ) + -(I / 2)) := fun x => by ring_nf
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  -- the pointwise identity
  have key : ∀ x : ℝ, ((x * Real.tanh (Real.pi * x) : ℝ) : ℂ) * (conj (ftC g x) * c x) =
      (1 / 2 : ℂ) * conj (rhoCoth ((x : ℂ) + I / 2) * (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) + I)) +
        rhoCoth ((x : ℂ) - I / 2) * (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) - I))) := by
    intro x
    have ht : Complex.tanh ((Real.pi : ℂ) * x) = ((Real.tanh (Real.pi * x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tanh, Complex.ofReal_mul]
    have c1 : conj ((x : ℂ) + I / 2) = (x : ℂ) - I / 2 := by
      rw [map_add, map_div₀, Complex.conj_ofReal, Complex.conj_I, h2]; ring
    have c2 : conj ((x : ℂ) - I / 2) = (x : ℂ) + I / 2 := by
      rw [map_sub, map_div₀, Complex.conj_ofReal, Complex.conj_I, h2]; ring
    have c3 : conj ((x : ℂ) + I) = (x : ℂ) - I := by rw [map_add, Complex.conj_ofReal, Complex.conj_I]; ring
    have c4 : conj ((x : ℂ) - I) = (x : ℂ) + I := by rw [map_sub, Complex.conj_ofReal, Complex.conj_I]; ring
    have hxa : conj (ftC g (x : ℂ)) = ftC (fun t => conj (g t)) (x : ℂ) := by
      rw [conj_ftC_even heven, Complex.conj_ofReal]
    rw [rhoCoth_add_half, rhoCoth_sub_half, map_add, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul,
      c1, c2, hxa, conj_ftC_conj_even heven, conj_ftC_conj_even heven, c3, c4, ht,
      Complex.conj_ofReal]
    have := hcz x
    rw [Complex.ofReal_mul]
    linear_combination ((Real.tanh (Real.pi * x) : ℂ) * ftC (fun t => conj (g t)) (x : ℂ)) * this
  have i4' : Integrable (fun x : ℝ => rhoCoth ((x : ℂ) - I / 2) *
      (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) - I))) := by
    simp_rw [e4]; exact i4
  have hS : Integrable (fun x : ℝ => rhoCoth ((x : ℂ) + I / 2) *
      (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) + I)) + rhoCoth ((x : ℂ) - I / 2) *
      (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) - I))) := i3.add i4'
  have hψ : Integrable (fun x : ℝ => (1 / 2 : ℂ) * conj (rhoCoth ((x : ℂ) + I / 2) *
      (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) + I)) + rhoCoth ((x : ℂ) - I / 2) *
      (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) - I)))) := by
    refine Integrable.const_mul ?_ _
    refine Integrable.mono' hS.norm
      (Complex.continuous_conj.comp_aestronglyMeasurable hS.aestronglyMeasurable)
      (Eventually.of_forall fun x => (RCLike.norm_conj (K := ℂ) _).le)
  refine ⟨by simp_rw [key]; exact hψ, ?_⟩
  rw [← integral_add i3 i4']
  simp_rw [key]
  rw [integral_const_mul, integral_conj]
  have h12 : (2 : ℂ) * ((1 / 2 : ℂ) * conj (∫ x : ℝ, (rhoCoth ((x : ℂ) + I / 2) *
      (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) + I)) + rhoCoth ((x : ℂ) - I / 2) *
      (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) - I))))) =
      conj (∫ x : ℝ, (rhoCoth ((x : ℂ) + I / 2) *
      (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) + I)) + rhoCoth ((x : ℂ) - I / 2) *
      (ftC g x * ftC (fun t => conj (g t)) ((x : ℂ) - I)))) := by ring
  rw [h12, Complex.conj_conj]

lemma rhoCoth_real {ρ : ℝ} (h : ρ ≠ 0) :
    rhoCoth (ρ : ℂ) = ((ρ * (Real.cosh (Real.pi * ρ) / Real.sinh (Real.pi * ρ)) : ℝ) : ℂ) := by
  unfold rhoCoth
  have h0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast h
  simp only [h0, ite_false]
  push_cast
  ring

lemma oddHat_neg {g : ℝ → ℂ} (heven : ∀ t, g (-t) = g t) (ρ : ℝ) : oddHat g (-ρ) = oddHat g ρ := by
  unfold oddHat
  have e1 : ((-ρ : ℝ) : ℂ) - I / 2 = -((ρ : ℂ) + I / 2) := by push_cast; ring
  have e2 : ((-ρ : ℝ) : ℂ) + I / 2 = -((ρ : ℂ) - I / 2) := by push_cast; ring
  rw [e1, e2, ftC_neg_of_even heven, ftC_neg_of_even heven]
  ring

/-- **The odd Plancherel identity in `G`-form.** For `G` smooth with compact support, `g = 𝒜G` and
`ĥ(ρ) = ∫ e^{iρt} 2cosh(t/2) g(t) dt`,
`2π² ∫_{v>1} (1 + v) ‖G(v)‖² dv = ¼ ∫_{ρ>0} ρ coth(πρ) ‖ĥ(ρ)‖² dρ`. -/
theorem odd_plancherel_G {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    2 * Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), (1 + v) * ‖G v‖ ^ 2 =
      (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ), ρ * (Real.cosh (Real.pi * ρ) / Real.sinh (Real.pi * ρ)) *
        ‖oddHat (abelTransform G) ρ‖ ^ 2 := by
  have hg1 : ContDiff ℝ ∞ (abelTransform G) := contDiff_abelTransform G hG hc
  have hg2 : ContDiff ℝ 2 (abelTransform G) := hg1.of_le (by norm_cast)
  have hgc := hasCompactSupport_abelTransform G hc
  have heven : ∀ t, abelTransform G (-t) = abelTransform G t := abelTransform_neg G
  obtain ⟨C, hC, hA, hB, hmain⟩ := odd_norm_contour hg2 hgc heven
  have T12 := T12_eq hg1.continuous hgc heven hA hB
  have hvG : ContDiff ℝ ∞ (fun v : ℝ => (v : ℂ) * G v) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_id).mul hG
  have hvGc : HasCompactSupport (fun v : ℝ => (v : ℂ) * G v) := hc.mul_left
  have hcz : ∀ x : ℝ, (x : ℂ) * ftC (abelTransform fun v : ℝ => (v : ℂ) * G v) (x : ℂ) =
      (1 / 2 : ℂ) * (((x : ℂ) - I / 2) * ftC (abelTransform G) ((x : ℂ) - I) +
        ((x : ℂ) + I / 2) * ftC (abelTransform G) ((x : ℂ) + I)) := fun x => ftC_abel_mul_v hG hc x
  obtain ⟨hψint, T34⟩ := T34_eq hg1.continuous hgc heven hA hB hcz
  -- the even Plancherel integral of `G`
  have R1 : ∫ x : ℝ, x * Real.tanh (Real.pi * x) * ‖ftC (abelTransform G) (x : ℂ)‖ ^ 2 =
      8 * Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), ‖G v‖ ^ 2 := by
    have hint : Integrable fun x : ℝ => x * Real.tanh (Real.pi * x) * ‖ftC (abelTransform G) (x : ℂ)‖ ^ 2 := by
      simpa only [ftC_ofReal] using integrable_sphWeight hG hc
    have hev : ∀ x : ℝ, (-x) * Real.tanh (Real.pi * (-x)) * ‖ftC (abelTransform G) ((-x : ℝ) : ℂ)‖ ^ 2 =
        x * Real.tanh (Real.pi * x) * ‖ftC (abelTransform G) (x : ℂ)‖ ^ 2 := fun x => by
      rw [Complex.ofReal_neg, ftC_neg_of_even heven, mul_neg, Real.tanh_neg, neg_mul_neg]
    rw [integral_eq_two_mul_Ioi hev hint]
    simp_rw [ftC_ofReal]
    have E := norm_sq_eq_sph G hG hc
    rw [smul_eq_mul]
    linear_combination (-8) * E
  -- the polarised integral of `(G, vG)`
  have R2 : ∫ x : ℝ, ((x * Real.tanh (Real.pi * x) : ℝ) : ℂ) *
      (conj (ftC (abelTransform G) (x : ℂ)) * ftC (abelTransform fun v : ℝ => (v : ℂ) * G v) (x : ℂ)) =
      ((8 * Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), v * ‖G v‖ ^ 2 : ℝ) : ℂ) := by
    have hevψ : ∀ x : ℝ, ((-x * Real.tanh (Real.pi * (-x)) : ℝ) : ℂ) *
        (conj (ftC (abelTransform G) ((-x : ℝ) : ℂ)) *
          ftC (abelTransform fun v : ℝ => (v : ℂ) * G v) ((-x : ℝ) : ℂ)) =
        ((x * Real.tanh (Real.pi * x) : ℝ) : ℂ) * (conj (ftC (abelTransform G) (x : ℂ)) *
          ftC (abelTransform fun v : ℝ => (v : ℂ) * G v) (x : ℂ)) := fun x => by
      rw [Complex.ofReal_neg, ftC_neg_of_even heven,
        ftC_neg_of_even (abelTransform_neg fun v : ℝ => (v : ℂ) * G v), mul_neg, Real.tanh_neg, neg_mul_neg]
    rw [integral_eq_two_mul_Ioi hevψ hψint]
    have Ep := sph_polarized hG hc hvG hvGc
    simp_rw [← ftC_ofReal] at Ep
    have hI : ∀ v : ℝ, conj (G v) * ((v : ℂ) * G v) = ((v * ‖G v‖ ^ 2 : ℝ) : ℂ) := fun v => by
      rw [Complex.ofReal_mul, cast_norm_sq]; ring
    simp_rw [hI] at Ep
    rw [integral_complex_ofReal] at Ep
    have hR : ((8 * Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), v * ‖G v‖ ^ 2 : ℝ) : ℂ) =
        8 * (Real.pi : ℂ) ^ 2 * ((∫ v in Ioi (1 : ℝ), v * ‖G v‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hR, Complex.real_smul, Complex.ofReal_ofNat]
    linear_combination (-8 : ℂ) * Ep
  -- assemble
  rw [add_assoc, T12, T34, R1, R2] at hmain
  -- the real density on the half line
  set r : ℝ → ℝ := fun ρ => ρ * (Real.cosh (Real.pi * ρ) / Real.sinh (Real.pi * ρ)) *
    ‖oddHat (abelTransform G) ρ‖ ^ 2 with hr
  have hae : (fun ρ : ℝ => rhoCoth (ρ : ℂ) * ((‖oddHat (abelTransform G) ρ‖ ^ 2 : ℝ) : ℂ)) =ᵐ[volume]
      fun ρ => ((r ρ : ℝ) : ℂ) := by
    filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with ρ hρ
    rw [rhoCoth_real (by simpa using hρ), ← Complex.ofReal_mul]
  have hb1 : ∀ ρ : ℝ, ‖ftC (abelTransform G) ((ρ : ℂ) - I / 2)‖ ≤ C / (1 + ρ ^ 2) := fun ρ => by
    have := hA ρ (-1 / 2) (by norm_num [abs_div])
    rwa [show (ρ : ℂ) + ((-1 / 2 : ℝ) : ℂ) * I = (ρ : ℂ) - I / 2 by push_cast; ring] at this
  have hb2 : ∀ ρ : ℝ, ‖ftC (abelTransform G) ((ρ : ℂ) + I / 2)‖ ≤ C / (1 + ρ ^ 2) := fun ρ => by
    have := hA ρ (1 / 2) (by norm_num [abs_div])
    rwa [show (ρ : ℂ) + ((1 / 2 : ℝ) : ℂ) * I = (ρ : ℂ) + I / 2 by push_cast; ring] at this
  have hhat : ∀ ρ : ℝ, ‖oddHat (abelTransform G) ρ‖ ≤ (2 * C) / (1 + ρ ^ 2) := fun ρ => by
    unfold oddHat
    calc _ ≤ ‖ftC (abelTransform G) ((ρ : ℂ) - I / 2)‖ + ‖ftC (abelTransform G) ((ρ : ℂ) + I / 2)‖ :=
          norm_add_le _ _
      _ ≤ C / (1 + ρ ^ 2) + C / (1 + ρ ^ 2) := add_le_add (hb1 ρ) (hb2 ρ)
      _ = (2 * C) / (1 + ρ ^ 2) := by ring
  have hhcont : Continuous fun ρ : ℝ => oddHat (abelTransform G) ρ := by
    have hf := (differentiable_ftC hg1.continuous hgc).continuous
    exact (hf.comp (Complex.continuous_ofReal.sub continuous_const)).add
      (hf.comp (Complex.continuous_ofReal.add continuous_const))
  have hI : Integrable fun ρ : ℝ => rhoCoth (ρ : ℂ) * ((‖oddHat (abelTransform G) ρ‖ ^ 2 : ℝ) : ℂ) := by
    refine integrable_rhoCoth_mul (C := (2 * C) ^ 2)
      (Complex.continuous_ofReal.comp ((hhcont.norm).pow 2)) fun ρ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    calc ‖oddHat (abelTransform G) ρ‖ ^ 2 ≤ ((2 * C) / (1 + ρ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hhat ρ) 2
      _ = (2 * C) ^ 2 / (1 + ρ ^ 2) ^ 2 := div_pow _ _ _
  have hr_int : Integrable r := by
    refine (hI.re).congr ?_
    filter_upwards [hae] with ρ h
    simp only [h, RCLike.re_to_complex, Complex.ofReal_re]
  have hrev : ∀ ρ : ℝ, r (-ρ) = r ρ := fun ρ => by
    simp only [hr]
    rw [mul_neg, Real.cosh_neg, Real.sinh_neg, div_neg, neg_mul_neg, oddHat_neg heven]
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  have hfin : ((2 * ∫ ρ in Ioi (0 : ℝ), r ρ : ℝ) : ℂ) =
      ((2 * (8 * Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), ‖G v‖ ^ 2) +
        2 * (8 * Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), v * ‖G v‖ ^ 2) : ℝ) : ℂ) := by
    calc ((2 * ∫ ρ in Ioi (0 : ℝ), r ρ : ℝ) : ℂ) = ((∫ ρ : ℝ, r ρ : ℝ) : ℂ) := by
          rw [integral_eq_two_mul_Ioi hrev hr_int, smul_eq_mul]
      _ = ∫ ρ : ℝ, ((r ρ : ℝ) : ℂ) := integral_complex_ofReal.symm
      _ = ∫ ρ : ℝ, rhoCoth (ρ : ℂ) * ((‖oddHat (abelTransform G) ρ‖ ^ 2 : ℝ) : ℂ) :=
          (integral_congr_ae hae).symm
      _ = _ := hmain
      _ = _ := by
          rw [map_mul, h2, Complex.conj_ofReal]
          simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hreal := Complex.ofReal_injective hfin
  have hcs1 : HasCompactSupport fun v : ℝ => ‖G v‖ ^ 2 :=
    hc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hi1 : IntegrableOn (fun v : ℝ => ‖G v‖ ^ 2) (Ioi (1 : ℝ)) :=
    ((hG.continuous.norm.pow 2).integrable_of_hasCompactSupport hcs1).integrableOn
  have hi2 : IntegrableOn (fun v : ℝ => v * ‖G v‖ ^ 2) (Ioi (1 : ℝ)) :=
    (continuous_id.mul (hG.continuous.norm.pow 2)).integrable_of_hasCompactSupport hcs1.mul_left
      |>.integrableOn
  have hI12 : ∫ v in Ioi (1 : ℝ), (1 + v) * ‖G v‖ ^ 2 =
      (∫ v in Ioi (1 : ℝ), ‖G v‖ ^ 2) + ∫ v in Ioi (1 : ℝ), v * ‖G v‖ ^ 2 := by
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    ring
  rw [hI12]
  linear_combination (-1 / 8 : ℝ) * hreal

end Lightlike.Lorentz.SL2ROddPlancherel
