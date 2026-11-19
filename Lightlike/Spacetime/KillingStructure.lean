import Lightlike.Spacetime.KillingAlgebraCoord
import Lightlike.Spacetime.KillingOrbitChart

/-!
# The structure constants of a maximally symmetric 3-metric (G1-024, stage 1)

In coordinates on an open set of `ℝ³`, a family of Killing fields indexed like the Killing algebra of the space form
(`SpaceForm.Idx`) is *normalized at `p`* when the translations `Pₘ` are transvections with `Pₘ(p) = eₘ`, `∇Pₘ(p) = 0`,
and the rotations vanish at `p` with `∇R_ab(p)` the generator `so3Gen a b` of `so(3)`.

* `so3Gen`, `so3_equivariant_eq_smul`: an `so(3)`-equivariant map of antisymmetric `3 × 3` arrays is a multiple of the
  identity (Schur's lemma, by eight instances of the equivariance);
* `sum_S_inl_inl`, `sum_S_inl_inr`, `sum_S_inr_inl`, `sum_S_inr_inr`: the combinations `Σₑ S k i j e f(e)`;
* `frameVal`, `frameCov`, `frame_val_S`, `frame_cov_S`: the data at `p` of the normalized family, and its bracket data
  against `SpaceForm.S k` when the curvature at `p` is isotropic;
* `NormalizedKillingFrame`, `NormalizedKillingFrame.metric_eq`: a family of Killing fields normalized at `p` (the
  metric at `p` is then `g₀₀(p) · 1`); `NormalizedKillingFrame.lieBracket_eq_S`: its brackets are
  `[Yᵢ, Yⱼ] = Σₑ S k i j e Yₑ` on a connected open set once `Rⁿ_{amb} - Rᵐ_{anb} = -k (so3Gen m n)_{ab}` at `p`;
* `NormalizedKillingFrame.isotropic`: that isotropy holds for some `k`, from the Leibniz identity
  `[R_ab, [Pₘ, Pₙ]] = [[R_ab, Pₘ], Pₙ] + [Pₘ, [R_ab, Pₙ]]` read through the data at `p` and Schur's lemma;
  `NormalizedKillingFrame.exists_lieBracket_eq_S`: so a normalized family has the brackets of the space form of some
  curvature `k`;
* `bilBasis`, `coordBil`, `coordBil_apply`, `hasFDerivAt_coordBil`, `fderiv_coordBil_apply`, `coordBil_lie`: the bilinear
  form of a coordinate metric, and Killing's equation in the form of `isometric_spaceForm` as the coordinate Lie
  derivative;
* `NormalizedKillingFrame.isometric`: on a ball around `p`, the metric is, in orbit charts, `g₀₀(p)` times the space
  form of some curvature `k` (`isometric_spaceForm`).
-/

open Set Filter
open scoped ContDiff Topology

namespace Lightlike

open SpaceForm

/-- The generator of `so(3)` in the plane `(a, b)`: `(so3Gen a b)_{dl} = δ_da δ_lb - δ_db δ_la`. -/
def so3Gen (a b d l : Fin 3) : ℝ :=
  (if d = a then 1 else 0) * (if l = b then 1 else 0) - (if d = b then 1 else 0) * (if l = a then 1 else 0)

/-- **Schur's lemma for `so(3)`**: a map `M` of antisymmetric arrays, antisymmetric in each pair, that commutes with the
action of the generators (`hJ`) is a multiple of the identity, `M m n a b = M 0 1 0 1 · (so3Gen m n)_{ab}`. -/
theorem so3_equivariant_eq_smul (M : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hMa : ∀ m n a b, M n m a b = -M m n a b) (hMb : ∀ m n a b, M m n b a = -M m n a b)
    (hJ : ∀ a b m n a' b', ∑ d, (so3Gen a b a' d * M m n d b' - M m n a' d * so3Gen a b d b') =
      -(∑ d, so3Gen a b m d * M d n a' b') - ∑ d, so3Gen a b n d * M m d a' b') :
    ∀ m n a b, M m n a b = M 0 1 0 1 * so3Gen m n a b := by
  have n1 : ∀ a b, M 1 0 a b = -M 0 1 a b := fun a b => hMa 0 1 a b
  have n2 : ∀ a b, M 2 0 a b = -M 0 2 a b := fun a b => hMa 0 2 a b
  have n3 : ∀ a b, M 2 1 a b = -M 1 2 a b := fun a b => hMa 1 2 a b
  have d0 : ∀ i a b, M i i a b = 0 := fun i a b => by linarith [hMa i i a b]
  have e1 : ∀ m n, M m n 1 0 = -M m n 0 1 := fun m n => hMb m n 0 1
  have e2 : ∀ m n, M m n 2 0 = -M m n 0 2 := fun m n => hMb m n 0 2
  have e3 : ∀ m n, M m n 2 1 = -M m n 1 2 := fun m n => hMb m n 1 2
  have z0 : ∀ m n i, M m n i i = 0 := fun m n i => by linarith [hMb m n i i]
  have f1 := hJ 0 1 0 1 1 2
  have f2 := hJ 0 1 0 1 0 2
  have f3 := hJ 0 1 1 2 0 1
  have f4 := hJ 1 2 0 1 0 2
  have f5 := hJ 0 2 0 2 0 1
  have f6 := hJ 0 1 0 2 0 1
  have f7 := hJ 0 2 0 1 0 2
  have f8 := hJ 0 2 0 1 1 2
  simp [so3Gen, n3, d0, e1, e3, z0] at f1 f2 f3 f4 f5 f6 f7 f8
  intro m n a b
  fin_cases m <;> fin_cases n <;> fin_cases a <;> fin_cases b <;>
    simp [so3Gen, n1, n2, n3, d0, e1, e2, e3, z0] <;> linarith

theorem sum_ind_mul (f : Idx → ℝ) (e₀ : Idx) : ∑ e, ind e e₀ * f e = f e₀ := by
  rw [Finset.sum_eq_single e₀ (fun e _ he => by simp [ind, he]) (by simp)]
  simp [ind]

theorem sum_S_inl_inl (k : ℝ) (f : Idx → ℝ) (m n : Fin 3) :
    ∑ e, S k (.inl m) (.inl n) e * f e = -k * f (.inr (m, n)) := by
  simp only [S, mul_assoc, ← Finset.mul_sum, sum_ind_mul]

theorem sum_S_inl_inr (k : ℝ) (f : Idx → ℝ) (m : Fin 3) (ab : Fin 3 × Fin 3) :
    ∑ e, S k (.inl m) (.inr ab) e * f e =
      (if m = ab.1 then f (.inl ab.2) else 0) - (if m = ab.2 then f (.inl ab.1) else 0) := by
  simp only [S, sub_mul, Finset.sum_sub_distrib]
  split_ifs <;> simp only [sum_ind_mul, zero_mul, Finset.sum_const_zero]

theorem sum_S_inr_inl (k : ℝ) (f : Idx → ℝ) (ab : Fin 3 × Fin 3) (m : Fin 3) :
    ∑ e, S k (.inr ab) (.inl m) e * f e =
      (if m = ab.2 then f (.inl ab.1) else 0) - (if m = ab.1 then f (.inl ab.2) else 0) := by
  simp only [S, sub_mul, Finset.sum_sub_distrib]
  split_ifs <;> simp only [sum_ind_mul, zero_mul, Finset.sum_const_zero]

theorem sum_S_inr_inr (k : ℝ) (f : Idx → ℝ) (ab cd : Fin 3 × Fin 3) :
    ∑ e, S k (.inr ab) (.inr cd) e * f e =
      -((if ab.1 = cd.2 then f (.inr (cd.1, ab.2)) else 0) - (if ab.1 = cd.1 then f (.inr (cd.2, ab.2)) else 0) -
        (if ab.2 = cd.2 then f (.inr (cd.1, ab.1)) else 0) + (if ab.2 = cd.1 then f (.inr (cd.2, ab.1)) else 0)) := by
  simp only [S, neg_mul, Finset.sum_neg_distrib, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  split_ifs <;> simp only [sum_ind_mul, zero_mul, Finset.sum_const_zero]

/-- The integer generator, for deciding identities of `so3Gen`. -/
def so3GenZ (a b d l : Fin 3) : ℤ :=
  (if d = a then 1 else 0) * (if l = b then 1 else 0) - (if d = b then 1 else 0) * (if l = a then 1 else 0)

theorem so3Gen_eq_cast (a b d l : Fin 3) : so3Gen a b d l = (so3GenZ a b d l : ℝ) := by
  unfold so3Gen so3GenZ; push_cast; rfl

theorem so3GenZ_comm : ∀ a₁ a₂ c₁ c₂ a b : Fin 3,
    so3GenZ a₁ a₂ a 0 * so3GenZ c₁ c₂ 0 b - so3GenZ c₁ c₂ a 0 * so3GenZ a₁ a₂ 0 b +
        (so3GenZ a₁ a₂ a 1 * so3GenZ c₁ c₂ 1 b - so3GenZ c₁ c₂ a 1 * so3GenZ a₁ a₂ 1 b) +
        (so3GenZ a₁ a₂ a 2 * so3GenZ c₁ c₂ 2 b - so3GenZ c₁ c₂ a 2 * so3GenZ a₁ a₂ 2 b) =
      -((if a₁ = c₂ then so3GenZ c₁ a₂ a b else 0) - (if a₁ = c₁ then so3GenZ c₂ a₂ a b else 0) -
        (if a₂ = c₂ then so3GenZ c₁ a₁ a b else 0) + (if a₂ = c₁ then so3GenZ c₂ a₁ a b else 0)) := by
  unfold so3GenZ; decide

/-- **The commutator of two generators of `so(3)`**, in the convention of `SpaceForm.S`:
`[so3Gen a₁ a₂, so3Gen c₁ c₂] = -(δ_{a₁c₂} so3Gen c₁ a₂ - δ_{a₁c₁} so3Gen c₂ a₂ - δ_{a₂c₂} so3Gen c₁ a₁ + δ_{a₂c₁} so3Gen c₂ a₁)`. -/
theorem so3Gen_comm (a₁ a₂ c₁ c₂ a b : Fin 3) :
    ∑ d, (so3Gen a₁ a₂ a d * so3Gen c₁ c₂ d b - so3Gen c₁ c₂ a d * so3Gen a₁ a₂ d b) =
      -((if a₁ = c₂ then so3Gen c₁ a₂ a b else 0) - (if a₁ = c₁ then so3Gen c₂ a₂ a b else 0) -
        (if a₂ = c₂ then so3Gen c₁ a₁ a b else 0) + (if a₂ = c₁ then so3Gen c₂ a₁ a b else 0)) := by
  have h := congrArg (Int.cast : ℤ → ℝ) (so3GenZ_comm a₁ a₂ c₁ c₂ a b)
  push_cast [apply_ite (Int.cast : ℤ → ℝ)] at h
  simp only [Fin.sum_univ_three, so3Gen_eq_cast]
  rw [h]

theorem sum_single_one_mul (i : Fin 3) (F : Fin 3 → ℝ) :
    ∑ e, (Pi.single i 1 : Fin 3 → ℝ) e * F e = F i := by
  simp [Pi.single_apply]

theorem sum_mul_single_one (i : Fin 3) (F : Fin 3 → ℝ) :
    ∑ e, F e * (Pi.single i 1 : Fin 3 → ℝ) e = F i := by
  simp [Pi.single_apply]

/-- The value at `p` of the normalized family: `Pₘ(p) = eₘ`, `R_ab(p) = 0`. -/
def frameVal : Idx → Fin 3 → ℝ
  | .inl m => Pi.single m 1
  | .inr _ => 0

/-- The covariant derivative at `p` of the normalized family: `∇Pₘ(p) = 0`, `∇R_ab(p) = so3Gen a b`. -/
def frameCov : Idx → Fin 3 → Fin 3 → ℝ
  | .inl _ => fun _ _ => 0
  | .inr ab => so3Gen ab.1 ab.2

/-- **The bracket values of the normalized data are those of `S k`**: `Yᵢᵈ ∇_d Yⱼᵇ - Yⱼᵈ ∇_d Yᵢᵇ = Σₑ S k i j e Yₑᵇ` at
`p`. -/
theorem frame_val_S (k : ℝ) (i j : Idx) (b : Fin 3) :
    ∑ d, (frameVal i d * frameCov j d b - frameVal j d * frameCov i d b) = ∑ e, S k i j e * frameVal e b := by
  rcases i with m | ⟨a, a'⟩ <;> rcases j with n | ⟨c, c'⟩
  · rw [sum_S_inl_inl]; simp [frameVal, frameCov]
  · rw [sum_S_inl_inr]; simp [frameVal, frameCov, Pi.single_apply, so3Gen]; split_ifs <;> simp_all
  · rw [sum_S_inr_inl]; simp [frameVal, frameCov, Pi.single_apply, so3Gen]; split_ifs <;> simp_all
  · rw [sum_S_inr_inr]; simp [frameVal, frameCov]

/-- **The bracket derivatives of the normalized data are those of `S k`** when the curvature at `p` is isotropic,
`Rⁿ_{amb} - Rᵐ_{anb} = -k (so3Gen m n)_{ab}`: `[∇Yᵢ, ∇Yⱼ] + Riem(Yᵢ, Yⱼ) = Σₑ S k i j e ∇Yₑ` at `p`. -/
theorem frame_cov_S (k : ℝ) (Rm : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hiso : ∀ m n a b, Rm n a m b - Rm m a n b = -k * so3Gen m n a b) (i j : Idx) (a b : Fin 3) :
    ∑ d, (frameCov i a d * frameCov j d b - frameCov j a d * frameCov i d b) +
        ∑ d, ∑ e, (frameVal i d * Rm e a d b * frameVal j e - frameVal j d * Rm e a d b * frameVal i e) =
      ∑ e, S k i j e * frameCov e a b := by
  rcases i with m | ⟨a₁, a₂⟩ <;> rcases j with n | ⟨c₁, c₂⟩
  · rw [sum_S_inl_inl]
    simp only [frameVal, frameCov, Pi.single_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
      sub_self, Finset.sum_const_zero, zero_add]
    rw [← hiso m n a b]
    simp
  · rw [sum_S_inl_inr]; simp [frameVal, frameCov]
  · rw [sum_S_inr_inl]; simp [frameVal, frameCov]
  · rw [sum_S_inr_inr]
    simp only [frameVal, frameCov, Pi.zero_apply, zero_mul, mul_zero, sub_self, Finset.sum_const_zero, add_zero]
    exact so3Gen_comm a₁ a₂ c₁ c₂ a b

/-- **A family of Killing fields normalized at `p`**, indexed like the Killing algebra of the space form: on an open
set `U` of coordinates, `g` is a metric, the fields are smooth and Killing (`∇_a θ_b + ∇_b θ_a = 0` for `θ = Y♭`), and
their data at `p` is `(Yᵢ(p), ∇Yᵢ(p)) = (frameVal i, frameCov i)`: transvections `Pₘ(p) = eₘ`, `∇Pₘ(p) = 0`, and
rotations `R_ab(p) = 0`, `∇R_ab(p) = so3Gen a b`. -/
structure NormalizedKillingFrame (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (U : Set (Fin 3 → ℝ))
    (Y : Idx → (Fin 3 → ℝ) → Fin 3 → ℝ) (p : Fin 3 → ℝ) : Prop where
  metric : IsCoordMetric g U
  symm : ∀ z a b, g z a b = g z b a
  mem : p ∈ U
  smooth : ∀ i c, ContDiffOn ℝ ∞ (fun z => Y i z c) U
  killing : ∀ i, ∀ z ∈ U, ∀ a b, covCo g (lowerVec g (Y i)) a b z + covCo g (lowerVec g (Y i)) b a z = 0
  val : ∀ i, Y i p = frameVal i
  cov : ∀ i a d, covVec g (Y i) a d p = frameCov i a d

namespace NormalizedKillingFrame

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {U : Set (Fin 3 → ℝ)} {Y : Idx → (Fin 3 → ℝ) → Fin 3 → ℝ}
  {p : Fin 3 → ℝ}

theorem diff (h : NormalizedKillingFrame g U Y p) {V : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hV : ∀ c, ContDiffOn ℝ ∞ (fun z => V z c) U) (c : Fin 3) : DifferentiableAt ℝ (fun z => V z c) p :=
  differentiableAt_of_contDiffOn (hV c) h.metric.isOpen h.mem

theorem metric_diff (h : NormalizedKillingFrame g U Y p) (a b : Fin 3) :
    DifferentiableAt ℝ (fun z => g z a b) p :=
  differentiableAt_of_contDiffOn (h.metric.smooth a b) h.metric.isOpen h.mem

/-- **The rotations make the metric at `p` a multiple of the identity**: `g(p) = g₀₀(p) · 1` (Killing's equation for
`R_ab` at `p` says `g(p)` is skew for each generator). -/
theorem metric_eq (h : NormalizedKillingFrame g U Y p) : g p = g p 0 0 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hdet := (h.metric.isUnit_det p h.mem).ne_zero
  have hc : ∀ a b d b', covCo g (lowerVec g (Y (.inr (a, b)))) d b' p =
      g p b' b * (if d = a then 1 else 0) - g p b' a * (if d = b then 1 else 0) := by
    intro a b d b'
    rw [covCo_lowerVec h.symm hdet h.metric_diff (h.diff (h.smooth _)) d b']
    have e : ∀ l, pd d (fun z => Y (.inr (a, b)) z l) p + ∑ c, christoffel g l d c p * Y (.inr (a, b)) p c =
        so3Gen a b d l := fun l => h.cov (.inr (a, b)) d l
    simp only [e, so3Gen, mul_sub, Finset.sum_sub_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have off : ∀ a b, a ≠ b → g p a b = 0 := fun a b hab => by
    have := h.killing (.inr (a, b)) p h.mem a a
    rw [hc] at this
    simp [hab] at this
    linarith [h.symm p a b]
  have dia : ∀ a b, a ≠ b → g p a a = g p b b := fun a b hab => by
    have := h.killing (.inr (a, b)) p h.mem a b
    rw [hc, hc] at this
    simp [hab, Ne.symm hab] at this
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> first | exact off _ _ (by decide) | exact dia _ _ (by decide)

theorem metric_ne_zero (h : NormalizedKillingFrame g U Y p) : g p 0 0 ≠ 0 := by
  have hdet := (h.metric.isUnit_det p h.mem).ne_zero
  rw [h.metric_eq, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  exact pow_ne_zero_iff (by norm_num) |>.1 hdet

/-- The value at `p` of the bracket of two smooth fields with given data at `p`. -/
theorem bracket_val (h : NormalizedKillingFrame g U Y p) {V W : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {vV vW : Fin 3 → ℝ} {AV AW : Fin 3 → Fin 3 → ℝ} (hvV : V p = vV) (hvW : W p = vW)
    (hAV : ∀ a d, covVec g V a d p = AV a d) (hAW : ∀ a d, covVec g W a d p = AW a d) (b : Fin 3) :
    bracketCo V W p b = ∑ d, (vV d * AW d b - vW d * AV d b) := by
  rw [bracketCo_eq_covVec h.symm]
  simp only [hvV, hvW, hAV, hAW]

/-- The covariant derivative at `p` of the bracket of two smooth Killing fields with given data at `p`. -/
theorem bracket_cov (h : NormalizedKillingFrame g U Y p) {V W : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hV : ∀ c, ContDiffOn ℝ ∞ (fun z => V z c) U) (hW : ∀ c, ContDiffOn ℝ ∞ (fun z => W z c) U)
    (hKV : ∀ z ∈ U, ∀ a b, covCo g (lowerVec g V) a b z + covCo g (lowerVec g V) b a z = 0)
    (hKW : ∀ z ∈ U, ∀ a b, covCo g (lowerVec g W) a b z + covCo g (lowerVec g W) b a z = 0)
    {vV vW : Fin 3 → ℝ} {AV AW : Fin 3 → Fin 3 → ℝ} (hvV : V p = vV) (hvW : W p = vW)
    (hAV : ∀ a d, covVec g V a d p = AV a d) (hAW : ∀ a d, covVec g W a d p = AW a d) (a b : Fin 3) :
    covVec g (bracketCo V W) a b p =
      ∑ d, (AV a d * AW d b - AW a d * AV d b) +
        ∑ d, ∑ e, (vV d * riemann g e a d b p * vW e - vW d * riemann g e a d b p * vV e) := by
  rw [covVec_bracketCo h.metric h.symm hV hW hKV hKW h.mem h.metric_eq h.metric_ne_zero]
  simp only [hvV, hvW, hAV, hAW]

/-- **The brackets of a normalized family are those of the space form** once the curvature at `p` is isotropic:
`[Yᵢ, Yⱼ] = Σₑ S k i j e Yₑ` on a connected `U`. -/
theorem lieBracket_eq_S (h : NormalizedKillingFrame g U Y p) (hU : IsPreconnected U) (k : ℝ)
    (hiso : ∀ m n a b, riemann g n a m b p - riemann g m a n b p = -k * so3Gen m n a b) (i j : Idx) :
    ∀ w ∈ U, VectorField.lieBracket ℝ (Y i) (Y j) w = ∑ e, S k i j e • Y e w := by
  have hdet := (h.metric.isUnit_det p h.mem).ne_zero
  have hcp := h.metric_eq
  refine lieBracket_eq_sum_of_data h.metric h.symm hU Y (h.smooth i) (h.smooth j) h.smooth (h.killing i)
    (h.killing j) h.killing h.mem (S k i j) (fun b => ?_) (fun a b => ?_)
  · rw [lowerVec_of_eq_smul_one hcp, h.bracket_val (h.val i) (h.val j) (h.cov i) (h.cov j), frame_val_S k,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [lowerVec_of_eq_smul_one hcp, h.val e]; ring
  · rw [covCo_lowerVec_of_eq_smul_one h.symm hdet h.metric_diff
      (h.diff (contDiffOn_bracketCo h.metric.isOpen (h.smooth i) (h.smooth j))) hcp,
      h.bracket_cov (h.smooth i) (h.smooth j) (h.killing i) (h.killing j) (h.val i) (h.val j) (h.cov i) (h.cov j),
      frame_cov_S k (fun e a d b => riemann g e a d b p) hiso, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by
      rw [covCo_lowerVec_of_eq_smul_one h.symm hdet h.metric_diff (h.diff (h.smooth e)) hcp, h.cov e]; ring


/-- **The curvature at `p` of a normalized family is isotropic**: `Rⁿ_{amb} - Rᵐ_{anb} = -k (so3Gen m n)_{ab}` for some
`k`. The Leibniz identity `[R_ab, [Pₘ, Pₙ]] = [[R_ab, Pₘ], Pₙ] + [Pₘ, [R_ab, Pₙ]]`, read through the data at `p`, says
the map `(m, n) ↦ ∇[Pₘ, Pₙ](p)` commutes with `so(3)`; Schur's lemma (`so3_equivariant_eq_smul`) does the rest. -/
theorem isotropic (h : NormalizedKillingFrame g U Y p) :
    ∃ k : ℝ, ∀ m n a b, riemann g n a m b p - riemann g m a n b p = -k * so3Gen m n a b := by
  set M : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun m n a b => riemann g n a m b p - riemann g m a n b p with hM
  have hdet := (h.metric.isUnit_det p h.mem).ne_zero
  have hs := h.smooth
  have hk := h.killing
  have hO := h.metric.isOpen
  have sB : ∀ V W : (Fin 3 → ℝ) → Fin 3 → ℝ, (∀ c, ContDiffOn ℝ ∞ (fun z => V z c) U) →
      (∀ c, ContDiffOn ℝ ∞ (fun z => W z c) U) → ∀ c, ContDiffOn ℝ ∞ (fun z => bracketCo V W z c) U :=
    fun V W hV hW => contDiffOn_bracketCo hO hV hW
  have kB : ∀ V W : (Fin 3 → ℝ) → Fin 3 → ℝ, (∀ c, ContDiffOn ℝ ∞ (fun z => V z c) U) →
      (∀ c, ContDiffOn ℝ ∞ (fun z => W z c) U) →
      (∀ z ∈ U, ∀ a b, covCo g (lowerVec g V) a b z + covCo g (lowerVec g V) b a z = 0) →
      (∀ z ∈ U, ∀ a b, covCo g (lowerVec g W) a b z + covCo g (lowerVec g W) b a z = 0) →
      ∀ z ∈ U, ∀ a b, covCo g (lowerVec g (bracketCo V W)) a b z + covCo g (lowerVec g (bracketCo V W)) b a z = 0 :=
    fun V W hV hW hKV hKW => killing_bracketCo h.metric h.symm hV hW hKV hKW
  have Qv : ∀ m n, bracketCo (Y (.inl m)) (Y (.inl n)) p = 0 := fun m n => funext fun b => by
    rw [h.bracket_val (h.val _) (h.val _) (h.cov _) (h.cov _)]; simp [frameVal, frameCov]
  have Qc : ∀ m n a b, covVec g (bracketCo (Y (.inl m)) (Y (.inl n))) a b p = M m n a b := fun m n a b => by
    rw [h.bracket_cov (hs _) (hs _) (hk _) (hk _) (h.val _) (h.val _) (h.cov _) (h.cov _)]
    simp [frameVal, frameCov, Pi.single_apply, hM]
  have Wv : ∀ a b m, bracketCo (Y (.inr (a, b))) (Y (.inl m)) p = fun l => -so3Gen a b m l :=
    fun a b m => funext fun l => by
      rw [h.bracket_val (h.val _) (h.val _) (h.cov _) (h.cov _)]; simp [frameVal, frameCov, Pi.single_apply]
  have Wc : ∀ a b m a' b', covVec g (bracketCo (Y (.inr (a, b))) (Y (.inl m))) a' b' p = 0 := fun a b m a' b' => by
    rw [h.bracket_cov (hs _) (hs _) (hk _) (hk _) (h.val _) (h.val _) (h.cov _) (h.cov _)]; simp [frameVal, frameCov]
  have hMb : ∀ m n a b, M m n b a = -M m n a b := fun m n a b => by
    have := kB _ _ (hs (.inl m)) (hs (.inl n)) (hk _) (hk _) p h.mem a b
    rw [covCo_lowerVec_of_eq_smul_one h.symm hdet h.metric_diff (h.diff (sB _ _ (hs _) (hs _))) h.metric_eq,
      covCo_lowerVec_of_eq_smul_one h.symm hdet h.metric_diff (h.diff (sB _ _ (hs _) (hs _))) h.metric_eq,
      Qc, Qc, ← mul_add] at this
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 h.metric_ne_zero
    · linarith
  have hJ : ∀ a b m n a' b', ∑ d, (so3Gen a b a' d * M m n d b' - M m n a' d * so3Gen a b d b') =
      -(∑ d, so3Gen a b m d * M d n a' b') - ∑ d, so3Gen a b n d * M m d a' b' := by
    intro a b m n a' b'
    have sQ := sB _ _ (hs (.inl m)) (hs (.inl n))
    have kQ := kB _ _ (hs (.inl m)) (hs (.inl n)) (hk _) (hk _)
    have sW := sB _ _ (hs (.inr (a, b))) (hs (.inl m))
    have kW := kB _ _ (hs (.inr (a, b))) (hs (.inl m)) (hk _) (hk _)
    have sW' := sB _ _ (hs (.inr (a, b))) (hs (.inl n))
    have kW' := kB _ _ (hs (.inr (a, b))) (hs (.inl n)) (hk _) (hk _)
    have hL := covVec_of_eqOn_add (g := g) hO h.mem (h.diff (sB _ _ sW (hs (.inl n))))
      (h.diff (sB _ _ (hs (.inl m)) sW'))
      (fun z hz => bracketCo_leibniz hO (hs (.inr (a, b))) (hs (.inl m)) (hs (.inl n)) hz) a' b'
    rw [h.bracket_cov (hs (.inr (a, b))) sQ (hk _) kQ (h.val _) (Qv m n) (h.cov _) (Qc m n),
      h.bracket_cov sW (hs (.inl n)) kW (hk _) (Wv a b m) (h.val _) (Wc a b m) (h.cov _),
      h.bracket_cov (hs (.inl m)) sW' (hk _) kW' (h.val _) (Wv a b n) (h.cov _) (Wc a b n)] at hL
    simp only [frameVal, frameCov, Pi.zero_apply, zero_mul, mul_zero, sub_self,
      Finset.sum_const_zero, add_zero, zero_add, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum,
      sum_single_one_mul, sum_mul_single_one] at hL
    simp only [hM, Fin.sum_univ_three] at hL ⊢
    linear_combination hL
  obtain hS := so3_equivariant_eq_smul M (fun m n a b => by simp only [hM]; ring) hMb hJ
  exact ⟨-M 0 1 0 1, fun m n a b => by rw [neg_neg]; exact hS m n a b⟩


/-- **G1-024, stage 1: the structure constants of a maximally symmetric 3-metric.** A family of Killing fields of a
metric on a connected open set of `ℝ³`, normalized at a point `p` like the Killing algebra of a space form, has the
brackets of the space form of some curvature `k`: `[Yᵢ, Yⱼ] = Σₑ S k i j e Yₑ` on `U`. -/
theorem exists_lieBracket_eq_S (h : NormalizedKillingFrame g U Y p) (hU : IsPreconnected U) :
    ∃ k : ℝ, ∀ i j, ∀ w ∈ U, VectorField.lieBracket ℝ (Y i) (Y j) w = ∑ e, S k i j e • Y e w := by
  obtain ⟨k, hk⟩ := h.isotropic
  exact ⟨k, h.lieBracket_eq_S hU k hk⟩

end NormalizedKillingFrame


section Bilinear

/-- The basis bilinear form `(u, w) ↦ u_a w_b` on `ℝ³`. -/
noncomputable def bilBasis (a b : Fin 3) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) a).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) b)

@[simp] theorem bilBasis_apply (a b : Fin 3) (u w : Fin 3 → ℝ) : bilBasis a b u w = u a * w b := by
  simp [bilBasis]

/-- The bilinear form `G(y)(u, w) = Σ_{ab} g_{ab}(y) u_a w_b` of a coordinate metric on `ℝ³`. -/
noncomputable def coordBil (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (y : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ a, ∑ b, g y a b • bilBasis a b

theorem coordBil_apply (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (y u w : Fin 3 → ℝ) :
    coordBil g y u w = ∑ a, ∑ b, g y a b * u a * w b := by
  simp only [coordBil, sum_apply, smul_apply, bilBasis_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

set_option maxSynthPendingDepth 3 in
theorem hasFDerivAt_coordBil {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {y : Fin 3 → ℝ}
    (hgd : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y) :
    HasFDerivAt (coordBil g) (∑ a, ∑ b, (fderiv ℝ (fun z => g z a b) y).smulRight (bilBasis a b)) y := by
  have : coordBil g = fun z => ∑ a, ∑ b, g z a b • bilBasis a b := rfl
  rw [this]
  exact HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ => (hgd a b).hasFDerivAt.smul_const (bilBasis a b)

theorem fderiv_coordBil_apply {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {y : Fin 3 → ℝ}
    (hgd : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y) (v u w : Fin 3 → ℝ) :
    fderiv ℝ (coordBil g) y v u w = ∑ a, ∑ b, (∑ c, v c * pd c (fun z => g z a b) y) * u a * w b := by
  rw [(hasFDerivAt_coordBil hgd).fderiv]
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    bilBasis_apply, smul_eq_mul, fderiv_eq_sum_pd]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **Killing's equation in the form of `isometric_spaceForm` is the coordinate Lie derivative**:
`DG(y)(Y)(u, w) + G(y)(DY u, w) + G(y)(u, DY w) = Σ_{ab} u_a w_b (L_Y g)_{ab}`. -/
theorem coordBil_lie {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {y : Fin 3 → ℝ} {Y : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hgd : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y) (hY : DifferentiableAt ℝ Y y) (u w : Fin 3 → ℝ) :
    fderiv ℝ (coordBil g) y (Y y) u w + coordBil g y (fderiv ℝ Y y u) w + coordBil g y u (fderiv ℝ Y y w) =
      ∑ a, ∑ b, u a * w b * lieCo g Y y a b := by
  have hcomp : ∀ v l, fderiv ℝ Y y v l = ∑ a, v a * pd a (fun z => Y z l) y := fun v l => by
    rw [fderiv_pi (fun i => (differentiableAt_pi.1 hY) i)]
    simp [fderiv_eq_sum_pd]
  rw [fderiv_coordBil_apply hgd, coordBil_apply, coordBil_apply]
  simp only [hcomp, lieCo, Fin.sum_univ_three]
  ring

end Bilinear

namespace NormalizedKillingFrame

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {Y : Idx → (Fin 3 → ℝ) → Fin 3 → ℝ} {p : Fin 3 → ℝ}

/-- **G1-024, stage 1: a metric on a ball of `ℝ³` with a Killing family normalized at the centre is, in orbit charts,
a constant multiple of the space form of some curvature `k`.** The family has the brackets `S k`
(`exists_lieBracket_eq_S`), so `isometric_spaceForm` applies: for some `T > 0` the orbit maps
`o ξ = exp(T Σ ξₑ Yₑ)(p)` and `o₂ ξ = exp(T Σ ξₑ Xₑ)(0)` satisfy
`G(o ξ)(Do ζ, Do ζ') = g₀₀(p) · δ/(1 + k|x|²/4)²(o₂ ξ)(Do₂ ζ, Do₂ ζ')` near `ξ = 0`. -/
theorem isometric {ρ : ℝ} (h : NormalizedKillingFrame g (Metric.ball p ρ) Y p) (hρ : 0 < ρ) :
    ∃ (k T ε : ℝ) (o : (Idx → ℝ) → (Fin 3 → ℝ)) (o₂ : (Idx → ℝ) → (Fin 3 → ℝ)), 0 < T ∧ 0 < ε ∧ o 0 = p ∧
      o₂ 0 = 0 ∧ (∀ ξ ∈ Metric.ball (0 : Idx → ℝ) ε, DifferentiableAt ℝ o ξ ∧ DifferentiableAt ℝ o₂ ξ) ∧
      (∀ ζ, fderiv ℝ o 0 ζ = T • ∑ e, ζ e • Y e p) ∧
      (∀ ζ, fderiv ℝ o₂ 0 ζ = T • ∑ e, ζ e • SpaceForm.X k e 0) ∧
      ∀ ξ ∈ Metric.ball (0 : Idx → ℝ) ε, ∀ ζ ζ',
        coordBil g (o ξ) (fderiv ℝ o ξ ζ) (fderiv ℝ o ξ ζ') =
          g p 0 0 * SpaceForm.metric k (o₂ ξ) (fderiv ℝ o₂ ξ ζ) (fderiv ℝ o₂ ξ ζ') := by
  obtain ⟨k, hS⟩ := h.exists_lieBracket_eq_S (convex_ball p ρ).isPreconnected
  have hO := h.metric.isOpen
  have hgd : ∀ y ∈ Metric.ball p ρ, ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y := fun y hy a b =>
    differentiableAt_of_contDiffOn (h.metric.smooth a b) hO hy
  have hYd : ∀ i, ∀ y ∈ Metric.ball p ρ, DifferentiableAt ℝ (Y i) y := fun i y hy =>
    differentiableAt_pi.2 fun c => differentiableAt_of_contDiffOn (h.smooth i c) hO hy
  have hYc : ∀ i, ContDiffAt ℝ 1 (Y i) p := fun i =>
    (contDiffAt_pi.2 fun c => (h.smooth i c).contDiffAt (hO.mem_nhds h.mem)).of_le (by simp)
  have hGd : ∀ y ∈ Metric.ball p ρ, DifferentiableAt ℝ (coordBil g) y := fun y hy =>
    (hasFDerivAt_coordBil (hgd y hy)).differentiableAt
  have hK : ∀ i, ∀ y ∈ Metric.ball p ρ, ∀ u w : Fin 3 → ℝ,
      fderiv ℝ (coordBil g) y (Y i y) u w + coordBil g y (fderiv ℝ (Y i) y u) w +
        coordBil g y u (fderiv ℝ (Y i) y w) = 0 := fun i y hy u w => by
    rw [coordBil_lie (hgd y hy) (hYd i y hy)]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [lieCo_lowerVec h.symm (h.metric.isUnit_det y hy).ne_zero (hgd y hy)
      (fun c => differentiableAt_of_contDiffOn (h.smooth i c) hO hy), h.killing i y hy a b, mul_zero]
  have hsym : ∀ y ∈ Metric.ball p ρ, ∀ u w : Fin 3 → ℝ, coordBil g y u w = coordBil g y w u := fun y _ u w => by
    rw [coordBil_apply, coordBil_apply, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [h.symm y b a]; ring
  have hiso : ∀ a b : Fin 3, Y (.inr (a, b)) p = 0 := fun a b => by rw [h.val]; rfl
  obtain ⟨T, ε, o, o₂, hT, hε, ho, ho₂, hd, hD, hD₂, hG⟩ :=
    isometric_spaceForm k (coordBil g) Y p hρ hYc hYd hGd hK hS hsym hiso
  have h00 : coordBil g p (Y (.inl 0) p) (Y (.inl 0) p) = g p 0 0 := by
    rw [h.val, coordBil_apply]
    simp [frameVal, Pi.single_apply]
  exact ⟨k, T, ε, o, o₂, hT, hε, ho, ho₂, hd, hD, hD₂, fun ξ hξ ζ ζ' => by rw [hG ξ hξ ζ ζ', h00]⟩

end NormalizedKillingFrame

end Lightlike
