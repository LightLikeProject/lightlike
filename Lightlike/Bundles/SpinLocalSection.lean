import Mathlib
import Lightlike.Bundles.SpinKernel

/-!
# A local inverse of the vector action `Spin(n) → SO(n)` near the identity

For an orthonormal frame `W : Fin n → ℝⁿ` close enough to the standard frame `e`, this file
constructs an explicit element `spinOfFrame W` of Mathlib's `spinGroup` of `Cl(ℝⁿ, -‖·‖²)` whose
vector action sends `e a` to `W a` for every `a`, and which is `1` at the standard frame.

The construction peels off one index at a time.  At step `k` the current frame `V` agrees with
`e` below `k`; with `m` the unit bisector of `e k` and `V k`, the product of the two reflections
`refl (e k) ∘ refl m` sends `V k` back to `e k` and fixes the earlier vectors, and the spin element
`-(ι m) (ι (e k))` acts on vectors by the inverse rotation `refl m ∘ refl (e k)`.  The spin element
of the frame is the product of these factors.  It is defined for every family of vectors and is
a polynomial in the vectors and the inverse norms `‖e k + V k‖⁻¹`; the condition for it to be a
lift (`FrameGood`: `e k + V k ≠ 0` at every step) is open and holds at the standard frame.

## Main results

* `refl`, `ι_mul_ι_mul_ι`: the reflection in the hyperplane orthogonal to a unit vector `u` is
  conjugation by `ι u`, `ι u * ι v * ι u = ι (refl u v)`;
* `spinOfFrame_mem`, `vecConj_spinOfFrame`: for an orthonormal frame with `FrameGood`, the element
  `spinOfFrame W` is a spin element whose vector action sends `e a` to `W a`;
* `spinOfFrame_standard`: `spinOfFrame e = 1`;
* `isOpen_frameGood`, `contDiffAt_spinOfFrame`: the frames with `FrameGood` form an open set, on
  which every linear coordinate of `spinOfFrame` is smooth (through the normed structure
  `clNormedRing` of the Clifford algebra).

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter I, §2 (reflections and the
  vector action of `Pin(n)` and `Spin(n)`).
-/

open CliffordAlgebra
open scoped InnerProductSpace RealInnerProductSpace ContDiff

namespace Lightlike.Dirac

variable {n : ℕ}

/-! ## Reflections -/

/-- The reflection of `v` in the hyperplane orthogonal to `u` (for a unit vector `u`). -/
noncomputable def refl (u v : E n) : E n := v - (2 * ⟪v, u⟫) • u

lemma refl_refl {u : E n} (hu : ‖u‖ = 1) (v : E n) : refl u (refl u v) = v := by
  have h : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  simp only [refl, inner_sub_left, inner_smul_left, h, RCLike.conj_to_real]
  module

lemma inner_refl {u : E n} (hu : ‖u‖ = 1) (v w : E n) : ⟪refl u v, refl u w⟫ = ⟪v, w⟫ := by
  have h : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  simp only [refl, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, h,
    RCLike.conj_to_real, real_inner_comm u v, real_inner_comm u w]
  ring

lemma refl_of_inner_eq_zero {u v : E n} (h : ⟪v, u⟫ = 0) : refl u v = v := by
  simp [refl, h]

lemma refl_neg (u v : E n) : refl (-u) v = refl u v := by
  simp [refl, inner_neg_right]

/-- The polar form of `Qneg`: `ι u ι v + ι v ι u = -2 ⟪u, v⟫`. -/
lemma ι_mul_ι_add_swap_Qneg (u v : E n) :
    ι (Qneg n) u * ι (Qneg n) v + ι (Qneg n) v * ι (Qneg n) u =
      algebraMap ℝ _ (-2 * ⟪u, v⟫) := by
  rw [ι_mul_ι_add_swap]
  congr 1
  rw [QuadraticMap.polar, Qneg_apply, Qneg_apply, Qneg_apply, norm_add_sq_real]
  ring

/-- **Reflection is conjugation by a unit vector**: `ι u * ι v * ι u = ι (refl u v)`. -/
lemma ι_mul_ι_mul_ι {u : E n} (hu : ‖u‖ = 1) (v : E n) :
    ι (Qneg n) u * ι (Qneg n) v * ι (Qneg n) u = ι (Qneg n) (refl u v) := by
  have h := ι_mul_ι_add_swap_Qneg u v
  have h2 : ι (Qneg n) u * ι (Qneg n) v = algebraMap ℝ _ (-2 * ⟪u, v⟫) -
      ι (Qneg n) v * ι (Qneg n) u := eq_sub_of_add_eq h
  rw [h2, sub_mul, mul_assoc, ι_mul_self_of_norm_eq_one hu, mul_neg_one, sub_neg_eq_add,
    Algebra.algebraMap_eq_smul_one, smul_one_mul, refl, map_sub, map_smul, real_inner_comm u v]
  module

/-! ## The bisector step -/

/-- The unit bisector of two vectors. -/
noncomputable def bisect (u w : E n) : E n := ‖u + w‖⁻¹ • (u + w)

lemma norm_bisect {u w : E n} (h : u + w ≠ 0) : ‖bisect u w‖ = 1 := by
  rw [bisect, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

/-- The reflection in the bisector exchanges `w` and `-u`. -/
lemma refl_bisect {u w : E n} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (h : u + w ≠ 0) :
    refl (bisect u w) w = -u := by
  have hn : ‖u + w‖ ≠ 0 := norm_ne_zero_iff.2 h
  have hsq : ‖u + w‖ ^ 2 = 2 * (1 + ⟪w, u⟫) := by
    rw [norm_add_sq_real, hu, hw, real_inner_comm]; ring
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw, one_pow]
  simp only [refl, bisect, inner_smul_right, inner_add_right, hww, smul_smul]
  have hc : 2 * (‖u + w‖⁻¹ * (⟪w, u⟫ + 1)) * ‖u + w‖⁻¹ = 1 := by
    field_simp
    nlinarith [hsq]
  rw [show 2 * (‖u + w‖⁻¹ * (⟪w, u⟫ + 1)) * ‖u + w‖⁻¹ = 1 from hc, one_smul]
  abel

/-- The rotation `refl u ∘ refl (bisect u w)` sends `w` to `u`. -/
lemma refl_refl_bisect {u w : E n} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (h : u + w ≠ 0) :
    refl u (refl (bisect u w) w) = u := by
  rw [refl_bisect hu hw h]
  have h1 : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  simp only [refl, inner_neg_left, h1]
  module

/-! ## Peeling a frame -/

/-- One peeling step at index `k`: rotate the frame by `refl (e k) ∘ refl m`, with `m` the bisector
of `e k` and `V k`. -/
noncomputable def peelStep (k : Fin n) (V : Fin n → E n) : Fin n → E n :=
  fun j => refl (e k) (refl (bisect (e k) (V k)) (V j))

/-- The frame after peeling the indices `0, …, k - 1`. -/
noncomputable def frameStage (W : Fin n → E n) : ℕ → Fin n → E n
  | 0 => W
  | k + 1 => if h : k < n then peelStep ⟨k, h⟩ (frameStage W k) else frameStage W k

/-- The spin factor of step `k`: `ι (-m) ι (e k)`, with `m` the bisector of `e k` and the `k`-th
vector of the current frame. -/
noncomputable def spinFactor (W : Fin n → E n) (k : ℕ) : CliffordAlgebra (Qneg n) :=
  if h : k < n then
    ι (Qneg n) (-bisect (e ⟨k, h⟩) (frameStage W k ⟨k, h⟩)) * ι (Qneg n) (e ⟨k, h⟩)
  else 1

/-- The product of the first `k` spin factors. -/
noncomputable def spinPartial (W : Fin n → E n) (k : ℕ) : CliffordAlgebra (Qneg n) :=
  ((List.range k).map (spinFactor W)).prod

/-- **The spin element of a frame**: the product of all `n` spin factors. -/
noncomputable def spinOfFrame (W : Fin n → E n) : CliffordAlgebra (Qneg n) := spinPartial W n

/-- The open condition under which `spinOfFrame W` lifts `W`: at every step the `k`-th vector of
the current frame is not `-e k`. -/
def FrameGood (W : Fin n → E n) : Prop :=
  ∀ k (h : k < n), e ⟨k, h⟩ + frameStage W k ⟨k, h⟩ ≠ 0

/-- A family of vectors is an orthonormal frame. -/
def IsOrthonormalFrame (W : Fin n → E n) : Prop := ∀ a b, ⟪W a, W b⟫ = if a = b then 1 else 0

lemma norm_of_isOrthonormalFrame {W : Fin n → E n} (hW : IsOrthonormalFrame W) (a : Fin n) :
    ‖W a‖ = 1 := by
  have h := hW a a
  rw [ite_eq_left rfl, real_inner_self_eq_norm_sq] at h
  have h0 := norm_nonneg (W a)
  nlinarith [h]

lemma isOrthonormalFrame_e : IsOrthonormalFrame (e (n := n)) := fun a b => by
  simp [e, EuclideanSpace.inner_single_left]

/-- The invariant of the peeling: after `k` steps the frame is orthonormal, agrees with `e` below
`k`, and the frame `W` is the conjugate of the current one by the product of the first `k`
factors. -/
lemma frameStage_spec {W : Fin n → E n} (hW : IsOrthonormalFrame W) (hg : FrameGood W) :
    ∀ k, k ≤ n → IsOrthonormalFrame (frameStage W k) ∧
      (∀ j : Fin n, (j : ℕ) < k → frameStage W k j = e j) ∧
      spinPartial W k ∈ spinGroup (Qneg n) ∧
      ∀ a, ι (Qneg n) (W a) =
        spinPartial W k * ι (Qneg n) (frameStage W k a) * star (spinPartial W k) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨hW, fun j hj => absurd hj (Nat.not_lt_zero _), ?_, fun a => ?_⟩
    · simp [spinPartial]
    · simp [spinPartial, frameStage]
  | succ k ih =>
    intro hk
    have hkn : k < n := hk
    obtain ⟨hON, hlow, hmem, hconj⟩ := ih hkn.le
    set K : Fin n := ⟨k, hkn⟩
    set V := frameStage W k
    have hu : ‖e K‖ = 1 := by simp [e]
    have hw : ‖V K‖ = 1 := norm_of_isOrthonormalFrame hON K
    have hgood : e K + V K ≠ 0 := hg k hkn
    set m := bisect (e K) (V K)
    have hm : ‖m‖ = 1 := norm_bisect hgood
    have hm' : ‖-m‖ = 1 := by rw [norm_neg, hm]
    have hstage : frameStage W (k + 1) = peelStep K V := by
      simp only [frameStage, dite_eq_left hkn]; rfl
    have hfac : spinFactor W k = ι (Qneg n) (-m) * ι (Qneg n) (e K) := by
      simp only [spinFactor, dite_eq_left hkn]; rfl
    have hpart : spinPartial W (k + 1) = spinPartial W k * spinFactor W k := by
      simp [spinPartial, List.range_succ, List.prod_append]
    -- the factor conjugates the new frame back to the old one
    have hstar : star (ι (Qneg n) (-m) * ι (Qneg n) (e K)) = ι (Qneg n) (e K) * ι (Qneg n) (-m) := by
      rw [star_mul, star_ι, star_ι, neg_mul_neg]
    have hfconj : ∀ x : E n, ι (Qneg n) (-m) * ι (Qneg n) (e K) * ι (Qneg n) x *
        star (ι (Qneg n) (-m) * ι (Qneg n) (e K)) = ι (Qneg n) (refl m (refl (e K) x)) := by
      intro x
      rw [hstar]
      calc ι (Qneg n) (-m) * ι (Qneg n) (e K) * ι (Qneg n) x * (ι (Qneg n) (e K) * ι (Qneg n) (-m))
          = ι (Qneg n) (-m) * (ι (Qneg n) (e K) * ι (Qneg n) x * ι (Qneg n) (e K)) *
              ι (Qneg n) (-m) := by noncomm_ring
        _ = ι (Qneg n) (refl m (refl (e K) x)) := by
          rw [ι_mul_ι_mul_ι hu, ι_mul_ι_mul_ι hm', refl_neg]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b
      rw [hstage]
      simp only [peelStep]
      rw [inner_refl hu, inner_refl hm]
      exact hON a b
    · intro j hj
      rw [hstage]
      simp only [peelStep]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · have hVj : V j = e j := hlow j hj
        have hjK : j ≠ K := fun h => by rw [h] at hj; exact lt_irrefl _ hj
        have h1 : ⟪V j, e K⟫ = 0 := by
          rw [hVj]; have := isOrthonormalFrame_e j K; rwa [ite_eq_right hjK] at this
        have h2 : ⟪V j, V K⟫ = 0 := by have := hON j K; rwa [ite_eq_right hjK] at this
        have h3 : ⟪V j, m⟫ = 0 := by
          simp only [m, bisect, inner_smul_right, inner_add_right, h1, h2, add_zero, mul_zero]
        rw [refl_of_inner_eq_zero h3, refl_of_inner_eq_zero h1, hVj]
      · have hjK : j = K := Fin.ext hj
        rw [hjK]
        exact refl_refl_bisect hu hw hgood
    · rw [hpart, hfac]
      exact Submonoid.mul_mem _ hmem (ι_mul_ι_mem_spinGroup hm' hu)
    · intro a
      rw [hconj a, hpart, hfac, star_mul]
      have hback : ι (Qneg n) (V a) = ι (Qneg n) (-m) * ι (Qneg n) (e K) *
          ι (Qneg n) (frameStage W (k + 1) a) * star (ι (Qneg n) (-m) * ι (Qneg n) (e K)) := by
        rw [hfconj, hstage]
        simp only [peelStep]
        rw [refl_refl hu, refl_refl hm]
      rw [hback]
      noncomm_ring

/-- **`spinOfFrame W` is a spin element** for an orthonormal frame with `FrameGood`. -/
theorem spinOfFrame_mem {W : Fin n → E n} (hW : IsOrthonormalFrame W) (hg : FrameGood W) :
    spinOfFrame W ∈ spinGroup (Qneg n) :=
  (frameStage_spec hW hg n le_rfl).2.2.1

/-- **`spinOfFrame W` lifts the frame**: its vector action sends `e a` to `W a`. -/
theorem vecConj_spinOfFrame {W : Fin n → E n} (hW : IsOrthonormalFrame W) (hg : FrameGood W)
    (a : Fin n) : vecConj ⟨spinOfFrame W, spinOfFrame_mem hW hg⟩ (e a) = W a := by
  obtain ⟨_, hlow, _, hconj⟩ := frameStage_spec hW hg n le_rfl
  rw [vecConj_eq_iff, hconj a, hlow a a.2]
  rfl

lemma frameStage_e : ∀ k, frameStage (e (n := n)) k = e := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [frameStage]
    split_ifs with h
    · rw [ih]
      funext j
      have hb : bisect (e ⟨k, h⟩) (e (n := n) ⟨k, h⟩) = e ⟨k, h⟩ := by
        have h1 : ‖e (⟨k, h⟩ : Fin n) + e ⟨k, h⟩‖ = 2 := by
          rw [← two_smul ℝ, norm_smul]; simp [e]
        rw [bisect, h1, ← two_smul ℝ (e _), smul_smul]; norm_num
      simp only [peelStep, hb]
      exact refl_refl (by simp [e]) _
    · exact ih

/-- **At the standard frame the spin element is `1`.** -/
theorem spinOfFrame_standard : spinOfFrame (e (n := n)) = 1 := by
  have hf : ∀ k ∈ List.range n, spinFactor (e (n := n)) k = 1 := by
    intro k hk
    have h : k < n := List.mem_range.1 hk
    have hb : bisect (e ⟨k, h⟩) (e (n := n) ⟨k, h⟩) = e ⟨k, h⟩ := by
      have h1 : ‖e (⟨k, h⟩ : Fin n) + e ⟨k, h⟩‖ = 2 := by
        rw [← two_smul ℝ, norm_smul]; simp [e]
      rw [bisect, h1, ← two_smul ℝ (e _), smul_smul]; norm_num
    simp only [spinFactor, dite_eq_left h, frameStage_e, hb, map_neg, neg_mul]
    rw [ι_mul_self_of_norm_eq_one (by simp [e]), neg_neg]
  rw [spinOfFrame, spinPartial, List.map_congr_left hf]
  simp

/-- The standard frame satisfies `FrameGood`. -/
lemma frameGood_e : FrameGood (e (n := n)) := by
  intro k h
  rw [frameStage_e, ← two_smul ℝ]
  exact smul_ne_zero two_ne_zero (by
    intro h0; have := congrArg norm h0; simp [e] at this)

/-! ## Smoothness -/

section Smooth

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f g : X → E n} {x : X}

lemma ContDiffAt.refl' (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (fun y => refl (f y) (g y)) x :=
  hg.sub ((contDiffAt_const.mul (hg.inner ℝ hf)).smul hf)

lemma ContDiffAt.bisect' (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (h : f x + g x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => bisect (f y) (g y)) x :=
  (((hf.add hg).norm ℝ h).inv (norm_ne_zero_iff.2 h)).smul (hf.add hg)

/-- The frames for which the first `k` peeling steps are defined. -/
def FrameGoodUpTo (k : ℕ) (W : Fin n → E n) : Prop :=
  ∀ j (h : j < n), j < k → e ⟨j, h⟩ + frameStage W j ⟨j, h⟩ ≠ 0

lemma frameGood_iff (W : Fin n → E n) : FrameGood W ↔ FrameGoodUpTo n W :=
  ⟨fun h j hj _ => h j hj, fun h j hj => h j hj hj⟩

/-- The peeled frames depend smoothly on the frame where the steps are defined. -/
lemma contDiffAt_frameStage : ∀ k, ∀ W, FrameGoodUpTo k W →
    ContDiffAt ℝ ∞ (fun V : Fin n → E n => frameStage V k) W := by
  intro k
  induction k with
  | zero => intro W _; exact contDiffAt_id
  | succ k ih =>
    intro W hW
    have hprev : ContDiffAt ℝ ∞ (fun V : Fin n → E n => frameStage V k) W :=
      ih W fun j h hj => hW j h (Nat.lt_succ_of_lt hj)
    by_cases hk : k < n
    · have heq : (fun V : Fin n → E n => frameStage V (k + 1)) =
          fun V => peelStep ⟨k, hk⟩ (frameStage V k) := by
        funext V; simp only [frameStage, dite_eq_left hk]
      rw [heq]
      have hK := contDiffAt_pi.1 hprev ⟨k, hk⟩
      refine contDiffAt_pi.2 fun j => ?_
      exact ContDiffAt.refl' contDiffAt_const (ContDiffAt.refl'
        (ContDiffAt.bisect' contDiffAt_const hK (hW k hk (Nat.lt_succ_self k)))
        (contDiffAt_pi.1 hprev j))
    · have heq : (fun V : Fin n → E n => frameStage V (k + 1)) = fun V => frameStage V k := by
        funext V; simp only [frameStage, hk, dite_false]
      rw [heq]; exact hprev

lemma continuousAt_frameStage (k : ℕ) {W : Fin n → E n} (hW : FrameGoodUpTo k W) :
    ContinuousAt (fun V : Fin n → E n => frameStage V k) W :=
  (contDiffAt_frameStage k W hW).continuousAt

/-- The frames for which the peeling steps are defined form an open set. -/
lemma isOpen_frameGoodUpTo : ∀ k, IsOpen {W : Fin n → E n | FrameGoodUpTo k W} := by
  intro k
  induction k with
  | zero =>
    convert isOpen_univ
    ext W; simp [FrameGoodUpTo]
  | succ k ih =>
    rw [isOpen_iff_mem_nhds]
    intro W hW
    have hprev : FrameGoodUpTo k W := fun j h hj => hW j h (Nat.lt_succ_of_lt hj)
    by_cases hk : k < n
    · have hc : ContinuousAt (fun V : Fin n → E n => e ⟨k, hk⟩ + frameStage V k ⟨k, hk⟩) W :=
        continuousAt_const.add ((continuous_apply _).continuousAt.comp
          (continuousAt_frameStage k hprev))
      have h1 := hc.preimage_mem_nhds (isOpen_ne.mem_nhds (hW k hk (Nat.lt_succ_self k)))
      filter_upwards [ih.mem_nhds hprev, h1] with V hV hV2
      intro j h hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hV j h hj
      · exact hV2
    · filter_upwards [ih.mem_nhds hprev] with V hV
      intro j h hj
      exact hV j h (by omega)

lemma isOpen_frameGood : IsOpen {W : Fin n → E n | FrameGood W} := by
  simp_rw [frameGood_iff]; exact isOpen_frameGoodUpTo n

attribute [local instance] clNormedRing clNormedAlgebra

/-- `ι` as a continuous linear map, for the normed structure of the Clifford algebra. -/
noncomputable def ιL : E n →L[ℝ] CliffordAlgebra (Qneg n) :=
  LinearMap.toContinuousLinearMap (ι (Qneg n))

lemma contDiffAt_spinPartial : ∀ k, ∀ W, FrameGoodUpTo k W →
    ContDiffAt ℝ ∞ (fun V : Fin n → E n => spinPartial V k) W := by
  intro k
  induction k with
  | zero => intro W _; simp only [spinPartial, List.range_zero, List.map_nil, List.prod_nil];
            exact contDiffAt_const
  | succ k ih =>
    intro W hW
    have hprev : FrameGoodUpTo k W := fun j h hj => hW j h (Nat.lt_succ_of_lt hj)
    have heq : (fun V : Fin n → E n => spinPartial V (k + 1)) =
        fun V => spinPartial V k * spinFactor V k := by
      funext V; simp [spinPartial, List.range_succ, List.prod_append]
    rw [heq]
    refine (ih W hprev).mul ?_
    by_cases hk : k < n
    · have heq2 : (fun V : Fin n → E n => spinFactor V k) = fun V =>
          ιL (-bisect (e ⟨k, hk⟩) (frameStage V k ⟨k, hk⟩)) * ιL (e ⟨k, hk⟩) := by
        funext V; simp only [spinFactor, dite_eq_left hk]; rfl
      rw [heq2]
      have hK := contDiffAt_pi.1 (contDiffAt_frameStage k W hprev) ⟨k, hk⟩
      exact (ιL.contDiff.contDiffAt.comp W
        (ContDiffAt.bisect' contDiffAt_const hK (hW k hk (Nat.lt_succ_self k))).neg).mul
          contDiffAt_const
    · have heq2 : (fun V : Fin n → E n => spinFactor V k) = fun _ => 1 := by
        funext V; simp only [spinFactor, hk, dite_false]
      rw [heq2]; exact contDiffAt_const

end Smooth

/-- **The spin element of a frame depends smoothly on the frame** where it is defined: every linear
coordinate of `spinOfFrame` is smooth at a frame with `FrameGood`. -/
theorem contDiffAt_spinOfFrame (φ : Module.Dual ℝ (CliffordAlgebra (Qneg n)))
    {W : Fin n → E n} (hW : FrameGood W) :
    ContDiffAt ℝ ∞ (fun V => φ (spinOfFrame V)) W := by
  let _ := clNormedRing n
  let _ := clNormedAlgebra n
  have h := contDiffAt_spinPartial n W ((frameGood_iff W).1 hW)
  exact (LinearMap.toContinuousLinearMap φ).contDiff.contDiffAt.comp W h

/-- Non-vacuity: at the standard frame the construction applies, and gives `1`. -/
example : FrameGood (e (n := n)) ∧ spinOfFrame (e (n := n)) = 1 :=
  ⟨frameGood_e, spinOfFrame_standard⟩

/-- Trust check (a wrong input): the orientation-reversed frame `-e` of `ℝ¹` is not `FrameGood`;
it has no lift to `Spin(1)`, since the vector action of a spin element preserves orientation. -/
example : ¬ FrameGood (fun a : Fin 1 => -e a) := by
  intro h
  exact h 0 Nat.one_pos (by simp [frameStage])

end Lightlike.Dirac
