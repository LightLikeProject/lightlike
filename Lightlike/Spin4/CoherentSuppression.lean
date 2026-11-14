import Lightlike.Spin4.CoherentIntertwiner

/-!
# Suppression of coherent intertwiners whose normals do not close (SF5e)

For any number of links, a Livine–Speziale coherent intertwiner whose normals do not close is
exponentially small at large spins. With the spins `J_a = n K_a` scaled by `n` and the weighted
closure defect `N = Σ_a K_a ν_a`,

  `‖ι_{nK}(g⃗)‖² ≤ exp(-n N_i² / (4 Σ_a K_a))` for each axis `i`, hence
  `‖ι_{nK}(g⃗)‖² ≤ exp(-n |N|² / (12 Σ_a K_a))`

(`normSq_cohInt_le_exp_z`, `normSq_cohInt_le_exp`, `cohInt_suppressed`). This is the suppression
of non-closing normals of Livine–Speziale (2007) and Conrady–Freidel (2009), as a bound with an
explicit rate. Their stationary-phase analysis gives the sharper rate `exp(-n Nᵀ H⁻¹ N / 2)`,
`H = Σ_a K_a (1 - ν_a ν_aᵀ)` (numerical evidence in `scripts/spin4/coherent_check.py`).

The proof is elementary:

* invariant vectors are supported on the labels of total weight `Σ_a (J_a - 2 k_a) = 0`, by
  invariance under the diagonal elements of SU(2) (`IsInvariantN.eq_zero_of_weight_ne_zero`);
* so `‖P v‖² ≤ Σ_{weight k = 0} |v_k|²` by Cauchy–Schwarz (`normSq_avgP_le`);
* for a product of coherent states `|v_k|²` is a product of binomial weights
  `C(J_a, k_a) p_a^{J_a-k_a} q_a^{k_a}`, `p_a = |g_a₀₀|²`, `q_a = |g_a₁₀|²`; a Chernoff bound and
  the binomial theorem give `Σ_{weight k = 0} |v_k|² ≤ Π_a ((p_a + q_a s²)/s)^{J_a}` for every
  `s > 0` (`sum_weight_zero_le`);
* `s = 1 + ε` or `s = 1/(1 + ε)` with `ε = |N_z| / (2 Σ_a K_a)` gives the rate, and a global
  rotation, which does not change the coherent intertwiner (`cohInt_mul_left`), moves any axis
  to the `z`-axis.
-/

open Matrix Finset

namespace Lightlike.Spin4

open SU2

variable {N : ℕ} {J : Fin N → ℕ}

/-! ## Global rotations -/

/-- `P ρ(h) = P`. -/
theorem avgP_mul_rhoN (h : SU2) : avgP J * rhoN J h = avgP J := by
  have e := rhoN_mul_avgP (J := J) (star h)
  have hs : ((star h : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = (h : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := rfl
  rw [hs, ← rhoN_conjTranspose] at e
  have e' := congrArg conjTranspose e
  rwa [conjTranspose_mul, conjTranspose_conjTranspose, avgP_conjTranspose] at e'

/-- **A global rotation does not change a coherent intertwiner**: `ι(h g⃗) = ι(g⃗)`. -/
theorem cohInt_mul_left (h : SU2) (g : Fin N → SU2) :
    cohInt J (fun a => h * g a) = cohInt J g := by
  have hv : (prodVec J fun a => cohState (J a) ((h * g a : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) =
      rhoN J h *ᵥ prodVec J fun a => cohState (J a) (g a) := by
    rw [rhoN_mulVec_prodVec]
    congr 1
    funext a
    rw [spinMat_mulVec_cohState]
    rfl
  rw [cohInt, cohInt, hv, mulVec_mulVec, avgP_mul_rhoN]

/-! ## Invariant vectors have total weight zero -/

variable (J) in
/-- The total weight `Σ_a (J_a - 2 k_a)` of a basis label (twice its total magnetic number). -/
def weight (k : LIdx J) : ℤ := ∑ a, ((J a : ℤ) - 2 * (k a : ℕ))

/-- A product representation of a matrix acting diagonally on each factor is diagonal. -/
lemma rhoN_eq_diagonal (g : Matrix (Fin 2) (Fin 2) ℂ) (d : (a : Fin N) → Fin (J a + 1) → ℂ)
    (hg : ∀ a, spinMat (J a) g = diagonal (d a)) :
    rhoN J g = diagonal fun k => ∏ a, d a (k a) := by
  ext k l
  simp only [rhoN, of_apply, hg, diagonal_apply]
  by_cases hkl : k = l
  · subst hkl
    simp
  · obtain ⟨a, ha⟩ := Function.ne_iff.mp hkl
    simp only [hkl, ite_false]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

/-- **Invariant vectors are supported on the labels of total weight zero**: the rotation
`diag(e^{iθ}, e^{-iθ})` multiplies the component `k` by `e^{iθ weight(k)}`. -/
theorem IsInvariantN.eq_zero_of_weight_ne_zero {w : LIdx J → ℂ} (hw : IsInvariantN J w)
    {k : LIdx J} (hk : weight J k ≠ 0) : w k = 0 := by
  set θ : ℝ := Real.pi / (weight J k : ℝ) with hθ
  have hz : Complex.exp (θ * Complex.I) * star (Complex.exp (θ * Complex.I)) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]; simp [Complex.conj_ofReal]
  have hrho : rhoN J (torus _ hz : Matrix (Fin 2) (Fin 2) ℂ) = diagonal fun l =>
      ∏ a, Complex.exp ((((J a : ℝ) - 2 * (l a : ℕ)) * θ : ℝ) * Complex.I) :=
    rhoN_eq_diagonal _ _ fun a => spinMat_torus_exp θ
  have e := congrFun (hw (torus _ hz)) k
  rw [hrho, mulVec_diagonal] at e
  have hD : (∏ a, Complex.exp ((((J a : ℝ) - 2 * (k a : ℕ)) * θ : ℝ) * Complex.I)) = -1 := by
    rw [← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum]
    have hw' : (weight J k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hs : ∑ a, (((J a : ℝ) - 2 * (k a : ℕ)) * θ) = Real.pi := by
      rw [← Finset.sum_mul]
      have : (∑ a, ((J a : ℝ) - 2 * (k a : ℕ))) = (weight J k : ℝ) := by
        simp only [weight]; push_cast; rfl
      rw [this, hθ]
      field_simp
    rw [hs]
    exact Complex.exp_pi_mul_I
  rw [hD] at e
  linear_combination (-1 / 2 : ℂ) * e

/-! ## The projection bound -/

/-- **`‖P v‖² ≤ Σ_{weight k = 0} |v_k|²`**: the invariant vector `P v` is supported on the labels
of total weight zero, and `‖P v‖² = ⟨P v, v⟩`. -/
theorem normSq_avgP_le (v : LIdx J → ℂ) :
    ∑ k, Complex.normSq ((avgP J *ᵥ v) k) ≤
      ∑ k ∈ univ.filter (fun k => weight J k = 0), Complex.normSq (v k) := by
  set u := avgP J *ᵥ v with hu_def
  have hu : IsInvariantN J u := isInvariantN_avgP_mulVec v
  have h0 : ∀ k, weight J k ≠ 0 → u k = 0 := fun k hk => hu.eq_zero_of_weight_ne_zero hk
  set S := univ.filter (fun k : LIdx J => weight J k = 0)
  have e : star u ⬝ᵥ u = star u ⬝ᵥ v := inner_avgP_of_invariant hu v
  set X := ∑ k, ‖u k‖ ^ 2
  set Y := ∑ k ∈ S, ‖v k‖ ^ 2
  have hX : star u ⬝ᵥ u = (X : ℂ) := by
    simp only [X, dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
  have hXS : X = ∑ k ∈ S, ‖u k‖ ^ 2 := by
    refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
    by_contra h
    exact hk (by rw [h0 k h, norm_zero]; ring)
  have huv : star u ⬝ᵥ v = ∑ k ∈ S, star (u k) * v k := by
    refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
    by_contra h
    exact hk (by rw [Pi.star_apply, h0 k h, star_zero, zero_mul])
  have hle : X ≤ ∑ k ∈ S, ‖u k‖ * ‖v k‖ := by
    have h1 : ‖(X : ℂ)‖ = X := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => by positivity)]
    rw [← h1, ← hX, e, huv]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [norm_mul, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun k => ‖u k‖) (fun k => ‖v k‖)
  rw [← hXS] at hcs
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun k _ => by positivity
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun k _ => by positivity
  have hXY : X ≤ Y := by
    rcases hX0.eq_or_lt with h | h
    · rw [← h]; exact hY0
    · have : X * X ≤ X * Y := by nlinarith
      exact le_of_mul_le_mul_left this h
  have hn : ∀ z : ℂ, Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq
  simp only [hn]
  exact hXY

/-! ## The Chernoff bound -/

/-- `|⟨k|j, g⟩|² = C(2j, k) |g₀₀|^{2(2j-k)} |g₁₀|^{2k}`: a binomial weight. -/
lemma normSq_cohState (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin (n + 1)) :
    Complex.normSq (cohState n g a) =
      (n.choose a : ℝ) * Complex.normSq (g 0 0) ^ (n - a) * Complex.normSq (g 1 0) ^ (a : ℕ) := by
  rw [cohState_apply, map_mul, map_mul, map_pow, map_pow, Complex.normSq_ofReal,
    Real.mul_self_sqrt (Nat.cast_nonneg _)]

/-- `|v_k|²` for a product of coherent states is a product of binomial weights. -/
lemma normSq_prodVec_cohState (g : Fin N → SU2) (k : LIdx J) :
    Complex.normSq (prodVec J (fun a => cohState (J a) (g a)) k) =
      ∏ a, ((J a).choose (k a) : ℝ) * Complex.normSq ((g a : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^
        (J a - k a) * Complex.normSq ((g a : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ^ (k a : ℕ) := by
  simp only [prodVec, map_prod, normSq_cohState]

/-- The binomial theorem, indexed by `Fin (n + 1)`. -/
lemma add_mul_pow_eq_sum (n : ℕ) (p q t : ℝ) :
    (p + q * t) ^ n =
      ∑ m : Fin (n + 1), (n.choose m : ℝ) * p ^ (n - m) * q ^ (m : ℕ) * t ^ (m : ℕ) := by
  rw [add_comm, add_pow, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow]; ring

/-- **Chernoff bound**: for weights `p_a, q_a ≥ 0` and any `s > 0`, the binomial weights summed
over the labels of total weight zero are at most `Π_a ((p_a + q_a s²)/s)^{J_a}`. On those labels
`Π_a s^{2 k_a} = s^{Σ_a J_a}`; the full sum is a product of binomial expansions. -/
theorem sum_weight_zero_le (p q : Fin N → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) {s : ℝ}
    (hs : 0 < s) :
    ∑ k ∈ univ.filter (fun k : LIdx J => weight J k = 0),
        ∏ a, ((J a).choose (k a) : ℝ) * p a ^ (J a - k a) * q a ^ (k a : ℕ) ≤
      ∏ a, ((p a + q a * s ^ 2) / s) ^ J a := by
  set b : LIdx J → ℝ := fun k =>
    ∏ a, ((J a).choose (k a) : ℝ) * p a ^ (J a - k a) * q a ^ (k a : ℕ) with hb_def
  have hb : ∀ k, 0 ≤ b k := fun k => Finset.prod_nonneg fun a _ => by
    have := hp a; have := hq a; positivity
  have hexp : ∏ a, (p a + q a * s ^ 2) ^ J a =
      ∑ k : LIdx J, b k * (s ^ 2) ^ (∑ a, (k a : ℕ)) := by
    simp only [add_mul_pow_eq_sum, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hS : ∀ k ∈ univ.filter (fun k : LIdx J => weight J k = 0),
      2 * ∑ a, (k a : ℕ) = ∑ a, J a := by
    intro k hk
    have h := (Finset.mem_filter.mp hk).2
    simp only [weight, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
    have : (((2 * ∑ a, (k a : ℕ) : ℕ)) : ℤ) = ((∑ a, J a : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have hrhs : ∏ a, ((p a + q a * s ^ 2) / s) ^ J a =
      (∏ a, (p a + q a * s ^ 2) ^ J a) / s ^ (∑ a, J a) := by
    simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hrhs, le_div_iff₀ (by positivity), hexp, Finset.sum_mul]
  calc ∑ k ∈ univ.filter (fun k : LIdx J => weight J k = 0), b k * s ^ (∑ a, J a)
      = ∑ k ∈ univ.filter (fun k : LIdx J => weight J k = 0),
          b k * (s ^ 2) ^ (∑ a, (k a : ℕ)) :=
        Finset.sum_congr rfl fun k hk => by rw [← pow_mul, hS k hk]
    _ ≤ ∑ k : LIdx J, b k * (s ^ 2) ^ (∑ a, (k a : ℕ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun k _ _ => mul_nonneg (hb k) (by positivity)

/-- **Chernoff bound for coherent intertwiners**: for every `s > 0`,
`‖ι(g⃗)‖² ≤ Π_a ((|g_a₀₀|² + |g_a₁₀|² s²)/s)^{J_a}`. -/
theorem normSq_cohInt_le (g : Fin N → SU2) {s : ℝ} (hs : 0 < s) :
    ∑ k, Complex.normSq (cohInt J g k) ≤
      ∏ a, ((Complex.normSq ((g a : Matrix (Fin 2) (Fin 2) ℂ) 0 0) +
        Complex.normSq ((g a : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * s ^ 2) / s) ^ J a := by
  unfold cohInt
  refine (normSq_avgP_le _).trans ((Finset.sum_congr rfl fun k _ =>
    normSq_prodVec_cohState g k).trans_le ?_)
  exact sum_weight_zero_le _ _ (fun a => Complex.normSq_nonneg _)
    (fun a => Complex.normSq_nonneg _) hs

/-! ## The rate -/

/-- `p/(1+ε) + q(1+ε) ≤ exp(-ε(p - q) + ε²)` for `p, q ≥ 0`, `p + q = 1` and `ε ≥ 0`. -/
lemma div_add_mul_le_exp {p q ε : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hε : 0 ≤ ε) : p / (1 + ε) + q * (1 + ε) ≤ Real.exp (-(ε * (p - q)) + ε ^ 2) := by
  have h1 : 1 / (1 + ε) ≤ 1 - ε + ε ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg hε 3]
  have h2 : p / (1 + ε) ≤ p * (1 - ε + ε ^ 2) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left h1 hp
  refine le_trans ?_ (Real.add_one_le_exp _)
  have hq' : q = 1 - p := by linarith
  subst hq'
  nlinarith [h2, mul_nonneg hq (sq_nonneg ε)]

/-- If every factor of the Chernoff bound at some `s` is at most `exp(x_a)`, then
`‖ι_{nK}‖² ≤ exp(n Σ_a K_a x_a)`. -/
lemma normSq_cohInt_le_exp_of (K : Fin N → ℕ) (g : Fin N → SU2) (n : ℕ) {s : ℝ} (hs : 0 < s)
    (x : Fin N → ℝ)
    (hx : ∀ a, (Complex.normSq ((g a : Matrix (Fin 2) (Fin 2) ℂ) 0 0) +
      Complex.normSq ((g a : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * s ^ 2) / s ≤ Real.exp (x a)) :
    ∑ k, Complex.normSq (cohInt (fun a => n * K a) g k) ≤
      Real.exp (n * ∑ a, (K a : ℝ) * x a) := by
  refine (normSq_cohInt_le g hs).trans ?_
  have : Real.exp (n * ∑ a, (K a : ℝ) * x a) = ∏ a, Real.exp (x a) ^ (n * K a) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [this]
  have h0 : ∀ a, 0 ≤ (Complex.normSq ((g a : Matrix (Fin 2) (Fin 2) ℂ) 0 0) +
      Complex.normSq ((g a : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * s ^ 2) / s := fun a =>
    div_nonneg (add_nonneg (Complex.normSq_nonneg _)
      (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg s))) hs.le
  exact Finset.prod_le_prod₀ (fun a _ => pow_nonneg (h0 a) _) fun a _ =>
    pow_le_pow_left₀ (h0 a) (hx a) _

/-- **Suppression along the `z`-axis**: with spins `J_a = n K_a` and `N_z = Σ_a K_a (ν_a)_z`,
`‖ι_{nK}(g⃗)‖² ≤ exp(-n N_z² / (4 Σ_a K_a))`. -/
theorem normSq_cohInt_le_exp_z (K : Fin N → ℕ) (g : Fin N → SU2) (n : ℕ) :
    ∑ k, Complex.normSq (cohInt (fun a => n * K a) g k) ≤
      Real.exp (-(n * (∑ a, (K a : ℝ) * bloch (g a) 2) ^ 2 / (4 * ∑ a, (K a : ℝ)))) := by
  set D := ∑ a, (K a : ℝ) * bloch (g a) 2 with hD_def
  set S := ∑ a, (K a : ℝ) with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Nat.cast_nonneg _
  set ε := |D| / (2 * S) with hε_def
  have hε : 0 ≤ ε := div_nonneg (abs_nonneg D) (by linarith)
  set p : Fin N → ℝ := fun a => Complex.normSq ((g a : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
  set q : Fin N → ℝ := fun a => Complex.normSq ((g a : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
  have hpq : ∀ a, p a + q a = 1 := fun a => normSq_col (g a)
  have hp : ∀ a, 0 ≤ p a := fun a => Complex.normSq_nonneg _
  have hq : ∀ a, 0 ≤ q a := fun a => Complex.normSq_nonneg _
  have hbz : ∀ a, bloch (g a) 2 = p a - q a := fun a => by simp [bloch, p, q]
  have h1ε : (1 + ε) ≠ 0 := by linarith
  obtain ⟨σ, s, hs, hσD, hx⟩ : ∃ σ s : ℝ, 0 < s ∧ σ * D = |D| ∧
      ∀ a, (p a + q a * s ^ 2) / s ≤ Real.exp (-(σ * ε * (p a - q a)) + ε ^ 2) := by
    rcases le_or_gt 0 D with h | h
    · refine ⟨1, 1 + ε, by linarith, by rw [one_mul, abs_of_nonneg h], fun a => ?_⟩
      have := div_add_mul_le_exp (hp a) (hq a) (hpq a) hε
      rw [one_mul]
      convert this using 1
      field_simp
    · refine ⟨-1, (1 + ε)⁻¹, by positivity, by rw [abs_of_neg h]; ring, fun a => ?_⟩
      have := div_add_mul_le_exp (hq a) (hp a) (by linarith [hpq a]) hε
      convert this using 1
      · field_simp; ring
      · congr 1; ring
  refine (normSq_cohInt_le_exp_of K g n hs _ hx).trans (le_of_eq ?_)
  congr 1
  have hsum : ∑ a, (K a : ℝ) * (-(σ * ε * (p a - q a)) + ε ^ 2) = -(ε * (σ * D)) + ε ^ 2 * S := by
    rw [hD_def, hS_def]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hbz a]; ring
  rw [hsum, hσD]
  rcases eq_or_ne S 0 with h0 | h0
  · simp [hε_def, h0]
  · rw [hε_def, ← sq_abs D]; field_simp; ring

/-! ## Any axis, and the main theorem -/

/-- The rotation `curveY (π/4)` turns the `x`-component of a normal into the `z`-component:
`(ν(R g))_z = -(ν(g))_x`. -/
lemma bloch_curveY_mul (g : SU2) :
    bloch ((curveY (Real.pi / 4) * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 2 =
      -bloch (g : Matrix (Fin 2) (Fin 2) ℂ) 0 := by
  have hY : ((curveY (Real.pi / 4) * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.cos (Real.pi / 4) : ℝ) : ℂ), -((Real.sin (Real.pi / 4) : ℝ) : ℂ);
        ((Real.sin (Real.pi / 4) : ℝ) : ℂ), ((Real.cos (Real.pi / 4) : ℝ) : ℂ)] * g := rfl
  rw [hY, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [bloch, Matrix.mul_apply, Fin.sum_univ_two]
  simp [Complex.normSq_apply]
  set α := (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  set β := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  linear_combination (-(α.re * β.re + α.im * β.im)) * h2

/-- The rotation `curveX (π/4)` turns the `y`-component of a normal into the `z`-component:
`(ν(R g))_z = -(ν(g))_y`. -/
lemma bloch_curveX_mul (g : SU2) :
    bloch ((curveX (Real.pi / 4) * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 2 =
      -bloch (g : Matrix (Fin 2) (Fin 2) ℂ) 1 := by
  have hX : ((curveX (Real.pi / 4) * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.cos (Real.pi / 4) : ℝ) : ℂ), Complex.I * ((Real.sin (Real.pi / 4) : ℝ) : ℂ);
        Complex.I * ((Real.sin (Real.pi / 4) : ℝ) : ℂ), ((Real.cos (Real.pi / 4) : ℝ) : ℂ)] * g :=
    rfl
  rw [hX, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [bloch, Matrix.mul_apply, Fin.sum_univ_two]
  simp [Complex.normSq_apply]
  set α := (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  set β := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  linear_combination (-(α.re * β.im - α.im * β.re)) * h2

/-- **Suppression along any axis**: with spins `J_a = n K_a` and `N_i = Σ_a K_a (ν_a)_i`,
`‖ι_{nK}(g⃗)‖² ≤ exp(-n N_i² / (4 Σ_a K_a))` for `i = x, y, z`. -/
theorem normSq_cohInt_le_exp_axis (K : Fin N → ℕ) (g : Fin N → SU2) (n : ℕ) (i : Fin 3) :
    ∑ k, Complex.normSq (cohInt (fun a => n * K a) g k) ≤
      Real.exp (-(n * (∑ a, (K a : ℝ) * bloch (g a) i) ^ 2 / (4 * ∑ a, (K a : ℝ)))) := by
  fin_cases i
  · have h := normSq_cohInt_le_exp_z K (fun a => curveY (Real.pi / 4) * g a) n
    rw [cohInt_mul_left] at h
    simp only [bloch_curveY_mul, mul_neg, Finset.sum_neg_distrib, neg_sq] at h
    exact h
  · have h := normSq_cohInt_le_exp_z K (fun a => curveX (Real.pi / 4) * g a) n
    rw [cohInt_mul_left] at h
    simp only [bloch_curveX_mul, mul_neg, Finset.sum_neg_distrib, neg_sq] at h
    exact h
  · exact normSq_cohInt_le_exp_z K g n

/-- The largest of three squares is at least a third of their sum, in exponential bounds. -/
lemma le_exp_of_three {X a b c S n : ℝ} (hn : 0 ≤ n) (hS : 0 ≤ S)
    (ha : X ≤ Real.exp (-(n * a ^ 2 / (4 * S)))) (hb : X ≤ Real.exp (-(n * b ^ 2 / (4 * S))))
    (hc : X ≤ Real.exp (-(n * c ^ 2 / (4 * S)))) :
    X ≤ Real.exp (-(n * (a ^ 2 + b ^ 2 + c ^ 2) / (12 * S))) := by
  have key : ∀ t : ℝ, a ^ 2 + b ^ 2 + c ^ 2 ≤ 3 * t ^ 2 → X ≤ Real.exp (-(n * t ^ 2 / (4 * S))) →
      X ≤ Real.exp (-(n * (a ^ 2 + b ^ 2 + c ^ 2) / (12 * S))) := by
    intro t ht hX
    refine hX.trans (Real.exp_le_exp.mpr (neg_le_neg ?_))
    rw [show n * (a ^ 2 + b ^ 2 + c ^ 2) / (12 * S) = n * (a ^ 2 + b ^ 2 + c ^ 2) / 3 / (4 * S) by
      ring]
    have := mul_le_mul_of_nonneg_left ht hn
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  rcases le_total (b ^ 2) (a ^ 2) with h1 | h1 <;> rcases le_total (c ^ 2) (a ^ 2) with h2 | h2 <;>
    rcases le_total (c ^ 2) (b ^ 2) with h3 | h3 <;>
    first
      | exact key a (by linarith) ha
      | exact key b (by linarith) hb
      | exact key c (by linarith) hc

/-- **Suppression of non-closing normals, any valence**: with spins `J_a = n K_a` and the closure
defect `N = Σ_a K_a ν_a`, `‖ι_{nK}(g⃗)‖² ≤ exp(-n |N|² / (12 Σ_a K_a))`. -/
theorem normSq_cohInt_le_exp (K : Fin N → ℕ) (g : Fin N → SU2) (n : ℕ) :
    ∑ k, Complex.normSq (cohInt (fun a => n * K a) g k) ≤
      Real.exp (-(n * ((∑ a, (K a : ℝ) • bloch (g a)) ⬝ᵥ (∑ a, (K a : ℝ) • bloch (g a))) /
        (12 * ∑ a, (K a : ℝ)))) := by
  have hcomp : ∀ i, (∑ a, (K a : ℝ) • bloch (g a)) i = ∑ a, (K a : ℝ) * bloch (g a) i :=
    fun i => by simp [Finset.sum_apply]
  have hdot : (∑ a, (K a : ℝ) • bloch (g a)) ⬝ᵥ (∑ a, (K a : ℝ) • bloch (g a)) =
      (∑ a, (K a : ℝ) * bloch (g a) 0) ^ 2 + (∑ a, (K a : ℝ) * bloch (g a) 1) ^ 2 +
        (∑ a, (K a : ℝ) * bloch (g a) 2) ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_three, hcomp, sq]
  rw [hdot]
  exact le_exp_of_three (Nat.cast_nonneg n) (Finset.sum_nonneg fun a _ => Nat.cast_nonneg _)
    (normSq_cohInt_le_exp_axis K g n 0) (normSq_cohInt_le_exp_axis K g n 1)
    (normSq_cohInt_le_exp_axis K g n 2)

/-- **Coherent intertwiners whose normals do not close are exponentially suppressed**, at any
valence: if `Σ_a K_a ν_a ≠ 0`, there is `r < 1` with `‖ι_{nK}(g⃗)‖² ≤ rⁿ` for all `n`. -/
theorem cohInt_suppressed (K : Fin N → ℕ) (g : Fin N → SU2)
    (hN : ∑ a, (K a : ℝ) • bloch (g a) ≠ 0) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ n : ℕ, ∑ k, Complex.normSq (cohInt (fun a => n * K a) g k) ≤ r ^ n := by
  set V := ∑ a, (K a : ℝ) • bloch (g a) with hV
  set S := ∑ a, (K a : ℝ) with hS_def
  have hpos : 0 < V ⬝ᵥ V := by
    refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (V i)) fun h => hN ?_
    exact dotProduct_self_eq_zero.mp h.symm
  have hS : 0 < S := by
    rcases (Finset.sum_nonneg fun a _ => Nat.cast_nonneg (K a) : (0 : ℝ) ≤ S).eq_or_lt with h | h
    · exfalso
      apply hN
      have hK : ∀ a, (K a : ℝ) = 0 := fun a =>
        (Finset.sum_eq_zero_iff_of_nonneg fun a _ => Nat.cast_nonneg _).mp h.symm a (mem_univ a)
      simp [hV, hK]
    · exact h
  refine ⟨Real.exp (-(V ⬝ᵥ V / (12 * S))), (Real.exp_pos _).le,
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (div_pos hpos (by linarith))), fun n => ?_⟩
  refine (normSq_cohInt_le_exp K g n).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- `⟨v, v⟩ = Σ_k |v_k|²`, linking the bounds above to the norms `star ι ⬝ᵥ ι` used elsewhere. -/
lemma star_dotProduct_self_eq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    star v ⬝ᵥ v = ((∑ k, Complex.normSq (v k) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RCLike.star_def, mul_comm, Complex.mul_conj]

end Lightlike.Spin4
