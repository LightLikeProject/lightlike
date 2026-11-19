import Lightlike.Canonical.AshtekarCanonical
import Lightlike.Canonical.MatrixSmooth

/-!
# The variation of the spin connection satisfies the linearised compatibility condition

For a smooth co-triad `e` and a smooth variation `δe`, along the path `e_t = e + t δe` with the metrics `h_t = e_tᵀ e_t`,
the spin connection `Γ_t = spinConn e_t h_t` is differentiable in `t` at every point where `det e ≠ 0`
(`differentiableAt_spinConn_path`), and its derivative `δΓ` satisfies the linearisation of the compatibility condition
(Ashtekar–Lewandowski (2.17)) (`linCompat_dSpin`). So `integral_E_dSpin_eq_zero` applies to the actual variation of the
spin connection: `∫ E^a_i δΓ^i_a = 0` (`integral_E_deriv_spinConn_eq_zero`).

The compatibility along the path needs only local invertibility (`spin_compat_local`): the co-triad is replaced, away from
its invertibility domain, by the identity, which changes nothing near the point.
-/

open Matrix MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ}

/-- The Christoffel symbols at `x` depend only on the germ of the metric at `x`. -/
lemma christoffel_congr {g₁ g₂ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ} (h : g₁ =ᶠ[𝓝 x] g₂)
    (i j k : Fin n) : Lightlike.christoffel g₁ i j k x = Lightlike.christoffel g₂ i j k x := by
  have hx : g₁ x = g₂ x := h.self_of_nhds
  have hent : ∀ a b, (fun y => g₁ y a b) =ᶠ[𝓝 x] fun y => g₂ y a b := fun a b =>
    h.mono fun y hy => by show g₁ y a b = g₂ y a b; rw [hy]
  unfold Lightlike.christoffel
  rw [hx]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Lightlike.pd_congr (hent l k) j, Lightlike.pd_congr (hent l j) k, Lightlike.pd_congr (hent j k) l]

/-- The spin connection at `x` depends only on the germs of the co-triad and of the metric at `x`. -/
lemma spinConn_congr {e₁ e₂ : CoTriad} {h₁ h₂ : TensorField 3} {x : Fin 3 → ℝ} (he : e₁ =ᶠ[𝓝 x] e₂)
    (hh : h₁ =ᶠ[𝓝 x] h₂) : spinConn e₁ h₁ x = spinConn e₂ h₂ x := by
  have hx : e₁ x = e₂ x := he.self_of_nhds
  have hent : ∀ k b, (fun y => e₁ y k b) =ᶠ[𝓝 x] fun y => e₂ y k b := fun k b =>
    he.mono fun y hy => by show e₁ y k b = e₂ y k b; rw [hy]
  ext a i
  simp only [spinConn, triadOmega, covTriad, Matrix.of_apply, hx, christoffel_congr hh,
    fun k b => Lightlike.pd_congr (hent k b) a]

/-- **Compatibility with local invertibility**: for a smooth co-triad `e` of `h` (`h = eᵀ e` everywhere) with
`det e(x) ≠ 0`, the compatibility condition holds at `x`. -/
theorem spin_compat_local {e : CoTriad} {h : TensorField 3} (hh : ∀ y, (e y)ᵀ * e y = h y)
    (hs : ∀ i b, ContDiff ℝ ∞ (fun y => e y i b)) {x : Fin 3 → ℝ} (hx : (e x).det ≠ 0) (k a b : Fin 3) :
    Lightlike.pd a (fun y => e y k b) x - Lightlike.pd b (fun y => e y k a) x +
      ∑ i, ∑ j, eps3 k i j * (spinConn e h x a i * e x j b - spinConn e h x b i * e x j a) = 0 := by
  classical
  have hdetc : Continuous fun y => (e y).det := by
    have : ∀ i j, Continuous fun y => e y i j := fun i j => (hs i j).continuous
    simp only [Matrix.det_apply]
    fun_prop
  set V : Set (Fin 3 → ℝ) := {y | (e y).det ≠ 0} with hV
  have hVo : IsOpen V := isOpen_ne_fun hdetc continuous_const
  have hxV : x ∈ V := hx
  set e' : CoTriad := fun y => if (e y).det ≠ 0 then e y else 1 with he'
  set h' : TensorField 3 := fun y => (e' y)ᵀ * e' y with hh'
  have hee : e' =ᶠ[𝓝 x] e := eventually_of_mem (hVo.mem_nhds hxV) fun y hy => by
    simp only [he', ite_eq_left (show (e y).det ≠ 0 from hy)]
  have hhh : h' =ᶠ[𝓝 x] h := hee.mono fun y hy => by simp only [hh', hy, hh]
  have hT : IsCoTriad e' h' := fun y => by
    refine ⟨?_, rfl⟩
    by_cases hy : (e y).det ≠ 0
    · simp only [he', ite_eq_left hy]; exact isUnit_iff_ne_zero.2 hy
    · simp only [he', ite_eq_right hy, det_one, isUnit_one]
  have hg : IsCoordMetric h' V := by
    refine ⟨hVo, fun y _ => by simp [hh', Matrix.transpose_mul], fun y hy => ?_, fun i j => ?_⟩
    · rw [hh', det_mul, det_transpose]; exact (hT y).1.mul (hT y).1
    · have hsm : ContDiff ℝ ∞ (fun y => h y i j) := by
        have : (fun y => h y i j) = fun y => ∑ l, e y l i * e y l j := funext fun y => by
          rw [← hh y]; simp [Matrix.mul_apply, Matrix.transpose_apply]
        rw [this]; exact ContDiff.sum fun l _ => (hs l i).mul (hs l j)
      refine hsm.contDiffOn.congr fun y hy => ?_
      have : e' y = e y := by simp only [he', ite_eq_left (show (e y).det ≠ 0 from hy)]
      simp only [hh', this, hh]
  have hd : ∀ i b, DifferentiableAt ℝ (fun y => e' y i b) x := fun i b =>
    (((hs i b).differentiable (by simp)) x).congr_of_eventuallyEq
      (hee.mono fun y hy => by show e' y i b = e y i b; rw [hy])
  have hc := spin_compat hT hg hxV hd k a b
  have hent : ∀ k b, (fun y => e' y k b) =ᶠ[𝓝 x] fun y => e y k b := fun k b =>
    hee.mono fun y hy => by show e' y k b = e y k b; rw [hy]
  rw [Lightlike.pd_congr (hent k b) a, Lightlike.pd_congr (hent k a) b, spinConn_congr hee hhh,
    hee.self_of_nhds] at hc
  exact hc

section Path

variable (e δe : CoTriad) (x : Fin 3 → ℝ)

/-- `∂_a` of the entries of the path `e + t δe`. -/
lemma pd_path {t : ℝ} (hde : ∀ k b, DifferentiableAt ℝ (fun y => e y k b) x)
    (hdl : ∀ k b, DifferentiableAt ℝ (fun y => δe y k b) x) (a k b : Fin 3) :
    Lightlike.pd a (fun y => (e y + t • δe y) k b) x =
      Lightlike.pd a (fun y => e y k b) x + t * Lightlike.pd a (fun y => δe y k b) x := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Lightlike.pd_add (hde k b) ((hdl k b).const_mul t), Lightlike.pd_const_mul _ (hdl k b)]

/-- `∂_a` of the entries of the metric `(e + t δe)ᵀ (e + t δe)` of the path. -/
lemma pd_pathMetric {t : ℝ} (hde : ∀ k b, DifferentiableAt ℝ (fun y => e y k b) x)
    (hdl : ∀ k b, DifferentiableAt ℝ (fun y => δe y k b) x) (a l m : Fin 3) :
    Lightlike.pd a (fun y => ((e y + t • δe y)ᵀ * (e y + t • δe y)) l m) x =
      ∑ i, ((Lightlike.pd a (fun y => e y i l) x + t * Lightlike.pd a (fun y => δe y i l) x) *
          (e x i m + t * δe x i m) +
        (e x i l + t * δe x i l) *
          (Lightlike.pd a (fun y => e y i m) x + t * Lightlike.pd a (fun y => δe y i m) x)) := by
  have dp : ∀ k b, DifferentiableAt ℝ (fun y => (e y + t • δe y) k b) x := fun k b => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (hde k b).add ((hdl k b).const_mul t)
  have hf : (fun y => ((e y + t • δe y)ᵀ * (e y + t • δe y)) l m) =
      fun y => ∑ i, (e y + t • δe y) i l * (e y + t • δe y) i m := funext fun y => by
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  rw [hf, Lightlike.pd_sum (f := fun i y => (e y + t • δe y) i l * (e y + t • δe y) i m) _
    (fun i _ => (dp i l).mul (dp i m))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Lightlike.pd_mul (dp i l) (dp i m), pd_path e δe x hde hdl, pd_path e δe x hde hdl]
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- **The spin connection is smooth along the path** `e + t δe` (with the metrics of the path), at `t = 0`, at a point
where `det e ≠ 0`. -/
theorem contDiffAt_spinConn_path (hde : ∀ k b, DifferentiableAt ℝ (fun y => e y k b) x)
    (hdl : ∀ k b, DifferentiableAt ℝ (fun y => δe y k b) x) (hx : (e x).det ≠ 0) (a i : Fin 3) :
    ContDiffAt ℝ ∞ (fun t : ℝ => spinConn (fun y => e y + t • δe y)
      (fun y => (e y + t • δe y)ᵀ * (e y + t • δe y)) x a i) 0 := by
  have hM1 : ∀ p q, ContDiffAt ℝ ∞ (fun t : ℝ => (e x + t • δe x) p q) 0 := fun p q => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; fun_prop
  have hinv1 : ∀ b j, ContDiffAt ℝ ∞ (fun t : ℝ => (e x + t • δe x)⁻¹ b j) 0 := fun b j =>
    contDiffAt_inv_entry (fun t : ℝ => e x + t • δe x) hM1 (by simpa using hx) b j
  have hM2 : ∀ p q, ContDiffAt ℝ ∞ (fun t : ℝ => ((e x + t • δe x)ᵀ * (e x + t • δe x)) p q) 0 := fun p q => by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiffAt.sum fun l _ => (hM1 l p).mul (hM1 l q)
  have hinv2 : ∀ c l, ContDiffAt ℝ ∞ (fun t : ℝ => ((e x + t • δe x)ᵀ * (e x + t • δe x))⁻¹ c l) 0 :=
    fun c l => contDiffAt_inv_entry (fun t : ℝ => (e x + t • δe x)ᵀ * (e x + t • δe x)) hM2
      (by simp [det_mul, hx]) c l
  have hpdp : ∀ a k b, ContDiffAt ℝ ∞ (fun t : ℝ => Lightlike.pd a (fun y => (e y + t • δe y) k b) x) 0 := by
    intro a k b
    have : (fun t : ℝ => Lightlike.pd a (fun y => (e y + t • δe y) k b) x) = fun t : ℝ =>
        Lightlike.pd a (fun y => e y k b) x + t * Lightlike.pd a (fun y => δe y k b) x :=
      funext fun t => pd_path e δe x hde hdl a k b
    rw [this]; fun_prop
  have hpdh : ∀ a l m, ContDiffAt ℝ ∞
      (fun t : ℝ => Lightlike.pd a (fun y => ((e y + t • δe y)ᵀ * (e y + t • δe y)) l m) x) 0 := by
    intro a l m
    rw [show (fun t : ℝ => Lightlike.pd a (fun y => ((e y + t • δe y)ᵀ * (e y + t • δe y)) l m) x) = _ from
      funext fun t => pd_pathMetric e δe x hde hdl a l m]
    fun_prop
  have hchr : ∀ c a b, ContDiffAt ℝ ∞ (fun t : ℝ =>
      Lightlike.christoffel (fun y => (e y + t • δe y)ᵀ * (e y + t • δe y)) c a b x) 0 := by
    intro c a b
    unfold Lightlike.christoffel
    exact contDiffAt_const.mul (ContDiffAt.sum fun l _ =>
      (hinv2 c l).mul (((hpdh a l b).add (hpdh b l a)).sub (hpdh l a b)))
  unfold spinConn triadOmega covTriad
  simp only [Matrix.of_apply]
  exact contDiffAt_const.mul (ContDiffAt.sum fun j _ => ContDiffAt.sum fun k _ =>
    contDiffAt_const.mul (ContDiffAt.sum fun b _ => (hinv1 b j).mul
      ((hpdp a k b).sub (ContDiffAt.sum fun c _ => (hchr c a b).mul (hM1 k c)))))

/-- **The variation of the spin connection satisfies the linearised compatibility condition**: with
`δΓ = d/dt|₀ Γ(e + t δe)` (`Γ` the spin connection of the path with its metrics `(e + tδe)ᵀ(e + tδe)`),
`∂_a δe^k_b − ∂_b δe^k_a + ε_kij (δΓ^i_a e^j_b + Γ^i_a δe^j_b − δΓ^i_b e^j_a − Γ^i_b δe^j_a) = 0` at every point where
`det e ≠ 0`. -/
theorem linCompat_dSpin (hs : ∀ k b, ContDiff ℝ ∞ (fun y => e y k b)) (hδ : ∀ k b, ContDiff ℝ ∞ (fun y => δe y k b))
    (hx : (e x).det ≠ 0) (k a b : Fin 3) :
    Lightlike.pd a (fun y => δe y k b) x - Lightlike.pd b (fun y => δe y k a) x +
      ∑ i, ∑ j, eps3 k i j *
        (deriv (fun t : ℝ => spinConn (fun y => e y + t • δe y)
            (fun y => (e y + t • δe y)ᵀ * (e y + t • δe y)) x a i) 0 * e x j b +
          spinConn e (fun y => (e y)ᵀ * e y) x a i * δe x j b -
          deriv (fun t : ℝ => spinConn (fun y => e y + t • δe y)
            (fun y => (e y + t • δe y)ᵀ * (e y + t • δe y)) x b i) 0 * e x j a -
          spinConn e (fun y => (e y)ᵀ * e y) x b i * δe x j a) = 0 := by
  have hde : ∀ k b, DifferentiableAt ℝ (fun y => e y k b) x := fun k b => ((hs k b).differentiable (by simp)) x
  have hdl : ∀ k b, DifferentiableAt ℝ (fun y => δe y k b) x := fun k b => ((hδ k b).differentiable (by simp)) x
  set Γt : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun t => spinConn (fun y => e y + t • δe y)
    (fun y => (e y + t • δe y)ᵀ * (e y + t • δe y)) x with hΓt
  have hΓ0 : Γt 0 = spinConn e (fun y => (e y)ᵀ * e y) x := by simp [hΓt]
  have hΓ : ∀ p q, HasDerivAt (fun t => Γt t p q) (deriv (fun t => Γt t p q) 0) 0 := fun p q =>
    ((contDiffAt_spinConn_path e δe x hde hdl hx p q).differentiableAt (by simp)).hasDerivAt
  -- the compatibility condition along the path
  set C : ℝ → ℝ := fun t => Lightlike.pd a (fun y => (e y + t • δe y) k b) x -
    Lightlike.pd b (fun y => (e y + t • δe y) k a) x +
    ∑ i, ∑ j, eps3 k i j * (Γt t a i * (e x + t • δe x) j b - Γt t b i * (e x + t • δe x) j a) with hC
  have hdetc : ContinuousAt (fun t : ℝ => (e x + t • δe x).det) 0 := by
    have : Continuous fun t : ℝ => (e x + t • δe x).det := by
      simp only [Matrix.det_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; fun_prop
    exact this.continuousAt
  have hev : C =ᶠ[nhds 0] fun _ => 0 := by
    have hne : ∀ᶠ t in nhds (0 : ℝ), (e x + t • δe x).det ≠ 0 :=
      hdetc.eventually_ne (by simpa using hx)
    filter_upwards [hne] with t ht
    have hst : ∀ k b, ContDiff ℝ ∞ (fun y => (e y + t • δe y) k b) := fun k b => by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact (hs k b).add (contDiff_const.mul (hδ k b))
    exact spin_compat_local (e := fun y => e y + t • δe y) (fun y => rfl) hst ht k a b
  have hPa : ∀ a k b, HasDerivAt (fun t : ℝ => Lightlike.pd a (fun y => (e y + t • δe y) k b) x)
      (Lightlike.pd a (fun y => δe y k b) x) 0 := fun a k b => by
    rw [show (fun t : ℝ => Lightlike.pd a (fun y => (e y + t • δe y) k b) x) = fun t : ℝ =>
      Lightlike.pd a (fun y => e y k b) x + t * Lightlike.pd a (fun y => δe y k b) x from
      funext fun t => pd_path e δe x hde hdl a k b]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Lightlike.pd a (fun y => δe y k b) x)).const_add
      (Lightlike.pd a (fun y => e y k b) x)
  have hEt : ∀ j b, HasDerivAt (fun t : ℝ => (e x + t • δe x) j b) (δe x j b) 0 := fun j b => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δe x j b)).const_add (e x j b)
  have hCd : HasDerivAt C (Lightlike.pd a (fun y => δe y k b) x - Lightlike.pd b (fun y => δe y k a) x +
      ∑ i, ∑ j, eps3 k i j * ((deriv (fun t => Γt t a i) 0 * (e x + (0 : ℝ) • δe x) j b +
        Γt 0 a i * δe x j b) - (deriv (fun t => Γt t b i) 0 * (e x + (0 : ℝ) • δe x) j a +
        Γt 0 b i * δe x j a))) 0 := by
    refine ((hPa a k b).sub (hPa b k a)).add ?_
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    exact (((hΓ a i).mul (hEt j b)).sub ((hΓ b i).mul (hEt j a))).const_mul (eps3 k i j)
  have h0 := hCd.deriv
  rw [hev.deriv_eq] at h0
  simp only [deriv_const] at h0
  rw [hΓ0] at h0
  simp only [zero_smul, add_zero] at h0
  simp only [hΓt, Fin.sum_univ_three] at h0 ⊢
  linear_combination -h0

end Path


/-- **`∫ E^a_i δΓ^i_a = 0` for the variation of the spin connection** along `e + t δe`, for a smooth positively
oriented co-triad `e` and a smooth compactly supported `δe`: the functional derivative of `∫ Γ^i_a E^a_i` with respect to
`E` is `Γ` (Holst (5)–(6)). -/
theorem integral_E_deriv_spinConn_eq_zero (e δe : CoTriad) (hs : ∀ k b, ContDiff ℝ ∞ (fun y => e y k b))
    (hδ : ∀ k b, ContDiff ℝ ∞ (fun y => δe y k b)) (hδc : ∀ k b, HasCompactSupport (fun y => δe y k b))
    (hpos : ∀ y, 0 < (e y).det) :
    ∫ y, ∑ a, ∑ j, densTriad e y a j *
      deriv (fun t : ℝ => spinConn (fun z => e z + t • δe z)
        (fun z => (e z + t • δe z)ᵀ * (e z + t • δe z)) y a j) 0 = 0 := by
  refine integral_E_dSpin_eq_zero e δe (fun y => spinConn e (fun z => (e z)ᵀ * e z) y)
    (fun y => Matrix.of fun a j => deriv (fun t : ℝ => spinConn (fun z => e z + t • δe z)
      (fun z => (e z + t • δe z)ᵀ * (e z + t • δe z)) y a j) 0) hs hδ hδc hpos ?_ ?_
  · intro y k a b
    exact spin_compat_local (fun z => rfl) hs (hpos y).ne' k a b
  · intro y k a b
    simpa using linCompat_dSpin e δe y hs hδ (hpos y).ne' k a b

end Lightlike.Canonical
