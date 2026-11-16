module

public import Lightlike.GR.Einstein

/-!
# FLRW spacetimes: Einstein's equations and Friedmann's equations


* `flrwMetric a k` : the metric `-dt² + a(t)² dx² / (1 + k |x|²/4)²` in the chart `(t, x)`, for
  every real `k` (isotropic coordinates).
* `flrwDomain I k` : `t ∈ I` and `1 + k |x|²/4 > 0`. For `k ≥ 0` this is all of `I × ℝ³`; for
  `k < 0` it is the ball `|x| < 2/√|k|`, which is the whole hyperbolic space (the Poincaré ball).
* `perfectFluid ρ p g` : `T_{μν} = (ρ + p) u_μ u_ν + p g_{μν}` for the fluid at rest in the chart.
* `IsEinsteinSolution Λ G g T U` : `g` is a coordinate metric on `U` and `G_{μν} + Λ g_{μν} = 8πG T_{μν}`.
* `FirstFriedmann`, `SecondFriedmann` : Friedmann's equations for `a, ρ, p : ℝ → ℝ`, units `c = 1`
  (the same equations as Physlib's `FirstOrderFriedmann` and `SecondOrderFriedmann` at `c = 1`;
  the bridge to those definitions is a separate file, so that this one needs no Physlib build).
* `flrw_einstein_iff_friedmann` : Einstein's equations hold iff the two Friedmann equations hold.
* `friedmann_continuity` : `ρ' + 3H(ρ + p) = 0` follows where `a' ≠ 0`.

**References.** S. M. Carroll, *Lecture Notes on General Relativity* (1997), eqs. (8.29),
(8.33) to (8.36). The curvature identities used are cross-checked in `scripts/flrw_check.py`.
-/

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

namespace Cosmology

/-- The squared Euclidean norm of the spatial part of a point of the chart. -/
def spatialNormSq (x : Fin 4 → ℝ) : ℝ := ∑ i : Fin 3, x i.succ ^ 2

/-- The FLRW metric `-dt² + a(t)² dx² / (1 + k |x|²/4)²` in the chart `(t, x)`. -/
def flrwMetric (a : ℝ → ℝ) (k : ℝ) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun x => Matrix.diagonal fun μ =>
    if μ = 0 then -1 else (a (x 0) / (1 + k * spatialNormSq x / 4)) ^ 2

/-- The domain of the chart: `t ∈ I` and `1 + k |x|²/4 > 0`. -/
def flrwDomain (I : Set ℝ) (k : ℝ) : Set (Fin 4 → ℝ) :=
  {x | x 0 ∈ I ∧ 0 < 1 + k * spatialNormSq x / 4}

/-- The stress-energy tensor `(ρ + p) u_μ u_ν + p g_{μν}` of a perfect fluid at rest in the
chart, `u^μ = (1, 0, 0, 0)`, so `u_μ = g_{μ0}`. -/
def perfectFluid (ρ p : ℝ → ℝ) (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (μ ν : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  (ρ (x 0) + p (x 0)) * g x μ 0 * g x ν 0 + p (x 0) * g x μ ν

/-- Einstein's equations with cosmological constant `Λ` and matter `T`, in units `c = 1`:
`G_{μν} + Λ g_{μν} = 8πG T_{μν}` on `U`, with `g` a coordinate metric on `U`. -/
def IsEinsteinSolution (Λ Gn : ℝ) (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (T : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℝ) (U : Set (Fin 4 → ℝ)) : Prop :=
  IsCoordMetric g U ∧ ∀ x ∈ U, ∀ μ ν,
    einsteinTensor g μ ν x + Λ * g x μ ν = 8 * Real.pi * Gn * T μ ν x

/-- Friedmann's first equation, `(a'/a)² = 8πGρ/3 - k/a² + Λ/3`, units `c = 1`. -/
def FirstFriedmann (a ρ : ℝ → ℝ) (k Λ Gn : ℝ) (t : ℝ) : Prop :=
  (deriv a t / a t) ^ 2 = 8 * Real.pi * Gn / 3 * ρ t - k / a t ^ 2 + Λ / 3

/-- Friedmann's second equation, `a''/a = -(4πG/3)(ρ + 3p) + Λ/3`, units `c = 1`. -/
def SecondFriedmann (a ρ p : ℝ → ℝ) (Λ Gn : ℝ) (t : ℝ) : Prop :=
  deriv (deriv a) t / a t = -(4 * Real.pi * Gn / 3) * (ρ t + 3 * p t) + Λ / 3

section FLRWCurvature

/-- `f` is differentiable at `x` and its partial derivative in the direction `j` there is `v`. -/
def HasPd (j : Fin 4) (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (v : ℝ) : Prop :=
  DifferentiableAt ℝ f x ∧ pd j f x = v

variable {j : Fin 4} {f g : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} {u v k : ℝ}

theorem HasPd.add (hf : HasPd j f x u) (hg : HasPd j g x v) :
    HasPd j (fun y => f y + g y) x (u + v) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  have h1 := hf.2; have h2 := hg.2
  unfold pd at *
  rw [show (fun y => f y + g y) = f + g from rfl, (hf.1.hasFDerivAt.add hg.1.hasFDerivAt).fderiv]; simp [h1, h2]

theorem HasPd.mul (hf : HasPd j f x u) (hg : HasPd j g x v) :
    HasPd j (fun y => f y * g y) x (f x * v + g x * u) := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  have h1 := hf.2; have h2 := hg.2
  unfold pd at *
  rw [show (fun y => f y * g y) = f * g from rfl, (hf.1.hasFDerivAt.mul hg.1.hasFDerivAt).fderiv]; simp [h1, h2]

theorem HasPd.neg (hf : HasPd j f x u) : HasPd j (fun y => - f y) x (-u) := by
  refine ⟨hf.1.neg, ?_⟩
  have h1 := hf.2
  unfold pd at *
  rw [show (fun y => - f y) = -f from rfl, hf.1.hasFDerivAt.neg.fderiv]; simp [h1]

theorem HasPd.const (c : ℝ) : HasPd j (fun _ => c) x 0 :=
  ⟨differentiableAt_const c, pd_const _ _ _⟩

theorem HasPd.inv (hf : HasPd j f x u) (h0 : f x ≠ 0) :
    HasPd j (fun y => (f y)⁻¹) x (-(u / f x ^ 2)) := by
  refine ⟨hf.1.inv h0, ?_⟩
  have h1 := hf.2
  unfold pd at *
  have hc := (hasFDerivAt_inv' (𝕜 := ℝ) h0).comp x hf.1.hasFDerivAt
  rw [show (fun y => (f y)⁻¹) = Inv.inv ∘ f from rfl, hc.fderiv]
  simp [h1]
  field_simp

theorem hasPd_coord (m : Fin 4) : HasPd j (fun y => y m) x (if j = m then 1 else 0) := by
  refine ⟨(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) m).differentiableAt, ?_⟩
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) m).hasFDerivAt (x := x)
  simp only [pd]
  rw [show (fun y : Fin 4 → ℝ => y m) = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) m) from rfl, this.fderiv]
  simp [Pi.single_apply, eq_comm]

theorem hasPd_comp0 {φ : ℝ → ℝ} (hφ : DifferentiableAt ℝ φ (x 0)) :
    HasPd j (fun y => φ (y 0)) x (if j = 0 then deriv φ (x 0) else 0) := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).hasFDerivAt (x := x)
  have hc := hφ.hasDerivAt.comp_hasFDerivAt x h0
  refine ⟨hc.differentiableAt, ?_⟩
  simp only [pd]
  rw [show (fun y : Fin 4 → ℝ => φ (y 0)) = φ ∘ ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0) from rfl, hc.fderiv]
  simp [Pi.single_apply, eq_comm]

/-- `1 + k |x|² / 4`. -/
def Dn (k : ℝ) (y : Fin 4 → ℝ) : ℝ := 1 + k * spatialNormSq y / 4
/-- `1 / (1 + k |x|²/4)`. -/
def Sf (k : ℝ) (y : Fin 4 → ℝ) : ℝ := (Dn k y)⁻¹

theorem hasPd_nsq : HasPd j spatialNormSq x (if j = 0 then 0 else 2 * x j) := by
  have h : spatialNormSq = fun y => y 1 * y 1 + y 2 * y 2 + y 3 * y 3 := by
    funext y; simp [spatialNormSq, Fin.sum_univ_three, sq]
  rw [h]
  have e1 := (hasPd_coord (j := j) (x := x) 1)
  have e2 := (hasPd_coord (j := j) (x := x) 2)
  have e3 := (hasPd_coord (j := j) (x := x) 3)
  have := ((e1.mul e1).add (e2.mul e2)).add (e3.mul e3)
  convert this using 1
  fin_cases j <;> simp <;> ring

theorem hasPd_Dn : HasPd j (Dn k) x (if j = 0 then 0 else k / 2 * x j) := by
  have := ((HasPd.const 1 (j := j) (x := x)).add ((HasPd.const (k / 4) (j := j) (x := x)).mul
    (hasPd_nsq (j := j) (x := x))))
  unfold Dn
  convert this using 1
  · funext y; ring
  · fin_cases j <;> simp <;> ring

theorem hasPd_Sf (hD : Dn k x ≠ 0) :
    HasPd j (Sf k) x (if j = 0 then 0 else -(k / 2 * x j) * Sf k x ^ 2) := by
  have := (hasPd_Dn (j := j) (x := x) (k := k)).inv hD
  unfold Sf
  convert this using 1
  fin_cases j <;> simp [Sf] <;> field_simp

theorem christoffel_diag (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (d : (Fin 4 → ℝ) → Fin 4 → ℝ)
    (hg : ∀ y, g y = Matrix.diagonal (d y)) (x : Fin 4 → ℝ) (hd : ∀ i, d x i ≠ 0)
    (i j l : Fin 4) :
    christoffel g i j l x =
      1 / 2 * (d x i)⁻¹ * (pd j (fun y => g y i l) x +
        pd l (fun y => g y i j) x - pd i (fun y => g y j l) x) := by
  have hinv : (Matrix.diagonal (d x))⁻¹ = Matrix.diagonal (fun i => (d x i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one (n := Fin 4) (α := ℝ) using 2
    funext i; exact mul_inv_cancel₀ (hd i)
  unfold christoffel
  rw [hg x, hinv, Finset.sum_eq_single i]
  · simp; ring
  · intro b _ hb; simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · simp

/-- derivative of the scale-factor entry `Ψ = a S`. -/
def dPsi (a : ℝ → ℝ) (k : ℝ) (m : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  if m = 0 then deriv a (x 0) * Sf k x else a (x 0) * (-(k / 2 * x m) * Sf k x ^ 2)

theorem hasPd_Psi {a : ℝ → ℝ} (ha : DifferentiableAt ℝ a (x 0)) (hD : Dn k x ≠ 0) :
    HasPd j (fun y => a (y 0) * Sf k y) x (dPsi a k j x) := by
  have := (hasPd_comp0 (j := j) ha).mul (hasPd_Sf (j := j) hD)
  convert this using 1
  fin_cases j <;> simp [dPsi] <;> ring

theorem flrwEntry_eq (a : ℝ → ℝ) (k : ℝ) (y : Fin 4 → ℝ) (p q : Fin 4) :
    flrwMetric a k y p q = if p = q then (if p = 0 then -1 else (a (y 0) * Sf k y) * (a (y 0) * Sf k y)) else 0 := by
  unfold flrwMetric Sf Dn
  by_cases h : p = q
  · subst h; by_cases hp : p = 0 <;> simp [hp, div_eq_mul_inv, sq]
  · simp [Matrix.diagonal_apply_ne _ h, h]

theorem pd_flrwEntry {a : ℝ → ℝ} (ha : DifferentiableAt ℝ a (x 0)) (hD : Dn k x ≠ 0) (m p q : Fin 4) :
    pd m (fun y => flrwMetric a k y p q) x =
      if p = q then (if p = 0 then 0 else 2 * (a (x 0) * Sf k x) * dPsi a k m x) else 0 := by
  have hfun : (fun y => flrwMetric a k y p q) =
      fun y => if p = q then (if p = 0 then -1 else (a (y 0) * Sf k y) * (a (y 0) * Sf k y)) else 0 := by
    funext y; exact flrwEntry_eq a k y p q
  rw [hfun]
  by_cases h : p = q
  · subst h
    by_cases hp : p = 0
    · simp [hp, pd_const]
    · simp only [hp, ite_true, ite_false]
      have := (hasPd_Psi (j := m) ha hD).mul (hasPd_Psi (j := m) ha hD)
      rw [this.2]; ring
  · simp [h, pd_const]

/-- The diagonal of the FLRW metric in the chart: `-1` in time, `(a(t) / (1 + k |x|²/4))²`
in space. -/
def dF (a : ℝ → ℝ) (k : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => if μ = 0 then -1 else (a (y 0) / (1 + k * spatialNormSq y / 4)) ^ 2

/-- `a a' / (1 + k |x|²/4)²`, the time-space Christoffel symbols' common factor. -/
def F0 (a : ℝ → ℝ) (k : ℝ) (y : Fin 4 → ℝ) : ℝ := a (y 0) * deriv a (y 0) * Sf k y ^ 2
/-- The Hubble rate `a'/a` at the time coordinate of `y`. -/
def Hf (a : ℝ → ℝ) (y : Fin 4 → ℝ) : ℝ := deriv a (y 0) / a (y 0)
/-- `-(k/2) xᵢ / (1 + k |x|²/4)`, the spatial Christoffel symbols' common factor. -/
def Lf (k : ℝ) (i : Fin 4) (y : Fin 4 → ℝ) : ℝ := -(k / 2 * y i) * Sf k y

/-- The Christoffel symbols `Γ^i_{jl}` of the FLRW metric, in closed form. -/
def Γf (a : ℝ → ℝ) (k : ℝ) (i j l : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if i = 0 then (if j = l ∧ j ≠ 0 then F0 a k y else 0)
  else if j = 0 then (if l = i then Hf a y else 0)
  else if l = 0 then (if j = i then Hf a y else 0)
  else (if i = j then Lf k l y else 0) + (if i = l then Lf k j y else 0)
    - (if j = l then Lf k i y else 0)

theorem christoffel_flrw {a : ℝ → ℝ} (ha : DifferentiableAt ℝ a (x 0)) (hpos : a (x 0) ≠ 0)
    (hD : Dn k x ≠ 0) (i j l : Fin 4) :
    christoffel (flrwMetric a k) i j l x = Γf a k i j l x := by
  have hd : ∀ i, dF a k x i ≠ 0 := by
    intro i; unfold dF; split_ifs
    · norm_num
    · exact pow_ne_zero 2 (div_ne_zero hpos hD)
  rw [christoffel_diag (flrwMetric a k) (dF a k) (fun y => rfl) x hd, pd_flrwEntry ha hD,
    pd_flrwEntry ha hD, pd_flrwEntry ha hD]
  have hD4 : 4 + k * spatialNormSq x ≠ 0 := by
    intro h; apply hD; unfold Dn; linarith
  have hD' : 1 + k * spatialNormSq x / 4 ≠ 0 := hD
  fin_cases i <;> fin_cases j <;> fin_cases l <;>
    simp [Γf, F0, Hf, Lf, dPsi, dF, Sf, Dn] <;> field_simp <;> ring

/-- The partial derivative of `F0` in the direction `m`. -/
def dF0 (a : ℝ → ℝ) (k : ℝ) (m : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  if m = 0 then (deriv a (x 0) ^ 2 + a (x 0) * deriv (deriv a) (x 0)) * Sf k x ^ 2
  else -(k * a (x 0) * deriv a (x 0) * x m) * Sf k x ^ 3
/-- The partial derivative of `Hf` in the direction `m`. -/
def dH (a : ℝ → ℝ) (m : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  if m = 0 then (deriv (deriv a) (x 0) * a (x 0) - deriv a (x 0) ^ 2) / a (x 0) ^ 2 else 0
/-- The partial derivative of `Lf k i` in the direction `m`. -/
def dL (k : ℝ) (m i : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  if m = 0 then 0 else
    -(k / 2 * (if m = i then 1 else 0)) * Sf k x + (-(k / 2 * x i)) * (-(k / 2 * x m) * Sf k x ^ 2)

theorem HasPd.ite {c : Prop} [Decidable c] (hf : HasPd j f x u) :
    HasPd j (fun y => if c then f y else 0) x (if c then u else 0) := by
  by_cases h : c <;> simp [h, hf, HasPd.const]

theorem hasPd_F0 {a : ℝ → ℝ} (ha : DifferentiableAt ℝ a (x 0))
    (ha' : DifferentiableAt ℝ (deriv a) (x 0)) (hD : Dn k x ≠ 0) :
    HasPd j (F0 a k) x (dF0 a k j x) := by
  have hS := hasPd_Sf (j := j) hD
  have := ((hasPd_comp0 (j := j) ha).mul (hasPd_comp0 (j := j) ha')).mul (hS.mul hS)
  unfold F0
  convert this using 1
  · funext y; ring
  · fin_cases j <;> simp [dF0] <;> ring

theorem hasPd_Hf {a : ℝ → ℝ} (ha : DifferentiableAt ℝ a (x 0))
    (ha' : DifferentiableAt ℝ (deriv a) (x 0)) (hpos : a (x 0) ≠ 0) :
    HasPd j (Hf a) x (dH a j x) := by
  have := (hasPd_comp0 (j := j) ha').mul ((hasPd_comp0 (j := j) ha).inv hpos)
  unfold Hf
  convert this using 1
  · funext y; ring
  · fin_cases j <;> simp [dH] <;> field_simp <;> ring

theorem hasPd_Lf (i : Fin 4) (hi : i ≠ 0) (hD : Dn k x ≠ 0) : HasPd j (Lf k i) x (dL k j i x) := by
  have := (((HasPd.const (-(k / 2)) (j := j) (x := x)).mul (hasPd_coord (j := j) (x := x) i))).mul
    (hasPd_Sf (j := j) hD)
  unfold Lf
  convert this using 1
  · funext y; ring
  · fin_cases j <;> fin_cases i <;> simp_all [dL] <;> ring

/-- derivative of the Christoffel closed form. -/
def dΓf (a : ℝ → ℝ) (k : ℝ) (m i j l : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if i = 0 then (if j = l ∧ j ≠ 0 then dF0 a k m y else 0)
  else if j = 0 then (if l = i then dH a m y else 0)
  else if l = 0 then (if j = i then dH a m y else 0)
  else (if i = j then dL k m l y else 0) + (if i = l then dL k m j y else 0)
    - (if j = l then dL k m i y else 0)

theorem hasPd_Γf {a : ℝ → ℝ} (ha : DifferentiableAt ℝ a (x 0))
    (ha' : DifferentiableAt ℝ (deriv a) (x 0)) (hpos : a (x 0) ≠ 0) (hD : Dn k x ≠ 0)
    (m i j l : Fin 4) : HasPd m (Γf a k i j l) x (dΓf a k m i j l x) := by
  have hF := hasPd_F0 (j := m) ha ha' hD
  have hH := hasPd_Hf (j := m) ha ha' hpos
  have hL := fun p hp => hasPd_Lf (j := m) (k := k) p hp hD
  unfold Γf dΓf
  by_cases h1 : i = 0
  · simp only [h1, ite_true]; exact hF.ite
  · simp only [h1, ite_false]
    by_cases h2 : j = 0
    · simp only [h2, ite_true]; exact hH.ite
    · simp only [h2, ite_false]
      by_cases h3 : l = 0
      · simp only [h3, ite_true]; exact hH.ite
      · simp only [h3, ite_false]
        have := (((hL l h3).ite (c := i = j)).add ((hL j h2).ite (c := i = l))).add
          (((hL i h1).ite (c := j = l)).neg)
        simpa [sub_eq_add_neg] using this

theorem pd_christoffel_flrw {a : ℝ → ℝ}
    (hnb : ∀ᶠ y in nhds x, DifferentiableAt ℝ a (y 0) ∧ a (y 0) ≠ 0 ∧ Dn k y ≠ 0)
    (ha' : DifferentiableAt ℝ (deriv a) (x 0)) (m i j l : Fin 4) :
    pd m (christoffel (flrwMetric a k) i j l) x = dΓf a k m i j l x := by
  have hx := hnb.self_of_nhds
  have heq : christoffel (flrwMetric a k) i j l =ᶠ[nhds x] Γf a k i j l := by
    filter_upwards [hnb] with y hy using christoffel_flrw hy.1 hy.2.1 hy.2.2 i j l
  have : pd m (christoffel (flrwMetric a k) i j l) x = pd m (Γf a k i j l) x := by
    unfold pd; rw [heq.fderiv_eq]
  rw [this]
  exact (hasPd_Γf hx.1 ha' hx.2.1 hx.2.2 m i j l).2

theorem ricci_flrw {a : ℝ → ℝ}
    (hnb : ∀ᶠ y in nhds x, DifferentiableAt ℝ a (y 0) ∧ a (y 0) ≠ 0 ∧ Dn k y ≠ 0)
    (ha' : DifferentiableAt ℝ (deriv a) (x 0)) (σ ν : Fin 4) :
    ricci (flrwMetric a k) σ ν x =
      if σ = 0 ∧ ν = 0 then -3 * (deriv (deriv a) (x 0) / a (x 0))
      else if σ = 0 ∨ ν = 0 then 0
      else if σ = ν then (deriv (deriv a) (x 0) / a (x 0) + 2 * (deriv a (x 0) / a (x 0)) ^ 2) *
          (a (x 0) * Sf k x) ^ 2 + 2 * k * Sf k x ^ 2
      else 0 := by
  have hx := hnb.self_of_nhds
  obtain ⟨ha, hpos, hD⟩ := hx
  have hD4 : 4 + k * spatialNormSq x ≠ 0 := by
    intro h; apply hD; unfold Dn; linarith
  have hD' : 1 + k * spatialNormSq x / 4 ≠ 0 := hD
  have hN : spatialNormSq x = x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
    simp [spatialNormSq, Fin.sum_univ_three]
  unfold ricci riemann
  simp only [pd_christoffel_flrw hnb ha', christoffel_flrw ha hpos hD]
  rw [hN] at hD4 hD'
  fin_cases σ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, Γf, dΓf, F0, Hf, Lf, dF0, dH, dL, Sf, Dn, hN] <;>
    field_simp <;> ring

theorem inv_diag' (d : Fin 4 → ℝ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one (n := Fin 4) (α := ℝ) using 2
  funext i; exact mul_inv_cancel₀ (hd i)

theorem scalar_flrw {a : ℝ → ℝ}
    (hnb : ∀ᶠ y in nhds x, DifferentiableAt ℝ a (y 0) ∧ a (y 0) ≠ 0 ∧ Dn k y ≠ 0)
    (ha' : DifferentiableAt ℝ (deriv a) (x 0)) :
    scalarCurvature (flrwMetric a k) x =
      6 * (deriv (deriv a) (x 0) / a (x 0) + (deriv a (x 0) / a (x 0)) ^ 2 + k / a (x 0) ^ 2) := by
  have hx := hnb.self_of_nhds
  obtain ⟨ha, hpos, hD⟩ := hx
  have hSf : Sf k x ≠ 0 := inv_ne_zero hD
  have hD4 : 4 + k * spatialNormSq x ≠ 0 := by
    intro h; apply hD; unfold Dn; linarith
  have hd : ∀ i, dF a k x i ≠ 0 := by
    intro i; unfold dF; split_ifs
    · norm_num
    · exact pow_ne_zero 2 (div_ne_zero hpos hD)
  have hinv : (flrwMetric a k x)⁻¹ = Matrix.diagonal (fun i => (dF a k x i)⁻¹) :=
    inv_diag' _ hd
  unfold scalarCurvature
  rw [hinv]
  simp only [ricci_flrw hnb ha']
  simp [Fin.sum_univ_four, dF, Matrix.diagonal_apply, Sf, Dn] at hSf ⊢
  field_simp
  ring

theorem einstein_flrw {a : ℝ → ℝ}
    (hnb : ∀ᶠ y in nhds x, DifferentiableAt ℝ a (y 0) ∧ a (y 0) ≠ 0 ∧ Dn k y ≠ 0)
    (ha' : DifferentiableAt ℝ (deriv a) (x 0)) (μ ν : Fin 4) :
    einsteinTensor (flrwMetric a k) μ ν x =
      if μ = ν then
        (if μ = 0 then 3 * ((deriv a (x 0) / a (x 0)) ^ 2 + k / a (x 0) ^ 2)
         else -(2 * (deriv (deriv a) (x 0) / a (x 0)) + (deriv a (x 0) / a (x 0)) ^ 2
           + k / a (x 0) ^ 2) * ((a (x 0) * Sf k x) * (a (x 0) * Sf k x)))
      else 0 := by
  have hx := hnb.self_of_nhds
  obtain ⟨ha, hpos, hD⟩ := hx
  have hSf : Sf k x ≠ 0 := inv_ne_zero hD
  unfold einsteinTensor
  rw [ricci_flrw hnb ha', scalar_flrw hnb ha', flrwEntry_eq]
  fin_cases μ <;> fin_cases ν <;> simp <;> field_simp <;> ring

end FLRWCurvature

/-- **CO1.** For `a > 0` smooth on an open interval `I`, Einstein's equations for the FLRW metric
with a perfect fluid hold on the chart iff Friedmann's first and second equations hold at every
`t ∈ I`. -/
theorem flrw_einstein_iff_friedmann {I : Set ℝ} (hI : IsOpen I) {a ρ p : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a I) (hpos : ∀ t ∈ I, 0 < a t) (k Λ Gn : ℝ) :
    IsEinsteinSolution Λ Gn (flrwMetric a k) (perfectFluid ρ p (flrwMetric a k))
        (flrwDomain I k) ↔
      ∀ t ∈ I, FirstFriedmann a ρ k Λ Gn t ∧ SecondFriedmann a ρ p Λ Gn t := by
  have hU : IsOpen (flrwDomain I k) := by
    have h1 : IsOpen {x : Fin 4 → ℝ | x 0 ∈ I} := hI.preimage (continuous_apply 0)
    have h2 : IsOpen {x : Fin 4 → ℝ | 0 < 1 + k * spatialNormSq x / 4} :=
      isOpen_lt continuous_const (by unfold spatialNormSq; fun_prop)
    exact h1.inter h2
  have hDn : ∀ x ∈ flrwDomain I k, Dn k x ≠ 0 := fun x hx => (show 0 < Dn k x from hx.2).ne'
  have hda : ∀ t ∈ I, DifferentiableAt ℝ a t := fun t ht =>
    (ha.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)
  have hda' : ∀ t ∈ I, DifferentiableAt ℝ (deriv a) t := fun t ht =>
    ((ha.deriv_of_isOpen hI (m := ∞) (by simp)).contDiffAt (hI.mem_nhds ht)).differentiableAt
      (by simp)
  have hnb : ∀ x ∈ flrwDomain I k, ∀ᶠ y in nhds x,
      DifferentiableAt ℝ a (y 0) ∧ a (y 0) ≠ 0 ∧ Dn k y ≠ 0 := by
    intro x hx
    filter_upwards [hU.mem_nhds hx] with y hy
    exact ⟨hda _ hy.1, (hpos _ hy.1).ne', hDn y hy⟩
  have hcm : IsCoordMetric (flrwMetric a k) (flrwDomain I k) := by
    refine isCoordMetric_diagonal (dF a k) hU ?_ ?_
    · intro i
      by_cases hi : i = 0
      · simp only [dF, hi, ite_true]; exact contDiffOn_const
      · simp only [dF, hi, ite_false]
        have hs : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => 1 + k * spatialNormSq y / 4) := by
          unfold spatialNormSq; fun_prop
        have ha0 : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => a (y 0)) (flrwDomain I k) :=
          ha.comp (by fun_prop : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => y 0)).contDiffOn (fun y hy => hy.1)
        exact (ha0.div hs.contDiffOn (fun y hy => hDn y hy)).pow 2
    · intro x hx i
      unfold dF; split_ifs
      · norm_num
      · exact pow_ne_zero 2 (div_ne_zero (hpos _ hx.1).ne' (hDn x hx))
  constructor
  · rintro ⟨-, h⟩ t ht
    set x : Fin 4 → ℝ := ![t, 0, 0, 0] with hxdef
    have hx0 : x 0 = t := rfl
    have hN : spatialNormSq x = 0 := by simp [spatialNormSq, hxdef, Fin.sum_univ_three]
    have hxU : x ∈ flrwDomain I k := ⟨by rw [hx0]; exact ht, by rw [hN]; norm_num⟩
    have hSf : Sf k x = 1 := by simp [Sf, Dn, hN]
    have hA : a t ≠ 0 := (hpos t ht).ne'
    have e0 := h x hxU 0 0
    have e1 := h x hxU 1 1
    rw [einstein_flrw (hnb x hxU) (hda' _ ht)] at e0 e1
    simp only [perfectFluid, flrwEntry_eq, hx0, hSf] at e0 e1
    simp at e0 e1
    have e1' : (-(2 * (deriv (deriv a) t / a t) + (deriv a t / a t) ^ 2 + k / a t ^ 2) + Λ
        - 8 * Real.pi * Gn * p t) * (a t * a t) = 0 := by
      linear_combination e1
    have e1'' := (mul_eq_zero.1 e1').resolve_right (mul_ne_zero hA hA)
    have hF1 : FirstFriedmann a ρ k Λ Gn t := by unfold FirstFriedmann; linarith
    refine ⟨hF1, ?_⟩
    unfold SecondFriedmann
    unfold FirstFriedmann at hF1
    linarith
  · intro hF
    refine ⟨hcm, fun x hx μ ν => ?_⟩
    obtain ⟨h1, h2⟩ := hF (x 0) hx.1
    unfold FirstFriedmann at h1
    unfold SecondFriedmann at h2
    have e1' : -(2 * (deriv (deriv a) (x 0) / a (x 0)) + (deriv a (x 0) / a (x 0)) ^ 2
        + k / a (x 0) ^ 2) + Λ = 8 * Real.pi * Gn * p (x 0) := by linarith
    rw [einstein_flrw (hnb x hx) (hda' _ hx.1)]
    simp only [perfectFluid, flrwEntry_eq]
    fin_cases μ <;> fin_cases ν <;> simp
    all_goals first
      | linarith
      | linear_combination ((a (x 0) * Sf k x) * (a (x 0) * Sf k x)) * e1'

/-- The continuity equation `ρ' + 3H(ρ + p) = 0` follows from Friedmann's two equations on an open
interval, for `G ≠ 0` and `ρ` differentiable. (For `G = 0` the equations do not constrain `ρ`.)
No condition `a' ≠ 0` is needed in this direction; it is needed for the converse, from the continuity
equation and the first equation to the second. -/
theorem friedmann_continuity {I : Set ℝ} (hI : IsOpen I) {a ρ p : ℝ → ℝ} (k Λ Gn : ℝ)
    (hG : Gn ≠ 0) (hpos : ∀ t ∈ I, 0 < a t) (ha : ∀ t ∈ I, DifferentiableAt ℝ a t)
    (ha' : ∀ t ∈ I, DifferentiableAt ℝ (deriv a) t) (hρ : ∀ t ∈ I, DifferentiableAt ℝ ρ t)
    (h1 : ∀ t ∈ I, FirstFriedmann a ρ k Λ Gn t) (h2 : ∀ t ∈ I, SecondFriedmann a ρ p Λ Gn t)
    {t : ℝ} (ht : t ∈ I) :
    deriv ρ t + 3 * (deriv a t / a t) * (ρ t + p t) = 0 := by
  set c : ℝ := 8 * Real.pi * Gn / 3 with hc
  have hc0 : c ≠ 0 := by
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    simp only [hc]; positivity
  have hA : a t ≠ 0 := (hpos t ht).ne'
  have hAt : HasDerivAt a (deriv a t) t := (ha t ht).hasDerivAt
  have hBt : HasDerivAt (deriv a) (deriv (deriv a) t) t := (ha' t ht).hasDerivAt
  have hu : HasDerivAt (fun s => deriv a s / a s)
      ((deriv (deriv a) t * a t - deriv a t * deriv a t) / a t ^ 2) t := hBt.div hAt hA
  have h3 : HasDerivAt (fun s => (deriv a s / a s) ^ 2)
      (2 * (deriv a t / a t) * ((deriv (deriv a) t * a t - deriv a t * deriv a t) / a t ^ 2)) t := by
    have := (hasDerivAt_pow 2 (deriv a t / a t)).comp t hu
    exact this.congr_deriv (by simp)
  have hq : HasDerivAt (fun s => k / a s ^ 2) (-(2 * k * deriv a t) / a t ^ 3) t := by
    have := (hasDerivAt_const t k).div (hAt.pow 2) (pow_ne_zero 2 hA)
    convert this using 1
    simp only [Pi.pow_apply]
    field_simp
    try ring
  have hr := h3.add hq
  have hcr : HasDerivAt (fun s => c * ρ s) (c * deriv ρ t) t := ((hρ t ht).hasDerivAt).const_mul c
  have hev : (fun s => c * ρ s) =ᶠ[nhds t] fun s => (deriv a s / a s) ^ 2 + k / a s ^ 2 - Λ / 3 := by
    filter_upwards [hI.mem_nhds ht] with s hs
    have := h1 s hs
    simp only [FirstFriedmann, hc] at this ⊢
    linarith
  have hd := (hcr.congr_of_eventuallyEq hev.symm)
  have hd2 := hr.sub_const (Λ / 3)
  have key := hd.unique hd2
  have e1 := h1 t ht
  have e2 := h2 t ht
  simp only [FirstFriedmann] at e1
  simp only [SecondFriedmann] at e2
  have key2 : c * deriv ρ t = 2 * (deriv a t / a t) * (deriv (deriv a) t / a t - (deriv a t / a t) ^ 2)
      - 2 * k * (deriv a t / a t) / a t ^ 2 := by
    rw [key]; field_simp
    try ring
  have e1' : (deriv a t / a t) ^ 2 = c * ρ t - k / a t ^ 2 + Λ / 3 := by rw [e1]
  have e2' : deriv (deriv a) t / a t = -(c / 2) * (ρ t + 3 * p t) + Λ / 3 := by
    rw [e2, hc]; ring
  apply mul_left_cancel₀ hc0
  rw [e2'] at key2
  linear_combination key2 - 2 * (deriv a t / a t) * e1'

/-- Trust check: de Sitter. With `k = 0`, `Λ = 0`, `a = e^{Ht}` and `ρ = -p = ρΛ`, Friedmann's
equations hold at every time iff `H² = 8πGρΛ/3`. -/
theorem deSitter_friedmann_iff (H ρΛ Gn : ℝ) :
    (∀ t, FirstFriedmann (fun t => Real.exp (H * t)) (fun _ => ρΛ) 0 0 Gn t ∧
      SecondFriedmann (fun t => Real.exp (H * t)) (fun _ => ρΛ) (fun _ => -ρΛ) 0 Gn t) ↔
    H ^ 2 = 8 * Real.pi * Gn * ρΛ / 3 := by
  have hd : ∀ t, HasDerivAt (fun t => Real.exp (H * t)) (H * Real.exp (H * t)) t := fun t => by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul H).exp
  have hd1 : deriv (fun t => Real.exp (H * t)) = fun t => H * Real.exp (H * t) :=
    funext fun t => (hd t).deriv
  have hd2 : ∀ t, deriv (fun t => H * Real.exp (H * t)) t = H * (H * Real.exp (H * t)) := fun t => by
    simpa [mul_comm] using (((hasDerivAt_id t).const_mul H).exp.const_mul H).deriv
  constructor
  · intro h
    obtain ⟨h1, -⟩ := h 0
    simp only [FirstFriedmann, hd1] at h1
    field_simp at h1
    simp at h1
    linarith
  · intro h t
    have hp := Real.exp_pos (H * t)
    simp only [FirstFriedmann, SecondFriedmann, hd1, hd2]
    constructor <;> (field_simp; nlinarith [h])

/-- Trust check: Einstein's static universe. For `a` constant and positive, `k = 1`, `p = 0`,
Friedmann's equations hold iff `Λ = 1/a² = 4πGρ`. -/
theorem einsteinStatic_friedmann_iff {a : ℝ} (ha : 0 < a) (ρ Λ Gn : ℝ) :
    (∀ t, FirstFriedmann (fun _ => a) (fun _ => ρ) 1 Λ Gn t ∧
      SecondFriedmann (fun _ => a) (fun _ => ρ) (fun _ => 0) Λ Gn t) ↔
    Λ = 1 / a ^ 2 ∧ Λ = 4 * Real.pi * Gn * ρ := by
  simp only [FirstFriedmann, SecondFriedmann, deriv_const', zero_div]
  have ha2 : a ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h 0
    refine ⟨?_, ?_⟩ <;> field_simp at h1 h2 ⊢ <;> nlinarith [h1, h2]
  · rintro ⟨h1, h2⟩ t
    subst h2
    constructor <;> (field_simp at h1 ⊢; nlinarith [h1])

/-- Wrong-model check: with `k = -1`, constant `a > 0`, `p = 0`, `ρ > 0` and `G > 0`, Friedmann's
equations have no solution. -/
theorem not_einsteinStatic_friedmann_of_negCurvature {a : ℝ} (ha : 0 < a) {ρ Gn : ℝ}
    (hρ : 0 < ρ) (hG : 0 < Gn) (Λ : ℝ) :
    ¬ ∀ t, FirstFriedmann (fun _ => a) (fun _ => ρ) (-1) Λ Gn t ∧
      SecondFriedmann (fun _ => a) (fun _ => ρ) (fun _ => 0) Λ Gn t := by
  intro h
  obtain ⟨h1, h2⟩ := h 0
  simp only [FirstFriedmann, SecondFriedmann, deriv_const', zero_div] at h1 h2
  have hpi := Real.pi_pos
  have ha2 : 0 < a ^ 2 := by positivity
  have : 0 < 8 * Real.pi * Gn / 3 * ρ := by positivity
  have h3 : 0 < 1 / a ^ 2 := by positivity
  have h4 : (-1 : ℝ) / a ^ 2 = -(1 / a ^ 2) := by ring
  nlinarith [h1, h2, this, h3, h4]

/-- Trust check, Einstein level: de Sitter space. The FLRW metric with `a = e^{Ht}`, `k = 0`,
`Λ = 0` and a fluid with `ρ = -p = ρΛ` solves Einstein's equations on the whole chart iff
`H² = 8πGρΛ/3`. -/
theorem deSitter_einstein_iff (H ρΛ Gn : ℝ) :
    IsEinsteinSolution 0 Gn (flrwMetric (fun t => Real.exp (H * t)) 0)
        (perfectFluid (fun _ => ρΛ) (fun _ => -ρΛ) (flrwMetric (fun t => Real.exp (H * t)) 0))
        (flrwDomain Set.univ 0) ↔ H ^ 2 = 8 * Real.pi * Gn * ρΛ / 3 := by
  rw [flrw_einstein_iff_friedmann isOpen_univ
    (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (H * t))).contDiffOn
    (fun t _ => Real.exp_pos _) 0 0 Gn, ← deSitter_friedmann_iff]
  simp only [Set.mem_univ, forall_true_left]

/-- Non-vacuity: with `H = 1`, `ρΛ = 1` and `G = 3/(8π)` de Sitter space solves Einstein's
equations on the whole chart. -/
theorem deSitter_example :
    IsEinsteinSolution 0 (3 / (8 * Real.pi)) (flrwMetric (fun t => Real.exp (1 * t)) 0)
        (perfectFluid (fun _ => (1 : ℝ)) (fun _ => -1)
          (flrwMetric (fun t => Real.exp (1 * t)) 0))
        (flrwDomain Set.univ 0) := by
  rw [deSitter_einstein_iff]
  have := Real.pi_pos
  field_simp

/-- Trust check, Einstein level: Einstein's static universe. A constant `a > 0` with `k = 1`,
dust (`p = 0`) solves Einstein's equations on the whole chart iff `Λ = 1/a² = 4πGρ`. -/
theorem einsteinStatic_einstein_iff {a : ℝ} (ha : 0 < a) (ρ Λ Gn : ℝ) :
    IsEinsteinSolution Λ Gn (flrwMetric (fun _ => a) 1)
        (perfectFluid (fun _ => ρ) (fun _ => 0) (flrwMetric (fun _ => a) 1))
        (flrwDomain Set.univ 1) ↔ Λ = 1 / a ^ 2 ∧ Λ = 4 * Real.pi * Gn * ρ := by
  rw [flrw_einstein_iff_friedmann isOpen_univ contDiffOn_const (fun _ _ => ha) 1 Λ Gn,
    ← einsteinStatic_friedmann_iff ha]
  simp only [Set.mem_univ, forall_true_left]

/-- Wrong-model check, Einstein level: with `k = -1` there is no static dust solution. -/
theorem not_einsteinStatic_einstein_of_negCurvature {a : ℝ} (ha : 0 < a) {ρ Gn : ℝ}
    (hρ : 0 < ρ) (hG : 0 < Gn) (Λ : ℝ) :
    ¬ IsEinsteinSolution Λ Gn (flrwMetric (fun _ => a) (-1))
        (perfectFluid (fun _ => ρ) (fun _ => 0) (flrwMetric (fun _ => a) (-1)))
        (flrwDomain Set.univ (-1)) := by
  intro h
  rw [flrw_einstein_iff_friedmann isOpen_univ contDiffOn_const (fun _ _ => ha) (-1) Λ Gn] at h
  exact not_einsteinStatic_friedmann_of_negCurvature ha hρ hG Λ fun t => h t trivial

end Cosmology

end Lightlike
