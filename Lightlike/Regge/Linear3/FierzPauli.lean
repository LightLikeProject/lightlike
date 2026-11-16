import Lightlike.Regge.Linear3.LinearizedLimit
import Lightlike.Regge.Conv3.DivergencePeriodic

/-!
# The Saint-Venant form and the Fierz–Pauli form agree after integration over the torus

For a smooth symmetric field `h` of matrices on `ℝ³` invariant under integer translations, the limit of the coefficient
of the linearized Regge action (`Qn_converges`) is `∫_{[0,1]³} -¼ Σ h_ij ε_ikl ε_jmn ∂_k ∂_m h_ln`, the Saint-Venant
form `-¼ ⟨curl^t curl h, h⟩`. This file shows that it equals `∫_{[0,1]³} fpDens (∂h)`, where

`fpDens (∂h) = -¼ Σ (∂_l h_mn)² + ½ Σ_n (Σ_m ∂_m h_mn)² - ½ Σ_n (Σ_m ∂_m h_mn)(∂_n Σ_i h_ii) + ¼ Σ_k (∂_k Σ_i h_ii)²`

is one half of the massless Fierz–Pauli Lagrangian for a field that does not depend on time, with the term
`∂_μ h_νλ ∂^ν h^μλ` written as `(∂_μ h^μν)²` (the two differ by a divergence, which is part of the identity below).
The two integrands differ by the divergence `∂_m T_m` of an explicit periodic field `T` (`fp_identity`, `div_Tfield`),
and the integral of a periodic divergence over the unit cube is zero (`integral_div_periodic`).

## Main results

* `fpDens`: the Fierz–Pauli density of the array `dh k i j = ∂_k h_ij`.
* `fp_identity`: the pointwise polynomial identity `-¼ svPair - fpDens = tdiv` (symmetric `h`, `∂h`, `∂∂h`).
* `Tfield`, `div_Tfield`, `periodic_Tfield`: the field, its divergence, its periodicity.
* `saintVenant_eq_fierzPauli`: the equality of the two integrals.

## Conventions

Euclidean indices, all lower, `δ_ij` is the metric. `dh k i j = ∂_k h_ij`, `dd k l i j = ∂_k ∂_l h_ij`
(`dd2`), and `svPair H dd = Σ H_ij ε_ikl ε_jmn dd k m l n`, with `ε` as `eps3`.

## Limits

* `C³` symmetric `ℤ³`-periodic fields on the torus `ℝ³/ℤ³`, the unit cube, nothing else.
* Spatial (three-dimensional, time-independent) fields; no gauge condition, no mass term.
* That `fpDens` is the second variation of `∫ (R/2) √det g` at the flat metric is not proved here, and the term-by-term
  agreement with the Lagrangian of Hinterbichler, Rev. Mod. Phys. 84 (2012), eq. (2.1) is a statement of this
  docstring, not checked by the source tool (which confirms that the equation is the Fierz–Pauli action).
-/

open Real Finset MeasureTheory
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3

/-- The Fierz–Pauli density of a first-derivative array `dh k i j = ∂_k h_ij`:
`-¼ Σ (∂_l h_mn)² + ½ Σ_n (Σ_m ∂_m h_mn)² - ½ Σ_n (Σ_m ∂_m h_mn)(Σ_i ∂_n h_ii) + ¼ Σ_k (Σ_i ∂_k h_ii)²`. -/
noncomputable def fpDens (dh : Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  -(1 / 4) * ∑ l, ∑ m, ∑ n, dh l m n ^ 2 + (1 / 2) * ∑ n, (∑ m, dh m m n) ^ 2
    - (1 / 2) * ∑ n, (∑ m, dh m m n) * (∑ i, dh n i i) + (1 / 4) * ∑ k, (∑ i, dh k i i) ^ 2

/-- The divergence, as a polynomial in `H = h`, `dh = ∂h`, `dd = ∂∂h`, of the periodic field `Tfield`. -/
noncomputable def tdiv (H : Fin 3 → Fin 3 → ℝ) (dh : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ m, ((∑ i, ∑ j, ∑ k, ∑ l, ∑ n, (-(1 / 4) * (eps3 i k l * eps3 j m n)) *
      (dh m i j * dh k l n + H i j * dd k m l n))
    + ∑ b, ∑ c, (1 / 4) * (dh m b c * dh b m c + H b c * dd b m m c)
    - ∑ b, ∑ c, (1 / 4) * (dh m m b * dh c c b + H m b * dd c m c b))

-- needs about 0.12 million heartbeats (measured with `#count_heartbeats`); the cap is about twice that
set_option maxHeartbeats 250000 in
/-- **The pointwise identity**: `-¼ svPair - fpDens` is the divergence `tdiv`. -/
theorem fp_identity (H : Fin 3 → Fin 3 → ℝ) (dh : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hH : ∀ i j, H i j = H j i) (hd : ∀ k i j, dh k i j = dh k j i)
    (hd1 : ∀ k l i j, dd k l i j = dd l k i j) (hd2 : ∀ k l i j, dd k l i j = dd k l j i) :
    -(1 / 4) * svPair H dd - fpDens dh = tdiv H dh dd := by
  simp only [svPair, fpDens, tdiv, eps3, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  simp only [hH 1 0, hH 2 0, hH 2 1, hd 0 1 0, hd 0 2 0, hd 0 2 1, hd 1 1 0, hd 1 2 0, hd 1 2 1,
    hd 2 1 0, hd 2 2 0, hd 2 2 1, hd1 1 0, hd1 2 0, hd1 2 1, hd2 _ _ 1 0, hd2 _ _ 2 0, hd2 _ _ 2 1]
  ring

section calculus

variable {F G : (Fin 3 → ℝ) → ℝ}

theorem pd1_const_mul (c : ℝ) (hF : Differentiable ℝ F) (v : Fin 3 → ℝ) (k : Fin 3) :
    pd1 (fun y => c * F y) v k = c * pd1 F v k := by
  unfold pd1
  rw [fderiv_const_mul (hF v) c]
  simp

theorem pd1_mul (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (v : Fin 3 → ℝ) (k : Fin 3) :
    pd1 (fun y => F y * G y) v k = pd1 F v k * G v + F v * pd1 G v k := by
  unfold pd1
  rw [show (fun y => F y * G y) = F * G from rfl, fderiv_mul (hF v) (hG v)]
  simp; ring

theorem pd1_sum {ι : Type*} (s : Finset ι) (A : ι → (Fin 3 → ℝ) → ℝ) (hA : ∀ i, Differentiable ℝ (A i))
    (v : Fin 3 → ℝ) (k : Fin 3) :
    pd1 (fun y => ∑ i ∈ s, A i y) v k = ∑ i ∈ s, pd1 (A i) v k := by
  unfold pd1
  rw [show (fun y => ∑ i ∈ s, A i y) = ∑ i ∈ s, A i from by ext; simp, fderiv_sum (fun i _ => (hA i) v)]
  simp

/-- `∂_m` of the pairing of the `∂_k F` with another function. -/
theorem pd1_pd1 (hF : ContDiff ℝ 2 F) (v : Fin 3 → ℝ) (k m : Fin 3) :
    pd1 (fun y => pd1 F y k) v m = pd2 F v k m := by
  have hd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  simp only [pd1, pd2]
  rw [fderiv_clm_apply (hd v) (differentiableAt_const _)]
  simp

/-- `y ↦ ∂_k F y` is `C^n` when `F` is `C^(n+1)`. -/
theorem contDiff_pd1 {n : ℕ} (hF : ContDiff ℝ (n + 1) F) (k : Fin 3) :
    ContDiff ℝ n (fun y => pd1 F y k) := by
  have := (hF.fderiv_right (m := n) le_rfl).clm_apply (contDiff_const (c := (Pi.single k (1 : ℝ) : Fin 3 → ℝ)))
  exact this

/-- `∂_k F` is periodic when `F` is. -/
theorem pd1_periodic (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), F (p + fun i => (e i : ℝ)) = F p)
    (v : Fin 3 → ℝ) (e : Fin 3 → ℤ) (k : Fin 3) :
    pd1 F (v + fun i => (e i : ℝ)) k = pd1 F v k := by
  have : F = fun y => F (y + fun i => (e i : ℝ)) := by funext y; exact (hper y e).symm
  have h := congrArg (fun f => fderiv ℝ f v (Pi.single k 1)) this
  simp only [pd1]
  convert h.symm using 1
  rw [fderiv_comp_add_right]

theorem pd1_add (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (v : Fin 3 → ℝ) (k : Fin 3) :
    pd1 (fun y => F y + G y) v k = pd1 F v k + pd1 G v k := by
  unfold pd1
  rw [show (fun y => F y + G y) = F + G from rfl, fderiv_add (hF v) (hG v)]
  simp

theorem pd1_sub (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (v : Fin 3 → ℝ) (k : Fin 3) :
    pd1 (fun y => F y - G y) v k = pd1 F v k - pd1 G v k := by
  unfold pd1
  rw [show (fun y => F y - G y) = F - G from rfl, fderiv_sub (hF v) (hG v)]
  simp

/-- The product rule for a finite sum of constant multiples of products. -/
theorem pd1_sum_prod {ι : Type*} [Fintype ι] (c : ι → ℝ) (P Q : ι → (Fin 3 → ℝ) → ℝ)
    (hP : ∀ i, Differentiable ℝ (P i)) (hQ : ∀ i, Differentiable ℝ (Q i)) (v : Fin 3 → ℝ) (k : Fin 3) :
    pd1 (fun y => ∑ i, c i * (P i y * Q i y)) v k
      = ∑ i, c i * (pd1 (P i) v k * Q i v + P i v * pd1 (Q i) v k) := by
  rw [pd1_sum Finset.univ (fun i y => c i * (P i y * Q i y))
    (fun i => (((hP i).mul (hQ i)).const_mul (c i)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd1_const_mul (F := fun y => P i y * Q i y) (c i) ((hP i).mul (hQ i)) v k, pd1_mul (hP i) (hQ i)]

end calculus

/-- The first part of `Tfield`: the double-epsilon terms. -/
noncomputable def T1 (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  ∑ x : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3,
      (-(1 / 4) * (eps3 x.1 x.2.2.1 x.2.2.2.1 * eps3 x.2.1 m x.2.2.2.2)) *
        (hf y x.1 x.2.1 * pd1 (fun z => hf z x.2.2.2.1 x.2.2.2.2) y x.2.2.1)

/-- The second part of `Tfield`: `¼ h_bc ∂_b h_mc`. -/
noncomputable def T2 (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  ∑ x : Fin 3 × Fin 3, (1 / 4 : ℝ) * (hf y x.1 x.2 * pd1 (fun z => hf z m x.2) y x.1)

/-- The third part of `Tfield`: `¼ h_mb ∂_c h_cb`. -/
noncomputable def T3 (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  ∑ x : Fin 3 × Fin 3, (1 / 4 : ℝ) * (hf y m x.1 * pd1 (fun z => hf z x.2 x.1) y x.2)

/-- The periodic field whose divergence is `-¼ svPair - fpDens`. -/
noncomputable def Tfield (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  T1 hf m y + T2 hf m y - T3 hf m y

theorem integrable_unitCube {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict unitCube) := by
  have hbox : unitCube = Set.Icc (0 : Fin 3 → ℝ) 1 := by
    unfold unitCube; rw [Set.pi_univ_Icc]; rfl
  rw [hbox]
  exact hf.integrableOn_Icc

section field

variable {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}

theorem div_Tfield (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (y : Fin 3 → ℝ) :
    ∑ m, pd1 (Tfield hf m) y m = tdiv (Hm hf y) (dh1 hf y) (dd2 hf y) := by
  have hA : ∀ i j, Differentiable ℝ (fun z => hf z i j) := fun i j => (hsm i j).differentiable (by norm_num)
  have hB : ∀ k l n, Differentiable ℝ (fun z => pd1 (fun w => hf w l n) z k) := fun k l n =>
    (contDiff_pd1 (n := 2) (by exact_mod_cast hsm l n) k).differentiable (by norm_num)
  have hdd : ∀ k m l n, pd1 (fun z => pd1 (fun w => hf w l n) z k) y m = dd2 hf y k m l n := fun k m l n =>
    pd1_pd1 ((hsm l n).of_le (by norm_num)) y k m
  refine Finset.sum_congr rfl fun m _ => ?_
  have e1 := pd1_sum_prod (ι := Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3)
    (fun x => -(1 / 4) * (eps3 x.1 x.2.2.1 x.2.2.2.1 * eps3 x.2.1 m x.2.2.2.2))
    (fun x z => hf z x.1 x.2.1) (fun x z => pd1 (fun w => hf w x.2.2.2.1 x.2.2.2.2) z x.2.2.1)
    (fun x => hA _ _) (fun x => hB _ _ _) y m
  have e2 := pd1_sum_prod (ι := Fin 3 × Fin 3) (fun _ => 1 / 4)
    (fun x z => hf z x.1 x.2) (fun x z => pd1 (fun w => hf w m x.2) z x.1)
    (fun x => hA _ _) (fun x => hB _ _ _) y m
  have e3 := pd1_sum_prod (ι := Fin 3 × Fin 3) (fun _ => 1 / 4)
    (fun x z => hf z m x.1) (fun x z => pd1 (fun w => hf w x.2 x.1) z x.2)
    (fun x => hA _ _) (fun x => hB _ _ _) y m
  have hS1 : Differentiable ℝ (T1 hf m) := by unfold T1; fun_prop
  have hS2 : Differentiable ℝ (T2 hf m) := by unfold T2; fun_prop
  have hS3 : Differentiable ℝ (T3 hf m) := by unfold T3; fun_prop
  have hT : Tfield hf m = fun z => T1 hf m z + T2 hf m z - T3 hf m z := rfl
  have hS12 : Differentiable ℝ (fun z => T1 hf m z + T2 hf m z) := hS1.add hS2
  have e4 := pd1_sub hS12 hS3 y m
  have e5 := pd1_add hS1 hS2 y m
  rw [hT]
  refine e4.trans ?_
  rw [e5]
  unfold T1 T2 T3
  rw [e1, e2, e3]
  simp only [hdd, Fintype.sum_prod_type]
  rfl

theorem contDiff_Tfield (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (m : Fin 3) :
    ContDiff ℝ 1 (Tfield hf m) := by
  have hA : ∀ i j, ContDiff ℝ 1 (fun z => hf z i j) := fun i j => (hsm i j).of_le (by norm_num)
  have hB : ∀ k l n, ContDiff ℝ 1 (fun z => pd1 (fun w => hf w l n) z k) := fun k l n =>
    contDiff_pd1 (n := 1) ((hsm l n).of_le (by norm_num)) k
  unfold Tfield T1 T2 T3
  fun_prop

theorem periodic_Tfield (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p)
    (m : Fin 3) (p : Fin 3 → ℝ) (e : Fin 3 → ℤ) :
    Tfield hf m (p + fun i => (e i : ℝ)) = Tfield hf m p := by
  have hA : ∀ i j, hf (p + fun i => (e i : ℝ)) i j = hf p i j := fun i j => by rw [hper]
  have hB : ∀ l n k, pd1 (fun z => hf z l n) (p + fun i => (e i : ℝ)) k = pd1 (fun z => hf z l n) p k :=
    fun l n k => pd1_periodic (fun q e' => by rw [hper]) p e k
  simp only [Tfield, T1, T2, T3, hA, hB]

open Classical in
/-- **The Saint-Venant form and the Fierz–Pauli form have the same integral over the torus.** -/
theorem saintVenant_eq_fierzPauli (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j))
    (hsymm : ∀ y i j, hf y i j = hf y j i)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p) :
    ∫ y in unitCube, -(1 / 4) * svPair (Hm hf y) (dd2 hf y) = ∫ y in unitCube, fpDens (dh1 hf y) := by
  have hdiv := integral_div_periodic (Tfield hf) (contDiff_Tfield hsm) (periodic_Tfield hper)
  have hpt : ∀ y, -(1 / 4) * svPair (Hm hf y) (dd2 hf y) - fpDens (dh1 hf y)
      = ∑ m, fderiv ℝ (Tfield hf m) y (Pi.single m 1) := fun y => by
    rw [fp_identity (Hm hf y) (dh1 hf y) (dd2 hf y) (fun i j => by simp [Hm, hsymm y i j])
      (fun k i j => by simp [dh1, hsymm _ i j])
      (fun k l i j => pd2_symm (hsm i j) y k l) (fun k l i j => by simp [dd2, hsymm _ i j])]
    exact (div_Tfield hsm y).symm
  have c1 : ∀ i j, Continuous fun y => hf y i j := fun i j => (hsm i j).continuous
  have c2 : ∀ k i j, Continuous fun y => dh1 hf y k i j := fun k i j =>
    ((contDiff_pd1 (n := 0) ((hsm i j).of_le (by norm_num)) k)).continuous
  have c3 : ∀ k l i j, Continuous fun y => dd2 hf y k l i j := fun k l i j => pd2_continuous (hsm i j) k l
  have i1 : Integrable (fun y => -(1 / 4) * svPair (Hm hf y) (dd2 hf y)) (volume.restrict unitCube) := by
    refine integrable_unitCube ?_
    simp only [svPair, Hm]
    fun_prop
  have i2 : Integrable (fun y => fpDens (dh1 hf y)) (volume.restrict unitCube) := by
    refine integrable_unitCube ?_
    simp only [fpDens]
    fun_prop
  have := integral_sub i1 i2
  simp only [hpt] at this
  linarith [hdiv]

end field
