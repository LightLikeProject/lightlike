import Lightlike.Regge.Conv3.CurvaturePoly
import Lightlike.Regge.Linear3.FierzPauli
import Lightlike.Regge.Linear3.LinearizedExpansion
import Lightlike.Regge.Conv3.CurvatureCoeffs

/-!
# The periodic divergences that make the integrals of `F₁` and `F₂` explicit

For a smooth symmetric periodic matrix field `h` on `ℝ³`, the integral over the unit cube of the first coefficient `F₁`
of the curvature density of `1 + η h` is zero (`integral_F1_zero`): `F₁` is the divergence of the periodic field
`S_i = Σ_j ∂_j h_ij - ∂_i tr h` (`div_S1field`). The integral of the second coefficient `F₂` is the integral of the
Fierz–Pauli density (`integral_F2_eq`): `F₂ - fpDens` is the divergence `divTp` of the explicit periodic field `T'`
(`Tprime`, `div_Tprime`), and the integral of a periodic divergence over the unit cube is zero (`integral_div_periodic`).

## Main results

* `S1field`, `div_S1field`, `integral_F1_zero`.
* `Tprime`, `pd1_add6`, `div_Tprime`, `integral_F2_eq`.
* `jetOf`, `jet_symm`: the jet of a field at a point and its symmetries.

**Limits.** Dimension 3; `C³` symmetric periodic fields on the unit cube; the sums of products are those of
`CurvaturePoly`; nothing about the curvature itself.
-/

open Real Finset MeasureTheory
open scoped ContDiff
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3

section I1

variable {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}

/-- The field whose divergence is `Σ_ij ∂_i∂_j h_ij - Σ_ki ∂_i∂_i h_kk`: `S_i = Σ_j ∂_j h_ij - ∂_i tr h`. -/
noncomputable def S1field (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  (∑ j, pd1 (fun z => hf z i j) y j) - ∑ k, pd1 (fun z => hf z k k) y i

/-- The field `S1field` is `C¹`. -/
theorem contDiff_S1field (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (i : Fin 3) :
    ContDiff ℝ 1 (S1field hf i) := by
  have hB : ∀ k l n, ContDiff ℝ 1 (fun z => pd1 (fun w => hf w l n) z k) := fun k l n =>
    contDiff_pd1 (n := 1) ((hsm l n).of_le (by norm_num)) k
  unfold S1field
  fun_prop

/-- The field `S1field` is periodic. -/
theorem periodic_S1field (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p)
    (i : Fin 3) (p : Fin 3 → ℝ) (e : Fin 3 → ℤ) :
    S1field hf i (p + fun i => (e i : ℝ)) = S1field hf i p := by
  have hB : ∀ l n k, pd1 (fun z => hf z l n) (p + fun i => (e i : ℝ)) k = pd1 (fun z => hf z l n) p k :=
    fun l n k => pd1_periodic (fun q e' => by rw [hper]) p e k
  simp only [S1field, hB]

/-- The divergence of `S1field` in terms of the second derivatives. -/
theorem div_S1field (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (y : Fin 3 → ℝ) :
    ∑ i, pd1 (S1field hf i) y i =
      (∑ i, ∑ j, dd2 hf y j i i j) - ∑ i, ∑ k, dd2 hf y i i k k := by
  have hB : ∀ k l n, Differentiable ℝ (fun z => pd1 (fun w => hf w l n) z k) := fun k l n =>
    (contDiff_pd1 (n := 1) ((hsm l n).of_le (by norm_num)) k).differentiable (by norm_num)
  have hdd : ∀ k m l n, pd1 (fun z => pd1 (fun w => hf w l n) z k) y m = dd2 hf y k m l n := fun k m l n =>
    pd1_pd1 ((hsm l n).of_le (by norm_num)) y k m
  have key : ∀ i, pd1 (S1field hf i) y i = (∑ j, dd2 hf y j i i j) - ∑ k, dd2 hf y i i k k := fun i => by
    have hS1 : Differentiable ℝ (fun z => ∑ j, pd1 (fun w => hf w i j) z j) := by fun_prop
    have hS2 : Differentiable ℝ (fun z => ∑ k, pd1 (fun w => hf w k k) z i) := by fun_prop
    have e1 := pd1_sub hS1 hS2 y i
    have e2 := pd1_sum Finset.univ (fun j z => pd1 (fun w => hf w i j) z j) (fun j => hB _ _ _) y i
    have e3 := pd1_sum Finset.univ (fun k z => pd1 (fun w => hf w k k) z i) (fun k => hB _ _ _) y i
    show pd1 (fun z => (∑ j, pd1 (fun w => hf w i j) z j) - ∑ k, pd1 (fun w => hf w k k) z i) y i = _
    rw [e1, e2, e3]
    simp only [hdd]
  rw [Finset.sum_congr rfl fun i _ => key i, sum_sub_distrib]

end I1

section I2

variable {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}

/-- The six parts of the field `T'` with `div T' = divTp`. -/
noncomputable def U1 (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  ∑ x : Fin 3 × Fin 3, (1 / 2 : ℝ) * (hf y x.1 x.1 * pd1 (fun z => hf z x.2 m) y x.2)

/-- `-½ tr h ∂_m tr h`. -/
noncomputable def U2 (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  ∑ x : Fin 3 × Fin 3, (-(1 / 2) : ℝ) * (hf y x.1 x.1 * pd1 (fun z => hf z x.2 x.2) y m)

/-- `-½ h_ab ∂_a h_bm`. -/
noncomputable def U3 (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  ∑ x : Fin 3 × Fin 3, (-(1 / 2) : ℝ) * (hf y x.1 x.2 * pd1 (fun z => hf z x.2 m) y x.1)

/-- `h_am ∂_a tr h`. -/
noncomputable def U4 (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  ∑ x : Fin 3 × Fin 3, (1 : ℝ) * (hf y x.1 m * pd1 (fun z => hf z x.2 x.2) y x.1)

/-- `h_ab ∂_m h_ab`. -/
noncomputable def U5 (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  ∑ x : Fin 3 × Fin 3, (1 : ℝ) * (hf y x.1 x.2 * pd1 (fun z => hf z x.1 x.2) y m)

/-- `-(3/2) h_am ∂_c h_ac`. -/
noncomputable def U6 (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  ∑ x : Fin 3 × Fin 3, (-(3 / 2) : ℝ) * (hf y x.1 m * pd1 (fun z => hf z x.1 x.2) y x.2)

/-- The field `T'`. -/
noncomputable def Tprime (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  U1 hf m y + U2 hf m y + U3 hf m y + U4 hf m y + U5 hf m y + U6 hf m y

/-- The partial derivative of a sum of six differentiable functions. -/
theorem pd1_add6 {F1 F2 F3 F4 F5 F6 : (Fin 3 → ℝ) → ℝ} (h1 : Differentiable ℝ F1) (h2 : Differentiable ℝ F2)
    (h3 : Differentiable ℝ F3) (h4 : Differentiable ℝ F4) (h5 : Differentiable ℝ F5) (h6 : Differentiable ℝ F6)
    (v : Fin 3 → ℝ) (k : Fin 3) :
    pd1 (fun y => F1 y + F2 y + F3 y + F4 y + F5 y + F6 y) v k =
      pd1 F1 v k + pd1 F2 v k + pd1 F3 v k + pd1 F4 v k + pd1 F5 v k + pd1 F6 v k := by
  have := ((((((h1 v).hasFDerivAt.add (h2 v).hasFDerivAt).add (h3 v).hasFDerivAt).add (h4 v).hasFDerivAt).add
    (h5 v).hasFDerivAt).add (h6 v).hasFDerivAt).fderiv
  unfold pd1
  rw [show (fun y => F1 y + F2 y + F3 y + F4 y + F5 y + F6 y) = F1 + F2 + F3 + F4 + F5 + F6 from rfl, this]
  simp

/-- The divergence of `Tprime` is `divTp` of the jet. -/
theorem div_Tprime (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (y : Fin 3 → ℝ) :
    ∑ m, pd1 (Tprime hf m) y m =
      divTp (Hm hf y) (dh1 hf y) (fun a b i j => dd2 hf y b a i j) := by
  have hA : ∀ i j, Differentiable ℝ (fun z => hf z i j) := fun i j => (hsm i j).differentiable (by norm_num)
  have hB : ∀ k l n, Differentiable ℝ (fun z => pd1 (fun w => hf w l n) z k) := fun k l n =>
    (contDiff_pd1 (n := 1) ((hsm l n).of_le (by norm_num)) k).differentiable (by norm_num)
  have hdd : ∀ k m l n, pd1 (fun z => pd1 (fun w => hf w l n) z k) y m = dd2 hf y k m l n := fun k m l n =>
    pd1_pd1 ((hsm l n).of_le (by norm_num)) y k m
  have key : ∀ m, pd1 (Tprime hf m) y m = ∑ x : Fin 3 × Fin 3, (1 / 2 : ℝ) *
        (pd1 (fun z => hf z x.1 x.1) y m * pd1 (fun w => hf w x.2 m) y x.2 +
          hf y x.1 x.1 * dd2 hf y x.2 m x.2 m)
      + ∑ x : Fin 3 × Fin 3, (-(1 / 2) : ℝ) * (pd1 (fun z => hf z x.1 x.1) y m * pd1 (fun w => hf w x.2 x.2) y m +
          hf y x.1 x.1 * dd2 hf y m m x.2 x.2)
      + ∑ x : Fin 3 × Fin 3, (-(1 / 2) : ℝ) * (pd1 (fun z => hf z x.1 x.2) y m * pd1 (fun w => hf w x.2 m) y x.1 +
          hf y x.1 x.2 * dd2 hf y x.1 m x.2 m)
      + ∑ x : Fin 3 × Fin 3, (1 : ℝ) * (pd1 (fun z => hf z x.1 m) y m * pd1 (fun w => hf w x.2 x.2) y x.1 +
          hf y x.1 m * dd2 hf y x.1 m x.2 x.2)
      + ∑ x : Fin 3 × Fin 3, (1 : ℝ) * (pd1 (fun z => hf z x.1 x.2) y m * pd1 (fun w => hf w x.1 x.2) y m +
          hf y x.1 x.2 * dd2 hf y m m x.1 x.2)
      + ∑ x : Fin 3 × Fin 3, (-(3 / 2) : ℝ) * (pd1 (fun z => hf z x.1 m) y m * pd1 (fun w => hf w x.1 x.2) y x.2 +
          hf y x.1 m * dd2 hf y x.2 m x.1 x.2) := fun m => by
    have p1 := pd1_sum_prod (ι := Fin 3 × Fin 3) (fun _ => (1 / 2 : ℝ)) (fun x z => hf z x.1 x.1)
      (fun x z => pd1 (fun w => hf w x.2 m) z x.2) (fun x => hA _ _) (fun x => hB _ _ _) y m
    have p2 := pd1_sum_prod (ι := Fin 3 × Fin 3) (fun _ => (-(1 / 2) : ℝ)) (fun x z => hf z x.1 x.1)
      (fun x z => pd1 (fun w => hf w x.2 x.2) z m) (fun x => hA _ _) (fun x => hB _ _ _) y m
    have p3 := pd1_sum_prod (ι := Fin 3 × Fin 3) (fun _ => (-(1 / 2) : ℝ)) (fun x z => hf z x.1 x.2)
      (fun x z => pd1 (fun w => hf w x.2 m) z x.1) (fun x => hA _ _) (fun x => hB _ _ _) y m
    have p4 := pd1_sum_prod (ι := Fin 3 × Fin 3) (fun _ => (1 : ℝ)) (fun x z => hf z x.1 m)
      (fun x z => pd1 (fun w => hf w x.2 x.2) z x.1) (fun x => hA _ _) (fun x => hB _ _ _) y m
    have p5 := pd1_sum_prod (ι := Fin 3 × Fin 3) (fun _ => (1 : ℝ)) (fun x z => hf z x.1 x.2)
      (fun x z => pd1 (fun w => hf w x.1 x.2) z m) (fun x => hA _ _) (fun x => hB _ _ _) y m
    have p6 := pd1_sum_prod (ι := Fin 3 × Fin 3) (fun _ => (-(3 / 2) : ℝ)) (fun x z => hf z x.1 m)
      (fun x z => pd1 (fun w => hf w x.1 x.2) z x.2) (fun x => hA _ _) (fun x => hB _ _ _) y m
    have d1 : Differentiable ℝ (U1 hf m) := by unfold U1; fun_prop
    have d2 : Differentiable ℝ (U2 hf m) := by unfold U2; fun_prop
    have d3 : Differentiable ℝ (U3 hf m) := by unfold U3; fun_prop
    have d4 : Differentiable ℝ (U4 hf m) := by unfold U4; fun_prop
    have d5 : Differentiable ℝ (U5 hf m) := by unfold U5; fun_prop
    have d6 : Differentiable ℝ (U6 hf m) := by unfold U6; fun_prop
    have e := pd1_add6 d1 d2 d3 d4 d5 d6 y m
    have hT : Tprime hf m = fun z => U1 hf m z + U2 hf m z + U3 hf m z + U4 hf m z + U5 hf m z + U6 hf m z := rfl
    rw [hT]
    refine e.trans ?_
    unfold U1 U2 U3 U4 U5 U6
    rw [p1, p2, p3, p4, p5, p6]
    simp only [hdd]
  simp only [key, divTp, trH, Hm, dh1, Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

/-- The field `Tprime` is `C¹`. -/
theorem contDiff_Tprime (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (m : Fin 3) :
    ContDiff ℝ 1 (Tprime hf m) := by
  have hA : ∀ i j, ContDiff ℝ 1 (fun z => hf z i j) := fun i j => (hsm i j).of_le (by norm_num)
  have hB : ∀ k l n, ContDiff ℝ 1 (fun z => pd1 (fun w => hf w l n) z k) := fun k l n =>
    contDiff_pd1 (n := 1) ((hsm l n).of_le (by norm_num)) k
  unfold Tprime U1 U2 U3 U4 U5 U6
  fun_prop

/-- The field `Tprime` is periodic. -/
theorem periodic_Tprime (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p)
    (m : Fin 3) (p : Fin 3 → ℝ) (e : Fin 3 → ℤ) :
    Tprime hf m (p + fun i => (e i : ℝ)) = Tprime hf m p := by
  have hA : ∀ i j, hf (p + fun i => (e i : ℝ)) i j = hf p i j := fun i j => by rw [hper]
  have hB : ∀ l n k, pd1 (fun z => hf z l n) (p + fun i => (e i : ℝ)) k = pd1 (fun z => hf z l n) p k :=
    fun l n k => pd1_periodic (fun q e' => by rw [hper]) p e k
  simp only [Tprime, U1, U2, U3, U4, U5, U6, hA, hB]

/-- The jet `(h, ∂h, ∂∂h)` of a matrix field at a point. -/
noncomputable def jetOf (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (y : Fin 3 → ℝ) : Jet3 :=
  (fun i j => hf y i j, dh1 hf y, dd2 hf y)

/-- The symmetries of the jet of a symmetric `C³` field. -/
theorem jet_symm (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i)
    (y : Fin 3 → ℝ) :
    (∀ i j, (jetOf hf y).1 i j = (jetOf hf y).1 j i) ∧ (∀ k i j, (jetOf hf y).2.1 k i j = (jetOf hf y).2.1 k j i) ∧
    (∀ k l i j, (jetOf hf y).2.2 k l i j = (jetOf hf y).2.2 l k i j) ∧
    (∀ k l i j, (jetOf hf y).2.2 k l i j = (jetOf hf y).2.2 k l j i) :=
  ⟨fun i j => hsymm y i j, fun k i j => by simp [jetOf, dh1, hsymm _ i j],
    fun k l i j => pd2_symm (hsm i j) y k l, fun k l i j => by simp [jetOf, dd2, hsymm _ i j]⟩

open Classical in
/-- **The integral of the first coefficient over the unit cube is zero.** -/
theorem integral_F1_zero (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p) :
    ∫ y in unitCube, F1 (jetOf hf y) = 0 := by
  have hdiv := integral_div_periodic (S1field hf) (contDiff_S1field hsm) (periodic_S1field hper)
  have hpt : ∀ y, F1 (jetOf hf y) = 1 / 2 * ∑ i, fderiv ℝ (S1field hf i) y (Pi.single i 1) := fun y => by
    rw [F1_eq _ (jet_symm hsm hsymm y).2.2.1]
    show _ = 1 / 2 * ∑ i, pd1 (S1field hf i) y i
    rw [div_S1field hsm]
    have hs : ∀ i j, dd2 hf y j i i j = dd2 hf y i j i j := fun i j => pd2_symm (hsm i j) y j i
    simp only [jetOf, hs]
  simp only [hpt]
  rw [integral_const_mul, hdiv, mul_zero]

open Classical in
/-- **The integral of the second coefficient is the integral of the Fierz–Pauli density.** -/
theorem integral_F2_eq (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p) :
    ∫ y in unitCube, F2 (jetOf hf y) = ∫ y in unitCube, fpDens (dh1 hf y) := by
  have hdiv := integral_div_periodic (Tprime hf) (contDiff_Tprime hsm) (periodic_Tprime hper)
  have hpt : ∀ y, F2 (jetOf hf y) = fpDens (dh1 hf y) + ∑ m, fderiv ℝ (Tprime hf m) y (Pi.single m 1) := fun y => by
    obtain ⟨h1, h2, h3, h4⟩ := jet_symm hsm hsymm y
    rw [F2_eq _ h1 h2 h3 h4]
    show fpDens (dh1 hf y) + divTp (Hm hf y) (dh1 hf y) (dd2 hf y) = _ + ∑ m, pd1 (Tprime hf m) y m
    rw [div_Tprime hsm]
    congr 2
    funext a b i j
    exact pd2_symm (hsm i j) y a b
  have c2 : ∀ k i j, Continuous fun y => dh1 hf y k i j := fun k i j =>
    (contDiff_pd1 (n := 0) ((hsm i j).of_le (by norm_num)) k).continuous
  have i1 : Integrable (fun y => fpDens (dh1 hf y)) (volume.restrict unitCube) := by
    refine integrable_unitCube ?_
    simp only [fpDens]
    fun_prop
  have i2 : Integrable (fun y => ∑ m, fderiv ℝ (Tprime hf m) y (Pi.single m 1)) (volume.restrict unitCube) := by
    refine integrable_unitCube ?_
    refine continuous_finsetSum _ fun m _ => ?_
    exact ((contDiff_Tprime hsm m).continuous_fderiv (by norm_num)).clm_apply continuous_const
  simp only [hpt]
  rw [integral_add i1 i2, hdiv, add_zero]

end I2

end Lightlike.Regge.Linear3
