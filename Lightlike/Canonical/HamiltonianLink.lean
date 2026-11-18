import Mathlib
import Lightlike.Canonical.HamiltonianAlgebra
import Lightlike.Canonical.HamiltonianW
import Lightlike.Canonical.HamiltonianPm

/-!
# Linking the jet expressions to the index algebra

`Lbil`, `wDer` and `wJ` of the jets `δ_b ⊗ P`, `−(Hi P Hi)` and `∂P` are expressed through `G = Γ(Hi, ∂h)`, the
matrix `P` and its derivative (`LbG`, `wDG`, `Tnc`).
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- `Γ` of the jet `δ_b ⊗ P`, in the form `Qb`. -/
lemma gamJ_delta_Qb (Hi P : Matrix (Fin d) (Fin d) ℝ) (b i j k : Fin d) :
    gamJ Hi (fun a i j => if a = b then P i j else 0) i j k = Qb Hi P b i j k := by
  rw [gamJ_delta]
  unfold Qb
  simp only [Matrix.mul_apply]

/-- `Γ` for the inverse-metric change `−(Hi P Hi)`. -/
lemma gamJ_neg_sandwich (Hi P : Matrix (Fin d) (Fin d) ℝ) (H1 : H1arr d) (i j k : Fin d) :
    gamJ (-(Hi * P * Hi)) H1 i j k = -∑ m, (Hi * P) i m * gamJ Hi H1 m j k := by
  unfold gamJ
  have e : ∀ l, (-(Hi * P * Hi)) i l * (H1 j l k + H1 k l j - H1 l j k) =
      -∑ m, (Hi * P) i m * (Hi m l * (H1 j l k + H1 k l j - H1 l j k)) := by
    intro l
    simp only [Matrix.neg_apply, Matrix.mul_apply (M := Hi * P) (N := Hi), neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [e, Finset.sum_neg_distrib]
  rw [mul_neg]
  congr 1
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring

/-- `Lbil` of the jet `δ_b ⊗ P` is `LbG`. -/
lemma Lbil_delta (Hi P : Matrix (Fin d) (Fin d) ℝ) (H1 : H1arr d) (b : Fin d) :
    Lbil Hi H1 (fun a i j => if a = b then P i j else 0) = LbG Hi P (gamJ Hi H1) b := by
  unfold Lbil LbG
  simp only [gamJ_delta_Qb]

/-- `wDer` for the change `−(Hi P Hi)` is `wDG`. -/
lemma wDer_sandwich (Hi P : Matrix (Fin d) (Fin d) ℝ) (H1 : H1arr d) (b : Fin d) :
    wDer Hi (-(Hi * P * Hi)) H1 b = wDG Hi P (gamJ Hi H1) b := by
  unfold wDer wDG
  simp only [gamJ_neg_sandwich]

/-- `w^b` of a symmetric jet is the divergence-type contraction `Tnc`. -/
lemma wJ_eq_Tnc (Hi : Matrix (Fin d) (Fin d) ℝ) (X : H1arr d) (hHi : ∀ i j, Hi i j = Hi j i)
    (hX : ∀ a i j, X a i j = X a j i) (b : Fin d) : wJ Hi X b = Tnc Hi X b := by
  unfold wJ Tnc gamJ
  have s1 : ∀ σ ν, Hi σ ν * (1 / 2 * ∑ l, Hi b l * (X σ l ν + X ν l σ - X l σ ν)) =
      1 / 2 * (Hi σ ν * ∑ l, Hi b l * X σ l ν) + 1 / 2 * (Hi σ ν * ∑ l, Hi b l * X ν l σ) -
        1 / 2 * (Hi σ ν * ∑ l, Hi b l * X l σ ν) := fun σ ν => by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have s2 : ∑ σ, ∑ ν, Hi σ ν * ∑ l, Hi b l * X ν l σ = ∑ σ, ∑ ν, Hi σ ν * ∑ l, Hi b l * X σ l ν := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => by rw [hHi σ ν]
  have s3 : ∀ σ, ∑ l, 1 / 2 * ∑ m, Hi l m * (X σ m l + X l m σ - X m σ l) =
      1 / 2 * ∑ l, ∑ m, Hi l m * X σ l m := by
    intro σ
    have a1 : ∑ l, ∑ m, Hi l m * X σ m l = ∑ l, ∑ m, Hi l m * X σ l m := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by rw [hHi m l]
    have a2 : ∑ l, ∑ m, Hi l m * X l m σ = ∑ l, ∑ m, Hi l m * X m σ l := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by rw [hHi m l, hX m σ l]
    simp only [← Finset.mul_sum, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [a1, a2]; ring
  have s4 : ∀ σ ν, Hi σ ν * ∑ l, Hi b l * (X σ l ν - 1 / 2 * X l σ ν) =
      Hi σ ν * ∑ l, Hi b l * X σ l ν - 1 / 2 * (Hi σ ν * ∑ l, Hi b l * X l σ ν) := fun σ ν => by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [s1, s4, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, s2, s3]
  have h6 : ∑ x, Hi b x * (1 / 2 * ∑ l, ∑ m, Hi l m * X x l m) =
      1 / 2 * ∑ σ, Hi b σ * ∑ l, ∑ m, Hi l m * X σ l m := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  linarith [h6]

/-- `h_{im} Γ^m_{jk}` is the Christoffel symbol of the first kind. -/
lemma h_mul_gamJ (h Hi : Matrix (Fin d) (Fin d) ℝ) (H1 : H1arr d) (hhH : h * Hi = 1) (i j k : Fin d) :
    ∑ m, h i m * gamJ Hi H1 m j k = 1 / 2 * (H1 j i k + H1 k i j - H1 i j k) := by
  unfold gamJ
  have : ∀ m, h i m * (1 / 2 * ∑ l, Hi m l * (H1 j l k + H1 k l j - H1 l j k)) =
      ∑ l, 1 / 2 * (h i m * Hi m l) * (H1 j l k + H1 k l j - H1 l j k) := fun m => by
    rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  simp only [this]
  rw [Finset.sum_comm]
  have e : ∀ l, ∑ m, 1 / 2 * (h i m * Hi m l) * (H1 j l k + H1 k l j - H1 l j k) =
      1 / 2 * (if i = l then 1 else 0) * (H1 j l k + H1 k l j - H1 l j k) := by
    intro l
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have := congrFun (congrFun hhH i) l
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [this]
  simp only [e]
  simp [Finset.sum_ite_eq]

/-- The metric derivative is `h Γ_a + Γ_aᵀ h`: `∂_a h_ij = h_{im} Γ^m_{aj} + h_{jm} Γ^m_{ai}`. -/
lemma dh_eq (h Hi : Matrix (Fin d) (Fin d) ℝ) (H1 : H1arr d) (hhH : h * Hi = 1)
    (hh : ∀ i j, h i j = h j i) (hX : ∀ a i j, H1 a i j = H1 a j i) (a : Fin d) :
    (Matrix.of fun i j => H1 a i j) =
      h * (Matrix.of fun m j => gamJ Hi H1 m a j) + (Matrix.of fun m j => gamJ Hi H1 m a j)ᵀ * h := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
  have h1 := h_mul_gamJ h Hi H1 hhH i a j
  have h2 := h_mul_gamJ h Hi H1 hhH j a i
  have h3 : ∑ m, gamJ Hi H1 m a i * h m j = ∑ m, h j m * gamJ Hi H1 m a i :=
    Finset.sum_congr rfl fun m _ => by rw [mul_comm, hh m j]
  rw [h1, h3, h2]
  have := hX j i a
  have := hX i j a
  have := hX a j i
  linarith

/-- The trace of the Christoffel symbol: `Γ^m_{am} = ½ tr(Hi ∂_a h)`. -/
lemma gamJ_trace (Hi : Matrix (Fin d) (Fin d) ℝ) (H1 : H1arr d) (hHi : ∀ i j, Hi i j = Hi j i)
    (hX : ∀ a i j, H1 a i j = H1 a j i) (a : Fin d) :
    ∑ m, gamJ Hi H1 m a m = 1 / 2 * (Hi * Matrix.of fun i j => H1 a i j).trace := by
  unfold gamJ
  simp only [← Finset.mul_sum]
  have e : ∀ m, ∑ l, Hi m l * (H1 a l m + H1 m l a - H1 l a m) =
      ∑ l, Hi m l * H1 a l m + (∑ l, Hi m l * H1 m l a - ∑ l, Hi m l * H1 l a m) := fun m => by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have c : ∑ m, ∑ l, Hi m l * H1 m l a = ∑ m, ∑ l, Hi m l * H1 l a m := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by rw [hHi l m, hX l m a]
  rw [c]
  simp [Matrix.trace, Matrix.mul_apply]

/-- **Stage 2a**: the plain derivative of `X = 2 hπh − c t h` minus its Christoffel correction is `2 h Dπ h − c e h`. -/
lemma stage2a (h π dπ Ga : Matrix (Fin d) (Fin d) ℝ) (c t gtr dt e : ℝ) (he : e = dt - gtr * t) :
    (-gtr) • ((2 : ℝ) • (h * π * h) - (c * t) • h) +
        (2 : ℝ) • ((h * Ga + Gaᵀ * h) * π * h + h * dπ * h + h * π * (h * Ga + Gaᵀ * h)) -
        c • (dt • h + t • (h * Ga + Gaᵀ * h)) -
      (Gaᵀ * ((2 : ℝ) • (h * π * h) - (c * t) • h) + ((2 : ℝ) • (h * π * h) - (c * t) • h) * Ga) =
    (2 : ℝ) • (h * (dπ + Ga * π + π * Gaᵀ - gtr • π) * h) - (c * e) • h := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc, he]
  module

/-- The trace identity `tr(Dπ h) = tr(dh π + h dπ) − gtr · tr(hπ)` for `dh = h Ga + Gaᵀ h`. -/
lemma trace_Dpi (h π dπ Ga : Matrix (Fin d) (Fin d) ℝ) (gtr : ℝ) (hh : hᵀ = h) (hπ : πᵀ = π) :
    ((dπ + Ga * π + π * Gaᵀ - gtr • π) * h).trace =
      ((h * Ga + Gaᵀ * h) * π + h * dπ).trace - gtr * (h * π).trace := by
  have c1 : (Ga * π * h).trace = (h * Ga * π).trace := by
    rw [Matrix.trace_mul_comm (Ga * π) h, Matrix.mul_assoc]
  have c2 : (π * Gaᵀ * h).trace = (Gaᵀ * h * π).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm π (Gaᵀ * h), Matrix.mul_assoc]
  have c3 : (dπ * h).trace = (h * dπ).trace := Matrix.trace_mul_comm _ _
  have c4 : (π * h).trace = (h * π).trace := Matrix.trace_mul_comm _ _
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul]
  rw [c1, c2, c3, c4]
  ring

/-- The unit `π`-gradient is `X / √det h` (for symmetric `h`, `π`). -/
lemma Pm_eq_Xfield (h π : TensorField d) (hs : ∀ y, (h y)ᵀ = h y) (hps : ∀ y, (π y)ᵀ = π y) (y : Fin d → ℝ) :
    Pm h π y = (Real.sqrt (h y).det)⁻¹ • Xfield (2 / ((d : ℝ) - 1)) h π y := by
  unfold Pm hamiltonianPiGradient Xfield
  simp only [div_eq_inv_mul]
  rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_mul, hs y, hps y]
  simp only [Matrix.mul_assoc]
  rw [mul_one]
  simp only [two_smul]

/-- The covariant derivative of the density `π` along `a`:
`D_a π = ∂_a π + Γ_a π + π Γ_aᵀ − (tr Γ_a) π`, with `(Γ_a)_{mj} = Γ^m_{aj}` of the jet `∂h` at `x`. -/
def Dpi (h π : TensorField d) (x : Fin d → ℝ) (a : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  dM a π x + (Matrix.of fun m j => gamJ (h x)⁻¹ (jet1 h x) m a j) * π x +
    π x * (Matrix.of fun m j => gamJ (h x)⁻¹ (jet1 h x) m a j)ᵀ -
    (∑ m, gamJ (h x)⁻¹ (jet1 h x) m a m) • π x

/-- **The plain derivative of the unit `π`-gradient minus its Christoffel correction** is
`(1/√det h) · (2 h D_aπ h − c tr(D_aπ h) h)`. -/
lemma dP_sub_corr {h π : TensorField d} (hh : SmoothTensor h) (hπ : SmoothTensor π)
    (hs : ∀ y, (h y)ᵀ = h y) (hps : ∀ y, (π y)ᵀ = π y) {x : Fin d → ℝ} (hpos : 0 < (h x).det) (a : Fin d) :
    dM a (Pm h π) x - ((Matrix.of fun m j => gamJ (h x)⁻¹ (jet1 h x) m a j)ᵀ * Pm h π x +
        Pm h π x * (Matrix.of fun m j => gamJ (h x)⁻¹ (jet1 h x) m a j)) =
      (Real.sqrt (h x).det)⁻¹ • Ymat (h x) (Dpi h π x) (2 / ((d : ℝ) - 1)) a := by
  set c : ℝ := 2 / ((d : ℝ) - 1) with hc
  set s : ℝ := Real.sqrt (h x).det with hsdef
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hdetU : IsUnit (h x).det := hpos.ne'.isUnit
  set Hi : Matrix (Fin d) (Fin d) ℝ := (h x)⁻¹ with hHi
  have hhH : h x * Hi = 1 := Matrix.mul_nonsing_inv _ hdetU
  have hHs : Hiᵀ = Hi := by
    rw [hHi, Matrix.transpose_nonsing_inv, hs x]
  have hHsym : ∀ i j, Hi i j = Hi j i := fun i j => by
    have := congrFun (congrFun hHs j) i
    simpa [Matrix.transpose_apply] using this
  have hsym : ∀ i j, h x i j = h x j i := fun i j => by
    have := congrFun (congrFun (hs x) j) i
    simpa [Matrix.transpose_apply] using this
  have hH1 : ∀ k i j, jet1 h x k i j = jet1 h x k j i := fun k i j => by
    unfold jet1
    have : (fun y => h y i j) = fun y => h y j i := funext fun y => by
      have := congrFun (congrFun (hs y) j) i
      simpa [Matrix.transpose_apply] using this
    rw [this]
  set Ga : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun m j => gamJ Hi (jet1 h x) m a j with hGa
  set gtr : ℝ := ∑ m, gamJ Hi (jet1 h x) m a m with hgtr
  have hdh : dM a h x = h x * Ga + Gaᵀ * h x := dh_eq (h x) Hi (jet1 h x) hhH hsym hH1 a
  have hgtr' : gtr = 1 / 2 * (Hi * dM a h x).trace := gamJ_trace Hi (jet1 h x) hHsym hH1 a
  -- the derivative of `√det`
  have hds : Lightlike.pd a (fun y => Real.sqrt (h y).det) x = s * gtr := by
    rw [pd_sqrt_det hh hpos a]
    have : (Matrix.of fun a_1 b => Lightlike.pd a (fun y => h y a_1 b) x) = dM a h x := rfl
    rw [this, hgtr']
    have key : (h x).det = Real.sqrt (h x).det * Real.sqrt (h x).det := (Real.mul_self_sqrt hpos.le).symm
    rw [div_eq_iff (by positivity)]
    linear_combination ((h x)⁻¹ * dM a h x).trace * key
  -- the matrix form of the derivative of `P`
  have hdP : dM a (Pm h π) x = s⁻¹ • ((-gtr) • Xfield c h π x +
      (2 : ℝ) • (dM a h x * π x * h x + h x * dM a π x * h x + h x * π x * dM a h x) -
      c • ((dM a h x * π x + h x * dM a π x).trace • h x + (h x * π x).trace • dM a h x)) := by
    ext i j
    have e1 : (fun y => Pm h π y i j) = fun y => (Real.sqrt (h y).det)⁻¹ * Xfield c h π y i j := funext fun y => by
      rw [Pm_eq_Xfield h π hs hps y]; simp [hc]
    show Lightlike.pd a (fun y => Pm h π y i j) x = _
    rw [e1, pd_Pf hh hπ c hpos a i j, hds]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    field_simp
    ring
  have hPx : Pm h π x = s⁻¹ • Xfield c h π x := by rw [Pm_eq_Xfield h π hs hps x]
  have hY : Ymat (h x) (Dpi h π x) c a = (2 : ℝ) • (h x * (dM a π x + Ga * π x + π x * Gaᵀ - gtr • π x) * h x) -
      (c * ((dM a π x + Ga * π x + π x * Gaᵀ - gtr • π x) * h x).trace) • h x := rfl
  have he := trace_Dpi (h x) (π x) (dM a π x) Ga gtr (hs x) (hps x)
  have hs2 := stage2a (h x) (π x) (dM a π x) Ga c ((h x * π x).trace) gtr
    (((h x * Ga + Gaᵀ * h x) * π x + h x * dM a π x).trace)
    (((dM a π x + Ga * π x + π x * Gaᵀ - gtr • π x) * h x).trace) he
  rw [hdh] at hdP
  rw [hdP, hPx, hY, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, ← smul_sub]
  congr 1

/-- **Stage 2c**: the divergence of the covariant derivative `D π` is the covariant divergence of the momentum. -/
lemma sum_Dpi (h π : TensorField d) (x : Fin d → ℝ) (hπs : ∀ a b, π x a b = π x b a)
    (hΓ : ∀ i j k, gamJ (h x)⁻¹ (jet1 h x) i j k = gamJ (h x)⁻¹ (jet1 h x) i k j) (b : Fin d) :
    ∑ σ, Dpi h π x σ b σ = momentumDivergence h π b x := by
  unfold Dpi momentumDivergence
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.transpose_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, christoffel_eq_gamJ]
  have h1 : ∑ σ, ∑ m, gamJ (h x)⁻¹ (jet1 h x) b σ m * π x m σ =
      ∑ k, ∑ l, gamJ (h x)⁻¹ (jet1 h x) b k l * π x k l :=
    Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun m _ => by rw [hπs m σ]
  have h2 : ∑ σ, ∑ m, π x b m * gamJ (h x)⁻¹ (jet1 h x) σ σ m =
      ∑ σ, (∑ m, gamJ (h x)⁻¹ (jet1 h x) m σ m) * π x b σ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum, mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => hΓ σ σ m
  rw [h1, h2]
  simp only [dM, Matrix.of_apply]
  ring

/-- `X` is symmetric for symmetric data. -/
lemma Xfield_symm (c : ℝ) (h π : TensorField d) (hs : ∀ y, (h y)ᵀ = h y) (hps : ∀ y, (π y)ᵀ = π y)
    (y : Fin d → ℝ) : (Xfield c h π y)ᵀ = Xfield c h π y := by
  unfold Xfield
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_mul, hs y, hps y]
  simp only [Matrix.mul_assoc]

/-- The unit `π`-gradient is symmetric for symmetric data. -/
lemma Pm_symm (h π : TensorField d) (hs : ∀ y, (h y)ᵀ = h y) (hps : ∀ y, (π y)ᵀ = π y) (y : Fin d → ℝ)
    (i j : Fin d) : Pm h π y i j = Pm h π y j i := by
  rw [Pm_eq_Xfield h π hs hps y]
  have := congrFun (congrFun (Xfield_symm (2 / ((d : ℝ) - 1)) h π hs hps y) j) i
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.transpose_apply] at this
  rw [this]

/-- The correction `corr` of the index algebra as a matrix expression. -/
lemma corr_eq_mat (P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (a i j : Fin d) :
    corr P G a i j = ((Matrix.of fun m j => G m a j)ᵀ * P + P * Matrix.of fun m j => G m a j) i j := by
  unfold corr
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

end Lightlike.Canonical

end
