import Mathlib
import Lightlike.Canonical.CurvatureJet
import Lightlike.Canonical.DensityDeriv

/-!
# The scalar curvature as a first-order Lagrangian plus a total derivative

In terms of the 2-jet of a metric: `√h R = √h L + ∂_ρ (√h w^ρ)` with the Einstein `ΓΓ` Lagrangian
`L = h^{σν} (Γ^ρ_{λσ} Γ^λ_{ρν} − Γ^ρ_{σν} Γ^λ_{ρλ})` and `w^ρ = h^{σν} Γ^ρ_{σν} − h^{ρσ} Γ^λ_{σλ}`. The algebra is
`scalJ = LgJ + dwSum + divTerm` (`scalJ_eq`), for a symmetric inverse metric and symmetric jets. It lets the smeared
potential term of the Hamiltonian constraint be written, after one integration by parts, with first derivatives of the
metric only.
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- The Einstein `ΓΓ` Lagrangian (without the factor `√det h`) from the 1-jet. -/
def LgJ (Hi : Matrix (Fin d) (Fin d) ℝ) (H1 : Fin d → Fin d → Fin d → ℝ) : ℝ :=
  ∑ σ, ∑ ν, Hi σ ν * ∑ ρ, ∑ l, (gamJ Hi H1 ρ l σ * gamJ Hi H1 l ρ ν - gamJ Hi H1 ρ σ ν * gamJ Hi H1 l ρ l)

/-- The vector `w^ρ = h^{σν} Γ^ρ_{σν} − h^{ρσ} Γ^λ_{σλ}` from the 1-jet. -/
def wJ (Hi : Matrix (Fin d) (Fin d) ℝ) (H1 : Fin d → Fin d → Fin d → ℝ) (ρ : Fin d) : ℝ :=
  ∑ σ, ∑ ν, Hi σ ν * gamJ Hi H1 ρ σ ν - ∑ σ, Hi ρ σ * ∑ l, gamJ Hi H1 l σ l

lemma gamJ_symm {Hi : Matrix (Fin d) (Fin d) ℝ} {H1 : Fin d → Fin d → Fin d → ℝ}
    (hH1 : ∀ k a b, H1 k a b = H1 k b a) (i j k : Fin d) : gamJ Hi H1 i j k = gamJ Hi H1 i k j := by
  unfold gamJ
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hH1 l j k]; ring

/-- `∂_μ h^{il} = −Γ^i_{μc} h^{cl} − Γ^l_{μc} h^{ic}`. -/
lemma dHiJ_eq {Hi : Matrix (Fin d) (Fin d) ℝ} {H1 : Fin d → Fin d → Fin d → ℝ}
    (hHi : ∀ a b, Hi a b = Hi b a) (hH1 : ∀ k a b, H1 k a b = H1 k b a) (μ i l : Fin d) :
    dHiJ Hi H1 μ i l = -∑ c, gamJ Hi H1 i μ c * Hi c l - ∑ c, gamJ Hi H1 l μ c * Hi i c := by
  unfold dHiJ gamJ
  simp only [Finset.mul_sum, Finset.sum_mul]
  have hS2 : ∑ c, ∑ a, 1 / 2 * (Hi l a * (H1 μ a c + H1 c a μ - H1 a μ c)) * Hi i c =
      ∑ b, ∑ c, 1 / 2 * (Hi l b * (H1 μ b c + H1 c b μ - H1 b μ c)) * Hi i c := Finset.sum_comm
  rw [hS2, ← sub_eq_zero]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
  rw [hHi l b, hH1 μ b c, hH1 b μ c, hH1 c μ b]
  ring

/-- `∂_ρ w^ρ` (without the divergence of the density) from the 2-jet. -/
def dwSum (Hi : Matrix (Fin d) (Fin d) ℝ) (H1 : Fin d → Fin d → Fin d → ℝ)
    (H2 : Fin d → Fin d → Fin d → Fin d → ℝ) : ℝ :=
  ∑ ρ, ((∑ σ, ∑ ν, (dHiJ Hi H1 ρ σ ν * gamJ Hi H1 ρ σ ν + Hi σ ν * dgamJ Hi H1 H2 ρ ρ σ ν)) -
    ∑ σ, (dHiJ Hi H1 ρ ρ σ * ∑ l, gamJ Hi H1 l σ l + Hi ρ σ * ∑ l, dgamJ Hi H1 H2 ρ l σ l))

/-- `Γ^λ_{ρλ} w^ρ`, the part of `∂_ρ (√h w^ρ)/√h` that comes from `∂_ρ √h`. -/
def divTerm (Hi : Matrix (Fin d) (Fin d) ℝ) (H1 : Fin d → Fin d → Fin d → ℝ) : ℝ :=
  ∑ ρ, (∑ l, gamJ Hi H1 l ρ l) * wJ Hi H1 ρ

lemma scalJ_split (Hi : Matrix (Fin d) (Fin d) ℝ) (H1 : Fin d → Fin d → Fin d → ℝ)
    (H2 : Fin d → Fin d → Fin d → Fin d → ℝ) :
    scalJ Hi H1 H2 =
      (∑ σ, ∑ ν, ∑ ρ, Hi σ ν * dgamJ Hi H1 H2 ρ ρ ν σ) - (∑ σ, ∑ ν, ∑ ρ, Hi σ ν * dgamJ Hi H1 H2 ν ρ ρ σ) +
      (∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ ρ l * gamJ Hi H1 l ν σ)) -
      (∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ ν l * gamJ Hi H1 l ρ σ)) := by
  unfold scalJ riemJ
  simp only [Finset.mul_sum, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

section Algebra

variable {Hi : Matrix (Fin d) (Fin d) ℝ} {H1 : Fin d → Fin d → Fin d → ℝ}
  {H2 : Fin d → Fin d → Fin d → Fin d → ℝ}

lemma dgamJ_symm (hHi : ∀ a b, Hi a b = Hi b a) (hH1 : ∀ k a b, H1 k a b = H1 k b a)
    (hH2 : ∀ m k a b, H2 m k a b = H2 m k b a) (μ i j k : Fin d) :
    dgamJ Hi H1 H2 μ i j k = dgamJ Hi H1 H2 μ i k j := by
  unfold dgamJ
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hH1 l j k, hH2 μ l j k]
  ring

/-- `Σ_ρ Γ^ρ_{ρ l} = Σ_ρ Γ^ρ_{l ρ}`: the trace of the Christoffel symbols, in the two conventions. -/
lemma trace_gam (hH1 : ∀ k a b, H1 k a b = H1 k b a) (l : Fin d) :
    ∑ ρ, gamJ Hi H1 ρ ρ l = ∑ ρ, gamJ Hi H1 ρ l ρ :=
  Finset.sum_congr rfl fun ρ _ => gamJ_symm hH1 ρ ρ l

/-- The two terms `Q_b` and `L_1`. -/
lemma L1_eq_Qb (hHi : ∀ a b, Hi a b = Hi b a) (hH1 : ∀ k a b, H1 k a b = H1 k b a) :
    ∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ l σ * gamJ Hi H1 l ρ ν) =
      ∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ ν l * gamJ Hi H1 l ρ σ) := by
  calc ∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ l σ * gamJ Hi H1 l ρ ν)
      = ∑ ν, ∑ σ, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ l σ * gamJ Hi H1 l ρ ν) := Finset.sum_comm
    _ = ∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ ν l * gamJ Hi H1 l ρ σ) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun l _ => ?_
        rw [hHi b a, gamJ_symm hH1 ρ l b]

lemma sum3_cyc' (f : Fin d → Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ i, ∑ j, f i j k := by
  calc ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm

/-- `D_A = W_2`. -/
lemma Da_eq (hH1 : ∀ k a b, H1 k a b = H1 k b a) (hH2 : ∀ m k a b, H2 m k a b = H2 m k b a)
    (hHi : ∀ a b, Hi a b = Hi b a) :
    ∑ σ, ∑ ν, ∑ ρ, Hi σ ν * dgamJ Hi H1 H2 ρ ρ ν σ =
      ∑ ρ, ∑ σ, ∑ ν, Hi σ ν * dgamJ Hi H1 H2 ρ ρ σ ν := by
  rw [sum3_cyc']
  exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => by
    rw [dgamJ_symm hHi hH1 hH2 ρ ρ ν σ]

/-- `D_B = W_4`. -/
lemma Db_eq (hH1 : ∀ k a b, H1 k a b = H1 k b a) (hH2 : ∀ m k a b, H2 m k a b = H2 m k b a)
    (hHi : ∀ a b, Hi a b = Hi b a) :
    ∑ σ, ∑ ν, ∑ ρ, Hi σ ν * dgamJ Hi H1 H2 ν ρ ρ σ =
      ∑ ρ, ∑ σ, Hi ρ σ * ∑ l, dgamJ Hi H1 H2 ρ l σ l := by
  calc ∑ σ, ∑ ν, ∑ ρ, Hi σ ν * dgamJ Hi H1 H2 ν ρ ρ σ
      = ∑ ν, ∑ σ, ∑ ρ, Hi σ ν * dgamJ Hi H1 H2 ν ρ ρ σ := Finset.sum_comm
    _ = ∑ ρ, ∑ σ, Hi ρ σ * ∑ l, dgamJ Hi H1 H2 ρ l σ l := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hHi b a, dgamJ_symm hHi hH1 hH2 a l l b]

/-- A permutation of four sums: `(a, b, c, e) ↦ (c, e, b, a)`. -/
lemma sum4_perm (f : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ b, ∑ a, f a b c e := by
  calc ∑ a, ∑ b, ∑ c, ∑ e, f a b c e
      = ∑ a, ∑ c, ∑ b, ∑ e, f a b c e := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ e, f a b c e := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ b, ∑ a, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => Finset.sum_comm

/-- `∂ h^{-1}`-terms: `A = Q_b`. -/
lemma A_eq_Qb (hH1 : ∀ k a b, H1 k a b = H1 k b a) :
    ∑ ρ, ∑ σ, ∑ ν, ∑ c, gamJ Hi H1 σ ρ c * Hi c ν * gamJ Hi H1 ρ σ ν =
      ∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ ν l * gamJ Hi H1 l ρ σ) := by
  rw [sum4_perm (fun s n r l => Hi s n * (gamJ Hi H1 r n l * gamJ Hi H1 l r s))]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  rw [gamJ_symm hH1 a b c]
  ring

lemma B_eq_A (hHi : ∀ a b, Hi a b = Hi b a) (hH1 : ∀ k a b, H1 k a b = H1 k b a) :
    ∑ ρ, ∑ σ, ∑ ν, ∑ c, gamJ Hi H1 ν ρ c * Hi σ c * gamJ Hi H1 ρ σ ν =
      ∑ ρ, ∑ σ, ∑ ν, ∑ c, gamJ Hi H1 σ ρ c * Hi c ν * gamJ Hi H1 ρ σ ν := by
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hHi b c, gamJ_symm hH1 ρ a b]

/-- `W_1 = −2 Q_b`. -/
lemma W1_eq (hHi : ∀ a b, Hi a b = Hi b a) (hH1 : ∀ k a b, H1 k a b = H1 k b a) :
    ∑ ρ, ∑ σ, ∑ ν, dHiJ Hi H1 ρ σ ν * gamJ Hi H1 ρ σ ν =
      -2 * ∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ ν l * gamJ Hi H1 l ρ σ) := by
  have hA := A_eq_Qb (Hi := Hi) hH1
  have hB := B_eq_A hHi hH1
  have e : ∑ ρ, ∑ σ, ∑ ν, dHiJ Hi H1 ρ σ ν * gamJ Hi H1 ρ σ ν =
      -(∑ ρ, ∑ σ, ∑ ν, ∑ c, gamJ Hi H1 σ ρ c * Hi c ν * gamJ Hi H1 ρ σ ν) -
        ∑ ρ, ∑ σ, ∑ ν, ∑ c, gamJ Hi H1 ν ρ c * Hi σ c * gamJ Hi H1 ρ σ ν := by
    simp only [dHiJ_eq hHi hH1, sub_mul, neg_mul, Finset.sum_mul, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib]
  rw [e, hB, hA]
  ring

/-- `L_2 = Z_1`. -/
lemma L2_eq_Z1 :
    ∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ σ ν * gamJ Hi H1 l ρ l) =
      ∑ ρ, (∑ l, gamJ Hi H1 l ρ l) * ∑ σ, ∑ ν, Hi σ ν * gamJ Hi H1 ρ σ ν := by
  rw [sum4_perm (fun s n r l => Hi s n * (gamJ Hi H1 r s n * gamJ Hi H1 l r l))]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma LgJ_eq : LgJ Hi H1 =
    (∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ l σ * gamJ Hi H1 l ρ ν)) -
      ∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ σ ν * gamJ Hi H1 l ρ l) := by
  unfold LgJ
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]

lemma dwSum_eq : dwSum Hi H1 H2 =
    (∑ ρ, ∑ σ, ∑ ν, dHiJ Hi H1 ρ σ ν * gamJ Hi H1 ρ σ ν) +
      (∑ ρ, ∑ σ, ∑ ν, Hi σ ν * dgamJ Hi H1 H2 ρ ρ σ ν) -
      (∑ ρ, ∑ σ, dHiJ Hi H1 ρ ρ σ * ∑ l, gamJ Hi H1 l σ l) -
      ∑ ρ, ∑ σ, Hi ρ σ * ∑ l, dgamJ Hi H1 H2 ρ l σ l := by
  unfold dwSum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

lemma divTerm_eq : divTerm Hi H1 =
    (∑ ρ, (∑ l, gamJ Hi H1 l ρ l) * ∑ σ, ∑ ν, Hi σ ν * gamJ Hi H1 ρ σ ν) -
      ∑ ρ, (∑ l, gamJ Hi H1 l ρ l) * ∑ σ, Hi ρ σ * ∑ l, gamJ Hi H1 l σ l := by
  unfold divTerm wJ
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- `Q_a` as a sum over the trace of the Christoffel symbols. -/
lemma Qa_eq (hH1 : ∀ k a b, H1 k a b = H1 k b a) :
    ∑ σ, ∑ ν, ∑ ρ, ∑ l, Hi σ ν * (gamJ Hi H1 ρ ρ l * gamJ Hi H1 l ν σ) =
      ∑ l, (∑ m, gamJ Hi H1 m l m) * ∑ σ, ∑ ν, Hi σ ν * gamJ Hi H1 l σ ν := by
  rw [sum4_perm (fun s n r l => Hi s n * (gamJ Hi H1 r r l * gamJ Hi H1 l n s)), Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [gamJ_symm hH1 r r l, gamJ_symm hH1 l b a]
  ring

lemma W3_eq (hHi : ∀ a b, Hi a b = Hi b a) (hH1 : ∀ k a b, H1 k a b = H1 k b a) :
    ∑ ρ, ∑ σ, dHiJ Hi H1 ρ ρ σ * ∑ l, gamJ Hi H1 l σ l =
      -(∑ ρ, (∑ l, gamJ Hi H1 l ρ l) * ∑ σ, Hi ρ σ * ∑ l, gamJ Hi H1 l σ l) -
        ∑ l, (∑ m, gamJ Hi H1 m l m) * ∑ σ, ∑ ν, Hi σ ν * gamJ Hi H1 l σ ν := by
  have p1 : ∑ ρ, ∑ σ, (∑ c, gamJ Hi H1 ρ ρ c * Hi c σ) * ∑ l, gamJ Hi H1 l σ l =
      ∑ ρ, (∑ l, gamJ Hi H1 l ρ l) * ∑ σ, Hi ρ σ * ∑ l, gamJ Hi H1 l σ l := by
    calc ∑ ρ, ∑ σ, (∑ c, gamJ Hi H1 ρ ρ c * Hi c σ) * ∑ l, gamJ Hi H1 l σ l
        = ∑ ρ, ∑ σ, ∑ c, gamJ Hi H1 ρ ρ c * Hi c σ * ∑ l, gamJ Hi H1 l σ l := by
          simp only [Finset.sum_mul]
      _ = ∑ c, ∑ ρ, ∑ σ, gamJ Hi H1 ρ ρ c * Hi c σ * ∑ l, gamJ Hi H1 l σ l :=
          sum3_cyc' (fun ρ σ c => gamJ Hi H1 ρ ρ c * Hi c σ * ∑ l, gamJ Hi H1 l σ l)
      _ = ∑ ρ, (∑ l, gamJ Hi H1 l ρ l) * ∑ σ, Hi ρ σ * ∑ l, gamJ Hi H1 l σ l := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← trace_gam (Hi := Hi) hH1 c, Finset.sum_mul]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          ring
  have p2 : ∑ ρ, ∑ σ, (∑ c, gamJ Hi H1 σ ρ c * Hi ρ c) * ∑ l, gamJ Hi H1 l σ l =
      ∑ l, (∑ m, gamJ Hi H1 m l m) * ∑ σ, ∑ ν, Hi σ ν * gamJ Hi H1 l σ ν := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
  have e : ∑ ρ, ∑ σ, dHiJ Hi H1 ρ ρ σ * ∑ l, gamJ Hi H1 l σ l =
      -(∑ ρ, ∑ σ, (∑ c, gamJ Hi H1 ρ ρ c * Hi c σ) * ∑ l, gamJ Hi H1 l σ l) -
        ∑ ρ, ∑ σ, (∑ c, gamJ Hi H1 σ ρ c * Hi ρ c) * ∑ l, gamJ Hi H1 l σ l := by
    simp only [dHiJ_eq hHi hH1, sub_mul, neg_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [e, p1, p2]

/-- **The scalar curvature is a first-order Lagrangian plus a total derivative**, on 2-jets:
`R = L + Γ^λ_{ρλ} w^ρ + ∂_ρ w^ρ`, for a symmetric inverse metric and symmetric jets. -/
theorem scalJ_eq (hHi : ∀ a b, Hi a b = Hi b a) (hH1 : ∀ k a b, H1 k a b = H1 k b a)
    (hH2 : ∀ m k a b, H2 m k a b = H2 m k b a) :
    scalJ Hi H1 H2 = LgJ Hi H1 + dwSum Hi H1 H2 + divTerm Hi H1 := by
  rw [scalJ_split, LgJ_eq, dwSum_eq, divTerm_eq]
  have e1 := Da_eq (Hi := Hi) hH1 hH2 hHi
  have e2 := Db_eq (Hi := Hi) hH1 hH2 hHi
  have e3 := L1_eq_Qb (Hi := Hi) hHi hH1
  have e4 := W1_eq (Hi := Hi) hHi hH1
  have e5 := L2_eq_Z1 (Hi := Hi) (H1 := H1)
  have e6 := Qa_eq (Hi := Hi) hH1
  have e7 := W3_eq (Hi := Hi) hHi hH1
  linarith [e1, e2, e3, e4, e5, e6, e7]

/-- `Σ_l Γ^l_{ρ l} = ½ tr (h⁻¹ ∂_ρ h)`. -/
lemma trace_gam_eq (hHi : ∀ a b, Hi a b = Hi b a) (hH1 : ∀ k a b, H1 k a b = H1 k b a) (ρ : Fin d) :
    ∑ l, gamJ Hi H1 l ρ l = 1 / 2 * (Hi * Matrix.of fun a b => H1 ρ a b).trace := by
  have hz : ∑ l, ∑ a, Hi l a * (H1 l a ρ - H1 a ρ l) = 0 := by
    have : ∑ l, ∑ a, Hi l a * H1 l a ρ = ∑ l, ∑ a, Hi l a * H1 a ρ l := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => ?_
      rw [hHi a l, hH1 l a ρ]
    simp only [mul_sub, Finset.sum_sub_distrib, this, sub_self]
  unfold gamJ
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
  have h2 : ∑ x, ∑ i, 1 / 2 * (Hi x i * (H1 ρ i x + H1 x i ρ - H1 i ρ x)) =
      (∑ x, ∑ i, 1 / 2 * (Hi x i * H1 ρ i x)) + 1 / 2 * ∑ l, ∑ a, Hi l a * (H1 l a ρ - H1 a ρ l) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2, hz]; ring

end Algebra

section Analytic

variable {g : TensorField d}

lemma differentiableAt_inv_comp (hg : SmoothTensor g) {x : Fin d → ℝ} (hdet : (g x).det ≠ 0) (a b : Fin d) :
    DifferentiableAt ℝ (fun y => (g y)⁻¹ a b) x :=
  Gauge.differentiableAt_inv_entry g (fun i j => diff_of_smooth (hg i j) x) hdet a b

lemma pd_inv_entry (hg : SmoothTensor g) {x : Fin d → ℝ} (hdet : (g x).det ≠ 0) (μ a b : Fin d) :
    Lightlike.pd μ (fun y => (g y)⁻¹ a b) x = dHiJ (g x)⁻¹ (jet1 g x) μ a b := by
  unfold dHiJ Lightlike.pd
  rw [Gauge.fderiv_inv_entry_at g (fun a b => (hg a b).differentiable (by simp)) _ _ hdet]
  rfl

lemma differentiableAt_christoffel (hg : SmoothTensor g) {x : Fin d → ℝ} (hdet : (g x).det ≠ 0) (i j k : Fin d) :
    DifferentiableAt ℝ (fun y => Lightlike.christoffel g i j k y) x := by
  have dHi : ∀ i l, DifferentiableAt ℝ (fun y => (g y)⁻¹ i l) x := differentiableAt_inv_comp hg hdet
  have dT : ∀ l, DifferentiableAt ℝ (fun y => Lightlike.pd j (fun y => g y l k) y +
      Lightlike.pd k (fun y => g y l j) y - Lightlike.pd l (fun y => g y j k) y) x := fun l =>
    diff_of_smooth (((smooth_pd (hg l k) j).add (smooth_pd (hg l j) k)).sub (smooth_pd (hg j k) l)) x
  have e1 : (fun y => Lightlike.christoffel g i j k y) = fun y => (1 / 2 : ℝ) * ∑ l, (g y)⁻¹ i l *
      (Lightlike.pd j (fun y => g y l k) y + Lightlike.pd k (fun y => g y l j) y -
        Lightlike.pd l (fun y => g y j k) y) := rfl
  rw [e1]
  exact (DifferentiableAt.fun_sum fun l _ => (dHi i l).mul (dT l)).const_mul _

/-- The derivative of `w^ρ` in the direction `ρ`. -/
lemma pd_wJ (hg : SmoothTensor g) {x : Fin d → ℝ} (hdet : (g x).det ≠ 0) (ρ : Fin d) :
    Lightlike.pd ρ (fun y => wJ (g y)⁻¹ (jet1 g y) ρ) x =
      (∑ σ, ∑ ν, (dHiJ (g x)⁻¹ (jet1 g x) ρ σ ν * gamJ (g x)⁻¹ (jet1 g x) ρ σ ν +
          (g x)⁻¹ σ ν * dgamJ (g x)⁻¹ (jet1 g x) (jet2 g x) ρ ρ σ ν)) -
        ∑ σ, (dHiJ (g x)⁻¹ (jet1 g x) ρ ρ σ * ∑ l, gamJ (g x)⁻¹ (jet1 g x) l σ l +
          (g x)⁻¹ ρ σ * ∑ l, dgamJ (g x)⁻¹ (jet1 g x) (jet2 g x) ρ l σ l) := by
  have dHi := differentiableAt_inv_comp hg hdet
  have dΓ := differentiableAt_christoffel hg hdet
  have hw : (fun y => wJ (g y)⁻¹ (jet1 g y) ρ) = fun y =>
      (∑ σ, ∑ ν, (g y)⁻¹ σ ν * Lightlike.christoffel g ρ σ ν y) -
        ∑ σ, (g y)⁻¹ ρ σ * ∑ l, Lightlike.christoffel g l σ l y := rfl
  have dS1 : ∀ σ, DifferentiableAt ℝ (fun y => ∑ ν, (g y)⁻¹ σ ν * Lightlike.christoffel g ρ σ ν y) x :=
    fun σ => DifferentiableAt.fun_sum fun ν _ => (dHi σ ν).mul (dΓ ρ σ ν)
  have dS2 : ∀ σ, DifferentiableAt ℝ (fun y => (g y)⁻¹ ρ σ * ∑ l, Lightlike.christoffel g l σ l y) x :=
    fun σ => (dHi ρ σ).mul (DifferentiableAt.fun_sum fun l _ => dΓ l σ l)
  rw [hw]
  rw [Lightlike.pd_sub (f₁ := fun y => ∑ σ, ∑ ν, (g y)⁻¹ σ ν * Lightlike.christoffel g ρ σ ν y)
    (f₂ := fun y => ∑ σ, (g y)⁻¹ ρ σ * ∑ l, Lightlike.christoffel g l σ l y)
    (DifferentiableAt.fun_sum fun σ _ => dS1 σ) (DifferentiableAt.fun_sum fun σ _ => dS2 σ)]
  rw [Lightlike.pd_sum Finset.univ (f := fun σ y => ∑ ν, (g y)⁻¹ σ ν * Lightlike.christoffel g ρ σ ν y)
    (fun σ _ => dS1 σ),
    Lightlike.pd_sum Finset.univ (f := fun σ y => (g y)⁻¹ ρ σ * ∑ l, Lightlike.christoffel g l σ l y)
    (fun σ _ => dS2 σ)]
  congr 1
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Lightlike.pd_sum Finset.univ (f := fun ν y => (g y)⁻¹ σ ν * Lightlike.christoffel g ρ σ ν y)
      (fun ν _ => (dHi σ ν).mul (dΓ ρ σ ν))]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Lightlike.pd_mul (dHi σ ν) (dΓ ρ σ ν), pd_inv_entry hg hdet, pd_christoffel hg hdet]
    rfl
  · refine Finset.sum_congr rfl fun σ _ => ?_
    have dsum : DifferentiableAt ℝ (fun y => ∑ l, Lightlike.christoffel g l σ l y) x :=
      DifferentiableAt.fun_sum fun l _ => dΓ l σ l
    rw [Lightlike.pd_mul (dHi ρ σ) dsum, pd_inv_entry hg hdet,
      Lightlike.pd_sum Finset.univ (f := fun l y => Lightlike.christoffel g l σ l y) (fun l _ => dΓ l σ l)]
    congr 2
    exact Finset.sum_congr rfl fun l _ => pd_christoffel hg hdet ρ l σ l

/-- **`√h R = √h L + ∂_ρ (√h w^ρ)`** for a smooth symmetric metric with `det > 0` at `x`. -/
theorem sqrtDet_mul_scalar (hg : SmoothTensor g) (hsymm : ∀ y a b, g y a b = g y b a) {x : Fin d → ℝ}
    (hpos : 0 < (g x).det) :
    Real.sqrt (g x).det * Lightlike.scalarCurvature g x =
      Real.sqrt (g x).det * LgJ (g x)⁻¹ (jet1 g x) +
        ∑ ρ, Lightlike.pd ρ (fun y => Real.sqrt (g y).det * wJ (g y)⁻¹ (jet1 g y) ρ) x := by
  have hdet : (g x).det ≠ 0 := hpos.ne'
  have hHi : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a := by
    intro a b
    have hT : (g x)ᵀ = g x := by ext i j; exact hsymm x j i
    have := congrFun (congrFun (Matrix.transpose_nonsing_inv (g x)) b) a
    rw [Matrix.transpose_apply, hT] at this
    exact this
  have hH1 : ∀ k a b, jet1 g x k a b = jet1 g x k b a := by
    intro k a b
    unfold jet1
    have : (fun y => g y a b) = fun y => g y b a := funext fun y => hsymm y a b
    rw [this]
  have hH2 : ∀ m k a b, jet2 g x m k a b = jet2 g x m k b a := by
    intro m k a b
    unfold jet2
    have : (fun y => g y a b) = fun y => g y b a := funext fun y => hsymm y a b
    rw [this]
  have hs := differentiableAt_sqrt_det_comp hg hpos
  have hW : ∀ ρ, DifferentiableAt ℝ (fun y => wJ (g y)⁻¹ (jet1 g y) ρ) x := by
    intro ρ
    have dHi := differentiableAt_inv_comp hg hdet
    have dΓ := differentiableAt_christoffel hg hdet
    have hw : (fun y => wJ (g y)⁻¹ (jet1 g y) ρ) = fun y =>
        (∑ σ, ∑ ν, (g y)⁻¹ σ ν * Lightlike.christoffel g ρ σ ν y) -
          ∑ σ, (g y)⁻¹ ρ σ * ∑ l, Lightlike.christoffel g l σ l y := rfl
    rw [hw]
    exact (DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.fun_sum fun ν _ => (dHi σ ν).mul (dΓ ρ σ ν)).sub
      (DifferentiableAt.fun_sum fun σ _ => (dHi ρ σ).mul (DifferentiableAt.fun_sum fun l _ => dΓ l σ l))
  have hps : ∀ ρ, Lightlike.pd ρ (fun y => Real.sqrt (g y).det) x =
      Real.sqrt (g x).det * ∑ l, gamJ (g x)⁻¹ (jet1 g x) l ρ l := by
    intro ρ
    rw [pd_sqrt_det hg hpos ρ, trace_gam_eq hHi hH1 ρ]
    have hsq : Real.sqrt (g x).det ^ 2 = (g x).det := Real.sq_sqrt hpos.le
    have hs0 : Real.sqrt (g x).det ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have e : (Matrix.of fun a b => Lightlike.pd ρ (fun y => g y a b) x) = Matrix.of fun a b => jet1 g x ρ a b := rfl
    rw [e, div_eq_iff (by positivity)]
    linear_combination (-(((g x)⁻¹ * Matrix.of fun a b => jet1 g x ρ a b).trace)) * hsq
  have hR := scalarCurvature_eq_scalJ hg hdet
  rw [hR, scalJ_eq hHi hH1 hH2]
  simp only [Lightlike.pd_mul hs (hW _), hps, Finset.sum_add_distrib]
  unfold dwSum divTerm
  simp only [pd_wJ hg hdet, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
  ring

end Analytic

end Lightlike.Canonical

end
