import Mathlib
import Lightlike.Canonical.CurvatureJet

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

end Algebra

end Lightlike.Canonical

end
