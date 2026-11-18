import Mathlib
import Lightlike.Canonical.FirstOrderPotential

/-!
# Stage 1 of the bracket of two Hamiltonian constraints: pure index algebra

For a symmetric inverse metric `Hi`, a symmetric `P`, and `G = Γ(Hi, ∂h)` symmetric in its lower indices, the
combination `-Lbil(δ_b ⊗ P) - ½ tr(Hi P) w^b - wDer(-(Hi P Hi))` equals the plain-minus-covariant correction
`Tnc(corr P G)` of the divergence-type contraction `Tnc` (`stage1`).
-/

open Finset Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- Index algebra for the bracket of two Hamiltonian constraints (`Qb`). -/
def Qb (Hi P : Matrix (Fin d) (Fin d) ℝ) (b i j k : Fin d) : ℝ :=
  1 / 2 * ((if j = b then (Hi * P) i k else 0) + (if k = b then (Hi * P) i j else 0) - Hi i b * P j k)

/-- Index algebra for the bracket of two Hamiltonian constraints (`q_i`). -/
lemma q_i (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (b σ ν : Fin d) :
    ∑ ρ, ∑ l, G ρ l σ * Qb Hi P b l ρ ν =
      1 / 2 * (∑ l, G b l σ * (Hi * P) l ν + (if ν = b then ∑ ρ, ∑ l, G ρ l σ * (Hi * P) l ρ else 0) -
        ∑ ρ, ∑ l, G ρ l σ * (Hi l b * P ρ ν)) := by
  have h1 : ∑ ρ, ∑ l, G ρ l σ * (1 / 2 * (if ρ = b then (Hi * P) l ν else 0)) =
      1 / 2 * ∑ l, G b l σ * (Hi * P) l ν := by
    rw [Finset.sum_comm]
    simp [Finset.mul_sum, Finset.sum_ite_eq', mul_left_comm, mul_ite]
  have h2 : ∑ ρ, ∑ l, G ρ l σ * (1 / 2 * (if ν = b then (Hi * P) l ρ else 0)) =
      1 / 2 * (if ν = b then ∑ ρ, ∑ l, G ρ l σ * (Hi * P) l ρ else 0) := by
    by_cases hν : ν = b <;> simp [hν, Finset.mul_sum, mul_left_comm]
  have h3 : ∑ ρ, ∑ l, G ρ l σ * (1 / 2 * (Hi l b * P ρ ν)) = 1 / 2 * ∑ ρ, ∑ l, G ρ l σ * (Hi l b * P ρ ν) := by
    simp [Finset.mul_sum, mul_left_comm]
  have e : ∀ ρ l, G ρ l σ * Qb Hi P b l ρ ν = G ρ l σ * (1 / 2 * (if ρ = b then (Hi * P) l ν else 0)) +
      G ρ l σ * (1 / 2 * (if ν = b then (Hi * P) l ρ else 0)) - G ρ l σ * (1 / 2 * (Hi l b * P ρ ν)) := by
    intro ρ l; unfold Qb; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3]; ring

/-- Index algebra for the bracket of two Hamiltonian constraints (`q_ii`). -/
lemma q_ii (Hi P : Matrix (Fin d) (Fin d) ℝ) (hHi : ∀ i j, Hi i j = Hi j i) (hP : ∀ i j, P i j = P j i)
    (b ρ : Fin d) :
    ∑ l, Qb Hi P b l ρ l = 1 / 2 * (if ρ = b then (Hi * P).trace else 0) := by
  have e : ∀ l, Qb Hi P b l ρ l = 1 / 2 * (if ρ = b then (Hi * P) l l else 0) +
      1 / 2 * ((if l = b then (Hi * P) l ρ else 0) - Hi l b * P ρ l) := by
    intro l; unfold Qb; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have h1 : ∑ l, (if ρ = b then (Hi * P) l l else 0) = if ρ = b then (Hi * P).trace else 0 := by
    by_cases h : ρ = b <;> simp [h, Matrix.trace]
  have h2 : ∑ l, Hi l b * P ρ l = (Hi * P) b ρ := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [hHi l b, hP ρ l]
  rw [h1, h2]
  simp [Finset.sum_ite_eq']

/-- Index algebra for the bracket of two Hamiltonian constraints (`q_iii`). -/
lemma q_iii (Hi P : Matrix (Fin d) (Fin d) ℝ) (hHi : ∀ i j, Hi i j = Hi j i) (hP : ∀ i j, P i j = P j i)
    (b ρ : Fin d) :
    ∑ σ, ∑ ν, Hi σ ν * Qb Hi P b ρ σ ν =
      (Hi * P * Hi) ρ b - 1 / 2 * Hi ρ b * (Hi * P).trace := by
  have e : ∀ σ ν, Hi σ ν * Qb Hi P b ρ σ ν = 1 / 2 * (Hi σ ν * (if σ = b then (Hi * P) ρ ν else 0)) +
      1 / 2 * (Hi σ ν * (if ν = b then (Hi * P) ρ σ else 0)) - 1 / 2 * (Hi σ ν * (Hi ρ b * P σ ν)) := by
    intro σ ν; unfold Qb; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ σ, ∑ ν, Hi σ ν * (if σ = b then (Hi * P) ρ ν else 0) = (Hi * P * Hi) ρ b := by
    rw [Finset.sum_eq_single b]
    · simp only [Matrix.mul_apply, hHi b, if_true, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    · intro σ _ hσ; simp [hσ]
    · simp
  have h2 : ∑ σ, ∑ ν, Hi σ ν * (if ν = b then (Hi * P) ρ σ else 0) = (Hi * P * Hi) ρ b := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  have h3 : ∑ σ, ∑ ν, Hi σ ν * (Hi ρ b * P σ ν) = Hi ρ b * (Hi * P).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [hP σ ν]; ring
  rw [h1, h2, h3]; ring

/-- The bilinear form `Lbil` for the jet `δ_b ⊗ P`, with `G = Γ(Hi, H1)`. -/
def LbG (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (b : Fin d) : ℝ :=
  ∑ σ, ∑ ν, Hi σ ν * ∑ ρ, ∑ l, (G ρ l σ * Qb Hi P b l ρ ν + Qb Hi P b ρ l σ * G l ρ ν -
    G ρ σ ν * Qb Hi P b l ρ l - Qb Hi P b ρ σ ν * G l ρ l)

/-- Index algebra for the bracket of two Hamiltonian constraints (`LbG_closed`). -/
lemma LbG_closed (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ)
    (hHi : ∀ i j, Hi i j = Hi j i) (hP : ∀ i j, P i j = P j i) (b : Fin d) :
    LbG Hi P G b =
      (∑ σ, ∑ ν, Hi σ ν * ∑ l, G b l σ * (Hi * P) l ν) +
      (∑ σ, Hi σ b * ∑ ρ, ∑ l, G ρ l σ * (Hi * P) l ρ) -
      (∑ σ, ∑ ν, Hi σ ν * ∑ ρ, ∑ l, G ρ l σ * (Hi l b * P ρ ν)) -
      1 / 2 * (Hi * P).trace * (∑ σ, ∑ ν, Hi σ ν * G b σ ν) -
      ∑ ρ, ((Hi * P * Hi) ρ b - 1 / 2 * Hi ρ b * (Hi * P).trace) * ∑ l, G l ρ l := by
  unfold LbG
  have hA : ∀ σ ν, ∑ ρ, ∑ l, Qb Hi P b ρ l σ * G l ρ ν = ∑ ρ, ∑ l, G ρ l ν * Qb Hi P b l ρ σ := by
    intro σ ν
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun l _ => by ring
  have hC : ∀ σ ν, ∑ ρ, ∑ l, G ρ σ ν * Qb Hi P b l ρ l = 1 / 2 * (Hi * P).trace * G b σ ν := by
    intro σ ν
    have : ∀ ρ, ∑ l, G ρ σ ν * Qb Hi P b l ρ l = G ρ σ ν * (1 / 2 * (if ρ = b then (Hi * P).trace else 0)) := by
      intro ρ; rw [← Finset.mul_sum, q_ii Hi P hHi hP]
    simp only [this]
    simp [mul_ite, Finset.sum_ite_eq']
    ring
  have hD : ∀ σ ν, ∑ ρ, ∑ l, Qb Hi P b ρ σ ν * G l ρ l = ∑ ρ, Qb Hi P b ρ σ ν * ∑ l, G l ρ l := by
    intro σ ν
    exact Finset.sum_congr rfl fun ρ _ => by rw [Finset.mul_sum]
  have e : ∀ σ ν, Hi σ ν * ∑ ρ, ∑ l, (G ρ l σ * Qb Hi P b l ρ ν + Qb Hi P b ρ l σ * G l ρ ν -
      G ρ σ ν * Qb Hi P b l ρ l - Qb Hi P b ρ σ ν * G l ρ l) =
      Hi σ ν * (∑ ρ, ∑ l, G ρ l σ * Qb Hi P b l ρ ν) + Hi σ ν * (∑ ρ, ∑ l, G ρ l ν * Qb Hi P b l ρ σ) -
      Hi σ ν * (1 / 2 * (Hi * P).trace * G b σ ν) -
      Hi σ ν * ∑ ρ, Qb Hi P b ρ σ ν * ∑ l, G l ρ l := by
    intro σ ν
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hA, hC, hD]
    ring
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => e σ ν]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- the symmetric partner
  have hS : ∑ σ, ∑ ν, Hi σ ν * (∑ ρ, ∑ l, G ρ l ν * Qb Hi P b l ρ σ) =
      ∑ σ, ∑ ν, Hi σ ν * (∑ ρ, ∑ l, G ρ l σ * Qb Hi P b l ρ ν) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => by rw [hHi σ ν]
  have hT4 : ∑ σ, ∑ ν, Hi σ ν * ∑ ρ, Qb Hi P b ρ σ ν * ∑ l, G l ρ l =
      ∑ ρ, ((Hi * P * Hi) ρ b - 1 / 2 * Hi ρ b * (Hi * P).trace) * ∑ l, G l ρ l := by
    have : ∀ σ ν, Hi σ ν * ∑ ρ, Qb Hi P b ρ σ ν * ∑ l, G l ρ l =
        ∑ ρ, (Hi σ ν * Qb Hi P b ρ σ ν) * ∑ l, G l ρ l := by
      intro σ ν; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ρ _ => by ring
    simp only [this]
    calc ∑ σ, ∑ ν, ∑ ρ, (Hi σ ν * Qb Hi P b ρ σ ν) * ∑ l, G l ρ l
        = ∑ ρ, ∑ σ, ∑ ν, (Hi σ ν * Qb Hi P b ρ σ ν) * ∑ l, G l ρ l := by
          rw [sum3_cyc']
      _ = ∑ ρ, (∑ σ, ∑ ν, Hi σ ν * Qb Hi P b ρ σ ν) * ∑ l, G l ρ l := by
          refine Finset.sum_congr rfl fun ρ _ => ?_
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun σ _ => by rw [Finset.sum_mul]
      _ = _ := by simp only [q_iii Hi P hHi hP]
  have hSA : ∑ σ, ∑ ν, Hi σ ν * (∑ ρ, ∑ l, G ρ l σ * Qb Hi P b l ρ ν) =
      1 / 2 * ((∑ σ, ∑ ν, Hi σ ν * ∑ l, G b l σ * (Hi * P) l ν) +
        (∑ σ, Hi σ b * ∑ ρ, ∑ l, G ρ l σ * (Hi * P) l ρ) -
        (∑ σ, ∑ ν, Hi σ ν * ∑ ρ, ∑ l, G ρ l σ * (Hi l b * P ρ ν))) := by
    have e2 : ∀ σ ν, Hi σ ν * (∑ ρ, ∑ l, G ρ l σ * Qb Hi P b l ρ ν) =
        1 / 2 * (Hi σ ν * ∑ l, G b l σ * (Hi * P) l ν) +
        1 / 2 * (Hi σ ν * (if ν = b then ∑ ρ, ∑ l, G ρ l σ * (Hi * P) l ρ else 0)) -
        1 / 2 * (Hi σ ν * ∑ ρ, ∑ l, G ρ l σ * (Hi l b * P ρ ν)) := by
      intro σ ν; rw [q_i]; ring
    simp only [e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h : ∑ σ, ∑ ν, Hi σ ν * (if ν = b then ∑ ρ, ∑ l, G ρ l σ * (Hi * P) l ρ else 0) =
        ∑ σ, Hi σ b * ∑ ρ, ∑ l, G ρ l σ * (Hi * P) l ρ := by
      simp [mul_ite, Finset.sum_ite_eq']
    rw [h]; ring
  have hU : ∑ σ, ∑ ν, Hi σ ν * (1 / 2 * (Hi * P).trace * G b σ ν) =
      1 / 2 * (Hi * P).trace * ∑ σ, ∑ ν, Hi σ ν * G b σ ν := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  rw [hS, hSA, hU, hT4]; ring

/-- `R₁ = h^{bl} Γ^m_{al} P^a_m`. -/
def R1 (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (b : Fin d) : ℝ :=
  ∑ l, Hi b l * ∑ a, ∑ m, G m a l * (Hi * P) a m

/-- Index algebra for the bracket of two Hamiltonian constraints (`a2_eq`). -/
lemma a2_eq (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (hHi : ∀ i j, Hi i j = Hi j i)
    (b : Fin d) :
    (∑ σ, Hi σ b * ∑ ρ, ∑ l, G ρ l σ * (Hi * P) l ρ) = R1 Hi P G b := by
  unfold R1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hHi σ b, Finset.sum_comm]

/-- Index algebra for the bracket of two Hamiltonian constraints (`a1_eq`). -/
lemma a1_eq (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (hHi : ∀ i j, Hi i j = Hi j i)
    (b : Fin d) :
    (∑ σ, ∑ ν, Hi σ ν * ∑ l, G b l σ * (Hi * P) l ν) = ∑ σ, ∑ ν, (Hi * P * Hi) σ ν * G b σ ν := by
  have h1 : ∀ σ ν, Hi σ ν * ∑ l, G b l σ * (Hi * P) l ν = ∑ l, Hi σ ν * (G b l σ * (Hi * P) l ν) := fun σ ν => by
    rw [Finset.mul_sum]
  have h2 : ∀ σ ν, (Hi * P * Hi) σ ν * G b σ ν = ∑ l, (Hi * P) σ l * Hi l ν * G b σ ν := fun σ ν => by
    rw [Matrix.mul_apply, Finset.sum_mul]
  simp only [h1, h2]
  -- LHS: Σ_{σ ν l} Hi σ ν G b l σ Pu l ν ; RHS: Σ_{σ ν l} Pu σ l Hi l ν G b σ ν
  calc ∑ σ, ∑ ν, ∑ l, Hi σ ν * (G b l σ * (Hi * P) l ν)
      = ∑ l, ∑ σ, ∑ ν, Hi σ ν * (G b l σ * (Hi * P) l ν) := sum3_cyc' _
    _ = ∑ σ, ∑ ν, ∑ l, (Hi * P) σ l * Hi l ν * G b σ ν := by
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by
          rw [hHi c e]; ring

/-- Index algebra for the bracket of two Hamiltonian constraints (`a3_eq`). -/
lemma a3_eq (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (hHi : ∀ i j, Hi i j = Hi j i)
    (hP : ∀ i j, P i j = P j i) (hG : ∀ i j k, G i j k = G i k j) (b : Fin d) :
    (∑ σ, ∑ ν, Hi σ ν * ∑ ρ, ∑ l, G ρ l σ * (Hi l b * P ρ ν)) = R1 Hi P G b := by
  have s1 : ∀ σ ν, Hi σ ν * ∑ ρ, ∑ l, G ρ l σ * (Hi l b * P ρ ν) =
      ∑ ρ, ∑ l, G ρ l σ * Hi l b * (Hi σ ν * P ρ ν) := fun σ ν => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  simp only [s1]
  have s2 : ∀ σ, ∑ ν, ∑ ρ, ∑ l, G ρ l σ * Hi l b * (Hi σ ν * P ρ ν) =
      ∑ ρ, ∑ l, G ρ l σ * Hi l b * (Hi * P) σ ρ := by
    intro σ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_sum, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl fun ν _ => by rw [hP ρ ν]
  simp only [s2]
  unfold R1
  calc ∑ σ, ∑ ρ, ∑ l, G ρ l σ * Hi l b * (Hi * P) σ ρ
      = ∑ l, ∑ σ, ∑ ρ, G ρ l σ * Hi l b * (Hi * P) σ ρ := by
        rw [Finset.sum_congr rfl fun σ _ => Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
        exact Finset.sum_comm
    _ = ∑ l, Hi b l * ∑ a, ∑ m, G m a l * (Hi * P) a m := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hG m l a, hHi b l]; ring

/-- Index algebra for the bracket of two Hamiltonian constraints (`ctr1`). -/
lemma ctr1 (Hi P : Matrix (Fin d) (Fin d) ℝ) (hP : ∀ i j, P i j = P j i) (σ m : Fin d) :
    ∑ ν, Hi σ ν * P m ν = (Hi * P) σ m := by
  rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun ν _ => by rw [hP m ν]

/-- Index algebra for the bracket of two Hamiltonian constraints (`ctr2`). -/
lemma ctr2 (Hi P : Matrix (Fin d) (Fin d) ℝ) (hHi : ∀ i j, Hi i j = Hi j i) (ν m : Fin d) :
    ∑ σ, Hi σ ν * P σ m = (Hi * P) ν m := by
  rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun σ _ => by rw [hHi σ ν]

/-- `R₂ = Pu^b_m U^m`. -/
def R2 (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (b : Fin d) : ℝ :=
  ∑ m, (Hi * P) b m * ∑ σ, ∑ ν, Hi σ ν * G m σ ν

/-- Index algebra for the bracket of two Hamiltonian constraints (`t_R1a`). -/
lemma t_R1a (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ)
    (hP : ∀ i j, P i j = P j i) (b : Fin d) :
    (∑ σ, ∑ ν, Hi σ ν * ∑ l, Hi b l * ∑ m, G m σ l * P m ν) = R1 Hi P G b := by
  unfold R1
  have s1 : ∀ σ ν, Hi σ ν * ∑ l, Hi b l * ∑ m, G m σ l * P m ν =
      ∑ l, ∑ m, Hi b l * (G m σ l * (Hi σ ν * P m ν)) := fun σ ν => by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring
  simp only [s1]
  have s2 : ∀ σ, ∑ ν, ∑ l, ∑ m, Hi b l * (G m σ l * (Hi σ ν * P m ν)) =
      ∑ l, ∑ m, Hi b l * (G m σ l * (Hi * P) σ m) := by
    intro σ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ctr1 Hi P hP σ m, Finset.mul_sum, Finset.mul_sum]
  simp only [s2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]

/-- Index algebra for the bracket of two Hamiltonian constraints (`t_R3`). -/
lemma t_R3 (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ)
    (hP : ∀ i j, P i j = P j i) (hG : ∀ i j k, G i j k = G i k j) (b : Fin d) :
    (∑ σ, ∑ ν, Hi σ ν * ∑ l, Hi b l * ∑ m, G m l σ * P m ν) = R1 Hi P G b := by
  rw [← t_R1a Hi P G hP b]
  exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => by simp only [hG _ _ σ]

/-- Index algebra for the bracket of two Hamiltonian constraints (`t_R4`). -/
lemma t_R4 (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ)
    (hHi : ∀ i j, Hi i j = Hi j i) (hP : ∀ i j, P i j = P j i) (hG : ∀ i j k, G i j k = G i k j) (b : Fin d) :
    (∑ σ, ∑ ν, Hi σ ν * ∑ l, Hi b l * ∑ m, G m l ν * P σ m) = R1 Hi P G b := by
  unfold R1
  rw [Finset.sum_comm]
  have s1 : ∀ ν σ, Hi σ ν * ∑ l, Hi b l * ∑ m, G m l ν * P σ m =
      ∑ l, ∑ m, Hi b l * (G m l ν * (Hi σ ν * P σ m)) := fun ν σ => by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring
  simp only [s1]
  have s2 : ∀ ν, ∑ σ, ∑ l, ∑ m, Hi b l * (G m l ν * (Hi σ ν * P σ m)) =
      ∑ l, ∑ m, Hi b l * (G m l ν * (Hi * P) ν m) := by
    intro ν
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ctr2 Hi P hHi ν m, Finset.mul_sum, Finset.mul_sum]
  simp only [s2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [hG m l a]

/-- Index algebra for the bracket of two Hamiltonian constraints (`t_R5`). -/
lemma t_R5 (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ)
    (hP : ∀ i j, P i j = P j i) (hG : ∀ i j k, G i j k = G i k j) (b : Fin d) :
    (∑ σ, Hi b σ * ∑ l, ∑ m, Hi l m * ∑ k, G k σ l * P k m) = R1 Hi P G b := by
  unfold R1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have s1 : ∀ l, ∑ m, Hi l m * ∑ k, G k σ l * P k m = ∑ k, G k σ l * (Hi * P) l k := by
    intro l
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← ctr1 Hi P hP l k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [s1]
  congr 1
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [hG k σ l]

/-- Index algebra for the bracket of two Hamiltonian constraints (`t_R6`). -/
lemma t_R6 (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (hHi : ∀ i j, Hi i j = Hi j i)
    (hP : ∀ i j, P i j = P j i) (hG : ∀ i j k, G i j k = G i k j) (b : Fin d) :
    (∑ σ, Hi b σ * ∑ l, ∑ m, Hi l m * ∑ k, G k σ m * P l k) = R1 Hi P G b := by
  unfold R1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have s1 : ∀ m, ∑ l, Hi l m * ∑ k, G k σ m * P l k = ∑ k, G k σ m * (Hi * P) m k := by
    intro m
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← ctr2 Hi P hHi m k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hP l k]; ring
  rw [Finset.sum_comm]
  have s2 : ∀ m, ∑ l, Hi l m * ∑ k, G k σ m * P l k = ∑ k, G k σ m * (Hi * P) m k := s1
  simp only [s2]
  congr 1
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [hG k σ l]

/-- Index algebra for the bracket of two Hamiltonian constraints (`t_R2`). -/
lemma t_R2 (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (b : Fin d) :
    (∑ σ, ∑ ν, Hi σ ν * ∑ l, Hi b l * ∑ m, G m σ ν * P l m) = R2 Hi P G b := by
  unfold R2
  have s1 : ∀ σ ν, Hi σ ν * ∑ l, Hi b l * ∑ m, G m σ ν * P l m =
      ∑ m, (Hi * P) b m * (Hi σ ν * G m σ ν) := fun σ ν => by
    simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [s1]
  rw [sum3_cyc']
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]

/-- Index algebra for the bracket of two Hamiltonian constraints (`t_last`). -/
lemma t_last (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ)
    (hG : ∀ i j k, G i j k = G i k j) (b : Fin d) :
    (∑ σ, Hi b σ * ∑ l, ∑ m, (Hi * P) l m * G m σ l) = R1 Hi P G b := by
  unfold R1
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by rw [hG m σ l]; ring

/-- The correction `Γ^m_{ai} P_{mj} + Γ^m_{aj} P_{im}` between a plain and a covariant derivative of `P`. -/
def corr (P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (a i j : Fin d) : ℝ :=
  ∑ m, (G m a i * P m j + G m a j * P i m)

/-- The divergence-type contraction of `X_{a,ij}` that appears in `w^b`. -/
def Tnc (Hi : Matrix (Fin d) (Fin d) ℝ) (X : Fin d → Fin d → Fin d → ℝ) (b : Fin d) : ℝ :=
  (∑ σ, ∑ ν, Hi σ ν * ∑ l, Hi b l * (X σ l ν - 1 / 2 * X l σ ν)) -
    1 / 2 * ∑ σ, Hi b σ * ∑ l, ∑ m, Hi l m * X σ l m

/-- Index algebra for the bracket of two Hamiltonian constraints (`Tcorr_closed`). -/
lemma Tcorr_closed (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ)
    (hHi : ∀ i j, Hi i j = Hi j i) (hP : ∀ i j, P i j = P j i) (hG : ∀ i j k, G i j k = G i k j) (b : Fin d) :
    Tnc Hi (corr P G) b = R2 Hi P G b - R1 Hi P G b := by
  unfold Tnc corr
  have eA : ∀ σ ν, Hi σ ν * ∑ l, Hi b l * (∑ m, (G m σ l * P m ν + G m σ ν * P l m) -
      1 / 2 * ∑ m, (G m l σ * P m ν + G m l ν * P σ m)) =
      Hi σ ν * ∑ l, Hi b l * ∑ m, G m σ l * P m ν + Hi σ ν * ∑ l, Hi b l * ∑ m, G m σ ν * P l m -
      1 / 2 * (Hi σ ν * ∑ l, Hi b l * ∑ m, G m l σ * P m ν) -
      1 / 2 * (Hi σ ν * ∑ l, Hi b l * ∑ m, G m l ν * P σ m) := by
    intro σ ν
    simp only [Finset.sum_add_distrib, mul_add, mul_sub, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring
  have eC : ∀ σ, Hi b σ * ∑ l, ∑ m, Hi l m * ∑ k, (G k σ l * P k m + G k σ m * P l k) =
      Hi b σ * ∑ l, ∑ m, Hi l m * ∑ k, G k σ l * P k m +
      Hi b σ * ∑ l, ∑ m, Hi l m * ∑ k, G k σ m * P l k := by
    intro σ
    rw [← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => eA σ ν,
    Finset.sum_congr rfl fun σ _ => eC σ]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [t_R1a Hi P G hP, t_R2 Hi P G, t_R3 Hi P G hP hG, t_R4 Hi P G hHi hP hG, t_R5 Hi P G hP hG,
    t_R6 Hi P G hHi hP hG]
  ring

/-- `wDer` of the inverse-metric change `D = -(Hi P Hi)`, in terms of `G = Γ(Hi, H1)`. -/
def wDG (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ) (b : Fin d) : ℝ :=
  (∑ σ, ∑ ν, ((-(Hi * P * Hi)) σ ν * G b σ ν + Hi σ ν * (-∑ m, (Hi * P) b m * G m σ ν))) -
    ∑ σ, ((-(Hi * P * Hi)) b σ * ∑ l, G l σ l + Hi b σ * ∑ l, (-∑ m, (Hi * P) l m * G m σ l))

/-- Index algebra for the bracket of two Hamiltonian constraints (`wDG_closed`). -/
lemma wDG_closed (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ)
    (hG : ∀ i j k, G i j k = G i k j) (b : Fin d) :
    wDG Hi P G b = -(∑ σ, ∑ ν, (Hi * P * Hi) σ ν * G b σ ν) - R2 Hi P G b +
      (∑ σ, (Hi * P * Hi) b σ * ∑ l, G l σ l) + R1 Hi P G b := by
  unfold wDG
  have h2 : ∑ σ, ∑ ν, Hi σ ν * ∑ m, (Hi * P) b m * G m σ ν = R2 Hi P G b := by
    unfold R2
    have : ∀ σ ν, Hi σ ν * ∑ m, (Hi * P) b m * G m σ ν = ∑ m, (Hi * P) b m * (Hi σ ν * G m σ ν) := fun σ ν => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    simp only [this]
    rw [sum3_cyc']
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by rw [Finset.mul_sum]
  have h4 : ∑ σ, Hi b σ * ∑ l, ∑ m, (Hi * P) l m * G m σ l = R1 Hi P G b := t_last Hi P G hG b
  simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [h2, h4]
  ring

/-- Index algebra for the bracket of two Hamiltonian constraints (`Pup_symm`). -/
lemma Pup_symm (Hi P : Matrix (Fin d) (Fin d) ℝ) (hHi : ∀ i j, Hi i j = Hi j i) (hP : ∀ i j, P i j = P j i)
    (i j : Fin d) : (Hi * P * Hi) i j = (Hi * P * Hi) j i := by
  have hHT : Hiᵀ = Hi := Matrix.ext fun a b => (hHi b a)
  have hPT : Pᵀ = P := Matrix.ext fun a b => (hP b a)
  have := congrFun (congrFun (show (Hi * P * Hi)ᵀ = Hi * P * Hi by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hHT, hPT, Matrix.mul_assoc]) j) i
  simpa [Matrix.transpose_apply] using this

/-- **Stage 1**: `-Ψ_b + Θ_a^b-part` equals the plain-minus-covariant correction. -/
lemma stage1 (Hi P : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → Fin d → ℝ)
    (hHi : ∀ i j, Hi i j = Hi j i) (hP : ∀ i j, P i j = P j i) (hG : ∀ i j k, G i j k = G i k j) (b : Fin d) :
    -LbG Hi P G b - 1 / 2 * (Hi * P).trace *
        ((∑ σ, ∑ ν, Hi σ ν * G b σ ν) - ∑ σ, Hi b σ * ∑ l, G l σ l) - wDG Hi P G b =
      Tnc Hi (corr P G) b := by
  rw [LbG_closed Hi P G hHi hP b, wDG_closed Hi P G hG b, Tcorr_closed Hi P G hHi hP hG b,
    a1_eq Hi P G hHi b, a2_eq Hi P G hHi b, a3_eq Hi P G hHi hP hG b]
  have s1 : ∑ ρ, ((Hi * P * Hi) ρ b - 1 / 2 * Hi ρ b * (Hi * P).trace) * ∑ l, G l ρ l =
      ∑ σ, (Hi * P * Hi) b σ * ∑ l, G l σ l - 1 / 2 * (Hi * P).trace * ∑ σ, Hi b σ * ∑ l, G l σ l := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun ρ _ => by rw [Pup_symm Hi P hHi hP ρ b]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ρ _ => by rw [hHi ρ b]; ring
  rw [s1]
  ring

/-- Index algebra for the bracket of two Hamiltonian constraints (`contr_full`). -/
lemma contr_full (Hi N : Matrix (Fin d) (Fin d) ℝ) :
    ∑ σ, ∑ ν, Hi σ ν * N σ ν = (Hi * Nᵀ).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]

/-- Index algebra for the bracket of two Hamiltonian constraints (`Tnc_split`). -/
lemma Tnc_split (Hi : Matrix (Fin d) (Fin d) ℝ) (X : Fin d → Fin d → Fin d → ℝ) (b : Fin d) :
    Tnc Hi X b = (∑ σ, ∑ ν, Hi σ ν * ∑ l, Hi b l * X σ l ν) -
      1 / 2 * (∑ σ, ∑ ν, Hi σ ν * ∑ l, Hi b l * X l σ ν) -
      1 / 2 * ∑ σ, Hi b σ * ∑ l, ∑ m, Hi l m * X σ l m := by
  unfold Tnc
  have : ∀ σ ν, Hi σ ν * ∑ l, Hi b l * (X σ l ν - 1 / 2 * X l σ ν) =
      Hi σ ν * ∑ l, Hi b l * X σ l ν - 1 / 2 * (Hi σ ν * ∑ l, Hi b l * X l σ ν) := fun σ ν => by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Index algebra for the bracket of two Hamiltonian constraints (`sandwich`). -/
lemma sandwich (Hi h M : Matrix (Fin d) (Fin d) ℝ) (hHh : Hi * h = 1) (hhH : h * Hi = 1) :
    Hi * (h * M * h) * Hi = M := by
  have : Hi * (h * M * h) * Hi = (Hi * h) * M * (h * Hi) := by simp only [Matrix.mul_assoc]
  rw [this, hHh, hhH, Matrix.one_mul, Matrix.mul_one]

/-- The tensor `Y_a = 2 h Dπ_a h − c (tr Dπ_a h) h`. -/
def Ymat (h : Matrix (Fin d) (Fin d) ℝ) (Dπ : Fin d → Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (a : Fin d) :
    Matrix (Fin d) (Fin d) ℝ :=
  (2 : ℝ) • (h * Dπ a * h) - (c * (Dπ a * h).trace) • h

/-- Index algebra for the bracket of two Hamiltonian constraints (`Ymat_trace`). -/
lemma Ymat_trace (Hi h : Matrix (Fin d) (Fin d) ℝ) (Dπ : Fin d → Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (hHh : Hi * h = 1) (hsym : hᵀ = h) (a : Fin d) :
    ∑ l, ∑ m, Hi l m * Ymat h Dπ c a l m = (2 - c * d) * (Dπ a * h).trace := by
  rw [contr_full]
  unfold Ymat
  have e1 : (((2 : ℝ) • (h * Dπ a * h) - (c * (Dπ a * h).trace) • h)ᵀ) =
      (2 : ℝ) • (h * (Dπ a)ᵀ * h) - (c * (Dπ a * h).trace) • h := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_mul, hsym]
    simp only [Matrix.mul_assoc]
  rw [e1, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul]
  have e2 : Hi * (h * (Dπ a)ᵀ * h) = (Hi * h) * (Dπ a)ᵀ * h := by simp only [Matrix.mul_assoc]
  rw [e2, hHh, Matrix.one_mul, Matrix.trace_one]
  have e3 : ((Dπ a)ᵀ * h).trace = (Dπ a * h).trace := by
    calc ((Dπ a)ᵀ * h).trace = (((Dπ a)ᵀ * h)ᵀ).trace := (Matrix.trace_transpose _).symm
      _ = (h * Dπ a).trace := by rw [Matrix.transpose_mul, hsym, Matrix.transpose_transpose]
      _ = (Dπ a * h).trace := Matrix.trace_mul_comm _ _
  rw [e3]
  simp
  ring

/-- **Stage 2b**: the contraction of `Y_a = 2 h Dπ_a h − c (tr Dπ_a h) h` is twice the divergence of `Dπ`. -/
lemma Tnc_Ymat (Hi h : Matrix (Fin d) (Fin d) ℝ) (Dπ : Fin d → Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (hHs : Hiᵀ = Hi) (hHh : Hi * h = 1) (hhH : h * Hi = 1) (hsym : hᵀ = h) (hc : c * ((d : ℝ) - 1) = 2)
    (b : Fin d) :
    Tnc Hi (fun a i j => Ymat h Dπ c a i j) b = 2 * ∑ σ, Dπ σ b σ := by
  rw [Tnc_split]
  have hA : ∀ σ, ∑ ν, Hi σ ν * ∑ l, Hi b l * Ymat h Dπ c σ l ν =
      2 * Dπ σ b σ - c * (Dπ σ * h).trace * Hi b σ := by
    intro σ
    have e1 : ∀ ν, Hi σ ν * ∑ l, Hi b l * Ymat h Dπ c σ l ν = (Hi * Ymat h Dπ c σ) b ν * Hiᵀ ν σ := by
      intro ν
      rw [Matrix.mul_apply, Matrix.transpose_apply, mul_comm]
    simp only [e1]
    rw [← Matrix.mul_apply (M := Hi * Ymat h Dπ c σ) (N := Hiᵀ), hHs]
    have : Hi * Ymat h Dπ c σ * Hi = (2 : ℝ) • Dπ σ - (c * (Dπ σ * h).trace) • Hi := by
      unfold Ymat
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
        sandwich Hi h _ hHh hhH]
      have : Hi * h * Hi = Hi := by rw [hHh, Matrix.one_mul]
      rw [this]
    rw [this]
    simp [Matrix.sub_apply]
  have hBC : ∀ a, ∑ σ, ∑ ν, Hi σ ν * Ymat h Dπ c a σ ν = (2 - c * d) * (Dπ a * h).trace := fun a =>
    Ymat_trace Hi h Dπ c hHh hsym a
  have hB : ∑ σ, ∑ ν, Hi σ ν * ∑ l, Hi b l * Ymat h Dπ c l σ ν =
      ∑ l, Hi b l * ((2 - c * d) * (Dπ l * h).trace) := by
    have : ∀ σ ν, Hi σ ν * ∑ l, Hi b l * Ymat h Dπ c l σ ν = ∑ l, Hi b l * (Hi σ ν * Ymat h Dπ c l σ ν) := by
      intro σ ν; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    simp only [this]
    rw [sum3_cyc']
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hBC l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
  have hC : ∑ σ, Hi b σ * ∑ l, ∑ m, Hi l m * Ymat h Dπ c σ l m =
      ∑ σ, Hi b σ * ((2 - c * d) * (Dπ σ * h).trace) :=
    Finset.sum_congr rfl fun σ _ => by rw [Ymat_trace Hi h Dπ c hHh hsym σ]
  rw [Finset.sum_congr rfl fun σ _ => hA σ, hB, hC]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  linear_combination ((Dπ σ * h).trace * Hi b σ) * hc

/-- `Tnc` is additive. -/
lemma Tnc_sub (Hi : Matrix (Fin d) (Fin d) ℝ) (X Y : Fin d → Fin d → Fin d → ℝ) (b : Fin d) :
    Tnc Hi (fun a i j => X a i j - Y a i j) b = Tnc Hi X b - Tnc Hi Y b := by
  rw [Tnc_split, Tnc_split, Tnc_split]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- `Tnc` is homogeneous. -/
lemma Tnc_smul (Hi : Matrix (Fin d) (Fin d) ℝ) (X : Fin d → Fin d → Fin d → ℝ) (k : ℝ) (b : Fin d) :
    Tnc Hi (fun a i j => k * X a i j) b = k * Tnc Hi X b := by
  unfold Tnc
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  have S : ∀ f g : Fin d → Fin d → Fin d → ℝ, (∀ x y i, f x y i = g x y i) →
      (∑ x, ∑ y, ∑ i, f x y i) = ∑ x, ∑ y, ∑ i, g x y i := fun f g h =>
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => h x y i
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;> exact S _ _ fun x y i => by ring

end Lightlike.Canonical

end
