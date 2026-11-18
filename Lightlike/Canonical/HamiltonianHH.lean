import Mathlib
import Lightlike.Canonical.HamiltonianFirstOrder

/-!
# The bracket of two smeared Hamiltonian constraints: the algebra of the first-order form

The structure of `{H[N], H[M]}` when the variation is `M · P` with `P` the `π`-gradient: the terms without
derivatives of the lapses cancel, the cross terms cancel by the symmetry of the coefficient of `∂ h` in `√h w^ρ`,
and what is left is `Σ_b (N ∂_b M − M ∂_b N) W^b`.
-/

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- **The antisymmetrization**: the terms without derivatives of the lapses cancel, and so do the cross terms when
the coefficient `Θb ρ b` is symmetric. -/
lemma B_algebra (N0 M0 : ℝ) (dN dM : Fin d → ℝ) (Ψa Ψd : ℝ) (Ψb Θa Θd : Fin d → ℝ)
    (Θb : Fin d → Fin d → ℝ) (hsym : ∀ ρ b, Θb ρ b = Θb b ρ) :
    (N0 * (M0 * Ψa + ∑ b, dM b * Ψb b + M0 * Ψd) +
        ∑ ρ, dN ρ * (M0 * Θa ρ + ∑ b, dM b * Θb ρ b + M0 * Θd ρ)) -
      (M0 * (N0 * Ψa + ∑ b, dN b * Ψb b + N0 * Ψd) +
        ∑ ρ, dM ρ * (N0 * Θa ρ + ∑ b, dN b * Θb ρ b + N0 * Θd ρ)) =
    ∑ b, (N0 * dM b - M0 * dN b) * (Ψb b - Θa b - Θd b) := by
  have hcross : ∑ ρ, ∑ b, dN ρ * dM b * Θb ρ b = ∑ ρ, ∑ b, dM ρ * dN b * Θb ρ b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsym b ρ]; ring
  have e1 : ∑ ρ, dN ρ * (M0 * Θa ρ + ∑ b, dM b * Θb ρ b + M0 * Θd ρ) =
      M0 * ∑ ρ, dN ρ * Θa ρ + (∑ ρ, ∑ b, dN ρ * dM b * Θb ρ b) + M0 * ∑ ρ, dN ρ * Θd ρ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [mul_add, mul_add, Finset.mul_sum]
    have : ∑ b, dN ρ * (dM b * Θb ρ b) = ∑ b, dN ρ * dM b * Θb ρ b :=
      Finset.sum_congr rfl fun b _ => by ring
    rw [this]; ring
  have e2 : ∑ ρ, dM ρ * (N0 * Θa ρ + ∑ b, dN b * Θb ρ b + N0 * Θd ρ) =
      N0 * ∑ ρ, dM ρ * Θa ρ + (∑ ρ, ∑ b, dM ρ * dN b * Θb ρ b) + N0 * ∑ ρ, dM ρ * Θd ρ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [mul_add, mul_add, Finset.mul_sum]
    have : ∑ b, dM ρ * (dN b * Θb ρ b) = ∑ b, dM ρ * dN b * Θb ρ b :=
      Finset.sum_congr rfl fun b _ => by ring
    rw [this]; ring
  have e3 : N0 * (M0 * Ψa + ∑ b, dM b * Ψb b + M0 * Ψd) = N0 * M0 * Ψa + N0 * ∑ b, dM b * Ψb b + N0 * M0 * Ψd := by ring
  have e4 : M0 * (N0 * Ψa + ∑ b, dN b * Ψb b + N0 * Ψd) = M0 * N0 * Ψa + M0 * ∑ b, dN b * Ψb b + M0 * N0 * Ψd := by ring
  have rhs : ∑ b, (N0 * dM b - M0 * dN b) * (Ψb b - Θa b - Θd b) =
      N0 * ∑ b, dM b * Ψb b - M0 * ∑ b, dN b * Ψb b - N0 * ∑ b, dM b * Θa b + M0 * ∑ b, dN b * Θa b -
        N0 * ∑ b, dM b * Θd b + M0 * ∑ b, dN b * Θd b := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [e1, e2, e3, e4, rhs]
  linear_combination hcross

/-- `δH[N]/δπ = N · δH[1]/δπ`. -/
lemma hamiltonianPiGradient_smul (N : (Fin d → ℝ) → ℝ) (h π : TensorField d) (x : Fin d → ℝ) :
    hamiltonianPiGradient N h π x = N x • hamiltonianPiGradient (fun _ => (1 : ℝ)) h π x := by
  unfold hamiltonianPiGradient
  rw [← Matrix.transpose_smul, smul_smul, mul_one_div]

/-- The unit `π`-gradient of the Hamiltonian constraint at `x`. -/
abbrev Pm (h π : TensorField d) (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  hamiltonianPiGradient (fun _ => (1 : ℝ)) h π x

/-- The three directions of the variation `M · P`: the `h`-direction `(P, 0)`. -/
def Va (h π : TensorField d) (x : Fin d → ℝ) : Arr d × H1arr d :=
  (((fun a b => Pm h π x a b, fun _ _ => 0) : Arr d), fun _ _ _ => 0)

/-- The `∂_b h`-direction `δ_b ⊗ P`. -/
def Vb (h π : TensorField d) (x : Fin d → ℝ) (b : Fin d) : Arr d × H1arr d :=
  (((fun _ _ => 0, fun _ _ => 0) : Arr d), fun a i j => if a = b then Pm h π x i j else 0)

/-- The `∂ h`-direction `∂P`. -/
def Vd (h π : TensorField d) (x : Fin d → ℝ) : Arr d × H1arr d :=
  (((fun _ _ => 0, fun _ _ => 0) : Arr d), fun a i j => Lightlike.pd a (fun y => Pm h π y i j) x)

lemma V1_split {M : (Fin d → ℝ) → ℝ} (hM : ContDiff ℝ ∞ M) {h π : TensorField d}
    (hP : SmoothTensor (hamiltonianPiGradient (fun _ => (1 : ℝ)) h π)) (x : Fin d → ℝ) :
    V1 (hamiltonianPiGradient M h π) x = ((0 : ℝ), (0 : Fin d → ℝ),
      (M x • Va h π x + ∑ b, Lightlike.pd b M x • Vb h π x b + M x • Vd h π x)) := by
  have hk : ∀ y i j, hamiltonianPiGradient M h π y i j = M y * Pm h π y i j := by
    intro y i j
    rw [hamiltonianPiGradient_smul]
    simp
  unfold V1
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext (Prod.ext ?_ ?_) ?_))
  · funext a b; simp [hk, Va, Vb, Vd, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  · funext a b; simp [Va, Vb, Vd, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  · funext j a b
    have hpd : Lightlike.pd j (fun y => hamiltonianPiGradient M h π y a b) x =
        Lightlike.pd j M x * Pm h π x a b + M x * Lightlike.pd j (fun y => Pm h π y a b) x := by
      have e : (fun y => hamiltonianPiGradient M h π y a b) = fun y => M y * Pm h π y a b :=
        funext fun y => hk y a b
      rw [e]
      exact Lightlike.pd_mul (diff_of_smooth hM x) (diff_of_smooth (hP a b) x) j
    show Lightlike.pd j (fun y => hamiltonianPiGradient M h π y a b) x = _
    rw [hpd]
    simp [Va, Vb, Vd, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.add_apply, Pi.smul_apply]

/-- The jet data `(h, π, ∂h)` at `x`. -/
abbrev Zthree (h π : TensorField d) (x : Fin d → ℝ) : Arr d × H1arr d :=
  (((fun a b => h x a b, fun a b => π x a b) : Arr d), jet1 h x)

/-- **The derivative of the first-order density along `M · P`**, split into the three directions. -/
lemma first_deriv_split {N M : (Fin d → ℝ) → ℝ} (hM : ContDiff ℝ ∞ M) {h π : TensorField d}
    (hP : SmoothTensor (hamiltonianPiGradient (fun _ => (1 : ℝ)) h π)) {x : Fin d → ℝ}
    (hdet : 0 < (h x).det) :
    fderiv ℝ (Phi1 (1 / ((d : ℝ) - 1))) (Z1 N h π x) (V1 (hamiltonianPiGradient M h π) x) =
      N x * (M x * fderiv ℝ (Psi (1 / ((d : ℝ) - 1))) (Zthree h π x) (Va h π x) +
          ∑ b, Lightlike.pd b M x * fderiv ℝ (Psi (1 / ((d : ℝ) - 1))) (Zthree h π x) (Vb h π x b) +
          M x * fderiv ℝ (Psi (1 / ((d : ℝ) - 1))) (Zthree h π x) (Vd h π x)) +
        ∑ ρ, Lightlike.pd ρ N x * (M x * fderiv ℝ (Theta ρ) (Zthree h π x) (Va h π x) +
          ∑ b, Lightlike.pd b M x * fderiv ℝ (Theta ρ) (Zthree h π x) (Vb h π x b) +
          M x * fderiv ℝ (Theta ρ) (Zthree h π x) (Vd h π x)) := by
  rw [V1_split hM hP x]
  have := fderiv_Phi1_third (1 / ((d : ℝ) - 1)) (q := Z1 N h π x) (by show 0 < (h x).det; exact hdet)
    (M x • Va h π x + ∑ b, Lightlike.pd b M x • Vb h π x b + M x • Vd h π x)
  rw [this]
  simp only [map_add, map_smul, map_sum, smul_eq_mul]
  rfl

end Lightlike.Canonical

end
