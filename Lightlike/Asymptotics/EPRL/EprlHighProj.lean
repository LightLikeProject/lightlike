import Lightlike.Asymptotics.EPRL.EprlHighMap
import Lightlike.Asymptotics.EPRL.HomForm

/-!
# `projSpin4` is the Haar average of the conjugation action of `Spin(4)`

The orthogonal projection `projSpin4` onto the Spin(4) intertwiners `ι⁺_x ⊗ ι⁻_y` is the Haar average
`Q ↦ ∫ G, D(G) Q D'(G)ᴴ` of the conjugation action of `Spin(4) = SU(2) × SU(2)` on matrices from the last
two (self-dual and anti-self-dual) legs to the first two (`projSpin4_eq_integral`). The integral is
the entrywise integral `matInt4` with the Haar probability measure `haarSpin4`. The average is a
Spin(4) intertwiner by the translation invariance of the Haar measure, it has the same pairing with
every basis intertwiner as `Q`, and a Spin(4) intertwiner equals the expansion in the basis
(`eq_sum_ivec4`).

## Main results

* `matInt4`, `matInt4_mul_left`, `matInt4_mul_right`, `hsInner_matInt4`, `integral_mul_left4`: the
  entrywise integral and the rules used.
* `act4`, `act4_mul`, `act4_unitary`: the action of `Spin(4)` on the legs.
* `hsInner_conj_of_intertwines`: the pairing with an intertwiner is invariant under conjugation.
* `projSpin4_eq_integral`: `projSpin4 Q = ∫ D(G) Q D'(G)ᴴ dG`.

## References

* Lightlike/Spin4/Fusion.lean (`projSpin4`, `eq_sum_ivec4`).
-/

open Matrix Finset MeasureTheory
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology SU2 :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance : IsProbabilityMeasure haarSpin4 := by unfold haarSpin4; infer_instance

/-- Left translation preserves the Haar measure of `Spin(4)`. -/
lemma measurePreserving_mul_left4 (h : Spin4) :
    MeasurePreserving (fun G : Spin4 => h * G) haarSpin4 haarSpin4 := by
  have h1 : MeasurePreserving (fun x : SU2 => h.1 * x) haarSU2 haarSU2 :=
    measurePreserving_mul_left haarSU2 h.1
  have h2 : MeasurePreserving (fun x : SU2 => h.2 * x) haarSU2 haarSU2 :=
    measurePreserving_mul_left haarSU2 h.2
  exact h1.prod h2

/-- An integral of matrices over `Spin(4)`, entrywise, with the Haar probability measure. -/
noncomputable def matInt4 {ι κ : Type*} (F : Spin4 → Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  Matrix.of fun i j => ∫ G, F G i j ∂haarSpin4

lemma integrable_of_continuous4 {f : Spin4 → ℂ} (hf : Continuous f) : Integrable f haarSpin4 :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Left translation does not change an integral over `Spin(4)`. -/
lemma integral_mul_left4 (h : Spin4) (f : Spin4 → ℂ) :
    ∫ G, f (h * G) ∂haarSpin4 = ∫ G, f G ∂haarSpin4 :=
  (measurePreserving_mul_left4 h).integral_comp (Homeomorph.mulLeft h).measurableEmbedding f

lemma matInt4_apply {ι κ : Type*} (F : Spin4 → Matrix ι κ ℂ) (i : ι) (j : κ) :
    matInt4 F i j = ∫ G, F G i j ∂haarSpin4 := rfl


section Lin

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

lemma matInt4_mul_left (A : Matrix μ ι ℂ) (F : Spin4 → Matrix ι κ ℂ)
    (hF : ∀ i j, Continuous fun G => F G i j) :
    A * matInt4 F = matInt4 fun G => A * F G := by
  ext i j
  simp only [Matrix.mul_apply, matInt4_apply]
  rw [integral_finsetSum _ fun k _ => integrable_of_continuous4
    (f := fun G => A i k * F G k j) (continuous_const.mul (hF k j))]
  exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm

lemma matInt4_mul_right (A : Matrix κ μ ℂ) (F : Spin4 → Matrix ι κ ℂ)
    (hF : ∀ i j, Continuous fun G => F G i j) :
    matInt4 F * A = matInt4 fun G => F G * A := by
  ext i j
  simp only [Matrix.mul_apply, matInt4_apply]
  rw [integral_finsetSum _ fun k _ => integrable_of_continuous4
    (f := fun G => F G i k * A k j) ((hF i k).mul continuous_const)]
  exact Finset.sum_congr rfl fun k _ => (integral_mul_const _ _).symm

lemma hsInner_matInt4 (R : Matrix ι κ ℂ) (F : Spin4 → Matrix ι κ ℂ)
    (hF : ∀ i j, Continuous fun G => F G i j) :
    hsInner R (matInt4 F) = ∫ G, hsInner R (F G) ∂haarSpin4 := by
  unfold hsInner
  simp only [matInt4_apply]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => integrable_of_continuous4
      (f := fun G => star (R i j) * F G i j) (continuous_const.mul (hF i j))]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
  · exact integrable_finsetSum _ fun j _ => integrable_of_continuous4
      (f := fun G => star (R i j) * F G i j) (continuous_const.mul (hF i j))

end Lin

section Proj

variable {n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ : ℕ}

/-- The action of `Spin(4)` on `(V_{n₁} ⊗ V_{n₂}) ⊗ (V_{m₁} ⊗ V_{m₂})`. -/
noncomputable abbrev act4 (n₁ n₂ m₁ m₂ : ℕ) (G : Spin4) :
    Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₁ n₂ × Idx m₁ m₂) ℂ :=
  pairMat n₁ n₂ G.1 ⊗ₖ pairMat m₁ m₂ G.2

lemma continuous_act4 (n₁ n₂ m₁ m₂ : ℕ) (i j) :
    Continuous fun G : Spin4 => act4 n₁ n₂ m₁ m₂ G i j := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := i
  obtain ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := j
  simp only [act4, pairMat, kroneckerMap_apply]
  have h1 : ∀ (n : ℕ) (i j : Fin (n + 1)), Continuous fun G : Spin4 =>
      spinMat n (G.1 : Matrix (Fin 2) (Fin 2) ℂ) i j := fun n i j =>
    (continuous_spinMat_apply n i j).comp continuous_fst
  have h2 : ∀ (n : ℕ) (i j : Fin (n + 1)), Continuous fun G : Spin4 =>
      spinMat n (G.2 : Matrix (Fin 2) (Fin 2) ℂ) i j := fun n i j =>
    (continuous_spinMat_apply n i j).comp continuous_snd
  exact (((h1 _ _ _).mul (h1 _ _ _)).mul ((h2 _ _ _).mul (h2 _ _ _)))

lemma act4_mul (n₁ n₂ m₁ m₂ : ℕ) (h G : Spin4) :
    act4 n₁ n₂ m₁ m₂ (h * G) = act4 n₁ n₂ m₁ m₂ h * act4 n₁ n₂ m₁ m₂ G := by
  unfold act4 pairMat
  simp only [Prod.fst_mul, Prod.snd_mul, Submonoid.coe_mul, Subgroup.coe_mul, spinMat_mul,
    Matrix.mul_kronecker_mul]

lemma act4_unitary (n₁ n₂ m₁ m₂ : ℕ) (G : Spin4) :
    (act4 n₁ n₂ m₁ m₂ G)ᴴ * act4 n₁ n₂ m₁ m₂ G = 1 := by
  unfold act4
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, pair_conjTranspose_mul_self,
    pair_conjTranspose_mul_self, Matrix.one_kronecker_one]

lemma continuous_act4_matrix (n₁ n₂ m₁ m₂ : ℕ) : Continuous fun G : Spin4 => act4 n₁ n₂ m₁ m₂ G :=
  continuous_matrix fun i j => continuous_act4 n₁ n₂ m₁ m₂ i j

/-- The Hilbert–Schmidt pairing with a matrix that intertwines two unitaries is invariant under
conjugation: `⟨R, A T Bᴴ⟩ = ⟨R, T⟩` when `Aᴴ A = 1` and `A R = R B`. -/
lemma hsInner_conj_of_intertwines {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} {R : Matrix ι κ ℂ}
    (hAA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) (hRg : A * R = R * B) (T : Matrix ι κ ℂ) :
    hsInner R (A * T * Bᴴ) = hsInner R T := by
  have hBB : B * Bᴴ = 1 := mul_eq_one_comm.mp hB
  have key : Aᴴ * R * B = R := by
    calc Aᴴ * R * B = Aᴴ * (R * B) := by rw [Matrix.mul_assoc]
      _ = Aᴴ * (A * R) := by rw [hRg]
      _ = R := by rw [← Matrix.mul_assoc, hAA, Matrix.one_mul]
  rw [hsInner_eq_trace, hsInner_eq_trace]
  calc Matrix.trace (Rᴴ * (A * T * Bᴴ)) = Matrix.trace (Bᴴ * (Rᴴ * (A * T))) := by
        rw [show Rᴴ * (A * T * Bᴴ) = (Rᴴ * (A * T)) * Bᴴ by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
    _ = Matrix.trace ((Aᴴ * R * B)ᴴ * T) := by
        have : Bᴴ * (Rᴴ * (A * T)) = (Aᴴ * R * B)ᴴ * T := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
        rw [this]
    _ = Matrix.trace (Rᴴ * T) := by rw [key]

/-- **`projSpin4` is the Haar average of the conjugation action of `Spin(4)`.** -/
theorem projSpin4_eq_integral (Q : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ) :
    projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q =
      matInt4 fun G => act4 n₁ n₂ m₁ m₂ G * Q * (act4 n₃ n₄ m₃ m₄ G)ᴴ := by
  set F : Spin4 → Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ :=
    fun G => act4 n₁ n₂ m₁ m₂ G * Q * (act4 n₃ n₄ m₃ m₄ G)ᴴ with hF
  have hFc : ∀ i j, Continuous fun G => F G i j := fun i j =>
    (((continuous_act4_matrix n₁ n₂ m₁ m₂).matrix_mul continuous_const).matrix_mul
      (continuous_act4_matrix n₃ n₄ m₃ m₄).matrix_conjTranspose).matrix_elem i j
  have hFh : ∀ h G, F (h * G) * act4 n₃ n₄ m₃ m₄ h = act4 n₁ n₂ m₁ m₂ h * F G := by
    intro h G
    simp only [hF, act4_mul, Matrix.conjTranspose_mul]
    have hu := act4_unitary n₃ n₄ m₃ m₄ h
    calc _ = act4 n₁ n₂ m₁ m₂ h * act4 n₁ n₂ m₁ m₂ G * Q * ((act4 n₃ n₄ m₃ m₄ G)ᴴ *
          ((act4 n₃ n₄ m₃ m₄ h)ᴴ * act4 n₃ n₄ m₃ m₄ h)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hinv : ∀ h, act4 n₁ n₂ m₁ m₂ h * matInt4 F = matInt4 F * act4 n₃ n₄ m₃ m₄ h := by
    intro h
    rw [matInt4_mul_left _ _ hFc, matInt4_mul_right _ _ hFc]
    ext i j
    simp only [matInt4_apply]
    rw [← integral_mul_left4 h (fun G => (F G * act4 n₃ n₄ m₃ m₄ h) i j)]
    refine integral_congr_ae (ae_of_all _ fun G => ?_)
    have := congrFun (congrFun (hFh h G) i) j
    exact this.symm
  have hA : IsSpin4Intertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (matInt4 F) := fun h => hinv h
  have hcoef : ∀ p ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄,
      hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2) (matInt4 F) =
        hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2) Q := by
    intro p hp
    rw [hsInner_matInt4 _ _ hFc]
    have hI := ivec4_isSpin4Intertwiner hp
    have : ∀ G, hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2) (F G) =
        hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2) Q := fun G =>
      hsInner_conj_of_intertwines (act4_unitary _ _ _ _ G) (act4_unitary _ _ _ _ G) (hI G) Q
    simp only [this]
    simp
  conv_rhs => rw [eq_sum_ivec4 hA]
  unfold projSpin4
  exact Finset.sum_congr rfl fun p hp => by rw [hcoef p hp]

end Proj

end Lightlike.Asymptotics.EPRL
