import Lightlike.Spacetime.RaychaudhuriAlgebra
import Lightlike.Spacetime.RaychaudhuriSplit
import Lightlike.Spacetime.ContractedBianchi

/-!
# The Raychaudhuri identity for a geodesic field in coordinates (G1-009)

Kar and SenGupta (gr-qc/0611123), eq. (12): along a timelike geodesic congruence `v`,
`dΘ/dλ = -Θ²/3 - σ² + ω² - Rₐᵦ vᵃ vᵇ`, which is the trace of the identity `vᶜ ∇_c (∇_b vᵃ)`; eq. (1) splits `∇_b vᵃ` into
expansion, shear and rotation. Here, for a coordinate metric `g` on an open `U ⊆ ℝⁿ` and a smooth field `v` that is
geodesic on `U` (`vᶜ ∇_c vᵈ = 0`), with `∇_b vᵃ = ∂_b vᵃ + Γᵃ_{bc} vᶜ` (`covD`) and the expansion `Θ = ∇ₐ vᵃ`
(`expansion`): **`vᶜ ∂_c Θ = -(∇_b vᵃ)(∇ₐ vᵇ) - R_{σν} vᵠ vᵛ`** (`raychaudhuri_coord`), in the library's `ricci`
convention. No normalisation of `v` is used. The index computation is `Raychaudhuri.raychaudhuri_algebra`
(fable1's, `RaychaudhuriAlgebra.lean`).
-/

open Filter Topology
open scoped ContDiff Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- `∇_b vᵃ = ∂_b vᵃ + Σ_c Γᵃ_{bc} vᶜ`. -/
def covD (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (a b : Fin n)
    (y : Fin n → ℝ) : ℝ :=
  pd b (fun z => v z a) y + ∑ c, christoffel g a b c y * v y c

/-- The expansion `Θ = ∇ₐ vᵃ`. -/
def expansion (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ a, covD g v a a y

/-- The matrix `Mᵃ_b = ∇_b vᵃ` at `x`. -/
def covDMat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => covD g v a b x

/-- The shear `σ_ab = ½(∇_b v_a + ∇_a v_b) - Θ h_ab/(n-1)`, `h = g + v♭ ⊗ v♭` (Kar–SenGupta (1)), indices lowered with
`g`: the matrix `L = g M` has entries `L_ab = ∇_b v_a`. -/
def shear (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (g x * covDMat g v x + (g x * covDMat g v x)ᵀ) -
    (expansion g v x / ((n : ℝ) - 1)) • (g x + Matrix.vecMulVec (g x *ᵥ v x) (g x *ᵥ v x))

/-- The rotation `ω_ab = ½(∇_b v_a - ∇_a v_b)` (Kar–SenGupta (1)). -/
def rotation (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (g x * covDMat g v x - (g x * covDMat g v x)ᵀ)

section

variable {v : (Fin n → ℝ) → Fin n → ℝ} (hg : IsCoordMetric g U) (hv : ∀ a, ContDiffOn ℝ ∞ (fun y => v y a) U)
include hg hv

/-- `∇_b vᵃ` is differentiable on `U`. -/
theorem differentiableAt_covD {y : Fin n → ℝ} (hy : y ∈ U) (a b : Fin n) :
    DifferentiableAt ℝ (covD g v a b) y := by
  unfold covD
  refine (differentiableAt_of_contDiffOn (contDiffOn_pd (hv a) hg.isOpen b) hg.isOpen hy).add ?_
  refine DifferentiableAt.fun_sum fun c _ => ?_
  exact (differentiableAt_of_contDiffOn (hg.contDiffOn_christoffel a b c) hg.isOpen hy).mul
    (differentiableAt_of_contDiffOn (hv c) hg.isOpen hy)

/-- The derivative of `∇_b vᵃ`. -/
theorem pd_covD {y : Fin n → ℝ} (hy : y ∈ U) (a b c : Fin n) :
    pd c (covD g v a b) y = pd c (pd b fun z => v z a) y +
      ∑ d, (pd c (christoffel g a b d) y * v y d + christoffel g a b d y * pd c (fun z => v z d) y) := by
  have h1 := differentiableAt_of_contDiffOn (contDiffOn_pd (hv a) hg.isOpen b) hg.isOpen hy
  have hΓ := fun d => differentiableAt_of_contDiffOn (hg.contDiffOn_christoffel a b d) hg.isOpen hy
  have hvd := fun d => differentiableAt_of_contDiffOn (hv d) hg.isOpen hy
  have hm : ∀ d, DifferentiableAt ℝ (fun z => christoffel g a b d z * v z d) y := fun d => (hΓ d).mul (hvd d)
  have h2 : DifferentiableAt ℝ (fun z => ∑ d, christoffel g a b d z * v z d) y :=
    DifferentiableAt.fun_sum fun d _ => hm d
  unfold covD
  rw [pd_add h1 h2 c, pd_sum (f := fun d z => christoffel g a b d z * v z d) _ (fun d _ => hm d) c]
  congr 1
  exact Finset.sum_congr rfl fun d _ => pd_mul (hΓ d) (hvd d) c

/-- **The Raychaudhuri identity in coordinates**: for a field geodesic on `U`,
`vᶜ ∂_c Θ = -(∇_b vᵃ)(∇ₐ vᵇ) - R_{σν} vᵠ vᵛ`. -/
theorem raychaudhuri_coord (hgeo : ∀ y ∈ U, ∀ d, ∑ c, v y c * covD g v d c y = 0) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∑ c, v x c * pd c (expansion g v) x =
      -(∑ a, ∑ b, covD g v a b x * covD g v b a x) - ∑ s, ∑ t, ricci g s t x * v x s * v x t := by
  set V : Fin n → ℝ := v x
  set D : Fin n → Fin n → ℝ := fun a b => pd b (fun z => v z a) x
  set H : Fin n → Fin n → Fin n → ℝ := fun a b c => pd c (pd b fun z => v z a) x
  set Γ : Fin n → Fin n → Fin n → ℝ := fun a b c => christoffel g a b c x
  set dΓ : Fin n → Fin n → Fin n → Fin n → ℝ := fun a b c d => pd d (christoffel g a b c) x
  have hH : ∀ a b c, H a b c = H a c b := fun a b c => pd_pd_comm (hv a) hg.isOpen hx c b
  have hΓs : ∀ a b c, Γ a b c = Γ a c b := fun a b c => christoffel_symm_at hg hx a b c
  have hcov : ∀ a b, covD g v a b x = D a b + ∑ c, Γ a b c * V c := fun a b => rfl
  -- the derivative of the geodesic equation vanishes
  have hE : ∀ a, ∑ b, (D b a * (D a b + ∑ c, Γ a b c * V c) +
      V b * (H a b a + ∑ c, (dΓ a b c a * V c + Γ a b c * D c a))) = 0 := by
    intro a
    have hz : (fun y => ∑ b, v y b * covD g v a b y) =ᶠ[𝓝 x] fun _ => 0 :=
      Filter.eventually_of_mem (hg.isOpen.mem_nhds hx) fun y hy => hgeo y hy a
    have h0 := pd_congr hz a
    have hc : pd a (fun _ : Fin n → ℝ => (0 : ℝ)) x = 0 := by simp [pd]
    have hm : ∀ b, DifferentiableAt ℝ (fun y => v y b * covD g v a b y) x := fun b =>
      (differentiableAt_of_contDiffOn (hv b) hg.isOpen hx).mul (differentiableAt_covD hg hv hx a b)
    rw [hc, pd_sum (f := fun b y => v y b * covD g v a b y) _ (fun b _ => hm b) a] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [pd_mul (differentiableAt_of_contDiffOn (hv b) hg.isOpen hx) (differentiableAt_covD hg hv hx a b) a,
      pd_covD hg hv hx a b a]
    rfl
  have hG : ∀ d, ∑ c, V c * (D d c + ∑ e, Γ d c e * V e) = 0 := fun d => hgeo x hx d
  have key := Raychaudhuri.raychaudhuri_algebra V D H Γ dΓ hH hΓs hE hG
  -- the left side is `v(Θ)`, the right side the library's terms
  have hL : ∑ c, v x c * pd c (expansion g v) x =
      ∑ c, V c * ∑ a, (H a a c + ∑ d, (dΓ a a d c * V d + Γ a a d * D d c)) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold expansion
    rw [pd_sum _ (fun a _ => differentiableAt_covD hg hv hx a a) c]
    congr 1
    exact Finset.sum_congr rfl fun a _ => pd_covD hg hv hx a a c
  have hRic : ∀ s t, ricci g s t x =
      ∑ r, (dΓ r t s r - dΓ r r s t + ∑ l, (Γ r r l * Γ l t s - Γ r t l * Γ l r s)) := by
    intro s t
    unfold ricci riemann
    rfl
  rw [hL, key]
  simp only [hcov, hRic]

/-- **Raychaudhuri's equation in coordinates** (Kar–SenGupta (12), any dimension `n ≥ 2`): for a field geodesic on `U` with
`g(v, v) = -1` at `x`, `v(Θ) = -Θ²/(n-1) - σ² + ω² - R_{σν} vᵠ vᵛ`, with `σ² = σ_ab σ^ab` and `ω² = ω_ab ω^ab`
(`Raychaudhuri.normSqG`, indices raised with `g⁻¹`). -/
theorem raychaudhuri_equation (hgeo : ∀ y ∈ U, ∀ d, ∑ c, v y c * covD g v d c y = 0) {x : Fin n → ℝ} (hx : x ∈ U)
    (hnorm : v x ⬝ᵥ (g x *ᵥ v x) = -1) (hn : 1 < n) :
    ∑ c, v x c * pd c (expansion g v) x =
      -(expansion g v x) ^ 2 / (n - 1) - Raychaudhuri.normSqG (g x) (shear g v x) +
        Raychaudhuri.normSqG (g x) (rotation g v x) - ∑ s, ∑ t, ricci g s t x * v x s * v x t := by
  unfold shear rotation covDMat
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => covD g v a b x
  have hMu : M *ᵥ v x = 0 := by
    funext d; simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, Pi.zero_apply]
    rw [← hgeo x hx d]; exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have htr : Matrix.trace M = expansion g v x := by simp [Matrix.trace, M, expansion]
  have hsq : Matrix.trace (M * M) = ∑ a, ∑ b, covD g v a b x * covD g v b a x := by
    simp [Matrix.trace, Matrix.mul_apply, M]
  have hsplit := Raychaudhuri.trace_sq_split (g x) M (v x) (hg.symm x hx) (hg.isUnit_det x hx) hMu hnorm hn
  rw [raychaudhuri_coord hg hv hgeo hx, ← hsq, hsplit, htr]
  ring

end

end Lightlike
