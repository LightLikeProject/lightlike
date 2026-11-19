import Lightlike.Spacetime.RaychaudhuriCoord
import Lightlike.Spacetime.RaychaudhuriShear
import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Cosmology.Raychaudhuri

/-!
# Focusing of a timelike geodesic congruence in coordinates (G1-009)

Kar and SenGupta (gr-qc/0611123), (16) and the paragraph after it: a congruence with initially negative expansion
converges if `R_ab vᵃ vᵇ + σ² - ω² ≥ 0`, and for a rotation-free (hypersurface-orthogonal) congruence the criterion is
`R_ab vᵃ vᵇ ≥ 0`: geodesic focusing. Here, for a coordinate metric on an open `U ⊆ ℝⁿ` and a smooth unit
(`g(v, v) = -1` on `U`) geodesic field `v`, along an integral curve `γ` of `v` on `[0, L)` with `Θ(γ(0)) < 0`:

* `raychaudhuri_convergence`: if `R(v, v) + σ² - ω² ≥ 0` along `γ`, then `L ≤ (n-1)/|Θ(γ(0))|` (any signature);
* `raychaudhuri_focusing`: for a Lorentzian coordinate metric, if `ω = 0` and `R(v, v) ≥ 0` along `γ`, the same bound;
  the shear term is nonnegative (`shear_normSq_nonneg`), since `g(v, ∇_b v) = 0` (`covD_orthogonal`) makes `σ` spatial.

The bound says the expansion cannot stay finite along `γ` beyond the parameter `(n-1)/|Θ(γ(0))|`; the Riccati argument
is `Cosmology.focusing`.
-/

open Filter Topology Set Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
  {v : (Fin n → ℝ) → Fin n → ℝ}

/-- **A unit field is orthogonal to its derivative**: if `g(v, v) = -1` on `U`, then `g(v, ∇_b v) = 0` on `U`. -/
theorem covD_orthogonal (hg : IsCoordMetric g U) (hv : ∀ a, ContDiffOn ℝ ∞ (fun y => v y a) U)
    (hnorm : ∀ y ∈ U, v y ⬝ᵥ (g y *ᵥ v y) = -1) {x : Fin n → ℝ} (hx : x ∈ U) (b : Fin n) :
    ∑ a, (g x *ᵥ v x) a * covD g v a b x = 0 := by
  have dv := fun a => differentiableAt_of_contDiffOn (hv a) hg.isOpen hx
  have dg := fun a c => differentiableAt_of_contDiffOn (hg.smooth a c) hg.isOpen hx
  have hF : (fun y => ∑ a, ∑ c, v y a * g y a c * v y c) =ᶠ[𝓝 x] fun _ => -1 :=
    Filter.eventually_of_mem (hg.isOpen.mem_nhds hx) fun y hy => by
      rw [← hnorm y hy]; simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have h0 := pd_congr hF b
  have hc : pd b (fun _ : Fin n → ℝ => (-1 : ℝ)) x = 0 := by simp [pd]
  have hm2 : ∀ a c, DifferentiableAt ℝ (fun y => v y a * g y a c) x := fun a c => (dv a).mul (dg a c)
  have hm : ∀ a c, DifferentiableAt ℝ (fun y => v y a * g y a c * v y c) x := fun a c => (hm2 a c).mul (dv c)
  have hpdF : pd b (fun y => ∑ a, ∑ c, v y a * g y a c * v y c) x =
      ∑ a, ∑ c, ((pd b (fun z => v z a) x * g x a c + v x a * (christoffelFirst g a b c x +
        christoffelFirst g c b a x)) * v x c + v x a * g x a c * pd b (fun z => v z c) x) := by
    rw [pd_sum (f := fun a y => ∑ c, v y a * g y a c * v y c) _
      (fun a _ => DifferentiableAt.fun_sum fun c _ => hm a c) b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pd_sum (f := fun c y => v y a * g y a c * v y c) _ (fun c _ => hm a c) b]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [pd_mul (hm2 a c) (dv c) b, pd_mul (dv a) (dg a c) b, hg.pd_eq_christoffelFirst hx b a c]
  rw [hc, hpdF] at h0
  have hs : ∀ a c, g x a c = g x c a := fun a c => by
    conv_rhs => rw [← hg.symm x hx]
    rfl
  -- the two halves
  set T1 := ∑ a, ∑ c, g x a c * v x c * pd b (fun z => v z a) x
  set T2 := ∑ a, ∑ c, v x a * christoffelFirst g a b c x * v x c
  have e1 : ∑ a, ∑ c, v x a * g x a c * pd b (fun z => v z c) x = T1 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hs]; ring
  have e2 : ∑ a, ∑ c, v x a * christoffelFirst g c b a x * v x c = T2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  have hpd : (∑ a, ∑ c, ((pd b (fun z => v z a) x * g x a c + v x a * (christoffelFirst g a b c x +
      christoffelFirst g c b a x)) * v x c + v x a * g x a c * pd b (fun z => v z c) x)) = 2 * T1 + 2 * T2 := by
    have : ∀ a c, ((pd b (fun z => v z a) x * g x a c + v x a * (christoffelFirst g a b c x +
        christoffelFirst g c b a x)) * v x c + v x a * g x a c * pd b (fun z => v z c) x) =
        g x a c * v x c * pd b (fun z => v z a) x + v x a * christoffelFirst g a b c x * v x c +
        v x a * christoffelFirst g c b a x * v x c + v x a * g x a c * pd b (fun z => v z c) x := fun a c => by ring
    simp only [this, Finset.sum_add_distrib, e1, e2]
    ring
  have h1 : ∑ a, (∑ c, g x a c * v x c) * pd b (fun z => v z a) x = T1 := by
    simp only [T1, Finset.sum_mul]
  have h2 : ∑ a, (∑ c, g x a c * v x c) * ∑ d, christoffel g a b d x * v x d = T2 := by
    have : T2 = ∑ c, ∑ d, ∑ a, g x a c * v x c * (christoffel g a b d x * v x d) := by
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      rw [← hg.lower_christoffel hx c b d, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by rw [hs a c]; ring
    rw [this]
    simp only [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
  have hT : ∑ a, (g x *ᵥ v x) a * covD g v a b x = T1 + T2 := by
    simp only [covD, mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
    rw [h1, h2]
  rw [hT]
  linarith [hpd, h0]

/-- The orthogonal complement of a timelike vector is spacelike for a Lorentzian coordinate metric. -/
theorem IsLorentzianCoordMetric.orthogonal_nonneg (hgL : IsLorentzianCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    {u : Fin n → ℝ} (hu : u ⬝ᵥ (g x *ᵥ u) < 0) (w : Fin n → ℝ) (hw : u ⬝ᵥ (g x *ᵥ w) = 0) :
    0 ≤ w ⬝ᵥ (g x *ᵥ w) := by
  obtain ⟨P, hP, hgx⟩ := hgL.2 x hx
  have hL : IsLorentzianForm n (matForm (g x)) := by rw [hgx]; exact matForm_isLorentzian P hP
  exact Raychaudhuri.orthogonal_nonneg_of_lorentzian hL (matForm_eq_dotProduct _) hu w hw

/-- `w = Σ_c wᶜ eᶜ` under a linear functional: `ℓ w = Σ_c wᶜ ℓ(e_c)`. -/
theorem clm_apply_eq_sum (ℓ : (Fin n → ℝ) →L[ℝ] ℝ) (w : Fin n → ℝ) : ℓ w = ∑ c, w c * ℓ (Pi.single c 1) := by
  conv_lhs => rw [show w = ∑ c, w c • Pi.single c (1 : ℝ) by ext i; simp [Pi.single_apply]]
  simp [map_sum, map_smul, smul_eq_mul]

section

variable (hv : ∀ a, ContDiffOn ℝ ∞ (fun y => v y a) U) (hgeo : ∀ y ∈ U, ∀ d, ∑ c, v y c * covD g v d c y = 0)
  (hnorm : ∀ y ∈ U, v y ⬝ᵥ (g y *ᵥ v y) = -1)
include hv hgeo hnorm

omit hgeo hnorm in
/-- The expansion along an integral curve: if `v(Θ) ≤ -Θ²/m` along an integral curve `γ` of `v` in `U` on `[0, L)`, with
`Θ(γ(0)) < 0`, then `L ≤ m/|Θ(γ(0))|` (`Cosmology.focusing`). -/
theorem focusing_along (hg : IsCoordMetric g U) {m L : ℝ} (hm : 0 < m) {γ : ℝ → Fin n → ℝ}
    (hγU : ∀ s ∈ Ico 0 L, γ s ∈ U) (hγ : ∀ s ∈ Ico 0 L, HasDerivAt γ (v (γ s)) s)
    (hle : ∀ s ∈ Ico 0 L, ∑ c, v (γ s) c * pd c (expansion g v) (γ s) ≤ -(expansion g v (γ s)) ^ 2 / m)
    (h0 : expansion g v (γ 0) < 0) : L ≤ m / |expansion g v (γ 0)| := by
  refine Cosmology.focusing (Θ := fun s => expansion g v (γ s))
    (Θ' := fun s => ∑ c, v (γ s) c * pd c (expansion g v) (γ s)) hm ?_ hle h0
  intro s hs
  have hd : DifferentiableAt ℝ (expansion g v) (γ s) := by
    unfold expansion
    exact DifferentiableAt.fun_sum fun a _ => differentiableAt_covD hg hv (hγU s hs) a a
  exact (hd.hasFDerivAt.comp_hasDerivAt s (hγ s hs)).congr_deriv (by rw [clm_apply_eq_sum]; rfl)

/-- **Convergence** (Kar–SenGupta (16)): for a unit geodesic field with `R_ab vᵃ vᵇ + σ² - ω² ≥ 0` along an integral
curve `γ` on `[0, L)` in `U` that starts converging (`Θ(γ(0)) < 0`), `L ≤ (n-1)/|Θ(γ(0))|`: the expansion cannot stay
finite beyond that parameter. -/
theorem raychaudhuri_convergence (hg : IsCoordMetric g U) (hn : 1 < n) {γ : ℝ → Fin n → ℝ} {L : ℝ}
    (hγU : ∀ s ∈ Ico 0 L, γ s ∈ U) (hγ : ∀ s ∈ Ico 0 L, HasDerivAt γ (v (γ s)) s)
    (hc : ∀ s ∈ Ico 0 L, 0 ≤ (∑ a, ∑ b, ricci g a b (γ s) * v (γ s) a * v (γ s) b) +
      Raychaudhuri.normSqG (g (γ s)) (shear g v (γ s)) - Raychaudhuri.normSqG (g (γ s)) (rotation g v (γ s)))
    (h0 : expansion g v (γ 0) < 0) : L ≤ (n - 1) / |expansion g v (γ 0)| := by
  have hm : (0 : ℝ) < n - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  refine focusing_along hv hg hm hγU hγ (fun s hs => ?_) h0
  rw [raychaudhuri_equation hg hv hgeo (hγU s hs) (hnorm _ (hγU s hs)) hn]
  linarith [hc s hs]

/-- **The shear term is nonnegative** for a unit timelike geodesic field of a Lorentzian coordinate metric: `σ` is
spatial (`σ v = 0`, from `g(v, ∇v) = 0`) and the orthogonal complement of `v` is spacelike. -/
theorem shear_normSq_nonneg (hgL : IsLorentzianCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    0 ≤ Raychaudhuri.normSqG (g x) (shear g v x) := by
  have hg := hgL.1
  unfold shear covDMat
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => covD g v a b x with hM
  set L := g x * M with hL
  set θ := expansion g v x
  set u' := g x *ᵥ v x with hu'
  have hMu : M *ᵥ v x = 0 := by
    funext d; simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, Pi.zero_apply]
    rw [← hgeo x hx d]; exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have hLu : L *ᵥ v x = 0 := by rw [hL, ← mulVec_mulVec, hMu, mulVec_zero]
  have hLtu : Lᵀ *ᵥ v x = 0 := by
    rw [mulVec_transpose, hL, ← vecMul_vecMul,
      show v x ᵥ* g x = g x *ᵥ v x by rw [← mulVec_transpose, hg.symm x hx]]
    funext b
    simp only [vecMul, dotProduct, M, Matrix.of_apply, Pi.zero_apply]
    exact covD_orthogonal hg hv hnorm hx b
  have huv : u' ⬝ᵥ v x = -1 := by rw [dotProduct_comm]; exact hnorm x hx
  have hhu : (g x + vecMulVec u' u') *ᵥ v x = 0 := by
    rw [add_mulVec, vecMulVec_mulVec, huv, ← hu']
    ext i; simp
  have hsym : ((1 / 2 : ℝ) • (L + Lᵀ) - (θ / ((n : ℝ) - 1)) • (g x + vecMulVec u' u'))ᵀ =
      (1 / 2 : ℝ) • (L + Lᵀ) - (θ / ((n : ℝ) - 1)) • (g x + vecMulVec u' u') := by
    rw [transpose_sub, transpose_smul, transpose_smul, transpose_add, transpose_add, transpose_transpose,
      hg.symm x hx, transpose_vecMulVec, add_comm Lᵀ L]
  have hσu : ((1 / 2 : ℝ) • (L + Lᵀ) - (θ / ((n : ℝ) - 1)) • (g x + vecMulVec u' u')) *ᵥ v x = 0 := by
    rw [sub_mulVec, smul_mulVec, smul_mulVec, add_mulVec, hLu, hLtu, hhu]; simp
  exact Raychaudhuri.normSqG_nonneg (g x) _ (v x) (hg.symm x hx) (hg.isUnit_det x hx) hsym hσu
    (Raychaudhuri.spacelike_complement (g x) (v x) (hg.symm x hx) (hnorm x hx)
      (hgL.orthogonal_nonneg hx (by rw [hnorm x hx]; norm_num)))

/-- **The focusing inequality** for a rotation-free congruence (Kar–SenGupta, after (16)): for a unit timelike geodesic
field of a Lorentzian coordinate metric with `ω = 0` and `R(v, v) ≥ 0` at `x`, `v(Θ) ≤ -Θ²/(n-1)`. -/
theorem raychaudhuri_focusing_at (hgL : IsLorentzianCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (hn : 1 < n)
    (hω : rotation g v x = 0) (hR : 0 ≤ ∑ s, ∑ t, ricci g s t x * v x s * v x t) :
    ∑ c, v x c * pd c (expansion g v) x ≤ -(expansion g v x) ^ 2 / (n - 1) := by
  rw [raychaudhuri_equation hgL.1 hv hgeo hx (hnorm x hx) hn, hω]
  have hσ := shear_normSq_nonneg hv hgeo hnorm hgL hx
  have h0 : Raychaudhuri.normSqG (g x) 0 = 0 := by simp [Raychaudhuri.normSqG]
  rw [h0]
  linarith

/-- **Geodesic focusing** (Kar–SenGupta, after (16): zero rotation and `R_ab vᵃ vᵇ ≥ 0`): along an integral curve `γ` on
`[0, L)` in `U` of a unit timelike geodesic field of a Lorentzian coordinate metric, rotation-free with `R(v, v) ≥ 0`
along `γ`, that starts converging (`Θ(γ(0)) < 0`), `L ≤ (n-1)/|Θ(γ(0))|`. -/
theorem raychaudhuri_focusing (hgL : IsLorentzianCoordMetric g U) (hn : 1 < n) {γ : ℝ → Fin n → ℝ} {L : ℝ}
    (hγU : ∀ s ∈ Ico 0 L, γ s ∈ U) (hγ : ∀ s ∈ Ico 0 L, HasDerivAt γ (v (γ s)) s)
    (hω : ∀ s ∈ Ico 0 L, rotation g v (γ s) = 0)
    (hR : ∀ s ∈ Ico 0 L, 0 ≤ ∑ a, ∑ b, ricci g a b (γ s) * v (γ s) a * v (γ s) b)
    (h0 : expansion g v (γ 0) < 0) : L ≤ (n - 1) / |expansion g v (γ 0)| := by
  have hm : (0 : ℝ) < n - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  exact focusing_along hv hgL.1 hm hγU hγ
    (fun s hs => raychaudhuri_focusing_at hv hgeo hnorm hgL (hγU s hs) hn (hω s hs) (hR s hs)) h0

end

end Lightlike
