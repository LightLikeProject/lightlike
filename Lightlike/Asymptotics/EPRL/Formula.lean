import Lightlike.Asymptotics.EPRL.ReggeState
import Lightlike.Spin4.Vertex

/-!
# The asymptotic formulas for the 15j symbol and the Euclidean EPRL vertex

Two statements, as propositions (proved as `coh15jAsymptoticFormula` and `eprlAsymptoticFormula`), about the coherent integrals of `Amplitude.lean` with the Regge
state of `ReggeState.lean`.

* `Coh15jAsymptoticFormula` (Barrett, Fairbairn, Hellmann, arXiv:0912.4907, eq. (16)): for a
  geometric 4-simplex `σ` and doubled spins `n` proportional to the triangle areas, with even sums
  at each node,
  `coh15j (λn) = (2π/λ)^6 2^4 (4π)^{-8} (e^{iλS} det(-H₊)^{-1/2} + e^{-iλS} det(-H₋)^{-1/2})
  + O(λ^{-7})`, with `S = Σ_e (n_e/2) Θ_e` the Regge action and `H_±` the Hessians at the two
  critical points `critPlus σ`, `critMinus`. BFH state the leading term (`∼`); the error term
  `O(λ^{-7})` is the one of the stationary phase theorem
  (`Lightlike.Oscillatory.stationary_phase`) in dimension `12`.
* `EPRLAsymptoticFormula` (Barrett, Dowdall, Fairbairn, Gomes, Hellmann, J. Math. Phys. 50 (2009)
  112504, arXiv:0902.1170, Theorem 1 for `γ < 1`): for `0 < γ < 1` and EPRL labels `(n, m)` of
  doubled spins `J = n + m` proportional to the areas, the coherent EPRL integral is the sum of four
  terms with phases `±λS` and `±γλS`, `S = Σ_e (J_e/2) Θ_e`, of order `λ^{-12}`, up to `O(λ^{-13})`.
  The four constants are products of the 15j constants of the self-dual and the anti-self-dual
  spins and are kept separate.

Both carry the nondegeneracy of the Hessians as an explicit hypothesis, as BDFGH do. Every other
hypothesis holds at the regular 4-simplex with `γ = 1/2` and `(n, m) = (3, 1)` on every edge
(`regular_coh15j_hyps`, `regular_eprl_hyps`), and its exterior dihedral angles are
`π - arccos(1/4)` (`reggeAngle_regular`).

The statements concern the coherent integral forms. The 15j symbol and the EPRL vertex of
`Lightlike.Spin4.eprlVertex`, contracted with coherent intertwiners, differ from them by a sign
`(-1)^χ` (BFH, eq. (1)); that identification is a separate statement. The case `γ > 1`, where the
anti-self-dual boundary state carries the reflected normal, is not covered.
-/

open Matrix Complex Filter Asymptotics Finset
open scoped Real

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.Oscillatory Lightlike.Regge4

/-- The contribution `det(-H₊)^{-1/2}` of the critical point `U⁺` with doubled spins `n`. -/
noncomputable def ampPlus (n : Fin 10 → ℕ) (σ : Simplex4) : ℂ :=
  invSqrtDet (-hessAmp n (reggeState σ) (critPlus σ))

/-- The contribution `det(-H₋)^{-1/2}` of the critical point `U⁻` with doubled spins `n`. -/
noncomputable def ampMinus (n : Fin 10 → ℕ) (σ : Simplex4) : ℂ :=
  invSqrtDet (-hessAmp n (reggeState σ) critMinus)

/-- **The asymptotic formula for the coherent 15j integral** (BFH, eq. (16), with an explicit
error term). For a geometric 4-simplex `σ` and doubled spins `n` that are proportional to the
triangle areas, with even sums at each node and nondegenerate Hessians at the two critical points,
`coh15j (λn) (reggeState σ) - (2π/λ)^6 2^4 (4π)^{-8} (e^{iλS} det(-H₊)^{-1/2} +
e^{-iλS} det(-H₋)^{-1/2}) = O(λ^{-7})` for `λ ∈ ℕ`, `λ → ∞`, with `S = reggeAction σ n`. -/
def Coh15jAsymptoticFormula : Prop :=
  ∀ (σ : Simplex4) (n : Fin 10 → ℕ),
    (∃ c : ℝ, 0 < c ∧ ∀ e, (n e : ℝ) = c * triArea σ e) →
    (∀ a, Even (∑ k, k5Spins n a k)) →
    (-hessAmp n (reggeState σ) (critPlus σ)).det ≠ 0 →
    (-hessAmp n (reggeState σ) critMinus).det ≠ 0 →
    (fun lam : ℕ => coh15j (lam • n) (reggeState σ) -
        (((2 * π / lam) ^ 6 * 2 ^ 4 / (4 * π) ^ 8 : ℝ) : ℂ) *
          (cexp (I * lam * reggeAction σ n) * ampPlus n σ +
            cexp (-(I * lam * reggeAction σ n)) * ampMinus n σ))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ 7)⁻¹

/-- **The asymptotic formula for the Euclidean EPRL vertex**, `0 < γ < 1` (BDFGH, Theorem 1, on the
coherent integral form). For a geometric 4-simplex `σ`, EPRL labels `(n, m)` (doubled self-dual and
anti-self-dual spins) of doubled spins `J = n + m` proportional to the triangle areas, even node
sums of `n` and of `m`, and nondegenerate Hessians, with `S = reggeAction σ (n + m)`:
`eprlCoh (λn) (λm) (reggeState σ) = (2π/λ)^12 2^8 (4π)^{-16} (N₊₊ e^{iλS} + N₋₋ e^{-iλS} +
N₊₋ e^{iγλS} + N₋₊ e^{-iγλS}) + O(λ^{-13})`, where `N_{ε₁ε₂}` is the product of the contributions
of the critical points `ε₁` for `n` and `ε₂` for `m`. -/
def EPRLAsymptoticFormula : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 1 → ∀ (σ : Simplex4) (n m : Fin 10 → ℕ),
    IsEPRLVertexLabel γ n m →
    (∃ c : ℝ, 0 < c ∧ ∀ e, ((n e + m e : ℕ) : ℝ) = c * triArea σ e) →
    (∀ a, Even (∑ k, k5Spins n a k)) → (∀ a, Even (∑ k, k5Spins m a k)) →
    (-hessAmp n (reggeState σ) (critPlus σ)).det ≠ 0 →
    (-hessAmp n (reggeState σ) critMinus).det ≠ 0 →
    (-hessAmp m (reggeState σ) (critPlus σ)).det ≠ 0 →
    (-hessAmp m (reggeState σ) critMinus).det ≠ 0 →
    (fun lam : ℕ => eprlCoh (lam • n) (lam • m) (reggeState σ) -
        (((2 * π / lam) ^ 12 * 2 ^ 8 / (4 * π) ^ 16 : ℝ) : ℂ) *
          (cexp (I * lam * reggeAction σ (n + m)) * (ampPlus n σ * ampPlus m σ) +
            cexp (-(I * lam * reggeAction σ (n + m))) * (ampMinus n σ * ampMinus m σ) +
            cexp (I * lam * (γ * reggeAction σ (n + m))) * (ampPlus n σ * ampMinus m σ) +
            cexp (-(I * lam * (γ * reggeAction σ (n + m)))) * (ampMinus n σ * ampPlus m σ)))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ 13)⁻¹

/-! ## The regular 4-simplex -/

/-- The parameter `t = (1 - √5)/4` of the regular 4-simplex `e₀, e₁, e₂, e₃, t(1, 1, 1, 1)`. -/
noncomputable def regT : ℝ := (1 - √5) / 4

/-- `t = (1 - √5)/4` is a root of `4t² - 2t - 1`. -/
theorem regT_root : 4 * regT ^ 2 - 2 * regT - 1 = 0 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [regT]
  nlinarith

/-- The vertices `e₀, e₁, e₂, e₃, t(1, 1, 1, 1)` of the regular 4-simplex with edge length `√2`. -/
noncomputable def regPoint : Fin 5 → EuclideanSpace ℝ (Fin 4) :=
  ![WithLp.toLp 2 ![1, 0, 0, 0], WithLp.toLp 2 ![0, 1, 0, 0], WithLp.toLp 2 ![0, 0, 1, 0],
    WithLp.toLp 2 ![0, 0, 0, 1], WithLp.toLp 2 ![regT, regT, regT, regT]]

/-- The five vertices of the regular simplex are affinely independent. -/
theorem regPoint_affineIndependent : AffineIndependent ℝ regPoint := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hs
  have hj := fun j : Fin 4 => congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v j) hs
  simp only [Fin.sum_univ_five, regPoint] at hj hw
  have h0 := hj 0
  have h1 := hj 1
  have h2 := hj 2
  have h3 := hj 3
  simp at h0 h1 h2 h3
  have h5 : 0 < √5 := Real.sqrt_pos.mpr (by norm_num)
  have h4 : w 4 = 0 := by
    have : w 4 * (1 - 4 * regT) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · simp only [regT] at h
      linarith
  intro i
  fin_cases i <;> simp <;> nlinarith

/-- **The regular 4-simplex** with vertices `e₀, e₁, e₂, e₃, t(1, 1, 1, 1)`, `t = (1 - √5)/4`. -/
noncomputable def regSimplex : Simplex4 := ⟨regPoint, regPoint_affineIndependent⟩

/-- All edges of the regular simplex have length `√2`. -/
theorem dist_regPoint {a b : Fin 5} (h : a ≠ b) : dist (regPoint a) (regPoint b) = √2 := by
  have ht := regT_root
  rw [EuclideanSpace.dist_eq]
  congr 1
  fin_cases a <;> fin_cases b <;> simp_all [regPoint, Fin.sum_univ_four, Real.dist_eq, sq_abs] <;>
    nlinarith

/-- The edge lengths of the regular simplex are `√2`. -/
theorem simplexLength_regular {t : Finset (Fin 5)} (ht : t.card = 2) :
    simplexLength regSimplex t = √2 := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp ht
  rw [simplexLength_pair _ hab]
  exact dist_regPoint hab

/-- The triangles of the regular simplex have area `√3/2`. -/
theorem triArea_regular (e : Fin 10) : triArea regSimplex e = √3 / 2 := by
  have hc : (edgeTriSet e).card = 3 := by revert e; decide
  have hs : ∀ s ∈ (edgeTriSet e).powersetCard 2, simplexLength regSimplex s = √2 :=
    fun s hs => simplexLength_regular (mem_powersetCard.mp hs).2
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hH : Lightlike.Regge.triH (simplexLength regSimplex) (edgeTriSet e) = 12 := by
    have e2 : ∑ s ∈ (edgeTriSet e).powersetCard 2, simplexLength regSimplex s ^ 2 =
        ∑ s ∈ (edgeTriSet e).powersetCard 2, √2 ^ 2 := sum_congr rfl fun s hs' => by rw [hs s hs']
    have e4 : ∑ s ∈ (edgeTriSet e).powersetCard 2, simplexLength regSimplex s ^ 4 =
        ∑ s ∈ (edgeTriSet e).powersetCard 2, √2 ^ 4 := sum_congr rfl fun s hs' => by rw [hs s hs']
    rw [Lightlike.Regge.triH, e2, e4, sum_const, sum_const, card_powersetCard, hc]
    norm_num
    nlinarith
  rw [triArea, area4, hH, show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  ring

/-- `cosDihedral4` depends on the lengths only through the squared edge lengths `sq`. -/
theorem cosDihedral4_congr {ℓ ℓ' : Finset (Fin 5) → ℝ} (h : Regge4.sq ℓ = Regge4.sq ℓ')
    (p q r s u : Fin 5) :
    cosDihedral4 ℓ p q r s u = cosDihedral4 ℓ' p q r s u := by
  unfold cosDihedral4 mixed gram3 ip
  rw [h]

/-- **The exterior dihedral angles of the regular simplex** are `π - arccos(1/4) ≈ 1.8235`. -/
theorem reggeAngle_regular (e : Fin 10) : reggeAngle regSimplex e = π - Real.arccos (1 / 4) := by
  have hsq : Regge4.sq (simplexLength regSimplex) = Regge4.sq (fun _ => √2) := by
    funext a b
    by_cases hab : a = b
    · simp [Regge4.sq, hab]
    · simp only [Regge4.sq, hab, ↓reduceIte]
      rw [simplexLength_regular (card_pair hab)]
  have hd : ∀ e : Fin 10, edgeTri e 0 ≠ edgeTri e 1 ∧ edgeTri e 0 ≠ edgeTri e 2 ∧
      edgeTri e 0 ≠ edgeTgt e ∧ edgeTri e 0 ≠ edgeSrc e ∧ edgeTri e 1 ≠ edgeTri e 2 ∧
      edgeTri e 1 ≠ edgeTgt e ∧ edgeTri e 1 ≠ edgeSrc e ∧ edgeTri e 2 ≠ edgeTgt e ∧
      edgeTri e 2 ≠ edgeSrc e ∧ edgeTgt e ≠ edgeSrc e := by decide
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hd e
  rw [reggeAngle, dihedral4, cosDihedral4_congr hsq,
    cosDihedral4_regular (Real.sqrt_ne_zero'.mpr (by norm_num)) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]

/-- The doubled spins `3` on every edge have even node sums (`12`). -/
theorem even_k5Spins_three (a : Fin 5) : Even (∑ k, k5Spins (fun _ => 3) a k) := by
  revert a
  decide

/-- The doubled spins `1` on every edge have even node sums (`4`). -/
theorem even_k5Spins_one (a : Fin 5) : Even (∑ k, k5Spins (fun _ => 1) a k) := by
  revert a
  decide

/-- **Non-vacuity of `Coh15jAsymptoticFormula`**: at the regular simplex, the doubled spins `3` on
every edge are proportional to the areas and have even node sums. The two Hessian conditions are
checked numerically (`scripts/asymptotics/eprl_asymptotics_check.py`). -/
theorem regular_coh15j_hyps :
    (∃ c : ℝ, 0 < c ∧ ∀ e, ((fun _ => 3 : Fin 10 → ℕ) e : ℝ) = c * triArea regSimplex e) ∧
      ∀ a, Even (∑ k, k5Spins (fun _ => 3) a k) := by
  refine ⟨⟨6 / √3, by positivity, fun e => ?_⟩, even_k5Spins_three⟩
  rw [triArea_regular]
  have h3 : √3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp
  norm_num

/-- **Non-vacuity of `EPRLAsymptoticFormula`**: at the regular simplex with `γ = 1/2`, the labels
`(n, m) = (3, 1)` on every edge are the EPRL labels of the doubled spin `J = 4`, `J` is
proportional to the areas, and both `n` and `m` have even node sums. The four Hessian conditions
are checked numerically (`scripts/asymptotics/eprl_asymptotics_check.py`). -/
theorem regular_eprl_hyps :
    IsEPRLVertexLabel (1 / 2) (fun _ => 3) (fun _ => 1) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ e, (((fun _ => 3 : Fin 10 → ℕ) e + (fun _ => 1 : Fin 10 → ℕ) e : ℕ) : ℝ)
        = c * triArea regSimplex e) ∧
      (∀ a, Even (∑ k, k5Spins (fun _ => 3) a k)) ∧ ∀ a, Even (∑ k, k5Spins (fun _ => 1) a k) := by
  refine ⟨fun e => ⟨?_, ?_⟩, ⟨8 / √3, by positivity, fun e => ?_⟩, even_k5Spins_three,
    even_k5Spins_one⟩
  · simp only [jPlus]
    norm_num [abs_of_pos]
  · simp only [jMinus]
    norm_num [abs_of_pos]
  · rw [triArea_regular]
    have h3 : √3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
    norm_num

/-- **Wrong inputs fail the hypotheses** at the regular simplex: the doubled spins `3` on the edge
`01` and `1` elsewhere are not proportional to the areas, and the doubled spins `2` on `01` and
`1` elsewhere have the odd sum `5` at the node `0`. -/
theorem regular_wrong_spins :
    (¬ ∃ c : ℝ, 0 < c ∧
        ∀ e, ((![3, 1, 1, 1, 1, 1, 1, 1, 1, 1] : Fin 10 → ℕ) e : ℝ) = c * triArea regSimplex e) ∧
      ¬ Even (∑ k, k5Spins ![2, 1, 1, 1, 1, 1, 1, 1, 1, 1] 0 k) := by
  refine ⟨fun ⟨c, _, hc⟩ => ?_, by decide⟩
  have h0 := hc 0
  have h1 := hc 1
  rw [triArea_regular] at h0 h1
  norm_num at h0 h1
  linarith

end Lightlike.Asymptotics.EPRL
