import Lightlike.Regge.Linear3.DeficitDeriv
import Lightlike.Regge.Linear3.TorusBridgeLengths
import Lightlike.Regge.Linear3.InterpEdge
import Lightlike.Regge.Linear3.SaintVenantCore

/-!
# The coefficient `Q_n (h)` of the linearized Regge action on the periodic Kuhn complex

For a smooth field `h` of symmetric matrices on `ℝ³` invariant under integer translations, give the edges
of the periodic Kuhn complex `torusComplex n` of mesh `1/n` the squared lengths `ℓ_e² + ε a_e`, with `ℓ_e` the
Euclidean base lengths (`lenMesh`) and `a_e = μ_e (h)` Christiansen's degrees of freedom of the Regge
interpolant of `δ + ε h` (`lenD n (muE h)`). `Qn` is the coefficient `Σ_e (a_e / (2 ℓ_e)) δ_e'(0)` of
`ε²/2` in the Regge action (`SecondOrder.lean`). This file writes it as a sum over the edge classes `k`
and the cells `z`, the deficit angle derivative being `-Σ dth h (n² μ-vector) / √(hbase h 0)` over the
incidences of the class (`Qn_eq`): the hinge-length factor times the derivative of the dihedral angle of the
Kuhn star in the unit-scale variation `muVec` (`Dh_inc`, using the scale invariance `Dh_scale`).

## Main results

* `valid_hbase`: the base squared lengths of each hinge are admissible.
* `incV_len0_sq`, `incV_lenD_mu`, `Dh_inc`: the base lengths, the degrees of freedom and the angle derivative of an
  incidence.
* `lengthsNondeg_lenMesh`: the base lengths of mesh `1/n` are non-degenerate.
* `Qn`, `Qn_eq`: the coefficient and its class-and-cell form.

**Limits.** `n ≥ 3`; `h` invariant under integer translations (`μ_e` then depends only on the edge of the torus).
No limit `n → ∞` here (`Linear3/…` later): this is the exact finite-mesh rewriting.
-/

open Real Finset Filter Topology
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3

theorem valid_hbase (h : Fin 6) : Valid (hbase h) := by
  fin_cases h <;> simp [Valid, hbase, Pp, cosSq, Nn] <;> norm_num
  all_goals (
    have h2 : (1 : ℝ) < √2 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    rw [abs_of_pos (by positivity)]
    exact inv_lt_one_of_one_lt₀ h2)


variable (n : ℕ) [NeZero n]

theorem incV_len0_sq (hn : 3 ≤ n) (c : TV n) (σ h : Fin 6) :
    incV n (fun e => (len0 n e / n) ^ 2) c σ h = (1 / (n : ℝ) ^ 2) • hbase h := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hinge_distinct h
  have hb := hbase_eq h
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  funext i
  fin_cases i
  · have := len0_sq n (by omega) c σ d1
    simp only [incV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Pi.smul_apply, smul_eq_mul, div_pow, this]
    rw [hb]; simp; ring
  · have := len0_sq n (by omega) c σ d2
    simp only [incV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Pi.smul_apply, smul_eq_mul, div_pow, this]
    rw [hb]; simp; ring
  · have := len0_sq n (by omega) c σ d4
    simp only [incV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Pi.smul_apply, smul_eq_mul, div_pow, this]
    rw [hb]; simp; ring
  · have := len0_sq n (by omega) c σ d3
    simp only [incV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Pi.smul_apply, smul_eq_mul, div_pow, this]
    rw [hb]; simp; ring
  · have := len0_sq n (by omega) c σ d5
    simp only [incV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Pi.smul_apply, smul_eq_mul, div_pow, this]
    rw [hb]; simp; ring
  · have := len0_sq n (by omega) c σ d6
    simp only [incV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Pi.smul_apply, smul_eq_mul, div_pow, this]
    rw [hb]; simp; ring


/-- The six interpolated degrees of freedom `n² μ_e` of the incidence `(σ, h)` at the corners with integer
cell representative `ct`. -/
noncomputable def muVec (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (ct : Fin 3 → ℤ) (σ h : Fin 6) :
    Fin 6 → ℝ :=
  ![(n : ℝ) ^ 2 * muE hf (cornerPt n ct σ (hP h)) (cornerPt n ct σ (hQ h)),
    (n : ℝ) ^ 2 * muE hf (cornerPt n ct σ (hP h)) (cornerPt n ct σ (hR h)),
    (n : ℝ) ^ 2 * muE hf (cornerPt n ct σ (hQ h)) (cornerPt n ct σ (hR h)),
    (n : ℝ) ^ 2 * muE hf (cornerPt n ct σ (hP h)) (cornerPt n ct σ (hS h)),
    (n : ℝ) ^ 2 * muE hf (cornerPt n ct σ (hQ h)) (cornerPt n ct σ (hS h)),
    (n : ℝ) ^ 2 * muE hf (cornerPt n ct σ (hR h)) (cornerPt n ct σ (hS h))]

theorem incV_lenD_mu (hn : 3 ≤ n) (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p)
    (c : TV n) (ct : Fin 3 → ℤ) (hc : ∀ i, (ct i : ZMod n) = c i) (σ h : Fin 6) :
    incV n (lenD n (muE hf)) c σ h = (1 / (n : ℝ) ^ 2) • muVec n hf ct σ h := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hinge_distinct h
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hsym := muE_comm hf
  have hp : ∀ x y (e : Fin 3 → ℤ), muE hf (x + fun i => (e i : ℝ)) (y + fun i => (e i : ℝ)) = muE hf x y :=
    fun x y e => muE_translate hf _ (hper · e) x y
  have hl : ∀ {a b : Fin 4}, a ≠ b → lenD n (muE hf) {c + off n σ a, c + off n σ b} =
      muE hf (cornerPt n ct σ a) (cornerPt n ct σ b) := fun {a b} hab =>
    lenD_corner n hn (muE hf) hsym hp c ct hc σ hab
  funext i
  fin_cases i <;>
  · simp [incV, muVec, hl d1, hl d2, hl d3, hl d4, hl d5, hl d6]
    field_simp

/-- **The derivative of the angle of an incidence in terms of `dth`.** -/
theorem Dh_inc (hn : 3 ≤ n) (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p)
    (c : TV n) (ct : Fin 3 → ℤ) (hc : ∀ i, (ct i : ZMod n) = c i) (σ h : Fin 6) :
    Dh (incV n (fun e => (len0 n e / n) ^ 2) c σ h, incV n (lenD n (muE hf)) c σ h) =
      dth h (muVec n hf ct σ h) / √(hbase h 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [incV_len0_sq n hn, incV_lenD_mu n hn hf hper c ct hc]
  rw [Dh_scale (by positivity) (valid_hbase h)]
  exact dihSq'_eq h _


theorem lengthsNondeg_smul {V : Type*} [DecidableEq V] {K : Lightlike.PR.Complex3 V} {ℓ : Finset V → ℝ}
    (hK : LengthsNondeg K ℓ) {c : ℝ} (hc : 0 < c) : LengthsNondeg K (fun e => c * ℓ e) := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := hK t ht
  refine ⟨fun e he => mul_pos hc (h1 e he), fun f hf => ?_, ?_⟩
  · have : triH (fun e => c * ℓ e) f = c ^ 4 * triH ℓ f := by
      unfold triH
      simp only [mul_pow, ← Finset.mul_sum]
      ring
    rw [this]; exact mul_pos (by positivity) (h2 f hf)
  · have : tetV2 (fun e => c * ℓ e) t = c ^ 6 * tetV2 ℓ t := by
      obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ := exists_label (K := K) ht
      rw [tetV2_eq _ hpq hpr hps hqr hqs hrs, tetV2_eq _ hpq hpr hps hqr hqs hrs]
      unfold Lightlike.PR.vol2
      ring
    rw [this]; exact mul_pos (by positivity) h3


/-- The base lengths of the complex of mesh `1/n`. -/
noncomputable def lenMesh (e : Finset (TV n)) : ℝ := len0 n e / n

theorem lengthsNondeg_lenMesh (hn : 3 ≤ n) : LengthsNondeg (torusComplex n (by omega)) (lenMesh n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have := lengthsNondeg_smul (lengthsNondeg_len0 n hn) (c := 1 / (n : ℝ)) (by positivity)
  convert this using 2
  simp [lenMesh, div_eq_inv_mul]

/-- **The coefficient `Q_n (h)`** of the second-order expansion of the Regge action of the periodic Kuhn
complex of mesh `1/n` for the interpolated lengths of the perturbation `h`: `Σ_e (a_e / (2 ℓ_e)) δ_e'(0)`,
with `a_e = μ_e (h)` (`Lightlike/Regge/Linear3/SecondOrder.lean`). -/
noncomputable def Qn (hn : 2 ≤ n) (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ e ∈ (torusComplex n hn).edges,
    lenD n (muE hf) e / (2 * lenMesh n e) *
      deriv (fun ε => deficit (torusComplex n hn)
        (lenLine (lenMesh n) (lenD n (muE hf)) ε) e) 0


/-- **The coefficient `Q_n (h)` as a sum over the edge classes and the cells.** -/
theorem Qn_eq (hn : 3 ≤ n) (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p) :
    Qn n (by omega) hf = ∑ k : Fin 7, ∑ z : TV n,
      lenD n (muE hf) (edgeOf n z k) / (2 * lenMesh n (edgeOf n z k)) *
        (-∑ σ : Fin 6, ∑ h : Fin 6, if Cond (dirsN k) σ h then
          dth h (muVec n hf (fun i => (((z i).val : ℕ) : ℤ) - koff (hP h) (perms σ i)) σ h) /
            √(hbase h 0) else 0) := by
  unfold Qn
  rw [edges_torus n hn, sum_image (fun a _ b _ h => edgeOf_injective n hn h), Fintype.sum_prod_type,
    sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun z _ => ?_
  congr 1
  rw [(hasDerivAt_deficit_edgeOf n hn (lengthsNondeg_lenMesh n hn) (lenD n (muE hf)) z k).deriv]
  congr 1
  refine sum_congr rfl fun σ _ => sum_congr rfl fun h _ => ?_
  by_cases hc : Cond (dirsN k) σ h
  · simp only [hc, if_true]
    have hcc : ∀ i, (((((z i).val : ℕ) : ℤ) - koff (hP h) (perms σ i) : ℤ) : ZMod n) =
        (z - off n σ (hP h)) i := fun i => by
      simp [off]
    exact Dh_inc n hn hf hper (z - off n σ (hP h)) _ hcc σ h
  · simp [hc]

end Lightlike.Regge.Linear3
