import Lightlike.Regge.Conv3.EdgePoly
import Lightlike.Regge.Conv3.DihedralTaylor2
import Lightlike.Regge.Conv3.DihedralScale
import Lightlike.Regge.Conv3.KuhnCore
import Lightlike.Spacetime.Curvature

/-!
# The star of an edge at a single metric jet

The squared length of an edge of the Kuhn triangulation, at scale `ε` around a base point `m`, is
the jet polynomial `edgePoly` of the metric and its first two derivatives at `m`. Under the
scaling of the vertices by `ε` it splits into the three homogeneous pieces `ε² q + ε³ c + ε⁴ r`
(`edgePoly_smul`), the Gram length `q`, the first-derivative term `c` and the rest `r`.

This file sets up, for the 36 incidences (tetrahedron, hinge) of a cube, the six squared lengths
`q`, `c`, `r` of each tetrahedron, and states the jet-level star identity as a named hypothesis
`JetStarCore`. The hypothesis is about one jet: it does not mention the Regge sum or its limit.

## Main results

* `edgeQ`, `edgeC`, `edgeR`: the three homogeneous parts of `edgePoly`.
* `incVec`: the six squared lengths of a tetrahedron at a hinge, from a function of the midpoint
  offset and edge vector of an edge.
-/

open Lightlike Real
open scoped Matrix

namespace Lightlike.Regge.Conv3

open Lightlike.Geodesic

section

variable {n : ℕ} (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)

/-- The Gram part of `edgePoly`: `g_v(Δ, Δ)`. -/
noncomputable def edgeQ (v Δ : Fin n → ℝ) : ℝ := Δ ⬝ᵥ (g v *ᵥ Δ)

/-- The first-derivative part of `edgePoly`: `∂_s g_v(Δ, Δ)`. -/
noncomputable def edgeC (v s Δ : Fin n → ℝ) : ℝ := Δ ⬝ᵥ (dmat g v s *ᵥ Δ)

/-- The second-order part of `edgePoly`: the terms of total degree four in `(s, Δ)`. -/
noncomputable def edgeR (v s Δ : Fin n → ℝ) : ℝ :=
  (1 / 2) * (Δ ⬝ᵥ (ddmat g v s s *ᵥ Δ)) + (1 / 24) * (Δ ⬝ᵥ (ddmat g v Δ Δ *ᵥ Δ))
    - (1 / 12) * (chr g v Δ Δ ⬝ᵥ (g v *ᵥ chr g v Δ Δ))

/-- **Homogeneous decomposition of the edge polynomial.** Scaling the midpoint offset and the edge
vector by `ε` multiplies the three parts by `ε²`, `ε³`, `ε⁴`. -/
theorem edgePoly_smul (v s Δ : Fin n → ℝ) (ε : ℝ) :
    edgePoly g v (ε • s) (ε • Δ) = ε ^ 2 * edgeQ g v Δ + ε ^ 3 * edgeC g v s Δ
      + ε ^ 4 * edgeR g v s Δ := by
  simp only [edgePoly, edgeQ, edgeC, edgeR, dmat_smul, ddmat_smul_left, ddmat_smul_right,
    chr_smul_left, chr_smul_right, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul,
    Matrix.mulVec_smul, smul_eq_mul]
  ring

end

section Bounds

open Set Metric

/-- The second derivative of the dihedral angle is uniformly bounded, as a bilinear form, on a
compact admissible set. -/
theorem fderiv2_Dsq_bound {K : Set (Fin 6 → ℝ)} (hK : IsCompact K) (hKV : ∀ L ∈ K, Valid L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L ∈ K, ∀ c ρ : Fin 6 → ℝ,
      |fderiv ℝ (fderiv ℝ Dsq) L c ρ| ≤ C * ‖c‖ * ‖ρ‖ := by
  have hF : ContDiffOn ℝ 3 Dsq {L | Valid L} := fun L hL =>
    (contDiffAt_Dsq hL).contDiffWithinAt
  have h3 : ContinuousOn (fun x => ‖iteratedFDeriv ℝ 2 Dsq x‖) {L | Valid L} := by
    have := hF.continuousOn_iteratedFDerivWithin (m := 2) (by norm_num) isOpen_valid.uniqueDiffOn
    exact (this.congr (iteratedFDerivWithin_of_isOpen 2 isOpen_valid).symm).norm
  obtain ⟨B, hB⟩ := hK.bddAbove_image (h3.mono (fun L hL => hKV L hL))
  refine ⟨max B 0, le_max_right _ _, fun L hL c ρ => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ 2 Dsq L‖ ≤ max B 0 :=
    (hB ⟨L, hL, rfl⟩).trans (le_max_left _ _)
  have h2 := (iteratedFDeriv ℝ 2 Dsq L).le_opNorm ![c, ρ]
  rw [iteratedFDeriv_two_apply] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two] at h2
  calc |fderiv ℝ (fderiv ℝ Dsq) L c ρ| = ‖fderiv ℝ (fderiv ℝ Dsq) L c ρ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖iteratedFDeriv ℝ 2 Dsq L‖ * (‖c‖ * ‖ρ‖) := by simpa using h2
    _ ≤ max B 0 * (‖c‖ * ‖ρ‖) := by gcongr
    _ = max B 0 * ‖c‖ * ‖ρ‖ := by ring

set_option maxHeartbeats 800000 in
/-- **Uniform expansion of the dihedral angle along a quadratic curve.** On a compact admissible
set `K`, for `‖c‖, ‖ρ‖ ≤ B` and `0 < ε ≤ r`,
`Dsq (L + ε c + ε² ρ)` equals `Dsq L + ε Dh(L, c) + ε² (Dh(L, ρ) + ½ D²Dsq(L)(c, c))` up to
`M ε³`. -/
theorem dihSq_curve_expansion {K : Set (Fin 6 → ℝ)} (hK : IsCompact K)
    (hKV : ∀ L ∈ K, Valid L) {B : ℝ} (hB : 0 ≤ B) :
    ∃ M r : ℝ, 0 < r ∧ ∀ L ∈ K, ∀ c ρ : Fin 6 → ℝ, ‖c‖ ≤ B → ‖ρ‖ ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ r →
        |Dsq (L + ε • c + ε ^ 2 • ρ) - Dsq L - ε * Dh (L, c)
          - ε ^ 2 * (Dh (L, ρ) + (1 / 2) * fderiv ℝ (fderiv ℝ Dsq) L c c)| ≤ M * ε ^ 3 := by
  obtain ⟨M0, r0, hr0, hT⟩ := dihSq_taylor3 hK hKV
  obtain ⟨C, hC0, hC⟩ := fderiv2_Dsq_bound hK hKV
  refine ⟨|M0| * (2 * B) ^ 3 + 2 * C * B ^ 2, min 1 (r0 / (2 * B + 1)), lt_min one_pos
    (div_pos hr0 (by linarith)), fun L hL c ρ hc hρ ε hε hεr => ?_⟩
  have hε1 : ε ≤ 1 := hεr.trans (min_le_left _ _)
  have hε2 : ε ≤ r0 / (2 * B + 1) := hεr.trans (min_le_right _ _)
  set δ : Fin 6 → ℝ := ε • c + ε ^ 2 • ρ with hδ
  have hδn : ‖δ‖ ≤ 2 * B * ε := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε,
      abs_of_pos (pow_pos hε 2)]
    have a1 : ε * ‖c‖ ≤ ε * B := mul_le_mul_of_nonneg_left hc hε.le
    have a2 : ε ^ 2 * ‖ρ‖ ≤ ε * B :=
      calc ε ^ 2 * ‖ρ‖ ≤ ε ^ 2 * B := mul_le_mul_of_nonneg_left hρ (by positivity)
        _ ≤ ε * B := by nlinarith [mul_nonneg (mul_nonneg hε.le hB) (sub_nonneg.2 hε1)]
    linarith
  have hδr : ‖δ‖ ≤ r0 := by
    have : 2 * B * ε ≤ r0 := by
      rw [le_div_iff₀ (by linarith)] at hε2
      nlinarith
    linarith
  have t := hT L hL δ hδr
  have lin : Dh (L, δ) = ε * Dh (L, c) + ε ^ 2 * Dh (L, ρ) := by
    rw [← fderiv_Dsq δ (hKV L hL), ← fderiv_Dsq c (hKV L hL), ← fderiv_Dsq ρ (hKV L hL), hδ]
    simp
  have hess : fderiv ℝ (fderiv ℝ Dsq) L δ δ = ε ^ 2 * fderiv ℝ (fderiv ℝ Dsq) L c c
      + (ε ^ 3 * (fderiv ℝ (fderiv ℝ Dsq) L c ρ + fderiv ℝ (fderiv ℝ Dsq) L ρ c)
      + ε ^ 4 * fderiv ℝ (fderiv ℝ Dsq) L ρ ρ) := by
    rw [hδ]
    simp
    ring
  rw [lin, hess] at t
  have hcn := norm_nonneg c
  have hρn := norm_nonneg ρ
  have hcB : ‖c‖ * ‖ρ‖ ≤ B ^ 2 := by
    rw [sq]; exact mul_le_mul hc hρ hρn hB
  have hρB : ‖ρ‖ * ‖ρ‖ ≤ B ^ 2 := by
    rw [sq]; exact mul_le_mul hρ hρ hρn hB
  have b1 : |fderiv ℝ (fderiv ℝ Dsq) L c ρ| ≤ C * B ^ 2 :=
    (hC L hL c ρ).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hcB hC0)
  have b2 : |fderiv ℝ (fderiv ℝ Dsq) L ρ c| ≤ C * B ^ 2 :=
    (hC L hL ρ c).trans (by rw [mul_assoc, mul_comm ‖ρ‖ ‖c‖]; exact
      mul_le_mul_of_nonneg_left hcB hC0)
  have b3 : |fderiv ℝ (fderiv ℝ Dsq) L ρ ρ| ≤ C * B ^ 2 :=
    (hC L hL ρ ρ).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hρB hC0)
  have hε3 : ε ^ 4 ≤ ε ^ 3 := by
    have := mul_le_mul_of_nonneg_left hε1 (pow_pos hε 3).le
    calc ε ^ 4 = ε ^ 3 * ε := by ring
      _ ≤ ε ^ 3 * 1 := this
      _ = ε ^ 3 := mul_one _
  have hCB : 0 ≤ C * B ^ 2 := by positivity
  have hT1 : |ε ^ 3 * (fderiv ℝ (fderiv ℝ Dsq) L c ρ + fderiv ℝ (fderiv ℝ Dsq) L ρ c)|
      ≤ ε ^ 3 * (2 * (C * B ^ 2)) := by
    rw [abs_mul, abs_of_pos (pow_pos hε 3)]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (by linarith)) (by positivity)
  have hT2 : |ε ^ 4 * fderiv ℝ (fderiv ℝ Dsq) L ρ ρ| ≤ ε ^ 3 * (C * B ^ 2) := by
    rw [abs_mul, abs_of_pos (pow_pos hε 4)]
    calc ε ^ 4 * |fderiv ℝ (fderiv ℝ Dsq) L ρ ρ| ≤ ε ^ 4 * (C * B ^ 2) :=
          mul_le_mul_of_nonneg_left b3 (by positivity)
      _ ≤ ε ^ 3 * (C * B ^ 2) := mul_le_mul_of_nonneg_right hε3 hCB
  have hTT := abs_le.1 ((abs_add_le _ _).trans (add_le_add hT1 hT2))
  have e3 : ‖δ‖ ^ 3 ≤ (2 * B * ε) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hδn 3
  have hM0 : M0 * ‖δ‖ ^ 3 ≤ |M0| * ((2 * B) ^ 3 * ε ^ 3) :=
    (mul_le_mul_of_nonneg_right (le_abs_self M0) (by positivity)).trans
      (by rw [← mul_pow]; exact mul_le_mul_of_nonneg_left e3 (abs_nonneg _))
  have hq := abs_le.1 t
  have key : Dsq (L + ε • c + ε ^ 2 • ρ) = Dsq (L + δ) := by rw [hδ, add_assoc]
  rw [key, abs_le]
  constructor <;> linarith [hq.1, hq.2, hM0, hTT.1, hTT.2]

end Bounds

section Three

variable (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)

/-! ### The six squared lengths of a tetrahedron at a hinge -/

/-- The six squared lengths `(pq, pr, qr, ps, qs, rs)` of the tetrahedron `σ` at the hinge `h`,
obtained by applying `f s Δ` to the midpoint offset `s` and the edge vector `Δ` of each edge,
measured from the midpoint of the hinge (`kpos`). -/
noncomputable def incVec (f : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) (σ h : Fin 6) : Fin 6 → ℝ :=
  let e : Fin 4 → Fin 4 → ℝ := fun a b =>
    f (fun i => (kpos σ h a i + kpos σ h b i) / 2) (fun i => kpos σ h b i - kpos σ h a i)
  ![e (hP h) (hQ h), e (hP h) (hR h), e (hQ h) (hR h), e (hP h) (hS h), e (hQ h) (hS h),
    e (hR h) (hS h)]

/-- The Gram squared lengths of the incidence `(σ, h)` for the metric at `m`. -/
noncomputable def incQ (m : Fin 3 → ℝ) (σ h : Fin 6) : Fin 6 → ℝ :=
  incVec (fun _ Δ => edgeQ g m Δ) σ h

/-- The `ε³` coefficient of the squared lengths of the incidence `(σ, h)`. -/
noncomputable def incC (m : Fin 3 → ℝ) (σ h : Fin 6) : Fin 6 → ℝ :=
  incVec (fun s Δ => edgeC g m s Δ) σ h

/-- The `ε⁴` coefficient of the squared lengths of the incidence `(σ, h)`. -/
noncomputable def incR (m : Fin 3 → ℝ) (σ h : Fin 6) : Fin 6 → ℝ :=
  incVec (fun s Δ => edgeR g m s Δ) σ h

/-- The squared lengths of the incidence `(σ, h)` at scale `ε`: the edge polynomial of the metric
jet at `m` on the vertices `ε • kpos`. -/
noncomputable def incLen (m : Fin 3 → ℝ) (ε : ℝ) (σ h : Fin 6) : Fin 6 → ℝ :=
  incVec (fun s Δ => edgePoly g m (ε • s) (ε • Δ)) σ h

/-- The squared lengths at scale `ε` are `ε² (q + ε c + ε² r)`. -/
theorem incLen_eq (m : Fin 3 → ℝ) (ε : ℝ) (σ h : Fin 6) :
    incLen g m ε σ h = ε ^ 2 • (incQ g m σ h + ε • incC g m σ h + ε ^ 2 • incR g m σ h) := by
  ext i
  fin_cases i <;>
  · simp [incLen, incQ, incC, incR, incVec, edgePoly_smul]
    ring

/-! ### The seven edge classes and the jet-level star identity -/

/-- The seven directions `w ∈ {0,1}³ \ {0}` of the edges of the Kuhn triangulation of the cube:
three axes, three face diagonals and the body diagonal. -/
def dirs : Fin 7 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

/-- The hinge of the incidence `(σ, h)` lies in the edge class of direction `w`. -/
def InClass (w : Fin 3 → ℝ) (σ h : Fin 6) : Prop :=
  ∀ i, kv (hQ h) (perms σ i) - kv (hP h) (perms σ i) = w i

open Classical in
/-- The sum of `f σ h` over the incidences whose hinge lies in the class of direction `w`. -/
noncomputable def clsSum (w : Fin 3 → ℝ) (f : Fin 6 → Fin 6 → ℝ) : ℝ :=
  ∑ σ, ∑ h, if InClass w σ h then f σ h else 0

/-- The first-order coefficient of the dihedral angle of the incidence `(σ, h)`:
`Dh(q, c)`. -/
noncomputable def angC1 (m : Fin 3 → ℝ) (σ h : Fin 6) : ℝ :=
  Dh (incQ g m σ h, incC g m σ h)

/-- The second-order coefficient of the dihedral angle of the incidence `(σ, h)`:
`Dh(q, r) + ½ D²Dsq(q)(c, c)`. -/
noncomputable def angC2 (m : Fin 3 → ℝ) (σ h : Fin 6) : ℝ :=
  Dh (incQ g m σ h, incR g m σ h)
    + (1 / 2) * fderiv ℝ (fderiv ℝ Dsq) (incQ g m σ h) (incC g m σ h) (incC g m σ h)

/-- **The jet-level star identity (named hypothesis).** For the metric `g` at the point `m`
(its value, first and second derivatives), with the star of each of the seven edge classes of the
Kuhn triangulation taken at scale `ε`:

* `valid`: the Gram squared lengths of every incidence are admissible (`Valid`);
* `angle_sum`: the dihedral angles of the Gram star add up to `2π` in every class (a flat star);
* `first_order`: the `ε`-coefficient of the class angle sum vanishes;
* `curvature`: the hinge-length weighted `ε²`-coefficients, added over the seven classes, equal
  minus half the scalar curvature times `√det g`.

This is a statement about one jet. It does not mention a triangulation of a manifold or the
limit of the Regge sum. Its normal-coordinate slice is proved from `kuhn_regge_core`; the general
case is the content of the hypothesis. -/
structure JetStarCore (m : Fin 3 → ℝ) : Prop where
  /-- The Gram squared lengths are admissible. -/
  valid : ∀ σ h, Valid (incQ g m σ h)
  /-- The Gram star is flat: the dihedral angles in each class add up to `2π`. -/
  angle_sum : ∀ k, clsSum (dirs k) (fun σ h => Dsq (incQ g m σ h)) = 2 * π
  /-- The first-order coefficient of each class angle sum vanishes. -/
  first_order : ∀ k, clsSum (dirs k) (angC1 g m) = 0
  /-- The weighted second-order coefficients sum to `-(R/2) √det g`. -/
  curvature : ∑ k, √(edgeQ g m (dirs k)) * clsSum (dirs k) (angC2 g m)
    = -(scalarCurvature g m / 2) * √((g m).det)


/-- The dihedral angle is unchanged when the squared lengths are scaled by a positive number, if
the hinge is not degenerate. -/
theorem Dsq_smul {t : ℝ} (ht : 0 < t) {L : Fin 6 → ℝ} (hL : L 0 ≠ 0) : Dsq (t • L) = Dsq L := by
  unfold Dsq
  simpa only [Pi.smul_apply, smul_eq_mul] using dihSq_smul ht hL

/-- **Uniform expansion of the angle of a rescaled curve.** Same as `dihSq_curve_expansion`, for the
squared lengths `ε² (L + ε c + ε² ρ)` of an edge polynomial; scale invariance of the angle removes
the factor `ε²`, which needs the first coordinate of the perturbed curve to stay nonzero. -/
theorem dihSq_scaled_expansion {K : Set (Fin 6 → ℝ)} (hK : IsCompact K)
    (hKV : ∀ L ∈ K, Valid L) {a : ℝ} (ha : 0 < a) (hKa : ∀ L ∈ K, a ≤ L 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ M r : ℝ, 0 < r ∧ ∀ L ∈ K, ∀ c ρ : Fin 6 → ℝ, ‖c‖ ≤ B → ‖ρ‖ ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ r →
        |Dsq (ε ^ 2 • (L + ε • c + ε ^ 2 • ρ)) - Dsq L - ε * Dh (L, c)
          - ε ^ 2 * (Dh (L, ρ) + (1 / 2) * fderiv ℝ (fderiv ℝ Dsq) L c c)| ≤ M * ε ^ 3 := by
  obtain ⟨M, r, hr, hexp⟩ := dihSq_curve_expansion hK hKV hB
  refine ⟨M, min (min r 1) (a / (4 * B + 1)), lt_min (lt_min hr one_pos)
    (div_pos ha (by linarith)), fun L hL c ρ hc hρ ε hε hεr => ?_⟩
  have hεr1 : ε ≤ r := hεr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε1 : ε ≤ 1 := hεr.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε2 : ε ≤ a / (4 * B + 1) := hεr.trans (min_le_right _ _)
  have h2B : 2 * B * ε ≤ a / 2 := by
    rw [le_div_iff₀ (by linarith)] at hε2
    nlinarith
  have e := hexp L hL c ρ hc hρ ε hε hεr1
  have c0' := norm_le_pi_norm c 0
  have r0' := norm_le_pi_norm ρ 0
  rw [Real.norm_eq_abs] at c0' r0'
  have c0 : |c 0| ≤ B := c0'.trans hc
  have r0 : |ρ 0| ≤ B := r0'.trans hρ
  have q0 : a ≤ L 0 := hKa L hL
  have hεε : ε ^ 2 ≤ ε := by nlinarith
  have u1 : -(ε * B) ≤ ε * c 0 := by
    have := mul_le_mul_of_nonneg_left (abs_le.1 c0).1 hε.le
    linarith
  have u2 : -(ε * B) ≤ ε ^ 2 * ρ 0 := by
    have := mul_le_mul_of_nonneg_left (abs_le.1 r0).1 (pow_pos hε 2).le
    have := mul_le_mul_of_nonneg_right hεε hB
    linarith
  have hpos : (L + ε • c + ε ^ 2 • ρ) 0 ≠ 0 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine ne_of_gt ?_
    linarith
  rw [Dsq_smul (pow_pos hε 2) hpos]
  exact e

/-- **The class angle sum at scale `ε`, for abstract incidence data.** Let `q σ h`, `c σ h`, `ρ σ h`
be admissible squared lengths and two perturbation directions for each incidence. If the class
sum of the base angles is `2π` and the class sum of the first-order coefficients is `0`, then the
class sum of the angles of `ε² (q + ε c + ε² ρ)` is `2π + ε² c₂` up to `M ε³`, where `c₂` is the
class sum of the second-order coefficients. -/
theorem class_sum_expansion (w : Fin 3 → ℝ) (q c ρ : Fin 6 → Fin 6 → Fin 6 → ℝ)
    (hv : ∀ σ h, Valid (q σ h))
    (hsum : clsSum w (fun σ h => Dsq (q σ h)) = 2 * π)
    (hfirst : clsSum w (fun σ h => Dh (q σ h, c σ h)) = 0) :
    ∃ M r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      |clsSum w (fun σ h => Dsq (ε ^ 2 • (q σ h + ε • c σ h + ε ^ 2 • ρ σ h))) - 2 * π
        - ε ^ 2 * clsSum w (fun σ h => Dh (q σ h, ρ σ h)
          + (1 / 2) * fderiv ℝ (fderiv ℝ Dsq) (q σ h) (c σ h) (c σ h))| ≤ M * ε ^ 3 := by
  classical
  set A1 : Fin 6 → Fin 6 → ℝ := fun σ h => Dh (q σ h, c σ h) with hA1
  set A2 : Fin 6 → Fin 6 → ℝ := fun σ h => Dh (q σ h, ρ σ h)
    + (1 / 2) * fderiv ℝ (fderiv ℝ Dsq) (q σ h) (c σ h) (c σ h) with hA2
  have hK : IsCompact (Set.range (fun p : Fin 6 × Fin 6 => q p.1 p.2)) :=
    (Set.finite_range _).isCompact
  have hKV : ∀ L ∈ Set.range (fun p : Fin 6 × Fin 6 => q p.1 p.2), Valid L := by
    rintro _ ⟨p, rfl⟩
    exact hv p.1 p.2
  obtain ⟨x, hx⟩ := Finite.exists_min (fun p : Fin 6 × Fin 6 => q p.1 p.2 0)
  have ha : 0 < q x.1 x.2 0 := (hv x.1 x.2).1
  have hKa : ∀ L ∈ Set.range (fun p : Fin 6 × Fin 6 => q p.1 p.2), q x.1 x.2 0 ≤ L 0 := by
    rintro _ ⟨p, rfl⟩
    exact hx p
  obtain ⟨B, hB0, hBc, hBρ⟩ : ∃ B : ℝ, 0 ≤ B ∧ (∀ σ h, ‖c σ h‖ ≤ B) ∧ (∀ σ h, ‖ρ σ h‖ ≤ B) := by
    refine ⟨∑ p : Fin 6 × Fin 6, (‖c p.1 p.2‖ + ‖ρ p.1 p.2‖), Finset.sum_nonneg fun p _ => by positivity,
      fun σ h => ?_, fun σ h => ?_⟩
    · have := Finset.single_le_sum (f := fun p : Fin 6 × Fin 6 => ‖c p.1 p.2‖ + ‖ρ p.1 p.2‖)
        (fun p _ => by positivity) (Finset.mem_univ (σ, h))
      have := norm_nonneg (ρ σ h)
      simp only at *; linarith
    · have := Finset.single_le_sum (f := fun p : Fin 6 × Fin 6 => ‖c p.1 p.2‖ + ‖ρ p.1 p.2‖)
        (fun p _ => by positivity) (Finset.mem_univ (σ, h))
      have := norm_nonneg (c σ h)
      simp only at *; linarith
  obtain ⟨M, r, hr, hexp⟩ := dihSq_scaled_expansion hK hKV ha hKa hB0
  refine ⟨36 * |M|, r, hr, fun ε hε hεr => ?_⟩
  have hinc : ∀ σ h : Fin 6, |Dsq (ε ^ 2 • (q σ h + ε • c σ h + ε ^ 2 • ρ σ h)) - Dsq (q σ h)
      - ε * A1 σ h - ε ^ 2 * A2 σ h| ≤ |M| * ε ^ 3 := fun σ h =>
    (hexp (q σ h) ⟨(σ, h), rfl⟩ (c σ h) (ρ σ h) (hBc σ h) (hBρ σ h) ε hε hεr).trans
      (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity))
  have h1 := hsum
  have h2 : clsSum w A1 = 0 := hfirst
  set err : Fin 6 → Fin 6 → ℝ := fun σ h => Dsq (ε ^ 2 • (q σ h + ε • c σ h + ε ^ 2 • ρ σ h)) - Dsq (q σ h)
    - ε * A1 σ h - ε ^ 2 * A2 σ h with herr
  have hsplit : clsSum w (fun σ h => Dsq (ε ^ 2 • (q σ h + ε • c σ h + ε ^ 2 • ρ σ h))) =
      clsSum w (fun σ h => Dsq (q σ h)) + ε * clsSum w (A1)
        + ε ^ 2 * clsSum w (A2) + clsSum w err := by
    simp only [clsSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun h _ => ?_
    split_ifs
    · simp only [herr]; ring
    · simp
  have herrb : |clsSum w err| ≤ 36 * |M| * ε ^ 3 := by
    unfold clsSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ σ : Fin 6, |∑ h : Fin 6, (if InClass w σ h then err σ h else 0)|
        ≤ ∑ σ : Fin 6, ∑ h : Fin 6, |M| * ε ^ 3 :=
          Finset.sum_le_sum fun σ _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun h _ => by
              split_ifs
              · exact hinc σ h
              · simp; positivity)
      _ = 36 * |M| * ε ^ 3 := by simp; ring
  have : clsSum w (fun σ h => Dsq (ε ^ 2 • (q σ h + ε • c σ h + ε ^ 2 • ρ σ h))) - 2 * π
      - ε ^ 2 * clsSum w (A2) = clsSum w err := by
    rw [hsplit, h1, h2]; ring
  rw [this]
  exact herrb


/-- **The class angle sum at scale `ε`.** Under `JetStarCore`, for each edge class the sum of the
dihedral angles of the star at scale `ε` is `2π + ε² c₂` up to `M ε³`, where `c₂` is the sum of
`angC2` over the class. -/
theorem JetStarCore.class_expansion {m : Fin 3 → ℝ} (H : JetStarCore g m) (k : Fin 7) :
    ∃ M r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      |clsSum (dirs k) (fun σ h => Dsq (incLen g m ε σ h)) - 2 * π
        - ε ^ 2 * clsSum (dirs k) (angC2 g m)| ≤ M * ε ^ 3 := by
  obtain ⟨M, r, hr, h⟩ := class_sum_expansion (dirs k) (incQ g m) (incC g m) (incR g m)
    H.valid (H.angle_sum k) (H.first_order k)
  refine ⟨M, r, hr, fun ε hε hεr => ?_⟩
  have := h ε hε hεr
  simp only [incLen_eq]
  exact this

end Three

end Lightlike.Regge.Conv3
