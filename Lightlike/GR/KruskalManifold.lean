import Lightlike.GR.KruskalRegions
import Lightlike.Spacetime.OpenCoordMetric

/-!
# The Kruskal–Szekeres manifold in one global chart

Gap row G1-020, toward maximality. The chart `(T, X, θ, φ)` of the Kruskal metric omits the rotation axis
`θ = 0, π`; the Kruskal manifold is `{X² - T² > -1} × S²`. Since `ℝ × S²` is `ℝ³ ∖ {0}` by `(X, n) ↦ e^X n`, the
whole manifold is the open subset

`kruskalC = {(T, x) ∈ ℝ × ℝ³ : x ≠ 0, (log |x|)² - T² > -1}`

of `ℝ⁴`, with `X = log |x|`. In these coordinates the Kruskal metric
`h(r) (-dT² + dX²) + r² dΩ²`, `dX = x·dx/|x|²`, `dΩ² = (|dx|² - (x·dx)²/|x|²)/|x|²`, is

`g = -h dT² + ((h - r²)/|x|⁴) (x·dx)² + (r²/|x|²) |dx|²` (`kruskalCMetric`),

with `r = kG ((log |x|)² - T²)` (`krC`).

* `kruskalC_isLorentzian`: a smooth Lorentzian coordinate metric on all of `kruskalC`, with the frame
  `P = diag(√h, S)`, `S = (r/|x|) 1 + ((√h - r)/|x|³) x xᵀ`.
* `kruskalManifoldMetric`: the Lorentzian metric on the manifold `kruskalCOpen` (an open subset of `ℝ⁴`, the whole
  Kruskal manifold, both exteriors, the black and the white hole, every two-sphere complete).

This is the library's own global chart; the sources use `(T, X, θ, φ)`.
-/

open Matrix Real Set
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- `|x|²` for the spatial part `x = (y 1, y 2, y 3)`. -/
def rhoSq (y : Fin 4 → ℝ) : ℝ := y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2

/-- The Kruskal coordinate `X = log |x|` minus-squared combination `X² - T²`. -/
def sC (y : Fin 4 → ℝ) : ℝ := ((1 / 2) * log (rhoSq y)) ^ 2 - y 0 ^ 2

/-- The radius `r = kG (X² - T²)` in the global chart. -/
def krC (y : Fin 4 → ℝ) : ℝ := kG M (sC y)

/-- The domain of the global chart: `x ≠ 0` and `X² - T² > -1`. -/
def kruskalC : Set (Fin 4 → ℝ) := {y | 0 < rhoSq y ∧ -1 < sC y}

/-- **The Kruskal metric in the global chart** `(T, x)`:
`-h dT² + ((h - r²)/|x|⁴) (x·dx)² + (r²/|x|²) |dx|²`. -/
def kruskalCMetric (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-kh M (krC M y), 0, 0, 0;
     0, (kh M (krC M y) - krC M y ^ 2) / rhoSq y ^ 2 * (y 1 * y 1) + krC M y ^ 2 / rhoSq y,
        (kh M (krC M y) - krC M y ^ 2) / rhoSq y ^ 2 * (y 1 * y 2),
        (kh M (krC M y) - krC M y ^ 2) / rhoSq y ^ 2 * (y 1 * y 3);
     0, (kh M (krC M y) - krC M y ^ 2) / rhoSq y ^ 2 * (y 2 * y 1),
        (kh M (krC M y) - krC M y ^ 2) / rhoSq y ^ 2 * (y 2 * y 2) + krC M y ^ 2 / rhoSq y,
        (kh M (krC M y) - krC M y ^ 2) / rhoSq y ^ 2 * (y 2 * y 3);
     0, (kh M (krC M y) - krC M y ^ 2) / rhoSq y ^ 2 * (y 3 * y 1),
        (kh M (krC M y) - krC M y ^ 2) / rhoSq y ^ 2 * (y 3 * y 2),
        (kh M (krC M y) - krC M y ^ 2) / rhoSq y ^ 2 * (y 3 * y 3) + krC M y ^ 2 / rhoSq y]

lemma contDiff_rhoSq : ContDiff ℝ ∞ rhoSq := by
  unfold rhoSq; fun_prop

lemma contDiffOn_sC : ContDiffOn ℝ ∞ sC {y | 0 < rhoSq y} := by
  have h1 : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => log (rhoSq y)) {y | 0 < rhoSq y} :=
    fun y hy => ((contDiffAt_log.2 (ne_of_gt hy)).comp y contDiff_rhoSq.contDiffAt).contDiffWithinAt
  have h0 : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 0 ^ 2 := by fun_prop
  exact ((contDiffOn_const.mul h1).pow 2).sub h0.contDiffOn

lemma isOpen_kruskalC : IsOpen kruskalC := by
  have h1 : IsOpen {y : Fin 4 → ℝ | 0 < rhoSq y} := isOpen_lt continuous_const contDiff_rhoSq.continuous
  have h2 := contDiffOn_sC.continuousOn.isOpen_inter_preimage h1 (isOpen_Ioi (a := (-1 : ℝ)))
  exact h2

lemma krC_pos (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalC) : 0 < krC M y := kG_pos M hM hy.2

lemma contDiffOn_krC (hM : 0 < M) : ContDiffOn ℝ ∞ (krC M) kruskalC := fun y hy =>
  ((contDiffAt_kG M hM hy.2).comp_contDiffWithinAt y
    ((contDiffOn_sC.mono fun z hz => hz.1) y hy))

lemma contDiffOn_khC (hM : 0 < M) : ContDiffOn ℝ ∞ (fun y => kh M (krC M y)) kruskalC := fun y hy =>
  ((contDiffAt_kh M hM (krC_pos M hM hy)).comp_contDiffWithinAt y (contDiffOn_krC M hM y hy))

/-- The frame `P = diag(√h, S)`, `S = f 1 + e x xᵀ`, with `f = r/|x|`, `e = (√h - r)/|x|³`. -/
def kruskalCFrame (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![√(kh M (krC M y)), 0, 0, 0;
     0, (√(kh M (krC M y)) - krC M y) / √(rhoSq y) ^ 3 * (y 1 * y 1) + krC M y / √(rhoSq y),
        (√(kh M (krC M y)) - krC M y) / √(rhoSq y) ^ 3 * (y 1 * y 2),
        (√(kh M (krC M y)) - krC M y) / √(rhoSq y) ^ 3 * (y 1 * y 3);
     0, (√(kh M (krC M y)) - krC M y) / √(rhoSq y) ^ 3 * (y 2 * y 1),
        (√(kh M (krC M y)) - krC M y) / √(rhoSq y) ^ 3 * (y 2 * y 2) + krC M y / √(rhoSq y),
        (√(kh M (krC M y)) - krC M y) / √(rhoSq y) ^ 3 * (y 2 * y 3);
     0, (√(kh M (krC M y)) - krC M y) / √(rhoSq y) ^ 3 * (y 3 * y 1),
        (√(kh M (krC M y)) - krC M y) / √(rhoSq y) ^ 3 * (y 3 * y 2),
        (√(kh M (krC M y)) - krC M y) / √(rhoSq y) ^ 3 * (y 3 * y 3) + krC M y / √(rhoSq y)]

/-- The algebra behind the frame: for `c = e² |x|² + 2 e f`, `d = f²`, `s² = h`. -/
lemma frame_identity (h c d e f s y1 y2 y3 : ℝ) (hc : c = e ^ 2 * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) + 2 * e * f)
    (hd : d = f ^ 2) (hs : s ^ 2 = h) :
    (!![-h, 0, 0, 0;
       0, c * (y1 * y1) + d, c * (y1 * y2), c * (y1 * y3);
       0, c * (y2 * y1), c * (y2 * y2) + d, c * (y2 * y3);
       0, c * (y3 * y1), c * (y3 * y2), c * (y3 * y3) + d] : Matrix (Fin 4) (Fin 4) ℝ) =
      (!![s, 0, 0, 0;
         0, e * (y1 * y1) + f, e * (y1 * y2), e * (y1 * y3);
         0, e * (y2 * y1), e * (y2 * y2) + f, e * (y2 * y3);
         0, e * (y3 * y1), e * (y3 * y2), e * (y3 * y3) + f] : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * eta 4 *
        !![s, 0, 0, 0;
         0, e * (y1 * y1) + f, e * (y1 * y2), e * (y1 * y3);
         0, e * (y2 * y1), e * (y2 * y2) + f, e * (y2 * y3);
         0, e * (y3 * y1), e * (y3 * y2), e * (y3 * y3) + f] := by
  subst hc hd hs
  rw [eta]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, etaDiag, Matrix.diagonal_apply] <;> ring

/-- The metric is `Pᵀ η P` for the frame `P`. -/
lemma kruskalCMetric_eq_frame (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalC) :
    kruskalCMetric M y = (kruskalCFrame M y)ᵀ * eta 4 * kruskalCFrame M y := by
  have hr := krC_pos M hM hy
  have hh : 0 < kh M (krC M y) := kh_pos M hM hr
  have hq : 0 < rhoSq y := hy.1
  have hsum : y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 = rhoSq y := rfl
  have hc : (kh M (krC M y) - krC M y ^ 2) / rhoSq y ^ 2 =
      ((√(kh M (krC M y)) - krC M y) / √(rhoSq y) ^ 3) ^ 2 * (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) +
        2 * ((√(kh M (krC M y)) - krC M y) / √(rhoSq y) ^ 3) * (krC M y / √(rhoSq y)) := by
    rw [hsum]
    obtain ⟨sa, hsa0, hkh⟩ : ∃ sa : ℝ, 0 < sa ∧ kh M (krC M y) = sa ^ 2 :=
      ⟨√(kh M (krC M y)), Real.sqrt_pos.2 hh, (Real.sq_sqrt hh.le).symm⟩
    obtain ⟨ρ, hρ0, hqe⟩ : ∃ ρ : ℝ, 0 < ρ ∧ rhoSq y = ρ ^ 2 :=
      ⟨√(rhoSq y), Real.sqrt_pos.2 hq, (Real.sq_sqrt hq.le).symm⟩
    rw [hkh, hqe, Real.sqrt_sq hsa0.le, Real.sqrt_sq hρ0.le]
    field_simp
    ring
  have hd : krC M y ^ 2 / rhoSq y = (krC M y / √(rhoSq y)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hq.le]
  exact frame_identity _ _ _ _ _ _ _ _ _ hc hd (Real.sq_sqrt hh.le)

/-- The determinant of the frame is `√h · f² · (f + e |x|²) = √h · r² · √h / |x|³ ≠ 0`. -/
lemma isUnit_det_kruskalCFrame (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalC) :
    IsUnit (kruskalCFrame M y).det := by
  have hr := krC_pos M hM hy
  have hh : 0 < kh M (krC M y) := kh_pos M hM hr
  have hq : 0 < rhoSq y := hy.1
  have hsa0 : 0 < √(kh M (krC M y)) := Real.sqrt_pos.2 hh
  have hρ0 : 0 < √(rhoSq y) := Real.sqrt_pos.2 hq
  have hρ : √(rhoSq y) ^ 2 = y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 := Real.sq_sqrt hq.le
  set sa := √(kh M (krC M y))
  set ρ := √(rhoSq y)
  set e : ℝ := (sa - krC M y) / ρ ^ 3 with he
  set f : ℝ := krC M y / ρ with hf
  have hdet : (kruskalCFrame M y).det = sa * (f ^ 2 * (f + e * (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2))) := by
    simp only [kruskalCFrame, ← he, ← hf]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    ring
  rw [hdet, ← hρ]
  have h1 : f + e * ρ ^ 2 = sa / ρ := by
    rw [he, hf]; field_simp; ring
  rw [h1]
  have hf0 : 0 < f := div_pos hr hρ0
  exact (by positivity : sa * (f ^ 2 * (sa / ρ)) ≠ 0).isUnit

/-- **The Kruskal metric in the global chart is a coordinate metric on the whole Kruskal manifold.** -/
theorem isCoordMetric_kruskalC (hM : 0 < M) : IsCoordMetric (kruskalCMetric M) kruskalC where
  isOpen := isOpen_kruskalC
  symm := fun y _ => by
    ext i j
    show kruskalCMetric M y j i = kruskalCMetric M y i j
    fin_cases i <;> fin_cases j <;> first | rfl | simp [kruskalCMetric, mul_comm]
  isUnit_det := fun y hy => by
    rw [kruskalCMetric_eq_frame M hM hy, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have h1 := isUnit_det_kruskalCFrame M hM hy
    have h2 : IsUnit (eta 4).det := by
      rw [eta, Matrix.det_diagonal]
      exact (Finset.prod_ne_zero_iff.2 fun i _ => etaDiag_ne_zero i).isUnit
    exact (h1.mul h2).mul h1
  smooth := fun i j => by
    have hA := contDiffOn_khC M hM
    have hB : ContDiffOn ℝ ∞ (fun y => krC M y ^ 2) kruskalC := (contDiffOn_krC M hM).pow 2
    have hq : ContDiffOn ℝ ∞ rhoSq kruskalC := contDiff_rhoSq.contDiffOn
    have hq0 : ∀ y ∈ kruskalC, rhoSq y ≠ 0 := fun y hy => ne_of_gt hy.1
    have hq20 : ∀ y ∈ kruskalC, rhoSq y ^ 2 ≠ 0 := fun y hy => pow_ne_zero 2 (hq0 y hy)
    have hc : ContDiffOn ℝ ∞ (fun y => (kh M (krC M y) - krC M y ^ 2) / rhoSq y ^ 2) kruskalC :=
      (hA.sub hB).div (hq.pow 2) hq20
    have hd : ContDiffOn ℝ ∞ (fun y => krC M y ^ 2 / rhoSq y) kruskalC := hB.div hq hq0
    have hy : ∀ a b : Fin 4, ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => y a * y b) kruskalC := fun a b =>
      (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y a * y b).contDiffOn
    fin_cases i <;> fin_cases j <;> simp only [kruskalCMetric] <;>
      first
        | exact contDiffOn_const
        | exact hA.neg
        | exact (hc.mul (hy _ _)).add hd
        | exact hc.mul (hy _ _)
        | (simp; first
            | exact contDiffOn_const
            | exact hA.neg
            | exact (hc.mul (hy _ _)).add hd
            | exact hc.mul (hy _ _))

/-- **The Kruskal metric in the global chart is Lorentzian on the whole Kruskal manifold.** -/
theorem kruskalC_isLorentzian (hM : 0 < M) : IsLorentzianCoordMetric (kruskalCMetric M) kruskalC :=
  ⟨isCoordMetric_kruskalC M hM, fun y hy =>
    ⟨kruskalCFrame M y, isUnit_det_kruskalCFrame M hM hy, kruskalCMetric_eq_frame M hM hy⟩⟩

/-- The Kruskal manifold `{X² - T² > -1} × S²` as an open subset of `ℝ⁴`. -/
def kruskalCOpen : TopologicalSpace.Opens (Fin 4 → ℝ) := ⟨kruskalC, isOpen_kruskalC⟩

/-- **The Kruskal–Szekeres spacetime**: the Lorentzian metric on the whole Kruskal manifold. -/
def kruskalManifoldMetric (hM : 0 < M) : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) kruskalCOpen 4 :=
  openMetric kruskalCOpen (kruskalCMetric M) (kruskalC_isLorentzian M hM)

end Lightlike
