import Lightlike.GR.KerrJetEntries
import Lightlike.Regge.Conv3.JetCurvature

/-!
# The jet of the Kerr metric

The entries of `kerrMetric` as functions of `(r, θ)` with all their partial derivatives up to order two,
packaged by index (`gjet…`), the formulas for `pd` of the entries and of their first partials
(`pd_gjet…`, `pd_pd_kerrMetric`), which feed `Regge.Conv3.riemann_jet` for the Kerr Ricci tensor.

Gap row GE6, stage 3.
-/

open Matrix Real

noncomputable section

namespace Lightlike

/-- The entries of the Kerr metric after the derivatives `` in `(r, θ)`, by index. -/
def gjet0 (M a r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00 M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kgg03 M a r t
  else if i = 1 ∧ j = 1 then kgg11 M a r t
  else if i = 2 ∧ j = 2 then kgg22 M a r t
  else if i = 3 ∧ j = 3 then kgg33 M a r t
  else 0

/-- The entries of the Kerr metric after the derivatives `R` in `(r, θ)`, by index. -/
def gjetR (M a r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00R M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kgg03R M a r t
  else if i = 1 ∧ j = 1 then kgg11R M a r t
  else if i = 2 ∧ j = 2 then kgg22R M a r t
  else if i = 3 ∧ j = 3 then kgg33R M a r t
  else 0

/-- The entries of the Kerr metric after the derivatives `T` in `(r, θ)`, by index. -/
def gjetT (M a r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00T M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kgg03T M a r t
  else if i = 1 ∧ j = 1 then kgg11T M a r t
  else if i = 2 ∧ j = 2 then kgg22T M a r t
  else if i = 3 ∧ j = 3 then kgg33T M a r t
  else 0

/-- The entries of the Kerr metric after the derivatives `RR` in `(r, θ)`, by index. -/
def gjetRR (M a r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00RR M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kgg03RR M a r t
  else if i = 1 ∧ j = 1 then kgg11RR M a r t
  else if i = 2 ∧ j = 2 then kgg22RR M a r t
  else if i = 3 ∧ j = 3 then kgg33RR M a r t
  else 0

/-- The entries of the Kerr metric after the derivatives `RT` in `(r, θ)`, by index. -/
def gjetRT (M a r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00RT M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kgg03RT M a r t
  else if i = 1 ∧ j = 1 then kgg11RT M a r t
  else if i = 2 ∧ j = 2 then kgg22RT M a r t
  else if i = 3 ∧ j = 3 then kgg33RT M a r t
  else 0

/-- The entries of the Kerr metric after the derivatives `TR` in `(r, θ)`, by index. -/
def gjetTR (M a r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00TR M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kgg03TR M a r t
  else if i = 1 ∧ j = 1 then kgg11TR M a r t
  else if i = 2 ∧ j = 2 then kgg22TR M a r t
  else if i = 3 ∧ j = 3 then kgg33TR M a r t
  else 0

/-- The entries of the Kerr metric after the derivatives `TT` in `(r, θ)`, by index. -/
def gjetTT (M a r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00TT M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kgg03TT M a r t
  else if i = 1 ∧ j = 1 then kgg11TT M a r t
  else if i = 2 ∧ j = 2 then kgg22TT M a r t
  else if i = 3 ∧ j = 3 then kgg33TT M a r t
  else 0

/-- The Kerr metric entries are the `gjet0` entries. -/
theorem kerrMetric_eq_gjet (M a : ℝ) (z : Fin 4 → ℝ) (i j : Fin 4) :
    kerrMetric M a z i j = gjet0 M a (z 1) (z 2) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [kerrMetric, gjet0, kgg00, kgg03, kgg11, kgg22, kgg33, kerrS, kerrD]

/-- `pd` of the entries after the derivatives `` in `(r, θ)`. -/
theorem pd_gjet0 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (i j k : Fin 4) :
    pd k (fun z => gjet0 M a (z 1) (z 2) i j) y =
      if k = 1 then gjetR M a (y 1) (y 2) i j else if k = 2 then gjetT M a (y 1) (y 2) i j else 0 := by
  by_cases h00 : i = 0 ∧ j = 0
  · simp only [gjet0, gjetR, gjetT, h00, and_self, ite_true]
    exact pd_kgg00 M a hy k
  by_cases h03 : (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)
  · simp only [gjet0, gjetR, gjetT, h00, h03, ite_true, ite_false]
    exact pd_kgg03 M a hy k
  by_cases h11 : i = 1 ∧ j = 1
  · simp only [gjet0, gjetR, gjetT, h00, h03, h11, ite_true, ite_false]
    exact pd_kgg11 M a hy k
  by_cases h22 : i = 2 ∧ j = 2
  · simp only [gjet0, gjetR, gjetT, h00, h03, h11, h22, ite_true, ite_false]
    exact pd_kgg22 M a hy k
  by_cases h33 : i = 3 ∧ j = 3
  · simp only [gjet0, gjetR, gjetT, h00, h03, h11, h22, h33, ite_true, ite_false]
    exact pd_kgg33 M a hy k
  simp only [gjet0, gjetR, gjetT, h00, h03, h11, h22, h33, ite_false]
  simp [pd_const]

/-- `pd` of the entries after the derivatives `R` in `(r, θ)`. -/
theorem pd_gjetR (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (i j k : Fin 4) :
    pd k (fun z => gjetR M a (z 1) (z 2) i j) y =
      if k = 1 then gjetRR M a (y 1) (y 2) i j else if k = 2 then gjetRT M a (y 1) (y 2) i j else 0 := by
  by_cases h00 : i = 0 ∧ j = 0
  · simp only [gjetR, gjetRR, gjetRT, h00, and_self, ite_true]
    exact pd_kgg00R M a hy k
  by_cases h03 : (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)
  · simp only [gjetR, gjetRR, gjetRT, h00, h03, ite_true, ite_false]
    exact pd_kgg03R M a hy k
  by_cases h11 : i = 1 ∧ j = 1
  · simp only [gjetR, gjetRR, gjetRT, h00, h03, h11, ite_true, ite_false]
    exact pd_kgg11R M a hy k
  by_cases h22 : i = 2 ∧ j = 2
  · simp only [gjetR, gjetRR, gjetRT, h00, h03, h11, h22, ite_true, ite_false]
    exact pd_kgg22R M a hy k
  by_cases h33 : i = 3 ∧ j = 3
  · simp only [gjetR, gjetRR, gjetRT, h00, h03, h11, h22, h33, ite_true, ite_false]
    exact pd_kgg33R M a hy k
  simp only [gjetR, gjetRR, gjetRT, h00, h03, h11, h22, h33, ite_false]
  simp [pd_const]

/-- `pd` of the entries after the derivatives `T` in `(r, θ)`. -/
theorem pd_gjetT (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (i j k : Fin 4) :
    pd k (fun z => gjetT M a (z 1) (z 2) i j) y =
      if k = 1 then gjetTR M a (y 1) (y 2) i j else if k = 2 then gjetTT M a (y 1) (y 2) i j else 0 := by
  by_cases h00 : i = 0 ∧ j = 0
  · simp only [gjetT, gjetTR, gjetTT, h00, and_self, ite_true]
    exact pd_kgg00T M a hy k
  by_cases h03 : (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)
  · simp only [gjetT, gjetTR, gjetTT, h00, h03, ite_true, ite_false]
    exact pd_kgg03T M a hy k
  by_cases h11 : i = 1 ∧ j = 1
  · simp only [gjetT, gjetTR, gjetTT, h00, h03, h11, ite_true, ite_false]
    exact pd_kgg11T M a hy k
  by_cases h22 : i = 2 ∧ j = 2
  · simp only [gjetT, gjetTR, gjetTT, h00, h03, h11, h22, ite_true, ite_false]
    exact pd_kgg22T M a hy k
  by_cases h33 : i = 3 ∧ j = 3
  · simp only [gjetT, gjetTR, gjetTT, h00, h03, h11, h22, h33, ite_true, ite_false]
    exact pd_kgg33T M a hy k
  simp only [gjetT, gjetTR, gjetTT, h00, h03, h11, h22, h33, ite_false]
  simp [pd_const]

/-- **First partials of the Kerr metric.** -/
theorem pd_kerrMetric (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (i j k : Fin 4) :
    pd k (fun z => kerrMetric M a z i j) y =
      if k = 1 then gjetR M a (y 1) (y 2) i j else if k = 2 then gjetT M a (y 1) (y 2) i j else 0 := by
  simp only [kerrMetric_eq_gjet]
  exact pd_gjet0 M a hy i j k

/-- **Second partials of the Kerr metric**, `∂_μ ∂_ν g_{ij}`. -/
theorem pd_pd_kerrMetric (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (i j ν μ : Fin 4) :
    pd μ (fun w => pd ν (fun z => kerrMetric M a z i j) w) y =
      if μ = 1 then (if ν = 1 then gjetRR M a (y 1) (y 2) i j else if ν = 2 then gjetTR M a (y 1) (y 2) i j else 0)
      else if μ = 2 then (if ν = 1 then gjetRT M a (y 1) (y 2) i j else if ν = 2 then gjetTT M a (y 1) (y 2) i j else 0)
      else 0 := by
  have hev : (fun w => pd ν (fun z => kerrMetric M a z i j) w) =ᶠ[nhds y]
      fun w => if ν = 1 then gjetR M a (w 1) (w 2) i j else if ν = 2 then gjetT M a (w 1) (w 2) i j else 0 := by
    filter_upwards [(isOpen_kerrU M a).mem_nhds hy] with w hw
    exact pd_kerrMetric M a hw i j ν
  rw [pd_congr hev]
  by_cases h1 : ν = 1
  · simp only [h1, ite_true]
    exact pd_gjetR M a hy i j μ
  by_cases h2 : ν = 2
  · simp only [h1, h2, ite_true, ite_false]
    exact pd_gjetT M a hy i j μ
  simp only [h1, h2, ite_false]
  rw [pd_const]
  split_ifs <;> rfl

open Lightlike.Regge.Conv3 in
/-- The `(0, 0)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_00 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 0 0 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(0, 1)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_01 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 0 1 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(0, 2)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_02 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 0 2 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(0, 3)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_03 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 0 3 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(1, 0)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_10 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 1 0 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(1, 1)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_11 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 1 1 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(1, 2)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_12 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 1 2 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(1, 3)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_13 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 1 3 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(2, 0)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_20 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 2 0 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(2, 1)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_21 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 2 1 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(2, 2)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_22 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 2 2 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(2, 3)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_23 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 2 3 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(3, 0)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_30 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 3 0 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(3, 1)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_31 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 3 1 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(3, 2)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_32 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 3 2 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

open Lightlike.Regge.Conv3 in
/-- The `(3, 3)` component of the Kerr Ricci tensor vanishes. -/
theorem ricci_kerr_33 (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    ricci (kerrMetric M a) 3 3 y = 0 := by
  have hg := isCoordMetric_kerr M a
  have hinv := kerrMetric_inv M a hy
  have hD : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hy.2.1
  have hS : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := (kerrS_pos a hy.1).ne'
  have hsn : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hc := sin_sq_add_cos_sq (y 2)
  have hD' : y 1 * (y 1 - 2 * M) + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  simp only [ricci, riemann_jet hg hy, dChr, christoffel, pd_kerrMetric M a hy,
    pd_pd_kerrMetric M a hy, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg03R, kgg03T, kgg03RR, kgg03RT, kgg03TR, kgg03TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, gjetR, gjetT, gjetRR, gjetRT, gjetTR, gjetTT, kerrInv, kerrS, kerrD]
  try field_simp
  try (rw [show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]; ring)

/-- **The Ricci tensor of the Kerr metric vanishes** on `r > 0`, `Δ ≠ 0`, `0 < θ < π`: Kerr in
Boyer–Lindquist coordinates is Ricci-flat. Each of the 16 components is a rational identity in
`r, cos θ, sin θ, M, a` obtained from `riemann_jet` and the jet of the metric. -/
theorem ricci_kerr (M a : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (σ ν : Fin 4) :
    ricci (kerrMetric M a) σ ν y = 0 := by
  fin_cases σ <;> fin_cases ν
  · exact ricci_kerr_00 M a hy
  · exact ricci_kerr_01 M a hy
  · exact ricci_kerr_02 M a hy
  · exact ricci_kerr_03 M a hy
  · exact ricci_kerr_10 M a hy
  · exact ricci_kerr_11 M a hy
  · exact ricci_kerr_12 M a hy
  · exact ricci_kerr_13 M a hy
  · exact ricci_kerr_20 M a hy
  · exact ricci_kerr_21 M a hy
  · exact ricci_kerr_22 M a hy
  · exact ricci_kerr_23 M a hy
  · exact ricci_kerr_30 M a hy
  · exact ricci_kerr_31 M a hy
  · exact ricci_kerr_32 M a hy
  · exact ricci_kerr_33 M a hy

/-- **Kerr is a vacuum solution.** The Kerr metric in Boyer–Lindquist coordinates solves the vacuum
Einstein equations `G = 0` (cosmological constant `0`) on `r > 0`, `Δ ≠ 0`, `0 < θ < π`. -/
theorem kerr_isVacuumSolution (M a : ℝ) : IsVacuumSolution 0 (kerrMetric M a) (kerrU M a) :=
  ⟨isCoordMetric_kerr M a, fun y hy μ ν => by
    simp [einsteinTensor, scalarCurvature, ricci_kerr M a hy]⟩

end Lightlike
