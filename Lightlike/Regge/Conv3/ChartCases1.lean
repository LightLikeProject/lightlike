import Lightlike.Regge.Conv3.ChartBase
open Real
namespace Lightlike.Regge.Conv3

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (1, 0) of the diagonal chart is the closed form `cf10`. -/
theorem ldth_cf10 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 1 0 0) (dsq ![α, β, γ] 1 0 1)
      (dsq ![α, β, γ] 1 0 2) (dsq ![α, β, γ] 1 0 3) (dsq ![α, β, γ] 1 0 4)
      (dsq ![α, β, γ] 1 0 5)
      (dkds ric ![α, β, γ] 1 0 0) (dkds ric ![α, β, γ] 1 0 1)
      (dkds ric ![α, β, γ] 1 0 2) (dkds ric ![α, β, γ] 1 0 3)
      (dkds ric ![α, β, γ] 1 0 4) (dkds ric ![α, β, γ] 1 0 5) =
      cf10 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 1 0
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf10]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (1, 1) of the diagonal chart is the closed form `cf11`. -/
theorem ldth_cf11 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 1 1 0) (dsq ![α, β, γ] 1 1 1)
      (dsq ![α, β, γ] 1 1 2) (dsq ![α, β, γ] 1 1 3) (dsq ![α, β, γ] 1 1 4)
      (dsq ![α, β, γ] 1 1 5)
      (dkds ric ![α, β, γ] 1 1 0) (dkds ric ![α, β, γ] 1 1 1)
      (dkds ric ![α, β, γ] 1 1 2) (dkds ric ![α, β, γ] 1 1 3)
      (dkds ric ![α, β, γ] 1 1 4) (dkds ric ![α, β, γ] 1 1 5) =
      cf11 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 1 1
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf11]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (1, 2) of the diagonal chart is the closed form `cf12`. -/
theorem ldth_cf12 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 1 2 0) (dsq ![α, β, γ] 1 2 1)
      (dsq ![α, β, γ] 1 2 2) (dsq ![α, β, γ] 1 2 3) (dsq ![α, β, γ] 1 2 4)
      (dsq ![α, β, γ] 1 2 5)
      (dkds ric ![α, β, γ] 1 2 0) (dkds ric ![α, β, γ] 1 2 1)
      (dkds ric ![α, β, γ] 1 2 2) (dkds ric ![α, β, γ] 1 2 3)
      (dkds ric ![α, β, γ] 1 2 4) (dkds ric ![α, β, γ] 1 2 5) =
      cf12 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 1 2
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf12]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (1, 3) of the diagonal chart is the closed form `cf13`. -/
theorem ldth_cf13 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 1 3 0) (dsq ![α, β, γ] 1 3 1)
      (dsq ![α, β, γ] 1 3 2) (dsq ![α, β, γ] 1 3 3) (dsq ![α, β, γ] 1 3 4)
      (dsq ![α, β, γ] 1 3 5)
      (dkds ric ![α, β, γ] 1 3 0) (dkds ric ![α, β, γ] 1 3 1)
      (dkds ric ![α, β, γ] 1 3 2) (dkds ric ![α, β, γ] 1 3 3)
      (dkds ric ![α, β, γ] 1 3 4) (dkds ric ![α, β, γ] 1 3 5) =
      cf13 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 1 3
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf13]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (1, 4) of the diagonal chart is the closed form `cf14`. -/
theorem ldth_cf14 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 1 4 0) (dsq ![α, β, γ] 1 4 1)
      (dsq ![α, β, γ] 1 4 2) (dsq ![α, β, γ] 1 4 3) (dsq ![α, β, γ] 1 4 4)
      (dsq ![α, β, γ] 1 4 5)
      (dkds ric ![α, β, γ] 1 4 0) (dkds ric ![α, β, γ] 1 4 1)
      (dkds ric ![α, β, γ] 1 4 2) (dkds ric ![α, β, γ] 1 4 3)
      (dkds ric ![α, β, γ] 1 4 4) (dkds ric ![α, β, γ] 1 4 5) =
      cf14 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 1 4
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf14]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (1, 5) of the diagonal chart is the closed form `cf15`. -/
theorem ldth_cf15 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 1 5 0) (dsq ![α, β, γ] 1 5 1)
      (dsq ![α, β, γ] 1 5 2) (dsq ![α, β, γ] 1 5 3) (dsq ![α, β, γ] 1 5 4)
      (dsq ![α, β, γ] 1 5 5)
      (dkds ric ![α, β, γ] 1 5 0) (dkds ric ![α, β, γ] 1 5 1)
      (dkds ric ![α, β, γ] 1 5 2) (dkds ric ![α, β, γ] 1 5 3)
      (dkds ric ![α, β, γ] 1 5 4) (dkds ric ![α, β, γ] 1 5 5) =
      cf15 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 1 5
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf15]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

end Lightlike.Regge.Conv3
