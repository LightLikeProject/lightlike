import Lightlike.Regge.Conv3.ChartBase
/-!
# Closed forms at the hinges of tetrahedron 5 of the Kuhn cube (diagonal chart)

For the diagonal chart `diag(α, β, γ)` and a symmetric tensor `ric`, the hinge length times the first
variation of the dihedral angle (`ldth`) at the incidence (5, `h`) is the rational function `cf5h` of
`α, β, γ` and `ric`, for the six hinges `h = 0, …, 5`. Each is proved by exact algebra after
`inc_geom`.

## Main results

* `ldth_cf50`, …, `ldth_cf55`: the six closed forms.
-/

open Real
namespace Lightlike.Regge.Conv3

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (5, 0) of the diagonal chart is the closed form `cf50`. -/
theorem ldth_cf50 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 5 0 0) (dsq ![α, β, γ] 5 0 1)
      (dsq ![α, β, γ] 5 0 2) (dsq ![α, β, γ] 5 0 3) (dsq ![α, β, γ] 5 0 4)
      (dsq ![α, β, γ] 5 0 5)
      (dkds ric ![α, β, γ] 5 0 0) (dkds ric ![α, β, γ] 5 0 1)
      (dkds ric ![α, β, γ] 5 0 2) (dkds ric ![α, β, γ] 5 0 3)
      (dkds ric ![α, β, γ] 5 0 4) (dkds ric ![α, β, γ] 5 0 5) =
      cf50 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 5 0
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf50]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (5, 1) of the diagonal chart is the closed form `cf51`. -/
theorem ldth_cf51 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 5 1 0) (dsq ![α, β, γ] 5 1 1)
      (dsq ![α, β, γ] 5 1 2) (dsq ![α, β, γ] 5 1 3) (dsq ![α, β, γ] 5 1 4)
      (dsq ![α, β, γ] 5 1 5)
      (dkds ric ![α, β, γ] 5 1 0) (dkds ric ![α, β, γ] 5 1 1)
      (dkds ric ![α, β, γ] 5 1 2) (dkds ric ![α, β, γ] 5 1 3)
      (dkds ric ![α, β, γ] 5 1 4) (dkds ric ![α, β, γ] 5 1 5) =
      cf51 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 5 1
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf51]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (5, 2) of the diagonal chart is the closed form `cf52`. -/
theorem ldth_cf52 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 5 2 0) (dsq ![α, β, γ] 5 2 1)
      (dsq ![α, β, γ] 5 2 2) (dsq ![α, β, γ] 5 2 3) (dsq ![α, β, γ] 5 2 4)
      (dsq ![α, β, γ] 5 2 5)
      (dkds ric ![α, β, γ] 5 2 0) (dkds ric ![α, β, γ] 5 2 1)
      (dkds ric ![α, β, γ] 5 2 2) (dkds ric ![α, β, γ] 5 2 3)
      (dkds ric ![α, β, γ] 5 2 4) (dkds ric ![α, β, γ] 5 2 5) =
      cf52 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 5 2
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf52]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (5, 3) of the diagonal chart is the closed form `cf53`. -/
theorem ldth_cf53 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 5 3 0) (dsq ![α, β, γ] 5 3 1)
      (dsq ![α, β, γ] 5 3 2) (dsq ![α, β, γ] 5 3 3) (dsq ![α, β, γ] 5 3 4)
      (dsq ![α, β, γ] 5 3 5)
      (dkds ric ![α, β, γ] 5 3 0) (dkds ric ![α, β, γ] 5 3 1)
      (dkds ric ![α, β, γ] 5 3 2) (dkds ric ![α, β, γ] 5 3 3)
      (dkds ric ![α, β, γ] 5 3 4) (dkds ric ![α, β, γ] 5 3 5) =
      cf53 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 5 3
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf53]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (5, 4) of the diagonal chart is the closed form `cf54`. -/
theorem ldth_cf54 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 5 4 0) (dsq ![α, β, γ] 5 4 1)
      (dsq ![α, β, γ] 5 4 2) (dsq ![α, β, γ] 5 4 3) (dsq ![α, β, γ] 5 4 4)
      (dsq ![α, β, γ] 5 4 5)
      (dkds ric ![α, β, γ] 5 4 0) (dkds ric ![α, β, γ] 5 4 1)
      (dkds ric ![α, β, γ] 5 4 2) (dkds ric ![α, β, γ] 5 4 3)
      (dkds ric ![α, β, γ] 5 4 4) (dkds ric ![α, β, γ] 5 4 5) =
      cf54 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 5 4
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf54]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (5, 5) of the diagonal chart is the closed form `cf55`. -/
theorem ldth_cf55 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 5 5 0) (dsq ![α, β, γ] 5 5 1)
      (dsq ![α, β, γ] 5 5 2) (dsq ![α, β, γ] 5 5 3) (dsq ![α, β, γ] 5 5 4)
      (dsq ![α, β, γ] 5 5 5)
      (dkds ric ![α, β, γ] 5 5 0) (dkds ric ![α, β, γ] 5 5 1)
      (dkds ric ![α, β, γ] 5 5 2) (dkds ric ![α, β, γ] 5 5 3)
      (dkds ric ![α, β, γ] 5 5 4) (dkds ric ![α, β, γ] 5 5 5) =
      cf55 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 5 5
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf55]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

end Lightlike.Regge.Conv3
