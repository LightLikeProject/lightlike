import Lightlike.Regge.Conv3.ChartBase
/-!
# Closed forms at the hinges of tetrahedron 0 of the Kuhn cube (diagonal chart)

For the diagonal chart `diag(α, β, γ)` and a symmetric tensor `ric`, the hinge length times the first
variation of the dihedral angle (`ldth`) at the incidence (0, `h`) is the rational function `cf0h` of
`α, β, γ` and `ric`, for the six hinges `h = 0, …, 5`. Each is proved by exact algebra after
`inc_geom`.

## Main results

* `ldth_cf00`, …, `ldth_cf05`: the six closed forms.
-/

open Real
namespace Lightlike.Regge.Conv3

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (0, 0) of the diagonal chart is the closed form `cf00`. -/
theorem ldth_cf00 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 0 0 0) (dsq ![α, β, γ] 0 0 1)
      (dsq ![α, β, γ] 0 0 2) (dsq ![α, β, γ] 0 0 3) (dsq ![α, β, γ] 0 0 4)
      (dsq ![α, β, γ] 0 0 5)
      (dkds ric ![α, β, γ] 0 0 0) (dkds ric ![α, β, γ] 0 0 1)
      (dkds ric ![α, β, γ] 0 0 2) (dkds ric ![α, β, γ] 0 0 3)
      (dkds ric ![α, β, γ] 0 0 4) (dkds ric ![α, β, γ] 0 0 5) =
      cf00 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 0 0
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf00]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (0, 1) of the diagonal chart is the closed form `cf01`. -/
theorem ldth_cf01 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 0 1 0) (dsq ![α, β, γ] 0 1 1)
      (dsq ![α, β, γ] 0 1 2) (dsq ![α, β, γ] 0 1 3) (dsq ![α, β, γ] 0 1 4)
      (dsq ![α, β, γ] 0 1 5)
      (dkds ric ![α, β, γ] 0 1 0) (dkds ric ![α, β, γ] 0 1 1)
      (dkds ric ![α, β, γ] 0 1 2) (dkds ric ![α, β, γ] 0 1 3)
      (dkds ric ![α, β, γ] 0 1 4) (dkds ric ![α, β, γ] 0 1 5) =
      cf01 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 0 1
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf01]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (0, 2) of the diagonal chart is the closed form `cf02`. -/
theorem ldth_cf02 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 0 2 0) (dsq ![α, β, γ] 0 2 1)
      (dsq ![α, β, γ] 0 2 2) (dsq ![α, β, γ] 0 2 3) (dsq ![α, β, γ] 0 2 4)
      (dsq ![α, β, γ] 0 2 5)
      (dkds ric ![α, β, γ] 0 2 0) (dkds ric ![α, β, γ] 0 2 1)
      (dkds ric ![α, β, γ] 0 2 2) (dkds ric ![α, β, γ] 0 2 3)
      (dkds ric ![α, β, γ] 0 2 4) (dkds ric ![α, β, γ] 0 2 5) =
      cf02 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 0 2
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf02]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (0, 3) of the diagonal chart is the closed form `cf03`. -/
theorem ldth_cf03 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 0 3 0) (dsq ![α, β, γ] 0 3 1)
      (dsq ![α, β, γ] 0 3 2) (dsq ![α, β, γ] 0 3 3) (dsq ![α, β, γ] 0 3 4)
      (dsq ![α, β, γ] 0 3 5)
      (dkds ric ![α, β, γ] 0 3 0) (dkds ric ![α, β, γ] 0 3 1)
      (dkds ric ![α, β, γ] 0 3 2) (dkds ric ![α, β, γ] 0 3 3)
      (dkds ric ![α, β, γ] 0 3 4) (dkds ric ![α, β, γ] 0 3 5) =
      cf03 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 0 3
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf03]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (0, 4) of the diagonal chart is the closed form `cf04`. -/
theorem ldth_cf04 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 0 4 0) (dsq ![α, β, γ] 0 4 1)
      (dsq ![α, β, γ] 0 4 2) (dsq ![α, β, γ] 0 4 3) (dsq ![α, β, γ] 0 4 4)
      (dsq ![α, β, γ] 0 4 5)
      (dkds ric ![α, β, γ] 0 4 0) (dkds ric ![α, β, γ] 0 4 1)
      (dkds ric ![α, β, γ] 0 4 2) (dkds ric ![α, β, γ] 0 4 3)
      (dkds ric ![α, β, γ] 0 4 4) (dkds ric ![α, β, γ] 0 4 5) =
      cf04 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 0 4
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf04]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `ℓ dθ` at the incidence (0, 5) of the diagonal chart is the closed form `cf05`. -/
theorem ldth_cf05 (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ldth (α * β * γ / 6) (dsq ![α, β, γ] 0 5 0) (dsq ![α, β, γ] 0 5 1)
      (dsq ![α, β, γ] 0 5 2) (dsq ![α, β, γ] 0 5 3) (dsq ![α, β, γ] 0 5 4)
      (dsq ![α, β, γ] 0 5 5)
      (dkds ric ![α, β, γ] 0 5 0) (dkds ric ![α, β, γ] 0 5 1)
      (dkds ric ![α, β, γ] 0 5 2) (dkds ric ![α, β, γ] 0 5 3)
      (dkds ric ![α, β, γ] 0 5 4) (dkds ric ![α, β, γ] 0 5 5) =
      cf05 α β γ ric := by
  have g := inc_geom α β γ hα hβ hγ 0 5
  apply ldth_eq_of g.2.1.ne' g.2.2.1.ne' (by positivity)
  have h1 : α ^ 2 + β ^ 2 ≠ 0 := by positivity
  have h2 : α ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h3 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h4 : α ^ 2 + β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hγ' := hγ.ne'
  simp only [dsq, dkds, dpos, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal, Nn,
    Nn', Pp, Pp', sqd, cf05]
  simp [Fin.sum_univ_three]
  try simp only [hs 1 0, hs 2 0, hs 2 1]
  ring_nf
  field_simp
  try ring

end Lightlike.Regge.Conv3
