import Lightlike.GR.AdSConformalBoundary.Robustness

/-!
# Group laws and the semidirect structure on null infinity (second route, stress tests)

Tier-3 robustness checks for gap row GE7. Everything is proved by passing to the parametrisation
`scriPoint u θ φ` of `I⁺`, an independent route to the group laws of `Dilation.lean` and `Rotation.lean`:

* time translations form a group acting on `I⁺` (`scriTimeShift_comp`, `scriTimeShift_zero`);
* the dilations normalise the translations: `D_c ∘ T_a = T_{c a} ∘ D_c` (`scriDilate_scriTimeShift`), and the
  rotations commute with both (`scriRotate_scriTimeShift`, `scriRotate_scriDilate`);
* rotations preserve the conformal factor (`scriFactor_scriRotate`);
* the sign of `c` matters: a dilation with `c > 0` preserves the order of retarded times, one with `c < 0` reverses it
  (`scriDilate_scriPoint_lt`, `scriDilate_scriPoint_gt`), so the time orientation of `I⁺` is not preserved when `c < 0`.
-/

open Real

noncomputable section

namespace Lightlike

/-- Time translations compose: `T_a ∘ T_b = T_{a+b}` on `I⁺`. -/
theorem scriTimeShift_comp (a b : ℝ) {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) :
    scriTimeShift a (scriTimeShift b p) = scriTimeShift (a + b) p := by
  rw [scriPlus_eq_range] at hp
  obtain ⟨x, rfl⟩ := hp
  rw [scriTimeShift_scriPoint, scriTimeShift_scriPoint, scriTimeShift_scriPoint, add_assoc, add_comm b a]

/-- The time translation by `0` is the identity on `I⁺`. -/
theorem scriTimeShift_zero {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) : scriTimeShift 0 p = p := by
  rw [scriPlus_eq_range] at hp
  obtain ⟨x, rfl⟩ := hp
  rw [scriTimeShift_scriPoint, add_zero]

/-- **Semidirect law**: `D_c ∘ T_a = T_{c a} ∘ D_c` on `I⁺` (dilations normalise translations). -/
theorem scriDilate_scriTimeShift (c a : ℝ) {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) :
    scriDilate c (scriTimeShift a p) = scriTimeShift (c * a) (scriDilate c p) := by
  rw [scriPlus_eq_range] at hp
  obtain ⟨x, rfl⟩ := hp
  rw [scriTimeShift_scriPoint, scriDilate_scriPoint, scriDilate_scriPoint, scriTimeShift_scriPoint, mul_add]

/-- Rotations commute with time translations on `I⁺`. -/
theorem scriRotate_scriTimeShift (α a : ℝ) {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) :
    scriRotate α (scriTimeShift a p) = scriTimeShift a (scriRotate α p) := by
  rw [scriPlus_eq_range] at hp
  obtain ⟨x, rfl⟩ := hp
  rw [scriTimeShift_scriPoint, scriRotate_scriPoint, scriRotate_scriPoint, scriTimeShift_scriPoint]

/-- Rotations commute with dilations on `I⁺`. -/
theorem scriRotate_scriDilate (α c : ℝ) {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) :
    scriRotate α (scriDilate c p) = scriDilate c (scriRotate α p) := by
  rw [scriPlus_eq_range] at hp
  obtain ⟨x, rfl⟩ := hp
  rw [scriDilate_scriPoint, scriRotate_scriPoint, scriRotate_scriPoint, scriDilate_scriPoint]

/-- Rotations preserve the conformal factor `scriFactor` (it only depends on the first two coordinates). -/
theorem scriFactor_scriRotate (α : ℝ) (p : Fin 4 → ℝ) : scriFactor (scriRotate α p) = scriFactor p := by
  simp [scriFactor, scriRotate]

/-- **Orientation, `c > 0`**: a positive dilation preserves the order of retarded times
(in the coordinate `ũ₊ = T + R`-independent first slot of `scriPoint`, which is strictly increasing in `u`). -/
theorem scriDilate_scriPoint_lt {c : ℝ} (hc : 0 < c) {u v : ℝ} (huv : u < v) (θ φ : ℝ) :
    scriDilate c (scriPoint u θ φ) 0 < scriDilate c (scriPoint v θ φ) 0 := by
  rw [scriDilate_scriPoint, scriDilate_scriPoint]
  have : arctan (c * u) < arctan (c * v) := Real.arctan_strictMono (by nlinarith)
  simp [scriPoint]
  linarith

/-- **Orientation, `c < 0`**: a negative dilation reverses the order of retarded times, so it does not preserve the
time orientation of `I⁺`. -/
theorem scriDilate_scriPoint_gt {c : ℝ} (hc : c < 0) {u v : ℝ} (huv : u < v) (θ φ : ℝ) :
    scriDilate c (scriPoint v θ φ) 0 < scriDilate c (scriPoint u θ φ) 0 := by
  rw [scriDilate_scriPoint, scriDilate_scriPoint]
  have : arctan (c * v) < arctan (c * u) := Real.arctan_strictMono (by nlinarith)
  simp [scriPoint]
  linarith

end Lightlike
