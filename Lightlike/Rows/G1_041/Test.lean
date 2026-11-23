import Mathlib
import Lightlike.Rows.G1_041.Tendsto

/-!
# Test of the cosmic no-hair theorem (G1-041)

The de Sitter model `H = 1`, `Λ = 3`, `ρ = p = σ² = R = 0` (the attractor) is a solution of the scalar
system, admissible, and the theorem returns `H → √(3/3) = 1`.
-/

open Filter Topology

namespace Lightlike
namespace Cosmology
namespace Bianchi

/-- De Sitter space solves the scalar system with `Λ = 3`. -/
lemma deSitter_isSolution :
    IsSolution 3 0 (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨fun t _ => by simpa using hasDerivAt_const t (1 : ℝ), fun t _ => by norm_num⟩

/-- De Sitter space is admissible. -/
lemma deSitter_isAdmissible :
    IsAdmissible 0 (fun _ => (0 : ℝ)) (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ _ => le_rfl, fun _ _ => by norm_num, fun _ _ => le_rfl, fun _ _ => le_rfl⟩

/-- The theorem applied to de Sitter: the limit of `H` is the de Sitter rate, here `1`. -/
example : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 (deSitterRate 3)) :=
  (no_hair_tendsto (by norm_num) deSitter_isSolution deSitter_isAdmissible (by norm_num)).1

end Bianchi
end Cosmology
end Lightlike
