import Lightlike.TuraevViro.CraneYetterSphere

/-!
# The 1024 cone cocycles of `∂Δ⁵` have weight `1` at `r = 3`

Kernel evaluation of `sphereM` and `sphereE` on the colourings `coneCol` of the ten triangles through the vertex `0`, in
sixteen pieces of 64 cases (the kernel evaluation of all 1024 cases at once needs more than 16 GB).
-/

open Finset Lightlike.Pentagon Lightlike.FourD Lightlike.FourD.Tests

namespace Lightlike.TV

/-- The cone cocycles with the colours `0, 0, 0, 0` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_0000 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 0 → Lightlike.PR.extS tri0 b {0, 1, 3} = 0 → Lightlike.PR.extS tri0 b {0, 1, 4} = 0 → Lightlike.PR.extS tri0 b {0, 1, 5} = 0 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `0, 0, 0, 1` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_0001 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 0 → Lightlike.PR.extS tri0 b {0, 1, 3} = 0 → Lightlike.PR.extS tri0 b {0, 1, 4} = 0 → Lightlike.PR.extS tri0 b {0, 1, 5} = 1 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `0, 0, 1, 0` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_0010 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 0 → Lightlike.PR.extS tri0 b {0, 1, 3} = 0 → Lightlike.PR.extS tri0 b {0, 1, 4} = 1 → Lightlike.PR.extS tri0 b {0, 1, 5} = 0 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `0, 0, 1, 1` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_0011 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 0 → Lightlike.PR.extS tri0 b {0, 1, 3} = 0 → Lightlike.PR.extS tri0 b {0, 1, 4} = 1 → Lightlike.PR.extS tri0 b {0, 1, 5} = 1 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `0, 1, 0, 0` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_0100 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 0 → Lightlike.PR.extS tri0 b {0, 1, 3} = 1 → Lightlike.PR.extS tri0 b {0, 1, 4} = 0 → Lightlike.PR.extS tri0 b {0, 1, 5} = 0 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `0, 1, 0, 1` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_0101 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 0 → Lightlike.PR.extS tri0 b {0, 1, 3} = 1 → Lightlike.PR.extS tri0 b {0, 1, 4} = 0 → Lightlike.PR.extS tri0 b {0, 1, 5} = 1 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `0, 1, 1, 0` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_0110 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 0 → Lightlike.PR.extS tri0 b {0, 1, 3} = 1 → Lightlike.PR.extS tri0 b {0, 1, 4} = 1 → Lightlike.PR.extS tri0 b {0, 1, 5} = 0 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `0, 1, 1, 1` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_0111 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 0 → Lightlike.PR.extS tri0 b {0, 1, 3} = 1 → Lightlike.PR.extS tri0 b {0, 1, 4} = 1 → Lightlike.PR.extS tri0 b {0, 1, 5} = 1 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `1, 0, 0, 0` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_1000 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 1 → Lightlike.PR.extS tri0 b {0, 1, 3} = 0 → Lightlike.PR.extS tri0 b {0, 1, 4} = 0 → Lightlike.PR.extS tri0 b {0, 1, 5} = 0 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `1, 0, 0, 1` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_1001 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 1 → Lightlike.PR.extS tri0 b {0, 1, 3} = 0 → Lightlike.PR.extS tri0 b {0, 1, 4} = 0 → Lightlike.PR.extS tri0 b {0, 1, 5} = 1 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `1, 0, 1, 0` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_1010 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 1 → Lightlike.PR.extS tri0 b {0, 1, 3} = 0 → Lightlike.PR.extS tri0 b {0, 1, 4} = 1 → Lightlike.PR.extS tri0 b {0, 1, 5} = 0 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `1, 0, 1, 1` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_1011 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 1 → Lightlike.PR.extS tri0 b {0, 1, 3} = 0 → Lightlike.PR.extS tri0 b {0, 1, 4} = 1 → Lightlike.PR.extS tri0 b {0, 1, 5} = 1 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `1, 1, 0, 0` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_1100 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 1 → Lightlike.PR.extS tri0 b {0, 1, 3} = 1 → Lightlike.PR.extS tri0 b {0, 1, 4} = 0 → Lightlike.PR.extS tri0 b {0, 1, 5} = 0 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `1, 1, 0, 1` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_1101 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 1 → Lightlike.PR.extS tri0 b {0, 1, 3} = 1 → Lightlike.PR.extS tri0 b {0, 1, 4} = 0 → Lightlike.PR.extS tri0 b {0, 1, 5} = 1 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `1, 1, 1, 0` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_1110 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 1 → Lightlike.PR.extS tri0 b {0, 1, 3} = 1 → Lightlike.PR.extS tri0 b {0, 1, 4} = 1 → Lightlike.PR.extS tri0 b {0, 1, 5} = 0 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

/-- The cone cocycles with the colours `1, 1, 1, 1` on the triangles `012, 013, 014, 015` have weight `1` (64 cases). -/
theorem sphere_weight_one_1111 :
    ∀ b ∈ tri0.pi (fun _ => range 2), Lightlike.PR.extS tri0 b {0, 1, 2} = 1 → Lightlike.PR.extS tri0 b {0, 1, 3} = 1 → Lightlike.PR.extS tri0 b {0, 1, 4} = 1 → Lightlike.PR.extS tri0 b {0, 1, 5} = 1 →
      WeightOne (Lightlike.PR.extS tri0 b) := by
  unfold WeightOne sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

lemma extS_tri0_lt {b : ∀ f ∈ tri0, ℕ} (hb : b ∈ tri0.pi (fun _ => range 2)) (f : Finset (Fin 6)) :
    Lightlike.PR.extS tri0 b f < 2 := by
  unfold Lightlike.PR.extS
  split_ifs with h
  · exact mem_range.1 (Finset.mem_pi.1 hb f h)
  · omega

/-- **Every cone cocycle of `∂Δ⁵` has weight `1` at `r = 3`**: for every choice of the colours `0, 1` on the ten triangles
through the vertex `0`, either `sphereM = 1` and `sphereE ≡ 0` or `sphereM = -1` and `sphereE ≡ 6` modulo `12`, i.e.
`sphereM · (q^{1/2})^{sphereE} = 1` (as `(q^{1/2})^{12} = 1`). The check is by kernel evaluation of the 1024 cases, in
sixteen pieces of 64. -/
theorem sphere_weight_one : ∀ b ∈ tri0.pi (fun _ => range 2), WeightOne (Lightlike.PR.extS tri0 b) := by
  intro b hb
  have l1 := extS_tri0_lt hb {0, 1, 2}
  have l2 := extS_tri0_lt hb {0, 1, 3}
  have l3 := extS_tri0_lt hb {0, 1, 4}
  have l4 := extS_tri0_lt hb {0, 1, 5}
  rcases (by omega : Lightlike.PR.extS tri0 b {0, 1, 2} = 0 ∨ Lightlike.PR.extS tri0 b {0, 1, 2} = 1) with h1 | h1 <;>
  rcases (by omega : Lightlike.PR.extS tri0 b {0, 1, 3} = 0 ∨ Lightlike.PR.extS tri0 b {0, 1, 3} = 1) with h2 | h2 <;>
  rcases (by omega : Lightlike.PR.extS tri0 b {0, 1, 4} = 0 ∨ Lightlike.PR.extS tri0 b {0, 1, 4} = 1) with h3 | h3 <;>
  rcases (by omega : Lightlike.PR.extS tri0 b {0, 1, 5} = 0 ∨ Lightlike.PR.extS tri0 b {0, 1, 5} = 1) with h4 | h4 <;>
  first
    | exact sphere_weight_one_0000 b hb h1 h2 h3 h4
    | exact sphere_weight_one_0001 b hb h1 h2 h3 h4
    | exact sphere_weight_one_0010 b hb h1 h2 h3 h4
    | exact sphere_weight_one_0011 b hb h1 h2 h3 h4
    | exact sphere_weight_one_0100 b hb h1 h2 h3 h4
    | exact sphere_weight_one_0101 b hb h1 h2 h3 h4
    | exact sphere_weight_one_0110 b hb h1 h2 h3 h4
    | exact sphere_weight_one_0111 b hb h1 h2 h3 h4
    | exact sphere_weight_one_1000 b hb h1 h2 h3 h4
    | exact sphere_weight_one_1001 b hb h1 h2 h3 h4
    | exact sphere_weight_one_1010 b hb h1 h2 h3 h4
    | exact sphere_weight_one_1011 b hb h1 h2 h3 h4
    | exact sphere_weight_one_1100 b hb h1 h2 h3 h4
    | exact sphere_weight_one_1101 b hb h1 h2 h3 h4
    | exact sphere_weight_one_1110 b hb h1 h2 h3 h4
    | exact sphere_weight_one_1111 b hb h1 h2 h3 h4

end Lightlike.TV
