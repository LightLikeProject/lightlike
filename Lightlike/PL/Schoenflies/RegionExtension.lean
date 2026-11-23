import Mathlib
import Lightlike.PL.Schoenflies.ConeExtension

/-!
# Extending a boundary homeomorphism over the regions of two simple polygons

Row G3-188, milestone PL5 (third pass).  Combining the disc form of the polygonal Schoenflies theorem
(`polygonal_schoenflies_disc`) with Alexander's cone extension (`circle_homeo_extends`): every
homeomorphism between the carriers of two simple polygons (with at least three vertices each) extends to a
homeomorphism between their closed regions (`boundary_homeo_extends`).  This is the gluing tool for the
polygonal Schoenflies theorem in the whole plane and for the approximation step of the topological theorem.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- A homeomorphism `R ≃ₜ D` of subsets of the plane that carries `S ⊆ R` exactly onto `T ⊆ D`
restricts to a homeomorphism `S ≃ₜ T`. -/
def restrictHomeo {R D S T : Set (ℝ × ℝ)} (e : R ≃ₜ D) (hS : S ⊆ R) (hT : T ⊆ D)
    (h : ∀ x : R, (x : ℝ × ℝ) ∈ S ↔ ((e x : D) : ℝ × ℝ) ∈ T) : S ≃ₜ T where
  toFun x := ⟨(e ⟨x, hS x.2⟩ : ℝ × ℝ), (h ⟨x, hS x.2⟩).1 x.2⟩
  invFun y := ⟨(e.symm ⟨y, hT y.2⟩ : ℝ × ℝ), (h _).2 (by simp)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  continuous_toFun :=
    ((continuous_subtype_val.comp (e.continuous.comp (continuous_inclusion hS)))).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp (e.symm.continuous.comp (continuous_inclusion hT)))).subtype_mk _

lemma restrictHomeo_apply {R D S T : Set (ℝ × ℝ)} (e : R ≃ₜ D) (hS : S ⊆ R) (hT : T ⊆ D)
    (h : ∀ x : R, (x : ℝ × ℝ) ∈ S ↔ ((e x : D) : ℝ × ℝ) ∈ T) (x : S) :
    ((restrictHomeo e hS hT h x : T) : ℝ × ℝ) = ((e ⟨x, hS x.2⟩ : D) : ℝ × ℝ) := rfl

lemma carrier_subset_region {n : ℕ} (p : Polygon n) : p.carrier ⊆ region p := subset_union_right

/-- **Boundary homeomorphisms extend over polygonal regions.**  For simple polygons `p`, `q` with at least
three vertices, every homeomorphism of the carriers extends to a homeomorphism of the closed regions. -/
theorem boundary_homeo_extends {n m : ℕ} [NeZero n] [NeZero m] {p : Polygon n} {q : Polygon m}
    (hn : 3 ≤ n) (hm : 3 ≤ m) (hp : p.IsSimple) (hq : q.IsSimple) (ψ : p.carrier ≃ₜ q.carrier) :
    ∃ E : region p ≃ₜ region q, ∀ (x : ℝ × ℝ) (hx : x ∈ p.carrier),
      ((E ⟨x, carrier_subset_region p hx⟩ : region q) : ℝ × ℝ) = ψ ⟨x, hx⟩ := by
  obtain ⟨ep, hep⟩ := polygonal_schoenflies_disc hn hp
  obtain ⟨eq', heq⟩ := polygonal_schoenflies_disc hm hq
  let hP : p.carrier ≃ₜ circ := restrictHomeo ep (carrier_subset_region p) circ_subset_disc hep
  let hQ : q.carrier ≃ₜ circ := restrictHomeo eq' (carrier_subset_region q) circ_subset_disc heq
  obtain ⟨Φ, hΦ⟩ := circle_homeo_extends (hP.symm.trans (ψ.trans hQ))
  refine ⟨ep.trans (Φ.trans eq'.symm), fun x hx => ?_⟩
  set xr : region p := ⟨x, carrier_subset_region p hx⟩ with hxr
  have h1 : ep xr = ⟨((hP ⟨x, hx⟩ : circ) : ℝ × ℝ), circ_subset_disc (hP ⟨x, hx⟩).2⟩ := rfl
  have h2 : ((Φ (ep xr) : disc) : ℝ × ℝ) = ((hQ (ψ ⟨x, hx⟩) : circ) : ℝ × ℝ) := by
    have := hΦ (hP ⟨x, hx⟩)
    rw [h1]
    rw [this]
    simp
  have h3 : eq'.symm (Φ (ep xr)) = ⟨ψ ⟨x, hx⟩, carrier_subset_region q (ψ ⟨x, hx⟩).2⟩ := by
    apply eq'.injective
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    rw [h2]
    rfl
  show ((eq'.symm (Φ (ep xr)) : region q) : ℝ × ℝ) = ψ ⟨x, hx⟩
  rw [h3]

end Lightlike.PL.Schoenflies
