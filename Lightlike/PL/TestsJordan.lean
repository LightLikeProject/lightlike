import Lightlike.PL.WeakJordanCircle
import Lightlike.PL.TestsK33

/-!
# Checks for the weak Jordan theorem

The unit circle in the plane is an instance of `weak_jordan`, and its complement is indeed not
connected. A circle together with a point of its inside shows a nonempty example of each side.
-/

open Set

namespace Lightlike.PL

/-- The unit circle in the plane, as a map `Circle → ℝ × ℝ`. -/
def unitCircle (z : Circle) : ℝ × ℝ := ((z : ℂ).re, (z : ℂ).im)

lemma unitCircle_continuous : Continuous unitCircle := by
  unfold unitCircle
  fun_prop

lemma unitCircle_injective : Function.Injective unitCircle := by
  intro z w h
  apply Circle.ext
  apply Complex.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- **Non-vacuity of `no_K33`.** The straight-line drawing of `K₃,₃ − (2, 2)` of `TestsK33`, with the
arcs `t ↦ u i + t • (v j - u i)`, is a drawing by continuous arcs, so the hypotheses of `no_K33` are
satisfiable for every edge set except the whole graph. -/
def contDrawing : ContDrawingOn TestsK33.E where
  u := TestsK33.drawing.u
  v := TestsK33.drawing.v
  γ i j t := TestsK33.drawing.u i + t • (TestsK33.drawing.v j - TestsK33.drawing.u i)
  cont i j _ := by fun_prop
  inj i j _ := by
    intro a _ b _ hab
    have h : a • (TestsK33.drawing.v j - TestsK33.drawing.u i) =
        b • (TestsK33.drawing.v j - TestsK33.drawing.u i) := by simpa using hab
    exact smul_left_injective ℝ (sub_ne_zero.2 (TestsK33.drawing.uv_ne i j).symm) h
  start i j _ := by simp
  stop i j _ := by simp
  disj i j i' j' h h' hne := by
    have e : ∀ i j, (i, j) ∈ TestsK33.E → (fun t : ℝ => TestsK33.drawing.u i +
        t • (TestsK33.drawing.v j - TestsK33.drawing.u i)) '' Icc 0 1 =
          chainSet (TestsK33.drawing.arc i j) := by
      intro i j hij
      have hseg : chainSet (TestsK33.drawing.arc i j) =
          segment ℝ (TestsK33.drawing.u i) (TestsK33.drawing.v j) := by
        have := TestsK33.mem_E hij
        fin_cases i <;> fin_cases j <;> simp_all [TestsK33.drawing, TestsK33.arc, TestsK33.chainSet2]
      rw [hseg, segment_eq_image']
    show (fun t : ℝ => TestsK33.drawing.u i + t • (TestsK33.drawing.v j - TestsK33.drawing.u i)) '' Icc 0 1 ∩
      (fun t : ℝ => TestsK33.drawing.u i' + t • (TestsK33.drawing.v j' - TestsK33.drawing.u i')) '' Icc 0 1 ⊆ _
    rw [e i j h, e i' j' h']
    exact TestsK33.drawing.disj i j i' j' h h' hne
  inj_u := TestsK33.drawing.inj_u
  inj_v := TestsK33.drawing.inj_v
  uv_ne := TestsK33.drawing.uv_ne

/-- Consistency with `no_K33`: a drawing with all nine edges would be a contradiction, while the one
without `(2, 2)` exists. -/
example : Nonempty (ContDrawingOn TestsK33.E) ∧ ¬ Nonempty (ContDrawingOn Set.univ) :=
  ⟨⟨contDrawing⟩, fun ⟨d⟩ => no_K33_on d⟩

/-- Non-vacuity: the hypotheses of `weak_jordan` are satisfied by the unit circle. -/
example : ¬ IsPreconnected (range unitCircle)ᶜ :=
  weak_jordan unitCircle_continuous unitCircle_injective

/-- A trust check: a map that is not injective does not satisfy the hypotheses (the constant map
sends the circle to a point, whose complement is connected). -/
example : ¬ Function.Injective (fun _ : Circle => ((0 : ℝ), (0 : ℝ))) := by
  intro h
  exact Circle.neg_ne_self 1 (h rfl).symm

end Lightlike.PL
