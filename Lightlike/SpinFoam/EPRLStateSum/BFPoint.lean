import Lightlike.SpinFoam.EPRL

/-!
# The EPRL state sum at the formal BF point `γ = 1`

At `γ = 1` the EPRL labels of a doubled spin `J` are `(n, m) = (J, 0)`: the anti-self-dual spin is
trivial. This is the "formal BF point" of `Lightlike/Spin4/Vertex.lean` (`eprlVertex_zero_right`);
whether the sources call it the BF point has not been checked against their text.

## Main results

* `eprlN_one`, `eprlM_one`, `faceAmp_one`, `eprlAdmissible_one`: the labels, the face amplitude
  `J + 1` and the admissibility of every spin at `γ = 1`.
* `simpE_one`: the EPRL vertex at `γ = 1` is the SU(2) 15j contraction `fifteenJSimplex` of the
  triangle spins and tetrahedron labels, in the order of the sorted vertices.
-/

open Finset Lightlike.Spin4 Lightlike.FourD Lightlike.Recoupling

namespace Lightlike.SpinFoam.EPRL

variable {V : Type*} [LinearOrder V]

/-- At `γ = 1` the self-dual label of the doubled spin `J` is `J`. -/
theorem eprlN_one (J : ℕ) : eprlN 1 J = J := by
  have : |(1 : ℝ) + 1| * J / 2 = J := by
    rw [abs_of_pos (by norm_num)]; ring
  rw [eprlN, this, Nat.floor_natCast]

/-- At `γ = 1` the anti-self-dual label is `0`. -/
theorem eprlM_one (J : ℕ) : eprlM 1 J = 0 := by
  simp [eprlM]

/-- At `γ = 1` the face amplitude is `J + 1`, the SU(2) dimension (as in the Ooguri weight). -/
theorem faceAmp_one (J : ℕ) : faceAmp 1 J = J + 1 := by
  simp [faceAmp, eprlN_one, eprlM_one]

/-- Every doubled spin is EPRL-admissible at `γ = 1`. -/
theorem eprlAdmissible_one (J : ℕ) : EPRLAdmissible 1 J := by
  refine ⟨⟨J, ?_⟩, ⟨0, ?_⟩⟩
  · simp only [jPlus]
    rw [abs_of_pos (by norm_num)]; ring
  · simp [jMinus]

/-- **The EPRL vertex at `γ = 1`**: when the tetrahedron labels are in their channels, it is the
SU(2) 15j contraction of the triangle spins and the tetrahedron labels, in the order of
`epair`. -/
theorem simpE_one {s : Finset V} (hs : #s = 5) (col : Finset V → ℕ)
    (hb : IsVertexBoundary (triSpins s hs col) 0 (tetLabels s hs col)) :
    simpE 1 col s =
      (fifteenJSimplex (triSpins s hs col 0) (triSpins s hs col 1) (triSpins s hs col 2)
        (triSpins s hs col 3) (triSpins s hs col 4) (triSpins s hs col 5) (triSpins s hs col 6)
        (triSpins s hs col 7) (triSpins s hs col 8) (triSpins s hs col 9)
        (tetLabels s hs col 0) (tetLabels s hs col 1) (tetLabels s hs col 2)
        (tetLabels s hs col 3) (tetLabels s hs col 4) : ℂ) := by
  have hN : (fun e => eprlN 1 (triSpins s hs col e)) = triSpins s hs col := by
    funext e; exact eprlN_one _
  have hM : (fun e => eprlM 1 (triSpins s hs col e)) = 0 := by
    funext e; exact eprlM_one _
  unfold simpE
  rw [dite_eq_left hs, hN, hM,
    ite_eq_left ⟨fun e => eprlAdmissible_one _, hb⟩]
  exact eprlVertex_zero_right _ _ hb

/-- **The weight at `γ = 1`**: the product of the SU(2) dimensions `J + 1` of the triangles and the
vertex amplitudes `simpE 1` (the edge amplitudes are `1`); the face factor is that of the Ooguri
weight. -/
theorem weightE_one (K : Complex4 V) (col : Finset V → ℕ) :
    weightE 1 K col =
      (∏ f ∈ K.tris, ((col f : ℂ) + 1)) * ∏ s ∈ K.simps, simpE 1 col s := by
  unfold weightE
  simp [edgeAmp, faceAmp_one]

end Lightlike.SpinFoam.EPRL
