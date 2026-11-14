import Lightlike.Asymptotics.EPRL.Amplitude
import Lightlike.Regge.D4.Dihedral
import Lightlike.Regge.D4.Complex

/-!
# The Regge boundary state of a geometric 4-simplex

The asymptotic formula of Barrett, Dowdall, Fairbairn, Gomes, Hellmann (J. Math. Phys. 50 (2009)
112504, arXiv:0902.1170) and of Barrett, Fairbairn, Hellmann (arXiv:0912.4907, eq. (16)) holds for
boundary data of *Regge type*: the coherent states of the boundary of a nondegenerate geometric
4-simplex `σ ⊂ ℝ⁴`, with phases fixed so that the critical values of the integrand are
`e^{± i Σ_e (n_e/2) Θ_e}` exactly. This file builds such a state constructively from `σ`.

* `simplexLength σ`: the edge lengths of `σ`, as a function of 2-element vertex sets, so that the
  Regge geometry of `Lightlike.Regge4` applies: `triArea σ e` (Heron, `Lightlike.Regge4.area4`) is the area of
  the triangle opposite the edge `e` of `K₅`, and `reggeAngle σ e = π - dihedral4` is the exterior
  dihedral angle at that triangle. `reggeAction σ J = Σ_e (J_e/2) Θ_e` is the Regge action for
  doubled spins `J`.
* `outNormal σ a`: the outward unit normal of the tetrahedron opposite the vertex `a`, from the
  foot of the altitude (`Affine.Simplex.altitudeFoot`).
* `quatMat v`: the unit quaternion `v₀ + v₁ i + v₂ j + v₃ k` as an element of SU(2).
* For the edge `e = ab`, the matrix `Q_a Q_b† = cos Θ_e + i sin Θ_e (b̂_e · σ)` defines the unit
  vector `b̂_e = unitBivector σ e` (the self-dual part of the bivector `N_a ∧ N_b`, up to
  normalisation), and `liftSU2 b̂_e` is an element of SU(2) with Bloch vector `b̂_e`.
* `reggeState σ`: `g_ab = Q_a† m_e d(Θ_e)` and `g_ba = Q_b† m_e ε`, with `m_e = liftSU2 b̂_e` and
  `d(β) = diag(e^{iβ/2}, e^{-iβ/2})`. The propagators do not depend on the phase of `m_e`.
* `critPlus σ` (`U⁺_a = Q_4† Q_a`) and `critMinus` (`U⁻_a = 1`) are the two critical points with
  `X_4 = 1`; at them every propagator equals `e^{± i Θ_e / 2}`.

The phase `e^{± i Σ_e (n_e/2) Θ_e}` of the asymptotic formula refers to this choice of phases of the
boundary state: other phase choices multiply the amplitude by a constant phase. The fixed lift
makes the integers `κ_ab` of BDFGH equal to `1`.
-/

open Matrix Complex Finset

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Regge4

/-- A geometric 4-simplex in `ℝ⁴`: five affinely independent points. -/
abbrev Simplex4 := Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 4)) 4

/-- The **edge lengths** of `σ` as a function of vertex sets: the distance of the two vertices on
2-element sets, `0` otherwise. -/
noncomputable def simplexLength (σ : Simplex4) (t : Finset (Fin 5)) : ℝ :=
  if h : t.card = 2 then
    dist (σ.points (t.min' (card_pos.mp (by omega)))) (σ.points (t.max' (card_pos.mp (by omega))))
  else 0

/-- The three vertices, in increasing order, of the triangle opposite the edge `e = ab` of `K₅`:
the triangle shared by the tetrahedra opposite `a` and opposite `b`. -/
def edgeTri : Fin 10 → Fin 3 → Fin 5 :=
  ![![2, 3, 4], ![1, 3, 4], ![1, 2, 4], ![1, 2, 3], ![0, 3, 4], ![0, 2, 4], ![0, 2, 3],
    ![0, 1, 4], ![0, 1, 3], ![0, 1, 2]]

/-- The vertex set of the triangle opposite the edge `e`. -/
def edgeTriSet (e : Fin 10) : Finset (Fin 5) := {edgeTri e 0, edgeTri e 1, edgeTri e 2}

/-- The **area** of the triangle opposite the edge `e`, from the edge lengths by Heron's formula. -/
noncomputable def triArea (σ : Simplex4) (e : Fin 10) : ℝ := area4 (simplexLength σ) (edgeTriSet e)

/-- The **exterior dihedral angle** `Θ_e = π - θ_e` of `σ` at the triangle opposite the edge
`e = ab`, where `θ_e` is the interior angle between the tetrahedra opposite `a` and opposite `b`,
computed from the edge lengths (`Lightlike.Regge4.dihedral4`). -/
noncomputable def reggeAngle (σ : Simplex4) (e : Fin 10) : ℝ :=
  Real.pi - dihedral4 (simplexLength σ) (edgeTri e 0) (edgeTri e 1) (edgeTri e 2) (edgeTgt e)
    (edgeSrc e)

/-- The **Regge action** `Σ_e (J_e/2) Θ_e` of `σ` with doubled spins `J`. -/
noncomputable def reggeAction (σ : Simplex4) (J : Fin 10 → ℕ) : ℝ :=
  ∑ e, (J e : ℝ) / 2 * reggeAngle σ e

/-- The **outward unit normal** of the tetrahedron opposite the vertex `a`: the unit vector from
`σ_a` to the foot of its altitude. -/
noncomputable def outNormal (σ : Simplex4) (a : Fin 5) : EuclideanSpace ℝ (Fin 4) :=
  (σ.height a)⁻¹ • (σ.altitudeFoot a -ᵥ σ.points a)

/-- The quaternion `v₀ + v₁ i + v₂ j + v₃ k` as the matrix
`[[v₀ + i v₁, v₂ + i v₃], [-v₂ + i v₃, v₀ - i v₁]]`, in SU(2) for a unit vector `v`. -/
noncomputable def quatMat (v : EuclideanSpace ℝ (Fin 4)) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![v 0 + I * v 1, v 2 + I * v 3; -v 2 + I * v 3, v 0 - I * v 1]

/-- The vector part `w` of `M = Q_a Q_b† = c + i w · σ` for the edge `e = ab`:
`w = (Im M₀₁, Re M₀₁, Im M₀₀)`. -/
noncomputable def bivector (σ : Simplex4) (e : Fin 10) : Fin 3 → ℝ :=
  let M := quatMat (outNormal σ (edgeSrc e)) * (quatMat (outNormal σ (edgeTgt e)))ᴴ
  ![(M 0 1).im, (M 0 1).re, (M 0 0).im]

/-- The unit vector `b̂_e = w / |w|` of the edge `e`. -/
noncomputable def unitBivector (σ : Simplex4) (e : Fin 10) : Fin 3 → ℝ :=
  (√(∑ k, bivector σ e k ^ 2))⁻¹ • bivector σ e

/-- An element of SU(2) with Bloch vector `v` (for a unit vector `v`): with `α = √((1 + v₂)/2)` and
`β = (v₀ + i v₁)/(2α)`, the matrix `[[α, -β̄], [β, α]]`, and `ε` for `v₂ = -1`. -/
noncomputable def liftSU2 (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if v 2 = -1 then epsMat else
    !![(√((1 + v 2) / 2) : ℂ), -((v 0 - I * v 1) / (2 * √((1 + v 2) / 2)));
      (v 0 + I * v 1) / (2 * √((1 + v 2) / 2)), (√((1 + v 2) / 2) : ℂ)]

/-- The diagonal matrix `d(β) = diag(e^{iβ/2}, e^{-iβ/2})`. -/
noncomputable def phaseMat (β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![cexp (I * β / 2), 0; 0, cexp (-(I * β / 2))]

/-- **The Regge state** of `σ`: for the edge `e = ab`, `g_ab = Q_a† m_e d(Θ_e)` and
`g_ba = Q_b† m_e ε`, with `Q_a = quatMat (outNormal σ a)`, `m_e = liftSU2 (unitBivector σ e)` and
`Θ_e = reggeAngle σ e`. -/
noncomputable def reggeState (σ : Simplex4) : BdryData := fun e =>
  ![(quatMat (outNormal σ (edgeSrc e)))ᴴ * liftSU2 (unitBivector σ e) * phaseMat (reggeAngle σ e),
    (quatMat (outNormal σ (edgeTgt e)))ᴴ * liftSU2 (unitBivector σ e) * epsMat]

/-- The critical point `U⁺_a = Q_4† Q_a` of the Regge state (with `U⁺_4 = 1`). -/
noncomputable def critPlus (σ : Simplex4) : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun a => (quatMat (outNormal σ 4))ᴴ * quatMat (outNormal σ a)

/-- The critical point `U⁻_a = 1` of the Regge state. -/
def critMinus : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ := fun _ => 1

/-! ## Basic checks -/

/-- The triangle opposite `e = ab` has three vertices and consists of the vertices other than `a`
and `b`. -/
theorem edgeTriSet_eq (e : Fin 10) : edgeTriSet e = univ \ {edgeSrc e, edgeTgt e} := by
  revert e
  decide

/-- The edge `e` joins two distinct nodes, with `edgeSrc e < edgeTgt e`. -/
theorem edgeSrc_lt_edgeTgt (e : Fin 10) : edgeSrc e < edgeTgt e := by
  revert e
  decide

/-- Distinct edges have distinct vertex pairs. -/
theorem edge_injective :
    Function.Injective fun e : Fin 10 => ({edgeSrc e, edgeTgt e} : Finset (Fin 5)) := by
  decide

/-- Every 2-element vertex set is an edge. -/
theorem edge_surjective (t : Finset (Fin 5)) (ht : t.card = 2) :
    ∃ e, ({edgeSrc e, edgeTgt e} : Finset (Fin 5)) = t := by
  revert t
  decide

/-- On a pair of distinct vertices, `simplexLength` is their distance. -/
theorem simplexLength_pair (σ : Simplex4) {a b : Fin 5} (h : a ≠ b) :
    simplexLength σ {a, b} = dist (σ.points a) (σ.points b) := by
  have hc : ({a, b} : Finset (Fin 5)).card = 2 := card_pair h
  simp only [simplexLength, hc, ↓reduceDIte]
  rcases lt_or_gt_of_ne h with hab | hab
  · rw [show ({a, b} : Finset (Fin 5)).min' _ = a from ?_, show ({a, b} : Finset (Fin 5)).max' _ = b
      from ?_]
    · exact le_antisymm (max'_le _ _ _ (by simp [hab.le])) (le_max' _ _ (by simp))
    · exact le_antisymm (min'_le _ _ (by simp)) (le_min' _ _ _ (by simp [hab.le]))
  · rw [show ({a, b} : Finset (Fin 5)).min' _ = b from ?_, show ({a, b} : Finset (Fin 5)).max' _ = a
      from ?_, dist_comm]
    · exact le_antisymm (max'_le _ _ _ (by simp [hab.le])) (le_max' _ _ (by simp))
    · exact le_antisymm (min'_le _ _ (by simp)) (le_min' _ _ _ (by simp [hab.le]))

end Lightlike.Asymptotics.EPRL
