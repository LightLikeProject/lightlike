import Lightlike.Spacetime.FlatConnection

/-!
# A connection with torsion has a different Ricci tensor from the Levi-Civita connection

On `ℝ²` with the Minkowski metric the flat connection `∇_v Y = DY(v)` is the Levi-Civita connection
(`flat_isMetricCompatible`, `flat_torsion`) and its Ricci tensor is `0`. The connection
`twistedConnection` adds the endomorphism-valued one-form `A_w v = w₁ v` to it:
`∇'_v Y = DY(v) + Y₁ v`. For constant fields `X, Y, Z` one gets

* torsion `T(X, Y) = X Y₁ − Y X₁`, so `T(e₀, e₁) = e₀ ≠ 0`;
* curvature `R(X, Y) Z = Z₁ (Y₁ X − X₁ Y)` and Ricci `Ric(Y, Z) = Y₁ Z₁`, so `Ric(e₁, e₁) = 1 ≠ 0`.

Main result `torsion_connection_ricci_ne`: the flat connection is a Levi-Civita connection of the Minkowski
metric with vanishing Ricci tensor, while `twistedConnection` has torsion and a Ricci tensor that is not zero.

**Difference from the cited statement** (Lee, *Introduction to Riemannian Manifolds*, ch. 5, comparison not
read at the cited location: pending): a worked example on `ℝ²` with one chosen connection, not a statement
for every connection with torsion.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

/-- `ℝ²`, the model space of the example. -/
abbrev V2 := Fin 2 → ℝ

/-- The one-form `w ↦ (v ↦ w₁ v)`. -/
def twistForm (x : V2) : TangentSpace 𝓘(ℝ, V2) x →L[ℝ] TangentSpace 𝓘(ℝ, V2) x →L[ℝ] TangentSpace 𝓘(ℝ, V2) x :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight
    (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, V2) x))

/-- The connection `∇'_v Y = DY(v) + Y₁ v`: the flat connection plus a one-form with torsion. -/
def twistedConnection : Connection 𝓘(ℝ, V2) V2 :=
  (flatConnection V2).addOneForm twistForm

theorem twistedConnection_apply (σ : Π y : V2, TangentSpace 𝓘(ℝ, V2) y) (x : V2)
    (v : TangentSpace 𝓘(ℝ, V2) x) :
    twistedConnection σ x v =
      (show TangentSpace 𝓘(ℝ, V2) x from fderiv ℝ (σ : V2 → V2) x v) + (σ x 1) • v := rfl

/-- The derivative of the extension of a vector is zero. -/
theorem fderiv_extend_V2 (x : V2) (w : TangentSpace 𝓘(ℝ, V2) x) (y : V2) :
    fderiv ℝ (fun z => (FiberBundle.extend V2 w z : V2)) y = 0 := by
  have h : (fun z => (FiberBundle.extend V2 w z : V2)) = fun _ => (w : V2) := funext (extend_flat x w)
  rw [h]; exact fderiv_const_apply (w : V2)

/-- The constant vector field `c` of `ℝ²`. -/
def constField (c : V2) : Π y : V2, TangentSpace 𝓘(ℝ, V2) y := fun _ => c

/-- The extension of a tangent vector is the constant field. -/
theorem extend_eq_constField (x : V2) (w : TangentSpace 𝓘(ℝ, V2) x) :
    (FiberBundle.extend V2 w : Π y : V2, TangentSpace 𝓘(ℝ, V2) y) = constField (w : V2) :=
  funext fun y => extend_flat x w y

/-- The twisted connection of a constant field `c` is `v ↦ c₁ v`. -/
theorem twisted_constField (c : V2) (y : V2) (v : TangentSpace 𝓘(ℝ, V2) y) :
    twistedConnection (constField c) y v = (c 1) • v := by
  simp only [twistedConnection_apply]
  have : fderiv ℝ (fun _ : V2 => c) y = 0 := fderiv_const_apply c
  have h : (constField c : V2 → V2) = fun _ : V2 => c := rfl
  rw [h]
  simp only [this]
  exact zero_add _

/-- The twisted connection of the extension of a vector `w` is `v ↦ w₁ v`. -/
theorem twisted_extend (x y : V2) (w : TangentSpace 𝓘(ℝ, V2) x) (v : TangentSpace 𝓘(ℝ, V2) y) :
    twistedConnection (FiberBundle.extend V2 w) y v = (w 1) • v := by
  rw [extend_eq_constField]
  exact twisted_constField (w : V2) y v

/-- **The twisted connection has torsion**: `T(X, Y) = Y₁ X − X₁ Y`. -/
theorem twisted_torsion_apply (x : V2) (X₀ Y₀ : TangentSpace 𝓘(ℝ, V2) x) :
    twistedConnection.torsion x X₀ Y₀ = (Y₀ 1) • X₀ - (X₀ 1) • Y₀ := by
  rw [CovariantDerivative.torsion_apply_eq_extend, twisted_extend, twisted_extend, mlieBracket_flat]
  simp only [fderiv_extend_V2, extend_flat]
  show _ - ((0 : TangentSpace 𝓘(ℝ, V2) x) - 0) = _
  simp

/-- **Curvature of the twisted connection** on vectors of `ℝ²`: `R(X, Y) Z = Z₁ (Y₁ X − X₁ Y)`. -/
theorem twisted_curvatureAt_aux (x : V2) (a b c : V2) :
    twistedConnection.curvatureAt x (a : TangentSpace 𝓘(ℝ, V2) x) (b : TangentSpace 𝓘(ℝ, V2) x)
      (c : TangentSpace 𝓘(ℝ, V2) x) = c 1 • (b 1 • a - a 1 • b) := by
  unfold Connection.curvatureAt
  have e : ∀ w : V2, (FiberBundle.extend V2 (w : TangentSpace 𝓘(ℝ, V2) x) :
      Π y : V2, TangentSpace 𝓘(ℝ, V2) y) = constField w := fun w => extend_eq_constField x w
  simp only [e]
  have hZ : ∀ A : V2, (fun y => twistedConnection (constField c) y (constField A y)) =
      constField (c 1 • A) := fun A => funext fun y => twisted_constField _ y _
  have hd : ∀ A : V2, fderiv ℝ (constField A : V2 → V2) x = 0 := fun A => fderiv_const_apply A
  have hb : mlieBracket 𝓘(ℝ, V2) (constField a) (constField b) x = 0 := by
    have := mlieBracket_flat (constField a) (constField b) x
    simp only [hd] at this
    rw [this]
    exact sub_self _
  rw [hZ, hZ, hb]
  rw [twisted_constField, twisted_constField]
  rw [map_zero, sub_zero]
  simp only [constField, Pi.smul_apply, smul_eq_mul, smul_sub, smul_smul]
  rfl

/-- **The Ricci tensor of the twisted connection**: `Ric(e₁, e₁) = 1`. -/
theorem twisted_ricciAt_e1 (x : V2) :
    twistedConnection.ricciAt x (Pi.single 1 1 : V2) (Pi.single 1 1 : V2) = 1 := by
  unfold Connection.ricciAt
  set b := Module.finBasis ℝ V2 with hb
  have hR : ∀ i, twistedConnection.curvatureAt x (b i : TangentSpace 𝓘(ℝ, V2) x)
      (Pi.single 1 1 : V2) (Pi.single 1 1 : V2) = (b i : V2) - (b i : V2) 1 • (Pi.single 1 1 : V2) := by
    intro i
    have := twisted_curvatureAt_aux x (b i : V2) (Pi.single 1 1) (Pi.single 1 1)
    rw [this]
    simp only [Pi.single_eq_same, one_smul]
    rfl
  simp only [hR]
  have hs : ∑ i, (b i : V2) 1 * b.repr (Pi.single 1 1 : V2) i = 1 := by
    have := congrFun (b.sum_repr (Pi.single 1 1 : V2)) 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at this
    exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans this
  simp only [map_sub, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul,
    Finset.sum_sub_distrib, hs, Finsupp.single_eq_same, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, V2, Module.finrank_fin_fun]
  norm_num

/-- The flat connection of `ℝ²` has vanishing Ricci tensor. -/
theorem flat_ricciAt_eq_zero (x : V2) (v w : TangentSpace 𝓘(ℝ, V2) x) :
    (flatConnection V2).ricciAt x v w = 0 := by
  unfold Connection.ricciAt
  exact Finset.sum_eq_zero fun i _ =>
    (congrArg ((Module.finBasis ℝ V2).coord i) (flat_curvatureAt x _ v w)).trans (map_zero _)

/-- The twisted connection has torsion. -/
theorem twisted_torsion_ne_zero : twistedConnection.torsion ≠ 0 := by
  intro h
  have h1 := congrArg (fun T => T (0 : V2) (Pi.single 0 1 : V2) (Pi.single 1 1 : V2) 0) h
  simp only [Pi.zero_apply] at h1
  have h2 := twisted_torsion_apply (0 : V2) (Pi.single 0 1 : V2) (Pi.single 1 1 : V2)
  rw [h2] at h1
  change ((1 : ℝ) • (Pi.single 0 1 : V2) - (0 : ℝ) • (Pi.single 1 1 : V2)) 0 = (0 : V2) 0 at h1
  simp at h1

/-- **A connection with torsion gives a different Ricci tensor from the Levi-Civita connection of the same
metric.** On `ℝ²` with the Minkowski metric: the flat connection is a Levi-Civita connection with vanishing
Ricci tensor; `twistedConnection` has torsion, so it is not Levi-Civita, and its Ricci tensor is not zero. -/
theorem torsion_connection_ricci_ne :
    (flatConnection V2).IsLeviCivita (minkowskiMetric 2) ∧
    (∀ x v w, (flatConnection V2).ricciAt x v w = 0) ∧
    twistedConnection.torsion ≠ 0 ∧ ¬ twistedConnection.IsLeviCivita (minkowskiMetric 2) ∧
    ∃ x v w, twistedConnection.ricciAt x v w ≠ (flatConnection V2).ricciAt x v w := by
  refine ⟨⟨flat_torsion, flat_isMetricCompatible 2⟩, flat_ricciAt_eq_zero, twisted_torsion_ne_zero,
    fun h => twisted_torsion_ne_zero h.1, 0, Pi.single 1 1, Pi.single 1 1, ?_⟩
  rw [twisted_ricciAt_e1]
  exact fun h => one_ne_zero (h.trans (flat_ricciAt_eq_zero 0 _ _))

end Lightlike
