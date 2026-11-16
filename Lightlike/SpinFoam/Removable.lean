import Lightlike.SpinFoam.HaarProducts
import Lightlike.SpinFoam.TwistedCohomologySU2

/-!
# Removing the cut-off of the group-integral Ponzano–Regge sum

The cut-off sum `partitionN C N` (`Lightlike.SpinFoam.GroupIntegral`) is *removable* when it has a
limit as `N → ∞`.

## Main results

* `Removable`: `partitionN C N` converges as `N → ∞`.
* `removable_loop`: the disc (one face on one loop) is removable, with limit `1`.
* `not_removable_sphere`, `not_removable_emptyFace`: the 2-sphere and a face with empty boundary are
  not removable, because the cut-off sum is unbounded.
* `removable_of_absSummable`: if the character-expansion coefficients (`coeff`, with the weights
  `Π_f (c_f + 1)`) are absolutely summable, the cut-off sum converges.
* `H2AbsSummable`: the **hypothesis** that, for a flat connection with `H² = 0`, the expansion is
  absolutely summable. **This implication is not proved here**; it is a named proposition, not a
  theorem. Checked by hand: disc (`H² = 0`, removable) and sphere (`H² ≠ 0`, not removable).

## Implementation notes

Why a hypothesis is needed.

`truncDelta N = Σ_{n ≤ N} (n+1) χ_n` is the sharp truncation of the delta function of `SU(2)`. On a
maximal torus it is a Dirichlet-type kernel in `θ`, not positive, so it is not an approximate
identity: convergence of `∫ φ · truncDelta N` to `φ(1)` can fail for a merely continuous density `φ`.
Deriving removability from `H² = 0` therefore needs a regularity statement for the density of the
face holonomies near the flat point, which is not formalized.
-/

open MeasureTheory Filter Topology Finset

namespace Lightlike.SpinFoam

/-- The cut-off sum has a limit as the cut-off is removed. -/
def Removable {Vtx E F : Type*} [Fintype E] [Fintype F]
    (C : Cell2 Vtx E F) : Prop :=
  ∃ L : ℂ, Tendsto (fun N => partitionN C N) atTop (𝓝 L)

/-- The disc is removable: the cut-off sum is `1` at every cut-off. -/
theorem removable_loop : Removable loopCx := by
  refine ⟨1, ?_⟩
  simp_rw [partitionN_loop]
  exact tendsto_const_nhds

/-- A sum bounded below by `N + 1` in norm does not converge. -/
lemma not_tendsto_of_norm_ge {u : ℕ → ℂ} (h : ∀ N : ℕ, (N : ℝ) + 1 ≤ ‖u N‖) {L : ℂ} :
    ¬ Tendsto u atTop (𝓝 L) := by
  intro ht
  have hb := ht.norm.bddAbove_range
  obtain ⟨B, hB⟩ := hb
  obtain ⟨N, hN⟩ := exists_nat_gt B
  have := hB ⟨N, rfl⟩
  linarith [h N]

/-- A sum of `(n+1)^2` over `n ≤ N` has norm at least `N + 1`. -/
lemma norm_sum_sq_ge (N : ℕ) :
    (N : ℝ) + 1 ≤ ‖∑ n ∈ range (N + 1), ((n : ℂ) + 1) ^ 2‖ := by
  have : (∑ n ∈ range (N + 1), ((n : ℂ) + 1) ^ 2) =
      ((∑ n ∈ range (N + 1), ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun n _ => by positivity)]
  have h1 : ((N : ℝ) + 1) ^ 2 ≤ ∑ n ∈ range (N + 1), ((n : ℝ) + 1) ^ 2 :=
    Finset.single_le_sum (f := fun n : ℕ => ((n : ℝ) + 1) ^ 2) (fun n _ => by positivity)
      (Finset.self_mem_range_succ N)
  nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- **The 2-sphere is not removable.** -/
theorem not_removable_sphere : ¬ Removable sphereCx := by
  rintro ⟨L, hL⟩
  refine not_tendsto_of_norm_ge (fun N => ?_) hL
  rw [partitionN_sphere]; exact norm_sum_sq_ge N

/-- **A face with empty boundary is not removable.** -/
theorem not_removable_emptyFace : ¬ Removable emptyFaceCx := by
  rintro ⟨L, hL⟩
  refine not_tendsto_of_norm_ge (fun N => ?_) hL
  rw [partitionN_emptyFace]; exact norm_sum_sq_ge N

/-- The Fourier coefficient of the face-holonomy density at the labelling `c`: the term of the
expansion `partitionN_eq_sum`, `Π_f (c_f + 1) ∫ Π_f χ_{c_f}(hol_f(g)) dg`. -/
noncomputable def coeff {Vtx E F : Type*} [Fintype E] [Fintype F]
    (C : Cell2 Vtx E F) (c : F → ℕ) : ℂ :=
  (∏ f, ((c f : ℂ) + 1)) * ∫ g, ∏ f, spinChar (c f) (hol g (C.bdry f)) ∂haarE E

/-- **Absolute summability of the expansion.** The coefficients `coeff C c`, which already carry the
weights `Π_f (c_f + 1)`, are absolutely summable over all labellings `c : F → ℕ`. -/
def AbsSummable {Vtx E F : Type*} [Fintype E] [Fintype F] (C : Cell2 Vtx E F) : Prop :=
  Summable fun c : F → ℕ => ‖coeff C c‖

/-- **Absolute summability makes the cut-off removable.** The cut-off sum is the sum of the
coefficients over the box `c_f ≤ N`, and the boxes exhaust `F → ℕ`; so an absolutely summable family
has these partial sums converging to its total sum. -/
theorem removable_of_absSummable {Vtx E F : Type*} [Fintype E] [Fintype F] [DecidableEq F]
    (C : Cell2 Vtx E F) (h : AbsSummable C) : Removable C := by
  have hs : Summable fun c : F → ℕ => coeff C c := Summable.of_norm h
  refine ⟨∑' c, coeff C c, ?_⟩
  have hbox : Tendsto (fun N : ℕ => Fintype.piFinset fun _ : F => range (N + 1)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro s
    refine ⟨s.sup fun c => Finset.univ.sup c, fun N hN c hc => ?_⟩
    rw [Fintype.mem_piFinset]
    intro f
    rw [mem_range]
    have h1 : c f ≤ Finset.univ.sup c := Finset.le_sup (f := c) (Finset.mem_univ f)
    have h2 : (Finset.univ.sup c) ≤ s.sup fun c => Finset.univ.sup c :=
      Finset.le_sup (f := fun c => Finset.univ.sup c) hc
    omega
  have := hs.hasSum.comp hbox
  refine this.congr fun N => ?_
  simp only [Function.comp]
  rw [partitionN_eq_sum]; rfl

/-- **Hypothesis (not proved).** For every flat `SU(2)` connection on `C` with `H² = 0`, the
character expansion of the cut-off sum is absolutely summable with the weights `Π_f (c_f + 1)`
(`AbsSummable`). By `removable_of_absSummable` this gives `Removable C`.

The link from `H² = 0` to this summability is **not proved**: it asks for a density of the face
holonomies near the flat point that is smooth enough for its character series to converge
absolutely. Absolute summability is used because the sharp kernel is not an approximate identity
(see above), so mere continuity of a density would not suffice. The two cases checkable by hand:
the disc (`H² = 0`; the only nonzero coefficient is `c = 0`, value `1`) and the sphere
(`H² ≠ 0`; the coefficients on the diagonal are `(n+1)²`, not summable, `not_removable_sphere`). -/
def H2AbsSummable {Vtx E F : Type*} [Fintype E] [Fintype F] (C : Cell2 Vtx E F) : Prop :=
  (∃ g : E → SU2, Flat C g ∧ Subsingleton (H2 adRep C g)) → AbsSummable C

/-- For the sphere the hypothesis holds exactly when no flat connection has `H² = 0`; its premise
fails (by `H² ≠ 0`, if every flat connection has nontrivial `H²`), its conclusion would not. -/
theorem h2AbsSummable_sphere_iff :
    H2AbsSummable sphereCx ↔
      ¬ ∃ g : Unit → SU2, Flat sphereCx g ∧ Subsingleton (H2 adRep sphereCx g) := by
  refine ⟨fun h hex => not_removable_sphere (removable_of_absSummable _ (h hex)), fun h hex => absurd hex h⟩

end Lightlike.SpinFoam
