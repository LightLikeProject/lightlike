import Lightlike.SpinFoam.TwistedCohomology
import Lightlike.Spin4.Haar
import Lightlike.SU2.Completeness
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The Ponzano–Regge sum with a cut-off as a Haar integral over `SU(2)`

For a finite 2-complex with edge group elements `g : E → SU(2)`, the group-variable form of the
Ponzano–Regge partition function integrates a delta function of the holonomy of every face
(the group-variable form of the model). On `SU(2)` the delta function is the character series
`δ(g) = Σ_n (n+1) χ_n(g)` over the spins `n/2`. This file takes it truncated at spin `N/2` and
proves that the resulting integral over `SU(2)^E` is the cut-off state sum over spin labellings of
the faces:

`Z_N(C) = ∫ Π_f δ_N(hol_f(g)) dg = Σ_{c : F → {0..N}} (Π_f (c_f + 1)) ∫ Π_f χ_{c_f}(hol_f(g)) dg`.

The labelling `c` is the doubled spin of each face. The integral on the right is the amplitude of
the labelled complex; it contains the product of the 6j symbols after the edge integrals are done
(not formalized here).

## Main results

* `spinChar n g`: the character of the spin-`n/2` representation, `tr D^{n/2}(g)`.
* `truncDelta N g`: the delta function cut off at spin `N/2`, `Σ_{n ≤ N} (n+1) χ_n(g)`.
* `partitionN C N`: the integral over `SU(2)^E` of the product over the faces of `truncDelta N`
  of the face holonomy.

* `integral_spinChar`: `∫ χ_n dg = 1` for `n = 0` and `0` for `n ≥ 1`.
* `partitionN_eq_sum`: the expansion into labelled amplitudes above.
* `partitionN_loop`: a single face bounded by one edge loop gives `1` at every cut-off.
* `partitionN_emptyFace`: a face with empty boundary word (no constraint on any edge) gives
  `Σ_{n ≤ N} (n+1)²`, which grows without bound. With `partitionN_loop` and
  `partitionN_loop_ne_emptyFace` these are the trust checks: the same definition gives `1` and a
  divergent value on the two simplest complexes.

## References

* `barrett-naish-guzman-2009`: the group-variable form of the Ponzano–Regge partition function.
-/

open Matrix MeasureTheory Finset Lightlike.SU2 Lightlike.Spin4

namespace Lightlike.SpinFoam

/-- The character of the spin-`n/2` representation of `SU(2)`. -/
noncomputable def spinChar (n : ℕ) (g : SU2) : ℂ :=
  trace (spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ))

/-- The delta function of `SU(2)` cut off at spin `N/2`: `Σ_{n ≤ N} (n+1) χ_n`. -/
noncomputable def truncDelta (N : ℕ) (g : SU2) : ℂ :=
  ∑ n ∈ range (N + 1), ((n : ℂ) + 1) * spinChar n g

lemma continuous_spinChar (n : ℕ) : Continuous (spinChar n) := by
  unfold spinChar
  simp only [trace, Matrix.diag]
  exact continuous_finsetSum _ fun i _ => continuous_spinMat_apply n i i

lemma spinChar_one (n : ℕ) : spinChar n 1 = (n : ℂ) + 1 := by
  simp [spinChar, spinMat_one]

lemma truncDelta_one (N : ℕ) : truncDelta N 1 = ∑ n ∈ range (N + 1), ((n : ℂ) + 1) ^ 2 := by
  unfold truncDelta
  refine sum_congr rfl fun n _ => ?_
  rw [spinChar_one]; ring

/-- `∫ D^{n/2}(g) dg` is fixed by every `D(h)`, so its range is an invariant subspace; for
`n ≥ 1` the representation is irreducible and not trivial, so the range is `0`. -/
theorem integral_spinChar (n : ℕ) :
    ∫ g, spinChar n g ∂haarSU2 = if n = 0 then 1 else 0 := by
  have hcont : ∀ k l, Continuous fun g : SU2 => spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) k l :=
    fun k l => continuous_spinMat_apply n k l
  have htr : ∫ g, spinChar n g ∂haarSU2 =
      trace (matInt fun g : SU2 => spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ)) :=
    (trace_matInt _ hcont).symm
  rw [htr]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [spinMat_zero']
    rw [matInt_const]; simp
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hn.ne')]
    set P := matInt fun g : SU2 => spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) with hP
    have hinv : ∀ h : SU2, spinMat n (h : Matrix (Fin 2) (Fin 2) ℂ) * P = P := by
      intro h
      have e1 := matInt_mul_left (fun g : SU2 => spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ)) h
      have e2 := matInt_mul_mul (spinMat n (h : Matrix (Fin 2) (Fin 2) ℂ))
        (fun g : SU2 => spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ))
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) hcont
      simp only [Matrix.mul_one] at e2
      have e3 : (fun g : SU2 => spinMat n ((h * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) =
          fun g : SU2 => spinMat n (h : Matrix (Fin 2) (Fin 2) ℂ) *
            spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) := by
        funext g; exact spinMat_mul _ _
      rw [e3, e2] at e1
      exact e1
    let W : Submodule ℂ (Fin (n + 1) → ℂ) := LinearMap.range (Matrix.toLin' P)
    have hW : IsInvariant n W := by
      intro g v hv
      obtain ⟨u, rfl⟩ := hv
      refine ⟨u, ?_⟩
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hinv g]
    rcases isInvariant_eq_bot_or_eq_top hW with h | h
    · have hP0 : P = 0 := by
        ext i j
        have : P *ᵥ (Pi.single j 1) = 0 := by
          have hm : P *ᵥ (Pi.single j 1) ∈ W := ⟨_, rfl⟩
          rw [h] at hm; simpa using hm
        have := congrFun this i
        simpa [Matrix.mulVec_single_one] using this
      rw [hP0]; simp
    · exfalso
      -- every vector is fixed by every `D(g)`, but a torus element moves the first basis vector
      have hfix : ∀ g : SU2, ∀ v, spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (P *ᵥ v) = P *ᵥ v :=
        fun g v => by rw [Matrix.mulVec_mulVec, hinv g]
      have hall : ∀ g : SU2, ∀ v, spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = v := by
        intro g v
        have hv : v ∈ W := by rw [h]; trivial
        obtain ⟨u, rfl⟩ := hv
        exact hfix g u
      set θ : ℝ := Real.pi / (2 * n) with hθ
      let z : ℂ := Complex.exp (θ * Complex.I)
      have hz : z * star z = 1 := by
        simp only [z]
        rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]; simp [Complex.conj_ofReal]
      have h0 := hall (torus z hz) (Pi.single 0 1)
      have hT := spinMat_torus_exp (n := n) θ
      have hco := congrFun h0 0
      simp only [z] at hco
      rw [hT] at hco
      simp at hco
      have hnθ : (n : ℂ) * (θ : ℂ) = (Real.pi : ℂ) / 2 := by
        have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        rw [hθ]; push_cast; field_simp
      rw [hnθ] at hco
      rw [Complex.exp_mul_I, ← Complex.ofReal_ofNat, ← Complex.ofReal_div] at hco
      simp at hco
      simpa using congrArg Complex.im hco

section Partition

variable {Vtx E F : Type*} [Fintype E] [Fintype F]

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology SU2 := TopologicalSpace.Subtype.secondCountableTopology _

/-- The normalised Haar measure on `SU(2)^E`. -/
noncomputable def haarE (E : Type*) [Fintype E] : Measure (E → SU2) :=
  Measure.pi fun _ => haarSU2

instance : IsProbabilityMeasure (haarE E) := by unfold haarE; infer_instance

lemma integrableE_of_continuous {f : (E → SU2) → ℂ} (hf : Continuous f) :
    Integrable f (haarE E) := by
  unfold haarE
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The cut-off Ponzano–Regge partition function in group variables:
`∫ Π_f δ_N(hol_f(g)) dg` over the edge group elements `g : E → SU(2)`. -/
noncomputable def partitionN (C : Cell2 Vtx E F) (N : ℕ) : ℂ :=
  ∫ g, ∏ f, truncDelta N (hol g (C.bdry f)) ∂haarE E

omit [Fintype E] [Fintype F] in
lemma continuous_lh (l : E × Bool) : Continuous fun g : E → SU2 => lh g l := by
  unfold lh
  by_cases h : l.2
  · simp only [h, ite_true]; exact continuous_apply l.1
  · simp only [h]; exact (continuous_apply l.1).inv

omit [Fintype E] [Fintype F] in
lemma continuous_hol (w : List (E × Bool)) : Continuous fun g : E → SU2 => hol g w := by
  induction w with
  | nil => exact continuous_const
  | cons l w ih => exact (continuous_lh l).mul ih

omit [Fintype E] in
lemma continuous_prod_spinChar (C : Cell2 Vtx E F) (c : F → ℕ) :
    Continuous fun g : E → SU2 => ∏ f, spinChar (c f) (hol g (C.bdry f)) :=
  continuous_finsetProd _ fun _ _ => (continuous_spinChar _).comp (continuous_hol _)

/-- **The group-integral form is the labelled state sum.** Expanding the product of the truncated
delta functions over the faces: `Z_N = Σ_c (Π_f (c_f + 1)) ∫ Π_f χ_{c_f}(hol_f(g)) dg`, summed over
all doubled-spin labellings `c` of the faces with `c_f ≤ N`. -/
theorem partitionN_eq_sum [DecidableEq F] (C : Cell2 Vtx E F) (N : ℕ) :
    partitionN C N =
      ∑ c ∈ Fintype.piFinset fun _ : F => range (N + 1),
        (∏ f, ((c f : ℂ) + 1)) *
          ∫ g, ∏ f, spinChar (c f) (hol g (C.bdry f)) ∂haarE E := by
  unfold partitionN truncDelta
  have hexp : ∀ g : E → SU2,
      ∏ f, ∑ n ∈ range (N + 1), ((n : ℂ) + 1) * spinChar n (hol g (C.bdry f)) =
        ∑ c ∈ Fintype.piFinset fun _ : F => range (N + 1),
          (∏ f, ((c f : ℂ) + 1)) * ∏ f, spinChar (c f) (hol g (C.bdry f)) := by
    intro g
    rw [Finset.prod_univ_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [← Finset.prod_mul_distrib]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun c _ => (integrableE_of_continuous (continuous_prod_spinChar C c)).const_mul _]
  refine sum_congr rfl fun c _ => ?_
  rw [integral_const_mul]

/-- Integrating over `SU(2)^Unit` is integrating over `SU(2)`. -/
lemma integral_haarE_unit (f : SU2 → ℂ) :
    ∫ g : Unit → SU2, f (g ()) ∂haarE Unit = ∫ x, f x ∂haarSU2 := by
  have h := (measurePreserving_funUnique haarSU2 Unit)
  exact h.integral_comp' f

/-- The complex with one edge loop and one face bounded by it. -/
def loopCx : Cell2 Unit Unit Unit where
  src _ := ()
  tgt _ := ()
  bdry _ := [((), true)]

/-- **Trust check, one loop.** A face bounded by one edge loop constrains the edge to the identity,
and the cut-off sum gives `1` at every cut-off. -/
theorem partitionN_loop (N : ℕ) : partitionN loopCx N = 1 := by
  unfold partitionN
  have : ∀ g : Unit → SU2, ∏ f : Unit, truncDelta N (hol g (loopCx.bdry f)) = truncDelta N (g ()) := by
    intro g; simp [loopCx, hol, lh]
  simp_rw [this]
  rw [integral_haarE_unit (fun x => truncDelta N x)]
  unfold truncDelta
  rw [integral_finsetSum _ fun n _ =>
    (integrable_of_continuous (continuous_spinChar n)).const_mul _]
  simp_rw [integral_const_mul, integral_spinChar]
  simp

/-- The complex with a single face with empty boundary word and no edges. -/
def emptyFaceCx : Cell2 Unit Empty Unit where
  src e := e.elim
  tgt e := e.elim
  bdry _ := []

/-- **Trust check, unconstrained face.** A face with empty boundary has holonomy `1`, and the
cut-off sum is `Σ_{n ≤ N} (n+1)²`, which is not bounded in `N`: the cut-off cannot be removed
there. -/
theorem partitionN_emptyFace (N : ℕ) :
    partitionN emptyFaceCx N = ∑ n ∈ range (N + 1), ((n : ℂ) + 1) ^ 2 := by
  unfold partitionN
  have : ∀ g : Empty → SU2, ∏ f : Unit, truncDelta N (hol g (emptyFaceCx.bdry f)) =
      truncDelta N 1 := by
    intro g; simp [emptyFaceCx, hol]
  simp_rw [this]
  rw [integral_const, probReal_univ, one_smul, truncDelta_one]

/-- The two trust checks differ at cut-off `1`: `1` against `5`. -/
theorem partitionN_loop_ne_emptyFace : partitionN loopCx 1 ≠ partitionN emptyFaceCx 1 := by
  rw [partitionN_loop, partitionN_emptyFace]
  norm_num [Finset.sum_range_succ]

end Partition

end Lightlike.SpinFoam
