import Lightlike.Asymptotics.EPRL.EprlHighProj
import Lightlike.Asymptotics.EPRL.HaarNode

/-!
# The Spin(4) contraction along `K₅` by edges, and Fubini over `Spin(4)⁵`

Two exact identities for the contraction `k5Contract4` of five tensors along `K₅`, the first steps from
the coherent node tensors of the lowest Clebsch–Gordan component to an integral of edge forms:

* `k5Contract4_prod`: if the node tensors are products over their four legs, the contraction is the
  product over the ten edges of the edge pairings `Σ_{μ,ν} ε_n(μ) ε_m(ν) f_src(μ,ν) f_tgt(-μ,-ν)`.
  It is the factorization over edges `∏_{a<b}` of the integrand of Barrett–Dowdall–Fairbairn–Gomes–
  Hellmann (arXiv:0902.1170) eqs. (17)–(19), with the pair of indices `(μ, ν)` per edge of `Spin(4)`.
* `k5Contract4_integral`: if the node tensors are Haar integrals over `Spin(4)` of continuous
  functions, the contraction is the integral over `Spin(4)⁵` of the contraction of the integrands,
  the `∫_{Spin(4)⁵} ∏_c dG_c` of eq. (19).

Both are statements about finite sums and integrals of continuous functions; neither uses the EPRL map.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, Section 3.4.
-/

open Matrix Finset MeasureTheory
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling

/-- A double sum over two boxes of an edgewise product is the product over the edges of the double
sums. -/
lemma sum_sum_prod_pi (A B : Fin 10 → Finset ℤ) (G : Fin 10 → ℤ → ℤ → ℂ) :
    ∑ μ ∈ Fintype.piFinset A, ∑ ν ∈ Fintype.piFinset B, ∏ e, G e (μ e) (ν e) =
      ∏ e, ∑ x ∈ A e, ∑ y ∈ B e, G e x y := by
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.prod_univ_sum]

/-- **Regrouping the Spin(4) `K₅` contraction by edges.** If the node tensors are products
`T_a(μ, ν) = Π_l f_{a,l}(μ_l, ν_l)` over their legs, the contraction is the product over the ten
edges of the edge pairings `Σ_{μ,ν} ε_n(μ) ε_m(ν) f_src(μ, ν) f_tgt(-μ, -ν)`. This is the
factorization of the `Spin(4)⁵` integrand over the edges, `∏_{a<b}` of BDFGH eqs. (17)–(19). -/
theorem k5Contract4_prod (n m : Fin 10 → ℕ) (f : Fin 5 → Fin 4 → ℤ → ℤ → ℂ) :
    k5Contract4 n m (fun a μ ν => ∏ l, f a l (μ l) (ν l)) =
      ∏ e : Fin 10, ∑ μ ∈ Finset.Icc (-(n e : ℤ)) (n e), ∑ ν ∈ Finset.Icc (-(m e : ℤ)) (m e),
        ((edgeSign (n e) μ * edgeSign (m e) ν : ℝ) : ℂ) *
          (f (edgeSrc e) (srcLeg e) μ ν * f (edgeTgt e) (tgtLeg e) (-μ) (-ν)) := by
  rw [← sum_sum_prod_pi]
  unfold k5Contract4 k5Box
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  simp [Fin.prod_univ_succ, k5Legs, edgeSrc, srcLeg, tgtLeg, edgeTgt]
  ring

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology SU2 := TopologicalSpace.Subtype.secondCountableTopology _

/-- **Fubini for the Spin(4) `K₅` contraction**: if the node tensors are Haar integrals over Spin(4)
of continuous functions, `T_a(μ, ν) = ∫ G_a(X, μ, ν) dX`, the contraction is the integral over
`Spin(4)⁵` of the contraction of the integrands at `(X_0, …, X_4)`: the `∫_{Spin(4)⁵} ∏_c dG_c` of
BDFGH eq. (19). -/
theorem k5Contract4_integral (n m : Fin 10 → ℕ) (G : Fin 5 → Spin4 → (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℂ)
    (hG : ∀ a μ ν, Continuous fun X => G a X μ ν) :
    k5Contract4 n m (fun a μ ν => ∫ X, G a X μ ν ∂haarSpin4) =
      ∫ X : Fin 5 → Spin4, k5Contract4 n m (fun a μ ν => G a (X a) μ ν)
        ∂(Measure.pi fun _ => haarSpin4) := by
  have hint : ∀ μ ν : Fin 10 → ℤ, Integrable (fun X : Fin 5 → Spin4 =>
      ∏ a, G a (X a) (k5Legs μ a) (k5Legs ν a)) (Measure.pi fun _ => haarSpin4) := by
    intro μ ν
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    exact continuous_finsetProd _ fun a _ => (hG a _ _).comp (continuous_apply a)
  unfold k5Contract4
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun ν _ => ?_
      rw [integral_const_mul]
      congr 1
      exact (integral_fintype_prod_eq_prod (μ := fun _ : Fin 5 => haarSpin4)
        (fun a X => G a X (k5Legs μ a) (k5Legs ν a))).symm
    · intro ν _
      exact (hint μ ν).const_mul _
  · intro μ _
    refine integrable_finsetSum _ fun ν _ => ?_
    exact (hint μ ν).const_mul _

end Lightlike.Asymptotics.EPRL
