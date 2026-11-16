import Lightlike.Asymptotics.EPRL.EprlCoherentNodeIdentity
import Lightlike.Asymptotics.EPRL.Decay

/-!
# The coherent EPRL vertex amplitude equals the coherent EPRL integral

For `γ < 1` and coherent boundary data with the same `SU(2)` elements on both chiral halves, the
`K₅` contraction of the coherent EPRL node tensors is the coherent EPRL integral `eprlCoh`, and
`eprlCoh` is the product of the two coherent `15j` integrals (`eprlCoh_eq_mul`). Expanding every node
in the intertwiner basis `ι_z`, this is the statement that the Euclidean EPRL vertex amplitude
`eprlVertex`, contracted with the coefficients of the coherent boundary intertwiners, is `eprlCoh`
(`eprlVertex_coherent`). The statement is exact at every spin: it is an identification of the coherent
integral form with the vertex, not an asymptotic formula, and it holds for doubled spins
`J = n + m` of any parity (an odd node sum makes both sides vanish).

## Main results

* `eprlCoh_eq_mul`: `eprlCoh n m g = coh15j n g · coh15j m g`.
* `k5Contract4_eprlCohNode`: the `K₅` contraction of the coherent EPRL node tensors is `eprlCoh`.
* `eprlVertex_coherent`: `Σ_{z⃗} Π_a c_a(z_a) eprlVertex n m z⃗ = eprlCoh n m g`, with `c_a(z)` the
  coefficients of the coherent boundary intertwiner of node `a` in the basis `ι_z`.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, §3.
* J. W. Barrett, W. J. Fairbairn, F. Hellmann, arXiv:0912.4907, eq. (1): the sign `(-1)^χ` of that
  equation is not compared with this library's conventions.
-/

open MeasureTheory Matrix Finset
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling

/-- **The coherent EPRL integral factorizes**: for `γ < 1` the integral over `Spin(4)^5 = SU(2)^5 ×
SU(2)^5` of the product of the self-dual and anti-self-dual integrands is the product of the two
coherent `15j` integrals. -/
theorem eprlCoh_eq_mul (n m : Fin 10 → ℕ) (g : BdryData) :
    eprlCoh n m g = coh15j n g * coh15j m g := by
  unfold eprlCoh coh15j
  have hmp := MeasureTheory.measurePreserving_arrowProdEquivProdArrow SU2 SU2 (Fin 5)
    (fun _ => haarSU2) (fun _ => haarSU2)
  have h := hmp.integral_comp' (g := fun y : (Fin 5 → SU2) × (Fin 5 → SU2) =>
    cohAmp n g (fun a => (y.1 a : Matrix (Fin 2) (Fin 2) ℂ)) *
      cohAmp m g (fun a => (y.2 a : Matrix (Fin 2) (Fin 2) ℂ)))
  have hP : (Measure.pi fun _ : Fin 5 => haarSpin4) =
      Measure.pi fun _ : Fin 5 => haarSU2.prod haarSU2 := rfl
  rw [hP]
  refine h.trans ?_
  unfold haarN
  exact integral_prod_mul
    (fun X : Fin 5 → SU2 => cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)))
    (fun X : Fin 5 → SU2 => cohAmp m g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)))

/-- **The `K₅` contraction of the coherent EPRL node tensors is the coherent EPRL integral.** -/
theorem k5Contract4_eprlCohNode (n m : Fin 10 → ℕ) (g : Fin 10 → Fin 2 → SU2) :
    k5Contract4 n m (fun a μ ν => eprlCohNode (k5Spins n a) (k5Spins m a) (nodeBdry g a) μ ν) =
      eprlCoh n m (fun e s => (g e s : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have h : (fun a μ ν => eprlCohNode (k5Spins n a) (k5Spins m a) (nodeBdry g a) μ ν) =
      fun a μ ν =>
        projNode (k5Spins n a) (cohInt (k5Spins n a) (nodeBdry g a)) μ *
          projNode (k5Spins m a) (cohInt (k5Spins m a) (nodeBdry g a)) ν := by
    funext a μ ν
    exact eprlCohNode_eq _ _ _ μ ν
  rw [h, k5Contract4_mul, k5Contract_cohInt, k5Contract_cohInt, eprlCoh_eq_mul]

/-- **The Euclidean EPRL vertex, contracted with the coherent boundary intertwiners, is the coherent
EPRL integral** (`γ < 1`, the same `SU(2)` elements on both chiral halves). The coefficient of the
coherent intertwiner of node `a` in the basis `ι_z` is `nodeSign * ⟨ι_z, homForm ι⟩`. -/
theorem eprlVertex_coherent (n m : Fin 10 → ℕ) (g : Fin 10 → Fin 2 → SU2) :
    ∑ P ∈ Fintype.piFinset (fun a : Fin 5 =>
        channel (k5Spins n a 0 + k5Spins m a 0) (k5Spins n a 1 + k5Spins m a 1)
          (k5Spins n a 2 + k5Spins m a 2) (k5Spins n a 3 + k5Spins m a 3)),
      (∏ a, (nodeSign (k5Spins n a + k5Spins m a) *
        hsInner (ivec (k5Spins n a 0 + k5Spins m a 0) (k5Spins n a 1 + k5Spins m a 1)
          (k5Spins n a 2 + k5Spins m a 2) (k5Spins n a 3 + k5Spins m a 3) (P a))
          (homForm (k5Spins n a + k5Spins m a)
            (cohInt (k5Spins n a + k5Spins m a) (nodeBdry g a))))) * eprlVertex n m P =
      eprlCoh n m (fun e s => (g e s : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [← k5Contract4_eprlCohNode]
  unfold eprlCohNode eprlVertex
  rw [k5Contract4_sum]

end Lightlike.Asymptotics.EPRL
