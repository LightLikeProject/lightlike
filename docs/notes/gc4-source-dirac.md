# GC4: the Dirac algorithm against a source that was read

Source: A. Wipf, "Hamilton's Formalism for Systems with Constraints", lectures, arXiv:hep-th/9312078 (ETH-TH/93-48), read in its arXiv HTML version. Section 3.3, equations (3.24)-(3.27), and the regularity assumptions of Sections 3.1 and 3.3.

What the source says: the consistency condition of the primary constraints is `h_m + C_mn u^n ≈ 0` (3.24) with the bracket
matrix `C_mn = {φ_m, φ_n}`; if `det C ≈ 0` it is solvable only when `h_m w^m_a ≈ 0` for every left null vector `w_a` of `C`
(secondary constraints, 3.26); the check is repeated on the enlarged surface; the procedure "terminates after a finite number
of iterations" (stated, no proof given). Assumptions stated: the constraints are regular (gradients locally linearly
independent) and "the rank of `C` is constant" on the final constraint surface.

Match with the library:
- `DiracStage.exists_multiplier_iff_chi` (with `DiracSchur`): where a block `B` of the bracket matrix is invertible and the
  rank is constant, the system `C u + h = 0` is solvable iff `h₂ - D B⁻¹ h₁ = 0`, the secondary constraints, from explicit left
  null vectors `[-D B⁻¹, 1]`; this is the source's (3.24)-(3.26) with the null vectors made explicit.
- `DiracRegular` and `DiracBridge.dChain_stabilizes_of_regular`: under regularity of each stage (independent derivatives) the
  chain stabilises by counting, which proves the termination that the source asserts; the regularity hypothesis is the
  source's own.
- `DiracTangent`: for a regular tuple the tangent cone of the surface is the common kernel of the derivatives (implicit function
  theorem), which is what "the evolution preserves the constraints" means.

Differences (the library statement is weaker than the source in these respects, none is accepted here): (1) the stage tuples and
the constant-rank sets `U k` enter as hypotheses (`hstage`); no theorem produces the whole sequence from the primary data
`(φ_a, H)` alone; (2) the construction of the null vectors is local, near a point where an `r × r` block is invertible, while the
source uses null vectors on the whole surface; (3) [closed] `DiracPoisson` ties the bracket matrix and `h` to Physlib's Poisson bracket (`poisson_exists_multiplier_iff_chi`); (4) `DiracAlgorithm` (the linear case) is a special case of the source's algorithm.
