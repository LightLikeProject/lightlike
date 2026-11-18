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

Differences (the library statement is weaker than the source in these respects, none is accepted here): (1) [closed] the stage tuples are generated from the primary data by `DiracAlgo.stages`
(secondary constraints `chiFun` from a selected invertible block of the consistency matrix of all the constraints of the earlier stages) and
`DiracAlgo.final_consistent_of_data` needs no hypothesis `hstage`; what remains hypotheses: the selection rule, regularity of
every stage, and the sets `U k` on which the chosen block is invertible with vanishing Schur complement; (2) the construction of the null vectors is local, near a point where an `r × r` block is invertible, while the
source uses null vectors on the whole surface; (3) [closed] `DiracPoisson` ties the bracket matrix and `h` to Physlib's Poisson bracket (`poisson_exists_multiplier_iff_chi`); (4) `DiracAlgorithm` (the linear case) is a special case of the source's algorithm.

## Update: stages from primary data, and the cover corollary

`DiracAlgo.final_consistent_of_cover`: if the sets `U k` (where the selected block is invertible with vanishing Schur
complement) cover the zero sets of the stages, then every point of the final surface has a multiplier solving all
consistency conditions `{S_i, H} + ∑_a {S_i, φ_a} u_a = 0` (eq. (3.24) with all the constraints of the earlier stages, Section 3.3 of Wipf's
lectures). The source's assumption, stated in Section 3.3, is that the rank of the bracket matrix `C` is constant on the final
constraint surface `Γ_c` and that the constraints are regular. Under constant rank `r` an invertible `r × r` block exists in a
neighbourhood of every point (a nonzero `r`-minor stays nonzero nearby), so the cover hypothesis is the source's constant-rank
assumption in local form; that step, from constant rank to the existence of the cover, is not proved here and is a
hypothesis (`hcover`), as is the selection rule.

Remaining differences with the source: (a) local selection of the invertible block instead of null eigenvectors `w_a` of `C`
on the whole surface (a representation difference: the null vectors used are the rows of `[-D B⁻¹, 1]`); (b) the cover
hypothesis (from constant rank to a cover by invertible blocks); (c) regularity of every stage is an explicit hypothesis, as
in the source, Section 3.3; (d) Wipf states the termination without proof; here it is `exists_stable_of_regular` by counting.

## Constant rank gives a nonzero minor (hcover): what is proved, and the representation difference

Proved (`MinorExists`): a real matrix of rank `r` has `r` rows and `r` columns with a nonzero `r × r` minor
(`exists_isUnit_det_submatrix`; no such lemma is in the pinned Mathlib), and an invertible block of a matrix-valued function with
continuous entries stays invertible on a neighbourhood (`eventually_isUnit_det`); with `DiracSchur.schur_eq_zero_of_rank_le_block`
(constant rank `r` forces the Schur complement of an invertible `r × r` block to vanish) this gives, near every point of the
surface and at each stage, an invertible block with vanishing Schur complement.

Not proved, and a representation difference against Wipf (Section 3.3, left null vectors `w_a` on the whole surface): the
block (the rows and columns of the minor) depends on the point, so the stage tuple built from a block is chart-dependent. The
algorithm `DiracAlgo.stages` uses one selection per stage; the pointwise statement near a point `x₀` is that one such
selection, adapted to `x₀`, works on a neighbourhood. A global statement needs a finite cover of the surface by such charts and
the compatibility of the resulting stage tuples on overlaps, which is not formalised.
