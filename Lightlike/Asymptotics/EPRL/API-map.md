# Large-spin asymptotics of the Euclidean EPRL vertex

## Abstract (Alpha)

This API proves the large-spin asymptotics of the coherent 15j integral and of the Euclidean EPRL
vertex integral in the Regge boundary state of a geometric 4-simplex. The integrals localise at the
points where the integrand has modulus one, which are the solutions of the gluing equations up to
sign, and stationary phase at each of these points gives the asymptotic formula, with two critical
values. Boundary data that do not glue give exponential suppression. The nondegeneracy of the two
Hessians is a hypothesis, as in the source. The coherent integral is identified with the EPRL
vertex on coherent boundary intertwiners for `γ < 1`; the case `γ > 1` is not covered.

## Content (Alpha)

The setting is that of Barrett, Dowdall, Fairbairn, Gomes and Hellmann {1}. The propagator `prop`,
the coherent amplitude `cohAmp`, the coherent 15j integral `coh15j`, the Euclidean EPRL vertex
integral `eprlCoh`, the chart `chart` and the Hessian amplitude `hessAmp` are defined [1]. The
Regge boundary state `reggeState` of a geometric 4-simplex is built from its edge lengths [27] and
its outward normals [25], and the exterior dihedral angle is the angle between the outward normals
[7].

The propagator and the amplitude have modulus at most one, with equality exactly when the boundary
data glue [12]. The gluing equations have two classes of solutions [13], the points of modulus one
are their sign lifts, and the amplitude is invariant under the sign flip [23]. The Regge state is
SU(2) data with closure, and its critical points are the two classes [4], with the two critical
values computed in [5]. Boundary data that do not glue give exponential suppression [6]. The
integrand is invariant under left multiplication, so the integral is gauge-fixed to `SU(2)^4` [11].

The Haar measure of SU(2) is the surface measure of the 3-sphere [16], which the gnomonic chart
maps to a cone [15]; on `SU(2)^4` this gives the chart integral on `ℝ¹²` [14]. The chart is written
as a matrix [2] and its inverse is continuous and injective [3].

Off a neighbourhood of the points of modulus one the integrand is uniformly below one, so the
integral localises [20], also after gauge fixing [21], and an `SU(2)^4` integral localises at
finitely many points [26]. The Hessian is computed through second derivatives along lines and
curves [18], in the gnomonic and in the exponential chart [17], with two rules for `invSqrtDet`
[19]. At a unimodular maximum the logarithmic phase gives the local asymptotics [22], and finitely
many nondegenerate maxima give the asymptotics of the integral [9].

The formulas are stated as `Coh15jAsymptoticFormula` and `EPRLAsymptoticFormula` [10], with the
nondegeneracy of the Hessians as a hypothesis. The coherent 15j formula is proven from the maximum
set as sign lifts and the Hessian at each of its points [24]. The EPRL integral is the product of
two coherent 15j integrals, which gives the EPRL formula [8]. The regular 4-simplex satisfies the
hypotheses, and spins not proportional to the areas, or with an odd node sum, do not [10]. The
script `scripts/asymptotics/eprl_asymptotics_check.py` compares the formula with the exact integral
at the regular 4-simplex, with wrong-formula controls; this is numerical evidence, not proof.
The edge pairing of the `K₅` contraction of the spin-network 15j, `Σ_μ (-1)^((n-μ)/2) u(μ) v(-μ)`,
is the bilinear form `u ⬝ᵥ (W v)` of the structure map on the coherent-state vectors [28]; it is the
first step towards writing the coherent 15j as a contraction of coherent intertwiners.
`k5Contract_cohInt` completes it: the coherent 15j is the `K₅` contraction of the coherent
intertwiners, with no extra sign in these conventions [29].

For `γ < 1` the Euclidean EPRL vertex contracted with the coherent boundary intertwiners is the
coherent EPRL integral. An invariant four-leg tensor becomes an `SU(2)` intertwiner in Hom form [31],
it is supported on total weight zero and expands in the `fourJ` basis with one constant sign [32], and
the EPRL map intertwines the singlet forms and sends products of coherent states to products of
self-dual and anti-self-dual coherent states [33]. The pairing of a Spin(4) basis intertwiner with the
EPRL lift of a coherent intertwiner is the product of the two `SU(2)` pairings [34], so the EPRL map
sends `ι_{n+m}(g)` to `ι_n(g) ⊗ ι_m(g)`; the signs of the bridge cancel by the additivity of the
constant sign [35]. The coherent EPRL node tensor is the product of the self-dual and anti-self-dual
coherent node tensors [36]. The `K₅` contraction of these is the coherent EPRL integral, which is the
product of the two coherent 15j integrals; expanding every node in the intertwiner basis gives the
vertex statement [37]. With an odd doubled-spin sum at a node the coherent intertwiner vanishes, so
the coherent 15j integral is zero for all boundary data and the even node sums are necessary [30].
The statement is exact at every spin and is not an asymptotic formula; the sign `(-1)^χ` of the
source's 15j equation is not compared with these conventions.

For `γ > 1` the lowest Clebsch–Gordan component replaces the sum of the two spins. The map, the
fusion coefficients and the node tensor are redefined for it [39]. The projection onto Spin(4)
intertwiners is the Haar average of the conjugation action [40]. The image of the `SU(2)` coherent
intertwiner is then a Spin(4) integral of the lifted coherent tensor [41], and the leg amplitude of
the lowest component on coherent states is, up to the abstract Clebsch–Gordan constant `c₀`, the
product of two overlaps [42]. The vertex sum with coherent boundary data is the `K₅` contraction
of the coherent node tensors, each a Spin(4) integral at the projections [43]. The positivity and the
closed value of `c₀` are not proved. The contraction of tensors that are products over their legs
is the product over the ten edges of the edge pairings, and the contraction of node integrals is the
integral over `Spin(4)^5` of the contraction of the integrands [44]; the `Spin(4)^5` integral of edge
forms itself is not yet in the library.

If the maximum set of the integrand is finite and the logarithmic phase has nonzero differential at
each of its points, then there is no critical point of the extended stationary phase and the coherent
15j integral decays faster than every power of the spin scale: the chart-level statement follows from
the non-stationary phase theorem [38], and `localise_pieces` glues the charts into the `SU(2)^4` statement
[38]. For SU(2) boundary data either some point of `SU(2)^5` has `|F_n| = 1` or the integral decays exponentially, and the coherent EPRL integral decays exponentially when the self-dual spins admit no gluing solution [38]. This is the case in which the proportionality of the spins to the areas is not assumed, and
the noncriticality of the maxima is the hypothesis; that it holds for spins that are not areas is not
proved here.

## Lean References

1. Lightlike/Asymptotics/EPRL/Amplitude.lean - `Asymptotics.EPRL.prop`, `Asymptotics.EPRL.cohAmp`,
   `Asymptotics.EPRL.coh15j`, `Asymptotics.EPRL.eprlCoh`, `Asymptotics.EPRL.chart`,
   `Asymptotics.EPRL.hessAmp`
2. Lightlike/Asymptotics/EPRL/ChartIntegral.lean - `Asymptotics.EPRL.coe_gammaSU`,
   `Asymptotics.EPRL.snoc_gamma_eq_qchart`
3. Lightlike/Asymptotics/EPRL/ChartPieces.lean - `Asymptotics.EPRL.chartMap`,
   `Asymptotics.EPRL.gammaSU_injective`, `Asymptotics.EPRL.continuous_gammaSU`
4. Lightlike/Asymptotics/EPRL/Critical.lean - `Asymptotics.EPRL.isSU2Data_reggeState`,
   `Asymptotics.EPRL.closure_reggeState`, `Asymptotics.EPRL.reggeState_critical_iff`,
   `Asymptotics.EPRL.linearIndependent_normalSU2`
5. Lightlike/Asymptotics/EPRL/CriticalValue.lean - `Asymptotics.EPRL.prop_critPlus`,
   `Asymptotics.EPRL.prop_critMinus`, `Asymptotics.EPRL.cohAmp_critPlus`,
   `Asymptotics.EPRL.cohAmp_critMinus`
6. Lightlike/Asymptotics/EPRL/Decay.lean - `Asymptotics.EPRL.coh15j_exp_decay`,
   `Asymptotics.EPRL.oneData_not_glued`, `Asymptotics.EPRL.coh15j_oneData_decay`
7. Lightlike/Asymptotics/EPRL/DihedralNormals.lean - `Asymptotics.EPRL.cos_reggeAngle`,
   `Asymptotics.EPRL.normal_mul_star_normal`
8. Lightlike/Asymptotics/EPRL/EPRLFormula.lean - `Asymptotics.EPRL.eprlCoh_eq_mul`,
   `Asymptotics.EPRL.eprlAsymptoticFormula`
9. Lightlike/Asymptotics/EPRL/FiniteMax.lean - `Asymptotics.EPRL.asymptotics_finite_max`
10. Lightlike/Asymptotics/EPRL/Formula.lean - `Asymptotics.EPRL.Coh15jAsymptoticFormula`,
    `Asymptotics.EPRL.EPRLAsymptoticFormula`, `Asymptotics.EPRL.regular_coh15j_hyps`,
    `Asymptotics.EPRL.regular_eprl_hyps`, `Asymptotics.EPRL.regular_wrong_spins`,
    `Asymptotics.EPRL.reggeAngle_regular`
11. Lightlike/Asymptotics/EPRL/GaugeFix.lean - `Asymptotics.EPRL.prop_mul_left`,
    `Asymptotics.EPRL.cohAmp_mul_left`, `Asymptotics.EPRL.coh15j_eq_gaugeFixed`
12. Lightlike/Asymptotics/EPRL/Gluing.lean - `Asymptotics.EPRL.norm_prop_le`,
    `Asymptotics.EPRL.norm_prop_eq_one_iff`, `Asymptotics.EPRL.norm_cohAmp_le`,
    `Asymptotics.EPRL.norm_cohAmp_eq_one_iff`
13. Lightlike/Asymptotics/EPRL/GluingSolutions.lean - `Asymptotics.EPRL.quat_two_classes`,
    `Asymptotics.EPRL.quat_glue_iff`, `Asymptotics.EPRL.glued_iff_two_classes`
14. Lightlike/Asymptotics/EPRL/HaarChart.lean - `Asymptotics.EPRL.integral_haar4_chart`,
    `Asymptotics.EPRL.measurePreserving_reshape`
15. Lightlike/Asymptotics/EPRL/HaarGraph.lean - `Asymptotics.EPRL.haarSU2_gnomonic`,
    `Asymptotics.EPRL.volume_cone4_image`
16. Lightlike/Asymptotics/EPRL/HaarSphere.lean - `Asymptotics.EPRL.haarSU2_eq_cone`,
    `Asymptotics.EPRL.measurePreserving_mulLeft`
17. Lightlike/Asymptotics/EPRL/HessianChart.lean - `Asymptotics.EPRL.hessMat_qchart`,
    `Asymptotics.EPRL.iteratedDeriv_two_qchart`, `Asymptotics.EPRL.coordDeriv_qchart_eq_zero`
18. Lightlike/Asymptotics/EPRL/HessianSlice.lean - `Asymptotics.EPRL.iteratedDeriv_two_comp_eq`,
    `Asymptotics.EPRL.iteratedDeriv_two_line`
19. Lightlike/Asymptotics/EPRL/InvSqrtDet.lean - `Asymptotics.EPRL.invSqrtDet_smul_pos`,
    `Asymptotics.EPRL.invSqrtDet_submatrix`
20. Lightlike/Asymptotics/EPRL/Localise.lean - `Asymptotics.EPRL.exists_sup_lt_one`,
    `Asymptotics.EPRL.norm_setIntegral_compl_le`, `Asymptotics.EPRL.not_hmax_empty`
21. Lightlike/Asymptotics/EPRL/Localise4.lean - `Asymptotics.EPRL.norm_setIntegral_pow_compl_le`,
    `Asymptotics.EPRL.norm_setIntegral_compl_le4`
22. Lightlike/Asymptotics/EPRL/LogPhase.lean - `Asymptotics.EPRL.hessMat_logPhase`,
    `Asymptotics.EPRL.local_asymptotics`
23. Lightlike/Asymptotics/EPRL/MaxSet.lean - `Asymptotics.EPRL.norm_eq_one_iff_signLift`,
    `Asymptotics.EPRL.cohAmp_flip`, `Asymptotics.EPRL.cohAmp_signLift`
24. Lightlike/Asymptotics/EPRL/MaxSetFinite.lean - `Asymptotics.EPRL.coh15jAsymptoticFormula`
25. Lightlike/Asymptotics/EPRL/Normals.lean - `Asymptotics.EPRL.linearIndependent_outNormal_three`,
    `Asymptotics.EPRL.sum_outNormal_div_height`, `Asymptotics.EPRL.triArea_mul_height_tgt`
26. Lightlike/Asymptotics/EPRL/Pieces.lean - `Asymptotics.EPRL.localise_pieces`
27. Lightlike/Asymptotics/EPRL/ReggeState.lean - `Asymptotics.EPRL.reggeState`,
    `Asymptotics.EPRL.edge_injective`, `Asymptotics.EPRL.simplexLength_pair`
28. Lightlike/Asymptotics/EPRL/EdgeBridge.lean - `Asymptotics.EPRL.projVec`,
    `Asymptotics.EPRL.edgePair_eq_sum`, `Asymptotics.EPRL.edgePair_eq`,
    `Asymptotics.EPRL.edgePair_antisymm_one`
29. Lightlike/Asymptotics/EPRL/HaarNode.lean - `Asymptotics.EPRL.cohInt_apply_eq_integral`,
    `Asymptotics.EPRL.cohState_pair`, `Asymptotics.EPRL.prop_eq_pair`,
    `Asymptotics.EPRL.k5Contract_prod`, `Asymptotics.EPRL.k5Contract_integral`,
    `Asymptotics.EPRL.projNode_cohInt`, `Asymptotics.EPRL.k5Contract_cohInt`,
    `Asymptotics.EPRL.pair_ne_overlap`
30. Lightlike/Asymptotics/EPRL/OddSum.lean - `Asymptotics.EPRL.rhoN_negOne`,
    `Asymptotics.EPRL.cohInt_eq_zero_of_odd`, `Asymptotics.EPRL.coh15j_eq_zero_of_odd`
31. Lightlike/Asymptotics/EPRL/HomForm.lean - `Asymptotics.EPRL.asMat_rhoN`,
    `Asymptotics.EPRL.homForm_rhoN`, `Asymptotics.EPRL.hsInner_conj_of_isIntertwiner`,
    `Asymptotics.EPRL.homForm_isIntertwiner`
32. Lightlike/Asymptotics/EPRL/HomFormExpansion.lean - `Asymptotics.EPRL.invariant_weight_zero`,
    `Asymptotics.EPRL.fourJ_support`, `Asymptotics.EPRL.homForm_apply`,
    `Asymptotics.EPRL.vec_eq_sum`, `Asymptotics.EPRL.hsInner_homForm_avgP`
33. Lightlike/Asymptotics/EPRL/EprlCoherentNode.lean - `Asymptotics.EPRL.eprlMap_Wm`,
    `Asymptotics.EPRL.eprlPair_Wm`, `Asymptotics.EPRL.singlet2_mul_eprlPair_conjTranspose`,
    `Asymptotics.EPRL.eprlPair_mulVec_coh`, `Asymptotics.EPRL.eprlLift_homForm_prod`
34. Lightlike/Asymptotics/EPRL/EprlCoherentPullback.lean -
    `Asymptotics.EPRL.pullback_isIntertwiner`, `Asymptotics.EPRL.hsInner_ivec4_eprlLift_cohInt`
35. Lightlike/Asymptotics/EPRL/EprlCoherentIntertwiner.lean -
    `Asymptotics.EPRL.eprlIntertwiner_homForm_cohInt`, `Asymptotics.EPRL.nodeSign_add`,
    `Asymptotics.EPRL.projNode_projOf`, `Asymptotics.EPRL.eprlNode_eq_eprlIntertwiner'`,
    `Asymptotics.EPRL.eprlIntertwiner_sum_smul`
36. Lightlike/Asymptotics/EPRL/EprlCoherentNodeIdentity.lean - `Asymptotics.EPRL.eprlCohNode`,
    `Asymptotics.EPRL.eprlCohNode_projOf`, `Asymptotics.EPRL.eprlCohNode_eq`
37. Lightlike/Asymptotics/EPRL/EprlCoherentVertex.lean -
    `Asymptotics.EPRL.k5Contract4_eprlCohNode`, `Asymptotics.EPRL.eprlVertex_coherent`
38. Lightlike/Asymptotics/EPRL/Suppression.lean - `Asymptotics.EPRL.local_suppression`,
    `Asymptotics.EPRL.suppression_finite_max`, `Asymptotics.EPRL.coh15j_dichotomy`,
    `Asymptotics.EPRL.eprlCoh_exp_decay_of_no_gluing`
39. Lightlike/Asymptotics/EPRL/EprlHighMap.lean - `Asymptotics.EPRL.eprlMapLow`,
    `Asymptotics.EPRL.eprlMapLow_isometry`, `Asymptotics.EPRL.eprlMapLow_equivariant`,
    `Asymptotics.EPRL.eprlLiftLow`, `Asymptotics.EPRL.eprlIntertwinerLow`,
    `Asymptotics.EPRL.fusionLow`, `Asymptotics.EPRL.eprlNodeLow`,
    `Asymptotics.EPRL.eprlNodeLow_eq_eprlIntertwinerLow`
40. Lightlike/Asymptotics/EPRL/EprlHighProj.lean - `Asymptotics.EPRL.matInt4`,
    `Asymptotics.EPRL.act4`, `Asymptotics.EPRL.hsInner_conj_of_intertwines`,
    `Asymptotics.EPRL.projSpin4_eq_integral`
41. Lightlike/Asymptotics/EPRL/EprlHighNode.lean -
    `Asymptotics.EPRL.homForm_avgP_eq_matInt`, `Asymptotics.EPRL.projSpin4_matInt`,
    `Asymptotics.EPRL.eprlIntertwinerLow_homForm_cohInt`
42. Lightlike/Asymptotics/EPRL/EprlHighLeg.lean - `Asymptotics.EPRL.weight_of_equivariant`,
    `Asymptotics.EPRL.c0Low`, `Asymptotics.EPRL.legAmp_mul`,
    `Asymptotics.EPRL.eprlMapLow_cohState_one`, `Asymptotics.EPRL.eprlMapLow_cohState`
43. Lightlike/Asymptotics/EPRL/EprlHighVertex.lean -
    `Asymptotics.EPRL.eprlVertexHigh`, `Asymptotics.EPRL.eprlCohNodeHigh`,
    `Asymptotics.EPRL.eprlCohNodeHigh_integral`, `Asymptotics.EPRL.eprlVertexHigh_coherent`
44. Lightlike/Asymptotics/EPRL/EprlHighEdge.lean - `Asymptotics.EPRL.k5Contract4_prod`,
    `Asymptotics.EPRL.k5Contract4_integral`

## References

1. J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes and F. Hellmann, Asymptotic analysis of
   the EPRL four-simplex amplitude, *J. Math. Phys.* 50 (2009) 112504.
