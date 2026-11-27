# Spin foam models: Ooguri and Barrett–Crane

## Abstract (Alpha)

This API defines the Ooguri state sum, the SU(2) BF spin foam model of a triangulated 4-manifold,
with the 15j symbol as vertex amplitude. The state sum is regularised by finite cutoffs and by a
gauge set of triangles whose spin is fixed to zero. It proves that the gauge-fixed state sum at
finite cutoff is invariant under the 4-dimensional Pachner moves 3-3, 2-4 and 1-5 and their
inverses, and that the gauge rule survives each move. It also defines the Barrett–Crane vertex
amplitude and proves that it is a sum of squared 15j symbols, hence real and non-negative.

## Content (Alpha)

The Ooguri model is the SU(2) BF spin foam model in four dimensions {1} {2}. A colouring gives a
spin to every triangle and a virtual spin, in the canonical intertwiner basis, to every
tetrahedron. The vertex amplitude of a 4-simplex is the evaluation of the spin network on its
boundary, the 15j symbol; it does not depend on the orientation of the 4-simplex [1]. The weight
of a colouring is the product of the dimensions of the triangle spins and of the vertex
amplitudes. The state sum is regularised by a cutoff on every coloured face and by a gauge set
of triangles whose spin is fixed to zero [2].

The gauge rule asks that the vertices, the edges and the gauge triangles form a collapsible
2-complex. It is this library's proposal for the 4-dimensional analogue of the maximal tree of
the Ponzano–Regge gauge fixing {3}. A gauge set has `E − V + 1` triangles [2], the degree of
divergence that Bonzom and Smerlak find for a triangulated 4-sphere {4}.

The gauge-fixed state sum is invariant under the 3-3 move [3], the 2-4 and 4-2 moves [4] and the 1-5
and 5-1 moves [5], for cutoffs that cut nothing off on the faces inside the move. In each case the
gauge rule survives the move, with the new triangles added to the gauge set. Each of the three moves
has an example on a closed 4-sphere in which the kernel checks every hypothesis, and a perturbed
vertex amplitude breaks the 3-3 identity [6]. The invariances rest on recoupling identities of spin networks: summed over the colours of the
inner triangles and tetrahedra, the union of the vertex networks of one side evaluates to a reduced
network, once the cutoffs exceed the triangle inequalities. For the 3-3 move the reduced networks of the two
sides agree by a gauge transformation [3]; for the 2-4 move the two-simplex side evaluates to the
reduced network of the other side [35]; for the 1-5 move the reduced network is the one-simplex
network times the dimensions of four free triangles [36]. Two gauge sets that each force every triangle give the
same state sum at every cutoff [7]. It is constant along a chain of these 4D Pachner moves (with the cutoffs re-chosen between
moves), and for a gauge set that forces every triangle it is `1` at every constant cutoff [8]. A set that forces every triangle still forces every triangle after a 1-5
move, when the four gauge triangles of the move are added [9]; for the 3-3 move, a set that forces the complex before the move and does not contain the moved triangle
forces the complex after it if and only if the closure of the set under the tetrahedra that do not contain that
triangle is already complete [10]; a 48-simplex 4-sphere gives a collapsible forcing gauge set that loses forcing under
3-3 (numerical evidence only). For the 2-4 move, a set that forces the complex before the move, together with
one new triangle `{a, p, q}`, forces the complex after it if and only if the closure of the set under the tetrahedra other
than the removed one is already complete [11]. The sets that the inverse moves 4-2 and 5-1 transport can lose forcing
(numerical evidence only). Call a set robust for a complex when it forces every triangle with any one
tetrahedron removed: robust sets stay robust under the 1-5 move, and a robust set keeps forcing under every 2-4 move and under
every 3-3 move that does not remove one of its triangles [12];
robust sets do not in general stay robust under the 3-3 move (an explicit counterexample is proved by `decide` [13]; for the 2-4 move a random search found one, numerical evidence only), while the gauge set carried along from the boundary of the 5-simplex was robust in every sample
(every tetrahedron of 1,104,480 on random 4-spheres, and 822 consecutive forward moves; numerical evidence only). For gauge sets that do not force, the state sum at a finite
cutoff can depend on the gauge set (numerical evidence, a non-manifold complex and a closed 4-sphere
triangulation), so independence for all gauge sets is not claimed. Removing the cutoff is not yet
formalized. [TODO]

The gauge-fixed state sum depends on the gauge set only through what it forces. Adding triangles that
the gauge set already forces does not change the sum at any cutoff, and gauge sets that force each
other give equal sums, whether or not they force every triangle [29]. The forcing closure `forcedTris`
of a set of triangles is monotone, idempotent and contained in the triangles of the complex, and
the state sum with the closure as gauge set equals the sum with the set itself [30]. The closure is
every triangle exactly when the set forces every triangle, and then the sum is `1` at every
cutoff [31]. Forcing between subsets of the triangles is the inclusion order of the closures, it is
transitive, and equal closures are mutual forcing, so the state sum is constant on forcing classes
[32]. On the boundary of the 5-simplex the cone gauge set and a twisted gauge set have the same
closure (every triangle) and the same sum, while the cone with one triangle removed has a smaller
closure [33]. The trust check bundles the milestone's two checks: the cone obeys the gauge rule
and gives `1`, and the cone minus one triangle violates it and gives `5` [34]. All of these are
finite-cutoff statements; nothing says that gauge sets with different closures give different sums.

The Barrett–Crane model {5} puts a simple representation `(j, j)` of Spin(4) on every triangle and
the Barrett–Crane intertwiner `Σ_i ι_i ⊗ ι_i` on every tetrahedron. A representation `(n, m)`
satisfies the simplicity constraint exactly when `n = m` [14]. The vertex amplitude is the sum of the
squares of the 15j symbols over the virtual spins of the five tetrahedra, so it is real and
non-negative for all spins [14]. Baez and Christensen's Riemannian 10j symbol, where nonzero, is
negative when the ten spins sum to a half-integer {6}, so the two sign conventions differ. The
Baez–Christensen vertex `bcVertexBC` is `(-1)^(Σ_e j_e)` times ours, with `j_e` the doubled spins
[14]: its absolute value is ours, it is non-negative when the spins sum to an integer and
non-positive when they sum to a half-integer [14]. The vertex is 1 at spin 0, `1/(j + 1)²` on the
closed loop of spin `j/2`, which sums to an integer, and `1/(j + 1)` on the triangle of spin
`j/2`, whose spins sum to `3j/2`; so at spin `1/2` the two conventions give `1/2` and `-1/2` [15].
The intertwiner is unique: a Spin(4)-invariant tensor of four simple representations whose
components are diagonal in the `(01)(23)` and the `(02)(13)` tree bases is a multiple of
`Σ_i ι_i ⊗ ι_i`. This is Reisenberger's theorem for four legs, assuming two of his three pairings;
the proof uses a stretched 6j symbol, which is nonzero [41].
The vertex is an exact rational number for all spins, because the square of each 15j symbol is
rational [42]. It reproduces the published Riemannian 10j values of Christensen and Egan: `7/18` at
ten spins `½`, `307/1500` at ten spins `1`, and `-163/1728`, with the Baez–Christensen sign, at
spins `1` and `½` on the two 5-cycles of `K₅` [42].

Whether the Ponzano–Regge cutoff can be removed is a cohomological question {7}. A flat `SU(2)`
connection on a finite 2-complex, with the adjoint representation on `su(2) ≅ ℝ³`, has a twisted
cochain complex whose differential `d1` obeys `d1 ∘ d0 = 0` exactly when the connection is flat
and the boundary words are closed walks [16]. For a flat connection, `d1` is the differential of
the holonomy map along the curves `exp(tΦ) g`, and it is onto exactly when `H² = 0` [17]. The
2-sphere with the trivial connection has `d1` not onto, and the disc has it onto; for `SU(2)` the
sphere has `H² ≠ 0` [18]. For Bing's house, summing over the two room spins first gives `1`, by the
Racah sum rule (6) [19]. The sum is not absolutely convergent: the simple cutoff on all spins truncates the room sums, and at doubled cutoff `2` its partial sum is `37/12` [19]; it has no limit (numerical evidence only). With the delta function of `SU(2)` cut off at spin `N/2`, the
Ponzano–Regge sum is the Haar integral over the edge variables of the product of the cut-off delta
functions of the face holonomies, and it expands into the labelled amplitudes over all face spins
up to the cutoff [20]. One edge loop bounding one face gives `1` at every cutoff, while a face
with empty boundary gives `Σ (n+1)²`, which grows without bound [20]. The characters are
orthonormal for the Haar measure, and the integral of a product of characters is the trace of the
projection onto the invariant vectors of the tensor product, which is the triangle indicator for
three spins and the number of virtual spins for four [24]; with this the 2-sphere (two faces
glued along one loop) gives `Σ (n+1)²` at cutoff `N` as well, so the cutoff sum is constant
on the disc (`H² = 0`) and unbounded on the sphere (`H² ≠ 0`) [21]. If the character
expansion of the cutoff sum is absolutely summable the cutoff is removable, with the sum as limit
[22]. That a vanishing `H²` gives this summability is stated as a hypothesis (`H2AbsSummable`)
and is not proved in general; it is proved for the disc and for a complex with two edges and two
faces (`H² = 0` there) [23]. For three spins the projection onto the invariant vectors is a
rank-one projector onto a unit vector for a triad and zero otherwise, and the character of `g h⁻¹`
expands into products of matrix elements of `g` and of `h` coupled by the matrix of `w` (this
removes the conjugate representation from the group integral of a tetrahedron, whose four vertex
integrals are then such projectors) [25]. The tetrahedron integral equals `Z Z̄` for the tetrahedral
network `Z` of the four vertex vectors contracted along the six edges by `W`. The vertex vector
is the 3j symbol up to a phase, and `Z` is the 6j symbol up to sign, so the tetrahedron integral is
the square of the 6j symbol of the six edge spins [26]; it is 1 for spin 0, 1/36 for spin 1 on
every edge, and 0 when a vertex is not a triad [27]. The cut-off sum over the six edge spins, with the
weights `Π (s + 1)`, has nonnegative terms, so it is monotone and has a limit exactly when it is
bounded; at doubled cut-off `0` it is `1`, and at `2` it is at least `1 + 81/4` [28]. It is
unbounded, as for the 2-sphere: the single term with the doubled spins `(0, N, N, N, N, 0)` equals
`(N+1)^2`, because the `6j` symbol with a zero spin is `±1/(N+1)` [28], so the sum has no limit
without the rescaling `M_Λ^{-v}` of Barrett and Naish-Guzman (§2.2). Existence as a distribution
is a different statement and is not treated. Exact values for doubled cut-offs `0` to `3` (`1`, `29`,
`2393/4`, `488337/100`) are numerical evidence only.

Three different statements about the cut-off must be kept apart. (A) Existence as a distribution
in the boundary data: Barrett and Naish-Guzman (§4.4) show that it holds exactly when the second
twisted cohomology `H²` at the flat connections is trivial. Only the finite-dimensional step is
proved here: `d1` is the differential of the holonomy map, so `H² = 0` exactly when every
variation of the face holonomies is realised [15]. The measure-theoretic step is not. (B) The
simple cut-off sum. For Bing's house, summing the room spins first gives `1`, while the simple
cut-off with all spins `≤ 1` gives `37/12` [17] (§2.4 of the same paper: no interior vertex, so no
rescaling, and the simple cut-off is not triangulation independent). The cut-off sum of the
tetrahedron is at least `(N+1)^2` [26]; §2.2 of the paper notes that such sums can diverge and
regularises with a rescaling per interior vertex. (C) What follows, for these two complexes: the
value of the sum depends on the summation order or the regularisation, and the unrescaled cut-off
sum of the tetrahedron has no limit. What does not follow, and is not claimed: that `H² ≠ 0` causes
this; that `H² = 0` makes the cut-off removable (this is the hypothesis `H2AbsSummable`, proved
only for the disc and a two-edge, two-face complex); that the rescaled limit of the tetrahedron
sum diverges (the rescaling factor is not defined here); and that the simple cut-off sum of
Bing's house is unbounded (the paper shows this numerically; here only the two values above are
proved).

The EPRL state sum is formalized in the sorted basis of the tetrahedra, in which a tetrahedron shared by two
4-simplices carries one and the same basis. The intrinsic vertex is the vertex of the 4-simplex with every virtual spin
rewritten by the transition matrix between the positional and the sorted channel, the exact overlap of the two orthonormal
bases of the invariant space of the tetrahedron, and at the BF point γ = 1 on a closed 4-complex the state sum is the sum
over the triangle colourings and the virtual spins of the triangle constraints times the Ooguri weight: the state sum of a
closed 4-complex equals the Ooguri state sum [46]. The corrected intrinsic vertex is the basis-free contraction of the
intertwiners of the sorted legs of its five tetrahedra along the ten links of `K₅` [43], and on a closed complex the
sum over the labels of the tetrahedra is a network of these projectors [44]. Relabelling the vertices by a permutation
`σ` reverses the orientation of the links of the pairs of vertices that `σ` inverts, and the sign `(-1)` to the number of
reversed links is even on a closed complex because the sum of the colours of the link of an edge is even [45]; so the
state sum is the same for every order of the vertices, also with the tetrahedra glued through `ε` [47]. Exchanging the
two factors of Spin(4), the opposite orientation of ℝ⁴ (γ ↦ -γ), leaves the vertex and the state sum unchanged [38]. On
the boundary of the 5-simplex with the cutoff of the bone colouring of any edge the γ = 1 state sum is 1 + 4 = 5, and
with the face amplitude (J + 1)² in place of J + 1 the same sum is 65 [39], [40]. The source (arXiv:0711.0146) fixes no
order or sign convention: "matches the source" means that the amplitude is the basis-free contraction of the definition
in the source.

## Lean References

1. Lightlike/SpinFoam/Vertex.lean - `SpinFoam.vertexAmp`, `SpinFoam.vertexContr_eq`,
   `SpinFoam.vertexContr_neg`
2. Lightlike/SpinFoam/Ooguri.lean - `SpinFoam.weight`, `SpinFoam.amplitudeGF`,
   `SpinFoam.amplitude`, `SpinFoam.IsGauge`, `SpinFoam.IsGauge.card_eq`
3. Lightlike/SpinFoam/Move33.lean - `SpinFoam.amplitudeGF_move33`,
   `SpinFoam.amplitudeGF_move33_gauge`, `SpinFoam.Move33.inner_eq`, `SpinFoam.Move33.lhs_eq_ev_NL`,
   `SpinFoam.Move33.ev_NL_rev`
4. Lightlike/SpinFoam/Move24Global.lean - `SpinFoam.amplitudeGF_move24`,
   `SpinFoam.amplitudeGF_move24_gauge`, `SpinFoam.amplitudeGF_move42_gauge`, `SpinFoam.IsGauge.move24`
5. Lightlike/SpinFoam/Move15Global.lean - `SpinFoam.Move15.amplitudeGF_move15`,
   `SpinFoam.Move15.amplitudeGF_move15_gauge`, `SpinFoam.Move15.amplitudeGF_move51_gauge`,
   `SpinFoam.Move15.isGauge_move15`
6. Lightlike/SpinFoam/Tests.lean - `SpinFoam.amplitudeGF_move33_example`,
   `SpinFoam.amplitudeGF_move24_example`, `SpinFoam.amplitudeGF_move15_example`,
   `SpinFoam.amplitudeGF_move24_gauge_example`, `SpinFoam.amplitudeGF_move15_gauge_example`,
   `SpinFoam.ampBad_breaks_move33`, `SpinFoam.forces_move15_example`, `SpinFoam.forces_move33_example`, `SpinFoam.forces_move24_example`, `SpinFoam.robust_move15_example`, `SpinFoam.forces_move24_of_robust_example`, `SpinFoam.forces_move33_of_robust_example`
7. Lightlike/SpinFoam/GaugeIndependence.lean - `SpinFoam.amplitudeGF_eq_of_forces`,
   `SpinFoam.amplitudeGF_eq_of_isGauge_forces`
8. Lightlike/SpinFoam/GaugeChain.lean - `SpinFoam.GFStep4`, `SpinFoam.GFStep4.isGauge`,
   `SpinFoam.amplitudeGF_eqvGen4`, `SpinFoam.amplitudeGF_congr_cut`,
   `SpinFoam.amplitudeGF_tendsto_one_of_forces`
9. Lightlike/SpinFoam/ForcingMoves.lean - `SpinFoam.Forces.mono`, `SpinFoam.Forces.of_union`,
   `SpinFoam.Move15.forces_move15`
10. Lightlike/SpinFoam/ForcingMove33.lean - `SpinFoam.Forcing33.local33_prop`,
   `SpinFoam.Forcing33.local33_vars`, `SpinFoam.Forcing33.local33_control`, `SpinFoam.ForcesIn`,
   `SpinFoam.ForcesIn.sound`, `SpinFoam.forcesInBy`, `SpinFoam.forcesIn_of_forcesInBy`,
   `SpinFoam.Forcing33.forcing_dichotomy`, `SpinFoam.Forcing33.forces_sigma_of_common`,
   `SpinFoam.Forcing33.forces_tau_of_common`, `SpinFoam.Forcing33.forces_iff_forcesIn`,
   `SpinFoam.Forcing33.forces_move33_iff`
11. Lightlike/SpinFoam/ForcingMove24.lean - `SpinFoam.Forcing24.local24`,
   `SpinFoam.Forcing24.local24_control`, `SpinFoam.Forcing24.forcing_dichotomy24`,
   `SpinFoam.Forcing24.forces24_of_common`, `SpinFoam.Forcing24.forces_move24_iff`
12. Lightlike/SpinFoam/ForcingRobust.lean - `SpinFoam.Robust`, `SpinFoam.robustBy`,
   `SpinFoam.robust_of_robustBy`, `SpinFoam.Move15.robust_move15`, `SpinFoam.forces_move24_of_robust`,
   `SpinFoam.Forcing33.forcesIn_common_of_robust_33`, `SpinFoam.Forcing33.forces_move33_of_robust`,
   `SpinFoam.Forcing33.lemmaX_abstract`
13. Lightlike/SpinFoam/ForcingRobustCounterexample.lean - `SpinFoam.robust_Kcex`,
   `SpinFoam.not_robust_Kcex_move`, `SpinFoam.robust_not_kept_by_move33`
14. Lightlike/SpinFoam/BarrettCrane.lean - `SpinFoam.BC.bcVertex`, `SpinFoam.BC.bcVertex_eq_sum`,
   `SpinFoam.BC.bcVertex_nonneg`, `SpinFoam.BC.simple_iff`, `SpinFoam.BC.bcVertexBC`,
   `SpinFoam.BC.abs_bcVertexBC`, `SpinFoam.BC.bcVertexBC_of_even`, `SpinFoam.BC.bcVertexBC_of_odd`,
   `SpinFoam.BC.bcVertexBC_nonneg_of_even`, `SpinFoam.BC.bcVertexBC_nonpos_of_odd`,
   `SpinFoam.BC.bcVertex_im`
15. Lightlike/SpinFoam/BarrettCraneTests.lean - `SpinFoam.BC.Tests.bcVertex_zero`,
   `SpinFoam.BC.Tests.bcVertex_cyc`, `SpinFoam.BC.Tests.bcVertex_triangle`,
   `SpinFoam.BC.Tests.bcVertexBC_cyc`, `SpinFoam.BC.Tests.bcVertexBC_triangle_one`,
   `SpinFoam.BC.Tests.bcVertexBC_triangle_ne`, `SpinFoam.BC.Tests.not_simple_half_zero`
16. Lightlike/SpinFoam/TwistedCohomology.lean - `SpinFoam.Cell2`, `SpinFoam.d0`, `SpinFoam.d1`,
    `SpinFoam.d1_comp_d0`, `SpinFoam.H2`, `SpinFoam.d1_surjective_iff`
17. Lightlike/SpinFoam/TwistedCohomologySU2.lean - `SpinFoam.adRep`,
    `SpinFoam.holonomy_hasDerivAt`, `SpinFoam.face_variation_iff`, `SpinFoam.h2_trivial_iff_face_variation`
18. Lightlike/SpinFoam/TwistedCohomologyTests.lean - `SpinFoam.disc_d1_surjective`,
    `SpinFoam.sphere_d1_not_surjective`, `SpinFoam.disc_nonflat_d1_comp_d0_ne`,
    `SpinFoam.sphere_su2_not_surjective`, `SpinFoam.sphere_su2_H2_nontrivial`
19. Lightlike/SpinFoam/BingsHouse.lean - `SpinFoam.racah_sum`, `SpinFoam.bingIterated_eq_one`,
    `SpinFoam.bingCutoff`, `SpinFoam.bingCutoff_two`, `SpinFoam.bingCutoff_two_ne_iterated`
20. Lightlike/SpinFoam/GroupIntegral.lean - `SpinFoam.spinChar`, `SpinFoam.truncDelta`,
    `SpinFoam.integral_spinChar`, `SpinFoam.partitionN`, `SpinFoam.partitionN_eq_sum`,
    `SpinFoam.partitionN_loop`, `SpinFoam.partitionN_emptyFace`,
    `SpinFoam.partitionN_loop_ne_emptyFace`
21. Lightlike/SpinFoam/HaarProducts.lean - `SpinFoam.matInt_spinMat_cross`,
    `SpinFoam.integral_spinChar_mul_star`, `SpinFoam.integral_prod_spinChar`,
    `SpinFoam.trace_avgP_single`, `SpinFoam.partitionN_sphere`,
    `SpinFoam.partitionN_loop_ne_sphere`
22. Lightlike/SpinFoam/Removable.lean - `SpinFoam.Removable`, `SpinFoam.removable_loop`,
    `SpinFoam.not_removable_sphere`, `SpinFoam.not_removable_emptyFace`, `SpinFoam.coeff`,
    `SpinFoam.AbsSummable`, `SpinFoam.removable_of_absSummable`, `SpinFoam.H2AbsSummable`
    (hypothesis, not proved), `SpinFoam.h2AbsSummable_sphere_iff`
23. Lightlike/SpinFoam/TwoFace.lean - `SpinFoam.twoFaceCx`, `SpinFoam.integral_haarE_two`,
    `SpinFoam.coeff_twoFace`, `SpinFoam.absSummable_twoFace`, `SpinFoam.partitionN_twoFace`,
    `SpinFoam.removable_twoFace`, `SpinFoam.twoFace_H2_trivial`, `SpinFoam.twoFace_premise`,
    `SpinFoam.h2AbsSummable_twoFace`
24. Lightlike/SpinFoam/IntertwinerCount.lean - `SpinFoam.spinChar_real`,
    `SpinFoam.spinChar_mul_eq_sum`, `SpinFoam.integral_spinChar_mul`,
    `SpinFoam.integral_spinChar_three`, `SpinFoam.integral_spinChar_four`,
    `SpinFoam.trace_avgP_three`, `SpinFoam.trace_avgP_four`
25. Lightlike/SpinFoam/Tetrahedron.lean - `SpinFoam.eq_zero_of_trace_zero`,
    `SpinFoam.exists_vecMulVec_of_trace_one`, `SpinFoam.wM`, `SpinFoam.Wm`,
    `SpinFoam.map_star_su2`, `SpinFoam.spinMat_map_star`, `SpinFoam.star_spinMat_eq`,
    `SpinFoam.YI`, `SpinFoam.spinChar_mul_inv_expand`, `SpinFoam.avgP_three_rank_one`,
    `SpinFoam.tetraF`, `SpinFoam.tetraInt`, `SpinFoam.tetraF_expand`, `SpinFoam.cc`,
    `SpinFoam.rhoN_entry`, `SpinFoam.tetra_term`, `SpinFoam.uV`, `SpinFoam.avgP_eq_uV`,
    `SpinFoam.aa`, `SpinFoam.Zt`, `SpinFoam.cc_eq`, `SpinFoam.continuous_tetra_term`,
    `SpinFoam.tetraInt_eq`
26. Lightlike/SpinFoam/TetrahedronSixJ.lean - `SpinFoam.Wm_eq_rev`, `SpinFoam.Smat`,
    `SpinFoam.svec`, `SpinFoam.svec_invariant`, `SpinFoam.svec_norm`, `SpinFoam.tV`,
    `SpinFoam.svec_eq`, `SpinFoam.eq_phase_of_rank_one`, `SpinFoam.uV_eq_phase_tV`,
    `SpinFoam.yOf`, `SpinFoam.sum_yOf`, `SpinFoam.pr`, `SpinFoam.ZR`,
    `SpinFoam.Zt_eq_phase_ZR`, `SpinFoam.kap`, `SpinFoam.epsS`, `SpinFoam.sixJTerm_kap`,
    `SpinFoam.sum_sixJTerm_kap`, `SpinFoam.ZR_eq`, `SpinFoam.tetraInt_eq_sixJ_sq`
27. Lightlike/SpinFoam/TetrahedronTests.lean - `SpinFoam.Tests.sixJ_all_two`,
    `SpinFoam.Tests.tetraInt_zero`, `SpinFoam.Tests.tetraInt_two`,
    `SpinFoam.Tests.tetraInt_eq_zero_of_not_tri`, `SpinFoam.Tests.tetraInt_ones_vertex`
28. Lightlike/SpinFoam/TetrahedronCutoff.lean - `SpinFoam.tetraTerm`, `SpinFoam.tetraPartition`,
    `SpinFoam.tetraTerm_eq`, `SpinFoam.tetraPartition_mono`, `SpinFoam.tetraPartition_zero`,
    `SpinFoam.tetraRemovable_iff_bddAbove`, `SpinFoam.tetraTerm_zeroSpin`,
    `SpinFoam.tetraPartition_ge`, `SpinFoam.tetraPartition_unbounded`,
    `SpinFoam.not_tetraRemovable`, `SpinFoam.tetraPartition_two_ge`
29. Lightlike/SpinFoam/OoguriGaugeFixed/ForcingClosure.lean - `SpinFoam.Forces.union`,
    `SpinFoam.amplitudeGF_union_of_forces`, `SpinFoam.amplitudeGF_insert_of_step`,
    `SpinFoam.forcedTris`, `SpinFoam.forces_forcedTris`, `SpinFoam.amplitudeGF_eq_forcedTris`,
    `SpinFoam.amplitudeGF_eq_of_mutual_forces`, `SpinFoam.tendsto_amplitudeGF_iff_of_mutual_forces`
30. Lightlike/SpinFoam/OoguriGaugeFixed/ForcingClosureAlgebra.lean - `SpinFoam.forcedTris_mono`,
    `SpinFoam.forcedTris_forcedTris`, `SpinFoam.forces_iff_subset_forcedTris`,
    `SpinFoam.amplitudeGF_eq_of_forcedTris_eq`
31. Lightlike/SpinFoam/OoguriGaugeFixed/ForcingClosureTotal.lean - `SpinFoam.forcedTris_eq_tris_iff`,
    `SpinFoam.amplitudeGF_forcedTris`, `SpinFoam.amplitudeGF_eq_one_of_forcedTris_eq_tris`,
    `SpinFoam.forcedTris_union_eq`, `SpinFoam.amplitudeGF_union_eq_forcedTris_union`
32. Lightlike/SpinFoam/OoguriGaugeFixed/ForcingClosureOrder.lean -
    `SpinFoam.forces_iff_forcedTris_subset`, `SpinFoam.Forces.trans'`,
    `SpinFoam.forcedTris_eq_iff_mutual_forces`, `SpinFoam.amplitudeGF_eq_of_forces_forces`
33. Lightlike/SpinFoam/OoguriGaugeFixed/Test.lean - `SpinFoam.forces_starT`,
    `SpinFoam.forcedTris_starT`, `SpinFoam.amplitudeGF_starT_eq_twistT`,
    `SpinFoam.forcedTris_gauge9_ne`
34. Lightlike/SpinFoam/OoguriGaugeFixed/Capstone.lean - `SpinFoam.gaugeFixed_sphere6_trust`
35. Lightlike/SpinFoam/Move24.lean - `SpinFoam.Move24.lhs_eq_ev_NL24`,
    `SpinFoam.Move24.sumB_eq_ev_QB`
36. Lightlike/SpinFoam/Move15.lean - `SpinFoam.Move15.lhs_eq_ev_NL15`,
    `SpinFoam.Move15.ev_NL_eq_QB`
37. Lightlike/SpinFoam/EPRLStateSum/IntrinsicVertex.lean - `SpinFoam.EPRLStateSum.simpEI_eq_sum_simpE`,
    `SpinFoam.EPRLStateSum.simpEIAux_eq_sum_nodeT`, `SpinFoam.EPRLStateSum.amplitudeI_one_eq_signed_ooguri`,
    `SpinFoam.EPRLStateSum.amplitudeI_one_closed`
38. Lightlike/SpinFoam/EPRLStateSum/Orientation.lean - `SpinFoam.EPRLStateSum.eprlVertex_swap`,
    `SpinFoam.EPRLStateSum.amplitudeI_neg`
39. Lightlike/SpinFoam/EPRLStateSum/BoneAmplitude.lean -
    `SpinFoam.EPRLStateSum.Trust.amplitudeI_sphere6_low_spin`, `SpinFoam.EPRLStateSum.Trust.amplitudeI_wrong_face`
40. Lightlike/SpinFoam/EPRLStateSum/BoneColouring.lean, BoneCollapse.lean, BoneWeight.lean -
    `SpinFoam.EPRLStateSum.Trust.weight_bone`, `SpinFoam.EPRLStateSum.Trust.amplitudeI_sphere6_bone`,
    `SpinFoam.EPRLStateSum.Trust.amplitudeI_sphere6_relabel`
41. Lightlike/SpinFoam/BarrettCraneUnique.lean - `SpinFoam.BC.bcNode_unique`, `SpinFoam.BC.bcNode_hyp`,
    `SpinFoam.BC.sixJSym_extreme_ne_zero`, `SpinFoam.BC.coefA_bcNodeR_half`
42. Lightlike/SpinFoam/BarrettCraneValues.lean - `SpinFoam.BC.bcVertex_eq_vertexQ`, `SpinFoam.BC.fifteenJ_sq`,
    `SpinFoam.BC.Tests.bcVertex_half`, `SpinFoam.BC.Tests.bcVertex_one`, `SpinFoam.BC.Tests.bcVertexBC_mixed`
43. Lightlike/SpinFoam/EPRLStateSum/VertexPerm.lean, SortedVertex.lean, ContractPerm.lean -
    `SpinFoam.EPRLStateSum.fifteenJSimplex_eq_contract5`, `SpinFoam.EPRLStateSum.simpEIAux_eq_contract5`,
    `SpinFoam.EPRLStateSum.contract5_perm`
44. Lightlike/SpinFoam/EPRLStateSum/ComplexNetwork.lean - `SpinFoam.EPRLStateSum.tetSum_network`
45. Lightlike/SpinFoam/EPRLStateSum/RelabelComplex.lean, NetworkCovariance.lean, LinkParity.lean, InversionParity.lean -
    `SpinFoam.EPRLStateSum.relabelComplex`, `SpinFoam.EPRLStateSum.Znet_relabel`,
    `SpinFoam.EPRLStateSum.link_sum_even`, `SpinFoam.EPRLStateSum.invSum_total_even`,
    `SpinFoam.EPRLStateSum.Znet_eq_zero`
46. Lightlike/SpinFoam/EPRLStateSum/LinkSignEven.lean - `SpinFoam.EPRLStateSum.linkSign_of_tetPar`,
    `SpinFoam.EPRLStateSum.amplitudeI_one_eq_ooguriSum`
47. Lightlike/SpinFoam/EPRLStateSum/RelabelAmplitude.lean - `SpinFoam.EPRLStateSum.Znet_relabel_eq`,
    `SpinFoam.EPRLStateSum.amplitudeI_one_relabel`, `SpinFoam.EPRLStateSum.amplitudeIeps_relabel`

## References

1. H. Ooguri, Topological lattice models in four dimensions, *Mod. Phys. Lett. A* 7 (1992) 2799.
2. A. Perez, The spin-foam approach to quantum gravity, *Living Rev. Relativ.* 16 (2013) 3.
3. L. Freidel, D. Louapre, Diffeomorphisms and spin foam models, *Nucl. Phys. B* 662 (2003) 279.
4. V. Bonzom, M. Smerlak, Bubble divergences from cellular cohomology, *Lett. Math. Phys.* 93
   (2010) 295.
5. J. W. Barrett, L. Crane, Relativistic spin networks and quantum gravity, *J. Math. Phys.* 39
   (1998) 3296.
6. J. C. Baez, J. D. Christensen, Positivity of spin foam amplitudes, *Class. Quantum Grav.* 19
   (2002) 2291.
7. J. W. Barrett, I. Naish-Guzman, The Ponzano–Regge model, *Class. Quantum Grav.* 26 (2009)
   155014.
