# G1-012 step D: focal bound (plan, 24 Nov 2026)

Goal: `NormalisedFocalBound T S Λ` (Rows/G1_012/ExpCompact.lean) for a closed trapped surface S under NEC.
Content: a future null geodesic γ from s∈S with γ(L)∉I⁺(S) has  -g(γ'(0),X)·L ≤ Λ.

Needed, none present on main (grep: only chart-level focusing in Spacetime/Raychaudhuri*.lean):
1. Normal null congruence off S: geodesics with initial data (s, k(s)), k smooth future null normal, flowed by the geodesic flow (ExpFlow `FlowGerm` gives continuity, smoothness of the flow in z is NOT yet available).
2. Expansion θ(t) of that congruence along γ, satisfying Raychaudhuri θ' ≤ -θ²/(n-2) - Ric(γ',γ') (chart-level RaychaudhuriFocusing exists; manifold transfer = RaychaudhuriManifold.lean).
3. θ(0) ≤ -c·(-g(k,X)) uniformly on compact S (needs hypothesis Θ<0 of IsClosedTrappedSurface + compactness; scale-covariant in k).
4. Focal point ⇒ leaves ∂J⁺(S): γ|[0,L] orthogonal to S with focal point before L ⇒ γ(L)∈I⁺(S) (index form / timelike deformation; the first-variation machinery NullVariation.lean does first order only).
Step 4 is the hard one; steps 1-3 give the bound Λ = 2/c.

Fallback if 4 stays out of reach: state it as the single named hypothesis `NoPastFocalGenerator`, keep 1-3 proved.

## Survey (24 Nov, later)
Spacetime/RaychaudhuriNull.lean already has chart-level `raychaudhuri_null_focusing` (n>2; null geodesic field v with auxiliary N, R(v,v)≥0, θ(γ0)<0 gives L ≤ m/|θ(γ0)| for an integral curve of v defined on [0,L)).
So parts 2-3 reduce to: a smooth null geodesic field v on an open set containing γ|[0,L), normal to S at γ(0) with θ<0 there. Such a field exists only up to the first focal point; "no field up to L" is exactly the focal-point (part 4) statement. Part 4 is the crux and the only genuinely new geometry.

## Route (24 Nov, later 2)
A field v is not needed: Raychaudhuri along γ only needs the area element A(t) = |det dF| of F(s,t) = exp_s(t k(s)) restricted to the (n-2)-dim cross-section, with θ = A'/A and (A^{1/(n-2)})'' ≤ 0 under NEC. Focal point = A(t₀)=0. Then A^{1/(n-2)} concave, positive at 0, derivative ≤ -c/(n-2)·A^{1/(n-2)} at 0 ⇒ zero by t = (n-2)/c.
Sub-theories to build, in order:
 D1 smooth dependence of the manifold geodesic flow on initial data along γ (ExpFlow gives continuity only; chart-level `exists_expMap_joint` gives local smoothness).
 D2 null normal bundle of S = f⁻¹(0) and a smooth null normal field k (exists locally; IsClosedTrappedSurface quantifies over global fields, so a global field is needed or the hypothesis is applied after a partition of unity: NOT available, flag).
 D3 Jacobi/Riccati for A(t); D4 focal ⇒ γ(L) ∈ I⁺(S) (second variation, nothing exists).

## Hidden gap: global null normal field
`IsClosedTrappedSurface` (Rows/G1_012/TrappedSurface.lean) concludes `frameExpansion < 0` only for fields k that are *globally smooth on M* and future null normals along S. Using it needs such a k. S = f⁻¹(0) with f : M → ℝ² a submersion along S has trivial normal bundle, spanned by grad f¹, grad f² (metric-dual of df), but the null combinations a·∇f¹ + b·∇f² are null only along a curve of (a,b) fixed by the induced metric on the normal plane, which is Lorentzian (S spacelike) with two null lines; choosing the future one smoothly along S needs the two lines to be globally distinguishable by the time orientation (true: g(k,T)<0 selects the future cone, the two null lines are the two future null rays) and then a smooth extension of k from S to M (Tietze/partition of unity for sections of a vector bundle, not yet in the repo). If S is not assumed spacelike, `IsClosedTrappedSurface` also needs that. So D2 = (i) S spacelike from the frame condition, (ii) smooth future null normal along S, (iii) smooth extension to M. None is present.

## Status 24 Nov (late): G1-012 assembled modulo NormalisedFocalBound
Proved and on branches: A ExpFlow, B+C+E ExpCompact (partial), D1 FlowSmooth, hproj/hopen (FieldFlow, ProjectionLines, Projection), PenroseFocal.penrose_of_focal_bound (regge/focal 8fe60d4).
Remaining: NormalisedFocalBound T S Λ for a closed trapped surface under NEC.

### Second hidden gap: spacelike
`IsClosedTrappedSurface` is vacuous at points where T_xS is not spacelike (no orthonormal (n-2)-frame exists there). The proof needs S spacelike: add field `∀ x ∈ S, ∀ v, df_x v = 0 → v ≠ 0 → g(v,v) > 0`. (Stronger hypothesis, a "weaker" difference; the source says spacelike.)

### D2 construction of the global smooth future null normals (no partition of unity needed beyond a bump)
f = (f¹,f²) with S = f⁻¹(0), df surjective on S. N_i := g-dual of df^i (smooth vector fields on M, needs the smooth metric dual). On a neighbourhood U of S where the 2x2 Gram matrix G_ij = g(N_i,N_j) has det G < 0 (open, contains S when S spacelike), the plane P_x = span(N_1,N_2) is Lorentzian. τ' := orthogonal projection of T.X onto P (timelike in P), w := rotation of τ' in P by the area form (N_1∧N_2), k± := τ' ± w normalised by √(-g(τ',τ')). Both smooth on U, future null normal along S. Cut off with a smooth bump (=1 near S, supp in U) to a global field.

Decision (24 Nov): the old `IsClosedTrappedSurface` stays untouched. New def `IsClosedTrappedSpacelikeSurface` (Rows/G1_012/TrappedSpacelike.lean) = same data plus the spacelike clause on ker df; D2–D4 and the Penrose assembly use the new one. Queue difference text: "old def vacuous where T_xS is not spacelike; new def adds spacelike per Senovilla–Garfinkle".

## D2 done (24 Nov, late)
`exists_null_normal_pair` (Rows/G1_012/TrappedNormals.lean): for a closed trapped spacelike surface there are smooth global fields `k₁, k₂` on `M`, future null normals along `S`, such that every future null normal at a point of `S` is a positive multiple of one of them, and `frameExpansion < 0` for both (the trapped hypothesis). Construction: `∇fⁱ` (metric duals), Gram matrix `G`, `D = -det G > 0` and `Q > 0` from spacelikeness (`PlaneData.D_pos_Q_pos`), `k_± = √D·τ' ± Rτ'` in the basis `∇f¹, ∇f²` (`kα`, `kβ`), smooth on `{D > 0}`, cut off by a smooth bump.
Remaining: D3 (expansion along a generator and its Riccati inequality), D4 (a focal point puts the end of the generator in `I⁺(S)`).
