# G1-011 (GE4): the round-sphere checks are met, the general trapped-surface statements are not

On main: `IsTrappedSphere` for coordinate round spheres, `nullExpansion_sch` (`2k¹/r₀`), `schwarzschild_interior_trapped` for `0 < r₀ < 2M`, and its non-vacuity; `minkowski_not_trapped` (round spheres are not trapped, expansions `±2/r`) is in the queue (regge).
Missing: "Minkowski has no closed trapped surface" for an arbitrary compact spacelike 2-surface (it needs a maximum-principle argument on a closed surface, or convexity of the spacelike hypersurface, not just the round spheres).
Missing: the closed trapped surface on a manifold (compact codimension-2 submanifold with `θ < 0` for both null normals), null focusing along geodesics orthogonal to it, and the generators of `∂J⁺(S)`; these need submanifold and normal-bundle geometry absent upstream.
The Penrose assembly and the achronal boundary are regge's (in the queue), not touched here.
Status (24 Nov 2026): record partial; no Lean file for the Minkowski spheres here (regge has it).
