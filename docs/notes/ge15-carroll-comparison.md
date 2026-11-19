# GE15: comparison of the Einstein-Hilbert variation with Carroll (read 18 November 2026)

Source read: S. M. Carroll, *Lecture Notes on General Relativity* (1997), arXiv gr-qc/9712019, pdf text, ch. 4; page numbers of the arXiv pdf.

* The action `S_H = ∫ dⁿx √−g R`, eq. (4.54)-(4.55), p. 114. With the cosmological constant `S = ∫ dⁿx √−g (R − 2Λ)`, eq. (4.73), p. 117-118: our density is `√|det g| (R − 2Λ)`: match.
* Variation `δS = ∫ √−g g^{μν} δR_{μν} + √−g R_{μν} δg^{μν} + R δ√−g`, eq. (4.56); the Palatini identity `δR^ρ_{μλν} = ∇_λ(δΓ^ρ_{νμ}) − ∇_ν(δΓ^ρ_{λμ})`, eq. (4.60), p. 115: our
  `palatini_coord` (the coordinate form: `√|g| g^{σν} δR_{σν}` is the divergence of `√|g| W`) is this identity contracted with `g^{μν}`; the term `(δS)_1` is a divergence and drops
  by Stokes (4.61), p. 115, where Carroll requires the variation to vanish at infinity: ours is a compact support perturbation, the divergence integrates to zero (a proved statement, not a
  quoted one).
* `δ√−g = −½ √−g g_{μν} δg^{μν}`, eq. (4.65), p. 116 (from `Tr(M⁻¹ δM) = δ(det M)/det M`, (4.63)): our `hasDerivAt_sqrt_abs` and the Jacobi formula.
* Result `δS = ∫ √−g (R_{μν} − ½ R g_{μν}) δg^{μν}`, (4.66), and the vacuum equations `R_{μν} − ½ R g_{μν} = 0`, (4.67), p. 116: our `eh_first_variation` and `isEHCritical_iff`.

## Differences
* Carroll varies with respect to the inverse metric `δg^{μν}`; ours perturbs the metric `g + t h`; `δg^{μν} = −g^{μα} g^{νβ} h_{αβ}` makes them equivalent, and the sign in our result
  (minus the Einstein tensor contracted with `h`) is the one this gives. Carroll does not prove the statement for a compact region with a given perturbation; he concludes (4.67) from
  "should vanish for arbitrary variations", which is the fundamental lemma used here.
* Carroll's derivation is on a manifold with covariant derivatives; ours is in coordinates on `ℝⁿ` (the manifold version is not included): weaker than the source's setting.
* Carroll's derivation of the Einstein equations with matter (4.68) onward is not covered.
