# G3-073 (non-MHV, step 3): polarization vectors and their completeness relation

Lean: `Lightlike/GR/Polarization.lean` (on G3-072's `SpinorHelicity.lean`).

## Source read (pdftotext of arXiv:1308.1697v2)

H. Elvang, Y. Huang, *Scattering Amplitudes*, §2.4:
* p. 16: the polarization vectors (2.49) `ε^μ_−(p; q) = −⟨p|γ^μ|q]/(√2 [qp])`, `ε^μ_+(p; q) = −⟨q|γ^μ|p]/(√2 ⟨qp⟩)`.
* p. 17: (2.50); "The arbitrariness in the choice of reference spinor reflects gauge invariance, namely that one is free to shift the
  polarization vector with any constant times the momentum vector … This does not change the on-shell amplitude A_n, as encoded in the
  familiar Ward identity p_μ A^μ_n = 0"; Exercise 2.10(c): `(ε₊(p; q))_{aḃ} = (√2/⟨qp⟩)|p]⟨q|`, and (d), the shift by `c₊ p^μ`.

Checked numerically before the Lean statements (random complex spinors): transversality, `ε₊² = 0`, `ε₊·ε₋ = −1`, the gauge shift, and the
completeness relation with the sign `ε₊^μ ε₋^ν + ε₋^μ ε₊^ν = −(η^{μν} − (p^μq^ν + q^μp^ν)/(p·q))` in the mostly-plus metric.

## How each Lean statement matches

* `epsPlus`, `epsMinus`: Exercise 2.10(c) and its negative-helicity analogue, as bispinors `momOf`.
* `mdot_epsPlus`, `mdot_epsMinus` (`p·ε± = 0`, p. 17), `mdot_epsPlus_self`, `mdot_epsPlus_epsMinus` (`ε₊·ε₋ = −1`).
* `epsPlus_sub_epsPlus`: changing the reference spinor shifts `ε₊` by `−√2⟨qq'⟩/(⟨qp⟩⟨q'p⟩) p` (p. 17, Exercise 2.10(d)); via
  `schouten_vec`.
* `completeness_eps`: the completeness relation, with the reference momentum `q = −|q]⟨q|`.
* Helpers: `mdot_momOf_vecMulVec` (`mdot` of two rank-one bispinors is `½⟨bd⟩[ac]`), `momOf_smul`, `momOf_sub`, `nullMom_eq_momOf`.

## Differences

None. The completeness relation is not printed in the source at the pages read; it is the step of the factorization argument for
which the plan of this item needs it.
