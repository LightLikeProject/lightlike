# HA2 (G3-143): the factor 4 between the library and Perez–Rovelli (A11)/(A16)

Question: why is `plancherel_trace_perezRovelli` (`1/(32π⁴)`, `Lightlike/Lorentz/Plancherel.lean`) four times
smaller than the `1/(8π⁴)` that Perez–Rovelli (gr-qc/0011037, App. A) write in (A11) and (A16)?

## What is established (MEASURED unless tagged)

1. Same objects: the library's `integral_haarC_eq_bruhat` is PR (A8) and `coeFn_principalSeries_perezRovelli` is
   PR (A6) with `μ = iσ`, `σ = 2ρ`. The cause is therefore not a different Haar measure or representation.
2. Range: all `(n, σ) ∈ ℤ × ℝ` count each class twice, so restricting to `σ ≥ 0` gives `1/(16π⁴)`, not `1/(8π⁴)`:
   the range accounts for a factor 2 at most, and the remaining factor 2 is not a range effect.
3. The library constant is corroborated by two independent routes, both in the repository: the numerical check
   `scripts/lorentz/plancherel_check.py` and the K-biinvariant hand check (polar form `4π³ ∫ F(cosh r) sinh² r dr`);
   and by Rühl as quoted by Simão (arXiv:2405.01360, App. B.3): `dg_R = (2π)⁻⁴ haarC` with constant `1/2` is
   `(1/2)(2π)⁻⁴ = 1/(32π⁴)` in `haarC`. (Simão's quotation of Rühl; Rühl's book not read.)
4. `testLF_perezRovelli_constant` is a Lean witness that `1/(8π⁴)` is wrong for `haarC` and the stated trace.

## What PR App. A says (text read: pdftotext extracts of the arXiv PDFs of gr-qc/0011037 and gr-qc/0009021,
App. A, (A6)-(A16); web text, untrusted)

Citation: Perez–Rovelli is cited here and in the library as arXiv:gr-qc/0011037 (*3+1 spinfoam model of quantum
gravity with spacelike and timelike components*, Phys. Rev. D 64 (2001) 064002). Its Appendix A, "Representation
theory of SL(2,C)", carries (A6)-(A16), with (A11) `f(g) = 1/(8π⁴) Σ_n ∫ Tr[F(n,ρ) T_{n,ρ}(g⁻¹)] (n²+ρ²) dρ` and (A16)
`δ(g) = 1/(8π⁴) Σ_n ∫ Tr[T_{n,ρ}(g)] (n²+ρ²) dρ`. The earlier paper gr-qc/0009021 (*Spin foam model for Lorentzian
General Relativity*, Phys. Rev. D 63 (2001) 041501) prints the same appendix with the same labels (A1)-(A19) (the
text differs only in typesetting and in the reference numbers), so the equations below are the same in both; the
library cites the one number gr-qc/0011037 everywhere.

- (A6): `T^n_μ(g)φ(z) = (βz+δ)^{(μ+n)/2-1} (β̄z̄+δ̄)^{(μ-n)/2-1} φ((αz+γ)/(βz+δ))`, principal series `μ = iρ`,
  so PR's `ρ` is the library's `σ = 2ρ_lib` (modulus power `iρ_PR - 2`, library `2iρ_lib - 2`). `n` is the same.
- (A7): `(φ,ψ) = ∫ φ̄ψ dz`, `dz = d Re z d Im z`: the library's `d²z`. (A12)-(A15): trace `∫ T(z,z;g) dz`, kernel
  with a complex delta, same objects as the library.
- (A8): `dg = (i/2)³ dβ dγ dδ/|δ|²`, "where dα, dβ, … denote integration over the real and imaginary part
  respectively". Read as `d²β d²γ d²δ/|δ|²` with the prefactor `(i/2)³` literally, `dg` is not real. Read with
  `dβ = dβ∧dβ̄ = -2i d²β` the prefactor is `1` per variable and `dg = haarC` (the reading used by the library).
- (A11), (A16): `1/(8π⁴) Σ_n ∫ … (n² + ρ²) dρ`; the range of `n` and `ρ` is not stated (footnote 5 only restricts to the
  principal series). The equivalence `T_{n,ρ} ≅ T_{-n,-ρ}` is stated after (A6).

## Does the (i/2)³ reading explain a factor?  (measured arithmetic; Perez–Rovelli's intent is not stated)

The constant in the trace form scales inversely with the Haar measure. If `dg = |(i/2)³| haarC = haarC/8` were meant,
the constant would be `8/(32π⁴) = 1/(4π⁴)`, not `1/(8π⁴)`: a factor 8, not 4, so that reading does not explain it.
With `dg = haarC` the constants differ by exactly 4 and the range (all `ℝ`, factor 2 at most, see 2.) does not
account for it. No reading of (A8), (A7), (A6) and the range that was checked gives `1/(8π⁴)` with a consistent
`haarC`. Perez–Rovelli's own derivation of (A11) is not in App. A (the formula is quoted, not derived), so the step
cannot be located from this text.

## Status

**Conclusion: Perez–Rovelli's printed 1/(8π⁴) in (A11) and (A16) is 4× too large; the library agrees with Rühl as
quoted by Simão.**

Evidence:

- Simão, arXiv:2405.01360, App. B.1, B.3 and eq. (B.3.1) (checked against the thesis text: the labels, the constant `1/2`
  and the measure are as `Plancherel.lean` quotes them). B.1 gives the principal series with the labels `ν = −n`,
  `ρ = σ` of (A6); B.3 gives `f(1) = ½ ∫ dρ Σ_ν (ν² + ρ²) Tr D^χ(∫ dg f(g) D^χ(g))`; (B.3.1) gives
  `dg = (2π)⁻⁴ haarC`. In Perez–Rovelli's variables this is `½ · (2π)⁻⁴ = 1/(32π⁴)`, the library's constant.
  Rühl's book itself was not read; this is Simão's quotation of it.
- `plancherel_trace_perezRovelli` and `plancherel_trace_ruhl` (`Lightlike/Lorentz/Plancherel.lean`): the library's
  theorem in Perez–Rovelli's variables with `1/(32π⁴)`, and in Rühl's variables with `1/2` and `dg_R = (2π)⁻⁴ haarC`.
- `testLF_perezRovelli_constant` (`Lightlike/Lorentz/PlancherelTests.lean`): with `1/(8π⁴)` the formula gives
  `4 F(1) ≠ F(1)`.
- `scripts/lorentz/plancherel_check.py`: a numerical check of the constant from the kernel alone, including `n ≠ 0`.

Kind of the difference with the source: a misprint in the source (not a convention): the Haar measure (A8) and the
representations (A6) are the library's, and the range of `σ` accounts for a factor 2 at most.

The citation of Perez–Rovelli in `PlancherelOperator.lean` now gives the title of arXiv:gr-qc/0011037, as `Plancherel.lean`
does.
