# SP2 / G3-167: a Racah sum with a known value (second attempt)

**Question.** Is there a sum in the exact shape of `racahSum` whose value is known independently, so that the definition (signs, factorials, ranges) is checked against an exact value?

**Result (PROVED in Lean, `Lightlike/Asymptotics/SP2/RacahZeroSpin.lean`).** For a triad `(a, b, c)`,
`racahSum ![0, a, a, c, b, b] = (-1)^(a+b+c) (a+b+c+1)! / ((b+c-a)! (a+c-b)! (a+b-c)!)` (`racahSum_zero_spin`),
computed from the definition. With `racahFormula` and the 6j symbol with a zero spin (`sixJSym_zero_left`, proved separately),
`Δ · racahSum = (-1)^(a+b+c) / √((2a+1)(2b+1))` (`racahDelta_mul_racahSum_zero_spin`): the two independent computations agree, so the sign
and factorial conventions of `racahSum` are confirmed in the exact shape (MEASURED by proof).

**Concrete obstruction (why this is not a check of the asymptotics).**
1. With a zero spin the face and quadrilateral bounds `max(2a, 2b, a+b+c) ≤ t ≤ min(a+b+c, 2a+2b)` leave the single term `t = a+b+c`: no cancellation, so
   it does not exercise the alternating-sum cancellation that SP2 is about (cf. `docs/notes/sp2-racah-trust-checks.md` on `oscillatory/sp2-known-sum`: the terms exceed the sum by `4^n/(4n+1)` for Kummer's sum).
2. A zero spin is not a Euclidean tetrahedron (`IsEuclid` fails), so `racahSumAsymptotics` does not apply; the known value is exact for every `λ`, but there
   is no saddle.
3. The same holds for the stretched triads (`c = a + b`) and other boundary cases: the sum collapses to one term. A closed form for a cancelling Racah sum
   (more than one term, all spins positive) is a balanced `4F3(1)`; Saalschütz applies when one numerator parameter is `-n` and a 3F2 remains, which for the
   Racah shape needs one 6j entry to be `1/2` or `0` (two or one terms). The orthogonality `racah_sum` (`Lightlike/SpinFoam/BingsHouse.lean`) is a known value of a sum of 6j
   symbols, not of the `t`-sum of one 6j.
**Verdict.** G3-167 stays PARTIAL on the "known asymptotics of a Racah-shaped sum": no Racah-shaped sum with several terms and a closed form was found; the exact
single-term value is proved and the numerical checks (`docs/notes/sp2-racah-trust-checks.md`) remain the evidence for the asymptotic statement. Limits: the
search for closed forms was by the structure above, not exhaustive.
