# SP2: two trust checks of the Racah sum asymptotics (G3-167)

**Question.** Does `racahSumAsymptotics` (`Lightlike/Asymptotics/SaddleAssembly.lean`) agree with the exact Racah sums for
growing spins, and does an estimate that works with the real terms of the sum fail? Both checks are named in the done-when
clause of SP2 (`docs/tasks/milestones.md`). The statement is proven in Lean; these are independent numerical checks, not proofs.

**Method.** The functions `racah_sum` (exact, Python integers), `geometry` and `prefactor_rate` of the existing
`scripts/asymptotics/racah_sum_asymptotics.py` (not edited, run from an inline command, 60 digits). With `l_e = λ j_e + 1/2`,
`S = Σ l_e θ_e` and `P = (vol2)^{1/4} e^{-D}`, the asymptotic value of the sum is
`cos(S + π/4) / (√(12π) (2π)² P)`. The script itself gives the normalised error (window maximum over 5 values of λ below 0.05 at
λ = 76 to 80, slope ≤ -0.8, and the two controls without `π/4` and with `(2π)^{5/2}` fail with 0.36 to 1.5).

## 1. Exact sums against the formula (MEASURED)

`exact` is `racahSum(λ j)`, `asymptotic` the formula above, `ratio = exact / asymptotic`.

| spins `j` | λ | exact | asymptotic | ratio |
|---|---|---|---|---|
| (1,1,1,1,1,1) | 10 | -8.644248e+25 | -8.188869e+25 | 1.0556 |
| | 20 | -6.248538e+54 | -6.187226e+54 | 1.0099 |
| | 40 | 4.060104e+111 | 4.039092e+111 | 1.0052 |
| | 80 | 4.697448e+225 | 4.684567e+225 | 1.0027 |
| (2,2,2,2,2,3) | 10 | -1.419058e+56 | -1.338316e+56 | 1.0603 |
| | 20 | -3.178881e+115 | -3.164169e+115 | 1.0046 |
| | 40 | 2.359490e+233 | 2.352533e+233 | 1.0030 |
| | 80 | beyond double range | beyond double range | 1.0021 |
| (2,3,3,2,3,2) | 10 | -3.291606e+62 | -8.249660e+62 | 0.3990 |
| | 20 | -2.821274e+130 | -2.789038e+130 | 1.0116 |
| | 40 | 3.960474e+262 | 3.774660e+262 | 1.0492 |
| | 80 | beyond double range | beyond double range | 1.0016 |

The ratio tends to 1 and the sign pattern (the oscillation) agrees. The point (2,3,3,2,3,2), λ = 10, is off (0.40) and λ = 40
is 5% off: that tetrahedron is close to a zero of the cosine at these values, where the relative error of `cos` is large; the
window maxima of the script are the proper test (all three pass).
Limits: three tetrahedra and four values of λ each, Euclidean data only.

## 2. The real-variable estimate fails (MEASURED)

SP2 says the summands are exponentially larger than the sum, so a method that bounds or approximates the terms in absolute
value (Riemann sums, Euler–Maclaurin) cannot see the sum. For the regular case `J = λ (1,…,1)`:

| λ | terms | `|sum|` | `Σ |term|` | `Σ|term| / |sum|` |
|---|---|---|---|---|
| 10 | 11 | 8.644e+25 | 9.593e+27 | 1.1e+02 |
| 20 | 21 | 6.249e+54 | 5.215e+57 | 8.3e+02 |
| 40 | 41 | 4.060e+111 | 4.225e+117 | 1.0e+06 |
| 80 | 81 | 4.697e+225 | 7.724e+237 | 1.6e+12 |

The cancellation factor grows exponentially in λ. So any estimate of the sum that has a relative error of ε on the terms is
wrong by about ε · 10^{12} times the sum at λ = 80; to be correct to 1% it would need ε below 1e-14. A Riemann-sum
replacement of the sum by an integral of the absolute size of the summand has an error far above the sum itself.
Limits: this shows that term-wise estimates are insufficient. It does not examine the particular step of Gurau (2008)
named in the milestone text, which was not read.

## 3. A sum with known value, outside the Racah shape (PROVED in Lean)

The done-when clause also asks for a sum with known asymptotics. `Lightlike/Asymptotics/SP2/KnownSum.lean` proves Kummer's
alternating sum of binomial squares, `Σ_t (−1)^t C(2n,t)² = (−1)^n C(2n,n)` (`kummer_alternating`), an alternating
ratio of Gamma functions `Γ(2n+1)² / (Γ(t+1)² Γ(2n−t+1)²)`, with the sum of the absolute values of the terms equal to `C(4n,2n)`
(`kummer_abs_sum`), so the terms exceed the sum by a factor at least `4^n/(4n+1)` (`kummer_cancellation`). It confirms in a case
where the answer is known exactly that estimates of the terms in absolute value cannot give the sum. It is **not** of the shape of
Racah's sum (four Gamma functions in the denominator and no `Γ(t+2)`), so it is not a check of `racahSumAsymptotics` itself;
the saddle-point statement proved on main is only for Racah's shape, which SP2 says is agreed with SF8.
