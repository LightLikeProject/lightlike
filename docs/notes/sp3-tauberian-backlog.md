# SP3: what the Tauberian results leave open

Proved: Karamata's theorem (`Lightlike.Tauberian.karamata`), the logarithmic Ingham theorem
(`ingham_log`: `β log L(β) → a` gives `log F(X) / (2√(aX)) → 1`), and Mukhametzhanov–Zhiboedov's (1.8)
(`cardy_mz`): for a positive spectrum whose partition function is modular invariant and has the high-temperature
form `Z(β) = e^{a/β}(1 + O(e^{-g/β}))`, the integrated density has the Cardy asymptotics with relative error `O(Δ^{-1/2})`.

The general-measure form (a positive measure with only `L(β) ~ C β^b e^{a/β}` on the real axis has the asymptotics
of `F`) is false: Bringmann–Jennings-Shaffer–Mahlburg, arXiv:1910.03036, Section 3.2, give a counterexample. So the
milestone item is ticked on `cardy_mz`, with the difference "MZ (1.8) assumes modular invariance" (owner decision D14 = (A)).

Backlog (open, not claimed):

1. **Ingham's theorem with a sector bound** (BJM Theorem 4.1): `F(X)` has the asymptotics of the Laplace transform when
   `L(z) = O(χ(|z|) e^{φ(|z|)})` in the sectors `|Im z| ≤ Δ Re z`. Needs a complex-`β` hypothesis and the contour
   argument; the library has the pole-free smoothing of `CardyCounting.lean`, not Ingham's original argument.
2. **MZ with the high-temperature hypothesis for complex `β`** is weaker in the library (real `β` only); the formal
   theorem is stronger there, nothing to prove.
