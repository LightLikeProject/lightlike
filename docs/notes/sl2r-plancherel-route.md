# The Plancherel formula of SL(2,ℝ): the route

Notation. `G = SL(2,ℝ)` with the Haar measure `dg = haarR`, normalised by `∫_G Φ(cosh d(g)) dg = 4π² ∫_{t>1} Φ(t) dt`
for `cosh d(g) = (a²+b²+c²+d²)/2` (`RadialHaar.lean`). `K = SO(2)`, `rot θ`. `P^{ε,iν}` (`ε ∈ {0,1}`, `ν ≥ 0`) is the
unitary principal series on `L²(ℝ)` (`SL2RPrincipal.lean`); `D_n^±` (`n ≥ 2`) are the discrete series on the weighted
Bergman spaces `A²_n` (`SL2RBergman.lean`) and their complex conjugates. For a unitary representation `π` and
`f ∈ C_c^∞(G)`, `π(f) = ∫_G f(g) π(g) dg` is Hilbert-Schmidt.

## Target

(P) For every `f ∈ C_c^∞(G)`,

`∫_G |f|² dg = Σ_{ε∈{0,1}} ∫_0^∞ ‖P^{ε,iν}(f)‖²_HS μ_ε(ν) dν + Σ_{n≥2} d_n (‖D_n^+(f)‖²_HS + ‖D_n^-(f)‖²_HS)`

with `μ_0(ν) = c ν tanh(πν/2)`, `μ_1(ν) = c ν coth(πν/2)`, `d_n = (n-1) c'`; the constants `c, c'` are fixed by the
steps below (the K-biinvariant case gives `c = 1/4`, see `norm_sq_eq_sph`; the formal degree gives `c' = 1/(8π²)`).

## Step A. K-type decomposition

For `f ∈ C_c^∞(G)` and integers `k, l` of the same parity, `f_{kl}(g) = (2π)^{-2} ∫∫ f(rot α · g · rot β) e^{-i(kα+lβ)} dα dβ`.

* A1. `f = Σ_{k,l} f_{kl}` and `∫|f|² = Σ ∫|f_{kl}|²` (Fourier series on `K × K`, uniformly convergent with every derivative
  for `f` smooth, compact support).
* A2. For a unitary representation `π` with a Hilbert basis of `K`-eigenvectors `e_k`, the matrix `⟨e_k, π(f) e_l⟩`
  depends only on `f_{kl}`, and `‖π(f)‖²_HS = Σ_{k,l} |⟨e_k, π(f) e_l⟩|²`.
* A3. (Cartan decomposition.) `G = K A⁺ K`, `g = rot α · a_r · rot β`, `dg` is a constant multiple of `sinh r dr dα dβ`; a
  function of type `(k,l)` is `f_{kl}(rot α a_r rot β) = e^{i(kα+lβ)} F_{kl}(r)` and `‖f_{kl}‖² = c₀ ∫_0^∞ |F_{kl}(r)|² sinh r dr`.

## Step B. Continuous part, one K-type at a time

For `(k,l)` the matrix coefficient `⟨e_k, P^{ε,iν}(a_r) e_l⟩ = φ^{kl}_ν(r)` is an associated Legendre / Jacobi function
`φ^{(α,β)}_λ` with `α = 0`, `β = |k-l|/2`-type parameters, `λ = ν/2`. The transform of `F_{kl}` is `∫ F_{kl}(r) φ^{kl}_ν(r) sinh r dr`.

* B1. (Abel transform of type `(k,l)`.) A transform `A_{kl}` of `F_{kl}` to an even function on `ℝ` with
  `φ^{kl}_ν`-transform of `F` = Fourier transform of `A_{kl} F` at `ν/2`; for `(k,l) = (0,0)` this is `abelTransform`.
* B2. (Plancherel for the Jacobi transform.) For `F ∈ C_c^∞([0,∞))` of type `(k,l)`,
  `∫|F|² sinh r dr = ∫_0^∞ |F̂(ν)|² dm_{kl}(ν) + (discrete terms)` with `dm_{kl}` the Harish-Chandra c-function density
  `|c_{kl}(ν)|^{-2} dν` computed from the Gamma-function expression of `c_{kl}`; the discrete terms occur exactly for
  `|k|, |l| ≥ 2` of equal sign.
* B3. `c_{kl}` is the same for all `(k,l)` of a given parity class up to the factor that the matrix coefficient
  normalisation produces: it equals `ν tanh(πν/2)` for even and `ν coth(πν/2)` for odd classes.

## Step B′. The ladder-operator route from the spherical case to all K-types

The Lie algebra acts on `C^∞(G)` by the left- and right-invariant vector fields; with `L_0 = -iΛ_0`, `L_{±1} = ∓Λ_1 - iΛ_2`
(Kitaev, arXiv:1711.08169, eq. (46)-(47)) a function of type `(l, r)` (`L_0^L Ψ = -lΨ`, `L_0^R Ψ = -rΨ`) is
`Ψ(e^{ϕΛ_0} e^{ξΛ_1} e^{-ϑΛ_0}) = e^{i(lϕ+rϑ)} f(u)`, `u = tanh²(ξ/2)`, and the left raising and lowering operators act as

`L^L_{±1}(l, r) = ±(1-u) u^{1/2} ∂_u - (l+r)/2 · u^{-1/2} - (l-r)/2 · u^{1/2}`, `(l, r) ↦ (l ± 1, r)`.

On the Casimir eigenfunctions `A_{λ,l,r}` (eq. (56)) they satisfy `L^L_{-1} A_{λ,l,r} = -A_{λ,l-1,r}` and
`L^L_{1} A_{λ,l,r} = -(l+λ)(l+1-λ) A_{λ,l+1,r}` (eq. (60)); for the principal series `λ = 1/2 + iρ` the factor is
`(l+1/2)² + ρ²`.

* B′1. `L^L_{±1}` are the vector fields of the complexified Lie algebra acting on `C_c^∞(G)`; `⟨L_{+1} f, g⟩ = -⟨f, L_{-1} g⟩`
  for `f, g ∈ C_c^∞(G)` (integration by parts for the Haar measure of the unimodular group `G`).
* B′2. On the representation side `π(L_{±1} f) = dπ(L_{±1}) π(f)`, and in the `K`-basis `e_l` of `P^{ε,iρ}` the raising operator
  has `‖dπ(L_{+1}) e_l‖² = (l+1/2)² + ρ²` (`SL2RCasimir.lean`).
* B′3. (Recursion.) If `∫|f|² = ∫ |⟨e_l, π(f) e_r⟩|² dμ(ρ)` for all `f` of type `(l, r)` in a subspace `V_{l,r}`, then the same holds, with
  the same `μ`, for `L_{+1} V_{l,r} ⊂ V_{l+1,r}`: both sides change by the factor `(l+1/2)² + ρ²`, using `L_{-1} L_{+1} = -Q + (L_0)² - L_0`
  and the Casimir eigenvalue.
* B′4. (Range.) For `f ∈ C_c^∞(G)` of type `(l+1, r)` orthogonal to the kernel of `L_{-1}` on the discrete series, `f ∈ L_{+1} C_c^∞(G)`;
  the first-order ODE `L_{+1} h = f` is solved by integration along `ξ` and the compactness of the support is the orthogonality
  to the lowest weight vectors. This is where the discrete series enters (`C1`-`C4`).
* B′5. Induction on `|l|` from the spherical case `(0, 0)` (`norm_sq_eq_sph`) for `l ≡ r ≡ 0 (mod 2)` and from a base case `(1, 1)`
  for `l ≡ r ≡ 1 (mod 2)`; the latter is the Plancherel formula on `L²(ℍ, y^{1} dμ_ℍ)`-sections and needs its own Mehler-Fock-type
  transform (`ρ coth(πρ)`).

## Step C. Discrete series

* C1. (Matrix coefficient of the lowest weight vector.) For `e_0 = lowestVec n` the coefficient
  `⟨D_n(g) e_0, e_0⟩ = (2/(a+d+i(b-c)))^n`, hence `|⟨D_n(g) e_0, e_0⟩|² = (2/(1+cosh d(g)))^n`.
* C2. (Formal degree.) `∫_G |⟨D_n(g) e_0, e_0⟩|² dg = 8π²/(n-1)`, from C1 and the radial formula for `dg`; with
  Schur orthogonality for the irreducible `D_n^+`, `∫_G |⟨D_n(g)v, w⟩|² dg = (8π²/(n-1)) ‖v‖²‖w‖²`.
* C3. (Irreducibility.) `A²_n` is irreducible for `D_n^+`: a closed invariant subspace contains `e_0`, since the
  `K`-eigenvectors `e_m` have distinct weights and generate the Bergman space.
* C4. For `f` of `K`-type `(k,l)` with `k, l ≥ n`, `n ≡ k` and equal sign, the part of `f` along `D_n^+` is
  `d_n ‖D_n^+(f)‖²_HS`; it equals the discrete term of B2.

## Step D. Assembly

* D1. Summing B2 over `(k,l)`, with A1 and A2, gives the continuous part of (P) for every `f ∈ C_c^∞(G)`.
* D2. Summing C4 over `n` gives the discrete part.
* D3. Hence (P). The theorem `plancherel_SL2R` takes B2 and C3 as named hypotheses (`JacobiPlancherel`,
  `DiscreteIrreducible`) and concludes (P).

## References

* S. Lang, *SL₂(ℝ)*, Springer GTM 105 (1985), Chapters VII-IX (K-types and Plancherel).
* A. W. Knapp, *Representation Theory of Semisimple Groups*, Princeton (1986), Chapter II §5 and Chapter XI.
* T. H. Koornwinder, *Jacobi functions and analysis on noncompact semisimple Lie groups*, in *Special Functions: Group
  Theoretical Aspects and Applications*, Reidel (1984).
* A. Kitaev, arXiv:1711.08169, Section 4 (the density `s tanh(πs)`).
