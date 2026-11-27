# Statement card: the large-spin asymptotic formula of the Euclidean EPRL vertex (LL-0047)

| | |
|---|---|
| Result | `Lightlike.Asymptotics.EPRL.eprlAsymptoticFormula : EPRLAsymptoticFormula`, entry LL-0047 (`main: true`); its input `coh15jAsymptoticFormula : Coh15jAsymptoticFormula` is proved alongside |
| Files | statements `Lightlike/Asymptotics/EPRL/Formula.lean` (`Coh15jAsymptoticFormula`, line 59; `EPRLAsymptoticFormula`, line 78); proofs `Lightlike/Asymptotics/EPRL/MaxSetFinite.lean` line 340 and `EPRLFormula.lean` line 84 (main at `eeba9873b`) |
| Sources | Barrett, Dowdall, Fairbairn, Gomes, Hellmann, *Asymptotic analysis of the EPRL four-simplex amplitude*, J. Math. Phys. 50 (2009) 112504, arXiv:0902.1170 (**BDFGH**): Theorem 1 (p. 12), the definition of `N` (p. 29), eq. (5), (10), (11), (71)–(76). Barrett, Fairbairn, Hellmann, *Quantum gravity asymptotics from the SU(2) 15j symbol*, arXiv:0912.4907 (**BFH**): eq. (1), (16), (26) |
| Card written | 27 Nov 2026, from page images of the two papers (every formula below was read off the rendered page, not from extracted text) and the Lean files |

**What this card is for.** The catalogue says "the large-spin asymptotic formula of the Euclidean EPRL vertex amplitude in coherent boundary states". The Lean statement is about the *coherent integral* `eprlCoh`, not about the vertex `Spin4.eprlVertex`. Section 4, difference 1, says exactly what is and is not connected, and section 6 records a catalogue note that contradicts a proven theorem.

## 1. The source theorem, word for word

BDFGH, p. 12 (page image):

> "A formula is asymptotic if the error term is bounded by a constant times one more power of λ⁻¹ than that stated in the asymptotic formula."
>
> **Theorem 1. (Asymptotic formula)** *Given a set* 𝓑 = {n_ab, k_ab}_{a≠b} *of boundary data, then in the limit λ → ∞*
>
> *1. If* 𝓑 *is a non-degenerate 4-simplex geometry, and ψ_λ is the associated Regge state, then*
>
> f₄(ψ_λ) ∼ (−1)^{χ′} (2π/λ)¹² [ 2N^γ_{+−} cos( λγ Σ_{a<b} k_ab Θ_ab ) + N^γ_{++} exp( iλ Σ_{a<b} k_ab Θ_ab ) + N^γ_{−−} exp( −iλ Σ_{a<b} k_ab Θ_ab ) ]  (20)
>
> *The numbers N^γ_{+−}, N^γ_{++}, N^γ_{−−} are independent of λ and are defined below.*
>
> *2. For a set of boundary data which is not a non-degenerate 4-geometry but forms a vector geometry the asymptotic formula is* |f₄(ψ_λ)| ∼ (2π/λ)¹² N  (21)
>
> *3. For a set of boundary data that is neither a non-degenerate 4-geometry nor a vector geometry, the amplitude is supressed and does not contribute for large λ.* f₄(ψ_λ) = o(λ^{−M}) ∀M  (22)

The constants, BDFGH p. 29, end of the proof for γ < 1 (page image):

> "This establishes the non degenerate boundary data with γ < 1 part of theorem 1 with
> N^γ_{ε₁ε₂} = 2⁸/(4π)¹⁶ · (det H({X^{ε₁}, X^{ε₂}}))^{−1/2}
> and ε₁, ε₂ = ±."

The Hessian, BDFGH p. 30 (image), eq. (71)–(76) for γ < 1: *"Here the Hessian matrix of the full action is a 24 × 24 matrix defined as H^{ij,±±}_{cd} = (∂²S / ∂X^{i,±}_c ∂X^{j,±}_d) … As the action is a sum of left and right sector, the terms off diagonal with respect to the ± index are 0 and H is a block diagonal matrix* H = ( H^{−−} 0 ; 0 H^{++} ) *where H^{++}, H^{−−} are the 12 × 12 Hessian matrices for the left and right sectors respectively. As the Hessian is block diagonal, its determinant can be written as the product of the determinants of the two submatrices* det(H) = det(H^{−−}) det(H^{++}) (73)", and at the critical point (75): H^{ij,++}_{cc}(X⁺) = −¼ Σ_{b≠c} 2j⁺_{cb} (δ^{ij} − n^{i,+}_{cb} n^{j,+}_{cb}), (76): H^{ij,++}_{cd}(X⁺) = −¼ 2j⁺_{cd} (δ^{ij} − i ε^{ijk} n^{k,+}_{cd} − n^{i,+}_{cd} n^{j,+}_{cd}).

How f₄ is defined, BDFGH p. 4, eq. (5), p. 9, eq. (10), (11) (page images):

> f₄ = (−1)^χ ∫_{Spin(4)⁵} Π_a dX⁺_a dX⁻_a ( ⊗_{a<b} 𝒦_ab ) ∘ ( ⊗_a ι̂_a )  (5)
>
> "Notice that as f₄ is linear in the ι̂ we can use unnormalized intertwiners …"
>
> f₄ = (−1)^{χ′} ∫_{Spin(4)⁵} Π_a dG_a ∫_{SU(2)⁵} Π_a dh_a Π_{a<b} 𝒫_ab  (10),  𝒫_ab = ⟨k_ab, −n_ab| π_{k_ab}(h_a⁻¹) C^{k_ab}_{j⁻_ab j⁺_ab} π_{j⁻_ab}(X⁻_ab) π_{j⁺_ab}(X⁺_ab) C^{j⁻_ab j⁺_ab}_{k_ab} π_{k_ab}(h_b) |k_ba, n_ba⟩  (11)
>
> "For γ < 1, the Clebsch–Gordan coefficient C^{j⁻_ab j⁺_ab}_{k_ab} injects into the highest spin subspace k_ab = j⁺_ab + j⁻_ab."
>
> "The asymptotic large spin limit can be investigated by scaling each spin simultaneously, replacing k_ab → λk_ab, then fixing numbers k_ab, and taking the limit λ → ∞ through the natural numbers." (p. 4, §3)

The SU(2) result it is built from, BFH p. 2 and p. 10 (page images):

> 15j(k, n) = (−1)^χ ∫_{SU(2)⁵} Π_{a=1..5} dX_a Π_{1≤a<b≤5} ⟨J n_ab| X_a† X_b |n_ba⟩^{2k_ab}  (1)
>
> 15j(λk, n) ∼ (−1)^χ (2π/λ)⁶ · 2⁴/(4π)⁸ · ( e^{iλS_R(σ)} / √(det H₊) + e^{−iλS_R(σ)} / √(det H₋) ),  "with H_± the Hessian of the action evaluated at b_± respectively."  (16)

and the Euclidean-gravity form, BFH p. 13 (image, "models without complex conjugation"), with ε, ε′ = ±1:

> Z(λj, n) ∼ (−1)^χ (2π/λ)¹² · 2⁸/(4π)¹⁶ · Σ_{ε,ε′=±1} e^{iλ(ε + ε′c_γ)S_R(σ)} / ( c_γ⁶ √(det H_ε det H_ε′) )  (26)

## 2. The Lean statement, verbatim

The 15j form (`Formula.lean`, line 59) and the EPRL form (line 78), with their docstrings:

`Formula.lean`, lines 54–69:

```lean
/-- **The asymptotic formula for the coherent 15j integral** (BFH, eq. (16), with an explicit
error term). For a geometric 4-simplex `σ` and doubled spins `n` that are proportional to the
triangle areas, with even sums at each node and nondegenerate Hessians at the two critical points,
`coh15j (λn) (reggeState σ) - (2π/λ)^6 2^4 (4π)^{-8} (e^{iλS} det(-H₊)^{-1/2} +
e^{-iλS} det(-H₋)^{-1/2}) = O(λ^{-7})` for `λ ∈ ℕ`, `λ → ∞`, with `S = reggeAction σ n`. -/
def Coh15jAsymptoticFormula : Prop :=
  ∀ (σ : Simplex4) (n : Fin 10 → ℕ),
    (∃ c : ℝ, 0 < c ∧ ∀ e, (n e : ℝ) = c * triArea σ e) →
    (∀ a, Even (∑ k, k5Spins n a k)) →
    (-hessAmp n (reggeState σ) (critPlus σ)).det ≠ 0 →
    (-hessAmp n (reggeState σ) critMinus).det ≠ 0 →
    (fun lam : ℕ => coh15j (lam • n) (reggeState σ) -
        (((2 * π / lam) ^ 6 * 2 ^ 4 / (4 * π) ^ 8 : ℝ) : ℂ) *
          (cexp (I * lam * reggeAction σ n) * ampPlus n σ +
            cexp (-(I * lam * reggeAction σ n)) * ampMinus n σ))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ 7)⁻¹
```

`Formula.lean`, lines 71–93:

```lean
/-- **The asymptotic formula for the Euclidean EPRL vertex**, `0 < γ < 1` (BDFGH, Theorem 1, on the
coherent integral form). For a geometric 4-simplex `σ`, EPRL labels `(n, m)` (doubled self-dual and
anti-self-dual spins) of doubled spins `J = n + m` proportional to the triangle areas, even node
sums of `n` and of `m`, and nondegenerate Hessians, with `S = reggeAction σ (n + m)`:
`eprlCoh (λn) (λm) (reggeState σ) = (2π/λ)^12 2^8 (4π)^{-16} (N₊₊ e^{iλS} + N₋₋ e^{-iλS} +
N₊₋ e^{iγλS} + N₋₊ e^{-iγλS}) + O(λ^{-13})`, where `N_{ε₁ε₂}` is the product of the contributions
of the critical points `ε₁` for `n` and `ε₂` for `m`. -/
def EPRLAsymptoticFormula : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 1 → ∀ (σ : Simplex4) (n m : Fin 10 → ℕ),
    IsEPRLVertexLabel γ n m →
    (∃ c : ℝ, 0 < c ∧ ∀ e, ((n e + m e : ℕ) : ℝ) = c * triArea σ e) →
    (∀ a, Even (∑ k, k5Spins n a k)) → (∀ a, Even (∑ k, k5Spins m a k)) →
    (-hessAmp n (reggeState σ) (critPlus σ)).det ≠ 0 →
    (-hessAmp n (reggeState σ) critMinus).det ≠ 0 →
    (-hessAmp m (reggeState σ) (critPlus σ)).det ≠ 0 →
    (-hessAmp m (reggeState σ) critMinus).det ≠ 0 →
    (fun lam : ℕ => eprlCoh (lam • n) (lam • m) (reggeState σ) -
        (((2 * π / lam) ^ 12 * 2 ^ 8 / (4 * π) ^ 16 : ℝ) : ℂ) *
          (cexp (I * lam * reggeAction σ (n + m)) * (ampPlus n σ * ampPlus m σ) +
            cexp (-(I * lam * reggeAction σ (n + m))) * (ampMinus n σ * ampMinus m σ) +
            cexp (I * lam * (γ * reggeAction σ (n + m))) * (ampPlus n σ * ampMinus m σ) +
            cexp (-(I * lam * (γ * reggeAction σ (n + m)))) * (ampMinus n σ * ampPlus m σ)))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ 13)⁻¹
```

Its inputs (`Amplitude.lean`, `ReggeState.lean`, `Formula.lean`):

`Amplitude.lean`, lines 54–63:

```lean
/-- **The propagator** of the edge `e = ab`:
`⟨J g_ab e₀ | X_a† X_b | g_ba e₀⟩ = ((g_ab ε)† X_a† X_b g_ba)₀₀`. -/
noncomputable def prop (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (e : Fin 10) : ℂ :=
  ((g e 0 * epsMat)ᴴ * (X (edgeSrc e))ᴴ * X (edgeTgt e) * g e 1) 0 0

/-- The integrand of the coherent 15j integral, `F_n(X) = Π_e prop(X)_e^{n_e}`, with doubled spins
`n`. -/
noncomputable def cohAmp (n : Fin 10 → ℕ) (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) :
    ℂ :=
  ∏ e, prop g X e ^ n e
```

`Amplitude.lean`, lines 65–68:

```lean
/-- **The coherent 15j integral** `∫_{SU(2)^5} Π_e prop(X)_e^{n_e} dX`, with the Haar probability
measure on each factor (BFH, eq. (1), without the sign `(-1)^χ`). -/
noncomputable def coh15j (n : Fin 10 → ℕ) (g : BdryData) : ℂ :=
  ∫ X : Fin 5 → SU2, cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ)) ∂(haarN (N := 5))
```

`Amplitude.lean`, lines 70–75:

```lean
/-- **The coherent EPRL integral** `∫_{Spin(4)^5} Π_e prop(X⁺)_e^{n_e} prop(X⁻)_e^{m_e} dX`, with
`X = (X⁺, X⁻)` and the Haar probability measure on each factor; `n` and `m` are the doubled
self-dual and anti-self-dual spins. -/
noncomputable def eprlCoh (n m : Fin 10 → ℕ) (g : BdryData) : ℂ :=
  ∫ X : Fin 5 → Spin4, cohAmp n g (fun a => ((X a).1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      cohAmp m g (fun a => ((X a).2 : Matrix (Fin 2) (Fin 2) ℂ)) ∂Measure.pi fun _ => haarSpin4
```

`Amplitude.lean`, lines 82–93:

```lean
/-- **The chart** around `X`: `X_a ↦ X_a exp((i/2) θ_a · σ)` for `a = 0, …, 3`, with
`θ_a = (θ_{3a}, θ_{3a+1}, θ_{3a+2})`, and `X_4` fixed. -/
noncomputable def chart (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) (θ : Fin 12 → ℝ) :
    Fin 5 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun a => if h : (a : ℕ) < 4 then
    X a * NormedSpace.exp (su2Gen fun k => θ (finProdFinEquiv (⟨a, h⟩, k))) else X a

/-- **The Hessian** `H = F(X)⁻¹ ∂²_θ F(chart X θ)|_{θ=0}` of `F = cohAmp n g` in the chart around
`X`, a `12 × 12` complex matrix. At a critical point (`∂_θ F = 0`) it is the Hessian of `log F`. -/
noncomputable def hessAmp (n : Fin 10 → ℕ) (g : BdryData) (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 12) (Fin 12) ℂ :=
  (cohAmp n g X)⁻¹ • Lightlike.Oscillatory.hessMat (fun θ => cohAmp n g (chart X θ)) 0
```

`Formula.lean`, lines 46–52:

```lean
/-- The contribution `det(-H₊)^{-1/2}` of the critical point `U⁺` with doubled spins `n`. -/
noncomputable def ampPlus (n : Fin 10 → ℕ) (σ : Simplex4) : ℂ :=
  invSqrtDet (-hessAmp n (reggeState σ) (critPlus σ))

/-- The contribution `det(-H₋)^{-1/2}` of the critical point `U⁻` with doubled spins `n`. -/
noncomputable def ampMinus (n : Fin 10 → ℕ) (σ : Simplex4) : ℂ :=
  invSqrtDet (-hessAmp n (reggeState σ) critMinus)
```

`ReggeState.lean`, lines 60–61:

```lean
/-- The **area** of the triangle opposite the edge `e`, from the edge lengths by Heron's formula. -/
noncomputable def triArea (σ : Simplex4) (e : Fin 10) : ℝ := area4 (simplexLength σ) (edgeTriSet e)
```

`ReggeState.lean`, lines 63–72:

```lean
/-- The **exterior dihedral angle** `Θ_e = π - θ_e` of `σ` at the triangle opposite the edge
`e = ab`, where `θ_e` is the interior angle between the tetrahedra opposite `a` and opposite `b`,
computed from the edge lengths (`Lightlike.Regge4.dihedral4`). -/
noncomputable def reggeAngle (σ : Simplex4) (e : Fin 10) : ℝ :=
  Real.pi - dihedral4 (simplexLength σ) (edgeTri e 0) (edgeTri e 1) (edgeTri e 2) (edgeTgt e)
    (edgeSrc e)

/-- The **Regge action** `Σ_e (J_e/2) Θ_e` of `σ` with doubled spins `J`. -/
noncomputable def reggeAction (σ : Simplex4) (J : Fin 10 → ℕ) : ℝ :=
  ∑ e, (J e : ℝ) / 2 * reggeAngle σ e
```

`ReggeState.lean`, lines 105–117:

```lean
/-- **The Regge state** of `σ`: for the edge `e = ab`, `g_ab = Q_a† m_e d(Θ_e)` and
`g_ba = Q_b† m_e ε`, with `Q_a = quatMat (outNormal σ a)`, `m_e = liftSU2 (unitBivector σ e)` and
`Θ_e = reggeAngle σ e`. -/
noncomputable def reggeState (σ : Simplex4) : BdryData := fun e =>
  ![(quatMat (outNormal σ (edgeSrc e)))ᴴ * liftSU2 (unitBivector σ e) * phaseMat (reggeAngle σ e),
    (quatMat (outNormal σ (edgeTgt e)))ᴴ * liftSU2 (unitBivector σ e) * epsMat]

/-- The critical point `U⁺_a = Q_4† Q_a` of the Regge state (with `U⁺_4 = 1`). -/
noncomputable def critPlus (σ : Simplex4) : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun a => (quatMat (outNormal σ 4))ᴴ * quatMat (outNormal σ a)

/-- The critical point `U⁻_a = 1` of the Regge state. -/
def critMinus : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ := fun _ => 1
```

and the labels (`Spin4/EPRL.lean`, `Spin4/Vertex.lean`):

`Lightlike/Spin4/EPRL.lean`, lines 57–61:

```lean
/-- The self-dual EPRL spin `j₊ = |1 + γ| j / 2`. -/
noncomputable def jPlus (γ j : ℝ) : ℝ := |1 + γ| * j / 2

/-- The anti-self-dual EPRL spin `j₋ = |1 - γ| j / 2`. -/
noncomputable def jMinus (γ j : ℝ) : ℝ := |1 - γ| * j / 2
```

`Lightlike/Spin4/EPRL.lean`, lines 66–69:

```lean
/-- `(n, m)` are the doubled EPRL labels of the doubled spin `J`: `n = 2 j₊`, `m = 2 j₋` for
`j = J/2`. -/
def IsEPRLLabel (γ : ℝ) (J n m : ℕ) : Prop :=
  (n : ℝ) = 2 * jPlus γ ((J : ℝ) / 2) ∧ (m : ℝ) = 2 * jMinus γ ((J : ℝ) / 2)
```

`Lightlike/Spin4/Vertex.lean`, lines 223–226:

```lean
/-- **EPRL labels on the ten edges**: `(n e, m e)` are the doubled EPRL labels `(2j⁺, 2j⁻)` of the
SU(2) spin `J e = n e + m e` for the Immirzi parameter `γ` (`IsEPRLLabel`). -/
def IsEPRLVertexLabel (γ : ℝ) (n m : Fin 10 → ℕ) : Prop :=
  ∀ e, IsEPRLLabel γ (n e + m e) (n e) (m e)
```

The statement that connects `eprlCoh` to the vertex (`EprlCoherentVertex.lean`, line 52; proved and catalogued as LL-0117, not part of LL-0047):

`EprlCoherentVertex.lean`, lines 49–61:

```lean
/-- **The Euclidean EPRL vertex, contracted with the coherent boundary intertwiners, is the coherent
EPRL integral** (`γ < 1`, the same `SU(2)` elements on both chiral halves). The coefficient of the
coherent intertwiner of node `a` in the basis `ι_z` is `nodeSign * ⟨ι_z, homForm ι⟩`. -/
theorem eprlVertex_coherent (n m : Fin 10 → ℕ) (g : Fin 10 → Fin 2 → SU2) :
    ∑ P ∈ Fintype.piFinset (fun a : Fin 5 =>
        channel (k5Spins n a 0 + k5Spins m a 0) (k5Spins n a 1 + k5Spins m a 1)
          (k5Spins n a 2 + k5Spins m a 2) (k5Spins n a 3 + k5Spins m a 3)),
      (∏ a, (nodeSign (k5Spins n a + k5Spins m a) *
        hsInner (ivec (k5Spins n a 0 + k5Spins m a 0) (k5Spins n a 1 + k5Spins m a 1)
          (k5Spins n a 2 + k5Spins m a 2) (k5Spins n a 3 + k5Spins m a 3) (P a))
          (homForm (k5Spins n a + k5Spins m a)
            (cohInt (k5Spins n a + k5Spins m a) (nodeBdry g a))))) * eprlVertex n m P =
      eprlCoh n m (fun e s => (g e s : Matrix (Fin 2) (Fin 2) ℂ)) := by
```

## 3. Dictionary

| Lean | Meaning | BDFGH / BFH |
|---|---|---|
| `n e`, `m e` (ℕ) | doubled spins `2j⁺_e`, `2j⁻_e` on edge `e = ab` of K₅; `IsEPRLVertexLabel γ n m` says `n = (1+γ)/2·(n+m)`, `m = (1−γ)/2·(n+m)` (for `0<γ<1`, `abs` removed in the proof) | `j^±_ab = (1±γ)j_ab/2`, `k_ab = j⁺_ab + j⁻_ab` (BDFGH p. 9) |
| `n + m` | doubled `k_ab`, i.e. `2k_ab` | `2k_ab` |
| `lam • n` | the spins `λn` | `k_ab → λk_ab`, `λ ∈ ℕ` (p. 4) |
| `σ : Simplex4` | five affinely independent points of ℝ⁴ | "non-degenerate 4-simplex geometry" |
| `triArea σ e` | area (Heron) of the triangle opposite the edge `e = ab`, i.e. the triangle shared by the tetrahedra opposite `a` and `b` | the area of the ab-th triangle; `k_ab` gives the areas |
| `∃ c > 0, n e + m e = c · triArea σ e` | the spins are the areas up to one overall scale | boundary data of a 4-simplex with areas `k_ab` |
| `reggeAngle σ e` | `Θ_e = π − (interior dihedral angle)`, from the edge lengths | `Θ_ab`, angle between the outward normals, `0 < Θ_ab < π` |
| `reggeAction σ J` | `Σ_e (J_e/2) Θ_e` | `Σ_{a<b} k_ab Θ_ab` (with `J = n + m`, `J_e/2 = k_ab`) |
| `reggeState σ` | boundary data `g e s ∈ SU(2)`: `g_ab = Q_a† m_e d(Θ_e)`, `g_ba = Q_b† m_e ε`, `Q_a` the unit quaternion of the outward normal of the tetrahedron opposite `a` | "the associated Regge state ψ_λ" (BDFGH §3, not compared; see difference 7) |
| `prop g X e` | `((g_ab ε)† X_a† X_b g_ba)₀₀ = ⟨J g_ab e₀ ∣ X_a† X_b ∣ g_ba e₀⟩` | the coherent propagator, one chiral half of 𝒫_ab, BFH (1) |
| `coh15j n g` | `∫_{SU(2)⁵} Π_e prop^{n_e}`, Haar probability measure | BFH (1) without `(−1)^χ` |
| `eprlCoh n m g` | `∫_{Spin(4)⁵} Π_e prop(X⁺)^{n_e} prop(X⁻)^{m_e}`; `eprlCoh_eq_mul : eprlCoh n m g = coh15j n g * coh15j m g` | the Spin(4) integral of (5)/(10) for `γ < 1`, the same normal on both halves |
| `chart X θ` | `X_a ↦ X_a exp((i/2) θ_a·σ)` for `a = 0..3`, `X_4` fixed | the gauge fixing "factored out `X⁺₅`" (p. 29) |
| `hessAmp n g X` | `F(X)⁻¹ ∂²_θ F(chart X θ)|₀`, `F = Π prop^{n_e}`; a 12 × 12 complex matrix; at a critical point it is the Hessian of `log F` | `H^{++}` or `H^{−−}` (73) |
| `critPlus σ`, `critMinus` | `U⁺_a = Q₄† Q_a` and `U⁻_a = 1` | the two critical points `X⁺`, `X⁻` of the SU(2) action |
| `ampPlus n σ`, `ampMinus n σ` | `invSqrtDet(−hessAmp n (reggeState σ) X)` at `critPlus σ` resp. `critMinus`; `invSqrtDet M = Π_μ μ^{−1/2}` over the eigenvalues `μ` of `M` (principal roots, with multiplicity) | `det(H)^{−1/2}` |
| `(2π/λ)¹² 2⁸/(4π)¹⁶ · ampε₁ n · ampε₂ m` | the contribution of the pair of critical points `(ε₁, ε₂)` | `(2π/λ)¹² N^γ_{ε₁ε₂}` with `N^γ_{ε₁ε₂} = 2⁸/(4π)¹⁶ det H^{−1/2}`, `det H = det H^{−−} det H^{++}` |
| `f =O[atTop] λ⁻¹³` | `‖f λ‖ ≤ C·λ⁻¹³` for large `λ ∈ ℕ` | BDFGH's definition of "asymptotic" (p. 12): one more power of λ⁻¹ than the leading `λ⁻¹²` |

## 4. Differences from the source

1. **FORM, what the statement is about (most important).** BDFGH's `f₄` is the EPRL vertex, eq. (5)/(10), contracted with the coherent boundary intertwiners. The Lean statement `EPRLAsymptoticFormula` is about `eprlCoh`, the coherent integral over `Spin(4)⁵` written down directly. The identity "vertex contracted with the coherent intertwiners = `eprlCoh`" is a separate theorem, `eprlVertex_coherent` (proved, axioms clean), for `g : Fin 10 → Fin 2 → SU2`; `isSU2Data_reggeState` (Critical.lean:369) says `reggeState σ` is SU(2)-valued. **There is no single declaration that states the asymptotics of `Spin4.eprlVertex` itself**: LL-0047 lists only `eprlAsymptoticFormula` in `decls`, and `eprlVertex_coherent` is not in the entry. Whether Lean's `eprlVertex` contracted with `cohInt` is BDFGH's `f₄` of (5)/(10) — same Clebsch–Gordan injection, same normalisation of the intertwiners, and the sign `(−1)^χ`/`(−1)^{χ′}` — is a comparison of conventions that this card did **not** make (the Lean docstring says only that the sign "is not compared").
2. **COVERAGE, which part of Theorem 1.** Only part 1 (Regge-like data) and only `γ < 1` are stated. Not stated for EPRL: part 2 (vector geometries, eq. (21)), part 3 (suppression, eq. (22)), and `γ > 1` (BDFGH p. 29 give a different constant with the extra product `Π(−1)^{(γ−1)k_ab}((γ+1)k_ab)²`; the catalogue says so). For the 15j there are conditional suppression theorems (`coh15j_exp_decay`: *if* `|F_n| < 1` everywhere on SU(2)⁵ then `‖coh15j(λn)‖ ≤ q^λ`; `coh15j_oneData_decay` for one data set) — not a general statement of part 3, and exponential where BDFGH say `o(λ^{−M})`.
3. **FORM, four constants instead of `2N_{+−} cos`.** BDFGH (20) merges the `(+,−)` and `(−,+)` terms using `det H({U⁺,U⁻}) = det H({U⁻,U⁺})` (p. 29). The Lean statement keeps four terms `e^{±iλS} ampε n·ampε m` and `e^{±iγλS}`, with `ampPlus n · ampMinus m` and `ampMinus n · ampPlus m`. They are equal to BDFGH's cosine form when those two products are complex conjugates of each other and real, which holds here because (PROXY, not machine-checked) the Hessian at a critical point is linear in the spins, `m = (1−γ)/(1+γ)·n`, so the two Hessians differ by a positive factor and have the same argument; the numerics of `regular_eprl_hyps` (below) show `det(−H₊) = 1185.2 − 898.4i`, `det(−H₋) = 1185.2 + 898.4i` for `n = 3` (complex conjugates) and the same argument `−0.6486` for `n = 1`.
4. **CONVENTION, the constants and the Hessian.** BDFGH write `N = 2⁸/(4π)¹⁶ · det H^{−1/2}` with `H` the 24 × 24 Hessian in coordinates `X^i` that "agree with the derivatives", and `a(x₀)` the density of the measure in those coordinates. Lean uses the exponential chart and the Haar *probability* measure and carries the same prefactor `2⁸/(4π)¹⁶`. The factor between the two charts is checked numerically (MEASURED, script check 4: `2⁴(2π²)⁻⁴ det(−H_v)^{−1/2} = 2⁴(4π)⁻⁸ det(−H_θ)^{−1/2}`, ratio 0.99999987). The explicit Hessian (74)–(76) is not proved equal to `hessAmp` in Lean; `hessAmp` is the definition.
5. **CONVENTION, the branch of `det^{−1/2}`.** The source writes `(det H)^{−1/2}` without a branch. Lean's `invSqrtDet` is the product of principal roots `μ^{−1/2}` over the eigenvalues. For matrices of size ≥ 3 this differs from the principal root of `det` when the arguments of the eigenvalues sum past `π` (`Gaussian.lean` proves an example: `(1+2i)·I₃`). The Lean choice is the one for which the Gaussian integral is correctly identified (via a path argument in `Gaussian.lean`). MEASURED (script check 3): at all 120 critical points of 60 random simplices the two agree (largest `|Σ arg| = 1.52 < π`). Not proved for all simplices; the statement does not need it.
6. **FORM, hypotheses made explicit.** (a) The four Hessian conditions `det(−hessAmp …) ≠ 0` are hypotheses; BDFGH take them as established by "the facts used about the Hessian … established in the next section" (p. 30). This card read only (71)–(76), not the rest of §5.6, so it does not say whether BDFGH prove nondegeneracy for every non-degenerate 4-simplex. (b) The even node sums `Even (Σ_k k5Spins n a k)` for `n` and for `m` are explicit; BDFGH's count "each critical solution occurs 2⁸ times" uses them implicitly (script check 2: `F(ε_a U) = F(U)` for all 16 sign patterns exactly when the sums are even).
7. **FORM, the Regge state.** BDFGH's "associated Regge state" is fixed by a choice of spin frame and phases (BDFGH §3, p. 7–8); Lean's `reggeState σ` is an explicit construction from `σ` (the table above). This card did not read the BDFGH definition against the Lean one. What is checked is the property that matters: at `U⁺` and `U⁻`, `|F| = 1` and `F = e^{±iΦ}`, `Φ = Σ (n_e/2)Θ_e` (MEASURED, script check 1), so the phase of the leading term is the Regge action, as in BFH p. 10. Also, BDFGH state the result for any boundary data 𝓑 whose geometry is a non-degenerate 4-simplex; Lean states it for the data `reggeState σ` built from a simplex `σ` in ℝ⁴ (that any boundary data of that kind arises this way up to a rotation is an ASSUMPTION, not checked).
8. **CONVENTION, `λ` and the remainder.** `λ ∈ ℕ`, as in BDFGH ("through the natural numbers"), and `O(λ⁻¹³)` is exactly BDFGH's definition of an asymptotic formula (one power of λ⁻¹ more than the leading `λ⁻¹²`). Not a weakening. The sign `(−1)^{χ′}` of the source is not in the Lean statement, because `eprlCoh` is defined without it (`coh15j` docstring: "without the sign `(−1)^χ`"); it only matters for difference 1.

## 5. Why each hypothesis is needed

- `0 < γ < 1`. For `γ < 1` both chiral halves of the boundary state carry the same normal (`n_ab` on `j⁺` and `j⁻`), which is what `eprlCoh` writes (the same `g` in `prop(X⁺)` and `prop(X⁻)`). For `γ > 1` the anti-self-dual half carries the reflected normal and the constants change. The proof uses `1 + γ > 0` and `1 − γ > 0` to remove the absolute values in `jPlus`, `jMinus`; where `0 < γ` itself is used was not checked.
- `IsEPRLVertexLabel γ n m`. Ties `(n, m)` to the Immirzi parameter: `n = (1+γ)/2·J`, `m = (1−γ)/2·J`. It forces the Regge actions `S_n = (1+γ)S/2`, `S_m = (1−γ)S/2`, so `S_n + S_m = S`, `S_n − S_m = γS`. Without it the phases are not `±S, ±γS`.
- `∃ c > 0, n + m = c·triArea σ`. The critical points are solutions of the gluing equations; for the Regge state the closure `Σ_b area_ab·bloch(g_ab) = 0` holds at every node with spins proportional to the areas (MEASURED, script check 1). That the hypothesis is *necessary* is not checked here (ASSUMPTION); wrong spins are shown to violate it in the kernel (`regular_wrong_spins`), and suppression without gluing is `coh15j_exp_decay` (conditional) and script check 8.
- Even node sums for `n` and `m`. They give `2⁴` identical critical points per chiral half (`2⁸` for EPRL) in the gauge `X₄ = 1`; the script checks the invariance under even sums only (what happens for odd sums is not checked here, ASSUMPTION: the `2⁸` count fails). In the numerics the control "formula without the `2⁴`" fails with `|r − 1| = 14.77`.
- Four nonsingular Hessians. `Lightlike.Oscillatory.stationary_phase` needs nondegenerate critical points; the leading coefficient is `det^{−1/2}`, undefined at a singular `H`.

## 6. Trust checks

- **Axioms** (MEASURED, `lake env lean` on the seed build of `eeba9873b`, `#print axioms`): `eprlAsymptoticFormula`, `coh15jAsymptoticFormula` and `eprlVertex_coherent` each depend on `[propext, Classical.choice, Quot.sound]` only.
- **Non-vacuity in the kernel** (read): `regular_coh15j_hyps` (spins `3` on every edge of the regular simplex are proportional to the areas, even node sums), `regular_eprl_hyps` (`γ = 1/2`, `(n, m) = (3, 1)` are the EPRL labels of `J = 4`; proportional to the areas; even sums), `regular_wrong_spins` (spins `3` on one edge and `1` elsewhere are not proportional to the areas; doubled spins `2` on `01` and `1` elsewhere have the odd sum `5` at node `0`). The Hessian conditions are **not** in the kernel.
- **Numerical evidence** (MEASURED, `python3 scripts/asymptotics/eprl_asymptotics_check.py`, run on 27 Nov 2026 on `eeba9873b`, exit 0, "OK", 70 `PASS`, 16.4 s):
  - Hessian at the regular simplex: `n = 3`: `det(−H₊) = 1185.2 − 898.4i`, `|det| = 1487`, `Re(−H)` positive definite (smallest eigenvalue of the real part 0.448); `n = 1`: `det(−H₊) = 0.00223 − 0.00169i`, `Re(−H)` positive definite (0.149). This is **one** simplex, two spin sizes.
  - 15j formula against the exact integral, `n = 3`, `μ = 1..20`: the leading coefficient of the exact integral relative to the formula, `r`, has `|r − 1| = 0.0379` (window 8..13), `0.0196` (10..15), `0.0148` (15..20); the three controls (no `2⁴`, wrong chart density, state without `d(Θ)`) fail with `|r − 1| = 14.8, 1.0, 32.8`. This is convergence of the leading coefficient to 1.5 %, not a check of the remainder exponent.
  - EPRL formula, `γ = 1/2`, `(n, m) = (3, 1)`: the four-term leading term equals the product of the two 15j leading terms (max deviation `5.1·10⁻¹²`). `λ¹²·eprlCoh / (λ¹²·leading)` at `λ = 1..6` is `0.04, 0.26, 0.35, 0.46, 0.54, 0.71`: rising towards 1, but `λ ≤ 6` is not asymptotic and these values do not fit `1 − c/λ` (PROXY). **The numerical support for the EPRL statement is therefore the 15j convergence plus the proved identity `eprlCoh_eq_mul`, not a direct test.**
  - Gluing, stationarity, the critical set (two gauge classes, 120 solver runs at the regular simplex and 6 × 40 at random simplices, 0 other solutions), and suppression without gluing.
- **Not done by this card:** reading the Lean proofs (stationary-phase assembly in `MaxSetFinite.lean`, `eprlAsymptoticFormula` is a short product argument, `EPRLFormula.lean:84`); BDFGH §3.1–3.3 (Regge state) and §5.1–5.5, §5.6 after (76); BFH §2 phase conventions; the comparison of `Spin4.eprlVertex` with BDFGH eq. (5)/(10) (difference 1); any simplex other than the regular one for the Hessian conditions in the kernel.
- **A catalogue inconsistency found while writing the card, now fixed (MEASURED, `docs/results.yaml`, LL-0047 `note`):** the note said "Equality of the coherent integral with the vertex Spin4.eprlVertex on Livine–Speziale intertwiners is not proven". `eprlVertex_coherent` (`EprlCoherentVertex.lean:52`) proves that the vertex, contracted with the coherent intertwiners `cohInt`, is `eprlCoh` for every spin, `γ < 1`, with clean axioms. The note was stale and now cites LL-0117 (maintainers' go, 27 Nov). The first draft of this card also said `eprlVertex_coherent` should be catalogued; it already is: LL-0117 (`decls` `k5Contract4_eprlCohNode`, `eprlVertex_coherent`; proven, kernel-checked; cited as item 37 of `Lightlike/Asymptotics/EPRL/API-map.md`), so no new entry was added. The claim "asymptotics of the EPRL vertex" is only as strong as the identification in difference 1.

## 7. One question for the reviewer

Is `Lightlike.Spin4.eprlVertex`, contracted with the coherent boundary intertwiners as in `eprlVertex_coherent`, the amplitude `f₄` of BDFGH eq. (5)/(10) for the same boundary data, with the same Clebsch–Gordan injection and intertwiner normalisation — or does it differ by a factor (for instance a constant or the sign `(−1)^{χ′}`)? If it does, LL-0047 is a correct theorem about `eprlCoh` but the entry's title ("the EPRL vertex amplitude") is only true up to that factor.
