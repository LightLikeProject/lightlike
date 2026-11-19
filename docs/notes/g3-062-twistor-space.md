# G3-062: twistor space, the form of signature (2, 2), PT, PN, PT±, and the incidence relation ω = i x π

Lean: `Lightlike/GR/TwistorSpace.lean` (on `TwistorConformal.lean`, G3-064, and `ComplexMinkowski.lean`, G3-061).

## Sources read (pdftotext of the arXiv PDFs)

* M. Atiyah, M. Dunajski, L. Mason, *Twistor theory at fifty*, arXiv:1704.07464, §2.1, p. 7: "The projective twistor space PT is defined
  to be CP³ − CP¹ ... (Z², Z³) ≠ (0, 0)"; the incidence relation (2.7), `(Z⁰, Z¹) = (i/√2) [[ct + z, x + iy], [x − iy, ct − z]] (Z², Z³)`;
  `Σ(Z, Z) = Z⁰Z̄² + Z¹Z̄³ + Z²Z̄⁰ + Z³Z̄¹`, "a (+ + − −) Hermitian inner product"; "The twistor space T is divided into three parts
  depending on whether Σ is positive, negative or zero. This partition descends to the projective twistor space"; `PN = {[Z] ∈ PT,
  Σ(Z, Z) = 0}`; "If the coordinates x^μ are real this line lies in the hypersurface PN".
* T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196: `CP³` and its charts (1.21), `PT` an open subset of `CP³` (1.22), p. 9; the
  Lorentzian incidence relation with the factor `i`, (2.2), p. 13; the inner product (2.5), "signature (+2, −2)", and `PN` (2.7), p. 14.
* A. Bette, arXiv:hep-th/0402150, (3.13)–(3.15), p. 15: `ρ = ω^A η̄_A + λ̄^{A'} π_{A'}`; "CP(3) is divided into three parts. The first part
  of CP(3) corresponds to twistors of positive norm, the second part to twistors of negative norm and the third to twistors with zero norm".

## How each Lean statement matches

* `penroseHerm`, `penroseNorm`, `penroseNorm_sumElim`: ADM's `Σ` in the coordinates `Z = (ω, π) = ((Z⁰, Z¹), (Z², Z³))` (MATCH).
* `penroseHerm_signature`: signature `(2, 2)`, as a unitary congruence to `diag(1, 1, −1, −1)` (ADM "(+ + − −)", Adamo "(+2, −2)").
  `twistorHerm_signature`: the same for the form of `TwistorConformal.lean` (`twistorHerm_eq`: the two are congruent by `toPenrose`).
* `incidencePenrose`: the row's `ω^A = i x^{AA'} π_{A'}`. `incidencePenrose_eq`: it is `μ = Xᵀ λ` (`twistorInc`, Adamo (1.23)) followed by
  `(μ, λ) ↦ (i μ, λ)` (`toPenrose`), `x = Xᵀ`; `penroseNorm_toPenrose`: the forms agree. `incidencePenrose_spinorMat`, `spinorMat_transpose`:
  ADM's (2.7) is `incidencePenrose (spinorMat x)ᵀ`, i.e. ADM's matrix is the transpose of Adamo's (1.12).
* `penroseNorm_incidence_eq_zero_iff`: the line of `x` is null iff `x` is Hermitian (ADM p. 7 and Adamo (2.7) state "⇐"; "⇒" added).
* `CP3`, `penroseSign_rep_mk` (the sign of `Σ` is projectively invariant, `penroseNorm_smul`, `penroseNorm_im`), `PTplus`, `PN`, `PTminus`,
  `mem_PTplus_mk`, `mem_PN_mk`, `mem_PTminus_mk`, `cp3_partition` (ADM, Bette p. 15); `PTplus_nonempty`, `PN_nonempty`, `PTminus_nonempty`.
* `PT`, `mem_PT_mk`: ADM's `PT = CP³ − CP¹`, `π ≠ 0`. `mk_incidencePenrose_mem`: lines of real points lie in `PN ∩ PT` (ADM p. 7).

## Differences

1. Representation: twistors are `Fin 2 ⊕ Fin 2 → ℂ`; `CP3 = ℙ ℂ (Fin 2 ⊕ Fin 2 → ℂ)` is Mathlib's projectivization (no topology yet; G3-063).
2. Convention: ADM's matrix `x^{AA'}` is `(spinorMat x)ᵀ` (ADM (2.7) p. 7 against Adamo (1.12) p. 7); the incidence relation of
   `TwistorConformal.lean` is Adamo's (1.23) without the factor `i` of (2.2), p. 13, moved into `toPenrose`.
3. `PT±` and `PN` are defined on all of `CP³`; ADM defines `PN` inside `PT`; `PN ∩ PT` is ADM's `PN`.
