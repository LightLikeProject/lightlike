# OP3: source check of the finite-dimensional modular theory and the KMS condition

Source read: E. Witten, *Notes on some entanglement properties of quantum field theory*, arXiv:1803.04993 (Rev. Mod. Phys.
90 (2018) 045003), Section 4.1 "The Modular Operators In The Finite-Dimensional Case" (printed pages 32-36) and Section 4.2
"The Modular Automorphism Group" (pages 36-39). Each item was read at its location in the arXiv text.

| Statement in `Lightlike/OperatorAlgebras/ModularFinite.lean` | Location | Match |
|---|---|---|
| `tomita H y = ρ^{-1/2} y† ρ^{1/2}` with `ρ = e^{-H}`, antilinear, `S (a ρ^{1/2}) = a† ρ^{1/2}` (`tomita_apply`), `S² = 1` (`tomita_tomita`) | (4.4): `S_Ψ((a ⊗ 1)Ψ) = (a† ⊗ 1)Ψ`, with `Ψ = Σ c_k |k,k⟩`, `ρ_1 = Tr_2 |Ψ⟩⟨Ψ|`; identification of `H_1 ⊗ H_2` with matrices by `|j,i⟩ ↔ E_{ji}` | The vector `Ψ` is `ρ^{1/2}` in the Hilbert–Schmidt space; same definition. |
| `modOp H y = ρ y ρ⁻¹` and `⟪S y, S z⟫ = ⟪z, Δ y⟫` (`inner_tomita`, the antilinear form of `Δ = S† S`) | (4.9)-(4.11): `Δ_Ψ |j,i⟩ = (|c_j|²/|c_i|²) |j,i⟩`, i.e. `ρ_1 ⊗ ρ_2^{-1}` | On `E_{ji}` the map `y ↦ ρ y ρ⁻¹` has eigenvalue `p_j/p_i`, the same. |
| `flow H z a = e^{-izH} a e^{izH}` (the modular flow `Δ^{iz} a Δ^{-iz}`) | (4.35) and the text after (4.46) | Same, with `ρ_1 = e^{-H}`. |
| `kms`: `Tr (e^{-H} b σ_{s-i}(a)) = Tr (e^{-H} σ_s(a) b)`, for every complex `s` | (4.46) `F(z) = Tr_{H_1} e^{-H} b e^{-izH} a e^{izH}` and (4.47) `F(s) = Tr e^{-H} b σ_s(a)`, `F(-i+s) = Tr e^{-H} σ_s(a) b` | Same two boundary values; the source states them for real `s` and notes `F` is entire for a finite-dimensional system. |
| `isKMS_gibbs`: `e^{-βH}` is `(H, β)`-KMS; `not_isKMS_of_ne`: a diagonal qubit state with `p ≠ q e^{βE}` is not | the thermal reading after (4.47): "thermal ensemble with Hamiltonian H (and inverse temperature 1)" | The scaling `H ↦ βH` is this library's; the source states inverse temperature 1 only. |

Not checked: the convention of Bratteli–Robinson, volume 2 (the KMS-states chapter): the book was not read. The statement is
in the convention of Witten's equations (4.46) and (4.47); the comparison with Bratteli–Robinson is pending.
