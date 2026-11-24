# The quantum group U_q(sl₂)

## Abstract (Alpha)

This API defines the quantum group `U_q(sl₂)` over any field `k` with any unit `q`, by generators and relations, with
its coproduct, counit and antipode, and its two-dimensional representation with the braiding `Ř` of its tensor square.
It proves that `Ř` commutes with the action of every element of `U_q(sl₂)` on the tensor square, satisfies the Hecke
relation and the braid relation. The universal R-matrix, the roots-of-unity quotient and the modular category are
not treated.

## Content (Alpha)

For a field `k` and a unit `q`, `UqSl2 k q` is the `k`-algebra with generators `E, F, K, K⁻¹` and relations
`K K⁻¹ = K⁻¹ K = 1`, `K E = q² E K`, `K F = q⁻² F K` and `(q - q⁻¹)(E F - F E) = K - K⁻¹`, the last written without
division so that every `q` is allowed [1]. A homomorphism out of it is determined by the images of the generators
(`algHom_ext`), and exists when the five relations hold [1]. The coproduct is `ΔE = E ⊗ K + 1 ⊗ E`,
`ΔF = F ⊗ 1 + K⁻¹ ⊗ F`, `ΔK = K ⊗ K`, the counit sends `E, F` to `0` and `K` to `1`, and the antipode is
`S E = -E K⁻¹`, `S F = -K F`, `S K = K⁻¹`; the checks `S` of `K K⁻¹`, of `E F` and the counit of a commutator are in [2] {1}.

On `k²` with basis `v₀, v₁`, `E v₁ = v₀`, `F v₀ = v₁`, `K v₀ = q v₀`, `K v₁ = q⁻¹ v₁`: these matrices satisfy the five
relations, so they define the two-dimensional representation `fundRep` for every unit `q` [3]. On the tensor square
the generators act by the matrices of their coproducts, which again satisfy the relations (`fundTensorRep`). The
braiding `Ř v₀₀ = q v₀₀`, `Ř v₁₁ = q v₁₁`, `Ř v₀₁ = v₁₀`, `Ř v₁₀ = v₀₁ + (q - q⁻¹) v₁₀` commutes with the images of
`E, F, K, K⁻¹`, hence with the image of every element, and satisfies the Hecke relation `(Ř - q)(Ř + q⁻¹) = 0` and the
braid relation `Ř₁₂ Ř₂₃ Ř₁₂ = Ř₂₃ Ř₁₂ Ř₂₃` on `k² ⊗ k² ⊗ k²` [4]. The identification of `fundTensorRep` with the tensor product
through the library's coproduct is not a Lean statement: the matrices were compared with `comul_E`, `comul_F` and
`comul_K` by reading [4]. The braid proof needs a raised heartbeat limit.

## Lean References

1. Lightlike/QuantumGroups/UqSl2.lean - `QuantumGroups.UqSl2`, `QuantumGroups.UqSl2.E`, `QuantumGroups.UqSl2.F`,
   `QuantumGroups.UqSl2.K`, `QuantumGroups.UqSl2.Ki`, `QuantumGroups.UqSl2.K_mul_Ki`, `QuantumGroups.UqSl2.Ki_mul_K`,
   `QuantumGroups.UqSl2.K_mul_E`, `QuantumGroups.UqSl2.K_mul_F`, `QuantumGroups.UqSl2.E_mul_F_sub`,
   `QuantumGroups.UqSl2.comulGen`, `QuantumGroups.UqSl2.comul`, `QuantumGroups.UqSl2.comul_E`,
   `QuantumGroups.UqSl2.comul_F`, `QuantumGroups.UqSl2.comul_K`, `QuantumGroups.UqSl2.comul_Ki`,
   `QuantumGroups.UqSl2.counit`, `QuantumGroups.UqSl2.counit_E`, `QuantumGroups.UqSl2.counit_F`,
   `QuantumGroups.UqSl2.counit_K`, `QuantumGroups.UqSl2.counit_Ki`, `QuantumGroups.UqSl2.antipodeOp`,
   `QuantumGroups.UqSl2.antipodeLin`, `QuantumGroups.UqSl2.antipodeLin_E`, `QuantumGroups.UqSl2.antipodeLin_F`,
   `QuantumGroups.UqSl2.antipodeLin_K`, `QuantumGroups.UqSl2.antipodeLin_Ki`, `QuantumGroups.UqSl2.adjoin_gen`,
   `QuantumGroups.UqSl2.algHom_ext`
2. Lightlike/QuantumGroups/UqSl2Tests.lean - `QuantumGroups.UqSl2.antipode_K_mul`,
   `QuantumGroups.UqSl2.antipode_EF`, `QuantumGroups.UqSl2.counit_commutator`, `QuantumGroups.UqSl2.comul_E_eq`
3. Lightlike/QuantumGroups/UqSl2Rep.lean - `QuantumGroups.UqSl2.fundRep`, `QuantumGroups.UqSl2.fundRep_E`,
   `QuantumGroups.UqSl2.fundRep_F`, `QuantumGroups.UqSl2.fundRep_K`, `QuantumGroups.UqSl2.fundRep_Ki`
4. Lightlike/QuantumGroups/UqSl2Braid.lean - `QuantumGroups.UqSl2.fundBraid`, `QuantumGroups.UqSl2.fundTensorRep`,
   `QuantumGroups.UqSl2.fundBraid_comm_E`, `QuantumGroups.UqSl2.fundBraid_comm_F`, `QuantumGroups.UqSl2.fundBraid_comm_K`,
   `QuantumGroups.UqSl2.fundBraid_comm_Ki`, `QuantumGroups.UqSl2.fundBraid_comm_all`,
   `QuantumGroups.UqSl2.fundBraid_hecke`, `QuantumGroups.UqSl2.braid12`, `QuantumGroups.UqSl2.braid23`,
   `QuantumGroups.UqSl2.fundBraid_braid`

## References

1. V. G. Turaev, *Quantum invariants of knots and 3-manifolds*, de Gruyter Studies in Mathematics 18 (1994), Chapter XI.
