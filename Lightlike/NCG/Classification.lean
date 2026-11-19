import Lightlike.NCG.TensorForm

/-!
# The multiplicity matrix of a real finite spectral triple

T. Krajewski, arXiv:hep-th/9701081, Section 3.2, pp. 12-13 (read): for a real structure `J`, `K(Hᵢⱼ) = Hⱼᵢ`, so "the
dimensions of `Hᵢⱼ` and `Hⱼᵢ` are equal, or equivalently, the matrix of multiplicities `m` is symmetric:
`mᵢⱼ = mⱼᵢ`". For `A = ⊕ Mₙᵢ(ℂ)` acting complex-linearly, `Hᵢⱼ ≅ ℂⁿⁱ ⊗ ℂʳⁱʲ ⊗ ℂⁿʲ` (Paschke-Sitarz, Lemma 2), and
`dim Hᵢⱼ = dim Hⱼᵢ` (Lemma 4) gives `rᵢⱼ = rⱼᵢ`.

* `multiplicity R i j = dim Vᵢⱼ`;
* `multiplicity_symm`: the multiplicity matrix is symmetric.
-/

namespace Lightlike.NCG

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} [∀ i, NeZero (n i)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {T : FiniteSpectralTriple (MatSum n) H} (R : RealStructure T)

/-- **The multiplicity** `rᵢⱼ = dim Vᵢⱼ` of the vertex `Hᵢⱼ ≅ ℂⁿⁱ ⊗ ℂʳⁱʲ ⊗ ℂⁿʲ`. -/
noncomputable def multiplicity (i j : ι) : ℕ := Module.finrank ℂ (Vsub R i j)

/-- **The multiplicity matrix is symmetric** (Krajewski, Section 3.2, p. 12): `rᵢⱼ = rⱼᵢ`. -/
theorem multiplicity_symm (i j : ι) : multiplicity R i j = multiplicity R j i := by
  have h := finrank_Hsub_symm R (stdPartition n) i j
  rw [finrank_Hsub_eq, finrank_Hsub_eq, mul_comm (n j) (n i)] at h
  have hpos : 0 < n i * n j := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (Nat.pos_of_ne_zero (NeZero.ne _))
  exact Nat.eq_of_mul_eq_mul_left hpos h

end Lightlike.NCG
