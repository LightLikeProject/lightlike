import Mathlib

/-!
# The colour algebra of `U(N)` and `SU(N)`: completeness (Fierz) and structure constants as traces

Generators in Elvang-Huang's normalisation (p. 21): Hermitian `N × N` matrices `Tᵃ` with
`Tr(Tᵃ Tᵇ) = δᵃᵇ` (`IsGenerators`). For `N²` of them (`U(N)`, i.e. `u(N)`):

* they form an orthonormal basis of `M_N(ℂ)` for the Frobenius inner product (`generatorBasis`), so
  every matrix is `X = Σₐ Tr(Tᵃ X) Tᵃ` (`expand_generators`);
* **the completeness (Fierz) relation** `Σₐ (Tᵃ)ᵢⱼ (Tᵃ)ₖₗ = δᵢₗ δₖⱼ` (`fierz`), and its trace forms
  `Σₐ Tr(X Tᵃ) Tr(Tᵃ Y) = Tr(X Y)` (`fierz_trace_trace`) and `Σₐ Tr(X Tᵃ Y Tᵃ) = Tr X Tr Y`
  (`fierz_trace`);
* **the structure constants are traces of commutators**: with `f̃ᵃᵇᶜ := −i Tr([Tᵃ, Tᵇ] Tᶜ)`,
  `[Tᵃ, Tᵇ] = i Σ_c f̃ᵃᵇᶜ Tᶜ` (`commutator_eq_structureConst`), and conversely any `f` with this
  commutator property satisfies `i fᵃᵇᶜ = Tr(TᵃTᵇTᶜ) − Tr(TᵇTᵃTᶜ)` (Elvang-Huang (2.67),
  `i_mul_eq_trace_sub`); `f̃` is antisymmetric and cyclic (`structureConst_antisymm`,
  `structureConst_cyclic`);
* **products of two structure constants are single traces** (Elvang-Huang (2.69)):
  `Σ_b f̃^{a₁a₂b} f̃^{ba₃a₄} = −(Tr(1234) − Tr(1243) − Tr(1342) + Tr(1432))` (`structureConst_mul_sum`),
  and **the Jacobi identity** `c_s + c_t + c_u = 0` (Elvang-Huang (2.66), `jacobi_colour`).

For `SU(N)` (`N² − 1` traceless generators) the completeness relation has the extra term `−(1/N) δᵢⱼ δₖₗ`
(Elvang-Huang (2.68), `fierz_su`), obtained by adding `1/√N` to the generators.

The trace basis (2.71) is stated (`colourTrace`, `trace_prod_rotate`, `traceBasisAmplitude`); the
diagram-by-diagram colour decomposition of the full Yang-Mills amplitude needs the Yang-Mills Feynman rules
and is not part of this file. Trust check: the `U(2)` generators `σᵃ/√2` (`isGenerators_u2Gen`).

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697, §2.5, p. 21 (the normalisation
  `Tr TᵃTᵇ = δᵃᵇ`, `[Tᵃ, Tᵇ] = i f̃ᵃᵇᶜ Tᶜ`), p. 22 ((2.65)–(2.69)).
-/

open Matrix Complex
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace Lightlike.Colour

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Generators in Elvang-Huang's normalisation (p. 21): Hermitian, `Tr(Tᵃ Tᵇ) = δᵃᵇ`. -/
structure IsGenerators (T : ι → Matrix (Fin N) (Fin N) ℂ) : Prop where
  herm : ∀ a, (T a).IsHermitian
  orth : ∀ a b, (T a * T b).trace = if a = b then 1 else 0

/-- A matrix as a vector of `ℂ^{N×N}` with the Frobenius inner product. -/
def flat (A : Matrix (Fin N) (Fin N) ℂ) : EuclideanSpace ℂ (Fin N × Fin N) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

lemma flat_apply (A : Matrix (Fin N) (Fin N) ℂ) (p : Fin N × Fin N) : flat A p = A p.1 p.2 := rfl

lemma inner_flat (A B : Matrix (Fin N) (Fin N) ℂ) : ⟪flat A, flat B⟫_ℂ = (Aᴴ * B).trace := by
  simp only [PiLp.inner_apply, flat_apply, RCLike.inner_apply, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [mul_comm]

omit [Fintype ι] in
lemma orthonormal_flat {T : ι → Matrix (Fin N) (Fin N) ℂ} (hT : IsGenerators T) :
    Orthonormal ℂ (fun a => flat (T a)) := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [inner_flat, (hT.herm a).eq, hT.orth]

/-- **`N²` generators form an orthonormal basis of `M_N(ℂ)`** (Frobenius inner product). -/
def generatorBasis {T : ι → Matrix (Fin N) (Fin N) ℂ} (hT : IsGenerators T)
    (hcard : Fintype.card ι = N * N) : OrthonormalBasis ι ℂ (EuclideanSpace ℂ (Fin N × Fin N)) :=
  OrthonormalBasis.mk (orthonormal_flat hT)
    (by
      rw [(orthonormal_flat hT).linearIndependent.span_eq_top_of_card_eq_finrank'
        (by rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, hcard])])

lemma generatorBasis_apply {T : ι → Matrix (Fin N) (Fin N) ℂ} (hT : IsGenerators T)
    (hcard : Fintype.card ι = N * N) (a : ι) : generatorBasis hT hcard a = flat (T a) := by
  simp [generatorBasis]

/-- **Every matrix is expanded in the generators**: `X = Σₐ Tr(Tᵃ X) Tᵃ` (the orthonormal basis
expansion of `flat X`). -/
theorem expand_generators {T : ι → Matrix (Fin N) (Fin N) ℂ} (hT : IsGenerators T)
    (hcard : Fintype.card ι = N * N) (X : Matrix (Fin N) (Fin N) ℂ) :
    X = ∑ a, (T a * X).trace • T a := by
  have h := (generatorBasis hT hcard).sum_repr' (flat X)
  simp only [generatorBasis_apply, inner_flat, fun a => (hT.herm a).eq] at h
  ext i j
  have hc := congrArg (fun w : EuclideanSpace ℂ (Fin N × Fin N) => w (i, j)) h
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    flat_apply] at hc
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hc.symm

/-- **The `U(N)` completeness (Fierz) relation** (Elvang-Huang (2.68) without the `SU(N)` term):
`Σₐ (Tᵃ)ᵢⱼ (Tᵃ)ₖₗ = δᵢₗ δₖⱼ`. -/
theorem fierz {T : ι → Matrix (Fin N) (Fin N) ℂ} (hT : IsGenerators T)
    (hcard : Fintype.card ι = N * N) (i j k l : Fin N) :
    ∑ a, T a i j * T a k l = if i = l ∧ k = j then 1 else 0 := by
  have h := (generatorBasis hT hcard).sum_repr' (EuclideanSpace.single (l, k) (1 : ℂ))
  have hc := congrArg (fun w : EuclideanSpace ℂ (Fin N × Fin N) => w (i, j)) h
  simp only [generatorBasis_apply, EuclideanSpace.inner_single_right, one_mul, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, flat_apply,
    PiLp.single_apply] at hc
  have hconj : ∀ a, (starRingEnd ℂ) (T a l k) = T a k l := fun a => by
    have := congrFun (congrFun (hT.herm a).eq k) l
    rw [Matrix.conjTranspose_apply] at this
    exact this
  simp only [hconj] at hc
  rw [show (∑ a, T a i j * T a k l) = ∑ a, T a k l * T a i j from
    Finset.sum_congr rfl fun a _ => mul_comm _ _, hc]
  by_cases h1 : i = l <;> by_cases h2 : j = k
  · subst h1; subst h2; simp
  · simp [h1, h2, Ne.symm h2, Prod.ext_iff]
  · simp [h1, Prod.ext_iff]
  · simp [h1, Prod.ext_iff]

/-- The trace form of completeness: `Σₐ Tr(X Tᵃ) Tr(Tᵃ Y) = Tr(X Y)`. -/
theorem fierz_trace_trace {T : ι → Matrix (Fin N) (Fin N) ℂ} (hT : IsGenerators T)
    (hcard : Fintype.card ι = N * N) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    ∑ a, (X * T a).trace * (T a * Y).trace = (X * Y).trace := by
  conv_rhs => rw [expand_generators hT hcard Y]
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-! ## Structure constants -/

/-- The structure constants as traces: `f̃ᵃᵇᶜ = −i Tr([Tᵃ, Tᵇ] Tᶜ)`. -/
def structureConst (T : ι → Matrix (Fin N) (Fin N) ℂ) (a b c : ι) : ℂ :=
  -I * ((T a * T b - T b * T a) * T c).trace

/-- **`[Tᵃ, Tᵇ] = i Σ_c f̃ᵃᵇᶜ Tᶜ`** for `N²` generators (Elvang-Huang p. 21). -/
theorem commutator_eq_structureConst {T : ι → Matrix (Fin N) (Fin N) ℂ} (hT : IsGenerators T)
    (hcard : Fintype.card ι = N * N) (a b : ι) :
    T a * T b - T b * T a = I • ∑ c, structureConst T a b c • T c := by
  conv_lhs => rw [expand_generators hT hcard (T a * T b - T b * T a)]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_smul, structureConst, Matrix.trace_mul_comm (T c)]
  congr 1
  rw [← mul_assoc, mul_neg, I_mul_I]
  ring

/-- **Elvang-Huang (2.67)**: if `[Tᵃ, Tᵇ] = i Σ_c fᵃᵇᶜ Tᶜ` for orthonormal generators, then
`i fᵃᵇᶜ = Tr(TᵃTᵇTᶜ) − Tr(TᵇTᵃTᶜ)`. -/
theorem i_mul_eq_trace_sub {T : ι → Matrix (Fin N) (Fin N) ℂ} (hT : IsGenerators T)
    (f : ι → ι → ι → ℂ) (hf : ∀ a b, T a * T b - T b * T a = I • ∑ c, f a b c • T c) (a b c : ι) :
    I * f a b c = (T a * T b * T c).trace - (T b * T a * T c).trace := by
  rw [← Matrix.trace_sub, ← Matrix.sub_mul, hf a b, Matrix.smul_mul, Matrix.trace_smul,
    Finset.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, hT.orth, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

omit [Fintype ι] [DecidableEq ι] in
theorem structureConst_antisymm (T : ι → Matrix (Fin N) (Fin N) ℂ) (a b c : ι) :
    structureConst T b a c = -structureConst T a b c := by
  simp only [structureConst, Matrix.sub_mul, Matrix.trace_sub]; ring

omit [Fintype ι] [DecidableEq ι] in
theorem structureConst_cyclic (T : ι → Matrix (Fin N) (Fin N) ℂ) (a b c : ι) :
    structureConst T b c a = structureConst T a b c := by
  simp only [structureConst, Matrix.sub_mul, Matrix.trace_sub]
  rw [Matrix.trace_mul_cycle (T b) (T a) (T c), Matrix.trace_mul_cycle (T c) (T b) (T a),
    Matrix.trace_mul_cycle (T b) (T c) (T a)]

/-- `Tr(Tᵃ Tᵇ Tᶜ Tᵈ)`. -/
def tr4 (T : ι → Matrix (Fin N) (Fin N) ℂ) (a b c d : ι) : ℂ := (T a * T b * T c * T d).trace

/-- **Products of two structure constants are single traces** (Elvang-Huang (2.69)):
`Σ_b f̃^{a₁a₂b} f̃^{ba₃a₄} = −(Tr(T¹T²T³T⁴) − Tr(T¹T²T⁴T³) − Tr(T¹T³T⁴T²) + Tr(T¹T⁴T³T²))`. -/
theorem structureConst_mul_sum {T : ι → Matrix (Fin N) (Fin N) ℂ} (hT : IsGenerators T)
    (hcard : Fintype.card ι = N * N) (a₁ a₂ a₃ a₄ : ι) :
    ∑ b, structureConst T a₁ a₂ b * structureConst T b a₃ a₄ =
      -(tr4 T a₁ a₂ a₃ a₄ - tr4 T a₁ a₂ a₄ a₃ - tr4 T a₁ a₃ a₄ a₂ + tr4 T a₁ a₄ a₃ a₂) := by
  have key : ∀ b, structureConst T a₁ a₂ b * structureConst T b a₃ a₄ =
      -(((T a₁ * T a₂ - T a₂ * T a₁) * T b).trace * (T b * (T a₃ * T a₄ - T a₄ * T a₃)).trace) := by
    intro b
    simp only [structureConst]
    have : ((T b * T a₃ - T a₃ * T b) * T a₄).trace = (T b * (T a₃ * T a₄ - T a₄ * T a₃)).trace := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm (T a₃) (T b * T a₄), Matrix.mul_assoc]
    rw [this]
    have hI : -I * -I = -1 := by rw [neg_mul_neg, I_mul_I]
    linear_combination (((T a₁ * T a₂ - T a₂ * T a₁) * T b).trace *
      (T b * (T a₃ * T a₄ - T a₄ * T a₃)).trace) * hI
  simp only [key, Finset.sum_neg_distrib]
  rw [fierz_trace_trace hT hcard]
  simp only [tr4, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (T a₂) (T a₁ * (T a₃ * T a₄)),
    Matrix.trace_mul_comm (T a₂) (T a₁ * (T a₄ * T a₃))]
  simp only [Matrix.mul_assoc]
  ring

/-- **The Jacobi identity** for the colour factors of the 4-gluon tree (Elvang-Huang (2.66)):
`c_s + c_t + c_u = 0` with `c_s = f̃^{a₁a₂b} f̃^{ba₃a₄}`, `c_t = f̃^{a₁a₃b} f̃^{ba₄a₂}`, `c_u = f̃^{a₁a₄b} f̃^{ba₂a₃}`. -/
theorem jacobi_colour {T : ι → Matrix (Fin N) (Fin N) ℂ} (hT : IsGenerators T)
    (hcard : Fintype.card ι = N * N) (a₁ a₂ a₃ a₄ : ι) :
    ∑ b, structureConst T a₁ a₂ b * structureConst T b a₃ a₄ +
      ∑ b, structureConst T a₁ a₃ b * structureConst T b a₄ a₂ +
        ∑ b, structureConst T a₁ a₄ b * structureConst T b a₂ a₃ = 0 := by
  rw [structureConst_mul_sum hT hcard, structureConst_mul_sum hT hcard,
    structureConst_mul_sum hT hcard]
  ring

/-! ## `SU(N)` -/

/-- **The `SU(N)` completeness relation** (Elvang-Huang (2.68)): for `N² − 1` traceless generators,
`Σₐ (Tᵃ)ᵢⱼ (Tᵃ)ₖₗ = δᵢₗ δₖⱼ − (1/N) δᵢⱼ δₖₗ`. -/
theorem fierz_su {κ : Type*} [Fintype κ] [DecidableEq κ] {T : κ → Matrix (Fin N) (Fin N) ℂ}
    (hT : IsGenerators T) (htr : ∀ a, (T a).trace = 0) (hN : 0 < N)
    (hcard : Fintype.card κ + 1 = N * N) (i j k l : Fin N) :
    ∑ a, T a i j * T a k l =
      (if i = l ∧ k = j then 1 else 0) - (1 / (N : ℂ)) * (if i = j then 1 else 0) *
        (if k = l then 1 else 0) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set c : ℂ := ((Real.sqrt N : ℝ) : ℂ)⁻¹ with hc
  have hsq : c * c = 1 / (N : ℂ) := by
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]; simp
    rw [hc, ← mul_inv, this, one_div]
  set U : Option κ → Matrix (Fin N) (Fin N) ℂ := fun o => o.elim (c • 1) T with hU
  have hcR : (starRingEnd ℂ) c = c := by rw [hc, map_inv₀, Complex.conj_ofReal]
  have hUgen : IsGenerators U := by
    refine ⟨fun o => ?_, fun o o' => ?_⟩
    · cases o with
      | none =>
        simp only [hU, Option.elim]
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
        simp [hcR]
      | some a => exact hT.herm a
    · cases o <;> cases o'
      · simp only [hU, Option.elim, smul_mul_smul_comm, mul_one, Matrix.trace_smul,
          Matrix.trace_one, Fintype.card_fin, smul_eq_mul, ↓reduceIte]
        rw [hsq, one_div, mul_comm, ← div_eq_mul_inv, div_self hN']
      · simp [hU, Option.elim, Matrix.trace_smul, htr]
      · simp [hU, Option.elim, Matrix.trace_smul, htr]
      · simp only [hU, Option.elim, Option.some.injEq]; exact hT.orth _ _
  have hf := fierz hUgen (by rw [Fintype.card_option, hcard]) i j k l
  rw [Fintype.sum_option] at hf
  simp only [hU, Option.elim, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hf
  rw [← hf, ← hsq]
  split_ifs <;> ring

/-! ## The trace basis -/

/-- The single-trace colour factor `Tr(T^{a₁} T^{a₂} ⋯ T^{aₙ})`. -/
def colourTrace {n : ℕ} (T : ι → Matrix (Fin N) (Fin N) ℂ) (a : Fin n → ι) : ℂ :=
  (List.ofFn fun k => T (a k)).prod.trace

omit [Fintype ι] [DecidableEq ι] in
/-- The trace of a product is invariant under cyclic rotation of the factors. -/
theorem trace_prod_rotate (l : List (Matrix (Fin N) (Fin N) ℂ)) (m : ℕ) :
    (l.rotate m).prod.trace = l.prod.trace := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← List.rotate_rotate, ← ih]
    rcases hl : l.rotate m with _ | ⟨x, xs⟩
    · simp
    · rw [List.rotate_cons_succ, List.rotate_zero, List.prod_append, List.prod_cons]
      simp only [List.prod_nil, mul_one, List.prod_cons]
      exact Matrix.trace_mul_comm xs.prod x

/-- **The colour-ordered trace basis** (Elvang-Huang (2.71)): the full tree amplitude of `n` adjoint
particles in terms of the colour-ordered amplitudes `A[1 σ(2) ⋯ σ(n)]`,
`g^{n−2} Σ_σ A[1 σ(2 ⋯ n)] Tr(T^{a₁} T^{a_{σ(2)}} ⋯ T^{a_{σ(n)}})`, the sum over the orderings that fix the
first particle (the trace is cyclic, `trace_prod_rotate`). This states the trace basis; its derivation from the
Yang-Mills Feynman rules is not part of this file. -/
def traceBasisAmplitude {n : ℕ} (T : ι → Matrix (Fin N) (Fin N) ℂ) (g : ℂ)
    (A : Equiv.Perm (Fin (n + 1)) → ℂ) (a : Fin (n + 1) → ι) : ℂ :=
  g ^ (n - 1) * ∑ σ : {σ : Equiv.Perm (Fin (n + 1)) // σ 0 = 0}, A σ.1 * colourTrace T (a ∘ σ.1)

/-! ## Trust check: the `U(2)` generators -/

/-- The Pauli matrices `σ⁰ = 1, σ¹, σ², σ³`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, 1], !![0, 1; 1, 0], !![0, -I; I, 0], !![1, 0; 0, -1]]

/-- The `U(2)` generators `σᵃ/√2` in Elvang-Huang's normalisation. -/
def u2Gen (a : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • pauli a

theorem isGenerators_u2Gen : IsGenerators u2Gen := by
  have hc : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  refine ⟨fun a => ?_, fun a b => ?_⟩
  · rw [Matrix.IsHermitian, u2Gen, Matrix.conjTranspose_smul]
    rw [hc]
    congr 1
    ext i j
    fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.conjTranspose_apply]
  · rw [u2Gen, u2Gen, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
      smul_eq_mul, h2]
    fin_cases a <;> fin_cases b <;> simp [pauli, Matrix.trace_fin_two] <;> ring_nf

/-- The `U(2)` completeness relation, an instance of `fierz`. -/
example (i j k l : Fin 2) :
    ∑ a, u2Gen a i j * u2Gen a k l = if i = l ∧ k = j then 1 else 0 :=
  fierz isGenerators_u2Gen (by simp) i j k l

end Lightlike.Colour
