import Lightlike.OperatorAlgebras.FockUnique

/-!
# Trust checks for the uniqueness of the Fock representation

* `fockGram` is a legitimate Gram function: `fockGram 0 0 = 1` (the vacuum is a unit vector) and
  `fockGram g f = conj (fockGram f g)` (Hermitian symmetry). A wrong sign in the phase would break the
  second statement.
* Non-vacuity: over the zero Hilbert space `h = 0` there is a Fock representation, on `ℂ` with `W 0 = 1` and
  vacuum `1`, so the statement of uniqueness is about an inhabited type (existence for every `h` is the open
  task `T-OP2-P1`).
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.OperatorAlgebras

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]

/-- The Gram function at `(0, 0)` is `1`. -/
theorem fockGram_zero : fockGram (0 : h) 0 = 1 := by
  simp [fockGram, symp]

/-- The Gram function is Hermitian: `fockGram g f = conj (fockGram f g)`. -/
theorem fockGram_conj (f g : h) : fockGram g f = conj (fockGram f g) := by
  have h3 : (⟪g, f⟫_ℂ).im = -(⟪f, g⟫_ℂ).im := by
    have := inner_conj_symm (𝕜 := ℂ) g f
    rw [← this, Complex.conj_im]
  have h1 : symp h (-g) f = -symp h (-f) g := by
    simp only [symp, inner_neg_left, Complex.neg_im, h3]
  have h2 : ‖-g + f‖ = ‖-f + g‖ := by
    rw [← norm_neg]; congr 1; abel
  unfold fockGram
  rw [h1, h2]
  simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I, Complex.conj_ofReal,
    map_ofNat, Complex.ofReal_neg]
  congr 2
  push_cast
  ring

/-- The trivial Fock representation over the zero Hilbert space `h` (any `h` with all vectors zero). -/
noncomputable def trivialFock (h : Type*) [NormedAddCommGroup h] [InnerProductSpace ℂ h]
    (hz : ∀ f : h, f = 0) : FockRep h ℂ where
  W := fun _ => LinearIsometryEquiv.refl ℂ ℂ
  W_zero := rfl
  weyl := fun f g ψ => by
    simp [hz f, hz g, symp]
  continuous_line := fun f ψ => continuous_const
  Ω := 1
  norm_Ω := by simp
  cyclic := by
    refine eq_top_iff.2 fun x _ => ?_
    have : (1 : ℂ) ∈ Submodule.span ℂ (Set.range fun f : h => (LinearIsometryEquiv.refl ℂ ℂ) (1 : ℂ)) :=
      Submodule.subset_span ⟨0, rfl⟩
    have hx : x = x • (1 : ℂ) := by simp
    rw [hx]
    exact Submodule.le_topologicalClosure _ (Submodule.smul_mem _ _ this)
  vacuum_expectation := fun f => by simp [hz f]

/-- **Non-vacuity of the uniqueness statement**: over the zero Hilbert space the uniqueness applies to the
trivial Fock representation and itself. -/
theorem trivialFock_unitary :
    let R := trivialFock (EuclideanSpace ℂ (Fin 0)) (fun _ => Subsingleton.elim _ _)
    ∃ U : ℂ ≃ₗᵢ[ℂ] ℂ, U R.Ω = R.Ω ∧ ∀ f ψ, U (R.W f ψ) = R.W f (U ψ) :=
  by intro R; exact ⟨fockUnitary R R, fockUnitary_spec R R⟩

end Lightlike.OperatorAlgebras
