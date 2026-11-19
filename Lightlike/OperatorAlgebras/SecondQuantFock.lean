import Lightlike.OperatorAlgebras.SecondQuantWedge

/-!
# Second quantization of bounded operators on the bosonic and fermionic Fock spaces

J. Dereziński, *Introduction to representations of the canonical commutation and anticommutation relations*,
arXiv:math-ph/0511030: Section 5.2, p. 19 (`dΓₙ(h) = ∑ⱼ 1 ⊗ ⋯ ⊗ h ⊗ ⋯ ⊗ 1` on `⊗ⁿZ`), Section 5.3, p. 20
(`Θ(σ) z₁ ⊗ ⋯ ⊗ zₙ = z_{σ⁻¹(1)} ⊗ ⋯ ⊗ z_{σ⁻¹(n)}`, `Θₙˢ = (n!)⁻¹ ∑_σ Θ(σ)`, `Θₙᵃ = (n!)⁻¹ ∑_σ sgn σ Θ(σ)` orthogonal
projections, `Γⁿ_{s/a}(Z) = Θⁿ_{s/a} ⊗ⁿZ`), Section 5.7, p. 22 (`a*(w)Ψ = √(n+1) w ⊗_{s/a} Ψ = √(n+1) Θ_{s/a}(w ⊗ Ψ)` on
`Γⁿ_{s/a}(Z)`, `a(w) = a*(w)*`), Theorem 18 (2), (4), p. 22 (`[dΓ(h), a(w)] = -a(h* w)`, `[dΓ(h), a*(w)] = a*(hw)`, in
the bosonic and the fermionic case) and Theorem 13 (1), p. 19 (`[dΓ(h₁), dΓ(h₂)] = dΓ([h₁, h₂])`), for every
`h, h₁, h₂ ∈ B(Z)` and any Hilbert space `Z`.

`⊗ⁿZ` is the coordinate tensor power `ℓ²(Fin n → ι)` of a Hilbert basis `b` of `Z` (`SecondQuantSlot`); all operators
are bounded operators between `ℓ²(Fin n → ι)` and `ℓ²(Fin (n+1) → ι)`, and the commutators are identities between them.

* `Statistics`, `Statistics.chi`, `theta`, `theta_fermion`: `Θ_{s/a} = (n!)⁻¹ ∑_σ χ(σ) P_σ`, the antisymmetrizer for fermions;
* `permL_permL`, `chi_mul`, `chi_mul_self`, `chi_inv`, `theta_comp`, `theta_theta`, `adjoint_permL`, `adjoint_theta`:
  `Θ_{s/a}` is an orthogonal projection;
* `dGammaT`, `dGammaT_permL`, `dGammaT_theta`, `dGammaT_creT`, `adjoint_dGammaT`: `dΓₙ(h) = ∑ⱼ hⱼ` (`0` on `⊗⁰Z`), commuting
  with `Θ_{s/a}`, `dΓ(h)* = dΓ(h*)`;
* `creF`, `annF`, `theta_creF`, `creF_theta`: `a*(w) = √(n+1) Θ (w ⊗ Θ ·)` and `a(w) = a*(w)*`, from `Γⁿ` to `Γⁿ⁺¹`;
* `dGammaT_creF`, `dGammaT_annF`, `dGammaT_comm`: Theorem 18 (4), (2) and Theorem 13 (1);
* `embCLM_creW`, `embCLM_dGammaFock`: on the fermionic side, `Eₙ` carries `FermiFockGeneral`'s `a*(w)` on `ℓ²(Finset ι)`
  and `SecondQuantWedge.dGammaFock` to `creF` and `dGammaT`.
-/

namespace Lightlike.OperatorAlgebras.SecondQuantFock

open SecondQuantWedge

variable {ι : Type*} [LinearOrder ι]

/-- **The statistics** of the particles: bosons (the symmetric Fock space) or fermions (the antisymmetric one). -/
inductive Statistics
  /-- Bosons: the symmetric Fock space. -/
  | boson
  /-- Fermions: the antisymmetric Fock space. -/
  | fermion

/-- The character of the permutation group for the statistics: `1` for bosons, `sgn σ` for fermions. -/
def Statistics.chi (s : Statistics) {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℂ :=
  match s with
  | .boson => 1
  | .fermion => ((Equiv.Perm.sign σ : ℤ) : ℂ)

section Theta

variable {n : ℕ}

/-- `χ(στ) = χ(σ) χ(τ)`. -/
lemma chi_mul (s : Statistics) (σ τ : Equiv.Perm (Fin n)) : s.chi (σ * τ) = s.chi σ * s.chi τ := by
  cases s
  · simp [Statistics.chi]
  · simp [Statistics.chi, Equiv.Perm.sign_mul]

/-- `χ(σ)² = 1`. -/
lemma chi_mul_self (s : Statistics) (σ : Equiv.Perm (Fin n)) : s.chi σ * s.chi σ = 1 := by
  cases s
  · simp [Statistics.chi]
  · exact sign_mul_self σ

/-- `χ(σ⁻¹) = χ(σ)`. -/
lemma chi_inv (s : Statistics) (σ : Equiv.Perm (Fin n)) : s.chi σ⁻¹ = s.chi σ := by
  cases s
  · simp [Statistics.chi]
  · simp [Statistics.chi, Equiv.Perm.sign_inv]

/-- `χ(σ)` is real. -/
lemma conj_chi (s : Statistics) (σ : Equiv.Perm (Fin n)) : (starRingEnd ℂ) (s.chi σ) = s.chi σ := by
  cases s
  · simp [Statistics.chi]
  · simp [Statistics.chi]

variable (n) in
/-- **The (anti)symmetrizer** `Θₙ_{s/a} = (n!)⁻¹ ∑_σ χ(σ) P_σ` on `ℓ²(Fin n → ι)` (Dereziński, Section 5.3, p. 20). -/
noncomputable def theta (s : Statistics) : lp (fun _ : Fin n → ι => ℂ) 2 →L[ℂ] lp (fun _ : Fin n → ι => ℂ) 2 :=
  ((n.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), s.chi σ • permL (ι := ι) σ

/-- The fermionic `Θₙ` is the antisymmetrizer. -/
lemma theta_fermion : theta (ι := ι) n .fermion = antisym n := rfl

/-- `Θ Φ (f) = (n!)⁻¹ ∑_σ χ(σ) Φ(f ∘ σ)`. -/
lemma theta_apply (s : Statistics) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) (f : Fin n → ι) :
    theta n s Φ f = (n.factorial : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), s.chi σ * Φ (f ∘ σ) := by
  simp only [theta, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, permL_apply]
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, permL_apply]

/-- `P_σ P_τ = P_{στ}`. -/
lemma permL_permL (σ τ : Equiv.Perm (Fin n)) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) :
    permL σ (permL τ Φ) = permL (σ * τ) Φ := by
  ext f
  rw [permL_apply, permL_apply, permL_apply]
  rfl

/-- **`Θ Φ` has the symmetry of the statistics**: `Θ Φ (f ∘ τ) = χ(τ) Θ Φ (f)`. -/
lemma theta_comp (s : Statistics) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) (f : Fin n → ι) (τ : Equiv.Perm (Fin n)) :
    theta n s Φ (f ∘ τ) = s.chi τ * theta n s Φ f := by
  have key : ∑ σ : Equiv.Perm (Fin n), s.chi σ * Φ ((f ∘ τ) ∘ σ) =
      s.chi τ * ∑ σ : Equiv.Perm (Fin n), s.chi σ * Φ (f ∘ σ) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft τ⁻¹)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hcomp : (f ∘ ⇑τ) ∘ ⇑(τ⁻¹ * ρ) = f ∘ ⇑ρ := by
      funext x; simp
    simp only [Equiv.coe_mulLeft, chi_mul, chi_inv]
    rw [hcomp]
    ring
  rw [theta_apply, theta_apply, key]
  ring

/-- **`Θ² = Θ`.** -/
theorem theta_theta (s : Statistics) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) :
    theta n s (theta n s Φ) = theta n s Φ := by
  ext f
  rw [theta_apply]
  have hterm : ∀ σ : Equiv.Perm (Fin n), s.chi σ * theta n s Φ (f ∘ σ) = theta n s Φ f := fun σ => by
    rw [theta_comp, ← mul_assoc, chi_mul_self, one_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- `P_σ* = P_{σ⁻¹}`. -/
lemma adjoint_permL (σ : Equiv.Perm (Fin n)) :
    ContinuousLinearMap.adjoint (permL (ι := ι) σ) = permL σ⁻¹ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hU : ∀ z : lp (fun _ : Fin n → ι => ℂ) 2, permL σ (permL σ⁻¹ z) = z := fun z => by
    rw [permL_permL, mul_inv_cancel]
    ext f; rw [permL_apply]; rfl
  have hiso : ∀ u v : lp (fun _ : Fin n → ι => ℂ) 2, inner ℂ (permL σ u) (permL σ v) = inner ℂ u v := fun u v =>
    (SecondQuantSlot.reindexL (permEquiv (ι := ι) σ)).inner_map_map u v
  calc inner ℂ (permL σ⁻¹ x) y = inner ℂ (permL σ (permL σ⁻¹ x)) (permL σ y) := (hiso _ _).symm
    _ = inner ℂ x (permL σ y) := by rw [hU]

/-- **`Θ* = Θ`**: `Θ_{s/a}` is an orthogonal projection. -/
theorem adjoint_theta (s : Statistics) : ContinuousLinearMap.adjoint (theta (ι := ι) n s) = theta n s := by
  have hsum : ∑ σ : Equiv.Perm (Fin n), s.chi σ • permL (ι := ι) σ⁻¹ =
      ∑ σ : Equiv.Perm (Fin n), s.chi σ • permL (ι := ι) σ := by
    rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
    simp only [Equiv.inv_apply, inv_inv, chi_inv]
  rw [theta, map_smulₛₗ, map_sum]
  simp only [map_smulₛₗ, adjoint_permL, conj_chi, map_inv₀, map_natCast]
  rw [hsum]

end Theta

section Gamma

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z] (b : HilbertBasis ι ℂ Z)

/-- **`dΓₙ(h) = ∑ⱼ hⱼ`** on `ℓ²(Fin n → ι)`, `0` on `⊗⁰Z = ℂ` (Dereziński, Section 5.2, p. 19). -/
noncomputable def dGammaT (n : ℕ) (h : Z →L[ℂ] Z) :
    lp (fun _ : Fin n → ι => ℂ) 2 →L[ℂ] lp (fun _ : Fin n → ι => ℂ) 2 :=
  match n with
  | 0 => 0
  | m + 1 => SecondQuantSlot.dGammaTensor b m h

/-- `dΓ₀(h) = 0`. -/
lemma dGammaT_zero (h : Z →L[ℂ] Z) : dGammaT (ι := ι) b 0 h = 0 := rfl

/-- `dΓₘ₊₁(h) = ∑ⱼ hⱼ`. -/
lemma dGammaT_succ (m : ℕ) (h : Z →L[ℂ] Z) : dGammaT b (m + 1) h = SecondQuantSlot.dGammaTensor b m h := rfl

/-- `dΓ(h)` commutes with the slot permutations. -/
lemma dGammaT_permL (n : ℕ) (σ : Equiv.Perm (Fin n)) (h : Z →L[ℂ] Z) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) :
    dGammaT b n h (permL σ Φ) = permL σ (dGammaT b n h Φ) := by
  cases n with
  | zero => rw [dGammaT_zero, ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, map_zero]
  | succ m => exact dGammaTensor_permL b σ h Φ

/-- **`dΓ(h)` commutes with `Θ_{s/a}`**, so it maps `Γⁿ_{s/a}` into itself (Dereziński, Section 5.5, p. 21). -/
theorem dGammaT_theta (s : Statistics) (n : ℕ) (h : Z →L[ℂ] Z) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) :
    dGammaT b n h (theta n s Φ) = theta n s (dGammaT b n h Φ) := by
  simp only [theta, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, map_smul, map_sum,
    dGammaT_permL]

/-- `dΓ(h) (w ⊗ Φ) = (h w) ⊗ Φ + w ⊗ dΓ(h) Φ`. -/
lemma dGammaT_creT (n : ℕ) (h : Z →L[ℂ] Z) (w : Z) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) :
    dGammaT b (n + 1) h (creT b w Φ) = creT b (h w) Φ + creT b w (dGammaT b n h Φ) := by
  cases n with
  | zero =>
    rw [dGammaT_succ, dGammaTensor_zero_creT, dGammaT_zero, ContinuousLinearMap.zero_apply, map_zero, add_zero]
  | succ m => exact dGammaTensor_creT b h w Φ

/-- **`dΓ(h)* = dΓ(h*)`.** -/
lemma adjoint_dGammaT (n : ℕ) (h : Z →L[ℂ] Z) :
    ContinuousLinearMap.adjoint (dGammaT b n h) = dGammaT b n (ContinuousLinearMap.adjoint h) := by
  cases n with
  | zero => rw [dGammaT_zero, dGammaT_zero, map_zero]
  | succ m => exact adjoint_dGammaTensor b m h

/-- **The creation operator** `a*(w) Ψ = √(n+1) Θ (w ⊗ Ψ)` from `Γⁿ_{s/a}` to `Γⁿ⁺¹_{s/a}` (Dereziński, Section 5.7,
p. 22), as `√(n+1) Θₙ₊₁ (w ⊗ Θₙ ·)` on `ℓ²(Fin n → ι)`. -/
noncomputable def creF (s : Statistics) (w : Z) (n : ℕ) :
    lp (fun _ : Fin n → ι => ℂ) 2 →L[ℂ] lp (fun _ : Fin (n + 1) → ι => ℂ) 2 :=
  ((Real.sqrt (n + 1) : ℝ) : ℂ) • (theta (n + 1) s ∘L creT b w ∘L theta n s)

/-- **The annihilation operator** `a(w) = a*(w)*` (Dereziński, Section 5.7, p. 22). -/
noncomputable def annF (s : Statistics) (w : Z) (n : ℕ) :
    lp (fun _ : Fin (n + 1) → ι => ℂ) 2 →L[ℂ] lp (fun _ : Fin n → ι => ℂ) 2 :=
  ContinuousLinearMap.adjoint (creF b s w n)

/-- `a*(w)` takes values in `Γⁿ⁺¹_{s/a}`. -/
lemma theta_creF (s : Statistics) (w : Z) (n : ℕ) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) :
    theta (n + 1) s (creF b s w n Φ) = creF b s w n Φ := by
  simp only [creF, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, theta_theta]

/-- **On `Γⁿ_{s/a}`, `a*(w) Ψ = √(n+1) Θ (w ⊗ Ψ)`.** -/
lemma creF_of_theta (s : Statistics) (w : Z) (n : ℕ) {Ψ : lp (fun _ : Fin n → ι => ℂ) 2} (hΨ : theta n s Ψ = Ψ) :
    creF b s w n Ψ = ((Real.sqrt (n + 1) : ℝ) : ℂ) • theta (n + 1) s (creT b w Ψ) := by
  simp only [creF, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hΨ]

/-- `a(w)` takes values in `Γⁿ_{s/a}`. -/
lemma theta_annF (s : Statistics) (w : Z) (n : ℕ) (Φ : lp (fun _ : Fin (n + 1) → ι => ℂ) 2) :
    theta n s (annF b s w n Φ) = annF b s w n Φ := by
  have h : creF b s w n ∘L theta n s = creF b s w n := by
    ext1 Ψ
    simp only [creF, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, theta_theta]
  have h' := congrArg ContinuousLinearMap.adjoint h
  rw [ContinuousLinearMap.adjoint_comp, adjoint_theta] at h'
  rw [annF]
  exact congrArg (fun T => T Φ) h'

/-- **Theorem 18 (4)**: `[dΓ(h), a*(w)] = a*(hw)`, for bosons and fermions. -/
theorem dGammaT_creF (s : Statistics) (n : ℕ) (h : Z →L[ℂ] Z) (w : Z) :
    dGammaT b (n + 1) h ∘L creF b s w n - creF b s w n ∘L dGammaT b n h = creF b s (h w) n := by
  ext1 Φ
  simp only [creF, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul]
  rw [dGammaT_theta, dGammaT_creT, dGammaT_theta, map_add, smul_add, add_sub_cancel_right]

/-- **Theorem 18 (2)**: `[dΓ(h), a(w)] = -a(h* w)`, for bosons and fermions. -/
theorem dGammaT_annF (s : Statistics) (n : ℕ) (h : Z →L[ℂ] Z) (w : Z) :
    dGammaT b n h ∘L annF b s w n - annF b s w n ∘L dGammaT b (n + 1) h =
      -annF b s (ContinuousLinearMap.adjoint h w) n := by
  have key := congrArg ContinuousLinearMap.adjoint (dGammaT_creF b s n (ContinuousLinearMap.adjoint h) w)
  rw [map_sub, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, adjoint_dGammaT, adjoint_dGammaT,
    ContinuousLinearMap.adjoint_adjoint] at key
  rw [annF, annF, ← key, neg_sub]

/-- **Theorem 13 (1)**: `[dΓ(h), dΓ(h')] = dΓ([h, h'])`. -/
theorem dGammaT_comm (n : ℕ) (h h' : Z →L[ℂ] Z) :
    dGammaT b n h ∘L dGammaT b n h' - dGammaT b n h' ∘L dGammaT b n h = dGammaT b n (h ∘L h' - h' ∘L h) := by
  cases n with
  | zero => simp only [dGammaT_zero, ContinuousLinearMap.zero_comp, sub_zero]
  | succ m =>
    ext1 Φ
    exact dGammaTensor_comm b m h h' Φ

/-- **The fermionic Fock space of `FermiFockGeneral` carries the same `a*(w)`**: `Eₙ₊₁ a*(w) = a*(w) Eₙ`. -/
theorem embCLM_creW (w : Z) (n : ℕ) (ψ : FermiL2 ι) :
    embCLM (n + 1) (creWCoeff b w ψ) = creF b .fermion w n (embCLM n ψ) := by
  have hA : theta n .fermion (embCLM n ψ) = embCLM n ψ := antisym_embL ψ
  rw [creF_of_theta b .fermion w n hA]
  exact embL_creW b w ψ

/-- **… and the same `dΓ(h)`**: `Eₙ₊₁ dΓₙ₊₁(h) = dΓₙ₊₁(h) Eₙ₊₁`. -/
theorem embCLM_dGammaFock (n : ℕ) (h : Z →L[ℂ] Z) (ψ : FermiL2 ι) :
    embCLM (n + 1) (dGammaFock b n h ψ) = dGammaT b (n + 1) h (embCLM (n + 1) ψ) := by
  show embCLM (n + 1) (ContinuousLinearMap.adjoint (embCLM (n + 1))
    (SecondQuantSlot.dGammaTensor b n h (embCLM (n + 1) ψ))) = _
  rw [embCLM_adjoint_apply, ← theta_fermion, ← dGammaT_succ, ← dGammaT_theta]
  congr 1
  exact antisym_embL ψ

end Gamma

end Lightlike.OperatorAlgebras.SecondQuantFock
