import Lightlike.OperatorAlgebras.CARShaleMain

/-!
# Fermionic Shale, necessity: an implementer gives a Hilbert-Schmidt antilinear part

If a unitary `U` implements `R` (`U φ(w) = φ(R w) U`), then `annV u (U x) = U (a(u) x)`, so `Ω' = U Ω₀` is a unit vector
killed by every `annV u`. By irreducibility some word `Ψ = creV(b_{j₁}) ⋯ creV(b_{j_r}) Ω'` has `⟪Ω₀, Ψ⟫ ≠ 0`, and `Ψ` is
killed by `annV (b_j)` for `j ∉ {j₁, …, j_r}`. Pairing `annV (b_j) Ψ = 0` with `a*(x) Ω₀` gives
`⟪a*(α b_j) a*(x) Ω₀, Ψ⟫ = -conj ⟪β b_j, x⟫ ⟪Ω₀, Ψ⟫`, and the two-particle components of `Ψ` bound the left side in the
square sum over `j`, `x = b_i`.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.OperatorAlgebras.CARShale

variable {ι : Type*} [LinearOrder ι] {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ]
  (B : HilbertBasis (Finset ι) ℂ Γ) {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
  (b : HilbertBasis ι ℂ Z) (R : Z →ₗ[ℝ] Z)

/-- `a(u) = (φ(u) + i φ(i u)) / 2`. -/
lemma annW_eq_field (u : Z) :
    annW B b u = (1 / 2 : ℂ) • (fockField B b u + Complex.I • fockField B b (Complex.I • u)) := by
  have h1 : creW B b (Complex.I • u) = Complex.I • creW B b u := creW_smul B b _ _
  have h2 : annW B b (Complex.I • u) = (-Complex.I) • annW B b u := annW_I B b u
  simp only [fockField, h1, h2]
  linear_combination (norm := (match_scalars <;> (ring_nf; try simp only [Complex.I_sq]; try ring)))

/-- An implementer intertwines `annV u` with `a(u)`. -/
lemma annV_comp_implementer (U : Γ ≃ₗᵢ[ℂ] Γ) (hU : ∀ w x, U (fockField B b w x) = fockField B b (R w) (U x))
    (u : Z) (x : Γ) : annV B b R u (U x) = U (annW B b u x) := by
  rw [annW_eq_field B b u]
  simp only [annV, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, map_smul, map_add, hU]

variable (hR : ∀ w w', (⟪R w, R w'⟫_ℂ).re = (⟪w, w'⟫_ℂ).re) (hRs : Function.Surjective R)

include hR hRs in
/-- **A word with nonzero vacuum overlap that is killed by the annihilators outside its support.** -/
lemma exists_word_overlap (U : Γ ≃ₗᵢ[ℂ] Γ)
    (hU : ∀ w x, U (fockField B b w x) = fockField B b (R w) (U x)) :
    ∃ (S : Finset ι) (Ψ : Γ), ⟪B ∅, Ψ⟫_ℂ ≠ 0 ∧ (∀ j, j ∉ S → annR B b R j Ψ = 0) := by
  classical
  have hΩ' : ∀ j, annR B b R j (U (B ∅)) = 0 := fun j => by
    rw [annR_eq_annV, annV_comp_implementer B b R U hU, annW_vac B b, map_zero]
  have hn' : U (B ∅) ≠ 0 := by
    intro h
    have : B ∅ = 0 := U.injective (by rw [h, map_zero])
    have h1 : ‖B ∅‖ = 1 := B.orthonormal.1 ∅
    rw [this, norm_zero] at h1; exact zero_ne_one h1
  obtain ⟨hc, hca, -⟩ := creR_car_ite B b R hR
  have hdense := dense_words B b R hR hRs (U (B ∅)) hn' hΩ'
  have hex : ∃ S : Finset ι, ⟪B ∅, vec (creR B b R) (U (B ∅)) S⟫_ℂ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    let T : Submodule ℂ Γ := (Submodule.span ℂ {B ∅})ᗮ
    have hsub : Submodule.span ℂ (Set.range (vec (creR B b R) (U (B ∅)))) ≤ T := by
      rw [Submodule.span_le]
      rintro _ ⟨S, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact hcon S
    have hcl : IsClosed (T : Set Γ) := Submodule.isClosed_orthogonal _
    have h1 : (Submodule.span ℂ (Set.range (vec (creR B b R) (U (B ∅))))).topologicalClosure ≤ T :=
      Submodule.topologicalClosure_minimal _ hsub hcl
    have h2 : B ∅ ∈ T := h1 (hdense Submodule.mem_top)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at h2
    have h3 : ‖B ∅‖ = 1 := B.orthonormal.1 ∅
    have : ⟪B ∅, B ∅⟫_ℂ = 0 := h2
    rw [inner_self_eq_zero] at this
    rw [this, norm_zero] at h3; exact zero_ne_one h3
  obtain ⟨S, hS⟩ := hex
  refine ⟨S, _, hS, fun j hj => ?_⟩
  rw [ann_vec (annR B b R) hca hΩ' S j, if_neg hj]

/-- **The pairing identity**: if `annV v Ψ = 0` then `⟪a*(α v) a*(x) Ω₀, Ψ⟫ = - conj⟪β v, x⟫ ⟪Ω₀, Ψ⟫`. -/
lemma pairing_identity (v x : Z) (Ψ : Γ) (hΨ : annV B b R v Ψ = 0) :
    ⟪creW B b (alphaPart R v) (creW B b x (B ∅)), Ψ⟫_ℂ = -(conj ⟪betaPart R v, x⟫_ℂ * ⟪B ∅, Ψ⟫_ℂ) := by
  have h0 : ⟪creW B b x (B ∅), annV B b R v Ψ⟫_ℂ = 0 := by rw [hΨ, inner_zero_right]
  have h1 : ⟪creW B b x (B ∅), annV B b R v Ψ⟫_ℂ = ⟪creV B b R v (creW B b x (B ∅)), Ψ⟫_ℂ := by
    have := inner_annV_creV B b R v Ψ (creW B b x (B ∅))
    calc ⟪creW B b x (B ∅), annV B b R v Ψ⟫_ℂ = (starRingEnd ℂ) ⟪annV B b R v Ψ, creW B b x (B ∅)⟫_ℂ :=
          (inner_conj_symm _ _).symm
      _ = (starRingEnd ℂ) ⟪Ψ, creV B b R v (creW B b x (B ∅))⟫_ℂ := by rw [this]
      _ = _ := inner_conj_symm _ _
  have h2 : annW B b (betaPart R v) (creW B b x (B ∅)) = ⟪betaPart R v, x⟫_ℂ • B ∅ := by
    have := congrArg (fun T => T (B ∅)) (annW_creW_anticomm B b (betaPart R v) x)
    simpa [annW_vac B b] using this
  rw [h1, creV_eq, ContinuousLinearMap.add_apply, h2, inner_add_left, inner_smul_left] at h0
  linear_combination h0

include hR hRs in
/-- **A Bessel inequality for `R`**: for an orthonormal family `e`, `∑_{j ∈ J} |⟪R eⱼ, v⟫|² ≤ 2 ‖v‖²`. -/
lemma bessel_R {κ : Type*} (e : κ → Z) (he : Orthonormal ℂ e) (J : Finset κ) (v : Z) :
    ∑ j ∈ J, ‖⟪R (e j), v⟫_ℂ‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  have hre : ∀ w : Z, ∑ j ∈ J, (⟪R (e j), w⟫_ℂ).re ^ 2 ≤ ‖w‖ ^ 2 := fun w => by
    have h1 := he.sum_inner_products_le (x := Sinv R hR hRs w) (s := J)
    rw [norm_Sinv R hR hRs] at h1
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) h1
    rw [re_inner_R_left R hR hRs]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  have hnorm : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 := hre v
  have h2 := hre (Complex.I • v)
  rw [norm_smul, Complex.norm_I, one_mul] at h2
  have e : ∀ j, ‖⟪R (e j), v⟫_ℂ‖ ^ 2 = (⟪R (e j), v⟫_ℂ).re ^ 2 + (⟪R (e j), Complex.I • v⟫_ℂ).re ^ 2 := fun j => by
    rw [hnorm, re_inner_I_right]; ring
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib]
  linarith

include hR hRs in
/-- **A Bessel inequality for `α`**: `∑_{j ∈ J} |⟪α eⱼ, v⟫|² ≤ 2 ‖v‖²` for an orthonormal family `e`. -/
lemma bessel_alpha {κ : Type*} (e : κ → Z) (he : Orthonormal ℂ e) (J : Finset κ) (v : Z) :
    ∑ j ∈ J, ‖⟪alphaPart R (e j), v⟫_ℂ‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  classical
  have he' : Orthonormal ℂ (fun j => Complex.I • e j) := by
    rw [orthonormal_iff_ite] at he ⊢
    intro i j
    rw [inner_smul_left, inner_smul_right, he i j]
    split_ifs <;> simp
  have h1 := bessel_R R hR hRs e he J v
  have h2 := bessel_R R hR hRs (fun j => Complex.I • e j) he' J v
  have hterm : ∀ j, ‖⟪alphaPart R (e j), v⟫_ℂ‖ ^ 2 ≤
      (‖⟪R (e j), v⟫_ℂ‖ ^ 2 + ‖⟪R (Complex.I • e j), v⟫_ℂ‖ ^ 2) / 2 := fun j => by
    have e1 : ⟪alphaPart R (e j), v⟫_ℂ = (1 / 2 : ℂ) * (⟪R (e j), v⟫_ℂ + Complex.I * ⟪R (Complex.I • e j), v⟫_ℂ) := by
      simp only [alphaPart, inner_smul_left, inner_sub_left]
      have c2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
      rw [c2]; simp [inner_smul_left]
    rw [e1, norm_mul]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h12]
    have h3 : ‖⟪R (e j), v⟫_ℂ + Complex.I * ⟪R (Complex.I • e j), v⟫_ℂ‖ ≤
        ‖⟪R (e j), v⟫_ℂ‖ + ‖⟪R (Complex.I • e j), v⟫_ℂ‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul]
    have hX2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith [sq_nonneg (‖⟪R (e j), v⟫_ℂ‖ - ‖⟪R (Complex.I • e j), v⟫_ℂ‖)]
  calc ∑ j ∈ J, ‖⟪alphaPart R (e j), v⟫_ℂ‖ ^ 2 ≤ ∑ j ∈ J, (‖⟪R (e j), v⟫_ℂ‖ ^ 2 + ‖⟪R (Complex.I • e j), v⟫_ℂ‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (∑ j ∈ J, ‖⟪R (e j), v⟫_ℂ‖ ^ 2 + ∑ j ∈ J, ‖⟪R (Complex.I • e j), v⟫_ℂ‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ 2 * ‖v‖ ^ 2 := by linarith

/-- The two-particle vector `a*(b_k) a*(b_i) Ω₀`. -/
lemma cre_cre_vac (i k : ι) :
    fermiCre B k (fermiCre B i (B ∅)) = if k = i then 0 else fermiSign {i} k • B (insert k {i}) := by
  have h1 : fermiCre B i (B ∅) = B {i} := by
    rw [fermiCre_basis, if_neg (by simp)]
    simp [fermiSign]
  rw [h1, fermiCre_basis]
  by_cases hki : k = i
  · simp [hki]
  · simp [hki]

/-- The norm of the two-particle coefficient is symmetric in the pair. -/
lemma norm_inner_cre_cre (i k : ι) (hik : i ≠ k) (ξ : Γ) :
    ‖⟪fermiCre B k (fermiCre B i (B ∅)), ξ⟫_ℂ‖ = ‖⟪B {i, k}, ξ⟫_ℂ‖ := by
  rw [cre_cre_vac, if_neg hik.symm, inner_smul_left, norm_mul, Complex.norm_conj, norm_fermiSign, one_mul]
  have : (insert k {i} : Finset ι) = {i, k} := by ext x; simp; tauto
  rw [this]

/-- **The two-particle coefficients are square summable**: for finite sets `I₀`, `K₀` of modes,
`∑_{i ∈ I₀} ∑_{k ∈ K₀} |⟪a*(b_k) a*(b_i) Ω₀, ξ⟫|² ≤ 2 ‖ξ‖²`. -/
lemma two_particle_bound (ξ : Γ) (I₀ K₀ : Finset ι) :
    ∑ i ∈ I₀, ∑ k ∈ K₀, ‖⟪fermiCre B k (fermiCre B i (B ∅)), ξ⟫_ℂ‖ ^ 2 ≤ 2 * ‖ξ‖ ^ 2 := by
  classical
  set c : Finset ι → ℝ := fun S => ‖⟪B S, ξ⟫_ℂ‖ ^ 2 with hc
  have hbessel : ∀ T : Finset (Finset ι), ∑ S ∈ T, c S ≤ ‖ξ‖ ^ 2 := fun T => by
    have := B.orthonormal.sum_inner_products_le (x := ξ) (s := T)
    simpa [hc] using this
  have hpt : ∀ i k : ι, ‖⟪fermiCre B k (fermiCre B i (B ∅)), ξ⟫_ℂ‖ ^ 2 ≤
      (if i < k then c {i, k} else 0) + (if k < i then c {i, k} else 0) := fun i k => by
    by_cases hik : i = k
    · subst hik
      rw [cre_cre_vac, if_pos rfl]; simp
    · rw [norm_inner_cre_cre B i k hik]
      rcases lt_or_gt_of_ne hik with h | h
      · simp [hc, h, not_lt.2 h.le]
      · simp [hc, h, not_lt.2 h.le]
  have key : ∀ X Y : Finset ι, ∑ x ∈ X, ∑ y ∈ Y, (if x < y then c {x, y} else 0) ≤ ‖ξ‖ ^ 2 := fun X Y => by
    rw [← Finset.sum_product' (f := fun x y => if x < y then c {x, y} else 0), ← Finset.sum_filter]
    have hinj : Set.InjOn (fun p : ι × ι => ({p.1, p.2} : Finset ι)) ↑((X ×ˢ Y).filter (fun p => p.1 < p.2)) := by
      intro p hp q hq hpq
      have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      have h3 : (({p.1, p.2} : Finset ι) : Set ι) = (({q.1, q.2} : Finset ι) : Set ι) := by
        simpa only using congrArg (fun S : Finset ι => (S : Set ι)) hpq
      rw [Finset.coe_pair, Finset.coe_pair, Set.pair_eq_pair_iff] at h3
      rcases h3 with ⟨h4, h5⟩ | ⟨h4, h5⟩
      · exact Prod.ext h4 h5
      · exfalso
        have := lt_trans hp' (h5 ▸ h4 ▸ hq')
        exact lt_irrefl _ (by rw [h4] at hp'; rw [h5] at hp'; exact lt_trans hp' hq')
    calc ∑ p ∈ (X ×ˢ Y).filter (fun p => p.1 < p.2), c {p.1, p.2}
        = ∑ S ∈ ((X ×ˢ Y).filter (fun p => p.1 < p.2)).image (fun p : ι × ι => ({p.1, p.2} : Finset ι)), c S :=
          (Finset.sum_image hinj).symm
      _ ≤ ‖ξ‖ ^ 2 := hbessel _
  have h1 := key I₀ K₀
  have h2 : ∑ i ∈ I₀, ∑ k ∈ K₀, (if k < i then c {i, k} else 0) ≤ ‖ξ‖ ^ 2 := by
    rw [Finset.sum_comm]
    have := key K₀ I₀
    simpa only [Finset.pair_comm] using this
  calc ∑ i ∈ I₀, ∑ k ∈ K₀, ‖⟪fermiCre B k (fermiCre B i (B ∅)), ξ⟫_ℂ‖ ^ 2
      ≤ ∑ i ∈ I₀, ∑ k ∈ K₀, ((if i < k then c {i, k} else 0) + (if k < i then c {i, k} else 0)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hpt i k
    _ = ∑ i ∈ I₀, ∑ k ∈ K₀, (if i < k then c {i, k} else 0) + ∑ i ∈ I₀, ∑ k ∈ K₀, (if k < i then c {i, k} else 0) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ 2 * ‖ξ‖ ^ 2 := by linarith

/-- The one-particle vector `v` with `⟪a*(y) η, Ψ⟫ = ⟪y, v⟫` for all `y`, for a vector `η` of norm `1`. -/
lemma exists_riesz (η Ψ : Γ) (hη : ‖η‖ = 1) :
    ∃ v : Z, ∀ y : Z, ⟪creW B b y η, Ψ⟫_ℂ = ⟪y, v⟫_ℂ := by
  let ℓ : Z →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun y => ⟪Ψ, creW B b y η⟫_ℂ
      map_add' := fun y z => by rw [creW_add, ContinuousLinearMap.add_apply, inner_add_right]
      map_smul' := fun a y => by
        rw [creW_smul, ContinuousLinearMap.smul_apply, inner_smul_right]; rfl } ‖Ψ‖
    (fun y => by
      show ‖⟪Ψ, creW B b y η⟫_ℂ‖ ≤ ‖Ψ‖ * ‖y‖
      calc ‖⟪Ψ, creW B b y η⟫_ℂ‖ ≤ ‖Ψ‖ * ‖creW B b y η‖ := norm_inner_le_norm _ _
        _ ≤ ‖Ψ‖ * (‖y‖ * ‖η‖) := by
            gcongr
            exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (norm_creW_le B b y) (norm_nonneg _))
        _ = ‖Ψ‖ * ‖y‖ := by rw [hη, mul_one])
  refine ⟨(InnerProductSpace.toDual ℂ Z).symm ℓ, fun y => ?_⟩
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (x := y) (y := ℓ)
  rw [← inner_conj_symm (y), h]
  exact (inner_conj_symm _ _).symm

/-- **Parseval** for a Hilbert basis, in the form `∑ |⟪eₖ, v⟫|² = ‖v‖²`. -/
lemma parseval_sq {κ : Type*} (e : HilbertBasis κ ℂ Z) (v : Z) :
    HasSum (fun k => ‖⟪e k, v⟫_ℂ‖ ^ 2) (‖v‖ ^ 2) := by
  have h := e.hasSum_inner_mul_inner v v
  have h2 := (Complex.hasSum_re h)
  have h3 : ∀ k, (⟪v, e k⟫_ℂ * ⟪e k, v⟫_ℂ).re = ‖⟪e k, v⟫_ℂ‖ ^ 2 := fun k => by
    have h4 : ⟪v, e k⟫_ℂ = (starRingEnd ℂ) ⟪e k, v⟫_ℂ := (inner_conj_symm _ _).symm
    rw [h4, Complex.conj_mul']
    simp [sq, Complex.mul_re]
  simp only [h3] at h2
  rw [inner_self_eq_norm_sq_to_K] at h2
  simp only [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h2
  simpa [sq] using h2

include hR hRs in
/-- **The key bound**: if `Ψ` is killed by `annR j` for `j ∉ S₀`, then for `J₀` disjoint from `S₀`,
`|⟪Ω₀, Ψ⟫|² ∑_{j ∈ J₀} ‖β bⱼ‖² ≤ 4 ‖Ψ‖²`. -/
lemma sum_beta_le (Ψ : Γ) (S₀ : Finset ι) (hΨ : ∀ j, j ∉ S₀ → annR B b R j Ψ = 0) (J₀ : Finset ι)
    (hJ₀ : ∀ j ∈ J₀, j ∉ S₀) :
    ‖⟪B ∅, Ψ⟫_ℂ‖ ^ 2 * ∑ j ∈ J₀, ‖betaPart R (b j)‖ ^ 2 ≤ 4 * ‖Ψ‖ ^ 2 := by
  classical
  set c := ⟪B ∅, Ψ⟫_ℂ with hcdef
  have hη : ∀ i, ‖creW B b (b i) (B ∅)‖ = 1 := fun i => by
    rw [norm_creW_vac B b]; exact b.orthonormal.1 i
  choose v hv using fun i => exists_riesz B b (creW B b (b i) (B ∅)) Ψ (hη i)
  have hpair : ∀ j ∈ J₀, ∀ i, ‖⟪alphaPart R (b j), v i⟫_ℂ‖ ^ 2 = ‖c‖ ^ 2 * ‖⟪betaPart R (b j), b i⟫_ℂ‖ ^ 2 := by
    intro j hj i
    have h1 := pairing_identity B b R (b j) (b i) Ψ (by rw [← annR_eq_annV]; exact hΨ j (hJ₀ j hj))
    rw [← hv i, h1, norm_neg, norm_mul, Complex.norm_conj, mul_pow, mul_comm]
  have hvsum : ∀ I₀ : Finset ι, ∑ i ∈ I₀, ‖v i‖ ^ 2 ≤ 2 * ‖Ψ‖ ^ 2 := fun I₀ => by
    have hs : HasSum (fun k => ∑ i ∈ I₀, ‖⟪b k, v i⟫_ℂ‖ ^ 2) (∑ i ∈ I₀, ‖v i‖ ^ 2) :=
      hasSum_sum fun i _ => parseval_sq b (v i)
    refine hasSum_le_of_sum_le hs (fun K₀ => ?_)
    rw [Finset.sum_comm]
    have := two_particle_bound B Ψ I₀ K₀
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_)) this
    rw [← hv i (b k), creW_basis B b, creW_basis B b]
  have hpart : ∀ I₀ : Finset ι, ‖c‖ ^ 2 * ∑ i ∈ I₀, ∑ j ∈ J₀, ‖⟪b i, betaPart R (b j)⟫_ℂ‖ ^ 2 ≤ 4 * ‖Ψ‖ ^ 2 := by
    intro I₀
    have e : ‖c‖ ^ 2 * ∑ i ∈ I₀, ∑ j ∈ J₀, ‖⟪b i, betaPart R (b j)⟫_ℂ‖ ^ 2 =
        ∑ i ∈ I₀, ∑ j ∈ J₀, ‖⟪alphaPart R (b j), v i⟫_ℂ‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hpair j hj i, ← norm_inner_symm (b i)]
    rw [e]
    calc ∑ i ∈ I₀, ∑ j ∈ J₀, ‖⟪alphaPart R (b j), v i⟫_ℂ‖ ^ 2 ≤ ∑ i ∈ I₀, 2 * ‖v i‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => bessel_alpha R hR hRs b b.orthonormal J₀ (v i)
      _ = 2 * ∑ i ∈ I₀, ‖v i‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * ‖Ψ‖ ^ 2 := by linarith [hvsum I₀]
  have hs : HasSum (fun i => ∑ j ∈ J₀, ‖⟪b i, betaPart R (b j)⟫_ℂ‖ ^ 2) (∑ j ∈ J₀, ‖betaPart R (b j)‖ ^ 2) :=
    hasSum_sum fun j _ => parseval_sq b (betaPart R (b j))
  have hs' := hs.mul_left (‖c‖ ^ 2)
  refine hasSum_le_of_sum_le hs' (fun I₀ => ?_)
  rw [← Finset.mul_sum]
  exact hpart I₀

include hR hRs in
/-- **Fermionic Shale, necessity**: if a unitary of the Fock space implements `R`, the square sum `∑ ‖β bⱼ‖²` over the
Fock basis converges, i.e. the antilinear part is Hilbert-Schmidt. -/
theorem summable_beta_of_implementer (U : Γ ≃ₗᵢ[ℂ] Γ)
    (hU : ∀ w x, U (fockField B b w x) = fockField B b (R w) (U x)) :
    Summable fun j : ι => ‖betaPart R (b j)‖ ^ 2 := by
  classical
  obtain ⟨S, Ψ, hc, hkill⟩ := exists_word_overlap B b R hR hRs U hU
  have hcpos : 0 < ‖⟪B ∅, Ψ⟫_ℂ‖ ^ 2 := by positivity
  refine summable_of_sum_le (c := 4 * ‖Ψ‖ ^ 2 / ‖⟪B ∅, Ψ⟫_ℂ‖ ^ 2 + S.card) (fun j => by positivity) (fun J₀ => ?_)
  have h1 := sum_beta_le B b R hR hRs Ψ S hkill (J₀.filter (fun j => j ∉ S)) (fun j hj => (Finset.mem_filter.1 hj).2)
  have h2 : ∑ j ∈ J₀.filter (fun j => j ∉ S), ‖betaPart R (b j)‖ ^ 2 ≤ 4 * ‖Ψ‖ ^ 2 / ‖⟪B ∅, Ψ⟫_ℂ‖ ^ 2 := by
    rw [le_div_iff₀ hcpos]; linarith
  have h3 : ∑ j ∈ J₀.filter (fun j => j ∈ S), ‖betaPart R (b j)‖ ^ 2 ≤ S.card := by
    calc ∑ j ∈ J₀.filter (fun j => j ∈ S), ‖betaPart R (b j)‖ ^ 2 ≤ ∑ j ∈ J₀.filter (fun j => j ∈ S), (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => by
            have := norm_betaPart_le R hR (b j)
            rw [b.orthonormal.1 j] at this
            nlinarith [norm_nonneg (betaPart R (b j))]
      _ = (J₀.filter (fun j => j ∈ S)).card := by simp
      _ ≤ S.card := by
          exact_mod_cast Finset.card_le_card (fun j hj => (Finset.mem_filter.1 hj).2)
  rw [← Finset.sum_filter_add_sum_filter_not J₀ (fun j => j ∈ S)]
  linarith

/-- A Hilbert basis indexed by an arbitrary type, re-indexed by its range (a set of vectors). -/
noncomputable def setBasis (b : HilbertBasis ι ℂ Z) : HilbertBasis (Set.range b) ℂ Z :=
  HilbertBasis.mk (v := fun p : Set.range b => (p : Z))
    (by
      have hinj : Function.Injective b := fun i j h => by
        by_contra hne
        have h1 := orthonormal_iff_ite.1 b.orthonormal i j
        rw [if_neg hne, h] at h1
        have h2 := orthonormal_iff_ite.1 b.orthonormal j j
        rw [if_pos rfl, h1] at h2
        exact zero_ne_one h2
      let e := Equiv.ofInjective b hinj
      have := b.orthonormal.comp e.symm e.symm.injective
      convert this using 1
      funext p
      exact (Equiv.apply_ofInjective_symm hinj p).symm)
    (by
      have : Set.range (fun p : Set.range b => (p : Z)) = Set.range b := by
        ext x; simp
      rw [this]
      exact b.dense_span.ge)

/-- Auxiliary lemma `setBasis_apply` for the necessity in the fermionic Shale theorem. -/
lemma setBasis_apply (b : HilbertBasis ι ℂ Z) (p : Set.range b) : setBasis b p = (p : Z) := by
  simp [setBasis, HilbertBasis.coe_mk]

include hR hRs in
/-- **Fermionic Shale's theorem** (Shale 1962, for the CAR): in the fermionic Fock space `Γ_a(Z)`, a surjective real-linear
`R` preserving `Re⟪·,·⟫` is implemented by a unitary, `U φ(w) = φ(R w) U`, if and only if its antilinear part is
Hilbert-Schmidt, `∑ ‖β bⱼ‖² < ∞` in the Fock basis. -/
theorem fermionic_shale_iff :
    (∃ U : Γ ≃ₗᵢ[ℂ] Γ, ∀ w x, U (fockField B b w x) = fockField B b (R w) (U x)) ↔
      Summable fun j : ι => ‖betaPart R (b j)‖ ^ 2 := by
  constructor
  · rintro ⟨U, hU⟩
    exact summable_beta_of_implementer B b R hR hRs U hU
  · intro hsum
    refine fermionic_shale_of_HS B b R hR hRs ⟨Set.range b, setBasis b, ?_⟩
    have hinj : Function.Injective b := fun i j h => by
      by_contra hne
      have h1 := orthonormal_iff_ite.1 b.orthonormal i j
      rw [if_neg hne, h] at h1
      have h2 := orthonormal_iff_ite.1 b.orthonormal j j
      rw [if_pos rfl, h1] at h2
      exact zero_ne_one h2
    simp only [setBasis_apply]
    exact (Equiv.summable_iff (Equiv.ofInjective b hinj) (f := fun p : Set.range b => ‖betaPart R (p : Z)‖ ^ 2)).1
      (show Summable ((fun p : Set.range b => ‖betaPart R (p : Z)‖ ^ 2) ∘ Equiv.ofInjective b hinj) from hsum)

end Lightlike.OperatorAlgebras.CARShale
