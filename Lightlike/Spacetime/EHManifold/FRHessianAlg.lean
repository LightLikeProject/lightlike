import Lightlike.Spacetime.EHManifold.WSplit

/-!
# Index algebra for the Hessian form of the `f(R)` field equations

Identities between finite sums over indices, for arrays `G` (inverse metric), `H` (perturbation), `C`
(Christoffel symbols) and `p` (a gradient). They are the algebraic part of the identification of the second
integration by parts of the `f(R)` variation with `-√|g| h_{ab} (∇^a ∇^b φ - g^{ab} □φ)`.

Supporting lemmas; no catalogue entry.
-/

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- Swapping two blocks of two summation indices. -/
lemma sum22_swap (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d
      = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- Moving the first of three summation indices to the last place. -/
lemma sum3_first_last (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- Moving the first of five summation indices to the last place. -/
lemma sum5_first_last (f : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ r, ∑ a, ∑ b, ∑ c, ∑ d, f r a b c d = ∑ a, ∑ b, ∑ c, ∑ d, ∑ r, f r a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact Finset.sum_comm

/-- **The values part of the Palatini vector against a gradient**, contracted:
`W₀^ρ p_ρ = -h_{ab} P^a T^b + h_{ab} g^{κa} Γ^b_{κσ} P^σ`, with `P^a = g^{ρa} p_ρ` and
`T^b = g^{σν} Γ^b_{σν}`. -/
lemma W0_contract (G H : Fin n → Fin n → ℝ) (C : Fin n → Fin n → Fin n → ℝ) (p : Fin n → ℝ) :
    ∑ ρ, ((∑ σ, ∑ ν, G σ ν * (-∑ a, ∑ b, G ρ a * H a b * C b σ ν)) -
        ∑ σ, G ρ σ * ∑ κ, (-∑ a, ∑ b, G κ a * H a b * C b κ σ)) * p ρ =
      -(∑ a, ∑ b, H a b * (∑ ρ, G ρ a * p ρ) * (∑ σ, ∑ ν, G σ ν * C b σ ν)) +
        ∑ a, ∑ b, H a b * ∑ κ, ∑ σ, G κ a * C b κ σ * (∑ ρ, G ρ σ * p ρ) := by
  have h1 : ∀ ρ, ∑ σ, ∑ ν, G σ ν * (-∑ a, ∑ b, G ρ a * H a b * C b σ ν) =
      -∑ a, ∑ b, G ρ a * H a b * (∑ σ, ∑ ν, G σ ν * C b σ ν) := by
    intro ρ
    simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
    congr 1
    rw [sum22_swap]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => by ring
  have h2 : ∀ ρ, ∑ σ, G ρ σ * ∑ κ, (-∑ a, ∑ b, G κ a * H a b * C b κ σ) =
      -∑ a, ∑ b, H a b * ∑ κ, ∑ σ, G κ a * C b κ σ * G ρ σ := by
    intro ρ
    simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
    congr 1
    rw [sum22_swap]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun σ _ => by ring
  have h3 : ∑ ρ, (-∑ a, ∑ b, G ρ a * H a b * (∑ σ, ∑ ν, G σ ν * C b σ ν)) * p ρ =
      -(∑ a, ∑ b, H a b * (∑ ρ, G ρ a * p ρ) * (∑ σ, ∑ ν, G σ ν * C b σ ν)) := by
    simp only [neg_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_neg_distrib]
    congr 1
    rw [sum3_first_last]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [sum3_first_last]
      exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ =>
        Finset.sum_congr rfl fun ρ _ => by ring
  have h4 : ∑ ρ, (-∑ a, ∑ b, H a b * ∑ κ, ∑ σ, G κ a * C b κ σ * G ρ σ) * p ρ =
      -(∑ a, ∑ b, H a b * ∑ κ, ∑ σ, G κ a * C b κ σ * (∑ ρ, G ρ σ * p ρ)) := by
    simp only [neg_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_neg_distrib]
    congr 1
    rw [sum5_first_last]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun σ _ =>
        Finset.sum_congr rfl fun ρ _ => by ring
  simp only [h1, h2, sub_mul, Finset.sum_sub_distrib]
  rw [h3, h4]
  ring

/-- Moving the first of four summation indices to the last place. -/
lemma sum4_first_last (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact Finset.sum_comm

/-- Moving the last of four summation indices to the second place. -/
lemma sum4_last_second (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ d, ∑ c, f a b c d :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c, f a b c d := Finset.sum_comm

/-- **The second-derivative part**: contracting `(g^{ρα} g^{μβ} - g^{ρμ} g^{αβ}) q_{μρ}` with `h_{αβ}` gives
`h_{ab} g^{aα} g^{bβ} q_{αβ} - (g^{αβ} q_{αβ}) (g^{αβ} h_{αβ})`. -/
lemma hess_q_contract (G H q : Fin n → Fin n → ℝ) (hG : ∀ a b, G a b = G b a)
    (hq : ∀ a b, q a b = q b a) :
    ∑ μ, ∑ α, ∑ β, (∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * q μ ρ) * H α β =
      (∑ a, ∑ b, H a b * ∑ α, ∑ β, G a α * G b β * q α β) -
        (∑ α, ∑ β, G α β * q α β) * ∑ α, ∑ β, G α β * H α β := by
  have h1 : ∑ μ, ∑ α, ∑ β, (∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * q μ ρ) * H α β =
      (∑ μ, ∑ α, ∑ β, ∑ ρ, G ρ α * G μ β * q μ ρ * H α β) -
        ∑ μ, ∑ α, ∑ β, ∑ ρ, G ρ μ * G α β * q μ ρ * H α β := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  have h2 : ∑ μ, ∑ α, ∑ β, ∑ ρ, G ρ α * G μ β * q μ ρ * H α β =
      ∑ a, ∑ b, H a b * ∑ α, ∑ β, G a α * G b β * q α β := by
    rw [sum4_first_last]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hG ρ a, hG μ b, hq μ ρ]
    ring
  have h3 : ∑ μ, ∑ α, ∑ β, ∑ ρ, G ρ μ * G α β * q μ ρ * H α β =
      (∑ α, ∑ β, G α β * q α β) * ∑ α, ∑ β, G α β * H α β := by
    rw [sum4_last_second, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [hG ρ μ]
    ring
  rw [h1, h2, h3]

/-- **The volume-density part**: contracting `Γ_μ (g^{ρα} g^{μβ} - g^{ρμ} g^{αβ}) p_ρ` with `h_{αβ}`, where
`Γ_μ = Γ^κ_{κμ}`. -/
lemma hess_ds_contract (G H : Fin n → Fin n → ℝ) (Γv p : Fin n → ℝ) :
    ∑ μ, ∑ α, ∑ β, (Γv μ * ∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * p ρ) * H α β =
      (∑ α, ∑ β, H α β * (∑ ρ, G ρ α * p ρ) * ∑ μ, Γv μ * G μ β) -
        (∑ μ, Γv μ * ∑ ρ, G ρ μ * p ρ) * ∑ α, ∑ β, G α β * H α β := by
  have h1 : ∑ μ, ∑ α, ∑ β, (Γv μ * ∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * p ρ) * H α β =
      (∑ μ, ∑ α, ∑ β, Γv μ * G μ β * H α β * ∑ ρ, G ρ α * p ρ) -
        ∑ μ, ∑ α, ∑ β, (Γv μ * ∑ ρ, G ρ μ * p ρ) * (G α β * H α β) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    have e : ∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * p ρ =
        G μ β * (∑ ρ, G ρ α * p ρ) - G α β * ∑ ρ, G ρ μ * p ρ := by
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun ρ _ => by ring
    rw [e]
    ring
  have h2 : ∑ μ, ∑ α, ∑ β, Γv μ * G μ β * H α β * ∑ ρ, G ρ α * p ρ =
      ∑ α, ∑ β, H α β * (∑ ρ, G ρ α * p ρ) * ∑ μ, Γv μ * G μ β := by
    rw [sum3_first_last]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by ring
  have h3 : ∑ μ, ∑ α, ∑ β, (Γv μ * ∑ ρ, G ρ μ * p ρ) * (G α β * H α β) =
      (∑ μ, Γv μ * ∑ ρ, G ρ μ * p ρ) * ∑ α, ∑ β, G α β * H α β := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    generalize Γv μ * ∑ ρ, G ρ μ * p ρ = c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
  rw [h1, h2, h3]

/-- **Reindexing a five-fold sum** by a bijection of the index tuples. -/
lemma sum5_reindex (e : Fin n × Fin n × Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n × Fin n × Fin n)
    (f g : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
    (h : ∀ x : Fin n × Fin n × Fin n × Fin n × Fin n,
      f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 =
        g (e x).1 (e x).2.1 (e x).2.2.1 (e x).2.2.2.1 (e x).2.2.2.2) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ r, f a b c d r = ∑ a, ∑ b, ∑ c, ∑ d, ∑ r, g a b c d r := by
  have key := Fintype.sum_equiv e (fun x => f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (fun x => g x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) h
  simpa only [Fintype.sum_prod_type] using key

/-- **The first inverse-metric derivative term** of the Hessian identity:
`(∂_μ g^{ρα}) g^{μβ} p_ρ h_{αβ}`, with `∂_μ g^{xy} = -(Γ^x_{μγ} g^{γy} + Γ^y_{μγ} g^{xγ})`. -/
lemma hess_dG1_contract (G H : Fin n → Fin n → ℝ) (C : Fin n → Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hC : ∀ i j k, C i j k = C i k j) :
    ∑ μ, ∑ α, ∑ β, (∑ ρ, (-∑ γ, (C ρ μ γ * G γ α + C α μ γ * G ρ γ)) * G μ β * p ρ) * H α β =
      -(∑ a, ∑ b, ∑ μ, H a b * p μ * ∑ γ, ∑ ν, G a γ * G b ν * C μ γ ν) -
        ∑ α, ∑ β, ∑ μ, ∑ γ, H α β * G μ β * C α μ γ * ∑ ρ, G ρ γ * p ρ := by
  have hL : ∑ μ, ∑ α, ∑ β, (∑ ρ, (-∑ γ, (C ρ μ γ * G γ α + C α μ γ * G ρ γ)) * G μ β * p ρ) * H α β =
      -(∑ μ, ∑ α, ∑ β, ∑ ρ, ∑ γ, C ρ μ γ * G γ α * G μ β * p ρ * H α β) -
        ∑ μ, ∑ α, ∑ β, ∑ ρ, ∑ γ, C α μ γ * G ρ γ * G μ β * p ρ * H α β := by
    simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    ring
  have h1 : ∑ μ, ∑ α, ∑ β, ∑ ρ, ∑ γ, C ρ μ γ * G γ α * G μ β * p ρ * H α β =
      ∑ a, ∑ b, ∑ μ, H a b * p μ * ∑ γ, ∑ ν, G a γ * G b ν * C μ γ ν := by
    have e := sum5_reindex
      ⟨fun x => (x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.1),
        fun y => (y.2.2.2.2, y.1, y.2.1, y.2.2.1, y.2.2.2.1), fun _ => rfl, fun _ => rfl⟩
      (fun μ α β ρ γ => C ρ μ γ * G γ α * G μ β * p ρ * H α β)
      (fun a b μ γ ν => H a b * p μ * (G a γ * G b ν * C μ γ ν))
      (fun x => by
        show C x.2.2.2.1 x.1 x.2.2.2.2 * G x.2.2.2.2 x.2.1 * G x.1 x.2.2.1 * p x.2.2.2.1 *
            H x.2.1 x.2.2.1 =
          H x.2.1 x.2.2.1 * p x.2.2.2.1 *
            (G x.2.1 x.2.2.2.2 * G x.2.2.1 x.1 * C x.2.2.2.1 x.2.2.2.2 x.1)
        rw [hC x.2.2.2.1 x.1 x.2.2.2.2, hG x.2.2.2.2 x.2.1, hG x.1 x.2.2.1]
        ring)
    rw [e]
    simp only [Finset.mul_sum]
  have h2 : ∑ μ, ∑ α, ∑ β, ∑ ρ, ∑ γ, C α μ γ * G ρ γ * G μ β * p ρ * H α β =
      ∑ α, ∑ β, ∑ μ, ∑ γ, H α β * G μ β * C α μ γ * ∑ ρ, G ρ γ * p ρ := by
    have e := sum5_reindex
      ⟨fun x => (x.2.1, x.2.2.1, x.1, x.2.2.2.2, x.2.2.2.1),
        fun y => (y.2.2.1, y.1, y.2.1, y.2.2.2.2, y.2.2.2.1), fun _ => rfl, fun _ => rfl⟩
      (fun μ α β ρ γ => C α μ γ * G ρ γ * G μ β * p ρ * H α β)
      (fun α β μ γ ρ => H α β * G μ β * C α μ γ * (G ρ γ * p ρ))
      (fun x => by
        show C x.2.1 x.1 x.2.2.2.2 * G x.2.2.2.1 x.2.2.2.2 * G x.1 x.2.2.1 * p x.2.2.2.1 *
            H x.2.1 x.2.2.1 =
          H x.2.1 x.2.2.1 * G x.1 x.2.2.1 * C x.2.1 x.1 x.2.2.2.2 *
            (G x.2.2.2.1 x.2.2.2.2 * p x.2.2.2.1)
        ring)
    rw [e]
    simp only [Finset.mul_sum]
  rw [hL, h1, h2]

/-- **Reindexing a four-fold sum** by a bijection of the index tuples. -/
lemma sum4_reindex (e : Fin n × Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n × Fin n)
    (f g : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h : ∀ x : Fin n × Fin n × Fin n × Fin n,
      f x.1 x.2.1 x.2.2.1 x.2.2.2 = g (e x).1 (e x).2.1 (e x).2.2.1 (e x).2.2.2) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, g a b c d := by
  have key := Fintype.sum_equiv e (fun x => f x.1 x.2.1 x.2.2.1 x.2.2.2)
    (fun x => g x.1 x.2.1 x.2.2.1 x.2.2.2) h
  simpa only [Fintype.sum_prod_type] using key

/-- **The second inverse-metric derivative term** of the Hessian identity: `g^{ρα} (∂_μ g^{μβ}) p_ρ h_{αβ}`. -/
lemma hess_dG2_contract (G H : Fin n → Fin n → ℝ) (C : Fin n → Fin n → Fin n → ℝ) (p : Fin n → ℝ) :
    ∑ μ, ∑ α, ∑ β, (∑ ρ, (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) * G ρ α * p ρ) * H α β =
      -(∑ α, ∑ β, H α β * (∑ ρ, G ρ α * p ρ) * ∑ μ, (∑ κ, C κ κ μ) * G μ β) -
        (∑ α, ∑ β, H α β * (∑ ρ, G ρ α * p ρ) * ∑ σ, ∑ ν, G σ ν * C β σ ν) := by
  rw [sum3_first_last]
  have key : ∀ α β, ∑ μ, (∑ ρ, (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) * G ρ α * p ρ) * H α β =
      -(H α β * (∑ ρ, G ρ α * p ρ) * ∑ μ, (∑ κ, C κ κ μ) * G μ β) -
        H α β * (∑ ρ, G ρ α * p ρ) * ∑ σ, ∑ ν, G σ ν * C β σ ν := by
    intro α β
    have e1 : ∀ μ, ∑ ρ, (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) * G ρ α * p ρ =
        (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) * ∑ ρ, G ρ α * p ρ := by
      intro μ
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ρ _ => by ring
    have e2 : ∑ μ, (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) =
        -(∑ μ, (∑ κ, C κ κ μ) * G μ β) - ∑ σ, ∑ ν, G σ ν * C β σ ν := by
      have ea : ∑ μ, ∑ γ, C μ μ γ * G γ β = ∑ μ, (∑ κ, C κ κ μ) * G μ β := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun γ _ => by rw [Finset.sum_mul]
      have eb : ∑ μ, ∑ γ, C β μ γ * G μ γ = ∑ σ, ∑ ν, G σ ν * C β σ ν :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun γ _ => by ring
      rw [← ea, ← eb]
      simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib]
      ring
    rw [Finset.sum_congr rfl fun μ _ => congrArg (· * H α β) (e1 μ)]
    rw [← Finset.sum_mul, ← Finset.sum_mul, e2]
    ring
  rw [Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => key α β]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

/-- **The third inverse-metric derivative term** of the Hessian identity: `(∂_μ g^{ρμ}) g^{αβ} p_ρ h_{αβ}`. -/
lemma hess_dG3_contract (G H : Fin n → Fin n → ℝ) (C : Fin n → Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) :
    ∑ μ, ∑ α, ∑ β, (∑ ρ, (-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * G α β * p ρ) * H α β =
      -((∑ ρ, p ρ * ∑ σ, ∑ ν, G σ ν * C ρ σ ν) + (∑ μ, (∑ κ, C κ κ μ) * ∑ ρ, G ρ μ * p ρ)) *
        (∑ α, ∑ β, G α β * H α β) := by
  have e1 : ∀ μ α β, (∑ ρ, (-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * G α β * p ρ) * H α β =
      (∑ ρ, (-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * p ρ) * (G α β * H α β) := by
    intro μ α β
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  have ea : ∑ μ, ∑ ρ, ∑ γ, C ρ μ γ * G γ μ * p ρ = (∑ ρ, p ρ * ∑ σ, ∑ ν, G σ ν * C ρ σ ν) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun γ _ => by rw [hG γ μ]; ring
  have eb : ∑ μ, ∑ ρ, ∑ γ, C μ μ γ * G ρ γ * p ρ = (∑ μ, (∑ κ, C κ κ μ) * ∑ ρ, G ρ μ * p ρ) := by
    refine (sum3_first_last (fun γ μ ρ => C μ μ γ * G ρ γ * p ρ)).symm.trans ?_
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  have ef : ∀ μ ρ, (-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * p ρ =
      -(∑ γ, C ρ μ γ * G γ μ * p ρ) - ∑ γ, C μ μ γ * G ρ γ * p ρ := by
    intro μ ρ
    rw [neg_mul, Finset.sum_mul]
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  have e2 : ∑ μ, ∑ ρ, (-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * p ρ =
      -((∑ ρ, p ρ * ∑ σ, ∑ ν, G σ ν * C ρ σ ν) + (∑ μ, (∑ κ, C κ κ μ) * ∑ ρ, G ρ μ * p ρ)) := by
    rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ρ _ => ef μ ρ]
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rw [ea, eb]
    ring
  have e3 : ∑ μ, ∑ α, ∑ β, (∑ ρ, (-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * p ρ) * (G α β * H α β) =
      (∑ μ, ∑ ρ, (-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * p ρ) * (∑ α, ∑ β, G α β * H α β) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    generalize ∑ ρ, (-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * p ρ = c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun β _ => e1 μ α β, e3, e2]

/-- The fourth inverse-metric derivative term, with an abstract vector `P` in place of `g^{ρμ} p_ρ`. -/
lemma hess_dG4_core (G H : Fin n → Fin n → ℝ) (C : Fin n → Fin n → Fin n → ℝ) (P : Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hH : ∀ a b, H a b = H b a) (hC : ∀ i j k, C i j k = C i k j) :
    ∑ μ, ∑ α, ∑ β, (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)) * P μ * H α β =
      -(2 * ∑ α, ∑ β, ∑ μ, ∑ γ, H α β * G μ β * C α μ γ * P γ) := by
  have ef : ∀ μ α β, (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)) * P μ * H α β =
      -(∑ γ, C α μ γ * G γ β * P μ * H α β) - ∑ γ, C β μ γ * G α γ * P μ * H α β := by
    intro μ α β
    rw [neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul]
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  have ea : ∑ μ, ∑ α, ∑ β, ∑ γ, C α μ γ * G γ β * P μ * H α β =
      ∑ α, ∑ β, ∑ μ, ∑ γ, H α β * G μ β * C α μ γ * P γ :=
    sum4_reindex
      ⟨fun x => (x.2.1, x.2.2.1, x.2.2.2, x.1), fun y => (y.2.2.2, y.1, y.2.1, y.2.2.1),
        fun _ => rfl, fun _ => rfl⟩
      (fun μ α β γ => C α μ γ * G γ β * P μ * H α β)
      (fun α β μ γ => H α β * G μ β * C α μ γ * P γ)
      (fun x => by
        show C x.2.1 x.1 x.2.2.2 * G x.2.2.2 x.2.2.1 * P x.1 * H x.2.1 x.2.2.1 =
          H x.2.1 x.2.2.1 * G x.2.2.2 x.2.2.1 * C x.2.1 x.2.2.2 x.1 * P x.1
        rw [hC x.2.1 x.1 x.2.2.2]
        ring)
  have eb : ∑ μ, ∑ α, ∑ β, ∑ γ, C β μ γ * G α γ * P μ * H α β =
      ∑ α, ∑ β, ∑ μ, ∑ γ, H α β * G μ β * C α μ γ * P γ :=
    sum4_reindex
      ⟨fun x => (x.2.2.1, x.2.1, x.2.2.2, x.1), fun y => (y.2.2.2, y.2.1, y.1, y.2.2.1),
        fun _ => rfl, fun _ => rfl⟩
      (fun μ α β γ => C β μ γ * G α γ * P μ * H α β)
      (fun α β μ γ => H α β * G μ β * C α μ γ * P γ)
      (fun x => by
        show C x.2.2.1 x.1 x.2.2.2 * G x.2.1 x.2.2.2 * P x.1 * H x.2.1 x.2.2.1 =
          H x.2.2.1 x.2.1 * G x.2.2.2 x.2.1 * C x.2.2.1 x.2.2.2 x.1 * P x.1
        rw [hC x.2.2.1 x.1 x.2.2.2, hG x.2.1 x.2.2.2, hH x.2.1 x.2.2.1]
        ring)
  rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun β _ => ef μ α β]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [ea, eb]
  ring

/-- **The fourth inverse-metric derivative term** of the Hessian identity: `g^{ρμ} (∂_μ g^{αβ}) p_ρ h_{αβ}`. -/
lemma hess_dG4_contract (G H : Fin n → Fin n → ℝ) (C : Fin n → Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hH : ∀ a b, H a b = H b a) (hC : ∀ i j k, C i j k = C i k j) :
    ∑ μ, ∑ α, ∑ β, (∑ ρ, (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)) * G ρ μ * p ρ) * H α β =
      -(2 * (∑ α, ∑ β, ∑ μ, ∑ γ, H α β * G μ β * C α μ γ * ∑ ρ, G ρ γ * p ρ)) := by
  have hP : ∀ μ α β, (∑ ρ, (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)) * G ρ μ * p ρ) * H α β =
      (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)) * (fun μ => ∑ ρ, G ρ μ * p ρ) μ * H α β := by
    intro μ α β
    show _ = (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)) * (∑ ρ, G ρ μ * p ρ) * H α β
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  refine Eq.trans (Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun β _ => hP μ α β) ?_
  exact hess_dG4_core G H C (fun μ => ∑ ρ, G ρ μ * p ρ) hG hH hC

/-- Linearity of a triple sum in six summands. -/
lemma sum3_lin6 (s : ℝ) (t0 t1 t2 t3 t4 t5 : Fin n → Fin n → Fin n → ℝ) :
    ∑ μ, ∑ α, ∑ β, s * (t0 μ α β + t1 μ α β + t2 μ α β - t3 μ α β - t4 μ α β + t5 μ α β) =
      s * ((∑ μ, ∑ α, ∑ β, t0 μ α β) + (∑ μ, ∑ α, ∑ β, t1 μ α β) + (∑ μ, ∑ α, ∑ β, t2 μ α β) -
        (∑ μ, ∑ α, ∑ β, t3 μ α β) - (∑ μ, ∑ α, ∑ β, t4 μ α β) + ∑ μ, ∑ α, ∑ β, t5 μ α β) := by
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- **The algebraic Hessian identity.** With `G` the inverse metric, `C` the Christoffel symbols, `p` the
gradient and `q` the second partial derivatives of `φ`, and `s = √|g|`: the values part of the Palatini
vector against the gradient, minus the divergence of the coefficient `c^{μαβ}` against `h`, is
`-s h_{ab} (∇^a ∇^b φ - g^{ab} □φ)`, where `∇^a ∇^b φ = g^{aα} g^{bβ} (q_{αβ} - Γ^μ_{αβ} p_μ)` and
`□φ = g^{αβ} q_{αβ} - p_ρ g^{σν} Γ^ρ_{σν}`. -/
theorem hess_assemble (G H q : Fin n → Fin n → ℝ) (C : Fin n → Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (s : ℝ) (hG : ∀ a b, G a b = G b a) (hH : ∀ a b, H a b = H b a) (hq : ∀ a b, q a b = q b a)
    (hC : ∀ i j k, C i j k = C i k j) :
    s * (∑ ρ, ((∑ σ, ∑ ν, G σ ν * (-∑ a, ∑ b, G ρ a * H a b * C b σ ν)) -
        ∑ σ, G ρ σ * ∑ κ, (-∑ a, ∑ b, G κ a * H a b * C b κ σ)) * p ρ) -
      ∑ μ, ∑ α, ∑ β, (s * (∑ κ, C κ κ μ) * (∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * p ρ) +
        s * ∑ ρ, (((-∑ γ, (C ρ μ γ * G γ α + C α μ γ * G ρ γ)) * G μ β + G ρ α * (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) - ((-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * G α β + G ρ μ * (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)))) * p ρ +
          (G ρ α * G μ β - G ρ μ * G α β) * q μ ρ)) * H α β =
      -s * ((∑ a, ∑ b, H a b * ∑ α, ∑ β, G a α * G b β * q α β) -
        (∑ a, ∑ b, ∑ μ, H a b * p μ * ∑ γ, ∑ ν, G a γ * G b ν * C μ γ ν) -
        (∑ α, ∑ β, G α β * q α β) * (∑ α, ∑ β, G α β * H α β) +
        (∑ ρ, p ρ * ∑ σ, ∑ ν, G σ ν * C ρ σ ν) * (∑ α, ∑ β, G α β * H α β)) := by
  have hρ : ∀ μ α β, ∑ ρ, (((-∑ γ, (C ρ μ γ * G γ α + C α μ γ * G ρ γ)) * G μ β + G ρ α * (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) - ((-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * G α β + G ρ μ * (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)))) * p ρ +
          (G ρ α * G μ β - G ρ μ * G α β) * q μ ρ) =
      (∑ ρ, (-∑ γ, (C ρ μ γ * G γ α + C α μ γ * G ρ γ)) * G μ β * p ρ) + (∑ ρ, (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) * G ρ α * p ρ) -
        (∑ ρ, (-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * G α β * p ρ) - (∑ ρ, (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)) * G ρ μ * p ρ) + ∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * q μ ρ := by
    intro μ α β
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  have hterm : ∀ μ α β, (s * (∑ κ, C κ κ μ) * (∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * p ρ) +
        s * ∑ ρ, (((-∑ γ, (C ρ μ γ * G γ α + C α μ γ * G ρ γ)) * G μ β + G ρ α * (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) - ((-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * G α β + G ρ μ * (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)))) * p ρ +
          (G ρ α * G μ β - G ρ μ * G α β) * q μ ρ)) * H α β =
      s * (((∑ κ, C κ κ μ) * ∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * p ρ) * H α β + (∑ ρ, (-∑ γ, (C ρ μ γ * G γ α + C α μ γ * G ρ γ)) * G μ β * p ρ) * H α β + (∑ ρ, (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) * G ρ α * p ρ) * H α β - (∑ ρ, (-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * G α β * p ρ) * H α β - (∑ ρ, (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)) * G ρ μ * p ρ) * H α β + (∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * q μ ρ) * H α β) := by
    intro μ α β
    rw [hρ μ α β]
    ring
  have hsplit : ∑ μ, ∑ α, ∑ β, (s * (∑ κ, C κ κ μ) * (∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * p ρ) +
        s * ∑ ρ, (((-∑ γ, (C ρ μ γ * G γ α + C α μ γ * G ρ γ)) * G μ β + G ρ α * (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) - ((-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * G α β + G ρ μ * (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)))) * p ρ +
          (G ρ α * G μ β - G ρ μ * G α β) * q μ ρ)) * H α β =
      s * ((∑ μ, ∑ α, ∑ β, ((∑ κ, C κ κ μ) * ∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * p ρ) * H α β) + (∑ μ, ∑ α, ∑ β, (∑ ρ, (-∑ γ, (C ρ μ γ * G γ α + C α μ γ * G ρ γ)) * G μ β * p ρ) * H α β) + (∑ μ, ∑ α, ∑ β, (∑ ρ, (-∑ γ, (C μ μ γ * G γ β + C β μ γ * G μ γ)) * G ρ α * p ρ) * H α β) - (∑ μ, ∑ α, ∑ β, (∑ ρ, (-∑ γ, (C ρ μ γ * G γ μ + C μ μ γ * G ρ γ)) * G α β * p ρ) * H α β) - (∑ μ, ∑ α, ∑ β, (∑ ρ, (-∑ γ, (C α μ γ * G γ β + C β μ γ * G α γ)) * G ρ μ * p ρ) * H α β) + (∑ μ, ∑ α, ∑ β, (∑ ρ, (G ρ α * G μ β - G ρ μ * G α β) * q μ ρ) * H α β)) := by
    rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => hterm μ α β]
    exact sum3_lin6 s _ _ _ _ _ _
  have hW0 := W0_contract G H C p
  have hds := hess_ds_contract G H (fun μ => ∑ κ, C κ κ μ) p
  beta_reduce at hds
  have h1 := hess_dG1_contract G H C p hG hC
  have h2 := hess_dG2_contract G H C p
  have h3 := hess_dG3_contract G H C p hG
  have h4 := hess_dG4_contract G H C p hG hH hC
  have h5 := hess_q_contract G H q hG hq
  have hA : (∑ a, ∑ b, H a b * ∑ κ, ∑ σ, G κ a * C b κ σ * (∑ ρ, G ρ σ * p ρ)) = (∑ α, ∑ β, ∑ μ, ∑ γ, H α β * G μ β * C α μ γ * ∑ ρ, G ρ γ * p ρ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun γ _ => by rw [hH β α]; ring
  rw [hsplit]
  linear_combination s * hW0 - s * hds - s * h1 - s * h2 + s * h3 + s * h4 - s * h5 + s * hA

end Lightlike
