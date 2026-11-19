import Lightlike.Spacetime.Curvature

/-!
# Index algebra for the boundary term with a general conormal

For a symmetric array `G` (inverse metric), a symmetric array `k` (the normal derivative of the
perturbation), a covector `ν` (the conormal of the boundary) and an array `D` of the form

`D ρ σ τ = ½ (ν_σ (G k)^ρ_τ + ν_τ (G k)^ρ_σ - N^ρ k_{στ})`, with `N^ρ = G^{ρb} ν_b`

(the variation of the Christoffel symbols at a boundary point where the perturbation vanishes):

* `conormal_flux`: `(G^{στ} D^ρ_{στ} - G^{ρσ} D^κ_{κσ}) ν_ρ = k(N, N) - N² tr k`;
* `conormal_hup`: `(G^{αβ} - N^α N^β / N²) D^μ_{αβ} ν_μ = ½ (k(N, N) - N² tr k)` if `N² ≠ 0`.

Hence the first is twice the second: the flux of the Palatini vector through the boundary is twice the
contraction that appears in the variation of the mean curvature.

Supporting lemmas; no catalogue entry.
-/

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The data of the two contractions: the vector `N`, the covector `k N`, `N²`, `tr k` and `k(N, N)`, with
the contraction `D^μ_{στ} ν_μ` and the trace `D^κ_{κσ}`. -/
theorem conormal_core (G k : Fin n → Fin n → ℝ) (ν : Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hk : ∀ a b, k a b = k b a)
    (hD : ∀ ρ σ τ, D ρ σ τ = (1 / 2) * (ν σ * (∑ l, G ρ l * k l τ) + ν τ * (∑ l, G ρ l * k l σ) -
      (∑ b, G ρ b * ν b) * k σ τ)) :
    ∃ (N kN : Fin n → ℝ) (S Tr Q : ℝ), (∀ a, N a = ∑ b, G a b * ν b) ∧
      (∀ τ, kN τ = ∑ l, N l * k l τ) ∧ S = ∑ a, ν a * N a ∧ Tr = ∑ a, ∑ b, G a b * k a b ∧
      Q = ∑ τ, N τ * kN τ ∧
      (∀ σ τ, ∑ μ, D μ σ τ * ν μ = (1 / 2) * (ν σ * kN τ + ν τ * kN σ - S * k σ τ)) ∧
      (∀ σ, ∑ κ, D κ κ σ = (1 / 2) * (ν σ * Tr)) ∧
      (∑ σ, ∑ τ, G σ τ * ((1 / 2) * (ν σ * kN τ + ν τ * kN σ - S * k σ τ)) =
        (1 / 2) * (2 * Q - S * Tr)) ∧
      (∑ α, ∑ β, N α * N β * (ν α * kN β + ν β * kN α - S * k α β) = S * Q) := by
  obtain ⟨N, hN⟩ : ∃ N : Fin n → ℝ, N = fun a => ∑ b, G a b * ν b := ⟨_, rfl⟩
  have hNa : ∀ a, N a = ∑ b, G a b * ν b := fun a => by rw [hN]
  obtain ⟨kN, hkN⟩ : ∃ kN : Fin n → ℝ, kN = fun τ => ∑ l, N l * k l τ := ⟨_, rfl⟩
  have hkNa : ∀ τ, kN τ = ∑ l, N l * k l τ := fun τ => by rw [hkN]
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ a, ν a * N a := ⟨_, rfl⟩
  obtain ⟨Tr, hTr⟩ : ∃ Tr : ℝ, Tr = ∑ a, ∑ b, G a b * k a b := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑ τ, N τ * kN τ := ⟨_, rfl⟩
  have hNsym : ∀ τ, ∑ σ, G σ τ * ν σ = N τ := fun τ => by
    rw [hNa τ]
    exact Finset.sum_congr rfl fun σ _ => by rw [hG σ τ]
  have hGkν : ∀ τ, ∑ μ, ν μ * ∑ l, G μ l * k l τ = kN τ := by
    intro τ
    rw [hkNa τ]
    have e : ∀ μ, ν μ * ∑ l, G μ l * k l τ = ∑ l, G μ l * ν μ * k l τ := fun μ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [Finset.sum_congr rfl fun μ _ => e μ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hNsym l, Finset.sum_mul]
  have hc : ∀ σ τ, ∑ μ, D μ σ τ * ν μ = (1 / 2) * (ν σ * kN τ + ν τ * kN σ - S * k σ τ) := by
    intro σ τ
    have e : ∀ μ, D μ σ τ * ν μ = (1 / 2) * (ν σ * (ν μ * ∑ l, G μ l * k l τ) +
        ν τ * (ν μ * ∑ l, G μ l * k l σ) - ν μ * N μ * k σ τ) := fun μ => by
      rw [hD μ σ τ, ← hNa μ]
      ring
    rw [Finset.sum_congr rfl fun μ _ => e μ, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, hGkν τ, hGkν σ,
      ← hS]
  have hd : ∀ σ, ∑ κ, D κ κ σ = (1 / 2) * (ν σ * Tr) := by
    intro σ
    have e : ∀ κ, D κ κ σ = (1 / 2) * (ν κ * (∑ l, G κ l * k l σ) + ν σ * (∑ l, G κ l * k l κ) -
        N κ * k κ σ) := fun κ => by
      rw [hD κ κ σ, ← hNa κ]
    have e3 : ∑ κ, ∑ l, G κ l * k l κ = Tr := by
      rw [hTr]
      exact Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun l _ => by rw [hk l κ]
    rw [Finset.sum_congr rfl fun κ _ => e κ, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hGkν σ, ← Finset.mul_sum, e3, ← hkNa σ]
    ring
  have hb : ∑ σ, ∑ τ, G σ τ * ((1 / 2) * (ν σ * kN τ + ν τ * kN σ - S * k σ τ)) =
      (1 / 2) * (2 * Q - S * Tr) := by
    have e1 : ∑ σ, ∑ τ, G σ τ * ν σ * kN τ = Q := by
      rw [Finset.sum_comm, hQ]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Finset.sum_mul, hNsym τ]
    have e2 : ∑ σ, ∑ τ, G σ τ * ν τ * kN σ = Q := by
      rw [hQ]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [← Finset.sum_mul, ← hNa σ]
    have e : ∀ σ τ, G σ τ * ((1 / 2) * (ν σ * kN τ + ν τ * kN σ - S * k σ τ)) =
        (1 / 2) * (G σ τ * ν σ * kN τ + G σ τ * ν τ * kN σ - S * (G σ τ * k σ τ)) := fun σ τ => by
      ring
    rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => e σ τ]
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [e1, e2, ← hTr]
    ring
  have hg1 : ∑ α, ∑ β, N α * N β * (ν α * kN β + ν β * kN α - S * k α β) = S * Q := by
    have a1 : ∑ α, ∑ β, ν α * N α * (N β * kN β) = S * Q := by
      rw [hS, hQ, Finset.sum_mul_sum]
    have a2 : ∑ α, ∑ β, N α * kN α * (ν β * N β) = Q * S := by
      rw [hS, hQ, Finset.sum_mul_sum]
    have a3 : ∑ α, ∑ β, S * (N β * (N α * k α β)) = S * Q := by
      rw [Finset.sum_comm, hQ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [hkNa β, ← Finset.mul_sum, ← Finset.mul_sum]
    have e : ∀ α β, N α * N β * (ν α * kN β + ν β * kN α - S * k α β) =
        ν α * N α * (N β * kN β) + N α * kN α * (ν β * N β) - S * (N β * (N α * k α β)) :=
      fun α β => by ring
    rw [Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => e α β]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [a1, a2, a3]
    ring
  exact ⟨N, kN, S, Tr, Q, hNa, hkNa, hS, hTr, hQ, hc, hd, hb, hg1⟩

/-- **The flux contraction**: `(G^{στ} D^ρ_{στ} - G^{ρσ} D^κ_{κσ}) ν_ρ = k(N, N) - N² tr k`. -/
theorem conormal_flux (G k : Fin n → Fin n → ℝ) (ν : Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hk : ∀ a b, k a b = k b a)
    (hD : ∀ ρ σ τ, D ρ σ τ = (1 / 2) * (ν σ * (∑ l, G ρ l * k l τ) + ν τ * (∑ l, G ρ l * k l σ) -
      (∑ b, G ρ b * ν b) * k σ τ)) :
    ∑ ρ, ((∑ σ, ∑ τ, G σ τ * D ρ σ τ) - ∑ σ, G ρ σ * ∑ κ, D κ κ σ) * ν ρ =
      (∑ τ, (∑ b, G τ b * ν b) * ∑ l, (∑ b, G l b * ν b) * k l τ) -
        (∑ a, ν a * ∑ b, G a b * ν b) * ∑ a, ∑ b, G a b * k a b := by
  obtain ⟨N, kN, S, Tr, Q, hNa, hkNa, hS, hTr, hQ, hc, hd, hb, -⟩ := conormal_core G k ν D hG hk hD
  have f1 : ∑ ρ, (∑ σ, ∑ τ, G σ τ * D ρ σ τ) * ν ρ = (1 / 2) * (2 * Q - S * Tr) := by
    rw [← hb]
    have e : ∀ ρ, (∑ σ, ∑ τ, G σ τ * D ρ σ τ) * ν ρ = ∑ σ, ∑ τ, G σ τ * (D ρ σ τ * ν ρ) :=
      fun ρ => by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun τ _ => by ring
    rw [Finset.sum_congr rfl fun ρ _ => e ρ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.mul_sum, hc σ τ]
  have f2 : ∑ ρ, (∑ σ, G ρ σ * ∑ κ, D κ κ σ) * ν ρ = (1 / 2) * (S * Tr) := by
    have e : ∀ ρ, (∑ σ, G ρ σ * ∑ κ, D κ κ σ) * ν ρ = (1 / 2) * Tr * (ν ρ * N ρ) := fun ρ => by
      have e' : ∑ σ, G ρ σ * ∑ κ, D κ κ σ = (1 / 2) * Tr * N ρ := by
        rw [hNa ρ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by rw [hd σ]; ring
      rw [e']
      ring
    rw [Finset.sum_congr rfl fun ρ _ => e ρ, ← Finset.mul_sum, ← hS]
    ring
  have hQ' : (∑ τ, (∑ b, G τ b * ν b) * ∑ l, (∑ b, G l b * ν b) * k l τ) = Q := by
    rw [hQ]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hkNa τ, hNa τ]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [hNa l]
  have hS' : (∑ a, ν a * ∑ b, G a b * ν b) = S := by
    rw [hS]
    exact Finset.sum_congr rfl fun a _ => by rw [hNa a]
  rw [hQ', hS', ← hTr, Finset.sum_congr rfl fun ρ _ => sub_mul _ _ (ν ρ), Finset.sum_sub_distrib, f1,
    f2]
  ring

/-- **The contraction with the induced inverse metric**:
`(G^{αβ} - N^α N^β / N²) D^μ_{αβ} ν_μ = ½ (k(N, N) - N² tr k)` if `N² ≠ 0`. -/
theorem conormal_hup (G k : Fin n → Fin n → ℝ) (ν : Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hk : ∀ a b, k a b = k b a)
    (hD : ∀ ρ σ τ, D ρ σ τ = (1 / 2) * (ν σ * (∑ l, G ρ l * k l τ) + ν τ * (∑ l, G ρ l * k l σ) -
      (∑ b, G ρ b * ν b) * k σ τ))
    (hS0 : (∑ a, ν a * ∑ b, G a b * ν b) ≠ 0) :
    ∑ α, ∑ β, (G α β - (∑ b, G α b * ν b) * (∑ b, G β b * ν b) / (∑ a, ν a * ∑ b, G a b * ν b)) *
        ∑ μ, D μ α β * ν μ =
      (1 / 2) * ((∑ τ, (∑ b, G τ b * ν b) * ∑ l, (∑ b, G l b * ν b) * k l τ) -
        (∑ a, ν a * ∑ b, G a b * ν b) * ∑ a, ∑ b, G a b * k a b) := by
  obtain ⟨N, kN, S, Tr, Q, hNa, hkNa, hS, hTr, hQ, hc, -, hb, hg1⟩ := conormal_core G k ν D hG hk hD
  have hQ' : (∑ τ, (∑ b, G τ b * ν b) * ∑ l, (∑ b, G l b * ν b) * k l τ) = Q := by
    rw [hQ]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hkNa τ, hNa τ]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [hNa l]
  have hS' : (∑ a, ν a * ∑ b, G a b * ν b) = S := by
    rw [hS]
    exact Finset.sum_congr rfl fun a _ => by rw [hNa a]
  rw [hS'] at hS0
  have e : ∀ α β, (G α β - (∑ b, G α b * ν b) * (∑ b, G β b * ν b) / S) * ∑ μ, D μ α β * ν μ =
      G α β * ((1 / 2) * (ν α * kN β + ν β * kN α - S * k α β)) -
        (1 / 2) * S⁻¹ * (N α * N β * (ν α * kN β + ν β * kN α - S * k α β)) := fun α β => by
    rw [hc α β, ← hNa α, ← hNa β, div_eq_mul_inv]
    ring
  rw [hQ', hS', ← hTr, Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => e α β]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hb, hg1]
  have hinv : S⁻¹ * S = 1 := inv_mul_cancel₀ hS0
  linear_combination (-(1 / 2) * Q) * hinv

end Lightlike
