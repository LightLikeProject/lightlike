import Lightlike.Surfaces.Basic

/-!
# Mod-2 homology of a closed surface: `χ ≤ 2`

The chain complex of `Lightlike/PonzanoRegge/SphereHomology.lean` (coefficients in a field of
characteristic `2`) applied to closed surfaces. The arguments there for the 2-cycles and the
0-boundaries use only that every edge lies in two triangles, that vertex links are connected and
that the 1-skeleton is connected; they are restated here for `IsSurface`.

* `IsSurface.ker_bd2`: the 2-cycles are `0` and the sum of all triangles.
* `IsSurface.mem_range_bd1_of_sum_eq_zero`: every 0-chain with coefficient sum `0` is a boundary.
* `IsSurface.euler_le`: **the Euler characteristic of a closed surface is at most `2`**. The
  boundaries of 2-chains (dimension `F - 1`) lie in the 1-cycles (dimension `E - (V - 1)`).
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V] {K : Type*} [Field K] [CharP K 2]

/-- **A 2-chain whose boundary vanishes on every edge through `u` is constant on the triangles
around `u`**: the link of `u` is connected, and the two triangles at each edge through `u` have the
same coefficient. -/
lemma IsSurface.const_around {L : Finset (Finset V)} (hS : IsSurface L) {σ : L → K} {u : V}
    (h0 : ∀ e : edges2 L, u ∈ (e : Finset V) → bd2 K L σ e = 0) {τ τ' : L}
    (hτ : u ∈ (τ : Finset V)) (hτ' : u ∈ (τ' : Finset V)) : σ τ = σ τ' := by
  have hu : u ∈ verts2 L := mem_verts2.mpr ⟨τ, τ.2, hτ⟩
  obtain ⟨w, hw, hwu⟩ := exists_other (hS.card τ τ.2) u
  obtain ⟨w', hw', hw'u⟩ := exists_other (hS.card τ' τ'.2) u
  have step_edge : ∀ y : V, y ≠ u → ∀ t₁ t₂ : L, ({u, y} : Finset V) ⊆ t₁ →
      ({u, y} : Finset V) ⊆ t₂ → σ t₁ = σ t₂ := by
    intro y hy t₁ t₂ h1 h2
    have he : ({u, y} : Finset V) ∈ edges2 L := mem_edges2.mpr ⟨t₁, t₁.2, h1, card_pair hy.symm⟩
    exact eq_of_bd2_eq_zero hS.closed (e := ⟨_, he⟩) (h0 ⟨_, he⟩ (by simp)) h1 h2
  have lkMem : ∀ t : L, ∀ y ∈ (t : Finset V), u ∈ (t : Finset V) → y ≠ u → y ∈ verts2 (lk2 L u) :=
    fun t y hy hut hyu => mem_verts2.mpr ⟨(t : Finset V).erase u,
      mem_lk2.mpr ⟨notMem_erase _ _, by rw [insert_erase hut]; exact t.2⟩, mem_erase.mpr ⟨hyu, hy⟩⟩
  have path := hS.link u hu w (lkMem τ w hw hτ hwu) w' (lkMem τ' w' hw' hτ' hw'u)
  have key : ∀ y, Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ lk2 L u) w y →
      y ≠ u → ∀ t : L, ({u, y} : Finset V) ⊆ t → σ t = σ τ := by
    intro y hy
    induction hy with
    | refl => exact fun _ t ht => step_edge w hwu t τ ht (pair_subset_of_mem hτ hw)
    | @tail p q _ hpq ih =>
      intro hq t ht
      obtain ⟨hupq, hT⟩ := mem_lk2.mp hpq
      have hpu : p ≠ u := fun h => hupq (h ▸ by simp)
      let T : L := ⟨insert u {p, q}, hT⟩
      have hT1 : ({u, p} : Finset V) ⊆ T := pair_subset_of_mem (by simp [T]) (by simp [T])
      have hT2 : ({u, q} : Finset V) ⊆ T := pair_subset_of_mem (by simp [T]) (by simp [T])
      rw [step_edge q hq t T ht hT2]
      exact ih hpu T hT1
  exact (key w' path hw'u τ' (pair_subset_of_mem hτ' hw')).symm

/-- **The 2-cycles of a closed surface are constant.** -/
lemma IsSurface.const_of_bd2_eq_zero {L : Finset (Finset V)} (hS : IsSurface L) {σ : L → K}
    (h0 : bd2 K L σ = 0) (τ τ' : L) : σ τ = σ τ' := by
  have hz : ∀ (u : V) (e : edges2 L), u ∈ (e : Finset V) → bd2 K L σ e = 0 := fun _ e _ => by
    rw [h0]; rfl
  obtain ⟨u, hu⟩ : (τ : Finset V).Nonempty := card_pos.mp (by rw [hS.card τ τ.2]; norm_num)
  obtain ⟨u', hu'⟩ : (τ' : Finset V).Nonempty := card_pos.mp (by rw [hS.card τ' τ'.2]; norm_num)
  have hconn := hS.connected u (mem_verts2.mpr ⟨τ, τ.2, hu⟩) u' (mem_verts2.mpr ⟨τ', τ'.2, hu'⟩)
  have key : ∀ y, Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ edges2 L) u y →
      ∀ t : L, y ∈ (t : Finset V) → σ t = σ τ := by
    intro y hy
    induction hy with
    | refl => exact fun t ht => IsSurface.const_around hS (hz u) ht hu
    | @tail p q _ hpq ih =>
      intro t ht
      obtain ⟨T, hTL, hsub, -⟩ := mem_edges2.mp hpq
      have h1 := ih ⟨T, hTL⟩ (hsub (by simp))
      rw [IsSurface.const_around hS (hz q) ht (show q ∈ ((⟨T, hTL⟩ : L) : Finset V) from hsub (by simp))]
      exact h1
  exact (key u' hconn τ' hu').symm

/-! ## The 2-cycles -/

/-- **The 2-cycles of a closed surface are `0` and the sum of all triangles.** -/
theorem IsSurface.ker_bd2 {L : Finset (Finset V)} (hS : IsSurface L) :
    LinearMap.ker (bd2 K L) = Submodule.span (K) {fun _ => 1} := by
  apply le_antisymm
  · intro σ hσ
    rw [LinearMap.mem_ker] at hσ
    rw [Submodule.mem_span_singleton]
    by_cases hL : L.Nonempty
    · obtain ⟨τ₀, hτ₀⟩ := hL
      refine ⟨σ ⟨τ₀, hτ₀⟩, funext fun τ => ?_⟩
      simp [IsSurface.const_of_bd2_eq_zero hS hσ τ ⟨τ₀, hτ₀⟩]
    · refine ⟨0, funext fun τ => absurd ⟨τ.1, τ.2⟩ hL⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    funext e
    obtain ⟨t₁, ht₁, t₂, ht₂, hne, hf⟩ := two_tris hS.closed e.2
    rw [bd2_apply, sum_filter_univ_coe (fun τ => (e : Finset V) ⊆ τ), hf, sum_pair hne]
    simp only [extFn, ht₁, ht₂, dite_true, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero 1

theorem IsSurface.finrank_ker_bd2 {L : Finset (Finset V)} (hS : IsSurface L)
    (hL : L.Nonempty) : Module.finrank (K) (LinearMap.ker (bd2 K L)) = 1 := by
  obtain ⟨τ₀, hτ₀⟩ := hL
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  have h1 : (fun _ => (1 : K) : L → K) ≠ 0 := fun h => h10 (congrFun h ⟨τ₀, hτ₀⟩)
  exact (LinearEquiv.ofEq _ _ hS.ker_bd2).finrank_eq.trans (finrank_span_singleton h1)

/-- **Every 0-chain `δ_u + δ_{u₀}` is a boundary**: join `u₀` to `u` by a path of edges. -/
lemma IsSurface.single_add_mem_range {L : Finset (Finset V)} (hS : IsSurface L) (u₀ u : verts2 L) :
    (Pi.single u (1 : K) + Pi.single u₀ 1 : verts2 L → K) ∈ LinearMap.range (bd1 K L) := by
  have key : ∀ y, Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 L) (u₀ : V) y →
      ∀ hy : y ∈ verts2 L,
        (Pi.single ⟨y, hy⟩ (1 : K) + Pi.single u₀ 1 : verts2 L → K) ∈ LinearMap.range (bd1 K L) := by
    intro y hy
    induction hy with
    | refl =>
      intro hy
      rw [show (⟨(u₀ : V), hy⟩ : verts2 L) = u₀ from rfl, single_add_self]
      exact zero_mem _
    | @tail p q _ hpq ih =>
      intro hq
      obtain ⟨τ, hτ, hsub, hc⟩ := mem_edges2.mp hpq
      have hpv : p ∈ verts2 L := mem_verts2_of_sub hτ hsub (by simp)
      have hpq' : p ≠ q := by
        rintro rfl
        simp at hc
      have h := add_mem (ih hpv) (LinearMap.mem_range_self (bd1 K L) (Pi.single ⟨_, hpq⟩ 1))
      rw [bd1_single_pair hpq' hpq hpv hq] at h
      convert h using 1
      calc _ = (Pi.single ⟨p, hpv⟩ (1 : K) + Pi.single ⟨p, hpv⟩ 1) +
            (Pi.single ⟨q, hq⟩ 1 + Pi.single u₀ 1 : verts2 L → K) := by
              rw [single_add_self, zero_add]
        _ = _ := by abel
  exact key u (hS.connected u₀ u₀.2 u u.2) u.2

/-- **The 0-chains with coefficient sum `0` are boundaries.** -/
lemma IsSurface.mem_range_bd1_of_sum_eq_zero {L : Finset (Finset V)} (hS : IsSurface L)
    (u₀ : verts2 L) {f : verts2 L → K} (hf : ∑ v, f v = 0) : f ∈ LinearMap.range (bd1 K L) := by
  have hrepr : f = ∑ u, f u • (Pi.single u (1 : K) + Pi.single u₀ 1 : verts2 L → K) := by
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hf, zero_mul, add_zero]
    simp [Pi.single_apply]
  rw [hrepr]
  exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (IsSurface.single_add_mem_range hS u₀ u)


/-- **The Euler characteristic of a closed surface is at most `2`**, for any field of
characteristic `2` used as coefficients. -/
theorem IsSurface.euler_le_of_field (K : Type*) [Field K] [CharP K 2] {L : Finset (Finset V)}
    (hS : IsSurface L) : euler2 L ≤ 2 := by
  obtain ⟨τ₀, hτ₀⟩ := hS.nonempty
  obtain ⟨x₀, hx₀⟩ : τ₀.Nonempty := card_pos.mp (by rw [hS.card τ₀ hτ₀]; norm_num)
  let u₀ : verts2 L := ⟨x₀, mem_verts2.mpr ⟨τ₀, hτ₀, hx₀⟩⟩
  let φ : (verts2 L → K) →ₗ[K] K := ∑ v : verts2 L, LinearMap.proj v
  have hφ : ∀ f, φ f = ∑ v, f v := fun f => by simp [φ]
  have hW : LinearMap.ker φ ≤ LinearMap.range (bd1 K L) := fun f hf =>
    IsSurface.mem_range_bd1_of_sum_eq_zero hS u₀ (by rw [← hφ]; exact hf)
  have hφs : LinearMap.range φ = ⊤ :=
    LinearMap.range_eq_top.mpr fun c => ⟨Pi.single u₀ c, by simp [hφ]⟩
  have r0 := LinearMap.finrank_range_add_finrank_ker φ
  have r1 := LinearMap.finrank_range_add_finrank_ker (bd1 K L)
  have r2 := LinearMap.finrank_range_add_finrank_ker (bd2 K L)
  rw [hφs, finrank_top, Module.finrank_self] at r0
  have k2 := hS.finrank_ker_bd2 (K := K) ⟨τ₀, hτ₀⟩
  have mW := Submodule.finrank_mono hW
  have m21 := Submodule.finrank_mono (LinearMap.range_le_ker_iff.mpr (bd1_bd2 (K := K) hS.card))
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at r0 r1 r2
  simp only [euler2]
  omega

/-- **The Euler characteristic of a closed surface is at most `2`.** -/
theorem IsSurface.euler_le {L : Finset (Finset V)} (hS : IsSurface L) : euler2 L ≤ 2 :=
  hS.euler_le_of_field (ZMod 2)

end Lightlike.Surfaces
