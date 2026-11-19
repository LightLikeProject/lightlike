import Lightlike.Gauge.DiracChart
import Lightlike.Gauge.DiracLocal

/-!
# Gluing the local charts of the Dirac algorithm

`final_consistent_of_cover` runs the algorithm with one selection rule whose chosen blocks are admissible on the whole
zero set of every stage (`hcover`). Constant rank (Wipf's lectures, arXiv:hep-th/9312078, Section 3.3, p. 17: "we
assume that the rank of `C` is constant on `Γ_c`") gives such a block only near each point
(`DiracLocal.exists_selection_near`). Here the algorithm is run in a finite atlas of charts, each with its own selection
rule admissible on its own open set, and the local surfaces are glued.

* `Stage.consistent_iff_of_zeroSet_inter_eq`, `zeroSet_stages_inter_eq`: for a first-order bracket, two stages with the
  same zero set near `x` have the same consistency condition at `x`, and two selection rules admissible on an open set
  give the same zero sets there at every stage;
* `zeroSet_anti`: the zero sets of the stages decrease;
* `DiracAtlas`, `DiracAtlas.surface`, `DiracAtlas.surface_inter`, `DiracAtlas.surface_zero`, `DiracAtlas.chart_succ`,
  `DiracAtlas.surface_succ`: the glued surfaces `Γₖ = ⋃_α (Γₖ^α ∩ U_α)` agree with every chart, start at the primary
  surface, and satisfy the chart-free recursion `Γₖ₊₁ = {x ∈ Γₖ | the consistency system of every chart at x is solvable}`;
* `DiracAtlas.chart_pause`, `DiracAtlas.chart_stable`: a step that leaves a chart's surface unchanged is final, so every
  chart stops changing by the stage `dim E + 1`;
* `DiracAtlas.ofSelection`, `DiracAtlas.surface_ofSelection`, `DiracAtlas.surface_eq`: a single selection rule admissible
  on every stage is the one-chart atlas, and the glued surfaces do not depend on the atlas;
* `Stage.consMat`, `selAt`, `selAt_admissible`, `ConstantRankAt`, `chartSet`, `chartSet_mem_nhds`,
  `DiracAtlas.ofConstantRank`, `final_consistent_of_constantRank`: the atlas from Wipf's constant-rank hypothesis, one chart
  at every point of the primary surface with the blocks chosen at that point;
* `DiracAtlas.final_consistent`: for any atlas the glued surfaces stop changing by the stage `dim E + 1`, and at every
  point of the final surface the consistency conditions `{S_i, H} + ∑_a {S_i, φ_a} u_a = 0` of each chart are solvable
  (Wipf, Section 3.3, pp. 16-17), with no single global selection.
-/

namespace Lightlike.Gauge

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {M : ℕ}

/-- **Consistency depends only on the zero set near the point**: for a first-order bracket, two regular stages whose
zero sets agree on a neighbourhood `V` of `x` have the same consistency condition at `x`. -/
theorem Stage.consistent_iff_of_zeroSet_inter_eq (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ)
    (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ) (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x))
    (S S' : Stage E) {V : Set E} {x : E} (hV : V ∈ 𝓝 x) (hZ : zeroSet S.Φ ∩ V = zeroSet S'.Φ ∩ V)
    (hx : x ∈ zeroSet S.Φ)
    (hS : ∀ i, HasStrictFDerivAt (S.Φ i) (fderiv ℝ (S.Φ i) x) x)
    (hS' : ∀ j, HasStrictFDerivAt (S'.Φ j) (fderiv ℝ (S'.Φ j) x) x)
    (hind : LinearIndependent ℝ fun i => fderiv ℝ (S.Φ i) x)
    (hind' : LinearIndependent ℝ fun j => fderiv ℝ (S'.Φ j) x) :
    S.Consistent br φ H x ↔ S'.Consistent br φ H x := by
  have hx' : x ∈ zeroSet S'.Φ := by
    have : x ∈ zeroSet S.Φ ∩ V := ⟨hx, mem_of_mem_nhds hV⟩
    rw [hZ] at this
    exact this.1
  have hker : ∀ v, (∀ i, fderiv ℝ (S.Φ i) x v = 0) ↔ ∀ j, fderiv ℝ (S'.Φ j) x v = 0 := fun v => by
    rw [← mem_tangentCone_zeroSet_iff hS hind hx v, ← mem_tangentCone_zeroSet_iff hS' hind' hx' v]
    show v ∈ tangentConeAt ℝ (zeroSet S.Φ) x ↔ v ∈ tangentConeAt ℝ (zeroSet S'.Φ) x
    rw [← tangentConeAt_inter_nhds hV, hZ, tangentConeAt_inter_nhds hV]
  let L : (Fin M → ℝ) → (E →L[ℝ] ℝ) →ₗ[ℝ] ℝ := fun u =>
    (LinearMap.proj (fderiv ℝ H x)).comp (B x) + ∑ a, u a • (LinearMap.proj (fderiv ℝ (φ a) x)).comp (B x)
  have hL : ∀ (T : Stage E) (u : Fin M → ℝ) (i : Fin T.n),
      br (T.Φ i) H x + ∑ a, br (T.Φ i) (φ a) x * u a = L u (fderiv ℝ (T.Φ i) x) := fun T u i => by
    simp only [L, hB, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, smul_eq_mul, mul_comm]
  have htransfer : ∀ (T T' : Stage E),
      (∀ v, (∀ i, fderiv ℝ (T.Φ i) x v = 0) → ∀ j, fderiv ℝ (T'.Φ j) x v = 0) →
        T.Consistent br φ H x → T'.Consistent br φ H x := fun T T' hk ⟨u, hu⟩ => by
    refine ⟨u, fun j => ?_⟩
    obtain ⟨c, hc⟩ := exists_coeff_of_ker (ξ := fun i => fderiv ℝ (T.Φ i) x) fun v hv => hk v hv j
    rw [hL, hc, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smul, ← hL, hu i, smul_zero]
  exact ⟨htransfer S S' fun v hv => (hker v).mp hv, htransfer S' S fun v hv => (hker v).mpr hv⟩

/-- **The surfaces of two charts agree on their overlap**: for a first-order bracket and two selection rules admissible
on the zero sets of their stages inside an open set `V`, with the stages regular and strictly differentiable there, every
stage has the same zero set inside `V`. -/
theorem zeroSet_stages_inter_eq (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ)
    (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ) (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x))
    (sel sel' : ∀ S : Stage E, Sel S M) (S₀ : Stage E) {V : Set E} (hVo : IsOpen V) (m : ℕ)
    (hreg : ∀ k < m, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ ∩ V,
      LinearIndependent ℝ fun i => fderiv ℝ ((stages br φ H sel S₀ k).Φ i) x)
    (hreg' : ∀ k < m, ∀ x ∈ zeroSet (stages br φ H sel' S₀ k).Φ ∩ V,
      LinearIndependent ℝ fun i => fderiv ℝ ((stages br φ H sel' S₀ k).Φ i) x)
    (hdiff : ∀ k < m, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ ∩ V, ∀ i,
      HasStrictFDerivAt ((stages br φ H sel S₀ k).Φ i) (fderiv ℝ ((stages br φ H sel S₀ k).Φ i) x) x)
    (hdiff' : ∀ k < m, ∀ x ∈ zeroSet (stages br φ H sel' S₀ k).Φ ∩ V, ∀ i,
      HasStrictFDerivAt ((stages br φ H sel' S₀ k).Φ i) (fderiv ℝ ((stages br φ H sel' S₀ k).Φ i) x) x)
    (hadm : ∀ k < m, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ ∩ V,
      (sel (stages br φ H sel S₀ k)).Admissible br φ x)
    (hadm' : ∀ k < m, ∀ x ∈ zeroSet (stages br φ H sel' S₀ k).Φ ∩ V,
      (sel' (stages br φ H sel' S₀ k)).Admissible br φ x) :
    ∀ k ≤ m, zeroSet (stages br φ H sel S₀ k).Φ ∩ V = zeroSet (stages br φ H sel' S₀ k).Φ ∩ V := by
  intro k hkm
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : k < m := by omega
    have ih := ih (by omega)
    show zeroSet (appendStage (stages br φ H sel S₀ k).Φ
        ((stages br φ H sel S₀ k).chiFun br φ H (sel (stages br φ H sel S₀ k)))) ∩ V =
      zeroSet (appendStage (stages br φ H sel' S₀ k).Φ
        ((stages br φ H sel' S₀ k).chiFun br φ H (sel' (stages br φ H sel' S₀ k)))) ∩ V
    rw [zeroSet_appendStage, zeroSet_appendStage]
    ext x
    simp only [Set.mem_inter_iff]
    have hiff : ∀ hxV : x ∈ V, x ∈ zeroSet (stages br φ H sel S₀ k).Φ →
        x ∈ zeroSet (stages br φ H sel' S₀ k).Φ ∧
          ((stages br φ H sel S₀ k).Consistent br φ H x ↔ (stages br φ H sel' S₀ k).Consistent br φ H x) :=
      fun hxV hx => by
        have hx' : x ∈ zeroSet (stages br φ H sel' S₀ k).Φ := by
          have : x ∈ zeroSet (stages br φ H sel S₀ k).Φ ∩ V := ⟨hx, hxV⟩
          rw [ih] at this
          exact this.1
        exact ⟨hx', (stages br φ H sel S₀ k).consistent_iff_of_zeroSet_inter_eq br φ H B hB _
          (hVo.mem_nhds hxV) ih hx (hdiff k hk x ⟨hx, hxV⟩) (hdiff' k hk x ⟨hx', hxV⟩) (hreg k hk x ⟨hx, hxV⟩)
          (hreg' k hk x ⟨hx', hxV⟩)⟩
    constructor
    · rintro ⟨⟨hx, hχ⟩, hxV⟩
      obtain ⟨hx', hc⟩ := hiff hxV hx
      refine ⟨⟨hx', ?_⟩, hxV⟩
      have h1 := ((stages br φ H sel S₀ k).chiFun_zero_iff br φ H (hadm k hk x ⟨hx, hxV⟩)).mp hχ
      exact ((stages br φ H sel' S₀ k).chiFun_zero_iff br φ H (hadm' k hk x ⟨hx', hxV⟩)).mpr (hc.mp h1)
    · rintro ⟨⟨hx', hχ⟩, hxV⟩
      have hx : x ∈ zeroSet (stages br φ H sel S₀ k).Φ := by
        have : x ∈ zeroSet (stages br φ H sel' S₀ k).Φ ∩ V := ⟨hx', hxV⟩
        rw [← ih] at this
        exact this.1
      obtain ⟨-, hc⟩ := hiff hxV hx
      refine ⟨⟨hx, ?_⟩, hxV⟩
      have h1 := ((stages br φ H sel' S₀ k).chiFun_zero_iff br φ H (hadm' k hk x ⟨hx', hxV⟩)).mp hχ
      exact ((stages br φ H sel S₀ k).chiFun_zero_iff br φ H (hadm k hk x ⟨hx, hxV⟩)).mpr (hc.mpr h1)

/-- **The zero sets of the stages decrease.** -/
theorem zeroSet_anti (n : ℕ → ℕ) (Φ : ∀ k, Fin (n k) → E → ℝ) (hmono : ∀ k, n k ≤ n (k + 1))
    (hext : ∀ k i, Φ (k + 1) (Fin.castLE (hmono k) i) = Φ k i) {k k' : ℕ} (hk : k ≤ k') :
    zeroSet (Φ k') ⊆ zeroSet (Φ k) := by
  induction k', hk using Nat.le_induction with
  | base => exact le_rfl
  | succ k' hk ih =>
    refine fun x hx => ih fun i => ?_
    rw [← hext k' i]
    exact hx _

/-- **An atlas for the Dirac algorithm up to the stage `K`**: open sets `U α` covering the primary surface, each with its
own selection rule, whose stages `k ≤ K` are regular, strictly differentiable and admissible at the points of their zero
sets inside `U α` (what the constant-rank hypothesis gives near each point, `DiracAtlas.ofConstantRank`). -/
structure DiracAtlas (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ) (S₀ : Stage E)
    (A : Type*) (K : ℕ) where
  /-- The chart domains. -/
  U : A → Set E
  /-- The chart domains are open. -/
  isOpen : ∀ α, IsOpen (U α)
  /-- The selection rule of each chart. -/
  sel : A → ∀ S : Stage E, Sel S M
  /-- The stages of each chart are regular inside its domain. -/
  reg : ∀ α, ∀ k ≤ K, ∀ x ∈ zeroSet (stages br φ H (sel α) S₀ k).Φ ∩ U α,
    LinearIndependent ℝ fun i => fderiv ℝ ((stages br φ H (sel α) S₀ k).Φ i) x
  /-- The stages of each chart are strictly differentiable inside its domain. -/
  diff : ∀ α, ∀ k ≤ K, ∀ x ∈ zeroSet (stages br φ H (sel α) S₀ k).Φ ∩ U α, ∀ i,
    HasStrictFDerivAt ((stages br φ H (sel α) S₀ k).Φ i) (fderiv ℝ ((stages br φ H (sel α) S₀ k).Φ i) x) x
  /-- The selected blocks of each chart are admissible inside its domain. -/
  adm : ∀ α, ∀ k ≤ K, ∀ x ∈ zeroSet (stages br φ H (sel α) S₀ k).Φ ∩ U α,
    (sel α (stages br φ H (sel α) S₀ k)).Admissible br φ x
  /-- The chart domains cover the primary surface. -/
  cover : zeroSet S₀.Φ ⊆ ⋃ α, U α

namespace DiracAtlas

variable {br : (E → ℝ) → (E → ℝ) → E → ℝ} {φ : Fin M → E → ℝ} {H : E → ℝ} {S₀ : Stage E} {A : Type*} {K : ℕ}

/-- **The glued surfaces** `Γₖ = ⋃_α (Γₖ^α ∩ U_α)`. -/
def surface (𝒜 : DiracAtlas br φ H S₀ A K) (k : ℕ) : Set E :=
  ⋃ α, zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α

/-- **The glued surface agrees with every chart**: `Γₖ ∩ U_α = Γₖ^α ∩ U_α`. -/
theorem surface_inter (𝒜 : DiracAtlas br φ H S₀ A K) (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ)
    (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x)) (α : A) {k : ℕ} (hk : k ≤ K + 1) :
    𝒜.surface k ∩ 𝒜.U α = zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α := by
  ext x
  constructor
  · rintro ⟨hx, hxα⟩
    obtain ⟨β, hxβ, hβ⟩ := Set.mem_iUnion.mp hx
    have hV : IsOpen (𝒜.U β ∩ 𝒜.U α) := (𝒜.isOpen β).inter (𝒜.isOpen α)
    have heq := zeroSet_stages_inter_eq br φ H B hB (𝒜.sel β) (𝒜.sel α) S₀ hV k
      (fun j hj x hx => 𝒜.reg β j (by omega) x ⟨hx.1, hx.2.1⟩)
      (fun j hj x hx => 𝒜.reg α j (by omega) x ⟨hx.1, hx.2.2⟩)
      (fun j hj x hx => 𝒜.diff β j (by omega) x ⟨hx.1, hx.2.1⟩)
      (fun j hj x hx => 𝒜.diff α j (by omega) x ⟨hx.1, hx.2.2⟩)
      (fun j hj x hx => 𝒜.adm β j (by omega) x ⟨hx.1, hx.2.1⟩)
      (fun j hj x hx => 𝒜.adm α j (by omega) x ⟨hx.1, hx.2.2⟩) k le_rfl
    have : x ∈ zeroSet (stages br φ H (𝒜.sel β) S₀ k).Φ ∩ (𝒜.U β ∩ 𝒜.U α) := ⟨hxβ, hβ, hxα⟩
    rw [heq] at this
    exact ⟨this.1, hxα⟩
  · rintro ⟨hx, hxα⟩
    exact ⟨Set.mem_iUnion.mpr ⟨α, hx, hxα⟩, hxα⟩

/-- **The glued surfaces start at the primary surface.** -/
theorem surface_zero (𝒜 : DiracAtlas br φ H S₀ A K) : 𝒜.surface 0 = zeroSet S₀.Φ := by
  ext x
  constructor
  · intro hx
    obtain ⟨α, hxα, -⟩ := Set.mem_iUnion.mp hx
    exact hxα
  · intro hx
    obtain ⟨α, hα⟩ := Set.mem_iUnion.mp (𝒜.cover hx)
    exact Set.mem_iUnion.mpr ⟨α, hx, hα⟩

/-- **One step in one chart**: the next surface of a chart is the set of points of its surface at which its consistency
system is solvable. -/
theorem chart_succ (𝒜 : DiracAtlas br φ H S₀ A K) (α : A) {k : ℕ} (hk : k ≤ K) :
    zeroSet (stages br φ H (𝒜.sel α) S₀ (k + 1)).Φ ∩ 𝒜.U α =
      {x | x ∈ zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α ∧
        (stages br φ H (𝒜.sel α) S₀ k).Consistent br φ H x} := by
  ext x
  show x ∈ zeroSet (appendStage (stages br φ H (𝒜.sel α) S₀ k).Φ
      ((stages br φ H (𝒜.sel α) S₀ k).chiFun br φ H (𝒜.sel α (stages br φ H (𝒜.sel α) S₀ k)))) ∩ 𝒜.U α ↔ _
  rw [zeroSet_appendStage]
  constructor
  · rintro ⟨⟨hx, hχ⟩, hxα⟩
    exact ⟨⟨hx, hxα⟩,
      ((stages br φ H (𝒜.sel α) S₀ k).chiFun_zero_iff br φ H (𝒜.adm α k hk x ⟨hx, hxα⟩)).mp hχ⟩
  · rintro ⟨⟨hx, hxα⟩, hc⟩
    exact ⟨⟨hx, ((stages br φ H (𝒜.sel α) S₀ k).chiFun_zero_iff br φ H (𝒜.adm α k hk x ⟨hx, hxα⟩)).mpr hc⟩,
      hxα⟩

/-- **The chart-free recursion**: `Γₖ₊₁` is the set of points of `Γₖ` at which the consistency system of every chart
containing the point is solvable. -/
theorem surface_succ (𝒜 : DiracAtlas br φ H S₀ A K) (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ)
    (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x)) {k : ℕ} (hk : k ≤ K) :
    𝒜.surface (k + 1) =
      {x | x ∈ 𝒜.surface k ∧ ∀ α, x ∈ 𝒜.U α → (stages br φ H (𝒜.sel α) S₀ k).Consistent br φ H x} := by
  have hstep := fun α => 𝒜.chart_succ α hk
  ext x
  constructor
  · intro hx
    obtain ⟨β, hxβ⟩ := Set.mem_iUnion.mp hx
    rw [hstep β] at hxβ
    refine ⟨Set.mem_iUnion.mpr ⟨β, hxβ.1⟩, fun α hxα => ?_⟩
    have h1 : x ∈ 𝒜.surface (k + 1) ∩ 𝒜.U α := ⟨hx, hxα⟩
    rw [𝒜.surface_inter B hB α (by omega), hstep α] at h1
    exact h1.2
  · rintro ⟨hx, hc⟩
    obtain ⟨α, hxα⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨α, ?_⟩
    rw [hstep α]
    exact ⟨hxα, hc α hxα.2⟩

/-- **A pause is final**: if the surface of a chart does not change at one step, it does not change at the next either
(its consistency condition depends only on the surface, `Stage.consistent_iff_of_zeroSet_inter_eq`). -/
theorem chart_pause (𝒜 : DiracAtlas br φ H S₀ A K) (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ)
    (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x)) (α : A) {k : ℕ} (hk1 : k + 1 ≤ K)
    (hk : zeroSet (stages br φ H (𝒜.sel α) S₀ (k + 1)).Φ ∩ 𝒜.U α = zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α) :
    zeroSet (stages br φ H (𝒜.sel α) S₀ (k + 2)).Φ ∩ 𝒜.U α =
      zeroSet (stages br φ H (𝒜.sel α) S₀ (k + 1)).Φ ∩ 𝒜.U α := by
  rw [𝒜.chart_succ α hk1]
  ext x
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
  have hxk : x ∈ zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α := hk ▸ hx
  have hck : (stages br φ H (𝒜.sel α) S₀ k).Consistent br φ H x := by
    have := hx
    rw [𝒜.chart_succ α (by omega : k ≤ K)] at this
    exact this.2
  exact ((stages br φ H (𝒜.sel α) S₀ (k + 1)).consistent_iff_of_zeroSet_inter_eq br φ H B hB _
    ((𝒜.isOpen α).mem_nhds hx.2) hk hx.1 (𝒜.diff α (k + 1) hk1 x hx) (𝒜.diff α k (by omega) x hxk)
    (𝒜.reg α (k + 1) hk1 x hx) (𝒜.reg α k (by omega) x hxk)).mpr hck

/-- **Every chart stops changing by the stage `dim E + 1`**: a step that changes the surface adds constraints, and a
regular stage with a point has at most `dim E` of them. -/
theorem chart_stable (𝒜 : DiracAtlas br φ H S₀ A K) (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ)
    (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x)) (hK : Module.finrank ℝ E + 1 ≤ K) (α : A) :
    ∀ k, Module.finrank ℝ E + 1 ≤ k → k ≤ K + 1 → zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α =
      zeroSet (stages br φ H (𝒜.sel α) S₀ (Module.finrank ℝ E + 1)).Φ ∩ 𝒜.U α := by
  set N := Module.finrank ℝ E + 1 with hNdef
  set Z : ℕ → Set E := fun k => zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α with hZ
  set n : ℕ → ℕ := fun k => (stages br φ H (𝒜.sel α) S₀ k).n with hn
  have hmono : ∀ k, n k ≤ n (k + 1) := fun k => Nat.le_add_right _ _
  have hext : ∀ k i, (stages br φ H (𝒜.sel α) S₀ (k + 1)).Φ (Fin.castLE (hmono k) i) =
      (stages br φ H (𝒜.sel α) S₀ k).Φ i := fun k i =>
    appendStage_castLE (stages br φ H (𝒜.sel α) S₀ k).Φ
      ((stages br φ H (𝒜.sel α) S₀ k).chiFun br φ H (𝒜.sel α (stages br φ H (𝒜.sel α) S₀ k))) i
  have hanti : ∀ {k k'}, k ≤ k' → Z k' ⊆ Z k := fun hk x hx =>
    ⟨zeroSet_anti n (fun k => (stages br φ H (𝒜.sel α) S₀ k).Φ) hmono hext hk hx.1, hx.2⟩
  intro k hk hkK
  by_cases hp : ∃ j < N, Z (j + 1) = Z j
  · obtain ⟨j, hjN, hj⟩ := hp
    have hall : ∀ m, j ≤ m → m ≤ K → Z (m + 1) = Z m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact fun _ => hj
      | succ m hm ih => exact fun h => 𝒜.chart_pause B hB α h (ih (by omega))
    have hconst : ∀ m, j ≤ m → m ≤ K + 1 → Z m = Z j := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact fun _ => rfl
      | succ m hm ih => exact fun h => by rw [hall m hm (by omega), ih (by omega)]
    show Z k = Z N
    rw [hconst k (by omega) hkK, hconst N hjN.le (by omega)]
  · push_neg at hp
    have hcount : ∀ j, j ≤ N → j ≤ n j := fun j hj => by
      induction j with
      | zero => exact Nat.zero_le _
      | succ j ih =>
        have hlt : n j < n (j + 1) := by
          by_contra hle
          have heq : n j = n (j + 1) := le_antisymm (hmono j) (not_lt.mp hle)
          apply hp j (by omega)
          show zeroSet (stages br φ H (𝒜.sel α) S₀ (j + 1)).Φ ∩ 𝒜.U α =
            zeroSet (stages br φ H (𝒜.sel α) S₀ j).Φ ∩ 𝒜.U α
          rw [zeroSet_eq_of_card_eq (stages br φ H (𝒜.sel α) S₀ j).Φ (stages br φ H (𝒜.sel α) S₀ (j + 1)).Φ
            (hmono j) (hext j) heq]
        have := ih (by omega)
        omega
    have hempty : Z N = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have h1 := LinearIndependent.fintype_card_le_finrank (𝒜.reg α N hK x hx)
      have h2 : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
        rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ))]
        exact Subspace.dual_finrank_eq
      have h3 : n N ≤ Module.finrank ℝ E := by simpa [h2] using h1
      have h4 := hcount N le_rfl
      omega
    show Z k = Z N
    rw [hempty]
    exact Set.subset_empty_iff.mp (hempty ▸ hanti hk)

/-- **The Dirac algorithm in an atlas** (Wipf, Section 3.3, pp. 16-17, with the constant-rank blocks chosen chart by
chart): with the charts valid up to a stage `K ≥ dim E + 1`, the glued surfaces stop changing at the stage
`N = dim E + 1` (`Γₖ = Γ_N` for `N ≤ k ≤ K + 1`), and at every point of `Γ_N` the consistency conditions
`{S_i, H} + ∑_a {S_i, φ_a} u_a = 0` of every chart containing the point are solvable. -/
theorem final_consistent (𝒜 : DiracAtlas br φ H S₀ A K)
    (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ) (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x))
    (hK : Module.finrank ℝ E + 1 ≤ K) :
    (∀ k, Module.finrank ℝ E + 1 ≤ k → k ≤ K + 1 → 𝒜.surface k = 𝒜.surface (Module.finrank ℝ E + 1)) ∧
      ∀ x ∈ 𝒜.surface (Module.finrank ℝ E + 1), ∀ α, x ∈ 𝒜.U α →
        (stages br φ H (𝒜.sel α) S₀ (Module.finrank ℝ E + 1)).Consistent br φ H x := by
  have hstab : ∀ k, Module.finrank ℝ E + 1 ≤ k → k ≤ K + 1 →
      𝒜.surface k = 𝒜.surface (Module.finrank ℝ E + 1) := fun k hk hkK => by
    simp only [surface]
    exact Set.iUnion_congr fun α => 𝒜.chart_stable B hB hK α k hk hkK
  refine ⟨hstab, fun x hx α hxα => ?_⟩
  have h1 : x ∈ 𝒜.surface (Module.finrank ℝ E + 1 + 1) := by
    rw [hstab _ (by omega) (by omega)]
    exact hx
  rw [𝒜.surface_succ B hB hK] at h1
  exact h1.2 α hxα

/-- **The one-chart atlas** of a single selection rule admissible on the whole zero set of every stage (the situation of
`final_consistent_of_cover`). -/
def ofSelection (K : ℕ) (sel : ∀ S : Stage E, Sel S M) (hreg : ∀ k, IsRegularStage (stages br φ H sel S₀ k).Φ)
    (hdiff : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ, ∀ i,
      HasStrictFDerivAt ((stages br φ H sel S₀ k).Φ i) (fderiv ℝ ((stages br φ H sel S₀ k).Φ i) x) x)
    (hadm : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ, (sel (stages br φ H sel S₀ k)).Admissible br φ x) :
    DiracAtlas br φ H S₀ Unit K where
  U _ := Set.univ
  isOpen _ := isOpen_univ
  sel _ := sel
  reg _ k _ x hx := hreg k x hx.1
  diff _ k _ x hx := hdiff k x hx.1
  adm _ k _ x hx := hadm k x hx.1
  cover _ _ := Set.mem_iUnion.mpr ⟨(), Set.mem_univ _⟩

/-- The glued surfaces of the one-chart atlas are the zero sets of the stages. -/
theorem surface_ofSelection (K : ℕ) (sel : ∀ S : Stage E, Sel S M)
    (hreg : ∀ k, IsRegularStage (stages br φ H sel S₀ k).Φ)
    (hdiff : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ, ∀ i,
      HasStrictFDerivAt ((stages br φ H sel S₀ k).Φ i) (fderiv ℝ ((stages br φ H sel S₀ k).Φ i) x) x)
    (hadm : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ, (sel (stages br φ H sel S₀ k)).Admissible br φ x) (k : ℕ) :
    (ofSelection K sel hreg hdiff hadm).surface k = zeroSet (stages br φ H sel S₀ k).Φ := by
  ext x
  simp [surface, ofSelection]

/-- **The glued surfaces do not depend on the atlas**: two atlases of the same algorithm have the same glued surfaces. -/
theorem surface_eq (𝒜 𝒜' : DiracAtlas br φ H S₀ A K) (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ)
    (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x)) {k : ℕ} (hk : k ≤ K + 1) :
    𝒜.surface k = 𝒜'.surface k := by
  have key : ∀ 𝒜₁ 𝒜₂ : DiracAtlas br φ H S₀ A K, 𝒜₁.surface k ⊆ 𝒜₂.surface k := fun 𝒜₁ 𝒜₂ x hx => by
    obtain ⟨α, hxα, hα⟩ := Set.mem_iUnion.mp hx
    have hx0 : x ∈ zeroSet S₀.Φ := zeroSet_anti (fun j => (stages br φ H (𝒜₁.sel α) S₀ j).n)
      (fun j => (stages br φ H (𝒜₁.sel α) S₀ j).Φ) (fun j => Nat.le_add_right _ _)
      (fun j i => appendStage_castLE (stages br φ H (𝒜₁.sel α) S₀ j).Φ
        ((stages br φ H (𝒜₁.sel α) S₀ j).chiFun br φ H (𝒜₁.sel α (stages br φ H (𝒜₁.sel α) S₀ j))) i)
      (Nat.zero_le k) hxα
    obtain ⟨β, hβ⟩ := Set.mem_iUnion.mp (𝒜₂.cover hx0)
    have hV : IsOpen (𝒜₁.U α ∩ 𝒜₂.U β) := (𝒜₁.isOpen α).inter (𝒜₂.isOpen β)
    have heq := zeroSet_stages_inter_eq br φ H B hB (𝒜₁.sel α) (𝒜₂.sel β) S₀ hV k
      (fun j hj y hy => 𝒜₁.reg α j (by omega) y ⟨hy.1, hy.2.1⟩)
      (fun j hj y hy => 𝒜₂.reg β j (by omega) y ⟨hy.1, hy.2.2⟩)
      (fun j hj y hy => 𝒜₁.diff α j (by omega) y ⟨hy.1, hy.2.1⟩)
      (fun j hj y hy => 𝒜₂.diff β j (by omega) y ⟨hy.1, hy.2.2⟩)
      (fun j hj y hy => 𝒜₁.adm α j (by omega) y ⟨hy.1, hy.2.1⟩)
      (fun j hj y hy => 𝒜₂.adm β j (by omega) y ⟨hy.1, hy.2.2⟩) k le_rfl
    have : x ∈ zeroSet (stages br φ H (𝒜₁.sel α) S₀ k).Φ ∩ (𝒜₁.U α ∩ 𝒜₂.U β) := ⟨hxα, hα, hβ⟩
    rw [heq] at this
    exact Set.mem_iUnion.mpr ⟨β, this.1, hβ⟩
  exact (key 𝒜 𝒜').antisymm (key 𝒜' 𝒜)

end DiracAtlas

section ConstantRank

open Matrix

/-- The consistency matrix `({S_i, φ_a}(x))` of a stage. -/
def Stage.consMat (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (S : Stage E) (x : E) :
    Matrix (Fin S.n) (Fin M) ℝ :=
  Matrix.of fun i a => br (S.Φ i) (φ a) x

/-- **The selection adapted to `x₀`**: the rows and columns of a nonzero minor of maximal size of the consistency matrix
at `x₀` (`exists_isUnit_det_submatrix`). -/
noncomputable def selAt (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (x₀ : E) (S : Stage E) : Sel S M :=
  Sel.ofMinor (exists_isUnit_det_submatrix (S.consMat br φ x₀)).choose
    (exists_isUnit_det_submatrix (S.consMat br φ x₀)).choose_spec.choose
    (exists_isUnit_det_submatrix (S.consMat br φ x₀)).choose_spec.choose_spec.1
    (exists_isUnit_det_submatrix (S.consMat br φ x₀)).choose_spec.choose_spec.2.1

set_option maxHeartbeats 1000000 in
/-- **The selection adapted to `x₀` is admissible near `x₀`** at the points of a set `Z` where the rank of the consistency
matrix is the rank at `x₀`, if its entries are continuous at `x₀` (the constant-rank hypothesis on the surface `Z`). -/
theorem selAt_admissible (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (S : Stage E) {x₀ : E} (Z : Set E)
    (hcont : ∀ i a, ContinuousAt (fun x => br (S.Φ i) (φ a) x) x₀)
    (hrank : ∀ᶠ x in 𝓝 x₀, x ∈ Z → (S.consMat br φ x).rank = (S.consMat br φ x₀).rank) :
    ∀ᶠ x in 𝓝 x₀, x ∈ Z → (selAt br φ x₀ S).Admissible br φ x := by
  obtain ⟨hR, hC, hunit⟩ := (exists_isUnit_det_submatrix (S.consMat br φ x₀)).choose_spec.choose_spec
  have hB : ∀ x, (S.consCm br φ (selAt br φ x₀ S) x).toBlocks₁₁ =
      (S.consMat br φ x).submatrix (exists_isUnit_det_submatrix (S.consMat br φ x₀)).choose
        (exists_isUnit_det_submatrix (S.consMat br φ x₀)).choose_spec.choose := fun x =>
    (Sel.ofMinor_block _ _ hR hC br φ x).trans (Matrix.ext fun _ _ => rfl)
  have hinv : ∀ᶠ x in 𝓝 x₀, IsUnit (S.consCm br φ (selAt br φ x₀ S) x).toBlocks₁₁.det := by
    refine eventually_isUnit_det (B := fun x => (S.consCm br φ (selAt br φ x₀ S) x).toBlocks₁₁) (fun i j => ?_) ?_
    · simp only [hB, Matrix.submatrix_apply]
      exact hcont _ _
    · show IsUnit (S.consCm br φ (selAt br φ x₀ S) x₀).toBlocks₁₁.det
      rw [hB]
      exact hunit
  filter_upwards [hinv, hrank] with x hx hxr hxZ
  refine ⟨hx, ?_⟩
  have hrk : (S.consCm br φ (selAt br φ x₀ S) x).rank = (S.consMat br φ x₀).rank := by
    rw [Stage.consCm_eq_reindex, Matrix.rank_reindex]
    exact hxr hxZ
  have hle0 : (S.consCm br φ (selAt br φ x₀ S) x).rank ≤ Fintype.card (Fin (selAt br φ x₀ S).r) := by
    rw [hrk, Fintype.card_fin]
    exact le_rfl
  have hfb := fromBlocks_toBlocks (S.consCm br φ (selAt br φ x₀ S) x)
  exact schur_eq_zero_of_rank_le_block (S.consCm br φ (selAt br φ x₀ S) x).toBlocks₁₁
    (S.consCm br φ (selAt br φ x₀ S) x).toBlocks₁₂ (S.consCm br φ (selAt br φ x₀ S) x).toBlocks₂₁
    (S.consCm br φ (selAt br φ x₀ S) x).toBlocks₂₂ hx (by rw [hfb]; exact hle0)

/-- **Wipf's constant-rank hypothesis at `x₀`, up to the stage `K`**, for the algorithm run with the blocks chosen at `x₀`:
at every stage `k ≤ K` the constraint functions are continuous at `x₀`, and if `x₀` lies on the `k`-th surface, the
entries of the consistency matrix are continuous at `x₀`, its rank on the surface near `x₀` is the rank at `x₀`
(Wipf, Section 3.3, p. 17: "we assume that the rank of `C` is constant"), and the stage is regular and strictly
differentiable at the points of the surface near `x₀`. -/
def ConstantRankAt (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ) (S₀ : Stage E) (K : ℕ)
    (x₀ : E) : Prop :=
  ∀ k ≤ K, (∀ i, ContinuousAt ((stages br φ H (selAt br φ x₀) S₀ k).Φ i) x₀) ∧
    (x₀ ∈ zeroSet (stages br φ H (selAt br φ x₀) S₀ k).Φ →
      (∀ i a, ContinuousAt (fun x => br ((stages br φ H (selAt br φ x₀) S₀ k).Φ i) (φ a) x) x₀) ∧
      (∀ᶠ x in 𝓝 x₀, x ∈ zeroSet (stages br φ H (selAt br φ x₀) S₀ k).Φ →
        ((stages br φ H (selAt br φ x₀) S₀ k).consMat br φ x).rank =
          ((stages br φ H (selAt br φ x₀) S₀ k).consMat br φ x₀).rank) ∧
      (∀ᶠ x in 𝓝 x₀, x ∈ zeroSet (stages br φ H (selAt br φ x₀) S₀ k).Φ →
        (LinearIndependent ℝ fun i => fderiv ℝ ((stages br φ H (selAt br φ x₀) S₀ k).Φ i) x) ∧
          ∀ i, HasStrictFDerivAt ((stages br φ H (selAt br φ x₀) S₀ k).Φ i)
            (fderiv ℝ ((stages br φ H (selAt br φ x₀) S₀ k).Φ i) x) x))

/-- The points near `x₀` where the chart at `x₀` works at every stage `k ≤ K`. -/
def chartSet (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ) (S₀ : Stage E) (K : ℕ) (x₀ : E) :
    Set E :=
  {x | ∀ k ≤ K, x ∈ zeroSet (stages br φ H (selAt br φ x₀) S₀ k).Φ →
    (selAt br φ x₀ (stages br φ H (selAt br φ x₀) S₀ k)).Admissible br φ x ∧
      (LinearIndependent ℝ fun i => fderiv ℝ ((stages br φ H (selAt br φ x₀) S₀ k).Φ i) x) ∧
        ∀ i, HasStrictFDerivAt ((stages br φ H (selAt br φ x₀) S₀ k).Φ i)
          (fderiv ℝ ((stages br φ H (selAt br φ x₀) S₀ k).Φ i) x) x}

/-- **The chart at `x₀` is a neighbourhood of `x₀`** under the constant-rank hypothesis at `x₀`. -/
theorem chartSet_mem_nhds {br : (E → ℝ) → (E → ℝ) → E → ℝ} {φ : Fin M → E → ℝ} {H : E → ℝ} {S₀ : Stage E} {K : ℕ}
    {x₀ : E} (h : ConstantRankAt br φ H S₀ K x₀) : chartSet br φ H S₀ K x₀ ∈ 𝓝 x₀ := by
  have hk : ∀ k ∈ Set.Iic K, ∀ᶠ x in 𝓝 x₀, x ∈ zeroSet (stages br φ H (selAt br φ x₀) S₀ k).Φ →
      (selAt br φ x₀ (stages br φ H (selAt br φ x₀) S₀ k)).Admissible br φ x ∧
        (LinearIndependent ℝ fun i => fderiv ℝ ((stages br φ H (selAt br φ x₀) S₀ k).Φ i) x) ∧
          ∀ i, HasStrictFDerivAt ((stages br φ H (selAt br φ x₀) S₀ k).Φ i)
            (fderiv ℝ ((stages br φ H (selAt br φ x₀) S₀ k).Φ i) x) x := fun k hk => by
    obtain ⟨hΦ, hsurf⟩ := h k hk
    by_cases hx₀ : x₀ ∈ zeroSet (stages br φ H (selAt br φ x₀) S₀ k).Φ
    · obtain ⟨hcont, hrank, hreg⟩ := hsurf hx₀
      filter_upwards [selAt_admissible br φ _ _ hcont hrank, hreg] with x hadm hrd hxZ
      exact ⟨hadm hxZ, hrd hxZ⟩
    · obtain ⟨i, hi⟩ : ∃ i, (stages br φ H (selAt br φ x₀) S₀ k).Φ i x₀ ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hx₀ hall
      filter_upwards [(hΦ i).eventually_ne hi] with x hx hxZ
      exact absurd (hxZ i) hx
  have := (Filter.eventually_all_finite (Set.finite_Iic K)).mpr hk
  filter_upwards [this] with x hx k hkK
  exact hx k (Set.mem_Iic.mpr hkK)

/-- **The atlas from the constant-rank hypothesis**: one chart at every point `x₀` of the primary surface, with the blocks
chosen at `x₀` and the interior of `chartSet` as its domain. -/
noncomputable def DiracAtlas.ofConstantRank (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ)
    (S₀ : Stage E) (K : ℕ) (h : ∀ x₀ ∈ zeroSet S₀.Φ, ConstantRankAt br φ H S₀ K x₀) :
    DiracAtlas br φ H S₀ (zeroSet S₀.Φ) K where
  U x₀ := interior (chartSet br φ H S₀ K x₀.1)
  isOpen _ := isOpen_interior
  sel x₀ := selAt br φ x₀.1
  reg x₀ k hk x hx := ((interior_subset hx.2 : x ∈ chartSet br φ H S₀ K x₀.1) k hk hx.1).2.1
  diff x₀ k hk x hx := ((interior_subset hx.2 : x ∈ chartSet br φ H S₀ K x₀.1) k hk hx.1).2.2
  adm x₀ k hk x hx := ((interior_subset hx.2 : x ∈ chartSet br φ H S₀ K x₀.1) k hk hx.1).1
  cover x₀ hx₀ := Set.mem_iUnion.mpr ⟨⟨x₀, hx₀⟩, mem_interior_iff_mem_nhds.mpr (chartSet_mem_nhds (h x₀ hx₀))⟩

/-- **The Dirac algorithm under Wipf's constant-rank hypothesis** (Section 3.3, pp. 16-17), with no global selection: if
the constant-rank hypothesis holds at every point of the primary surface up to a stage `K ≥ dim E + 1`, the glued
surfaces of the charts with blocks chosen pointwise stop changing at `N = dim E + 1`, and at every point `x` of `Γ_N` the
consistency conditions `{S_i, H} + ∑_a {S_i, φ_a} u_a = 0` of every chart containing `x` are solvable. The glued
surfaces do not depend on the atlas (`DiracAtlas.surface_eq`). -/
theorem final_consistent_of_constantRank (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ)
    (S₀ : Stage E) (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ)
    (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x)) {K : ℕ} (hK : Module.finrank ℝ E + 1 ≤ K)
    (h : ∀ x₀ ∈ zeroSet S₀.Φ, ConstantRankAt br φ H S₀ K x₀) :
    (∀ k, Module.finrank ℝ E + 1 ≤ k → k ≤ K + 1 → (DiracAtlas.ofConstantRank br φ H S₀ K h).surface k =
      (DiracAtlas.ofConstantRank br φ H S₀ K h).surface (Module.finrank ℝ E + 1)) ∧
      ∀ x ∈ (DiracAtlas.ofConstantRank br φ H S₀ K h).surface (Module.finrank ℝ E + 1),
        ∀ x₀ (hx₀ : x₀ ∈ zeroSet S₀.Φ), x ∈ interior (chartSet br φ H S₀ K x₀) →
          (stages br φ H (selAt br φ x₀) S₀ (Module.finrank ℝ E + 1)).Consistent br φ H x := by
  obtain ⟨h1, h2⟩ := (DiracAtlas.ofConstantRank br φ H S₀ K h).final_consistent B hB hK
  exact ⟨h1, fun x hx x₀ hx₀ hxU => h2 x hx ⟨x₀, hx₀⟩ hxU⟩

end ConstantRank

end Lightlike.Gauge
