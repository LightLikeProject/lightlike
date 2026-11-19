import Lightlike.Gauge.DiracChart

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
* `DiracAtlas.ofSelection`, `DiracAtlas.surface_ofSelection`: a single selection rule admissible on every stage is the
  one-chart atlas;
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
    (sel sel' : ∀ S : Stage E, Sel S M) (S₀ : Stage E) {V : Set E} (hVo : IsOpen V)
    (hreg : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ ∩ V,
      LinearIndependent ℝ fun i => fderiv ℝ ((stages br φ H sel S₀ k).Φ i) x)
    (hreg' : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel' S₀ k).Φ ∩ V,
      LinearIndependent ℝ fun i => fderiv ℝ ((stages br φ H sel' S₀ k).Φ i) x)
    (hdiff : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ ∩ V, ∀ i,
      HasStrictFDerivAt ((stages br φ H sel S₀ k).Φ i) (fderiv ℝ ((stages br φ H sel S₀ k).Φ i) x) x)
    (hdiff' : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel' S₀ k).Φ ∩ V, ∀ i,
      HasStrictFDerivAt ((stages br φ H sel' S₀ k).Φ i) (fderiv ℝ ((stages br φ H sel' S₀ k).Φ i) x) x)
    (hadm : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ ∩ V,
      (sel (stages br φ H sel S₀ k)).Admissible br φ x)
    (hadm' : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel' S₀ k).Φ ∩ V,
      (sel' (stages br φ H sel' S₀ k)).Admissible br φ x) :
    ∀ k, zeroSet (stages br φ H sel S₀ k).Φ ∩ V = zeroSet (stages br φ H sel' S₀ k).Φ ∩ V := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
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
          (hVo.mem_nhds hxV) ih hx (hdiff k x ⟨hx, hxV⟩) (hdiff' k x ⟨hx', hxV⟩) (hreg k x ⟨hx, hxV⟩)
          (hreg' k x ⟨hx', hxV⟩)⟩
    constructor
    · rintro ⟨⟨hx, hχ⟩, hxV⟩
      obtain ⟨hx', hc⟩ := hiff hxV hx
      refine ⟨⟨hx', ?_⟩, hxV⟩
      have h1 := ((stages br φ H sel S₀ k).chiFun_zero_iff br φ H (hadm k x ⟨hx, hxV⟩)).mp hχ
      exact ((stages br φ H sel' S₀ k).chiFun_zero_iff br φ H (hadm' k x ⟨hx', hxV⟩)).mpr (hc.mp h1)
    · rintro ⟨⟨hx', hχ⟩, hxV⟩
      have hx : x ∈ zeroSet (stages br φ H sel S₀ k).Φ := by
        have : x ∈ zeroSet (stages br φ H sel' S₀ k).Φ ∩ V := ⟨hx', hxV⟩
        rw [← ih] at this
        exact this.1
      obtain ⟨-, hc⟩ := hiff hxV hx
      refine ⟨⟨hx, ?_⟩, hxV⟩
      have h1 := ((stages br φ H sel' S₀ k).chiFun_zero_iff br φ H (hadm' k x ⟨hx', hxV⟩)).mp hχ
      exact ((stages br φ H sel S₀ k).chiFun_zero_iff br φ H (hadm k x ⟨hx, hxV⟩)).mpr (hc.mpr h1)

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

/-- **An atlas for the Dirac algorithm**: open sets `U α` covering the primary surface, each with its own selection rule,
whose stages are regular, strictly differentiable and admissible at the points of their zero sets inside `U α` (what the
constant-rank hypothesis gives near each point, `DiracLocal.exists_selection_near`). -/
structure DiracAtlas (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ) (S₀ : Stage E)
    (A : Type*) where
  /-- The chart domains. -/
  U : A → Set E
  /-- The chart domains are open. -/
  isOpen : ∀ α, IsOpen (U α)
  /-- The selection rule of each chart. -/
  sel : A → ∀ S : Stage E, Sel S M
  /-- The stages of each chart are regular inside its domain. -/
  reg : ∀ α k, ∀ x ∈ zeroSet (stages br φ H (sel α) S₀ k).Φ ∩ U α,
    LinearIndependent ℝ fun i => fderiv ℝ ((stages br φ H (sel α) S₀ k).Φ i) x
  /-- The stages of each chart are strictly differentiable inside its domain. -/
  diff : ∀ α k, ∀ x ∈ zeroSet (stages br φ H (sel α) S₀ k).Φ ∩ U α, ∀ i,
    HasStrictFDerivAt ((stages br φ H (sel α) S₀ k).Φ i) (fderiv ℝ ((stages br φ H (sel α) S₀ k).Φ i) x) x
  /-- The selected blocks of each chart are admissible inside its domain. -/
  adm : ∀ α k, ∀ x ∈ zeroSet (stages br φ H (sel α) S₀ k).Φ ∩ U α,
    (sel α (stages br φ H (sel α) S₀ k)).Admissible br φ x
  /-- The chart domains cover the primary surface. -/
  cover : zeroSet S₀.Φ ⊆ ⋃ α, U α

namespace DiracAtlas

variable {br : (E → ℝ) → (E → ℝ) → E → ℝ} {φ : Fin M → E → ℝ} {H : E → ℝ} {S₀ : Stage E} {A : Type*}

/-- **The glued surfaces** `Γₖ = ⋃_α (Γₖ^α ∩ U_α)`. -/
def surface (𝒜 : DiracAtlas br φ H S₀ A) (k : ℕ) : Set E :=
  ⋃ α, zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α

/-- **The glued surface agrees with every chart**: `Γₖ ∩ U_α = Γₖ^α ∩ U_α`. -/
theorem surface_inter (𝒜 : DiracAtlas br φ H S₀ A) (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ)
    (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x)) (α : A) (k : ℕ) :
    𝒜.surface k ∩ 𝒜.U α = zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α := by
  ext x
  constructor
  · rintro ⟨hx, hxα⟩
    obtain ⟨β, hxβ, hβ⟩ := Set.mem_iUnion.mp hx
    have hV : IsOpen (𝒜.U β ∩ 𝒜.U α) := (𝒜.isOpen β).inter (𝒜.isOpen α)
    have heq := zeroSet_stages_inter_eq br φ H B hB (𝒜.sel β) (𝒜.sel α) S₀ hV
      (fun k x hx => 𝒜.reg β k x ⟨hx.1, hx.2.1⟩) (fun k x hx => 𝒜.reg α k x ⟨hx.1, hx.2.2⟩)
      (fun k x hx => 𝒜.diff β k x ⟨hx.1, hx.2.1⟩) (fun k x hx => 𝒜.diff α k x ⟨hx.1, hx.2.2⟩)
      (fun k x hx => 𝒜.adm β k x ⟨hx.1, hx.2.1⟩) (fun k x hx => 𝒜.adm α k x ⟨hx.1, hx.2.2⟩) k
    have : x ∈ zeroSet (stages br φ H (𝒜.sel β) S₀ k).Φ ∩ (𝒜.U β ∩ 𝒜.U α) := ⟨hxβ, hβ, hxα⟩
    rw [heq] at this
    exact ⟨this.1, hxα⟩
  · rintro ⟨hx, hxα⟩
    exact ⟨Set.mem_iUnion.mpr ⟨α, hx, hxα⟩, hxα⟩

/-- **The glued surfaces start at the primary surface.** -/
theorem surface_zero (𝒜 : DiracAtlas br φ H S₀ A) : 𝒜.surface 0 = zeroSet S₀.Φ := by
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
theorem chart_succ (𝒜 : DiracAtlas br φ H S₀ A) (α : A) (k : ℕ) :
    zeroSet (stages br φ H (𝒜.sel α) S₀ (k + 1)).Φ ∩ 𝒜.U α =
      {x | x ∈ zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α ∧
        (stages br φ H (𝒜.sel α) S₀ k).Consistent br φ H x} := by
  ext x
  show x ∈ zeroSet (appendStage (stages br φ H (𝒜.sel α) S₀ k).Φ
      ((stages br φ H (𝒜.sel α) S₀ k).chiFun br φ H (𝒜.sel α (stages br φ H (𝒜.sel α) S₀ k)))) ∩ 𝒜.U α ↔ _
  rw [zeroSet_appendStage]
  constructor
  · rintro ⟨⟨hx, hχ⟩, hxα⟩
    exact ⟨⟨hx, hxα⟩, ((stages br φ H (𝒜.sel α) S₀ k).chiFun_zero_iff br φ H (𝒜.adm α k x ⟨hx, hxα⟩)).mp hχ⟩
  · rintro ⟨⟨hx, hxα⟩, hc⟩
    exact ⟨⟨hx, ((stages br φ H (𝒜.sel α) S₀ k).chiFun_zero_iff br φ H (𝒜.adm α k x ⟨hx, hxα⟩)).mpr hc⟩, hxα⟩

/-- **The chart-free recursion**: `Γₖ₊₁` is the set of points of `Γₖ` at which the consistency system of every chart
containing the point is solvable. -/
theorem surface_succ (𝒜 : DiracAtlas br φ H S₀ A) (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ)
    (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x)) (k : ℕ) :
    𝒜.surface (k + 1) =
      {x | x ∈ 𝒜.surface k ∧ ∀ α, x ∈ 𝒜.U α → (stages br φ H (𝒜.sel α) S₀ k).Consistent br φ H x} := by
  have hstep := 𝒜.chart_succ (k := k)
  ext x
  constructor
  · intro hx
    obtain ⟨β, hxβ⟩ := Set.mem_iUnion.mp hx
    rw [hstep β] at hxβ
    refine ⟨Set.mem_iUnion.mpr ⟨β, hxβ.1⟩, fun α hxα => ?_⟩
    have h1 : x ∈ 𝒜.surface (k + 1) ∩ 𝒜.U α := ⟨hx, hxα⟩
    rw [𝒜.surface_inter B hB α (k + 1), hstep α] at h1
    exact h1.2
  · rintro ⟨hx, hc⟩
    obtain ⟨α, hxα⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨α, ?_⟩
    rw [hstep α]
    exact ⟨hxα, hc α hxα.2⟩

/-- **A pause is final**: if the surface of a chart does not change at one step, it never changes again (its consistency
condition depends only on the surface, `Stage.consistent_iff_of_zeroSet_inter_eq`). -/
theorem chart_pause (𝒜 : DiracAtlas br φ H S₀ A) (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ)
    (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x)) (α : A) {k : ℕ}
    (hk : zeroSet (stages br φ H (𝒜.sel α) S₀ (k + 1)).Φ ∩ 𝒜.U α = zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α) :
    zeroSet (stages br φ H (𝒜.sel α) S₀ (k + 2)).Φ ∩ 𝒜.U α =
      zeroSet (stages br φ H (𝒜.sel α) S₀ (k + 1)).Φ ∩ 𝒜.U α := by
  rw [𝒜.chart_succ α (k + 1)]
  ext x
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
  have hxk : x ∈ zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α := hk ▸ hx
  have hck : (stages br φ H (𝒜.sel α) S₀ k).Consistent br φ H x := by
    have := hx
    rw [𝒜.chart_succ α k] at this
    exact this.2
  exact ((stages br φ H (𝒜.sel α) S₀ (k + 1)).consistent_iff_of_zeroSet_inter_eq br φ H B hB _
    ((𝒜.isOpen α).mem_nhds hx.2) hk hx.1 (𝒜.diff α (k + 1) x hx) (𝒜.diff α k x hxk) (𝒜.reg α (k + 1) x hx)
    (𝒜.reg α k x hxk)).mpr hck

/-- **Every chart stops changing by the stage `dim E + 1`**: a step that changes the surface adds constraints, and a
regular stage with a point has at most `dim E` of them. -/
theorem chart_stable (𝒜 : DiracAtlas br φ H S₀ A) (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ)
    (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x)) (α : A) :
    ∀ k, Module.finrank ℝ E + 1 ≤ k → zeroSet (stages br φ H (𝒜.sel α) S₀ k).Φ ∩ 𝒜.U α =
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
  intro k hk
  by_cases hp : ∃ j < N, Z (j + 1) = Z j
  · obtain ⟨j, hjN, hj⟩ := hp
    have hall : ∀ m, j ≤ m → Z (m + 1) = Z m := fun m hm => by
      induction m, hm using Nat.le_induction with
      | base => exact hj
      | succ m hm ih => exact 𝒜.chart_pause B hB α ih
    have hconst : ∀ m, j ≤ m → Z m = Z j := fun m hm => by
      induction m, hm using Nat.le_induction with
      | base => rfl
      | succ m hm ih => rw [hall m hm, ih]
    show Z k = Z N
    rw [hconst k (by omega), hconst N hjN.le]
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
      have h1 := LinearIndependent.fintype_card_le_finrank (𝒜.reg α N x hx)
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
chart): the glued surfaces stop changing by the stage `dim E + 1`, and at every point of the final surface the
consistency conditions `{S_i, H} + ∑_a {S_i, φ_a} u_a = 0` of every chart containing the point are solvable. -/
theorem final_consistent (𝒜 : DiracAtlas br φ H S₀ A)
    (B : E → (E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) → ℝ) (hB : ∀ f g x, br f g x = B x (fderiv ℝ f x) (fderiv ℝ g x)) :
    (∀ k, Module.finrank ℝ E + 1 ≤ k → 𝒜.surface k = 𝒜.surface (Module.finrank ℝ E + 1)) ∧
      ∀ x ∈ 𝒜.surface (Module.finrank ℝ E + 1), ∀ α, x ∈ 𝒜.U α →
        (stages br φ H (𝒜.sel α) S₀ (Module.finrank ℝ E + 1)).Consistent br φ H x := by
  have hstab : ∀ k, Module.finrank ℝ E + 1 ≤ k → 𝒜.surface k = 𝒜.surface (Module.finrank ℝ E + 1) := fun k hk => by
    simp only [surface]
    exact Set.iUnion_congr fun α => 𝒜.chart_stable B hB α k hk
  refine ⟨hstab, fun x hx α hxα => ?_⟩
  have h1 : x ∈ 𝒜.surface (Module.finrank ℝ E + 1 + 1) := by
    rw [hstab _ (by omega)]
    exact hx
  rw [𝒜.surface_succ B hB] at h1
  exact h1.2 α hxα

/-- **The one-chart atlas** of a single selection rule admissible on the whole zero set of every stage (the situation of
`final_consistent_of_cover`). -/
def ofSelection (sel : ∀ S : Stage E, Sel S M) (hreg : ∀ k, IsRegularStage (stages br φ H sel S₀ k).Φ)
    (hdiff : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ, ∀ i,
      HasStrictFDerivAt ((stages br φ H sel S₀ k).Φ i) (fderiv ℝ ((stages br φ H sel S₀ k).Φ i) x) x)
    (hadm : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ, (sel (stages br φ H sel S₀ k)).Admissible br φ x) :
    DiracAtlas br φ H S₀ Unit where
  U _ := Set.univ
  isOpen _ := isOpen_univ
  sel _ := sel
  reg _ k x hx := hreg k x hx.1
  diff _ k x hx := hdiff k x hx.1
  adm _ k x hx := hadm k x hx.1
  cover _ _ := Set.mem_iUnion.mpr ⟨(), Set.mem_univ _⟩

/-- The glued surfaces of the one-chart atlas are the zero sets of the stages. -/
theorem surface_ofSelection (sel : ∀ S : Stage E, Sel S M) (hreg : ∀ k, IsRegularStage (stages br φ H sel S₀ k).Φ)
    (hdiff : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ, ∀ i,
      HasStrictFDerivAt ((stages br φ H sel S₀ k).Φ i) (fderiv ℝ ((stages br φ H sel S₀ k).Φ i) x) x)
    (hadm : ∀ k, ∀ x ∈ zeroSet (stages br φ H sel S₀ k).Φ, (sel (stages br φ H sel S₀ k)).Admissible br φ x) (k : ℕ) :
    (ofSelection sel hreg hdiff hadm).surface k = zeroSet (stages br φ H sel S₀ k).Φ := by
  ext x
  simp [surface, ofSelection]

end DiracAtlas

end Lightlike.Gauge
