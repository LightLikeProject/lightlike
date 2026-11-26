import Lightlike.Spacetime.PenroseSingularity.FormContinuity
import Lightlike.Spacetime.PenroseSingularity.FamilyTheta
import Lightlike.Spacetime.PenroseSingularity.FocalLength

/-!
# A uniform bound for the expansion of a null normal field (G1-012, step 3)

For a smooth future null normal field `k` along a compact closed trapped spacelike surface `S`, the
expansion `frameExpansion k x e` over an orthonormal frame `e` of `T_x S` is negative, locally constant in
the sense that it equals `tr (Q⁻¹ Cᵀ)` of a local parametrisation, and hence bounded away from `0`
uniformly over `S`.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold Matrix

noncomputable section

namespace Lightlike.Penrose

/-- Continuity of `σ ↦ tr (Q⁻¹ Cᵀ)` at a point where `Q` is invertible. -/
theorem continuousAt_trace_inv {α : Type*} [TopologicalSpace α] {m : ℕ} {Q C : α → Matrix (Fin m) (Fin m) ℝ}
    {a : α} (hQ : ContinuousAt Q a) (hC : ContinuousAt C a) (hdet : (Q a).det ≠ 0) :
    ContinuousAt (fun σ => Matrix.trace ((Q σ)⁻¹ * (C σ)ᵀ)) a := by
  have hdet' : Continuous fun A : Matrix (Fin m) (Fin m) ℝ => A.det := Continuous.matrix_det continuous_id
  have hadj' : Continuous fun A : Matrix (Fin m) (Fin m) ℝ => A.adjugate :=
    Continuous.matrix_adjugate continuous_id
  have hdc : ContinuousAt (fun σ => (Q σ).det) a := hdet'.continuousAt.comp hQ
  have hadj : ContinuousAt (fun σ => (Q σ).adjugate) a := hadj'.continuousAt.comp hQ
  have hinv : ContinuousAt (fun σ => (Q σ)⁻¹) a := by
    have : (fun σ => (Q σ)⁻¹) = fun σ => ((Q σ).det)⁻¹ • (Q σ).adjugate := by
      funext σ; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    exact (hdc.inv₀ hdet).smul hadj
  have hmul : Continuous fun p : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ => p.1 * p.2 :=
    Continuous.matrix_mul continuous_fst continuous_snd
  have htr : Continuous fun A : Matrix (Fin m) (Fin m) ℝ => A.trace := Continuous.matrix_trace continuous_id
  have hCt : ContinuousAt (fun σ => (C σ)ᵀ) a :=
    (Continuous.matrix_transpose (continuous_id : Continuous fun A : Matrix (Fin m) (Fin m) ℝ => A)).continuousAt.comp hC
  exact htr.continuousAt.comp (hmul.continuousAt.comp (hinv.prodMk hCt))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **Local lower bound for the expansion.** Near a point `x₀` of `S`, every orthonormal frame of `ker df_y`,
`y ∈ S`, gives `|frameExpansion k y e| ≥ c` for a constant `c > 0`. -/
theorem local_expansion_bound (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita g.toNondegMetric) (T : Causal.TimeOrientation g) {S : Set M} (hn : 3 ≤ n)
    {f : M → Fin 2 → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f) (hS : S = f ⁻¹' {0})
    (hsub : ∀ x ∈ S, Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x))
    (hsp : ∀ x ∈ S, ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → v ≠ 0 → 0 < g.g x v v)
    {k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hk : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    (hexp : ∀ x ∈ S, ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x (e i) = 0) →
      (∀ i j, g.g x (e i) (e j) = if i = j then 1 else 0) → frameExpansion g cov k x e < 0)
    {x₀ : M} (hx₀ : x₀ ∈ S) :
    ∃ N ∈ 𝓝 x₀, ∃ c > 0, ∀ y ∈ N, y ∈ S → ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) y,
      (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f y (e i) = 0) →
      (∀ i j, g.g y (e i) (e j) = if i = j then 1 else 0) → c ≤ |frameExpansion g cov k y e| := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hfx₀ : f x₀ = 0 := by rw [hS] at hx₀; exact hx₀
  obtain ⟨xS, Sg₀, hSo, hS0, hsm, hx0, hfx, hinj, hker, hloc⟩ := exists_surface_param hn2 hf hfx₀ (hsub x₀ hx₀)
  subst hx0
  set Qx : (Fin (n - 2) → ℝ) → Matrix (Fin (n - 2)) (Fin (n - 2)) ℝ := fun σ =>
    Matrix.of fun i j => g.g (xS σ) (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single i 1))
      (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single j 1)) with hQx
  set Cx : (Fin (n - 2) → ℝ) → Matrix (Fin (n - 2)) (Fin (n - 2)) ℝ := fun σ =>
    Matrix.of fun i j => g.g (xS σ)
      (cov k (xS σ) (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single i 1)))
      (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single j 1)) with hCx
  have hQc : ContinuousAt Qx 0 := continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
    (continuousAt_forms g hLC hSo hS0 hsm hk (Pi.single i 1) (Pi.single j 1)).1
  have hCc : ContinuousAt Cx 0 := continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
    (continuousAt_forms g hLC hSo hS0 hsm hk (Pi.single i 1) (Pi.single j 1)).2
  have hxd : ∀ σ ∈ Sg₀, MDifferentiableAt 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ := fun σ hσ =>
    (hsm.contMDiffAt (hSo.mem_nhds hσ)).mdifferentiableAt (by simp)
  have hfd : ∀ σ, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (xS σ) := fun σ =>
    hf.contMDiffAt.mdifferentiableAt (by simp)
  have hfxe : ∀ σ ∈ Sg₀, ∀ᶠ σ' in 𝓝 σ, f (xS σ') = 0 := fun σ hσ =>
    Filter.eventually_of_mem (hSo.mem_nhds hσ) hfx
  have hker' : ∀ σ ∈ Sg₀, ∀ i : Fin (n - 2), mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (xS σ)
      (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single i 1)) = 0 := fun σ hσ i =>
    mfderiv_mem_ker (hfd σ) (hxd σ hσ) (hfxe σ hσ) (Pi.single i 1)
  have hlin0 : LinearIndependent ℝ (fun i : Fin (n - 2) =>
      mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0 (Pi.single i 1)) := by
    have := (Pi.basisFun ℝ (Fin (n - 2))).linearIndependent.map'
      (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0).toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    convert this using 1
    funext i
    have hb : (Pi.basisFun ℝ (Fin (n - 2))) i = Pi.single i 1 := by simp
    simp only [Function.comp_apply, hb]
    rfl
  obtain ⟨hpd0, e0, he0K, he0o, htr0⟩ := trace_neg_of_trapped g cov f k (xS 0) (hsp _ hx₀) (hexp _ hx₀) rfl
    (fun i => mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0 (Pi.single i 1)) hlin0
    (hker' 0 hS0)
  have hdet0 : (Qx 0).det ≠ 0 := hpd0.det_pos.ne'
  set T₀ : ℝ := Matrix.trace ((Qx 0)⁻¹ * (Cx 0)ᵀ) with hT₀
  have hT0neg : T₀ < 0 := by
    exact lt_of_eq_of_lt htr0 (hexp _ hx₀ e0 he0K he0o)
  have hTc := continuousAt_trace_inv hQc hCc hdet0
  have hE1 : ∀ᶠ σ in 𝓝 (0 : Fin (n - 2) → ℝ), Matrix.trace ((Qx σ)⁻¹ * (Cx σ)ᵀ) < T₀ / 2 :=
    hTc.eventually (Iio_mem_nhds (by linarith))
  have hE2 : ∀ᶠ σ in 𝓝 (0 : Fin (n - 2) → ℝ), (Qx σ).det ≠ 0 := by
    have hdc : ContinuousAt (fun σ => (Qx σ).det) 0 :=
      (Continuous.matrix_det (continuous_id : Continuous fun A : Matrix (Fin (n - 2)) (Fin (n - 2)) ℝ => A)).continuousAt.comp hQc
    exact hdc.eventually_ne hdet0
  have hE3 : ∀ᶠ σ in 𝓝 (0 : Fin (n - 2) → ℝ), σ ∈ Sg₀ := hSo.mem_nhds hS0
  obtain ⟨N, hNn, hN⟩ := hloc _ (hE1.and (hE2.and hE3))
  refine ⟨N, hNn, -T₀ / 2, by linarith, fun y hyN hyS e heK hortho => ?_⟩
  obtain ⟨σ, ⟨hT1, hdet, hσS⟩, rfl⟩ := hN y hyN (by rw [hS] at hyS; exact hyS)
  set Gm : TangentSpace 𝓘(ℝ, Fin n → ℝ) (xS σ) →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) (xS σ) →ₗ[ℝ] ℝ :=
    ContinuousLinearMap.toLinearMap₁₂ (g.g (xS σ)) with hGm
  set Bm : TangentSpace 𝓘(ℝ, Fin n → ℝ) (xS σ) →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) (xS σ) →ₗ[ℝ] ℝ :=
    ContinuousLinearMap.toLinearMap₁₂ ((g.g (xS σ)).comp (cov k (xS σ))) with hBm
  set uσ : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) (xS σ) := fun i =>
    mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single i 1) with huσ
  have hlin : LinearIndependent ℝ uσ :=
    linearIndependent_of_gram_det Gm (fun v w => g.symm (xS σ) v w) uσ (by simpa [hGm, huσ, hQx] using hdet)
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) (xS σ)) =
      Module.finrank ℝ (Fin 2 → ℝ) + (n - 2) := by
    have h1 : Module.finrank ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) (xS σ)) = n := by
      exact Module.finrank_fin_fun ℝ
    rw [h1]; simp; omega
  have hmain := sum_eq_trace_of_frame (m := n - 2) (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (xS σ)).toLinearMap
    (hsub _ hyS) hdim Gm Bm uσ hlin (fun i => hker' σ hσS i) e heK (fun a b => by simpa [hGm] using hortho a b)
  have hFE : frameExpansion g cov k (xS σ) e = Matrix.trace ((Qx σ)⁻¹ * (Cx σ)ᵀ) := by
    unfold frameExpansion
    simpa [hGm, hBm, huσ, hQx, hCx] using hmain
  rw [hFE, abs_of_neg (by linarith)]
  linarith

/-- The pairing of two continuous sections by a smooth metric is continuous. -/
theorem continuousAt_pairing (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {A B : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y} {x : M}
    (hA : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 0
      (fun q : M => (⟨q, A q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x)
    (hB : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 0
      (fun q : M => (⟨q, B q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x) :
    ContinuousAt (fun y => g.g y (A y) (B y)) x := by
  have hg : ContMDiffAt 𝓘(ℝ, Fin n → ℝ)
      (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)) 0
      (fun y => Bundle.TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) y →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) y →L[ℝ] ℝ) y (g.g y)) x :=
    (g.contMDiff x).of_le (by norm_num)
  have := ContMDiffAt.clm_bundle_apply₂ (b := id) (F₁ := Fin n → ℝ) (F₂ := Fin n → ℝ) (F₃ := ℝ)
    (E₁ := TangentSpace 𝓘(ℝ, Fin n → ℝ)) (E₂ := TangentSpace 𝓘(ℝ, Fin n → ℝ))
    (E₃ := Bundle.Trivial M ℝ) hg hA hB
  rw [Bundle.contMDiffAt_totalSpace] at this
  exact this.2.continuousAt

/-- The normalised length bound of a single null normal field is bounded by `Λ`. -/
def ExpansionBound (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (cov : Connection 𝓘(ℝ, Fin n → ℝ) M)
    (T : Causal.TimeOrientation g) (S : Set M) (f : M → Fin 2 → ℝ)
    (k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p) (Λ : ℝ) : Prop :=
  ∀ x ∈ S, ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
    (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x (e i) = 0) →
    (∀ i j, g.g x (e i) (e j) = if i = j then 1 else 0) →
    (-(g.g x (k x) (T.X x))) * (((n - 2 : ℕ) : ℝ) / |frameExpansion g cov k x e|) ≤ Λ

/-- **A uniform bound over the compact surface** for a smooth future null normal field. -/
theorem exists_expansion_bound (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita g.toNondegMetric) (T : Causal.TimeOrientation g) {S : Set M} (hn : 3 ≤ n)
    (hc : IsCompact S) {f : M → Fin 2 → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f)
    (hS : S = f ⁻¹' {0})
    (hsub : ∀ x ∈ S, Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x))
    (hsp : ∀ x ∈ S, ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → v ≠ 0 → 0 < g.g x v v)
    {k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hk : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    (hkN : ∀ x ∈ S, IsFutureNullNormalAt g T f x (k x))
    (hexp : ∀ x ∈ S, ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x (e i) = 0) →
      (∀ i j, g.g x (e i) (e j) = if i = j then 1 else 0) → frameExpansion g cov k x e < 0) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ExpansionBound g cov T S f k Λ := by
  classical
  have hloc : ∀ x ∈ S, ∃ N ∈ 𝓝 x, ∃ b : ℝ, 0 ≤ b ∧ ∀ y ∈ N, y ∈ S →
      ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) y,
        (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f y (e i) = 0) →
        (∀ i j, g.g y (e i) (e j) = if i = j then 1 else 0) →
        (-(g.g y (k y) (T.X y))) * (((n - 2 : ℕ) : ℝ) / |frameExpansion g cov k y e|) ≤ b := by
    intro x₀ hx₀
    obtain ⟨N₁, hN₁, c, hc0, hN₁b⟩ := local_expansion_bound g hLC T hn hf hS hsub hsp hk hexp hx₀
    have hcont : ContinuousAt (fun y => g.g y (k y) (T.X y)) x₀ :=
      continuousAt_pairing g (hk.contMDiffAt.of_le (by norm_num)) (T.contMDiff.contMDiffAt)
    set g₀ : ℝ := g.g x₀ (k x₀) (T.X x₀) with hg₀
    have hN₂ : {y | g₀ - 1 < g.g y (k y) (T.X y)} ∈ 𝓝 x₀ :=
      hcont.eventually (Ioi_mem_nhds (by linarith))
    refine ⟨N₁ ∩ {y | g₀ - 1 < g.g y (k y) (T.X y)}, Filter.inter_mem hN₁ hN₂,
      max (-g₀ + 1) 0 * (((n - 2 : ℕ) : ℝ) / c), by positivity, fun y hy hyS e heK hortho => ?_⟩
    have hgy : g.g y (k y) (T.X y) < 0 := (hkN y hyS).2.2.2
    have h1 : -(g.g y (k y) (T.X y)) ≤ max (-g₀ + 1) 0 := by
      have := hy.2; simp only [mem_setOf_eq] at this
      exact le_trans (by linarith) (le_max_left _ _)
    have hcy := hN₁b y hy.1 hyS e heK hortho
    have hpos : 0 < |frameExpansion g cov k y e| := lt_of_lt_of_le hc0 hcy
    have h2 : ((n - 2 : ℕ) : ℝ) / |frameExpansion g cov k y e| ≤ ((n - 2 : ℕ) : ℝ) / c :=
      div_le_div_of_nonneg_left (by positivity) hc0 hcy
    exact mul_le_mul h1 h2 (by positivity) (le_trans (by linarith) h1)
  choose! N hN b hb0 hb using hloc
  obtain ⟨t, htS, hcov⟩ := hc.elim_nhds_subcover N hN
  refine ⟨∑ x ∈ t, b x, Finset.sum_nonneg fun x hx => hb0 x (htS x hx), fun y hyS e heK hortho => ?_⟩
  obtain ⟨x, hxt, hyN⟩ := mem_iUnion₂.1 (hcov hyS)
  exact le_trans (hb x (htS x hxt) y hyN hyS e heK hortho)
    (Finset.single_le_sum (fun z hz => hb0 z (htS z hz)) hxt)

end Lightlike.Penrose
