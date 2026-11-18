import Lightlike.Spacetime.Causal.CurveOps

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {P : ∀ x : M, TangentSpace I x → Prop}

omit [IsManifold I ∞ M] in
/-- **A curve with velocity in `P` is determined, as such, by its values on the interval.** -/
theorem IsCurveWith.congr_on {σ σ' : ℝ → M} {a b : ℝ} (hab : a < b)
    (h : IsCurveWith (I := I) P σ (Icc a b)) (heq : EqOn σ' σ (Icc a b)) :
    IsCurveWith (I := I) P σ' (Icc a b) := by
  refine ⟨ordConnected_Icc, ?_, ?_⟩
  · intro t ht
    obtain ⟨K, U, hU, hmaps, hl⟩ := h.lipschitz t ht
    have hU' : U ∩ Icc a b ∈ nhdsWithin t (Icc a b) := inter_mem hU self_mem_nhdsWithin
    have hx : σ' t = σ t := heq ht
    refine ⟨K, U ∩ Icc a b, hU', ?_, ?_⟩
    · intro y hy
      rw [hx, heq hy.2]
      exact hmaps hy.1
    · rw [hx]
      intro x hx' y hy'
      simp only [Function.comp, heq hx'.2, heq hy'.2]
      exact hl hx'.1 hy'.1
  · have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a ∧ t ≠ b := by
      have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({a} : Set ℝ) := (countable_singleton a).ae_notMem _
      have h2 : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({b} : Set ℝ) := (countable_singleton b).ae_notMem _
      filter_upwards [h1, h2] with t h1 h2 using ⟨h1, h2⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc, h.ae_velocity, ae_restrict_of_ae hne]
      with t ht ⟨hd, hP⟩ hne'
    have hta : a < t := lt_of_le_of_ne ht.1 (Ne.symm hne'.1)
    have htb : t < b := lt_of_le_of_ne ht.2 hne'.2
    have hG : σ' =ᶠ[𝓝 t] σ := Filter.eventually_of_mem (Icc_mem_nhds hta htb) fun y hy => heq hy
    exact velocity_congr (P := P) (s := Icc a b) (s' := Icc a b) Filter.EventuallyEq.rfl hG hd hP


omit [IsManifold I ∞ M] in
/-- **A curve on `[0, ∞)` whose restrictions to `[0, m + 1]` have velocity in `P` has velocity in `P`.** -/
theorem IsCurveWith.of_forall_Icc {σ : ℝ → M}
    (h : ∀ m : ℕ, IsCurveWith (I := I) P σ (Icc 0 ((m : ℝ) + 1))) :
    IsCurveWith (I := I) P σ (Ici 0) := by
  refine ⟨ordConnected_Ici, ?_, ?_⟩
  · intro t ht
    obtain ⟨m, hm⟩ := exists_nat_gt t
    have htm : t ∈ Icc 0 ((m : ℝ) + 1) := ⟨ht, by linarith⟩
    obtain ⟨K, U, hU, hmaps, hl⟩ := (h m).lipschitz t htm
    refine ⟨K, U, ?_, hmaps, hl⟩
    obtain ⟨V, hV, hVU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hU
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨V ∩ Iio ((m : ℝ) + 1), inter_mem hV
      (Iio_mem_nhds (by linarith)), fun y hy => hVU ⟨hy.1.1, hy.2, hy.1.2.le⟩⟩
  · have hcov : (Ici (0 : ℝ)) = ⋃ m : ℕ, Icc 0 ((m : ℝ) + 1) := by
      ext y
      simp only [mem_Ici, mem_iUnion, mem_Icc]
      refine ⟨fun hy => ?_, fun ⟨m, hm⟩ => hm.1⟩
      obtain ⟨m, hm⟩ := exists_nat_ge y
      exact ⟨m, hy, by linarith⟩
    rw [hcov]
    refine (ae_restrict_iUnion_iff _ _).2 fun m => ?_
    have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 ∧ t ≠ (m : ℝ) + 1 := by
      have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({0} : Set ℝ) := (countable_singleton 0).ae_notMem _
      have h2 : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({(m : ℝ) + 1} : Set ℝ) :=
        (countable_singleton _).ae_notMem _
      filter_upwards [h1, h2] with t h1 h2 using ⟨h1, h2⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc, (h m).ae_velocity, ae_restrict_of_ae h0]
      with t ht ⟨hd, hP⟩ hne
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hne.1)
    have ht1 : t < (m : ℝ) + 1 := lt_of_le_of_ne ht.2 hne.2
    have hset : Ici (0 : ℝ) =ᶠ[𝓝 t] Icc 0 ((m : ℝ) + 1) := by
      refine (Filter.eventuallyEqSet_iff).2 (Filter.eventually_of_mem (Ioo_mem_nhds ht0 ht1) fun y hy => ?_)
      exact ⟨fun hy' => ⟨hy', hy.2.le⟩, fun hy' => hy'.1⟩
    -- the statement is about the hcov-rewritten set: restore it
    have := velocity_congr (P := P) (γ := σ) (G := σ) (s := Icc 0 ((m : ℝ) + 1)) (s' := Ici 0) (t := t) hset
      Filter.EventuallyEq.rfl hd hP
    rw [← hcov] at *
    exact this


/-! ## Limit points of subsequences -/

variable {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- `q` is a **limit point of the curves `γ (φ k)`**: every neighbourhood of `q` meets all but finitely many of them. -/
def IsLimitPointOf (γ : ℕ → ℝ → M) (s : ℕ → Set ℝ) (φ : ℕ → ℕ) (q : M) : Prop :=
  ∀ U ∈ 𝓝 q, ∀ᶠ k in atTop, ∃ t ∈ s (φ k), γ (φ k) t ∈ U

omit [IsManifold I ∞ M] in
/-- A limit point of the curves of a subsequence is one of every subsubsequence. -/
theorem IsLimitPointOf.comp {γ : ℕ → ℝ → M} {s : ℕ → Set ℝ} {φ ψ : ℕ → ℕ} {q : M}
    (h : IsLimitPointOf γ s φ q) (hψ : StrictMono ψ) : IsLimitPointOf γ s (φ ∘ ψ) q :=
  fun U hU => hψ.tendsto_atTop.eventually (h U hU)

omit [IsManifold I ∞ M] in
/-- **A point that infinitely many curves approach is a limit point of a subsequence.** -/
theorem exists_subseq_isLimitPointOf [FirstCountableTopology M] {γ : ℕ → ℝ → M} {s : ℕ → Set ℝ} {p : M}
    (hp : ∀ U ∈ 𝓝 p, ∃ᶠ k in atTop, ∃ t ∈ s k, γ k t ∈ U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsLimitPointOf γ s φ p := by
  obtain ⟨U, hU⟩ := (𝓝 p).exists_antitone_basis
  obtain ⟨φ, hφ, hφU⟩ := Filter.extraction_forall_of_frequently
    (P := fun m k => ∃ t ∈ s k, γ k t ∈ U m) fun m => hp (U m) (hU.mem m)
  refine ⟨φ, hφ, fun V hV => ?_⟩
  obtain ⟨m, hm⟩ := hU.mem_iff.1 hV
  filter_upwards [eventually_ge_atTop m] with k hk
  obtain ⟨t, ht, hγ⟩ := hφU k
  exact ⟨t, ht, hm (hU.antitone hk hγ)⟩


/-! ## The recursion over unit arcs -/

/-- **The step property at a centre `q`, with constants `ρ` and `N`**: from every point `q'` of `N` that is a limit point
of the curves of a subsequence there is a unit arc, of which all points are limit points of a subsubsequence, inside the chart
domain of `q`, of chart displacement at least `ρ` in the chart of `q`. -/
def StepAt (γ : ℕ → ℝ → M) (s : ℕ → Set ℝ) (q : M) (ρ : ℝ) (N : Set M) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ∀ q' ∈ N, IsLimitPointOf γ s φ q' →
    ∃ (τ : ℝ → M) (ψ : ℕ → ℕ), StrictMono ψ ∧ IsFutureCausalCurve T τ (Icc 0 1) ∧ τ 0 = q' ∧
      (∀ u ∈ Icc (0 : ℝ) 1, IsLimitPointOf γ s (φ ∘ ψ) (τ u)) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, τ u ∈ (extChartAt I q).source) ∧
      ρ ≤ ‖extChartAt I q (τ 1) - extChartAt I q q'‖

/-- The unit arc `[m, m + 1]` of `σ` is a step arc at the least index `j` with `σ m ∈ N j`. -/
def ArcProp (c : ℕ → M) (ρ : ℕ → ℝ) (N : ℕ → Set M) (σ : ℝ → M) (m : ℕ) : Prop :=
  ∃ j, σ m ∈ N j ∧ (∀ j', σ m ∈ N j' → j ≤ j') ∧
    (∀ u ∈ Icc (m : ℝ) (m + 1), σ u ∈ (extChartAt I (c j)).source) ∧
    ρ j ≤ ‖extChartAt I (c j) (σ ((m : ℝ) + 1)) - extChartAt I (c j) (σ m)‖

/-- The recursion invariant after `n + 1` arcs. -/
def GoodState (γ : ℕ → ℝ → M) (s : ℕ → Set ℝ) (p : M) (c : ℕ → M) (ρ : ℕ → ℝ) (N : ℕ → Set M)
    (n : ℕ) (φ : ℕ → ℕ) (σ : ℝ → M) : Prop :=
  StrictMono φ ∧ IsFutureCausalCurve T σ (Icc 0 ((n : ℝ) + 1)) ∧ σ 0 = p ∧
    (∀ u ∈ Icc (0 : ℝ) ((n : ℝ) + 1), IsLimitPointOf γ s φ (σ u)) ∧ ∀ m ≤ n, ArcProp (I := I) c ρ N σ m

section Family

variable {γ : ℕ → ℝ → M} {s : ℕ → Set ℝ} {p : M} {c : ℕ → M} {ρ : ℕ → ℝ} {N : ℕ → Set M}

omit [IsManifold I ∞ M] in
theorem exists_least_index (N : ℕ → Set M) (hcov : (⋃ j, N j) = univ) (q : M) :
    ∃ j, q ∈ N j ∧ ∀ j', q ∈ N j' → j ≤ j' := by
  classical
  have hex : ∃ j, q ∈ N j := by
    have : q ∈ ⋃ j, N j := by rw [hcov]; exact mem_univ q
    simpa using this
  exact ⟨Nat.find hex, Nat.find_spec hex, fun j' h => Nat.find_min' hex h⟩

/-- **The first arc.** -/
theorem goodState_zero (hcov : (⋃ j, N j) = univ) (hstep : ∀ j, StepAt T γ s (c j) (ρ j) (N j))
    {φ₀ : ℕ → ℕ} (hφ₀ : StrictMono φ₀) (hp : IsLimitPointOf γ s φ₀ p) :
    ∃ (φ : ℕ → ℕ) (σ : ℝ → M), GoodState T γ s p c ρ N 0 φ σ := by
  obtain ⟨j, hj, hjmin⟩ := exists_least_index N hcov p
  obtain ⟨τ, ψ, hψ, hτ, hτ0, hlim, hsrc, hdisp⟩ := hstep j φ₀ hφ₀ p hj hp
  refine ⟨φ₀ ∘ ψ, τ, hφ₀.comp hψ, by simpa using hτ, hτ0, ?_, ?_⟩
  · intro u hu
    exact hlim u (by simpa using hu)
  · intro m hm
    have hm0 : m = 0 := Nat.le_zero.1 hm
    subst hm0
    refine ⟨j, by simpa [hτ0] using hj, by simpa [hτ0] using hjmin, ?_, ?_⟩
    · intro u hu
      exact hsrc u (by simpa using hu)
    · simpa [hτ0] using hdisp


/-- **The recursion step**: one more arc, with the same curve on `[0, n + 1]` and a subsequence. -/
theorem goodState_succ (hcov : (⋃ j, N j) = univ) (hstep : ∀ j, StepAt T γ s (c j) (ρ j) (N j))
    {n : ℕ} {φ : ℕ → ℕ} {σ : ℝ → M} (hG : GoodState T γ s p c ρ N n φ σ) :
    ∃ (φ' : ℕ → ℕ) (σ' : ℝ → M), GoodState T γ s p c ρ N (n + 1) φ' σ' ∧
      (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ φ' = φ ∘ ψ) ∧ ∀ u ∈ Icc (0 : ℝ) ((n : ℝ) + 1), σ' u = σ u := by
  obtain ⟨hφ, hσ, hσ0, hlp, harcs⟩ := hG
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (n : ℝ) + 1 := ⟨_, rfl⟩
  rw [← hb] at hσ hlp
  have hb0 : (0 : ℝ) < b := by rw [hb]; positivity
  have hbmem : b ∈ Icc (0 : ℝ) b := ⟨hb0.le, le_rfl⟩
  obtain ⟨j, hj, hjmin⟩ := exists_least_index N hcov (σ b)
  obtain ⟨τ, ψ, hψ, hτ, hτ0, hlim, hsrc, hdisp⟩ := hstep j φ hφ (σ b) hj (hlp b hbmem)
  have hshift := IsCurveWith.shift (P := fun _ v => T.IsFutureCausal v) (I := I) hτ (by norm_num : (0 : ℝ) < 1) (-b)
  have hb1 : (0 : ℝ) - -b = b := by ring
  have hb2 : (1 : ℝ) - -b = b + 1 := by ring
  rw [hb1, hb2] at hshift
  have hjoin : σ b = τ (b + -b) := by rw [add_neg_cancel, hτ0]
  have hglue := IsCurveWith.glue (P := fun _ v => T.IsFutureCausal v) (I := I) hσ hshift hb0 (by linarith) hjoin
  obtain ⟨σ', hσ'⟩ : ∃ σ' : ℝ → M, σ' = fun t => if t ≤ b then σ t else τ (t + -b) := ⟨_, rfl⟩
  have hle : ∀ u, u ≤ b → σ' u = σ u := fun u hu => by rw [hσ']; simp [hu]
  have hgt : ∀ u, b < u → σ' u = τ (u + -b) := fun u hu => by rw [hσ']; simp [not_le.2 hu]
  have hcast : (((n + 1 : ℕ) : ℝ)) = b := by rw [hb]; push_cast; ring
  refine ⟨φ ∘ ψ, σ', ⟨hφ.comp hψ, ?_, ?_, ?_, ?_⟩, ⟨ψ, hψ, rfl⟩, ?_⟩
  · rw [hcast]
    rw [hσ']
    exact hglue
  · rw [hle 0 hb0.le]; exact hσ0
  · intro u hu
    rw [hcast] at hu
    by_cases hub : u ≤ b
    · rw [hle u hub]
      exact (hlp u ⟨hu.1, hub⟩).comp hψ
    · have hub' : b < u := not_le.1 hub
      rw [hgt u hub']
      exact hlim _ ⟨by linarith, by linarith [hu.2]⟩
  · intro m hm
    by_cases hmn : m ≤ n
    · obtain ⟨j', h1, h2, h3, h4⟩ := harcs m hmn
      have hmb : (m : ℝ) + 1 ≤ b := by rw [hb]; exact_mod_cast Nat.add_le_add_right hmn 1
      have hm0 : (m : ℝ) ≤ b := by linarith [Nat.cast_nonneg (α := ℝ) m]
      refine ⟨j', by rw [hle m hm0]; exact h1, fun j'' hj'' => h2 j'' (by rwa [hle m hm0] at hj''), ?_, ?_⟩
      · intro u hu
        rw [hle u (hu.2.trans hmb)]
        exact h3 u hu
      · rw [hle _ hmb, hle m hm0]; exact h4
    · have hmn' : m = n + 1 := by omega
      subst hmn'
      refine ⟨j, by rw [hcast, hle b le_rfl]; exact hj,
        fun j'' hj'' => hjmin j'' (by rwa [hcast, hle b le_rfl] at hj''), ?_, ?_⟩
      · intro u hu
        rw [hcast] at hu
        by_cases hub : u ≤ b
        · have : u = b := le_antisymm hub hu.1
          rw [this, hle b le_rfl]
          have := hsrc 0 ⟨le_rfl, zero_le_one⟩
          rwa [hτ0] at this
        · rw [hgt u (not_le.1 hub)]
          exact hsrc _ ⟨by linarith [not_le.1 hub], by linarith [hu.2]⟩
      · rw [hcast, hle b le_rfl, hgt (b + 1) (by linarith)]
        have : b + 1 + -b = 1 := by ring
        rw [this]
        exact hdisp
  · intro u hu
    rw [hb] at hle
    exact hle u hu.2

end Family

end Lightlike.Causal

end Lightlike.Causal
