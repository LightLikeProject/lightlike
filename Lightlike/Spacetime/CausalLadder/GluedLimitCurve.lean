import Lightlike.Spacetime.Causal.CurveOps

/-!
# The glued limit curve, from a uniform step

Step of the proof of the limit-curve theorem (task `T-GE2-P20`, Hawking–Ellis Lemma 6.2.1): from the **step property** at
every point (`StepAt`: near `q`, from every limit point of the curves of a subsequence there is a unit arc, a limit arc of a
subsubsequence, inside the chart of `q` with chart displacement at least `ρ`, with `ρ` and the neighbourhood independent of the
subsequence), a recursion over unit arcs gives one future causal curve on `[0, ∞)` that is a limit curve of a diagonal
subsequence (`exists_glued_limit_curve_of_step`). The arc `n` is a step arc at the centre `c j` of a fixed countable family
covering the manifold, `j` the least index with `σ n ∈ N j`, as needed by `not_tendsto_of_unit_arcs`. Also: a curve on `[0, ∞)` whose
restrictions to `[0, m + 1]` have velocity in `P` has velocity in `P` (`IsCurveWith.of_forall_Icc`), and two curves that agree on
an interval are curves with velocity in `P` together (`IsCurveWith.congr_on`).

Supporting lemma for the limit-curve theorem; no catalogue entry.
-/

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


/-- A sequence from a one-step existence property. -/
theorem exists_seq_of_step {X : Type*} (P : ℕ → X → Prop) (R : ℕ → X → X → Prop) (x0 : X) (h0 : P 0 x0)
    (hs : ∀ n x, P n x → ∃ y, P (n + 1) y ∧ R n x y) :
    ∃ f : ℕ → X, (∀ n, P n (f n)) ∧ ∀ n, R n (f n) (f (n + 1)) := by
  have key : ∀ n (x : {x // P n x}), ∃ y : {y // P (n + 1) y}, R n x.1 y.1 := fun n x => by
    obtain ⟨y, hy1, hy2⟩ := hs n x.1 x.2
    exact ⟨⟨y, hy1⟩, hy2⟩
  choose g hg using key
  let f : ∀ n, {x // P n x} := fun n => Nat.rec ⟨x0, h0⟩ (fun n x => g n x) n
  exact ⟨fun n => (f n).1, fun n => (f n).2, fun n => hg n (f n)⟩

theorem StepAt.mono {γ : ℕ → ℝ → M} {s : ℕ → Set ℝ} {q : M} {ρ : ℝ} {N N' : Set M}
    (h : StepAt T γ s q ρ N) (hN : N' ⊆ N) : StepAt T γ s q ρ N' :=
  fun φ hφ q' hq' hlp => h φ hφ q' (hN hq') hlp

/-- `σ` on the interval `r` is a **limit curve of the subsequence `φ`** through `p`: a future causal
curve on a nonempty interval, through `p`, each of whose points is met by all but finitely many curves
`γ (φ k)` in every neighbourhood. -/
def IsLimitCurveOf (γ : ℕ → ℝ → M) (s : ℕ → Set ℝ) (p : M) (σ : ℝ → M) (r : Set ℝ) (φ : ℕ → ℕ) :
    Prop :=
  IsFutureCausalCurve T σ r ∧ r.OrdConnected ∧ r.Nonempty ∧ p ∈ σ '' r ∧ StrictMono φ ∧
    ∀ q ∈ σ '' r, ∀ U ∈ 𝓝 q, ∀ᶠ k in atTop, ∃ t ∈ s (φ k), γ (φ k) t ∈ U

/-- **The glued curve, from the step property** (the recursion over unit arcs, with a diagonal subsequence). -/
theorem exists_glued_limit_curve_of_step [SecondCountableTopology M] (γ : ℕ → ℝ → M) (s : ℕ → Set ℝ) (p : M)
    (hp : ∀ U ∈ 𝓝 p, ∃ᶠ k in atTop, ∃ t ∈ s k, γ k t ∈ U)
    (hstep : ∀ q : M, ∃ ρ : ℝ, 0 < ρ ∧ ∃ N ∈ 𝓝 q, closure N ⊆ (extChartAt I q).source ∧
      StepAt T γ s q ρ N) :
    ∃ (c : ℕ → M) (ρ : ℕ → ℝ) (N : ℕ → Set M) (σ : ℝ → M) (φ : ℕ → ℕ),
      (∀ j, 0 < ρ j) ∧ (∀ j, IsOpen (N j)) ∧ (∀ j, closure (N j) ⊆ (extChartAt I (c j)).source) ∧
      (⋃ j, N j) = univ ∧ IsLimitCurveOf T γ s p σ (Ici 0) φ ∧ σ 0 = p ∧
      ∀ m : ℕ, ArcProp (I := I) c ρ N σ m := by
  classical
  choose ρq hρq Nq hNq hclq hstq using hstep
  obtain ⟨S, hSc, hScov⟩ := TopologicalSpace.countable_cover_nhds (f := fun q => interior (Nq q))
    fun q => interior_mem_nhds.2 (hNq q)
  have hne : S.Nonempty := by
    have : p ∈ ⋃ x ∈ S, interior (Nq x) := by rw [hScov]; exact mem_univ p
    simp only [mem_iUnion] at this
    obtain ⟨x, hx, -⟩ := this
    exact ⟨x, hx⟩
  obtain ⟨c, hc⟩ := hSc.exists_eq_range hne
  have hcov : (⋃ j, interior (Nq (c j))) = univ := by
    rw [← hScov, hc]
    ext x; simp
  have hstep' : ∀ j, StepAt T γ s (c j) (ρq (c j)) (interior (Nq (c j))) := fun j =>
    StepAt.mono T (hstq (c j)) interior_subset
  obtain ⟨φ₀, hφ₀, hp₀⟩ := exists_subseq_isLimitPointOf hp
  obtain ⟨φ₁, σ₁, h₁⟩ := goodState_zero T hcov hstep' hφ₀ hp₀
  -- the sequence of states
  obtain ⟨f, hf, hR⟩ := exists_seq_of_step
    (P := fun n (x : (ℕ → ℕ) × (ℝ → M)) => GoodState T γ s p c (fun j => ρq (c j)) (fun j => interior (Nq (c j))) n x.1 x.2)
    (R := fun n x y => (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ y.1 = x.1 ∘ ψ) ∧
      ∀ u ∈ Icc (0 : ℝ) ((n : ℝ) + 1), y.2 u = x.2 u)
    (φ₁, σ₁) h₁ (fun n x hx => by
      obtain ⟨φ', σ', h', hr1, hr2⟩ := goodState_succ T hcov hstep' hx
      exact ⟨(φ', σ'), h', hr1, hr2⟩)
  have hext : ∀ n : ℕ, ∀ u ∈ Icc (0 : ℝ) ((n : ℝ) + 1), (f (n + 1)).2 u = (f n).2 u := fun n => (hR n).2
  have hψ : ∀ n : ℕ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (f (n + 1)).1 = (f n).1 ∘ ψ := fun n => (hR n).1
  have hcoh : ∀ m n : ℕ, m ≤ n → ∀ u ∈ Icc (0 : ℝ) ((m : ℝ) + 1), (f n).2 u = (f m).2 u := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => intro u _; rfl
    | succ k hk ih =>
      intro u hu
      rw [hext k u ⟨hu.1, hu.2.trans (by exact_mod_cast Nat.add_le_add_right hk 1)⟩]
      exact ih u hu
  have hphi : ∀ m n : ℕ, m ≤ n → ∃ Ψ : ℕ → ℕ, StrictMono Ψ ∧ (f n).1 = (f m).1 ∘ Ψ := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, rfl⟩
    | succ k hk ih =>
      obtain ⟨Ψ, hΨ, he⟩ := ih
      obtain ⟨ψ, hψ', he'⟩ := hψ k
      exact ⟨Ψ ∘ ψ, hΨ.comp hψ', by rw [he', he]; rfl⟩
  obtain ⟨σinf, hσinfdef⟩ : ∃ σinf : ℝ → M, σinf = fun t => (f ⌈t⌉₊).2 t := ⟨_, rfl⟩
  have hσinf : ∀ n : ℕ, ∀ u ∈ Icc (0 : ℝ) ((n : ℝ) + 1), σinf u = (f n).2 u := by
    intro n u hu
    rw [hσinfdef]
    show (f ⌈u⌉₊).2 u = (f n).2 u
    have hm : ⌈u⌉₊ ≤ n + 1 := Nat.ceil_le.2 (by exact_mod_cast hu.2)
    have hum : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    rcases Nat.lt_or_ge ⌈u⌉₊ (n + 1) with h | h
    · exact (hcoh ⌈u⌉₊ n (Nat.lt_succ_iff.1 h) u ⟨hu.1, by linarith⟩).symm
    · have : ⌈u⌉₊ = n + 1 := le_antisymm hm h
      rw [this]
      exact hext n u hu
  have hcurve : IsFutureCausalCurve T σinf (Ici 0) := by
    refine IsCurveWith.of_forall_Icc fun m => ?_
    exact IsCurveWith.congr_on (by positivity) (hf m).2.1 fun u hu => hσinf m u hu
  have hσ0 : σinf 0 = p := by
    rw [hσinf 0 0 ⟨le_rfl, by simp⟩]
    exact (hf 0).2.2.1
  have hdmono : StrictMono fun k => (f k).1 k := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    obtain ⟨ψ, hψ', he⟩ := hψ k
    show (f k).1 k < (f (k + 1)).1 (k + 1)
    rw [he]
    exact (hf k).1 (lt_of_lt_of_le (Nat.lt_succ_self k) (hψ'.id_le (k + 1)))
  have hlimit : ∀ q ∈ σinf '' Ici 0, ∀ U ∈ 𝓝 q, ∀ᶠ k in atTop, ∃ t ∈ s ((f k).1 k), γ ((f k).1 k) t ∈ U := by
    rintro q ⟨u, hu, rfl⟩ U hU
    obtain ⟨n, hn⟩ := exists_nat_ge u
    have hun : u ∈ Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨hu, by linarith⟩
    have hq := (hf n).2.2.2.1 u hun
    rw [← hσinf n u hun] at hq
    obtain ⟨M0, hM0⟩ := eventually_atTop.1 (hq U hU)
    filter_upwards [eventually_ge_atTop (max n M0)] with k hk
    obtain ⟨Ψ, hΨ, he⟩ := hphi n k (le_trans (le_max_left _ _) hk)
    have := hM0 (Ψ k) (le_trans (le_trans (le_max_right _ _) hk) (hΨ.id_le k))
    rw [he]
    exact this
  refine ⟨c, fun j => ρq (c j), fun j => interior (Nq (c j)), σinf, fun k => (f k).1 k, fun j => hρq _,
    fun j => isOpen_interior, fun j => (closure_mono interior_subset).trans (hclq _), hcov,
    ⟨hcurve, ordConnected_Ici, ⟨0, mem_Ici.2 le_rfl⟩, ⟨0, mem_Ici.2 le_rfl, hσ0⟩, hdmono, hlimit⟩, hσ0, ?_⟩
  intro m
  obtain ⟨j, h1, h2, h3, h4⟩ := (hf m).2.2.2.2 m le_rfl
  have hmb : (m : ℝ) + 1 ≤ (m : ℝ) + 1 := le_rfl
  have hm0 : (m : ℝ) ∈ Icc (0 : ℝ) ((m : ℝ) + 1) := ⟨Nat.cast_nonneg m, by linarith⟩
  have hm1 : (m : ℝ) + 1 ∈ Icc (0 : ℝ) ((m : ℝ) + 1) := ⟨by positivity, le_rfl⟩
  refine ⟨j, by rw [hσinf m m hm0]; exact h1, fun j' hj' => h2 j' (by rwa [hσinf m m hm0] at hj'), ?_, ?_⟩
  · intro u hu
    rw [hσinf m u ⟨le_trans (Nat.cast_nonneg m) hu.1, hu.2⟩]
    exact h3 u hu
  · rw [hσinf m _ hm1, hσinf m m hm0]
    exact h4

end Lightlike.Causal
