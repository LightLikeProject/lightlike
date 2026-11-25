import Lightlike.GR.FeynmanFactorization

/-!
# The on-shell recursion for the colour-ordered Feynman amplitudes

* `eq_sum_div_sub_of_residues`: **partial fractions from Liouville's theorem**: a function holomorphic off finitely many
  points, with simple poles there (`(z − c) f(z) → r_c`) and `f → 0` at infinity, is `Σ_c r_c/(z − c)`; in particular
  `f(0) = −Σ_c r_c/c`, Elvang-Huang (3.4) with `B_n = 0`;
* `bgAmplitude_eq_sum_channels`: **the on-shell recursion (3.7)** for the colour-ordered Feynman amplitudes of every
  helicity, for any shift with (3.2)–(3.3), under the large-`z` falloff (3.6).

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697: (3.4)–(3.7), pp. 35–36.
-/

open Filter Topology

noncomputable section

namespace Lightlike.SpinorHelicity

/-- **Partial fractions from Liouville's theorem**: if `f` is holomorphic off a finite set `S`, has at each `c ∈ S` a
simple pole with residue `r c` (`(z − c) f(z) → r c`), and tends to `0` at infinity, then `f z = Σ_{c ∈ S} r c/(z − c)`
off `S`. -/
theorem eq_sum_div_sub_of_residues {f : ℂ → ℂ} (S : Finset ℂ) (r : ℂ → ℂ)
    (hd : ∀ z ∉ S, DifferentiableAt ℂ f z)
    (hres : ∀ c ∈ S, Tendsto (fun z => (z - c) * f z) (𝓝[≠] c) (𝓝 (r c)))
    (hinf : Tendsto f (cocompact ℂ) (𝓝 0)) {z : ℂ} (hz : z ∉ S) :
    f z = ∑ c ∈ S, r c / (z - c) := by
  set g : ℂ → ℂ := fun z => f z - ∑ c ∈ S, r c / (z - c) with hg
  -- `S` is closed, so points off `S` have neighbourhoods off `S`
  have hSc : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
  have hoff : ∀ w ∉ S, ∀ᶠ y in 𝓝 w, y ∉ S := fun w hw =>
    hSc.isOpen_compl.mem_nhds (by simpa using hw)
  have hpunct : ∀ c, ∀ᶠ y in 𝓝[≠] c, y ∉ S \ {c} := by
    intro c
    have : IsClosed ((S \ {c} : Finset ℂ) : Set ℂ) := (S \ {c}).finite_toSet.isClosed
    have hc : c ∉ ((S \ {c} : Finset ℂ) : Set ℂ) := by simp
    exact nhdsWithin_le_nhds (this.isOpen_compl.mem_nhds hc)
  have hgd : ∀ w ∉ S, DifferentiableAt ℂ g w := by
    intro w hw
    refine (hd w hw).sub (DifferentiableAt.fun_sum fun c hc => ?_)
    have : w - c ≠ 0 := sub_ne_zero.2 (fun h => hw (h ▸ hc))
    exact (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) this
  have hgd' : ∀ c, ∀ᶠ y in 𝓝[≠] c, DifferentiableAt ℂ g y := by
    intro c
    filter_upwards [hpunct c, self_mem_nhdsWithin] with y hy hyc
    exact hgd y fun h => hy (Finset.mem_sdiff.2 ⟨h, by simpa using hyc⟩)
  -- each pole is removable for `g`
  have hlim : ∀ c ∈ S, Tendsto g (𝓝[≠] c) (𝓝 (limUnder (𝓝[≠] c) g)) := by
    intro c hc
    refine Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO (hgd' c) ?_
    have h0 : Tendsto (fun z => (z - c) * (g z - g c)) (𝓝[≠] c) (𝓝 0) := by
      have hsplit : ∀ z, (z - c) * g z = (z - c) * f z - r c * ((z - c) / (z - c)) -
          ∑ c' ∈ S.erase c, (z - c) * (r c' / (z - c')) := by
        intro z
        simp only [hg]
        rw [mul_sub, ← Finset.add_sum_erase S _ hc, mul_add, Finset.mul_sum]
        ring
      have h1 : Tendsto (fun z => (z - c) * g z) (𝓝[≠] c) (𝓝 (r c - r c * 1 -
          ∑ c' ∈ S.erase c, (c - c) * (r c' / (c - c')))) := by
        simp only [hsplit]
        refine ((hres c hc).sub (tendsto_const_nhds.mul ?_)).sub (tendsto_finsetSum _ fun c' hc' => ?_)
        · refine tendsto_const_nhds.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with z hz
          rw [div_self (sub_ne_zero.2 hz)]
        · have hne : c - c' ≠ 0 := sub_ne_zero.2 (Finset.ne_of_mem_erase hc').symm
          exact ((((continuous_id.sub continuous_const).continuousAt).mul
            (continuousAt_const.div ((continuous_id.sub continuous_const).continuousAt) hne)).tendsto).mono_left
            nhdsWithin_le_nhds
      simp only [sub_self, zero_mul, Finset.sum_const_zero, mul_one] at h1
      have h2 : Tendsto (fun z => (z - c) * g c) (𝓝[≠] c) (𝓝 0) := by
        have : Tendsto (fun z => (z - c) * g c) (𝓝 c) (𝓝 ((c - c) * g c)) :=
          ((continuous_id.sub continuous_const).mul continuous_const).tendsto c
        simpa using this.mono_left nhdsWithin_le_nhds
      simpa [mul_sub] using h1.sub h2
    rw [Asymptotics.isLittleO_iff_tendsto']
    · refine h0.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [div_inv_eq_mul, mul_comm]
    · filter_upwards [self_mem_nhdsWithin] with z hz h
      exact absurd (inv_eq_zero.1 h) (sub_ne_zero.2 hz)
  -- the extension
  set G : ℂ → ℂ := fun w => if w ∈ S then limUnder (𝓝[≠] w) g else g w with hG
  have hGg : ∀ w ∉ S, G =ᶠ[𝓝 w] g := fun w hw => by
    filter_upwards [hoff w hw] with y hy
    simp [hG, hy]
  have hGg' : ∀ c, G =ᶠ[𝓝[≠] c] g := fun c => by
    filter_upwards [hpunct c, self_mem_nhdsWithin] with y hy hyc
    have : y ∉ S := fun h => hy (Finset.mem_sdiff.2 ⟨h, by simpa using hyc⟩)
    simp [hG, this]
  have hGd : Differentiable ℂ G := by
    intro w
    by_cases hw : w ∈ S
    · have hcont : ContinuousAt G w := by
        rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
        have : G w = limUnder (𝓝[≠] w) g := by simp [hG, hw]
        rw [this]
        exact (hlim w hw).congr' (hGg' w).symm
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hcont).differentiableAt
      filter_upwards [hpunct w, self_mem_nhdsWithin] with y hy hyw
      have hyS : y ∉ S := fun h => hy (Finset.mem_sdiff.2 ⟨h, by simpa using hyw⟩)
      exact (hgd y hyS).congr_of_eventuallyEq (hGg y hyS)
    · exact (hgd w hw).congr_of_eventuallyEq (hGg w hw)
  -- `G → 0` at infinity
  have hterm : ∀ c ∈ S, Tendsto (fun x : ℂ => r c / (x - c)) (cocompact ℂ) (𝓝 0) := by
    intro c _
    have hsub : Tendsto (fun x : ℂ => x - c) (cocompact ℂ) (cocompact ℂ) :=
      (Homeomorph.subRight c).isClosedEmbedding.tendsto_cocompact
    have hinv : Tendsto (fun x : ℂ => (x - c)⁻¹) (cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact] at hsub ⊢
      exact tendsto_inv₀_cobounded.comp hsub
    simpa [div_eq_mul_inv] using hinv.const_mul (r c)
  have hGinf : Tendsto G (cocompact ℂ) (𝓝 0) := by
    have := hinf.sub (tendsto_finsetSum S hterm)
    rw [Finset.sum_const_zero, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [S.finite_toSet.isCompact.compl_mem_cocompact] with y hy
    have : y ∉ S := by simpa using hy
    simp [hG, hg, this]
  have h := hGd.apply_eq_of_tendsto_cocompact z hGinf
  have : G z = g z := by simp [hG, hz]
  rw [this, hg] at h
  exact sub_eq_zero.1 h

/-- The factorized residue of the channel `{i, …, j}` (Elvang-Huang (3.5)):
`Σ_h A_L(…, −P^{−h}) A_R(P^h, …)`, for spinors `|P]`, `⟨P|` of the channel momentum and a reference spinor `q`. -/
def channelTerm (m : ℕ) (p e : ℕ → Fin 4 → ℂ) (i j : ℕ) (lP ltP lq ltq : Fin 2 → ℂ) : ℂ :=
  bgAmplitude (j - i - 1) (leftMom p i j (-momRange p i j)) (leftPol e i j (epsMinus lP (-ltP) lq)) *
      bgAmplitude (m - (j - i)) (collapse p i j (momRange p i j)) (collapse e i j (epsPlus lP ltP ltq)) +
    bgAmplitude (j - i - 1) (leftMom p i j (-momRange p i j)) (leftPol e i j (epsPlus lP (-ltP) ltq)) *
      bgAmplitude (m - (j - i)) (collapse p i j (momRange p i j)) (collapse e i j (epsMinus lP ltP lq))

/-- The large-`z` falloff of the shifted colour-ordered amplitude (Elvang-Huang (3.6)): `Â_n(z) → 0` as
`z → ∞`. It is a hypothesis of `bgAmplitude_eq_sum_channels` and `bgAmplitude_eq_sum_channels'`. The
library does not derive it: Elvang-Huang take it as the input of the recursion (p. 36). -/
def LargeZFalloff (m : ℕ) (p e : ℂ → ℕ → Fin 4 → ℂ) : Prop :=
  Tendsto (fun z => bgAmplitude m (p z) (e z)) (cocompact ℂ) (𝓝 0)

/-- **The on-shell recursion for the colour-ordered Feynman amplitudes** (Elvang-Huang (3.7)): for a holomorphic
one-parameter family of kinematics (a shift) under which the planar channels `C` have `P̂_I²(z) = P_I² + z s_I`
(`s_I ≠ 0`, (3.2)) with distinct poles `z_I` ((3.3)), the other channels have nonvanishing propagators, and
`Â_n(z) → 0` at infinity ((3.6), the input under which Elvang-Huang state the recursion, p. 36),
`A_n = Σ_{I ∈ C} (1/P_I²) Σ_h Â_L(z_I) Â_R(z_I)`, given on-shell, conserved momenta and transverse polarizations at the
poles and the Ward identities of the lower-point amplitudes. -/
theorem bgAmplitude_eq_sum_channels (m : ℕ) (p e : ℂ → ℕ → Fin 4 → ℂ)
    (hp : ∀ t, Differentiable ℂ fun z => p z t) (he : ∀ t, Differentiable ℂ fun z => e z t)
    (C : Finset (ℕ × ℕ)) (hC : ∀ x ∈ C, x.1 < x.2 ∧ x.2 ≤ m + 1 ∧ ¬ (x.1 = 0 ∧ x.2 = m + 1))
    (s zI : ℕ × ℕ → ℂ) (hs : ∀ x ∈ C, s x ≠ 0)
    (hlin : ∀ x ∈ C, ∀ z, mdot (momRange (p z) x.1 x.2) (momRange (p z) x.1 x.2) =
      mdot (momRange (p 0) x.1 x.2) (momRange (p 0) x.1 x.2) + z * s x)
    (hP0 : ∀ x ∈ C, mdot (momRange (p 0) x.1 x.2) (momRange (p 0) x.1 x.2) ≠ 0)
    (hzI : ∀ x ∈ C, mdot (momRange (p 0) x.1 x.2) (momRange (p 0) x.1 x.2) + zI x * s x = 0)
    (hinj : ∀ x ∈ C, ∀ y ∈ C, zI x = zI y → x = y)
    (hfix : ∀ c d, c < d → d ≤ m + 1 → ¬ (c = 0 ∧ d = m + 1) → (c, d) ∉ C → ∀ z,
      mdot (momRange (p z) c d) (momRange (p z) c d) ≠ 0)
    (hinf : LargeZFalloff m p e)
    (lP ltP lq ltq : ℕ × ℕ → Fin 2 → ℂ)
    (hP : ∀ x ∈ C, momRange (p (zI x)) x.1 x.2 = nullMom (lP x) (ltP x))
    (hq1 : ∀ x ∈ C, angleBr (ltq x) (ltP x) ≠ 0) (hq2 : ∀ x ∈ C, squareBr (lq x) (lP x) ≠ 0)
    (hnull : ∀ x ∈ C, ∀ t ≤ m + 2, mdot (p (zI x) t) (p (zI x) t) = 0)
    (hcons : ∀ x ∈ C, momRange (p (zI x)) 0 (m + 2) = 0)
    (htr : ∀ x ∈ C, ∀ t ≤ m + 2, mdot (e (zI x) t) (p (zI x) t) = 0)
    (hW : ∀ m' < m, ∀ j ≤ m' + 2, WardIdentity m' j) :
    bgAmplitude m (p 0) (e 0) = ∑ x ∈ C,
      (1 / mdot (momRange (p 0) x.1 x.2) (momRange (p 0) x.1 x.2)) *
        channelTerm m (p (zI x)) (e (zI x)) x.1 x.2 (lP x) (ltP x) (lq x) (ltq x) := by
  set f : ℂ → ℂ := fun z => bgAmplitude m (p z) (e z) with hf
  set R : ℕ × ℕ → ℂ := fun x => bgAmplitude (m - (x.2 - x.1))
    (collapse (p (zI x)) x.1 x.2 (momRange (p (zI x)) x.1 x.2))
    (collapse (e (zI x)) x.1 x.2 (bgVertexSum (bgCurrent (p (zI x)) (e (zI x))) (p (zI x)) x.1 x.2)) with hR
  have hpole : ∀ x ∈ C, ∀ z, mdot (momRange (p z) x.1 x.2) (momRange (p z) x.1 x.2) = s x * (z - zI x) := by
    intro x hx z
    rw [hlin x hx z]
    linear_combination hzI x hx
  have hzI0 : ∀ x ∈ C, zI x ≠ 0 := by
    intro x hx h
    exact hP0 x hx (by simpa [h] using hzI x hx)
  -- the propagators off the poles, and at a pole all but its own
  have hprop : ∀ z, ∀ c d, c < d → d ≤ m + 1 → ¬ (c = 0 ∧ d = m + 1) → (∀ x ∈ C, x ≠ (c, d) ∨ z ≠ zI x) →
      mdot (momRange (p z) c d) (momRange (p z) c d) ≠ 0 := by
    intro z c d h1 h2 h3 h4
    by_cases hcd : (c, d) ∈ C
    · rw [hpole _ hcd z]
      rcases h4 _ hcd with h | h
      · exact absurd rfl h
      · exact mul_ne_zero (hs _ hcd) (sub_ne_zero.2 h)
    · exact hfix c d h1 h2 h3 hcd z
  set S : Finset ℂ := C.image zI with hS
  set r : ℂ → ℂ := fun c => ∑ x ∈ C.filter (fun x => zI x = c), R x / s x with hr
  have hr_eq : ∀ x ∈ C, r (zI x) = R x / s x := by
    intro x hx
    simp only [hr]
    refine Finset.sum_eq_single_of_mem x (Finset.mem_filter.2 ⟨hx, rfl⟩) fun y hy hyx => ?_
    exact absurd (hinj y (Finset.mem_filter.1 hy).1 x hx (Finset.mem_filter.1 hy).2) hyx
  have hd : ∀ z ∉ S, DifferentiableAt ℂ f z := by
    intro z hz
    refine differentiableAt_bgAmplitude m (fun t => (hp t).differentiableAt) (fun t => (he t).differentiableAt)
      fun c d h1 h2 h3 => hprop z c d h1 h2 h3 fun x hx => Or.inr fun h => hz ?_
    rw [h]; exact Finset.mem_image_of_mem zI hx
  have hres : ∀ c ∈ S, Tendsto (fun z => (z - c) * f z) (𝓝[≠] c) (𝓝 (r c)) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨h1, h2, h3⟩ := hC x hx
    rw [hr_eq x hx]
    refine tendsto_residue_channel m p e h1 h2 (by omega) (hs x hx)
      (fun t => (hp t).continuous.continuousAt) (fun t => (he t).continuous.continuousAt) (hpole x hx)
      fun c d k1 k2 k3 k4 => hprop (zI x) c d k1 k2 k3 fun y hy => ?_
    by_cases hyx : y = x
    · subst hyx; exact Or.inl fun h => k4 (by subst h; exact ⟨rfl, rfl⟩)
    · exact Or.inr fun h => hyx (hinj y hy x hx h.symm)
  have h0S : (0 : ℂ) ∉ S := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Finset.mem_image.1 h
    exact hzI0 x hx hx0
  have key := eq_sum_div_sub_of_residues S r hd hres hinf h0S
  rw [hS, Finset.sum_image fun x hx y hy h => hinj x hx y hy h] at key
  simp only [hf] at key
  rw [key]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨h1, h2, h3⟩ := hC x hx
  rw [hr_eq x hx]
  have hfac := residue_factorization m (p (zI x)) (e (zI x)) h1 h2 (by omega) (lP x) (ltP x) (lq x) (ltq x)
    (hP x hx) (hq1 x hx) (hq2 x hx) (hnull x hx) (hcons x hx) (htr x hx)
    (fun c d k1 k2 k3 k4 => hprop (zI x) c d k1 k2 k3 fun y hy => by
      by_cases hyx : y = x
      · subst hyx; exact Or.inl fun h => k4 (by subst h; exact ⟨rfl, rfl⟩)
      · exact Or.inr fun h => hyx (hinj y hy x hx h.symm))
    (hW _ (by omega) _ (by omega)) (hW _ (by omega) _ (by omega))
  simp only [hR]
  rw [hfac, channelTerm]
  have hsz : s x * zI x = -mdot (momRange (p 0) x.1 x.2) (momRange (p 0) x.1 x.2) := by
    linear_combination hzI x hx
  rw [div_div, show s x * (0 - zI x) = mdot (momRange (p 0) x.1 x.2) (momRange (p 0) x.1 x.2) by
    linear_combination (-1 : ℂ) * hsz]
  ring

end Lightlike.SpinorHelicity
