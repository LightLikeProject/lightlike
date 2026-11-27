import Lightlike.TuraevViro.CraneYetterSphereSupport
import Lightlike.TuraevViro.CraneYetterSphereCheck

/-!
# The Crane–Yetter invariant of `S⁴` at `r = 3`

The state sum over the `2³⁵` colourings of `∂Δ⁵` at `r = 3` reduces to the 1024 cone colourings (the support,
`cone_of_ne_zero`), each of weight `1` (`sphere_weight_one`), and `N^{n₀ - n₁} = 2⁻⁹`, so that `craneYetter 3 = 1024 / 512 = 2 = N`.
-/

open Finset Lightlike.Pentagon Lightlike.FourD Lightlike.FourD.Tests

namespace Lightlike.TV

/-- The cone colouring only reads its datum on the triangles through `0`. -/
lemma coneCol_congr {γ γ' : Finset (Fin 6) → ℕ} (h : ∀ f, #f = 3 → 0 ∈ f → γ f = γ' f) (f : Finset (Fin 6)) :
    coneCol γ f = coneCol γ' f := by
  have htri : ∀ g : Finset (Fin 6), #g = 3 → triCol γ g = triCol γ' g := by
    intro g hg
    unfold triCol
    by_cases h0 : 0 ∈ g
    · rw [if_pos h0, if_pos h0]; exact h g hg h0
    · rw [if_neg h0, if_neg h0]
      congr 1
      refine Finset.sum_congr rfl fun e he => ?_
      have hsub := (mem_powersetCard.1 he)
      have h0e : 0 ∉ e := fun h' => h0 (hsub.1 h')
      apply h
      · rw [card_insert_of_notMem h0e, hsub.2]
      · exact mem_insert_self _ _
  unfold coneCol
  by_cases h3 : #f = 3
  · rw [if_pos h3, if_pos h3]; exact htri f h3
  rw [if_neg h3, if_neg h3]
  by_cases h4 : #f = 4
  · rw [if_pos h4, if_pos h4]
    unfold tetCol
    congr 1
    refine Finset.sum_congr rfl fun x hx => htri _ ?_
    rw [card_erase_of_mem (mem_filter.1 hx).1, h4]
  · rw [if_neg h4, if_neg h4]


lemma mem_tris_s6 (f : Finset (Fin 6)) : f ∈ sphere6.tris ↔ #f = 3 := by
  revert f; decide +kernel

lemma mem_tets_s6 (f : Finset (Fin 6)) : f ∈ sphere6.tets ↔ #f = 4 := by
  revert f; decide +kernel

lemma mem_colFaces_s6 (f : Finset (Fin 6)) : f ∈ Lightlike.SpinFoam.colFaces sphere6 ↔ #f = 3 ∨ #f = 4 := by
  unfold Lightlike.SpinFoam.colFaces
  rw [mem_union, mem_tris_s6, mem_tets_s6]

/-- The cone colouring has colours `0, 1` if its datum does. -/
lemma coneCol_le {γ : Finset (Fin 6) → ℕ} (h : ∀ f, #f = 3 → 0 ∈ f → γ f ≤ 1) (f : Finset (Fin 6)) :
    coneCol γ f ≤ 1 := by
  unfold coneCol triCol tetCol
  split_ifs
  · exact h f ‹_› ‹_›
  · exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  · exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  · exact Nat.zero_le _

lemma coneCol_zero_off {γ : Finset (Fin 6) → ℕ} {f : Finset (Fin 6)} (h3 : #f ≠ 3) (h4 : #f ≠ 4) :
    coneCol γ f = 0 := by
  unfold coneCol; rw [if_neg h3, if_neg h4]

lemma coneCol_zero_of_not_mem {γ : Finset (Fin 6) → ℕ} {f : Finset (Fin 6)}
    (h : f ∉ Lightlike.SpinFoam.colFaces sphere6) : coneCol γ f = 0 :=
  coneCol_zero_off (fun h3 => h ((mem_colFaces_s6 f).2 (Or.inl h3))) (fun h4 => h ((mem_colFaces_s6 f).2 (Or.inr h4)))

/-- **The value of a colouring with colours `0, 1` of `∂Δ⁵` whose tetrahedron weights are nonzero and whose cone datum is
`b`**: the weight of the cone colouring is `1`. -/
lemma weight_cone_one (γ : Finset (Fin 6) → ℕ) (hγ : ∀ f, #f = 3 → 0 ∈ f → γ f ≤ 1) (hw : WeightOne γ) :
    craneYetterWeight 3 sphere6 (relSign univ) (coneCol γ) = 1 := by
  rw [craneYetterWeight_three_sphere6 _ (coneCol_le hγ)]
  have h12 : qHalf 3 ^ 12 = 1 := by
    unfold qHalf
    rw [← Complex.exp_nat_mul]
    have : ((12 : ℕ) : ℂ) * (Complex.I * Real.pi / (2 * ((3 : ℕ) : ℂ))) = 2 * Real.pi * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_two_pi_mul_I]
  have h6 : qHalf 3 ^ 6 = -1 := by
    unfold qHalf
    rw [← Complex.exp_nat_mul]
    have : ((6 : ℕ) : ℂ) * (Complex.I * Real.pi / (2 * ((3 : ℕ) : ℂ))) = Real.pi * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_pi_mul_I]
  rcases hw with ⟨hM, hE⟩ | ⟨hM, hE⟩
  · have : sphereE (coneCol γ) = 12 * (sphereE (coneCol γ) / 12) := by omega
    rw [hM, this, zpow_mul]
    norm_num [h12]
  · have : sphereE (coneCol γ) = 12 * (sphereE (coneCol γ) / 12) + 6 := by omega
    rw [hM, this, zpow_add₀ (qHalf_ne_zero 3), zpow_mul]
    norm_num [h12, h6]


lemma extS_lt_gen {V : Type*} [LinearOrder V] {S : Finset (Finset V)} {n : ℕ} (hn : 0 < n) (c : ∀ f ∈ S, ℕ)
    (hc : c ∈ S.pi (fun _ => range n)) (f : Finset V) : Lightlike.PR.extS S c f < n := by
  unfold Lightlike.PR.extS
  split_ifs with h
  · exact mem_range.1 (Finset.mem_pi.1 hc f h)
  · exact hn

lemma extS_of_not_mem_gen {V : Type*} [LinearOrder V] {S : Finset (Finset V)} (c : ∀ f ∈ S, ℕ) {f : Finset V}
    (h : f ∉ S) : Lightlike.PR.extS S c f = 0 := by
  unfold Lightlike.PR.extS; rw [dif_neg h]

lemma extS_of_mem_gen {V : Type*} [LinearOrder V] {S : Finset (Finset V)} (c : ∀ f ∈ S, ℕ) {f : Finset V}
    (h : f ∈ S) : Lightlike.PR.extS S c f = c f h := by
  unfold Lightlike.PR.extS; rw [dif_pos h]

lemma mem_tri0 (f : Finset (Fin 6)) : f ∈ tri0 ↔ #f = 3 ∧ 0 ∈ f := by
  unfold tri0; revert f; decide +kernel

lemma card_tri0 : #tri0 = 10 := by unfold tri0; decide +kernel

lemma n_faces : ((sphere6.faces 0).card : ℤ) - (sphere6.faces 1).card = -9 := by
  have h0 : (sphere6.faces 0).card = 6 := by decide +kernel
  have h1 : (sphere6.faces 1).card = 15 := by decide +kernel
  rw [h0, h1]; norm_num

lemma cyN_three : cyN 3 = 2 := by
  unfold cyN
  have h : Real.sin (Real.pi / ((3 : ℕ) : ℝ)) = Real.sqrt 3 / 2 := by
    rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]; exact Real.sin_pi_div_three
  rw [h, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num


/-- **The Crane–Yetter invariant of the boundary of the 5-simplex at `r = 3` is `2 = N`**: the state sum over all
colourings of the triangles and tetrahedra by `{0, 1}` reduces to the 1024 cone colourings, each of weight `1`, and
`N^{n₀ - n₁} = 2⁻⁹`. -/
theorem craneYetter_sphere_three : craneYetter 3 sphere6 (relSign univ) = 2 := by
  classical
  have hCSm := mem_colFaces_s6
  unfold craneYetter
  generalize Lightlike.SpinFoam.colFaces sphere6 = CS at hCSm ⊢
  set Φ : (∀ f ∈ tri0, ℕ) → (∀ f ∈ CS, ℕ) := fun b f _ => coneCol (Lightlike.PR.extS tri0 b) f with hΦ
  have hdat : ∀ b ∈ tri0.pi (fun _ => range 2), ∀ f, #f = 3 → 0 ∈ f → Lightlike.PR.extS tri0 b f ≤ 1 := by
    intro b hb f hf h0
    have := extS_lt_gen (by norm_num) b hb f
    omega
  have hK2 : ∀ b, Lightlike.PR.extS CS (Φ b) = coneCol (Lightlike.PR.extS tri0 b) := by
    intro b
    funext f
    by_cases hf : f ∈ CS
    · rw [extS_of_mem_gen (Φ b) hf]
    · rw [extS_of_not_mem_gen _ hf]
      symm
      exact coneCol_zero_off (fun h3 => hf ((hCSm f).2 (Or.inl h3))) (fun h4 => hf ((hCSm f).2 (Or.inr h4)))
  have hmemΦ : ∀ b ∈ tri0.pi (fun _ => range 2), Φ b ∈ CS.pi (fun _ => range (3 - 1)) := by
    intro b hb
    rw [Finset.mem_pi]
    intro f hf
    rw [mem_range]
    have := coneCol_le (hdat b hb) f
    show coneCol (Lightlike.PR.extS tri0 b) f < 3 - 1
    omega
  have hK3 : ∀ b ∈ tri0.pi (fun _ => range 2),
      craneYetterWeight 3 sphere6 (relSign univ) (Lightlike.PR.extS CS (Φ b)) = 1 := by
    intro b hb
    rw [hK2 b]
    exact weight_cone_one _ (hdat b hb) (sphere_weight_one b hb)
  have hsupp : ∀ c ∈ CS.pi (fun _ => range (3 - 1)),
      craneYetterWeight 3 sphere6 (relSign univ) (Lightlike.PR.extS CS c) ≠ 0 →
        c ∈ (tri0.pi (fun _ => range 2)).image Φ := by
    intro c hc hne
    set col := Lightlike.PR.extS CS c with hcol
    have hc1 : ∀ f, col f ≤ 1 := fun f => by
      show Lightlike.PR.extS CS c f ≤ 1
      have := extS_lt_gen (by norm_num : 0 < 3 - 1) c hc f
      omega
    have hz : ∀ f, #f ≠ 3 → #f ≠ 4 → col f = 0 := fun f h3 h4 => by
      show Lightlike.PR.extS CS c f = 0
      apply extS_of_not_mem_gen
      intro h
      rcases (hCSm f).1 h with h | h
      · exact h3 h
      · exact h4 h
    rw [craneYetterWeight_three_sphere6 col hc1] at hne
    have hM : ∀ x ∈ tetIdx, tetModel col x.1 x.2 ≠ 0 := by
      intro x hx hx0
      apply hne
      unfold sphereM
      have : ∏ y ∈ tetIdx, tetModel col y.1 y.2 = 0 := Finset.prod_eq_zero hx hx0
      rw [this]
      simp
    have hcone := cone_of_ne_zero col hc1 hz hM
    let b : ∀ f ∈ tri0, ℕ := fun f _ => col f
    have hb : b ∈ tri0.pi (fun _ => range 2) := by
      rw [Finset.mem_pi]
      intro f hf
      rw [mem_range]
      have := hc1 f
      show col f < 2
      omega
    refine Finset.mem_image.2 ⟨b, hb, ?_⟩
    funext f hf
    show coneCol (Lightlike.PR.extS tri0 b) f = c f hf
    have hcongr : coneCol (Lightlike.PR.extS tri0 b) f = coneCol col f :=
      coneCol_congr (fun g hg h0 => by
        have hgT : g ∈ tri0 := (mem_tri0 g).2 ⟨hg, h0⟩
        rw [extS_of_mem_gen b hgT]) f
    rw [hcongr, ← hcone f, hcol, extS_of_mem_gen c hf]
  have hinj : Set.InjOn Φ ↑(tri0.pi (fun _ => range 2)) := by
    intro b hb b' hb' h
    funext f hf
    have hfT := (mem_tri0 f).1 hf
    have e : ∀ b'' : ∀ f ∈ tri0, ℕ, coneCol (Lightlike.PR.extS tri0 b'') f = b'' f hf := by
      intro b''
      unfold coneCol triCol
      rw [if_pos hfT.1, if_pos hfT.2]
      exact extS_of_mem_gen b'' hf
    have := congrFun (congrFun h f) ((hCSm f).2 (Or.inl hfT.1))
    simp only [hΦ] at this
    rw [e b, e b'] at this
    exact this
  have himg : (tri0.pi (fun _ => range 2)).image Φ ⊆ CS.pi (fun _ => range (3 - 1)) := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hc
    exact hmemΦ b hb
  have hsum : ∑ c ∈ CS.pi (fun _ => range (3 - 1)),
      craneYetterWeight 3 sphere6 (relSign univ) (Lightlike.PR.extS CS c) = 1024 := by
    rw [← Finset.sum_subset himg (fun c hc hn => by
      by_contra hne
      exact hn (hsupp c hc hne))]
    rw [Finset.sum_image hinj, Finset.sum_congr rfl hK3]
    simp [Finset.card_pi, card_tri0]
  rw [hsum, n_faces, cyN_three]
  norm_num

end Lightlike.TV
