import Lightlike.GR.MHVRefs
import Lightlike.GR.BCFWFalloffSpinor

/-!
# The shifted amplitude in the good gauge

For the `[0, 1⟩` shift the polarizations with the references `|q] = |1]` (negative legs) and `⟨q'| = ⟨0|` (positive legs)
are entire in `z` (`[1 0̂] = [1 0]`, `⟨0 1̂⟩ = ⟨0 1⟩` do not depend on `z`), which the residue recursion
`bgAmplitude_eq_sum_channels'` requires. The termwise falloff of `BCFWFalloff.lean` is proved for constant generic
references; by the reference independence (`bgAmplitude_refs`) the two amplitudes agree for large `|z|`, so the good-gauge
amplitude also tends to `0`.
-/

open Filter Topology Matrix

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The shifted square spinors `|0̂] = |0] + z|1]`. -/
def lHat (l : ℕ → Fin 2 → ℂ) (z : ℂ) : ℕ → Fin 2 → ℂ := fun t => if t = 0 then l 0 + z • l 1 else l t

/-- The shifted angle spinors `|1̂⟩ = |1⟩ − z|0⟩`. -/
def ltHat (lt : ℕ → Fin 2 → ℂ) (z : ℂ) : ℕ → Fin 2 → ℂ := fun t => if t = 1 then lt 1 - z • lt 0 else lt t

/-- Auxiliary statement `shiftedMom_eq` for the recursion of the true amplitudes. -/
lemma shiftedMom_eq (l lt : ℕ → Fin 2 → ℂ) (z : ℂ) (t : ℕ) :
    shiftedMom l lt z t = nullMom (lHat l z t) (ltHat lt z t) := rfl

/-- Auxiliary statement `shiftedPol_eq` for the recursion of the true amplitudes. -/
lemma shiftedPol_eq (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ) (j : ℕ) (hj : 2 ≤ j) (z : ℂ) (t : ℕ) :
    shiftedPol l lt qs qa j z t =
      polRef (fun t => t = 0 ∨ t = j) (lHat l z) (ltHat lt z) (fun _ => qs) (fun _ => qa) t := by
  unfold shiftedPol polRef lHat ltHat
  by_cases h0 : t = 0
  · subst h0; simp
  · by_cases h1 : t = 1
    · subst h1
      have : ¬ (1 = j) := by omega
      simp [this]
    · by_cases hj' : t = j
      · subst hj'; simp [h0, h1]
      · simp [h0, h1, hj']

/-- Auxiliary statement `eventually_ne_cocompact` for the recursion of the true amplitudes. -/
lemma eventually_ne_cocompact (a : ℂ) : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ a := by
  have := (isCompact_singleton (x := a)).compl_mem_cocompact
  filter_upwards [this] with z hz
  simpa using hz

/-- For large `|z|` all the channel propagators of the shifted kinematics are nonzero. -/
lemma FalloffData.eventually_prop_ne {m : ℕ} {p e : ℂ → ℕ → Fin 4 → ℂ} {r : Fin 4 → ℂ} (h : FalloffData m p e r) :
    ∀ᶠ z in cocompact ℂ, ∀ c d, c < d → d ≤ m + 1 → ¬ (c = 0 ∧ d = m + 1) →
      mdot (momRange (p z) c d) (momRange (p z) c d) ≠ 0 := by
  have hev : ∀ᶠ z : ℂ in cocompact ℂ, ∀ b ∈ Finset.Icc 2 (m + 1),
      z ≠ -(mdot (momRange (p 0) 1 b) (momRange (p 0) 1 b)) / (-2 * mdot (momRange (p 0) 1 b) r) :=
    (Filter.eventually_all_finset _).2 fun b _ => eventually_ne_cocompact _
  filter_upwards [hev] with z hz c d hcd hd hne
  by_cases hc : c = 1
  · subst hc
    have hb : 2 ≤ d := hcd
    rw [h.mdot_one hb z]
    have hs : (-2 : ℂ) * mdot (momRange (p 0) 1 d) r ≠ 0 := mul_ne_zero (by norm_num) (h.hone d hb hd)
    intro h0
    apply hz d (Finset.mem_Icc.2 ⟨hb, hd⟩)
    rw [eq_div_iff hs]
    linear_combination h0
  · rw [h.momRange_const hcd hc z]
    exact h.hother c d hcd hd hc hne

/-- **The falloff in the good gauge**: with the references `|q] = |1]`, `⟨q'| = ⟨0|` (entire polarizations) the shifted
amplitude tends to `0` as well. -/
theorem tendsto_goodGauge (m j : ℕ) (hj : 2 ≤ j) (hjm : j ≤ m + 2) (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ)
    (hq1 : squareBr qs (l 1) ≠ 0) (hq0 : angleBr qa (lt 0) ≠ 0)
    (hone : ∀ b, 2 ≤ b → b ≤ m + 1 →
      mdot (momRange (shiftedMom l lt 0) 1 b) (nullMom (l 1) (lt 0)) ≠ 0)
    (hother : ∀ a b, a < b → b ≤ m + 1 → a ≠ 1 → ¬ (a = 0 ∧ b = m + 1) →
      mdot (momRange (shiftedMom l lt 0) a b) (momRange (shiftedMom l lt 0) a b) ≠ 0)
    (hcons : momRange (shiftedMom l lt 0) 0 (m + 2) = 0)
    (hqsj : squareBr qs (l j) ≠ 0) (hqat : ∀ t, 2 ≤ t → t ≤ m + 2 → t ≠ j → angleBr qa (lt t) ≠ 0)
    (g0 : squareBr (l 1) (l 0) ≠ 0) (gj : squareBr (l 1) (l j) ≠ 0) (g1 : angleBr (lt 0) (lt 1) ≠ 0)
    (gt : ∀ t, 2 ≤ t → t ≤ m + 2 → t ≠ j → angleBr (lt 0) (lt t) ≠ 0) :
    Tendsto (fun z => bgAmplitude m (shiftedMom l lt z) (shiftedPol l lt (l 1) (lt 0) j z)) (cocompact ℂ) (𝓝 0) := by
  have hF := falloffData_spinor m j hj l lt qs qa hq1 hq0 hone hother
  have hgen := tendsto_bgAmplitude_shift m j hj l lt qs qa hq1 hq0 hone hother
  refine hgen.congr' ?_
  filter_upwards [hF.eventually_prop_ne, eventually_ne_cocompact (-squareBr qs (l 0) / squareBr qs (l 1)),
    eventually_ne_cocompact (angleBr qa (lt 1) / angleBr qa (lt 0))] with z hprop hz0 hz1
  have hpz : ∀ t, shiftedMom l lt z t = nullMom (lHat l z t) (ltHat lt z t) := fun t => rfl
  have hconsz : momRange (shiftedMom l lt z) 0 (m + 2) = 0 := by
    rw [hF.momRange_eq z 0 (m + 2)]
    simp [hcons]
  have hgenpol : shiftedPol l lt qs qa j z =
      polRef (fun t => t = 0 ∨ t = j) (lHat l z) (ltHat lt z) (fun _ => qs) (fun _ => qa) :=
    funext fun t => shiftedPol_eq l lt qs qa j hj z t
  have hgoodpol : shiftedPol l lt (l 1) (lt 0) j z =
      polRef (fun t => t = 0 ∨ t = j) (lHat l z) (ltHat lt z) (fun _ => l 1) (fun _ => lt 0) :=
    funext fun t => shiftedPol_eq l lt (l 1) (lt 0) j hj z t
  rw [hgenpol, hgoodpol]
  refine bgAmplitude_refs m _ (lHat l z) (ltHat lt z) _ _ _ _ _ hpz hconsz hprop ?_ ?_
  · intro t ht hneg
    rcases hneg with h0 | hjt
    · subst h0
      simp only [lHat, ltHat, if_true]
      refine ⟨?_, ?_⟩
      · rw [squareBr_add_smul_right]
        intro h
        apply hz0
        rw [eq_div_iff hq1]
        linear_combination h
      · rw [squareBr_add_smul_right]
        have : squareBr (l 1) (l 1) = 0 := by rw [squareBr_eq]; ring
        rw [this]; simpa using g0
    · subst hjt
      have h0 : t ≠ 0 := by omega
      simp only [lHat, if_neg h0]
      exact ⟨hqsj, gj⟩
  · intro t ht hneg
    push_neg at hneg
    by_cases h1 : t = 1
    · subst h1
      simp only [ltHat, if_true]
      refine ⟨?_, ?_⟩
      · rw [angleBr_sub_smul_right]
        intro h
        apply hz1
        rw [eq_div_iff hq0]
        linear_combination (-1 : ℂ) * h
      · rw [angleBr_sub_smul_right]
        have : angleBr (lt 0) (lt 0) = 0 := by rw [angleBr_eq]; ring
        rw [this]; simpa using g1
    · have h2 : 2 ≤ t := by
        have := hneg.1; omega
      simp only [ltHat, if_neg h1]
      exact ⟨hqat t h2 ht hneg.2, gt t h2 ht hneg.2⟩

/-- In the good gauge the polarizations of the shifted kinematics do not depend on `z`. -/
lemma shiftedPol_good_const (j : ℕ) (hj : 2 ≤ j) (l lt : ℕ → Fin 2 → ℂ) (g0 : squareBr (l 1) (l 0) ≠ 0)
    (g1 : angleBr (lt 0) (lt 1) ≠ 0) (z : ℂ) :
    shiftedPol l lt (l 1) (lt 0) j z = shiftedPol l lt (l 1) (lt 0) j 0 := by
  funext t
  unfold shiftedPol
  by_cases h0 : t = 0
  · subst h0
    simp only [if_true, epsMinus, squareBr_add_smul_right]
    have : squareBr (l 1) (l 1) = 0 := by rw [squareBr_eq]; ring
    simp [this]
  · by_cases h1 : t = 1
    · subst h1
      simp only [if_neg h0, if_true, epsPlus, angleBr_sub_smul_right]
      have : angleBr (lt 0) (lt 0) = 0 := by rw [angleBr_eq]; ring
      simp [this]
    · simp [h0, h1]

/-- The shifted polarizations of the good gauge are entire. -/
lemma shiftedPol_good_differentiable (j : ℕ) (hj : 2 ≤ j) (l lt : ℕ → Fin 2 → ℂ)
    (g0 : squareBr (l 1) (l 0) ≠ 0) (g1 : angleBr (lt 0) (lt 1) ≠ 0) (t : ℕ) :
    Differentiable ℂ fun z => shiftedPol l lt (l 1) (lt 0) j z t := by
  have : (fun z => shiftedPol l lt (l 1) (lt 0) j z t) = fun _ => shiftedPol l lt (l 1) (lt 0) j 0 t :=
    funext fun z => by rw [shiftedPol_good_const j hj l lt g0 g1 z]
  rw [this]; exact differentiable_const _

/-- The shifted momenta are entire. -/
lemma shiftedMom_differentiable (l lt : ℕ → Fin 2 → ℂ) (t : ℕ) :
    Differentiable ℂ fun z => shiftedMom l lt z t := by
  have : (fun z => shiftedMom l lt z t) = fun z => shiftedMom l lt 0 t + z • shiftVec (nullMom (l 1) (lt 0)) t := by
    funext z
    unfold shiftedMom shiftVec
    by_cases h0 : t = 0
    · subst h0; simp [nullMom_add_smul_left]
    · by_cases h1 : t = 1
      · subst h1
        simp only [if_neg h0, if_true, one_ne_zero, zero_smul, sub_zero, if_false]
        rw [nullMom_sub_smul_right]
        simp [sub_eq_add_neg]
      · simp [h0, h1]
  rw [this]
  exact (differentiable_const _).add (differentiable_id.smul_const _)

/-- The pole of the channel `[1, d]`: `z_d = −P²/(−2 P·r)`. -/
def zpole (l lt : ℕ → Fin 2 → ℂ) (d : ℕ) : ℂ :=
  -mdot (momRange (shiftedMom l lt 0) 1 d) (momRange (shiftedMom l lt 0) 1 d) /
    (-2 * mdot (momRange (shiftedMom l lt 0) 1 d) (nullMom (l 1) (lt 0)))

/-- The genericity hypotheses of the recursion for the true amplitudes (spinor kinematics, negative gluons `0`, `j`). -/
structure TrueKin (m j : ℕ) (l lt : ℕ → Fin 2 → ℂ) (qs0 qa0 : Fin 2 → ℂ) : Prop where
  /-- The second negative gluon is not adjacent to the first. -/
  hj : 2 ≤ j
  /-- `j` is a gluon. -/
  hjm : j ≤ m + 2
  /-- Generic references for the intermediate falloff. -/
  hq1 : squareBr qs0 (l 1) ≠ 0
  /-- Generic references for the intermediate falloff. -/
  hq0 : angleBr qa0 (lt 0) ≠ 0
  /-- Shifted channels have `P · r ≠ 0`. -/
  hone : ∀ b, 2 ≤ b → b ≤ m + 1 →
    mdot (momRange (shiftedMom l lt 0) 1 b) (nullMom (l 1) (lt 0)) ≠ 0
  /-- The other channels are not on shell. -/
  hother : ∀ a b, a < b → b ≤ m + 1 → a ≠ 1 → ¬ (a = 0 ∧ b = m + 1) →
    mdot (momRange (shiftedMom l lt 0) a b) (momRange (shiftedMom l lt 0) a b) ≠ 0
  /-- Momentum conservation. -/
  hcons : momRange (shiftedMom l lt 0) 0 (m + 2) = 0
  /-- Generic reference brackets. -/
  hqsj : squareBr qs0 (l j) ≠ 0
  /-- Generic reference brackets. -/
  hqat : ∀ t, 2 ≤ t → t ≤ m + 2 → t ≠ j → angleBr qa0 (lt t) ≠ 0
  /-- Good-gauge brackets. -/
  g0 : squareBr (l 1) (l 0) ≠ 0
  /-- Good-gauge brackets. -/
  gj : squareBr (l 1) (l j) ≠ 0
  /-- Good-gauge brackets. -/
  g1 : angleBr (lt 0) (lt 1) ≠ 0
  /-- Good-gauge brackets. -/
  gt : ∀ t, 2 ≤ t → t ≤ m + 2 → t ≠ j → angleBr (lt 0) (lt t) ≠ 0
  /-- The unshifted channel propagators are nonzero. -/
  hP0 : ∀ d, 2 ≤ d → d ≤ m + 1 →
    mdot (momRange (shiftedMom l lt 0) 1 d) (momRange (shiftedMom l lt 0) 1 d) ≠ 0
  /-- The poles are distinct. -/
  hinj : ∀ d d', 2 ≤ d → d ≤ m + 1 → 2 ≤ d' → d' ≤ m + 1 → zpole l lt d = zpole l lt d' → d = d'

/-- Auxiliary statement `polRef_transverse` for the recursion of the true amplitudes. -/
lemma polRef_transverse (neg : ℕ → Prop) [DecidablePred neg] (l lt qS qA : ℕ → Fin 2 → ℂ) (t : ℕ) :
    mdot (polRef neg l lt qS qA t) (nullMom (l t) (lt t)) = 0 := by
  unfold polRef
  by_cases h : neg t
  · rw [if_pos h, mdot_comm]; exact mdot_epsMinus _ _ _
  · rw [if_neg h, mdot_comm]; exact mdot_epsPlus _ _ _

/-- **The on-shell recursion for the true amplitudes in the good gauge**: the amplitude is the sum over the shifted
channels `[1, d]` of the factorized residues. -/
theorem true_recursion (m j : ℕ) (l lt : ℕ → Fin 2 → ℂ) (qs0 qa0 : Fin 2 → ℂ) (K : TrueKin m j l lt qs0 qa0)
    (lP ltP : ℕ → Fin 2 → ℂ)
    (hP : ∀ d, 2 ≤ d → d ≤ m + 1 →
      momRange (shiftedMom l lt (zpole l lt d)) 1 d = nullMom (lP d) (ltP d))
    (hq1 : ∀ d, 2 ≤ d → d ≤ m + 1 → angleBr (lt 0) (ltP d) ≠ 0)
    (hq2 : ∀ d, 2 ≤ d → d ≤ m + 1 → squareBr (l 1) (lP d) ≠ 0) :
    bgAmplitude m (shiftedMom l lt 0) (shiftedPol l lt (l 1) (lt 0) j 0) =
      ∑ d ∈ Finset.Icc 2 (m + 1),
        (1 / mdot (momRange (shiftedMom l lt 0) 1 d) (momRange (shiftedMom l lt 0) 1 d)) *
          channelTerm m (shiftedMom l lt (zpole l lt d)) (shiftedPol l lt (l 1) (lt 0) j (zpole l lt d)) 1 d
            (lP d) (ltP d) (l 1) (lt 0) := by
  classical
  have hF := falloffData_spinor m j K.hj l lt qs0 qa0 K.hq1 K.hq0 K.hone K.hother
  set r := nullMom (l 1) (lt 0) with hr
  set C : Finset (ℕ × ℕ) := (Finset.Icc 2 (m + 1)).image (fun d => (1, d)) with hC
  have hmemC : ∀ x, x ∈ C ↔ x.1 = 1 ∧ 2 ≤ x.2 ∧ x.2 ≤ m + 1 := fun x => by
    simp only [hC, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨d, hd, rfl⟩; exact ⟨rfl, hd⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨x.2, ⟨h2, h3⟩, by ext <;> simp [h1]⟩
  have key := bgAmplitude_eq_sum_channels' m (shiftedMom l lt) (shiftedPol l lt (l 1) (lt 0) j)
    (shiftedMom_differentiable l lt) (shiftedPol_good_differentiable j K.hj l lt K.g0 K.g1) C
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := (hmemC x).1 hx
      exact ⟨by omega, h3, by omega⟩)
    (fun x => -2 * mdot (momRange (shiftedMom l lt 0) 1 x.2) r)
    (fun x => zpole l lt x.2)
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := (hmemC x).1 hx
      exact mul_ne_zero (by norm_num) (K.hone x.2 h2 h3))
    (fun x hx z => by
      obtain ⟨h1, h2, h3⟩ := (hmemC x).1 hx
      rw [h1]; exact hF.mdot_one h2 z)
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := (hmemC x).1 hx
      rw [h1]; exact K.hP0 x.2 h2 h3)
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := (hmemC x).1 hx
      rw [h1]
      have hs : (-2 : ℂ) * mdot (momRange (shiftedMom l lt 0) 1 x.2) r ≠ 0 :=
        mul_ne_zero (by norm_num) (K.hone x.2 h2 h3)
      have hne : mdot (momRange (shiftedMom l lt 0) 1 x.2) r ≠ 0 := K.hone x.2 h2 h3
      unfold zpole
      rw [← hr]
      field_simp
      ring)
    (fun x hx y hy hxy => by
      obtain ⟨h1, h2, h3⟩ := (hmemC x).1 hx
      obtain ⟨h1', h2', h3'⟩ := (hmemC y).1 hy
      have := K.hinj x.2 y.2 h2 h3 h2' h3' hxy
      ext <;> simp [h1, h1', this])
    (fun c d hcd hd hne hnC z => by
      have hc : c ≠ 1 := fun hc1 => hnC ((hmemC (c, d)).2 ⟨hc1, by omega, hd⟩)
      rw [hF.momRange_const hcd hc z]
      exact K.hother c d hcd hd hc hne)
    (tendsto_goodGauge m j K.hj K.hjm l lt qs0 qa0 K.hq1 K.hq0 K.hone K.hother K.hcons K.hqsj K.hqat K.g0 K.gj K.g1 K.gt)
    (fun x => lP x.2) (fun x => ltP x.2) (fun _ => l 1) (fun _ => lt 0)
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := (hmemC x).1 hx
      rw [h1]; exact hP x.2 h2 h3)
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := (hmemC x).1 hx
      exact hq1 x.2 h2 h3)
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := (hmemC x).1 hx
      exact hq2 x.2 h2 h3)
    (fun x hx t ht => by
      show mdot (nullMom _ _) (nullMom _ _) = 0
      exact mdot_nullMom_self _ _)
    (fun x hx => by
      have := hF.momRange_eq (zpole l lt x.2) 0 (m + 2)
      rw [this, K.hcons]; simp)
    (fun x hx t ht => by
      rw [shiftedPol_eq l lt (l 1) (lt 0) j K.hj, shiftedMom_eq]
      exact polRef_transverse _ _ _ _ _ t)
  rw [key, hC, Finset.sum_image (fun a _ b _ h => by simpa using h)]

end Lightlike.SpinorHelicity
