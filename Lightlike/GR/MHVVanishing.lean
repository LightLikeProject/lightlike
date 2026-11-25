import Lightlike.GR.FeynmanWard
import Lightlike.GR.MHVTrue

/-!
# Colour-ordered amplitudes whose polarizations share an angle spinor vanish

If every polarization is a bispinor `|X_t]⟨κ|` with the same angle spinor `⟨κ|`, then `ε_s · ε_t ∝ ⟨κκ⟩ = 0`, so every
vertex of the Berends-Giele recursion keeps the form `|X]⟨κ|` and the last contraction `ε · J ∝ ⟨κκ⟩ = 0`
(`bgAmplitude_eq_zero_of_angle`). This proves the vanishing of the all-plus amplitude with the common reference `⟨q|`
and, with the reference changed to the angle spinor of the negative gluon, of the single-minus amplitude.
-/

open Matrix

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The vectors `|X]⟨κ|` with a fixed angle spinor `κ`. -/
def InV (κ : Fin 2 → ℂ) (v : Fin 4 → ℂ) : Prop := ∃ X : Fin 2 → ℂ, v = momOf (vecMulVec X κ)

variable {κ : Fin 2 → ℂ}

/-- Auxiliary statement `momOf_add'` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma momOf_add' (M N : Matrix (Fin 2) (Fin 2) ℂ) : momOf (M + N) = momOf M + momOf N := by
  funext μ
  fin_cases μ <;> simp [momOf] <;> ring

/-- Auxiliary statement `InV.zero` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma InV.zero : InV κ 0 := ⟨0, by
  funext μ; fin_cases μ <;> simp [momOf, vecMulVec_apply]⟩

/-- Auxiliary statement `InV.add` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma InV.add {u v : Fin 4 → ℂ} (hu : InV κ u) (hv : InV κ v) : InV κ (u + v) := by
  obtain ⟨X, rfl⟩ := hu
  obtain ⟨Y, rfl⟩ := hv
  refine ⟨X + Y, ?_⟩
  rw [← momOf_add']
  congr 1
  ext i j; simp [vecMulVec_apply]; ring

/-- Auxiliary statement `InV.smul` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma InV.smul {v : Fin 4 → ℂ} (c : ℂ) (hv : InV κ v) : InV κ (c • v) := by
  obtain ⟨X, rfl⟩ := hv
  refine ⟨c • X, ?_⟩
  rw [← momOf_smul]
  congr 1
  ext i j; simp [vecMulVec_apply]; ring

/-- Auxiliary statement `InV.neg` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma InV.neg {v : Fin 4 → ℂ} (hv : InV κ v) : InV κ (-v) := by
  simpa using hv.smul (-1)

/-- Auxiliary statement `InV.mdot_eq_zero` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma InV.mdot_eq_zero {u v : Fin 4 → ℂ} (hu : InV κ u) (hv : InV κ v) : mdot u v = 0 := by
  obtain ⟨X, rfl⟩ := hu
  obtain ⟨Y, rfl⟩ := hv
  rw [mdot_momOf_vecMulVec]
  have : angleBr κ κ = 0 := by rw [angleBr_eq]; ring
  rw [this]; ring

/-- Auxiliary statement `inV_vertex3` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma inV_vertex3 {a b : Fin 4 → ℂ} (pa pb : Fin 4 → ℂ) (ha : InV κ a) (hb : InV κ b) :
    InV κ (SpinorHelicity.vertex3 a pa b pb) := by
  unfold SpinorHelicity.vertex3
  rw [ha.mdot_eq_zero hb, zero_smul, zero_add]
  exact ((hb.smul _).add (ha.smul _)).smul _

/-- Auxiliary statement `inV_vertex4` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma inV_vertex4 {a b c : Fin 4 → ℂ} (ha : InV κ a) (hb : InV κ b) (hc : InV κ c) : InV κ (SpinorHelicity.vertex4 a b c) := by
  unfold SpinorHelicity.vertex4
  rw [ha.mdot_eq_zero hc, zero_smul]
  exact InV.zero

/-- Auxiliary statement `InV.vertexSum` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma InV.vertexSum {T : ℕ → ℕ → Fin 4 → ℂ} (p : ℕ → Fin 4 → ℂ) (a b : ℕ)
    (hT : ∀ c d, a ≤ c → c ≤ d → d ≤ b → d - c < b - a → InV κ (T c d)) : InV κ (bgVertexSum T p a b) := by
  unfold bgVertexSum
  refine InV.add ?_ ?_
  · refine Finset.sum_induction _ (InV κ) (fun u v => InV.add) InV.zero fun c hc => ?_
    have hc := Finset.mem_Ico.1 hc
    exact inV_vertex3 _ _ (hT a c le_rfl (by omega) (by omega) (by omega)) (hT (c + 1) b (by omega) (by omega) le_rfl (by omega))
  · refine Finset.sum_induction _ (InV κ) (fun u v => InV.add) InV.zero fun c hc => ?_
    refine Finset.sum_induction _ (InV κ) (fun u v => InV.add) InV.zero fun d hd => ?_
    have hc := Finset.mem_Ico.1 hc
    have hd := Finset.mem_Ico.1 hd
    exact inV_vertex4 (hT a c le_rfl (by omega) (by omega) (by omega))
      (hT (c + 1) d (by omega) (by omega) (by omega) (by omega)) (hT (d + 1) b (by omega) (by omega) le_rfl (by omega))

/-- Auxiliary statement `InV.current` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma InV.current (p e : ℕ → Fin 4 → ℂ) (N : ℕ) (he : ∀ t ≤ N, InV κ (e t)) :
    ∀ n a b, b - a ≤ n → a ≤ b → b ≤ N → InV κ (bgCurrent p e a b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab hbN
    rcases Nat.lt_or_ge a b with hlt | hge
    · rw [bgCurrent_of_lt p e hlt]
      refine InV.smul _ (InV.vertexSum p a b fun c d hac hcd hdb hlen => ?_)
      exact ih (d - c) (by omega) c d le_rfl hcd (by omega)
    · have : a = b := le_antisymm hab hge
      subst this
      rw [bgCurrent_self]; exact he a hbN

/-- **Amplitudes whose polarizations share an angle spinor vanish.** -/
theorem bgAmplitude_eq_zero_of_angle (m : ℕ) (p e : ℕ → Fin 4 → ℂ) (κ : Fin 2 → ℂ)
    (he : ∀ t ≤ m + 2, InV κ (e t)) : bgAmplitude m p e = 0 := by
  unfold bgAmplitude
  refine (he (m + 2) le_rfl).mdot_eq_zero (InV.vertexSum p 0 (m + 1) fun c d hac hcd hdb hlen => ?_)
  exact InV.current p e (m + 2) he (d - c) c d le_rfl hcd (by omega)

/-! ### Multilinearity of the amplitude in one polarization -/

/-- Auxiliary statement `bgCurrent_update_out` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma bgCurrent_update_out (p e : ℕ → Fin 4 → ℂ) (j : ℕ) (w : Fin 4 → ℂ) :
    ∀ n a b, b - a ≤ n → a ≤ b → (j < a ∨ b < j) →
      bgCurrent p (Function.update e j w) a b = bgCurrent p e a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab hj
    rcases Nat.lt_or_ge a b with hlt | hge
    · rw [bgCurrent_of_lt p _ hlt, bgCurrent_of_lt p e hlt]
      congr 1
      unfold bgVertexSum
      congr 1
      · refine Finset.sum_congr rfl fun c hc => ?_
        have hc := Finset.mem_Ico.1 hc
        rw [ih (c - a) (by omega) a c le_rfl (by omega) (by omega),
          ih (b - (c + 1)) (by omega) (c + 1) b le_rfl (by omega) (by omega)]
      · refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
        have hc := Finset.mem_Ico.1 hc
        have hd := Finset.mem_Ico.1 hd
        rw [ih (c - a) (by omega) a c le_rfl (by omega) (by omega),
          ih (d - (c + 1)) (by omega) (c + 1) d le_rfl (by omega) (by omega),
          ih (b - (d + 1)) (by omega) (d + 1) b le_rfl (by omega) (by omega)]
    · have : a = b := le_antisymm hab hge
      subst this
      rw [bgCurrent_self, bgCurrent_self, Function.update_of_ne (by omega)]

/-- A map `Fin 4 → ℂ → Fin 4 → ℂ` is additive and homogeneous. -/
def LinMap (f : (Fin 4 → ℂ) → (Fin 4 → ℂ)) : Prop :=
  (∀ u v, f (u + v) = f u + f v) ∧ ∀ (c : ℂ) u, f (c • u) = c • f u

/-- Auxiliary statement `LinMap.add` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma LinMap.add {f g : (Fin 4 → ℂ) → (Fin 4 → ℂ)} (hf : LinMap f) (hg : LinMap g) : LinMap (fun w => f w + g w) :=
  ⟨fun u v => by beta_reduce; rw [hf.1, hg.1]; abel, fun c u => by beta_reduce; rw [hf.2, hg.2, smul_add]⟩

/-- Auxiliary statement `LinMap.sum` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma LinMap.sum {ι : Type*} (s : Finset ι) {f : ι → (Fin 4 → ℂ) → (Fin 4 → ℂ)} (hf : ∀ i ∈ s, LinMap (f i)) :
    LinMap (fun w => ∑ i ∈ s, f i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun u v => by simp, fun c u => by simp⟩
  | insert a s ha ih =>
    have := (hf a (Finset.mem_insert_self _ _)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.sum_insert ha] using this

/-- Auxiliary statement `LinMap.smul_const` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma LinMap.smul_const {f : (Fin 4 → ℂ) → (Fin 4 → ℂ)} (hf : LinMap f) (c : ℂ) : LinMap (fun w => c • f w) :=
  ⟨fun u v => by beta_reduce; rw [hf.1, smul_add], fun d u => by beta_reduce; rw [hf.2, smul_comm]⟩

/-- Auxiliary statement `LinMap.const_zero` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma LinMap.const_zero : LinMap (fun _ => (0 : Fin 4 → ℂ)) := ⟨fun u v => by simp, fun c u => by simp⟩

/-- Auxiliary statement `LinMap.id` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma LinMap.id : LinMap (fun w : Fin 4 → ℂ => w) := ⟨fun u v => rfl, fun c u => rfl⟩

/-- Auxiliary statement `LinMap.vertex3_left` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma LinMap.vertex3_left {f : (Fin 4 → ℂ) → (Fin 4 → ℂ)} (hf : LinMap f) (pa pb b : Fin 4 → ℂ) :
    LinMap (fun w => SpinorHelicity.vertex3 (f w) pa b pb) := by
  unfold SpinorHelicity.vertex3
  refine ⟨fun u v => ?_, fun c u => ?_⟩ <;> beta_reduce
  · simp only [hf.1, mdot_add_left, add_smul, smul_add]; abel
  · simp only [hf.2, mdot_smul_left, smul_smul, smul_add]; module

/-- Auxiliary statement `LinMap.vertex3_right` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma LinMap.vertex3_right {f : (Fin 4 → ℂ) → (Fin 4 → ℂ)} (hf : LinMap f) (pa pb a : Fin 4 → ℂ) :
    LinMap (fun w => SpinorHelicity.vertex3 a pa (f w) pb) := by
  unfold SpinorHelicity.vertex3
  refine ⟨fun u v => ?_, fun c u => ?_⟩ <;> beta_reduce
  · simp only [hf.1, mdot_add_right, mdot_add_left, add_smul, smul_add]; abel
  · simp only [hf.2, mdot_smul_right, mdot_smul_left, smul_smul, smul_add]; module

/-- Auxiliary statement `LinMap.vertex4_first` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma LinMap.vertex4_first {f : (Fin 4 → ℂ) → (Fin 4 → ℂ)} (hf : LinMap f) (b c : Fin 4 → ℂ) :
    LinMap (fun w => SpinorHelicity.vertex4 (f w) b c) := by
  unfold SpinorHelicity.vertex4
  refine ⟨fun u v => ?_, fun d u => ?_⟩ <;> beta_reduce
  · simp only [hf.1, mdot_add_left, add_smul]
  · simp only [hf.2, mdot_smul_left, smul_smul]

/-- Auxiliary statement `LinMap.vertex4_second` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma LinMap.vertex4_second {f : (Fin 4 → ℂ) → (Fin 4 → ℂ)} (hf : LinMap f) (a c : Fin 4 → ℂ) :
    LinMap (fun w => SpinorHelicity.vertex4 a (f w) c) := by
  unfold SpinorHelicity.vertex4
  refine ⟨fun u v => ?_, fun d u => ?_⟩ <;> beta_reduce
  · simp only [hf.1, smul_add]
  · simp only [hf.2]; rw [smul_comm]

/-- Auxiliary statement `LinMap.vertex4_third` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma LinMap.vertex4_third {f : (Fin 4 → ℂ) → (Fin 4 → ℂ)} (hf : LinMap f) (a b : Fin 4 → ℂ) :
    LinMap (fun w => SpinorHelicity.vertex4 a b (f w)) := by
  unfold SpinorHelicity.vertex4
  refine ⟨fun u v => ?_, fun d u => ?_⟩ <;> beta_reduce
  · simp only [hf.1, mdot_add_right, add_smul]
  · simp only [hf.2, mdot_smul_right, smul_smul]

/-- Auxiliary statement `bgVertexSum_update_lin` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma bgVertexSum_update_lin (p e : ℕ → Fin 4 → ℂ) (j a b : ℕ)
    (hsub : ∀ c d, a ≤ c → c ≤ d → d ≤ b → d - c < b - a → c ≤ j → j ≤ d →
      LinMap (fun w => bgCurrent p (Function.update e j w) c d))
    (hab : a < b) (haj : a ≤ j) (hjb : j ≤ b) :
    LinMap (fun w => bgVertexSum (bgCurrent p (Function.update e j w)) p a b) := by
  unfold bgVertexSum
  refine LinMap.add (LinMap.sum _ fun c hc => ?_) (LinMap.sum _ fun c hc => LinMap.sum _ fun d hd => ?_)
  · have hc := Finset.mem_Ico.1 hc
    by_cases hjc : j ≤ c
    · have h2 : ∀ w, bgCurrent p (Function.update e j w) (c + 1) b = bgCurrent p e (c + 1) b := fun w =>
        bgCurrent_update_out p e j w (b - (c + 1)) (c + 1) b le_rfl (by omega) (Or.inl (by omega))
      have := (hsub a c le_rfl (by omega) (by omega) (by omega) haj hjc).vertex3_left (momRange p a c) (momRange p (c + 1) b)
        (bgCurrent p e (c + 1) b)
      simpa only [h2] using this
    · have h1 : ∀ w, bgCurrent p (Function.update e j w) a c = bgCurrent p e a c := fun w =>
        bgCurrent_update_out p e j w (c - a) a c le_rfl (by omega) (Or.inr (by omega))
      have := (hsub (c + 1) b (by omega) (by omega) le_rfl (by omega) (by omega) hjb).vertex3_right (momRange p a c)
        (momRange p (c + 1) b) (bgCurrent p e a c)
      simpa only [h1] using this
  · have hc := Finset.mem_Ico.1 hc
    have hd := Finset.mem_Ico.1 hd
    by_cases hjc : j ≤ c
    · have h2 : ∀ w, bgCurrent p (Function.update e j w) (c + 1) d = bgCurrent p e (c + 1) d := fun w =>
        bgCurrent_update_out p e j w (d - (c + 1)) (c + 1) d le_rfl (by omega) (Or.inl (by omega))
      have h3 : ∀ w, bgCurrent p (Function.update e j w) (d + 1) b = bgCurrent p e (d + 1) b := fun w =>
        bgCurrent_update_out p e j w (b - (d + 1)) (d + 1) b le_rfl (by omega) (Or.inl (by omega))
      have := (hsub a c le_rfl (by omega) (by omega) (by omega) haj hjc).vertex4_first (bgCurrent p e (c + 1) d) (bgCurrent p e (d + 1) b)
      simpa only [h2, h3] using this
    · by_cases hjd : j ≤ d
      · have h1 : ∀ w, bgCurrent p (Function.update e j w) a c = bgCurrent p e a c := fun w =>
          bgCurrent_update_out p e j w (c - a) a c le_rfl (by omega) (Or.inr (by omega))
        have h3 : ∀ w, bgCurrent p (Function.update e j w) (d + 1) b = bgCurrent p e (d + 1) b := fun w =>
          bgCurrent_update_out p e j w (b - (d + 1)) (d + 1) b le_rfl (by omega) (Or.inl (by omega))
        have := (hsub (c + 1) d (by omega) (by omega) (by omega) (by omega) (by omega) hjd).vertex4_second (bgCurrent p e a c)
          (bgCurrent p e (d + 1) b)
        simpa only [h1, h3] using this
      · have h1 : ∀ w, bgCurrent p (Function.update e j w) a c = bgCurrent p e a c := fun w =>
          bgCurrent_update_out p e j w (c - a) a c le_rfl (by omega) (Or.inr (by omega))
        have h2 : ∀ w, bgCurrent p (Function.update e j w) (c + 1) d = bgCurrent p e (c + 1) d := fun w =>
          bgCurrent_update_out p e j w (d - (c + 1)) (c + 1) d le_rfl (by omega) (Or.inr (by omega))
        have := (hsub (d + 1) b (by omega) (by omega) le_rfl (by omega) (by omega) hjb).vertex4_third (bgCurrent p e a c)
          (bgCurrent p e (c + 1) d)
        simpa only [h1, h2] using this

/-- Auxiliary statement `bgCurrent_update_lin` for the vanishing of tree amplitudes with at most one negative gluon. -/
lemma bgCurrent_update_lin (p e : ℕ → Fin 4 → ℂ) (j : ℕ) :
    ∀ n a b, b - a ≤ n → a ≤ j → j ≤ b →
      LinMap (fun w => bgCurrent p (Function.update e j w) a b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn haj hjb
    rcases Nat.lt_or_ge a b with hlt | hge
    · have hrec : (fun w => bgCurrent p (Function.update e j w) a b) = fun w =>
          (1 / mdot (momRange p a b) (momRange p a b)) • bgVertexSum (bgCurrent p (Function.update e j w)) p a b :=
        funext fun w => bgCurrent_of_lt p _ hlt
      rw [hrec]
      refine LinMap.smul_const ?_ _
      unfold bgVertexSum
      refine LinMap.add (LinMap.sum _ fun c hc => ?_) (LinMap.sum _ fun c hc => LinMap.sum _ fun d hd => ?_)
      · have hc := Finset.mem_Ico.1 hc
        by_cases hjc : j ≤ c
        · have h2 : ∀ w, bgCurrent p (Function.update e j w) (c + 1) b = bgCurrent p e (c + 1) b := fun w =>
            bgCurrent_update_out p e j w (b - (c + 1)) (c + 1) b le_rfl (by omega) (Or.inl (by omega))
          have := (ih (c - a) (by omega) a c le_rfl haj hjc).vertex3_left (momRange p a c) (momRange p (c + 1) b)
            (bgCurrent p e (c + 1) b)
          simpa only [h2] using this
        · have h1 : ∀ w, bgCurrent p (Function.update e j w) a c = bgCurrent p e a c := fun w =>
            bgCurrent_update_out p e j w (c - a) a c le_rfl (by omega) (Or.inr (by omega))
          have := (ih (b - (c + 1)) (by omega) (c + 1) b le_rfl (by omega) hjb).vertex3_right (momRange p a c)
            (momRange p (c + 1) b) (bgCurrent p e a c)
          simpa only [h1] using this
      · have hc := Finset.mem_Ico.1 hc
        have hd := Finset.mem_Ico.1 hd
        by_cases hjc : j ≤ c
        · have h2 : ∀ w, bgCurrent p (Function.update e j w) (c + 1) d = bgCurrent p e (c + 1) d := fun w =>
            bgCurrent_update_out p e j w (d - (c + 1)) (c + 1) d le_rfl (by omega) (Or.inl (by omega))
          have h3 : ∀ w, bgCurrent p (Function.update e j w) (d + 1) b = bgCurrent p e (d + 1) b := fun w =>
            bgCurrent_update_out p e j w (b - (d + 1)) (d + 1) b le_rfl (by omega) (Or.inl (by omega))
          have := (ih (c - a) (by omega) a c le_rfl haj hjc).vertex4_first (bgCurrent p e (c + 1) d) (bgCurrent p e (d + 1) b)
          simpa only [h2, h3] using this
        · by_cases hjd : j ≤ d
          · have h1 : ∀ w, bgCurrent p (Function.update e j w) a c = bgCurrent p e a c := fun w =>
              bgCurrent_update_out p e j w (c - a) a c le_rfl (by omega) (Or.inr (by omega))
            have h3 : ∀ w, bgCurrent p (Function.update e j w) (d + 1) b = bgCurrent p e (d + 1) b := fun w =>
              bgCurrent_update_out p e j w (b - (d + 1)) (d + 1) b le_rfl (by omega) (Or.inl (by omega))
            have := (ih (d - (c + 1)) (by omega) (c + 1) d le_rfl (by omega) hjd).vertex4_second (bgCurrent p e a c)
              (bgCurrent p e (d + 1) b)
            simpa only [h1, h3] using this
          · have h1 : ∀ w, bgCurrent p (Function.update e j w) a c = bgCurrent p e a c := fun w =>
              bgCurrent_update_out p e j w (c - a) a c le_rfl (by omega) (Or.inr (by omega))
            have h2 : ∀ w, bgCurrent p (Function.update e j w) (c + 1) d = bgCurrent p e (c + 1) d := fun w =>
              bgCurrent_update_out p e j w (d - (c + 1)) (c + 1) d le_rfl (by omega) (Or.inr (by omega))
            have := (ih (b - (d + 1)) (by omega) (d + 1) b le_rfl (by omega) hjb).vertex4_third (bgCurrent p e a c)
              (bgCurrent p e (c + 1) d)
            simpa only [h1, h2] using this
    · have : a = b := le_antisymm (by omega) hge
      subst this
      have : j = a := by omega
      subst this
      have h : (fun w => bgCurrent p (Function.update e j w) j j) = fun w => w :=
        funext fun w => by rw [bgCurrent_self, Function.update_self]
      rw [h]; exact LinMap.id

/-- The amplitude is additive and homogeneous in the polarization of any one leg. -/
lemma bgAmplitude_update_lin (m : ℕ) (p e : ℕ → Fin 4 → ℂ) {j : ℕ} (hj : j ≤ m + 2) :
    (∀ u v, bgAmplitude m p (Function.update e j (u + v)) =
        bgAmplitude m p (Function.update e j u) + bgAmplitude m p (Function.update e j v)) ∧
    ∀ (c : ℂ) u, bgAmplitude m p (Function.update e j (c • u)) = c * bgAmplitude m p (Function.update e j u) := by
  by_cases hjl : j = m + 2
  · subst hjl
    have hV : ∀ w, bgVertexSum (bgCurrent p (Function.update e (m + 2) w)) p 0 (m + 1) =
        bgVertexSum (bgCurrent p e) p 0 (m + 1) := fun w => by
      refine bgVertexSum_congr p 0 (m + 1) fun c d _ hcd hdb _ => ?_
      exact bgCurrent_update_out p e (m + 2) w (d - c) c d le_rfl hcd (Or.inr (by omega))
    refine ⟨fun u v => ?_, fun c u => ?_⟩
    · simp only [bgAmplitude, hV, Function.update_self, mdot_add_left]
    · simp only [bgAmplitude, hV, Function.update_self, mdot_smul_left]
  · have hjm : j ≤ m + 1 := by omega
    have hlin : LinMap (fun w => bgVertexSum (bgCurrent p (Function.update e j w)) p 0 (m + 1)) :=
      bgVertexSum_update_lin p e j 0 (m + 1)
        (fun c d _ hcd hdb _ hcj hjd => bgCurrent_update_lin p e j (d - c) c d le_rfl hcj hjd)
        (by omega) (by omega) hjm
    refine ⟨fun u v => ?_, fun c u => ?_⟩
    · simp only [bgAmplitude, Function.update_of_ne (Ne.symm hjl) , hlin.1, mdot_add_right]
    · simp only [bgAmplitude, Function.update_of_ne (Ne.symm hjl), hlin.2, mdot_smul_right]

/-- **Gauge invariance**: adding a multiple of the momentum to the polarization of a leg does not change the amplitude
(from the Ward identity). -/
theorem bgAmplitude_update_add_mom (m : ℕ) (p e : ℕ → Fin 4 → ℂ) {j : ℕ} (hj : j ≤ m + 2)
    (hnull : ∀ t ≤ m + 2, mdot (p t) (p t) = 0) (hcons : momRange p 0 (m + 2) = 0)
    (hprop : ∀ c d, c < d → d ≤ m + 1 → ¬ (c = 0 ∧ d = m + 1) →
      mdot (momRange p c d) (momRange p c d) ≠ 0)
    (htr : ∀ t ≤ m + 2, t ≠ j → mdot (e t) (p t) = 0) (c : ℂ) :
    bgAmplitude m p (Function.update e j (e j + c • p j)) = bgAmplitude m p e := by
  have h := bgAmplitude_update_lin m p e hj
  have hw : bgAmplitude m p (Function.update e j (p j)) = 0 := ward_all m j hj p e hnull hcons hprop htr
  have : bgAmplitude m p (Function.update e j (e j)) = bgAmplitude m p e := by
    rw [Function.update_eq_self]
  rw [h.1, h.2, hw, this]; ring

/-- The positive-helicity polarization `ε₊(p; q)` has the angle spinor `⟨q|`. -/
lemma inV_epsPlus (l lt ltq : Fin 2 → ℂ) : InV ltq (epsPlus l lt ltq) :=
  ⟨(((Real.sqrt 2 : ℝ) : ℂ) / angleBr ltq lt) • l, by
    rw [epsPlus]
    congr 1
    ext i j; simp [vecMulVec_apply]; ring⟩

/-- The negative-helicity polarization `ε₋(p; q)` has the angle spinor `⟨p|`. -/
lemma inV_epsMinus (l lt lq : Fin 2 → ℂ) : InV lt (epsMinus l lt lq) :=
  ⟨(((Real.sqrt 2 : ℝ) : ℂ) / squareBr lq l) • lq, by
    rw [epsMinus]
    congr 1
    ext i j; simp [vecMulVec_apply]; ring⟩

/-- **The all-plus amplitude vanishes** (common reference spinor). -/
theorem bgAmplitude_allPlus (m : ℕ) (p : ℕ → Fin 4 → ℂ) (l lt : ℕ → Fin 2 → ℂ) (qa : Fin 2 → ℂ) :
    bgAmplitude m p (fun t => epsPlus (l t) (lt t) qa) = 0 :=
  bgAmplitude_eq_zero_of_angle m p _ qa fun t _ => inV_epsPlus _ _ _

/-- **The single-minus amplitude vanishes**: negative gluon `k` (reference `|q]`), all others positive (reference `⟨q'|`),
for conserved null kinematics and nonvanishing propagators. -/
theorem bgAmplitude_oneMinus (m : ℕ) (k : ℕ) (hk : k ≤ m + 2) (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ)
    (p e : ℕ → Fin 4 → ℂ) (hp : ∀ t ≤ m + 2, p t = nullMom (l t) (lt t))
    (he : ∀ t ≤ m + 2, e t = if t = k then epsMinus (l t) (lt t) qs else epsPlus (l t) (lt t) qa)
    (hcons : momRange p 0 (m + 2) = 0)
    (hprop : ∀ c d, c < d → d ≤ m + 1 → ¬ (c = 0 ∧ d = m + 1) →
      mdot (momRange p c d) (momRange p c d) ≠ 0)
    (hqa : ∀ t ≤ m + 2, t ≠ k → angleBr qa (lt t) ≠ 0)
    (hkt : ∀ t ≤ m + 2, t ≠ k → angleBr (lt k) (lt t) ≠ 0) :
    bgAmplitude m p e = 0 := by
  classical
  have hnull : ∀ t ≤ m + 2, mdot (p t) (p t) = 0 := fun t ht => by rw [hp t ht]; exact mdot_nullMom_self _ _
  set eS : Finset ℕ → ℕ → Fin 4 → ℂ := fun S t => if t ∈ S then epsPlus (l t) (lt t) (lt k) else e t with heS
  have htrS : ∀ S : Finset ℕ, ∀ s ≤ m + 2, mdot (eS S s) (p s) = 0 := fun S s hs0 => by
    simp only [heS]
    by_cases hs : s ∈ S
    · rw [if_pos hs, hp s hs0, mdot_comm]; exact mdot_epsPlus _ _ _
    · rw [if_neg hs, he s hs0, hp s hs0]
      by_cases hsk : s = k
      · rw [if_pos hsk, mdot_comm]; exact mdot_epsMinus _ _ _
      · rw [if_neg hsk, mdot_comm]; exact mdot_epsPlus _ _ _
  have key : ∀ S : Finset ℕ, (∀ t ∈ S, t ≤ m + 2 ∧ t ≠ k) → bgAmplitude m p (eS S) = bgAmplitude m p e := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; congr 1
    | insert t S ht ih =>
      intro hS
      have ht' := hS t (Finset.mem_insert_self _ _)
      have ih' := ih fun s hs => hS s (Finset.mem_insert_of_mem hs)
      have hsub := epsPlus_sub_epsPlus (l t) (lt t) qa (lt k) (hqa t ht'.1 ht'.2) (hkt t ht'.1 ht'.2)
      have hnew : eS (insert t S) = Function.update (eS S) t (eS S t + (-((Real.sqrt 2 : ℝ) : ℂ) * angleBr qa (lt k) / (angleBr qa (lt t) * angleBr (lt k) (lt t))) • p t) := by
        funext s
        by_cases hst : s = t
        · subst hst
          simp only [heS, Finset.mem_insert_self, if_true, Function.update_self, ht, if_false]
          rw [he s ht'.1, if_neg ht'.2, hp s ht'.1, ← hsub]; abel
        · simp only [heS, Finset.mem_insert, hst, false_or, Function.update_of_ne hst]
      rw [hnew, bgAmplitude_update_add_mom m p (eS S) ht'.1 hnull hcons hprop (fun s hs0 _ => htrS S s hs0), ih']
  have hS : ∀ t ∈ (Finset.range (m + 3)).erase k, t ≤ m + 2 ∧ t ≠ k := fun t ht => by
    have := Finset.mem_erase.1 ht
    exact ⟨by have := Finset.mem_range.1 this.2; omega, this.1⟩
  rw [← key _ hS]
  refine bgAmplitude_eq_zero_of_angle m p _ (lt k) fun t ht => ?_
  simp only [heS]
  by_cases htk : t = k
  · subst htk
    have : t ∉ (Finset.range (m + 3)).erase t := by simp
    rw [if_neg this, he t ht, if_pos rfl]; exact inV_epsMinus _ _ _
  · have : t ∈ (Finset.range (m + 3)).erase k := Finset.mem_erase.2 ⟨htk, Finset.mem_range.2 (by omega)⟩
    rw [if_pos this]; exact inV_epsPlus _ _ _

end Lightlike.SpinorHelicity
