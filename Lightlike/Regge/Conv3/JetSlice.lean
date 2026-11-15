import Lightlike.Regge.Conv3.JetCore

/-!
# The normal-coordinate slice of the jet-level star identity

`JetStarCore` (in `JetCore`) is the jet-level identity for a general metric jet. Here it is
proved on the slice of normal-coordinate jets: the metric at `m` is the identity, its first
derivatives vanish, and its second derivatives are given by the curvature form
`∂_k ∂_l g_ij = -(1/3) (R_ikjl + R_iljk)` of an algebraic curvature tensor with Ricci tensor `ric`
(`NormalSlice`). On this slice:

* the Gram squared lengths of every incidence are those of the orthoscheme (`incQ_slice`);
* the first-derivative coefficients vanish (`incC_slice`);
* the second-order coefficients are the first variations `kds` of `kuhn_regge_core`
  (`incR_slice`);
* the class angle sums are `2π` (`star_angle_sum`), and the weighted second-order coefficients add
  up to `-(R/2)` (`kuhn_regge_core`), which is `JetStarCore.curvature` when `R` is the scalar
  curvature of the metric (`slice_core`).

So the general hypothesis visibly extends a proved case: the same four statements, on a larger
set of jets.
-/

open Lightlike Real
open scoped Matrix
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

section Slice

variable (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ)
  (ric : Fin 3 → Fin 3 → ℝ)

/-- **A normal-coordinate jet.** The metric at `m` is the identity, its first derivatives vanish,
and its second derivatives are `-(1/3) (R_ikjl + R_iljk)` for the algebraic curvature tensor `Rm`
with Ricci tensor `ric`. -/
structure NormalSlice : Prop where
  /-- The metric at `m` is the identity. -/
  metric : g m = 1
  /-- The first derivatives of the metric vanish at `m`. -/
  first : ∀ k i j, pd k (fun y => g y i j) m = 0
  /-- The second derivatives of the metric are given by the curvature form. -/
  second : ∀ k l i j, pd l (pd k (fun y => g y i j)) m
    = -(1 / 3) * (Rm ric i k j l + Rm ric i l j k)

variable {g m ric}

/-- The Gram part of the edge polynomial is the squared Euclidean length. -/
theorem NormalSlice.edgeQ_eq (H : NormalSlice g m ric) (Δ : Fin 3 → ℝ) :
    edgeQ g m Δ = Δ 0 ^ 2 + Δ 1 ^ 2 + Δ 2 ^ 2 := by
  simp [edgeQ, H.metric, dotProduct, Fin.sum_univ_three]
  ring

/-- The first-derivative part of the edge polynomial vanishes. -/
theorem NormalSlice.edgeC_eq (H : NormalSlice g m ric) (s Δ : Fin 3 → ℝ) :
    edgeC g m s Δ = 0 := by
  have : dmat g m s = 0 := by
    ext i j
    simp [dmat, H.first]
  simp [edgeC, this]

/-- The Christoffel contraction vanishes. -/
theorem NormalSlice.chr_eq (H : NormalSlice g m ric) (u v : Fin 3 → ℝ) : chr g m u v = 0 := by
  ext i
  simp [chr, christoffel, H.first]

/-- The second-order part of the edge polynomial is `-(1/3) Rm(Δ, s, Δ, s)`. -/
theorem NormalSlice.edgeR_eq (H : NormalSlice g m ric) (s Δ : Fin 3 → ℝ) :
    edgeR g m s Δ = -(1 / 3) * Qc ric Δ s := by
  have hd : ∀ u u' : Fin 3 → ℝ, Δ ⬝ᵥ (ddmat g m u u' *ᵥ Δ)
      = -(1 / 3) * ∑ i, ∑ j, ∑ k, ∑ l, u k * u' l * Δ i * Δ j *
        (Rm ric i k j l + Rm ric i l j k) := by
    intro u u'
    simp only [dotProduct, Matrix.mulVec, ddmat, Matrix.of_apply, H.second, Fin.sum_univ_three]
    ring
  simp only [edgeR, H.chr_eq, hd]
  simp [Qc, Fin.sum_univ_three, Rm]
  ring

/-- `Rm` is unchanged when the pair is replaced by the midpoint pair: the quadratic form `Qc` of
`(b - a, (a + b)/2)` equals that of `(a, b)`. -/
theorem Qc_mid (hs : ∀ i j, ric i j = ric j i) (a b : Fin 3 → ℝ) :
    Qc ric (fun i => b i - a i) (fun i => (a i + b i) / 2) = Qc ric a b := by
  rw [Qc_eq ric hs, Qc_eq ric hs]
  simp only [bil, scal, Fin.sum_univ_three]
  rw [hs 1 0, hs 2 0, hs 2 1]
  ring

/-- Sums over the coordinates of a permutation of `perms`. -/
theorem sumsq_perm (σ : Fin 6) (u : Fin 3 → ℝ) :
    ∑ i, u (perms σ i) ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  fin_cases σ <;> simp [perms, Fin.sum_univ_three] <;> ring

/-- On the slice, the Gram squared lengths of every incidence are those of the orthoscheme. -/
theorem NormalSlice.incQ_eq (H : NormalSlice g m ric) (σ h : Fin 6) :
    incQ g m σ h = hbase h := by
  have key : ∀ a b : Fin 4, edgeQ g m (fun i => kpos σ h b i - kpos σ h a i)
      = sqd (kv a) (kv b) := by
    intro a b
    rw [H.edgeQ_eq]
    have := sumsq_perm σ (fun j => kv b j - kv a j)
    simp only [Fin.sum_univ_three] at this
    simp only [kpos, sqd]
    have e : ∀ i, kv b (perms σ i) - (kv (hP h) (perms σ i) + kv (hQ h) (perms σ i)) / 2
        - (kv a (perms σ i) - (kv (hP h) (perms σ i) + kv (hQ h) (perms σ i)) / 2)
        = kv b (perms σ i) - kv a (perms σ i) := fun i => by ring
    simp only [e]
    rw [this]
    ring
  rw [hbase_eq h]
  ext i
  fin_cases i <;> simp [incQ, incVec, key]

/-- On the slice, the `ε³` coefficients vanish. -/
theorem NormalSlice.incC_eq (H : NormalSlice g m ric) (σ h : Fin 6) : incC g m σ h = 0 := by
  ext i
  fin_cases i <;> simp [incC, incVec, H.edgeC_eq]

/-- On the slice, the `ε⁴` coefficients are the first variations `kds` of `kuhn_regge_core`. -/
theorem NormalSlice.incR_eq (H : NormalSlice g m ric) (hs : ∀ i j, ric i j = ric j i)
    (σ h : Fin 6) : incR g m σ h = kds ric σ h := by
  have key : ∀ a b : Fin 4, edgeR g m (fun i => (kpos σ h a i + kpos σ h b i) / 2)
      (fun i => kpos σ h b i - kpos σ h a i) = -Qc ric (kpos σ h a) (kpos σ h b) / 3 := by
    intro a b
    rw [H.edgeR_eq, Qc_mid hs]
    ring
  ext i
  fin_cases i <;> simp [incR, incVec, kds, key]

end Slice

section Star

open Classical in
/-- Every incidence lies in exactly one of the seven edge classes. -/
theorem class_partition (f : Fin 6 → Fin 6 → ℝ) :
    ∑ k, clsSum (dirs k) f = ∑ σ, ∑ h, f σ h := by
  simp only [clsSum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  fin_cases σ <;> fin_cases h <;>
    simp [InClass, dirs, kv, perms, hP, hQ, Fin.sum_univ_succ, Fin.forall_fin_succ]

open Classical in
/-- `clsSum` in the form of `star_angle_sum`. -/
theorem clsSum_eq (w : Fin 3 → ℝ) (f : Fin 6 → Fin 6 → ℝ) :
    clsSum w f = ∑ σ : Fin 6, ∑ h : Fin 6,
      (if kv (hQ h) (perms σ 0) - kv (hP h) (perms σ 0) = w 0 ∧
          kv (hQ h) (perms σ 1) - kv (hP h) (perms σ 1) = w 1 ∧
          kv (hQ h) (perms σ 2) - kv (hP h) (perms σ 2) = w 2 then f σ h else 0) := by
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun h _ => ?_
  by_cases hh : InClass w σ h
  · have h3 := And.intro (hh 0) (And.intro (hh 1) (hh 2))
    simp only [hh, h3, and_self, ite_true]
  · have : ¬ (kv (hQ h) (perms σ 0) - kv (hP h) (perms σ 0) = w 0 ∧
          kv (hQ h) (perms σ 1) - kv (hP h) (perms σ 1) = w 1 ∧
          kv (hQ h) (perms σ 2) - kv (hP h) (perms σ 2) = w 2) := by
      intro hc
      exact hh fun i => by fin_cases i <;> simp [hc.1, hc.2.1, hc.2.2]
    simp only [hh, this, ite_false]

/-- The class angle sum of the orthoscheme is `2π`. -/
theorem clsSum_hang (k : Fin 7) : clsSum (dirs k) (fun _ h => hang h) = 2 * π := by
  rw [clsSum_eq]
  refine star_angle_sum _ _ _ ?_ ?_ ?_ ?_ <;> fin_cases k <;> simp [dirs]

/-- In a class of direction `w`, the squared length of `w` is that of the hinge. -/
theorem inClass_len {w : Fin 3 → ℝ} {σ h : Fin 6} (hw : InClass w σ h) :
    w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = hbase h 0 := by
  have := sumsq_perm σ (fun j => kv (hQ h) j - kv (hP h) j)
  simp only [Fin.sum_univ_three] at this
  rw [hw 0, hw 1, hw 2] at this
  rw [hbase_eq h]
  simp only [sqd, Matrix.cons_val_zero]
  rw [this]
  ring

end Star

section Core

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {m : Fin 3 → ℝ}
  {ric : Fin 3 → Fin 3 → ℝ}

/-- The orthoscheme's squared lengths are admissible. -/
theorem valid_hbase (h : Fin 6) : Valid (hbase h) := by
  have h2 : (1 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  fin_cases h <;> simp [Valid, hbase, Pp, cosSq, Nn] <;> norm_num <;>
    (rw [abs_of_pos (by positivity), inv_lt_one₀ (by positivity)]; exact h2)

/-- **The slice theorem.** For a normal-coordinate jet whose scalar curvature is `scal ric`, the
jet-level star identity `JetStarCore` holds: it is `kuhn_regge_core` and `star_angle_sum`. -/
theorem slice_core (H : NormalSlice g m ric) (hs : ∀ i j, ric i j = ric j i)
    (hscal : scalarCurvature g m = scal ric) : JetStarCore g m where
  valid σ h := by rw [H.incQ_eq]; exact valid_hbase h
  angle_sum k := by
    have : (fun σ h => Dsq (incQ g m σ h)) = fun _ h => hang h := by
      ext σ h
      rw [H.incQ_eq, Dsq, hang_eq]
    rw [this]
    exact clsSum_hang k
  first_order k := by
    have : angC1 g m = fun _ _ => 0 := by
      ext σ h
      simp [angC1, H.incC_eq, Dh, dihSq', Nn', Pp']
    rw [this]
    simp [clsSum]
  curvature := by
    have hang2 : ∀ σ h, angC2 g m σ h
        = dihSq' (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5)
          (kds ric σ h 0) (kds ric σ h 1) (kds ric σ h 2) (kds ric σ h 3) (kds ric σ h 4)
          (kds ric σ h 5) := by
      intro σ h
      simp [angC2, H.incC_eq, H.incR_eq hs, H.incQ_eq, Dh]
    have hw : ∀ k, √(edgeQ g m (dirs k)) * clsSum (dirs k) (angC2 g m)
        = clsSum (dirs k) (fun σ h => √(hbase h 0) * angC2 g m σ h) := by
      intro k
      rw [clsSum, clsSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases hc : InClass (dirs k) σ h
      · simp only [hc, ite_true]
        rw [H.edgeQ_eq, inClass_len hc]
      · simp [hc]
    simp only [hw]
    rw [class_partition]
    have := kuhn_regge_core ric hs
    simp only [hang2]
    rw [this, hscal, H.metric]
    simp
    ring

end Core

section NonVacuity

/-- A derivative of a constant function vanishes. -/
theorem pd_const' (k : Fin 3) (c : ℝ) : pd k (fun _ : Fin 3 → ℝ => c) = fun _ => 0 := by
  ext x; simp [pd]

/-- The Christoffel symbols of the constant identity metric vanish. -/
theorem christoffel_one (i j k : Fin 3) :
    christoffel (fun _ : Fin 3 → ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ)) i j k = fun _ => 0 := by
  ext x; simp [christoffel, pd_const']

/-- Non-vacuity: the constant Euclidean metric is a normal-coordinate jet with `ric = 0`. -/
theorem euclid_slice (m : Fin 3 → ℝ) :
    NormalSlice (fun _ : Fin 3 → ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ)) m (fun _ _ => 0) where
  metric := rfl
  first k i j := by simp [pd]
  second k l i j := by simp [pd_const', pd, Rm, scal]

/-- Non-vacuity of `slice_core`: the flat metric satisfies `JetStarCore`. -/
theorem euclid_core (m : Fin 3 → ℝ) :
    JetStarCore (fun _ : Fin 3 → ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ)) m := by
  refine slice_core (euclid_slice m) (fun _ _ => rfl) ?_
  simp [scalarCurvature, ricci, riemann, christoffel_one, pd, scal]

end NonVacuity

end Lightlike.Regge.Conv3
