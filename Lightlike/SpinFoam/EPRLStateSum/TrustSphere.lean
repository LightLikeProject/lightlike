import Lightlike.SpinFoam.EPRLStateSum.ComplexIntrinsicAmp
import Lightlike.SpinFoam.EPRLStateSum.SimplexOoguri
import Lightlike.SpinFoam.Tests
import Lightlike.FourD.Tests
import Lightlike.SpinFoam.EPRLStateSum.BFPoint

/-!
# A trust check on the boundary of the 5-simplex: the "bone" colouring

On `∂Δ⁵ = sphere6` (6 four-simplices, 15 tetrahedra, 20 triangles) the *bone colouring* gives the doubled spin `1`
to the four triangles through the edge `{0,1}` and the virtual spin `1` to the six tetrahedra through it, `0` to all the
other faces. The four 4-simplices through the edge have the data `triJ`, `triK` of `ampP_tri` (value `1/√2`), the two
others carry the zero colouring (value `1`).
-/

open Finset Lightlike.FourD Lightlike.SpinFoam Lightlike.FourD.Tests Lightlike.Spin4

namespace Lightlike.SpinFoam.EPRLStateSum.Trust

/-- The bone colouring of `∂Δ⁵`: `1` on the triangles and tetrahedra through the edge `{0,1}`. -/
def col0 : Finset (Fin 6) → ℕ := fun f => if {0, 1} ⊆ f ∧ 3 ≤ #f ∧ #f ≤ 4 then 1 else 0

/-- A simplex without the edge `{0,1}` carries the zero colouring. -/
lemma simpW_col0_of_not_sub {s : Finset (Fin 6)} (hs : #s = 5) (h : ¬ {0, 1} ⊆ s) :
    simpW col0 s = 1 := by
  have hz : ∀ f ⊆ s, col0 f = 0 := fun f hf => by
    unfold col0
    rw [if_neg]
    intro ⟨h1, _⟩
    exact h (h1.trans hf)
  unfold simpW
  rw [dif_pos hs, vertexAmp_eq_ampP]
  have e1 : simplexJ s hs col0 = fun _ _ => 0 := by
    funext p q
    exact hz _ ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
  have e2 : (fun i => col0 (s.erase (s.orderEmbOfFin hs i))) = fun _ => 0 := by
    funext i
    exact hz _ (Finset.erase_subset _ _)
  rw [e1, e2]
  exact ampP_zero

/-- The simplex `{0, 1, 2, 3, 4}`. -/
def S1 : Finset (Fin 6) := {0, 1, 2, 3, 4}

lemma S1_card : #S1 = 5 := by decide

lemma S1_emb (k : Fin 5) : S1.orderEmbOfFin S1_card k = ![(0 : Fin 6), 1, 2, 3, 4] k := by
  have := Finset.orderEmbOfFin_unique S1_card (f := ![(0 : Fin 6), 1, 2, 3, 4])
    (fun k => by revert k; decide) (by decide)
  exact (congrFun this k).symm

lemma simpW_col0_S1 : simpW col0 S1 = 1 / Real.sqrt 2 := by
  unfold simpW
  rw [dif_pos S1_card, vertexAmp_eq_ampP]
  have e1 : simplexJ S1 S1_card col0 = Lightlike.SpinFoam.triJ := by
    funext p q
    unfold simplexJ
    rw [S1_emb, S1_emb]
    fin_cases p <;> fin_cases q <;> simp [col0, Lightlike.SpinFoam.triJ, S1] <;> decide
  have e2 : (fun i => col0 (S1.erase (S1.orderEmbOfFin S1_card i))) = Lightlike.SpinFoam.triK := by
    funext i
    rw [S1_emb]
    fin_cases i <;> simp [col0, Lightlike.SpinFoam.triK, S1] <;> decide
  rw [e1, e2]
  exact Lightlike.SpinFoam.ampP_tri
/-- The simplex `{0, 1, 2, 3, 5}`. -/
def S2 : Finset (Fin 6) := {0, 1, 2, 3, 5}

lemma S2_card : #S2 = 5 := by decide

lemma S2_emb (k : Fin 5) : S2.orderEmbOfFin S2_card k = ![(0 : Fin 6), 1, 2, 3, 5] k := by
  have := Finset.orderEmbOfFin_unique S2_card (f := ![(0 : Fin 6), 1, 2, 3, 5])
    (fun k => by revert k; decide) (by decide)
  exact (congrFun this k).symm

lemma simpW_col0_S2 : simpW col0 S2 = 1 / Real.sqrt 2 := by
  unfold simpW
  rw [dif_pos S2_card, vertexAmp_eq_ampP]
  have e1 : simplexJ S2 S2_card col0 = Lightlike.SpinFoam.triJ := by
    funext p q
    unfold simplexJ
    rw [S2_emb, S2_emb]
    fin_cases p <;> fin_cases q <;> simp [col0, Lightlike.SpinFoam.triJ, S2] <;> decide
  have e2 : (fun i => col0 (S2.erase (S2.orderEmbOfFin S2_card i))) = Lightlike.SpinFoam.triK := by
    funext i
    rw [S2_emb]
    fin_cases i <;> simp [col0, Lightlike.SpinFoam.triK, S2] <;> decide
  rw [e1, e2]
  exact Lightlike.SpinFoam.ampP_tri
/-- The simplex `{0, 1, 2, 4, 5}`. -/
def S3 : Finset (Fin 6) := {0, 1, 2, 4, 5}

lemma S3_card : #S3 = 5 := by decide

lemma S3_emb (k : Fin 5) : S3.orderEmbOfFin S3_card k = ![(0 : Fin 6), 1, 2, 4, 5] k := by
  have := Finset.orderEmbOfFin_unique S3_card (f := ![(0 : Fin 6), 1, 2, 4, 5])
    (fun k => by revert k; decide) (by decide)
  exact (congrFun this k).symm

lemma simpW_col0_S3 : simpW col0 S3 = 1 / Real.sqrt 2 := by
  unfold simpW
  rw [dif_pos S3_card, vertexAmp_eq_ampP]
  have e1 : simplexJ S3 S3_card col0 = Lightlike.SpinFoam.triJ := by
    funext p q
    unfold simplexJ
    rw [S3_emb, S3_emb]
    fin_cases p <;> fin_cases q <;> simp [col0, Lightlike.SpinFoam.triJ, S3] <;> decide
  have e2 : (fun i => col0 (S3.erase (S3.orderEmbOfFin S3_card i))) = Lightlike.SpinFoam.triK := by
    funext i
    rw [S3_emb]
    fin_cases i <;> simp [col0, Lightlike.SpinFoam.triK, S3] <;> decide
  rw [e1, e2]
  exact Lightlike.SpinFoam.ampP_tri
/-- The simplex `{0, 1, 3, 4, 5}`. -/
def S4 : Finset (Fin 6) := {0, 1, 3, 4, 5}

lemma S4_card : #S4 = 5 := by decide

lemma S4_emb (k : Fin 5) : S4.orderEmbOfFin S4_card k = ![(0 : Fin 6), 1, 3, 4, 5] k := by
  have := Finset.orderEmbOfFin_unique S4_card (f := ![(0 : Fin 6), 1, 3, 4, 5])
    (fun k => by revert k; decide) (by decide)
  exact (congrFun this k).symm

lemma simpW_col0_S4 : simpW col0 S4 = 1 / Real.sqrt 2 := by
  unfold simpW
  rw [dif_pos S4_card, vertexAmp_eq_ampP]
  have e1 : simplexJ S4 S4_card col0 = Lightlike.SpinFoam.triJ := by
    funext p q
    unfold simplexJ
    rw [S4_emb, S4_emb]
    fin_cases p <;> fin_cases q <;> simp [col0, Lightlike.SpinFoam.triJ, S4] <;> decide
  have e2 : (fun i => col0 (S4.erase (S4.orderEmbOfFin S4_card i))) = Lightlike.SpinFoam.triK := by
    funext i
    rw [S4_emb]
    fin_cases i <;> simp [col0, Lightlike.SpinFoam.triK, S4] <;> decide
  rw [e1, e2]
  exact Lightlike.SpinFoam.ampP_tri

/-- The simplex without the vertex `0`. -/
def N0 : Finset (Fin 6) := univ.erase 0

/-- The simplex without the vertex `1`. -/
def N1 : Finset (Fin 6) := univ.erase 1

lemma sphere6_simps :
    sphere6.simps = {S1, S2, S3, S4, N0, N1} := by
  unfold sphere6 Complex4.sphere S1 S2 S3 S4 N0 N1
  decide +kernel

/-- The bone colouring gives spin `1` to exactly four triangles. -/
lemma tris_col0_card : (sphere6.tris.filter (fun f => col0 f = 1)).card = 4 := by
  unfold col0
  decide +kernel

lemma prod_tris_col0 : (∏ f ∈ sphere6.tris, ((col0 f : ℝ) + 1)) = 16 := by
  have h01 : ∀ f, col0 f = 0 ∨ col0 f = 1 := fun f => by
    unfold col0; split_ifs <;> simp
  have h : ∀ f ∈ sphere6.tris, ((col0 f : ℝ) + 1) = if col0 f = 1 then 2 else 1 := by
    intro f _
    rcases h01 f with h | h <;> simp [h]
    norm_num
  rw [Finset.prod_congr rfl h, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    tris_col0_card]
  norm_num

lemma N0_card : #N0 = 5 := by decide
lemma N1_card : #N1 = 5 := by decide

lemma simpW_col0_N0 : simpW col0 N0 = 1 :=
  simpW_col0_of_not_sub N0_card (by decide)

lemma simpW_col0_N1 : simpW col0 N1 = 1 :=
  simpW_col0_of_not_sub N1_card (by decide)

/-- **The Ooguri weight of the bone colouring of `∂Δ⁵` is `4`**: `2⁴` from the four triangles, `(1/√2)⁴` from
the four vertices through the edge. -/
theorem weight_col0 : weight sphere6 col0 = 4 := by
  unfold weight
  rw [prod_tris_col0, sphere6_simps, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, simpW_col0_S1, simpW_col0_S2, simpW_col0_S3, simpW_col0_S4,
    simpW_col0_N0, simpW_col0_N1]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2' : (Real.sqrt 2) ^ 4 = 4 := by nlinarith [h2]
  field_simp
  nlinarith [h2, h2']


/-! ### The positional EPRL weight at `γ = 1` vanishes on the bone triangles -/

lemma trisS1 (col : Finset (Fin 6) → ℕ) (hcol : ∀ f ∈ sphere6.tris, col f = col0 f) :
    EPRL.triSpins S1 S1_card col = ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1] := by
  funext e
  unfold EPRL.triSpins
  fin_cases e <;> simp [EPRL.epair, S1_emb] <;> (rw [hcol _ (by decide +kernel)]; decide +kernel)

lemma S1_pos3 (col : Finset (Fin 6) → ℕ) (hcol : ∀ f ∈ sphere6.tris, col f = col0 f)
    (h : EPRL.simpE 1 col S1 ≠ 0) : col {0, 1, 2, 4} = 1 := by
  have hb : IsVertexBoundary (EPRL.triSpins S1 S1_card col) 0 (EPRL.tetLabels S1 S1_card col) := by
    by_contra hbn
    apply h
    unfold EPRL.simpE
    rw [dif_pos S1_card]
    have hN : (fun e => EPRL.eprlN 1 (EPRL.triSpins S1 S1_card col e)) = EPRL.triSpins S1 S1_card col := by
      funext e; exact EPRL.eprlN_one _
    have hM : (fun e => EPRL.eprlM 1 (EPRL.triSpins S1 S1_card col e)) = 0 := by
      funext e; exact EPRL.eprlM_one _
    rw [hN, hM, if_neg (fun hh => hbn hh.2)]
  have h3 := hb 3
  rw [trisS1 col hcol] at h3
  simp only [k5Spins, Pi.zero_apply, add_zero] at h3
  have e3 : EPRL.tetLabels S1 S1_card col 3 = col {0, 1, 2, 4} := by
    unfold EPRL.tetLabels
    rw [S1_emb]
    have : S1.erase (![(0 : Fin 6), 1, 2, 3, 4] 3) = {0, 1, 2, 4} := by decide +kernel
    rw [this]
  rw [e3] at h3
  simp [mem_channel, Lightlike.Pentagon.Tri] at h3
  omega

lemma trisS3 (col : Finset (Fin 6) → ℕ) (hcol : ∀ f ∈ sphere6.tris, col f = col0 f) :
    EPRL.triSpins S3 S3_card col = ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1] := by
  funext e
  unfold EPRL.triSpins
  fin_cases e <;> simp [EPRL.epair, S3_emb] <;> (rw [hcol _ (by decide +kernel)]; decide +kernel)

lemma S3_pos4 (col : Finset (Fin 6) → ℕ) (hcol : ∀ f ∈ sphere6.tris, col f = col0 f)
    (h : EPRL.simpE 1 col S3 ≠ 0) : col {0, 1, 2, 4} = 0 := by
  have hb : IsVertexBoundary (EPRL.triSpins S3 S3_card col) 0 (EPRL.tetLabels S3 S3_card col) := by
    by_contra hbn
    apply h
    unfold EPRL.simpE
    rw [dif_pos S3_card]
    have hN : (fun e => EPRL.eprlN 1 (EPRL.triSpins S3 S3_card col e)) = EPRL.triSpins S3 S3_card col := by
      funext e; exact EPRL.eprlN_one _
    have hM : (fun e => EPRL.eprlM 1 (EPRL.triSpins S3 S3_card col e)) = 0 := by
      funext e; exact EPRL.eprlM_one _
    rw [hN, hM, if_neg (fun hh => hbn hh.2)]
  have h3 := hb 4
  rw [trisS3 col hcol] at h3
  simp only [k5Spins, Pi.zero_apply, add_zero] at h3
  have e3 : EPRL.tetLabels S3 S3_card col 4 = col {0, 1, 2, 4} := by
    unfold EPRL.tetLabels
    rw [S3_emb]
    have : S3.erase (![(0 : Fin 6), 1, 2, 4, 5] 4) = {0, 1, 2, 4} := by decide +kernel
    rw [this]
  rw [e3] at h3
  simp [mem_channel, Lightlike.Pentagon.Tri] at h3
  omega

/-- **The positional EPRL weight at `γ = 1` vanishes on the bone triangles, for every tetrahedron labelling**: the
simplex `{0,1,2,3,4}` forces the label `1` on the tetrahedron `{0,1,2,4}` (position `3`, channel `(1,0|0,1)`), the
simplex `{0,1,2,4,5}` forces `0` on it (position `4`, channel `(0,0|1,1)`). While the Ooguri weight of the bone
colouring (virtual spin `1`) is `4`: the two weights differ by the per-tetrahedron change of intertwiner basis. -/
theorem weightE_bone_zero (col : Finset (Fin 6) → ℕ) (hcol : ∀ f ∈ sphere6.tris, col f = col0 f) :
    EPRL.weightE 1 sphere6 col = 0 := by
  rw [EPRL.weightE_one]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero_iff.2 ?_)
  by_cases h1 : EPRL.simpE 1 col S1 = 0
  · exact ⟨S1, by rw [sphere6_simps]; simp, h1⟩
  · by_cases h3 : EPRL.simpE 1 col S3 = 0
    · exact ⟨S3, by rw [sphere6_simps]; simp, h3⟩
    · exact absurd ((S1_pos3 col hcol h1).symm.trans (S3_pos4 col hcol h3)) (by norm_num)


/-- The Ooguri weight with the wrong face amplitude `(J + 1)²` instead of `J + 1`. -/
noncomputable def weightWrong (K : Complex4 (Fin 6)) (col : Finset (Fin 6) → ℕ) : ℝ :=
  (∏ f ∈ K.tris, (((col f : ℝ) + 1) ^ 2)) * ∏ s ∈ K.simps, simpW col s

/-- **A wrong face amplitude is detected**: with `(J + 1)²` the bone colouring has weight `64`, not `4`. -/
theorem weightWrong_col0 : weightWrong sphere6 col0 = 64 := by
  have h : weight sphere6 col0 = 4 := weight_col0
  unfold weightWrong
  unfold weight at h
  rw [Finset.prod_pow, prod_tris_col0]
  rw [prod_tris_col0] at h
  nlinarith [h]

theorem weightWrong_col0_ne : weightWrong sphere6 col0 ≠ weight sphere6 col0 := by
  rw [weightWrong_col0, weight_col0]; norm_num

/-- **Trust check on `∂Δ⁵` (bone colouring).** For the triangle spins of the bone colouring, the Ooguri weight is `4`
for the tetrahedron labelling `col0` while the positional EPRL weight at `γ = 1` vanishes for every tetrahedron
labelling; the Ooguri weight with the face amplitude `(J + 1)²` is `64`, a different number. -/
theorem trust_bone :
    weight sphere6 col0 = 4 ∧
    (∀ col : Finset (Fin 6) → ℕ, (∀ f ∈ sphere6.tris, col f = col0 f) → EPRL.weightE 1 sphere6 col = 0) ∧
    weightWrong sphere6 col0 = 64 :=
  ⟨weight_col0, weightE_bone_zero, weightWrong_col0⟩

end Lightlike.SpinFoam.EPRLStateSum.Trust
