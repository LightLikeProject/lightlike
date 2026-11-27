import Lightlike.SpinFoam.Ooguri
import Lightlike.Spin4.Vertex

/-!
# The Euclidean EPRL state sum

The state sum of the Euclidean Engle–Pereira–Rovelli–Livine (EPRL) spin foam model with Immirzi
parameter `γ < 1` on a 4-complex `K`. Doubled spins throughout.

A colouring `col : Finset V → ℕ` gives the doubled SU(2) spin `J` of every triangle and the
doubled intertwiner label `z` of every tetrahedron (the virtual spin in the recoupling basis
`(J₁ J₂) z (J₃ J₄)` of its legs, taken in the order of its sorted vertices). The Spin(4) labels of a
triangle are the EPRL labels of its spin, `(n, m) = (2j⁺, 2j⁻)` with `n + m = J`, `n - m = γ J`
(`eprlN`, `eprlM`). The weight of a colouring is

`weightE γ K col = Π_{triangles} (n + 1)(m + 1) · Π_{tetrahedra} 1 · Π_{4-simplices} eprlVertex`.

* **Face amplitude** `faceAmp γ J = (n + 1)(m + 1)`: the dimension of the Spin(4) representation
  `(j⁺, j⁻)` of the triangle.
* **Edge amplitude** `edgeAmp = 1`: the boundary intertwiners `ι_z` are orthonormal in the
  recoupling basis and the EPRL map is an isometry on every leg (`eprlMap_isometry`), so no
  normalisation factor appears.
* **Vertex amplitude** `simpE`: `eprlVertex` of the 4-simplex, with its ten triangles and five
  tetrahedra taken in the order of the sorted vertices, as in `vertexAmp` of the Ooguri model. It is
  `0` unless every triangle spin is EPRL-admissible and every node label lies in its channel
  (`IsVertexBoundary`), which are the conditions under which `eprlVertex` has a meaning.

The state sum `amplitudeGF γ K T cut` sums the weight over the colourings with colour `≤ cut f` on
the faces `f ∉ T` and colour `0` on `T`, exactly as for the Ooguri model (`Lightlike.SpinFoam.amplitudeGF`).

## Main results

* `eprlN`, `eprlM`, `isEPRLLabel_eprlN`: the labels of an admissible spin, and `eprlN_add_eprlM`.
* `simpE_zero`, `weightE_zero`, `amplitude_zero`: at spin `0` every vertex is `1`, and with cutoff
  `0` the state sum is `1` on every complex.
* `simpE_im`, `amplitudeGF_im`: the vertex, hence the state sum, is real.
* `simpE_eq_zero_of_not_admissible`: a triangle of non-admissible spin kills the amplitude.

## Conventions

The vertex is `eprlVertex` of `Lightlike/Spin4/Vertex.lean`, which contracts the five node tensors
along the edges of `K₅` with the orientation of ascending vertices. The orientation independence
known for the Ooguri vertex (`vertexContr_neg`) is not claimed for it.

The label `z` of the tetrahedron `s∖{s_a}` enters `eprlVertex` in the channel of the node `a` of
`fifteenJSimplex`, whose legs are in the cyclic order `a+1, …, a+4`: a *positional* basis, which
for a tetrahedron shared by two 4-simplices at positions of different parity is not the same basis
on both sides (`Lightlike.SpinFoam.EPRLStateSum.positional_gluing_ne_intrinsic`). The state sum in
the sorted basis of every tetrahedron, which glues, is
`Lightlike.SpinFoam.EPRLStateSum.amplitudeI`; at `γ = 1` it is the Ooguri state sum
(`Lightlike.SpinFoam.EPRLStateSum.amplitudeI_one_eq_ooguriSum`), and on a closed complex it does not depend on the order of the
vertices (`Lightlike.SpinFoam.EPRLStateSum.amplitudeI_one_relabel`).

## References

* `eprl-2008`, §III: the model, its vertex and face amplitudes.
* `bianchi-regoli-rovelli-2010`, §IV: the face amplitude.
* `perez-2013`, §2.3.8: the EPRL state sum as a review.
-/

open Finset Lightlike.Spin4 Lightlike.FourD

namespace Lightlike.SpinFoam.EPRL

variable {V : Type*} [LinearOrder V]

/-! ## Labels, face and edge amplitudes -/

/-- The doubled self-dual spin `n = 2 j⁺ = |1 + γ| J / 2` of the doubled spin `J`, rounded down
(exact exactly when `J` is EPRL-admissible). -/
noncomputable def eprlN (γ : ℝ) (J : ℕ) : ℕ := ⌊|1 + γ| * J / 2⌋₊

/-- The doubled anti-self-dual spin `m = 2 j⁻ = |1 - γ| J / 2` of the doubled spin `J`, rounded
down (exact exactly when `J` is EPRL-admissible). -/
noncomputable def eprlM (γ : ℝ) (J : ℕ) : ℕ := ⌊|1 - γ| * J / 2⌋₊

/-- **The EPRL labels of an admissible spin**: `eprlN` and `eprlM` are its doubled labels. -/
theorem isEPRLLabel_eprlN {γ : ℝ} {J : ℕ} (h : EPRLAdmissible γ J) :
    IsEPRLLabel γ J (eprlN γ J) (eprlM γ J) := by
  obtain ⟨n, m, hn, hm⟩ := eprlAdmissible_iff_exists.mp h
  have e1 : (n : ℝ) = |1 + γ| * J / 2 := by rw [hn]; simp only [jPlus]; ring
  have e2 : (m : ℝ) = |1 - γ| * J / 2 := by rw [hm]; simp only [jMinus]; ring
  have f1 : eprlN γ J = n := by rw [eprlN, ← e1, Nat.floor_natCast]
  have f2 : eprlM γ J = m := by rw [eprlM, ← e2, Nat.floor_natCast]
  rw [f1, f2]
  exact ⟨hn, hm⟩

/-- For `0 < γ < 1` the two labels of an admissible spin add up to it. -/
theorem eprlN_add_eprlM {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) {J : ℕ} (h : EPRLAdmissible γ J) :
    eprlN γ J + eprlM γ J = J :=
  (isEPRLLabel_iff hγ hγ1).mp (isEPRLLabel_eprlN h) |>.1

/-- **The face amplitude**: the dimension `(n + 1)(m + 1)` of the Spin(4) representation
`(j⁺, j⁻)` of the EPRL labels of the doubled spin `J`. -/
noncomputable def faceAmp (γ : ℝ) (J : ℕ) : ℕ := (eprlN γ J + 1) * (eprlM γ J + 1)

/-- **The edge amplitude** of a tetrahedron: `1`, as the boundary intertwiners `Φ(ι_z)` are
normalised like the recoupling basis (the EPRL map is an isometry). -/
def edgeAmp : ℕ := 1

/-! ## The vertex amplitude of a 4-simplex -/

/-- The pairs of positions of the ten edges of `K₅`, in the order `01, 02, 03, 04, 12, 13, 14, 23,
24, 34` of `eprlVertex`. -/
def epair : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- The spins on the ten triangles `s∖{s_p, s_q}` of a 4-simplex, in the order of `epair`. -/
def triSpins (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) : Fin 10 → ℕ := fun e =>
  col ((s.erase (s.orderEmbOfFin hs (epair e).1)).erase (s.orderEmbOfFin hs (epair e).2))

/-- The labels on the five tetrahedra `s∖{s_a}` of a 4-simplex. -/
def tetLabels (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) : Fin 5 → ℕ := fun a =>
  col (s.erase (s.orderEmbOfFin hs a))

open scoped Classical in
/-- **The EPRL vertex amplitude of a 4-simplex** `s` in the colouring `col`: `eprlVertex` of the
Spin(4) labels `(n, m)` of the triangle spins and of the tetrahedron labels, when every triangle
spin is EPRL-admissible and every tetrahedron label is in its channel (`IsVertexBoundary`), and `0`
otherwise. `0` also for a vertex set that is not a 4-simplex. -/
noncomputable def simpE (γ : ℝ) (col : Finset V → ℕ) (s : Finset V) : ℂ :=
  if h : #s = 5 then
    if (∀ e, EPRLAdmissible γ (triSpins s h col e)) ∧
        IsVertexBoundary (fun e => eprlN γ (triSpins s h col e))
          (fun e => eprlM γ (triSpins s h col e)) (tetLabels s h col) then
      eprlVertex (fun e => eprlN γ (triSpins s h col e)) (fun e => eprlM γ (triSpins s h col e))
        (tetLabels s h col)
    else 0
  else 0

/-- **The weight of a coloured 4-complex**: face amplitudes of the triangles, edge amplitudes of
the tetrahedra and the vertex amplitudes of the 4-simplices. -/
noncomputable def weightE (γ : ℝ) (K : Complex4 V) (col : Finset V → ℕ) : ℂ :=
  (∏ f ∈ K.tris, (faceAmp γ (col f) : ℂ)) * (∏ _t ∈ K.tets, (edgeAmp : ℂ)) *
    ∏ s ∈ K.simps, simpE γ col s

/-- **The EPRL state sum** with face-wise cutoffs and a gauge set `T`: the sum of `weightE` over
the colourings with colour `≤ cut f` on every face `f ∉ T` and colour `0` on `T`. -/
noncomputable def amplitudeGF (γ : ℝ) (K : Complex4 V) (T : Finset (Finset V))
    (cut : Finset V → ℕ) : ℂ :=
  ∑ c ∈ (Lightlike.SpinFoam.colFaces K \ T).pi (fun f => range (cut f + 1)),
    weightE γ K (Lightlike.PR.extS (Lightlike.SpinFoam.colFaces K \ T) c)

/-- **The EPRL state sum** with spins `≤ L/2` on the triangles and labels `≤ L` on the
tetrahedra (doubled units), without gauge fixing. -/
noncomputable def amplitude (γ : ℝ) (K : Complex4 V) (L : ℕ) : ℂ :=
  amplitudeGF γ K ∅ (fun f => if #f = 4 then 2 * L else L)

/-! ## Spin zero -/

lemma eprlN_zero (γ : ℝ) : eprlN γ 0 = 0 := by simp [eprlN]

lemma eprlM_zero (γ : ℝ) : eprlM γ 0 = 0 := by simp [eprlM]

lemma eprlAdmissible_zero (γ : ℝ) : EPRLAdmissible γ 0 :=
  ⟨⟨0, by simp [jPlus]⟩, ⟨0, by simp [jMinus]⟩⟩

/-- **At spin `0` the vertex is `1`.** -/
theorem simpE_zero (γ : ℝ) {s : Finset V} (hs : #s = 5) : simpE γ (fun _ => 0) s = 1 := by
  have h1 : (fun e => eprlN γ (triSpins s hs (fun _ => 0) e)) = 0 := by
    funext e; simp [triSpins, eprlN_zero]
  have h2 : (fun e => eprlM γ (triSpins s hs (fun _ => 0) e)) = 0 := by
    funext e; simp [triSpins, eprlM_zero]
  have h3 : tetLabels s hs (fun _ => 0) = 0 := by funext a; simp [tetLabels]
  have hb : IsVertexBoundary (0 : Fin 10 → ℕ) 0 (0 : Fin 5 → ℕ) := by decide
  unfold simpE
  rw [dite_eq_left hs, h1, h2, h3,
    ite_eq_left ⟨fun e => by simpa [triSpins] using eprlAdmissible_zero γ, hb⟩]
  exact eprlVertex_zero

/-- **At spin `0` the weight is `1`.** -/
theorem weightE_zero (γ : ℝ) (K : Complex4 V) : weightE γ K (fun _ => 0) = 1 := by
  unfold weightE
  have hf : ∀ f ∈ K.tris, (faceAmp γ 0 : ℂ) = 1 := fun f _ => by
    simp [faceAmp, eprlN_zero, eprlM_zero]
  rw [prod_congr rfl hf]
  rw [prod_congr rfl (fun s hs => simpE_zero γ (K.card_eq s hs))]
  simp [edgeAmp]

/-- **Cutoff `0`**: the state sum is `1` on every complex. -/
theorem amplitude_zero (γ : ℝ) (K : Complex4 V) : amplitude γ K 0 = 1 := by
  unfold amplitude amplitudeGF
  rw [sdiff_empty]
  simp only [mul_zero, ite_self, zero_add, range_one]
  have hpi : (Lightlike.SpinFoam.colFaces K).pi (fun _ => ({0} : Finset ℕ)) =
      {fun _ _ => 0} := by
    ext c
    simp only [mem_pi, mem_singleton]
    constructor
    · intro hc; funext f hf; exact hc f hf
    · rintro rfl f _; rfl
  rw [hpi, sum_singleton]
  have h0 : Lightlike.PR.extS (Lightlike.SpinFoam.colFaces K) (fun _ _ => 0) = fun _ => 0 := by
    funext f; simp [Lightlike.PR.extS]
  rw [h0]
  exact weightE_zero γ K

/-! ## Reality and the admissibility gate -/

/-- The vertex amplitude of a 4-simplex is real. -/
theorem simpE_im (γ : ℝ) (col : Finset V → ℕ) (s : Finset V) : (simpE γ col s).im = 0 := by
  unfold simpE
  split_ifs with h h2
  · exact eprlVertex_im _ _ _ h2.2
  · rfl
  · rfl

/-- A triangle of non-admissible spin kills the vertex amplitude of every 4-simplex containing
it. -/
theorem simpE_eq_zero_of_not_admissible (γ : ℝ) (col : Finset V → ℕ) {s : Finset V}
    (hs : #s = 5) (e : Fin 10) (h : ¬ EPRLAdmissible γ (triSpins s hs col e)) :
    simpE γ col s = 0 := by
  unfold simpE
  rw [dite_eq_left hs, ite_eq_right (fun h' => h (h'.1 e))]

lemma prod_im_zero {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, (f i).im = 0) :
    (∏ i ∈ s, f i).im = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, Complex.mul_im, h a (mem_insert_self a s),
      ih (fun i hi => h i (mem_insert_of_mem hi))]
    simp

/-- The weight of a coloured complex is real. -/
theorem weightE_im (γ : ℝ) (K : Complex4 V) (col : Finset V → ℕ) : (weightE γ K col).im = 0 := by
  unfold weightE
  have hA : (∏ f ∈ K.tris, (faceAmp γ (col f) : ℂ)).im = 0 :=
    prod_im_zero _ _ fun f _ => by simp
  have hB : (∏ _t ∈ K.tets, (edgeAmp : ℂ)).im = 0 := prod_im_zero _ _ fun f _ => by simp
  have hC : (∏ s ∈ K.simps, simpE γ col s).im = 0 :=
    prod_im_zero _ _ fun s _ => simpE_im γ col s
  rw [Complex.mul_im, Complex.mul_im, hA, hB, hC]
  simp

/-- **The EPRL state sum is real.** -/
theorem amplitudeGF_im (γ : ℝ) (K : Complex4 V) (T : Finset (Finset V)) (cut : Finset V → ℕ) :
    (amplitudeGF γ K T cut).im = 0 := by
  unfold amplitudeGF
  rw [Complex.im_sum]
  exact sum_eq_zero fun c _ => weightE_im γ K _

end Lightlike.SpinFoam.EPRL
