import Lightlike.SpinFoam.EPRLStateSum.InversionParity

/-!
# The EPRL state sum at `γ = 1` does not depend on the vertex order

`amplitudeI 1 K cut` is a sum over the colourings of the triangles of the face amplitudes times the network `Znet K col`. A relabelling `σ` of the vertices
changes the network by `(-1)` to the number of reversed links (`Znet_relabel`), which is even when the tetrahedron sums of `col` are even
(`invSum_total_even`) and irrelevant otherwise (`Znet_eq_zero`).
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- **The network is invariant under a relabelling of the vertices** (closed complex, any colouring). -/
theorem Znet_relabel_eq (K : Complex4 V) (σ : V ≃ V) (hK : K.IsClosed4) (col : Finset V → ℕ) :
    Znet (relabelComplex K σ) (relabelCol σ col) = Znet K col := by
  rw [Znet_relabel K σ hK col]
  by_cases hp : TetPar K col
  · rw [(invSum_total_even K σ hK col hp).neg_one_pow, one_mul]
  · rw [Znet_eq_zero K hK col hp, mul_zero]

/-- The triangles of the relabelled complex are the images of those of `K`. -/
lemma tris_relabel (K : Complex4 V) (σ : V ≃ V) :
    (relabelComplex K σ).tris = K.tris.image (fun f => f.map σ.toEmbedding) := by
  ext f'
  rw [Finset.mem_image]
  constructor
  · intro h
    exact ⟨f'.map σ.symm.toEmbedding, (mem_relabel_faces K σ 2 f').1 h, map_symm_map σ f'⟩
  · rintro ⟨f, hf, rfl⟩
    rw [mem_relabel_faces, map_map_symm]
    exact hf

/-- **At `γ = 1` the amplitude is a sum over colourings of the face amplitudes times the network.** -/
theorem amplitudeI_one_eq_sum_Znet (K : Complex4 V) (cut : Finset V → ℕ) :
    amplitudeI 1 K cut =
      ∑ c ∈ K.tris.pi (fun f => range (cut f + 1)),
        (∏ f ∈ K.tris, (EPRL.faceAmp 1 (Lightlike.PR.extS K.tris c f) : ℂ)) *
          (Znet K (Lightlike.PR.extS K.tris c) : ℂ) := by
  unfold amplitudeI
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [EPRL.edgeAmp, Nat.cast_one, Finset.prod_const_one, mul_one]
  congr 1
  simp only [vertexI_one]
  have h : (∑ i ∈ Fintype.piFinset (tetBoxI K (Lightlike.PR.extS K.tris c)),
      tetSumTerm K (Lightlike.PR.extS K.tris c) i) = Znet K (Lightlike.PR.extS K.tris c) := by
    rw [tetSum_network]; rfl
  rw [← h, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold tetSumTerm
  rw [Complex.ofReal_prod]

lemma pi_congr {S : Finset (Finset V)} (c : ∀ f ∈ S, ℕ) {g f : Finset V} (hg : g = f) (p : g ∈ S) (q : f ∈ S) :
    c g p = c f q := by
  subst hg; rfl

/-- The face amplitudes are carried by the relabelling. -/
lemma faceProd_relabel (K : Complex4 V) (σ : V ≃ V) (col : Finset V → ℕ) :
    ∏ f' ∈ (relabelComplex K σ).tris, (EPRL.faceAmp 1 (relabelCol σ col f') : ℂ) =
      ∏ f ∈ K.tris, (EPRL.faceAmp 1 (col f) : ℂ) := by
  rw [tris_relabel, Finset.prod_image (fun a _ b _ h => Finset.map_injective σ.toEmbedding h)]
  refine Finset.prod_congr rfl fun f _ => ?_
  unfold relabelCol
  rw [map_map_symm]

/-- The extension of a colouring of the triangles of the relabelled complex is the relabelling of the extension. -/
lemma extS_relabel (K : Complex4 V) (σ : V ≃ V) (c : ∀ f ∈ K.tris, ℕ) :
    Lightlike.PR.extS (relabelComplex K σ).tris
        (fun f' hf' => c (f'.map σ.symm.toEmbedding) ((mem_relabel_faces K σ 2 f').1 hf')) =
      relabelCol σ (Lightlike.PR.extS K.tris c) := by
  funext f'
  unfold Lightlike.PR.extS relabelCol
  by_cases h : f' ∈ (relabelComplex K σ).tris
  · have h' : f'.map σ.symm.toEmbedding ∈ K.tris := (mem_relabel_faces K σ 2 f').1 h
    simp only [h, h', dite_true]
  · have h' : f'.map σ.symm.toEmbedding ∉ K.tris := fun h'' => h ((mem_relabel_faces K σ 2 f').2 h'')
    simp only [h, h', dite_false]

/-- **The sum over the colourings of a function of the colouring is carried by the relabelling.** -/
lemma sum_colourings_relabel (K : Complex4 V) (σ : V ≃ V) (cut : Finset V → ℕ) (Φ Φ' : (Finset V → ℕ) → ℂ)
    (h : ∀ col, Φ' (relabelCol σ col) = Φ col) :
    ∑ c' ∈ (relabelComplex K σ).tris.pi (fun f => range (cut (f.map σ.symm.toEmbedding) + 1)),
        Φ' (Lightlike.PR.extS (relabelComplex K σ).tris c') =
      ∑ c ∈ K.tris.pi (fun f => range (cut f + 1)), Φ (Lightlike.PR.extS K.tris c) := by
  have hm : ∀ f ∈ K.tris, f.map σ.toEmbedding ∈ (relabelComplex K σ).tris := fun f hf => by
    rw [mem_relabel_faces, map_map_symm]; exact hf
  refine Finset.sum_bij' (fun c' _ => fun f hf => c' (f.map σ.toEmbedding) (hm f hf))
    (fun c _ => fun f' hf' => c (f'.map σ.symm.toEmbedding) ((mem_relabel_faces K σ 2 f').1 hf'))
    ?_ ?_ ?_ ?_ ?_
  · intro c' hc'
    rw [Finset.mem_pi] at hc' ⊢
    intro f hf
    have := hc' (f.map σ.toEmbedding) (hm f hf)
    simpa [map_map_symm] using this
  · intro c hc
    rw [Finset.mem_pi] at hc ⊢
    intro f' hf'
    exact hc _ _
  · intro c' _
    funext f hf
    exact pi_congr c' (map_symm_map σ f) _ _
  · intro c _
    funext f' hf'
    exact pi_congr c (map_map_symm σ f') _ _
  · intro c' _
    have key : Lightlike.PR.extS (relabelComplex K σ).tris c' =
        relabelCol σ (Lightlike.PR.extS K.tris (fun f hf => c' (f.map σ.toEmbedding) (hm f hf))) := by
      rw [← extS_relabel K σ (fun f hf => c' (f.map σ.toEmbedding) (hm f hf))]
      congr 1
      funext f' hf'
      exact (pi_congr c' (map_symm_map σ f') _ _).symm
    rw [key, h]

/-- **The EPRL state sum at `γ = 1` is independent of the order of the vertices.** For a closed 4-complex `K`, every relabelling `σ` of its vertices
and every cutoff `cut` on the triangles, the amplitude of the relabelled complex with the relabelled cutoff equals the amplitude of `K`. -/
theorem amplitudeI_one_relabel (K : Complex4 V) (σ : V ≃ V) (hK : K.IsClosed4) (cut : Finset V → ℕ) :
    amplitudeI 1 (relabelComplex K σ) (fun f => cut (f.map σ.symm.toEmbedding)) = amplitudeI 1 K cut := by
  rw [amplitudeI_one_eq_sum_Znet, amplitudeI_one_eq_sum_Znet]
  exact sum_colourings_relabel K σ cut
    (fun col => (∏ f ∈ K.tris, (EPRL.faceAmp 1 (col f) : ℂ)) * (Znet K col : ℂ))
    (fun col => (∏ f ∈ (relabelComplex K σ).tris, (EPRL.faceAmp 1 (col f) : ℂ)) *
      (Znet (relabelComplex K σ) col : ℂ))
    fun col => by rw [faceProd_relabel, Znet_relabel_eq K σ hK]

/-! ## The variant with the form `ε` on the legs -/

/-- The tetrahedra of the relabelled complex are the images of those of `K`. -/
lemma tets_relabel (K : Complex4 V) (σ : V ≃ V) :
    (relabelComplex K σ).tets = K.tets.image (fun f => f.map σ.toEmbedding) := by
  ext f'
  rw [Finset.mem_image]
  constructor
  · intro h
    exact ⟨f'.map σ.symm.toEmbedding, (mem_relabel_faces K σ 3 f').1 h, map_symm_map σ f'⟩
  · rintro ⟨f, hf, rfl⟩
    rw [mem_relabel_faces, map_map_symm]
    exact hf

/-- **The sign of the gluing through `ε`**: gluing the two sides of a tetrahedron through the form `ε` instead of the identity multiplies the summand
by `(-1)^((J₀ + J₁ + J₂ + J₃) / 2)`, the sum of the four leg colours halved (`fourJ_neg`), a function of the colouring only. -/
noncomputable def epsSign (K : Complex4 V) (col : Finset V → ℕ) : ℝ :=
  ∏ t ∈ K.tets, (-1 : ℝ) ^ ((∑ v ∈ t, col (t.erase v)) / 2)

/-- The sign of the gluing through `ε` is carried by the relabelling. -/
lemma epsSign_relabel (K : Complex4 V) (σ : V ≃ V) (col : Finset V → ℕ) :
    epsSign (relabelComplex K σ) (relabelCol σ col) = epsSign K col := by
  unfold epsSign
  rw [tets_relabel, Finset.prod_image (fun a _ b _ h => Finset.map_injective σ.toEmbedding h)]
  refine Finset.prod_congr rfl fun t _ => ?_
  congr 2
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold relabelCol
  rw [Finset.map_erase, map_map_symm]
  simp

/-- **The EPRL state sum at `γ = 1` with the tetrahedra glued through `ε`**: the sum over the colourings of the face amplitudes, the sign `epsSign`
and the network. -/
noncomputable def amplitudeIeps (K : Complex4 V) (cut : Finset V → ℕ) : ℂ :=
  ∑ c ∈ K.tris.pi (fun f => range (cut f + 1)),
    (∏ f ∈ K.tris, (EPRL.faceAmp 1 (Lightlike.PR.extS K.tris c f) : ℂ)) *
      (epsSign K (Lightlike.PR.extS K.tris c) : ℂ) * (Znet K (Lightlike.PR.extS K.tris c) : ℂ)

/-- **The state sum glued through `ε` is also independent of the order of the vertices.** -/
theorem amplitudeIeps_relabel (K : Complex4 V) (σ : V ≃ V) (hK : K.IsClosed4) (cut : Finset V → ℕ) :
    amplitudeIeps (relabelComplex K σ) (fun f => cut (f.map σ.symm.toEmbedding)) = amplitudeIeps K cut := by
  unfold amplitudeIeps
  exact sum_colourings_relabel K σ cut
    (fun col => (∏ f ∈ K.tris, (EPRL.faceAmp 1 (col f) : ℂ)) * (epsSign K col : ℂ) * (Znet K col : ℂ))
    (fun col => (∏ f ∈ (relabelComplex K σ).tris, (EPRL.faceAmp 1 (col f) : ℂ)) *
      (epsSign (relabelComplex K σ) col : ℂ) * (Znet (relabelComplex K σ) col : ℂ))
    fun col => by rw [faceProd_relabel, Znet_relabel_eq K σ hK, epsSign_relabel]

end Lightlike.SpinFoam.EPRLStateSum
