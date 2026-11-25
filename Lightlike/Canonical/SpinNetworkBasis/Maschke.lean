import Lightlike.HarmonicAnalysis.SU2PeterWeyl
import Lightlike.Canonical.SpinNetworkBasis.Orthonormal

/-!
# Spin networks, step C1: coefficients of unitary `SU(2)`-representations are spin coefficients

Row G2-010 (milestone OP, task T-CA2). Every matrix coefficient of a continuous finite-dimensional unitary
representation of `SU(2)` is a linear combination of the spin coefficients `g ↦ Dⁿ(g)_{ab}`
(`entry_mem_spinSpan`). The irreducible case is `su2_irreducible_classification`; the general case is
complete reducibility (orthogonal complements of invariant subspaces), by induction on the dimension.

Supporting lemmas for the spin-network basis theorem; no catalogue entry.
-/

open Lightlike Lightlike.HarmonicAnalysis Lightlike.HarmonicAnalysis.UnitaryMatrixRep Matrix

namespace Lightlike.Rows.G2_010

noncomputable section

/-- The span of the spin coefficients `g ↦ Dⁿ(g)_{ab}` inside the functions `SU(2) → ℂ`. -/
def spinSpan : Submodule ℂ (SU2 → ℂ) :=
  Submodule.span ℂ {f | ∃ (n : ℕ) (i j : Fin (n + 1)), f = fun g : SU2 => SU2.spinMat n g i j}

lemma spinMat_mem_spinSpan (n : ℕ) (i j : Fin (n + 1)) :
    (fun g : SU2 => SU2.spinMat n g i j) ∈ spinSpan :=
  Submodule.subset_span ⟨n, i, j, rfl⟩

/-- The entries of a representation equivalent to a spin representation are spin coefficients. -/
lemma entry_mem_of_equivalent {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}
    {σ : UnitaryMatrixRep SU2 κ} (h : Equivalent (su2Spin n) σ) (i j : κ) :
    (fun g => σ.mat g i j) ∈ spinSpan := by
  obtain ⟨e, he⟩ := h
  set y : Fin (n + 1) → ℂ := e (Pi.single j 1) with hy
  set c : Fin (n + 1) → ℂ := fun a => e.symm (Pi.single a 1) i with hc
  have key : ∀ g : SU2, σ.mat g i j = ∑ b, ∑ a, (y b * c a) * SU2.spinMat n g a b := by
    intro g
    have h2 : σ.mat g *ᵥ (Pi.single j 1 : κ → ℂ) = e.symm (SU2.spinMat n g *ᵥ y) := by
      rw [LinearEquiv.eq_symm_apply, he g, hy]
      rfl
    have h1 : σ.mat g i j = e.symm (SU2.spinMat n g *ᵥ y) i := by
      rw [← h2]; simp
    rw [h1]
    have h3 : SU2.spinMat n g *ᵥ y = ∑ b, y b • (fun a => SU2.spinMat n g a b) := by
      ext a; simp [Matrix.mulVec, dotProduct, mul_comm]
    have h4 : ∀ b, (fun a => SU2.spinMat n g a b) =
        ∑ a, SU2.spinMat n g a b • (Pi.single a 1 : Fin (n + 1) → ℂ) := by
      intro b; ext a; simp [Finset.sum_apply, Pi.single_apply]
    rw [h3]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h4 b]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have : (fun g => σ.mat g i j) =
      ∑ b, ∑ a, (y b * c a) • (fun g : SU2 => SU2.spinMat n g a b) := by
    funext g; rw [key g]; simp [Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (spinMat_mem_spinSpan n a b)

section Abstract

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A continuous unitary representation of `SU(2)` on an inner product space `V`. -/
structure IsUnitaryRep (π : SU2 → V →ₗ[ℂ] V) : Prop where
  map_one : π 1 = LinearMap.id
  map_mul : ∀ g h, π (g * h) = π g ∘ₗ π h
  inner_map : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w
  continuous : ∀ v w, Continuous fun g => inner ℂ w (π g v)

/-- `W` is invariant under `π`. -/
def IsInv (π : SU2 → V →ₗ[ℂ] V) (W : Submodule ℂ V) : Prop := ∀ g, ∀ v ∈ W, π g v ∈ W

/-- All matrix coefficients `g ↦ ⟪w, π g v⟫` are spin coefficients. -/
def CoefSpin (π : SU2 → V →ₗ[ℂ] V) : Prop :=
  ∀ v w, (fun g => inner ℂ w (π g v)) ∈ spinSpan

lemma IsUnitaryRep.map_inv {π : SU2 → V →ₗ[ℂ] V} (hπ : IsUnitaryRep π) (g : SU2) (v : V) :
    π g (π g⁻¹ v) = v := by
  have := LinearMap.congr_fun (hπ.map_mul g g⁻¹) v
  rw [mul_inv_cancel, hπ.map_one] at this
  exact this.symm

lemma IsUnitaryRep.isInv_orthogonal {π : SU2 → V →ₗ[ℂ] V} (hπ : IsUnitaryRep π)
    {W : Submodule ℂ V} (hW : IsInv π W) : IsInv π Wᗮ := by
  intro g u hu
  rw [Submodule.mem_orthogonal]
  intro w hw
  have h1 := hπ.inner_map g (π g⁻¹ w) u
  rw [hπ.map_inv] at h1
  rw [h1]
  exact (Submodule.mem_orthogonal _ _).1 hu _ (hW g⁻¹ w hw)

/-- Restriction of a unitary representation to an invariant subspace. -/
def restrictRep (π : SU2 → V →ₗ[ℂ] V) {W : Submodule ℂ V} (hW : IsInv π W) :
    SU2 → W →ₗ[ℂ] W := fun g => (π g).restrict (hW g)

lemma IsUnitaryRep.restrict {π : SU2 → V →ₗ[ℂ] V} (hπ : IsUnitaryRep π) {W : Submodule ℂ V}
    (hW : IsInv π W) : IsUnitaryRep (restrictRep π hW) where
  map_one := by ext v; simp [restrictRep, hπ.map_one]
  map_mul := fun g h => by ext v; simp [restrictRep, hπ.map_mul]
  inner_map := fun g v w => by
    simpa [restrictRep] using hπ.inner_map g (v : V) (w : V)
  continuous := fun v w => by
    simpa [restrictRep] using hπ.continuous (v : V) (w : V)

end Abstract

section Irreducible

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {π : SU2 → V →ₗ[ℂ] V} {ι : Type} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ V)

/-- The matrix `π(g)_{ij} = ⟪b_i, π g b_j⟫` of a unitary representation in an orthonormal basis. -/
def repMat (π : SU2 → V →ₗ[ℂ] V) (g : SU2) : Matrix ι ι ℂ :=
  Matrix.of fun i j => inner ℂ (b i) (π g (b j))

omit [DecidableEq ι] in
lemma repMat_mul (hπ : IsUnitaryRep π) (g h : SU2) :
    repMat b π (g * h) = repMat b π g * repMat b π h := by
  ext i j
  simp only [repMat, Matrix.of_apply, Matrix.mul_apply, hπ.map_mul, LinearMap.comp_apply]
  have hx := b.sum_repr' (π h (b j))
  conv_lhs => rw [← hx]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

lemma repMat_one (hπ : IsUnitaryRep π) : repMat b π 1 = 1 := by
  ext i j
  simp [repMat, hπ.map_one, b.inner_eq_ite, Matrix.one_apply]

lemma repMat_mem_unitaryGroup (hπ : IsUnitaryRep π) (g : SU2) :
    repMat b π g ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have h : (star (repMat b π g) * repMat b π g) i j = inner ℂ (π g (b i)) (π g (b j)) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, repMat, Matrix.of_apply, RCLike.star_def]
    rw [← b.sum_inner_mul_inner (π g (b i)) (π g (b j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact inner_conj_symm (𝕜 := ℂ) (π g (b i)) (b k)
  rw [h, hπ.inner_map, b.inner_eq_ite, Matrix.one_apply]

/-- The unitary matrix representation of `π` in an orthonormal basis. -/
def toMatrixRep (hπ : IsUnitaryRep π) : UnitaryMatrixRep SU2 ι where
  toHom :=
    { toFun := fun g => ⟨repMat b π g, repMat_mem_unitaryGroup b hπ g⟩
      map_one' := Subtype.ext (repMat_one b hπ)
      map_mul' := fun g h => Subtype.ext (repMat_mul b hπ g h) }
  continuous_toHom := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact hπ.continuous (b j) (b i)

lemma toMatrixRep_mat (hπ : IsUnitaryRep π) (g : SU2) (i j : ι) :
    (toMatrixRep b hπ).mat g i j = inner ℂ (b i) (π g (b j)) := rfl

/-- The coefficients of `π` are combinations of the entries of its matrix in the basis `b`. -/
lemma inner_eq_sum (hπ : IsUnitaryRep π) (g : SU2) (v w : V) :
    inner ℂ w (π g v) = ∑ i, ∑ j, inner ℂ w (b i) * (toMatrixRep b hπ).mat g i j * inner ℂ (b j) v := by
  rw [← b.sum_inner_mul_inner w (π g v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx := b.sum_repr' v
  conv_lhs => rw [← hx]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum, toMatrixRep_mat]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma coefSpin_of_entries (hπ : IsUnitaryRep π)
    (h : ∀ i j, (fun g => (toMatrixRep b hπ).mat g i j) ∈ spinSpan) : CoefSpin π := by
  intro v w
  have : (fun g => inner ℂ w (π g v)) =
      ∑ i, ∑ j, (inner ℂ w (b i) * inner ℂ (b j) v) • (fun g => (toMatrixRep b hπ).mat g i j) := by
    funext g
    rw [inner_eq_sum b hπ]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h i j)

/-- Coordinates-to-vector isomorphism. -/
def coordLin : (ι → ℂ) ≃ₗ[ℂ] V := b.toBasis.equivFun.symm

omit [DecidableEq ι] in
lemma coordLin_apply (x : ι → ℂ) : coordLin b x = ∑ a, x a • b a := by
  show b.toBasis.equivFun.symm x = _
  rw [Module.Basis.equivFun_symm_apply]
  simp only [OrthonormalBasis.coe_toBasis]

lemma pi_coordLin (hπ : IsUnitaryRep π) (g : SU2) (x : ι → ℂ) :
    π g (coordLin b x) = coordLin b ((toMatrixRep b hπ).mat g *ᵥ x) := by
  rw [coordLin_apply, coordLin_apply, map_sum]
  simp only [map_smul]
  have h1 : ∀ a, π g (b a) = ∑ c, (toMatrixRep b hπ).mat g c a • b c :=
    fun a => (b.sum_repr' _).symm
  simp_rw [h1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- An irreducible invariant-subspace structure gives an irreducible matrix representation. -/
lemma toMatrixRep_isIrreducible (hπ : IsUnitaryRep π) [Nontrivial V]
    (hirr : ∀ W : Submodule ℂ V, IsInv π W → W = ⊥ ∨ W = ⊤) :
    (toMatrixRep b hπ).IsIrreducible := by
  refine ⟨?_, ?_⟩
  · by_contra hne
    rw [not_nonempty_iff] at hne
    have : IsEmpty ι := hne
    have : Subsingleton V := (coordLin b).symm.toEquiv.subsingleton
    exact not_subsingleton V this
  · intro X hX
    let W : Submodule ℂ V := X.map (coordLin b).toLinearMap
    have hWinv : IsInv π W := by
      rintro g _ ⟨x, hx, rfl⟩
      refine ⟨(toMatrixRep b hπ).mat g *ᵥ x, hX g x hx, ?_⟩
      exact (pi_coordLin b hπ g x).symm
    rcases hirr W hWinv with h | h
    · left
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have : coordLin b x ∈ W := ⟨x, hx, rfl⟩
      rw [h] at this
      have h0 : coordLin b x = 0 := by simpa using this
      exact (coordLin b).injective (by simpa using h0)
    · right
      refine (Submodule.eq_top_iff').2 fun y => ?_
      have : coordLin b y ∈ W := by rw [h]; trivial
      obtain ⟨x, hx, hxy⟩ := this
      have : x = y := (coordLin b).injective hxy
      rw [← this]; exact hx

end Irreducible

/-- **Complete reducibility for `SU(2)`.** Every matrix coefficient of a continuous unitary representation of
`SU(2)` on a finite-dimensional inner product space is a linear combination of spin coefficients. -/
theorem coefSpin_of_isUnitaryRep : ∀ (d : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V], Module.finrank ℂ V = d → ∀ π : SU2 → V →ₗ[ℂ] V,
    IsUnitaryRep π → CoefSpin π := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hd π hπ
  by_cases hsub : Subsingleton V
  · intro v w
    have : v = 0 := Subsingleton.elim _ _
    subst this
    have h0 : (fun g => inner ℂ w (π g 0)) = 0 := by funext g; simp
    rw [h0]; exact spinSpan.zero_mem
  · have : Nontrivial V := not_subsingleton_iff_nontrivial.1 hsub
    by_cases hirr : ∀ W : Submodule ℂ V, IsInv π W → W = ⊥ ∨ W = ⊤
    · let b := stdOrthonormalBasis ℂ V
      have hi := toMatrixRep_isIrreducible b hπ hirr
      obtain ⟨n, hn, -⟩ := su2_irreducible_classification hi
      exact coefSpin_of_entries b hπ fun i j => entry_mem_of_equivalent hn i j
    · push Not at hirr
      obtain ⟨W, hW, hbot, htop⟩ := hirr
      have hW' := hπ.isInv_orthogonal hW
      have hlt1 : Module.finrank ℂ W < d := hd ▸ Submodule.finrank_lt htop
      have hlt2 : Module.finrank ℂ (Wᗮ : Submodule ℂ V) < d := by
        refine hd ▸ Submodule.finrank_lt fun h => hbot ?_
        exact (Submodule.orthogonal_eq_top_iff W).1 h
      have c1 := ih _ hlt1 W rfl _ (hπ.restrict hW)
      have c2 := ih _ hlt2 (Wᗮ : Submodule ℂ V) rfl _ (hπ.restrict hW')
      have hdec : ∀ v : V, ∃ a ∈ W, ∃ c ∈ Wᗮ, a + c = v := by
        intro v
        have : v ∈ W ⊔ Wᗮ := by rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; trivial
        obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 this
        exact ⟨a, ha, c, hc, rfl⟩
      intro v w
      obtain ⟨v1, hv1, v2, hv2, rfl⟩ := hdec v
      obtain ⟨w1, hw1, w2, hw2, rfl⟩ := hdec w
      have e : (fun g => inner ℂ (w1 + w2) (π g (v1 + v2))) =
          (fun g => inner ℂ (⟨w1, hw1⟩ : W) (restrictRep π hW g ⟨v1, hv1⟩)) +
          (fun g => inner ℂ (⟨w2, hw2⟩ : (Wᗮ : Submodule ℂ V))
            (restrictRep π hW' g ⟨v2, hv2⟩)) := by
        funext g
        have a1 : π g v1 ∈ W := hW g v1 hv1
        have a2 : π g v2 ∈ Wᗮ := hW' g v2 hv2
        have z1 : inner ℂ w2 (π g v1) = 0 := 
          inner_eq_zero_symm.1 ((Submodule.mem_orthogonal _ _).1 hw2 _ a1)
        have z2 : inner ℂ w1 (π g v2) = 0 := (Submodule.mem_orthogonal _ _).1 a2 _ hw1
        simp only [map_add, inner_add_left, inner_add_right, z1, z2, Pi.add_apply]
        simp [restrictRep]
      rw [e]
      exact spinSpan.add_mem (c1 _ _) (c2 _ _)

/-- A continuous unitary matrix representation, as a unitary representation on `ℂ^ι`. -/
lemma isUnitaryRep_toLpLin {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : UnitaryMatrixRep SU2 ι) :
    IsUnitaryRep (fun g => Matrix.toLpLin 2 2 (σ.mat g) : SU2 → EuclideanSpace ℂ ι →ₗ[ℂ] _) where
  map_one := by rw [σ.mat_one]; exact Matrix.toLpLin_one 2
  map_mul := fun g h => by rw [σ.mat_mul]; exact Matrix.toLpLin_mul_same 2 _ _
  inner_map := fun g v w => by
    have h := star_mat_mul_mat σ g
    have e : ∀ x, Matrix.toLpLin 2 2 (σ.mat g)ᴴ (Matrix.toLpLin 2 2 (σ.mat g) x) = x := by
      intro x
      have := LinearMap.congr_fun (Matrix.toLpLin_mul_same 2 (σ.mat g)ᴴ (σ.mat g)) x
      rw [h, Matrix.toLpLin_one] at this
      exact this.symm
    have hadj : Matrix.toLpLin 2 2 (σ.mat g)ᴴ = LinearMap.adjoint (Matrix.toLpLin 2 2 (σ.mat g)) :=
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint _
    rw [hadj] at e
    rw [← LinearMap.adjoint_inner_left, e]
  continuous := fun v w => by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, dotProduct,
      Matrix.mulVec]
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.mul (continuous_finsetSum _ fun j _ => ?_) continuous_const
    exact (σ.continuous_mat_apply i j).mul continuous_const

/-- **Coefficients of unitary representations of `SU(2)` are spin coefficients.** -/
theorem entry_mem_spinSpan {ι : Type} [Fintype ι] [DecidableEq ι] (σ : UnitaryMatrixRep SU2 ι)
    (i j : ι) : (fun g => σ.mat g i j) ∈ spinSpan := by
  have h := coefSpin_of_isUnitaryRep _ (EuclideanSpace ℂ ι) rfl _ (isUnitaryRep_toLpLin σ)
    (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  convert h using 2 with g
  simp [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]

/-- Every element of `matrixCoeffSpan SU(2)` is a linear combination of spin coefficients. -/
theorem coe_mem_spinSpan_of_mem_matrixCoeffSpan {f : C(SU2, ℂ)} (hf : f ∈ matrixCoeffSpan SU2) :
    (f : SU2 → ℂ) ∈ spinSpan := by
  unfold matrixCoeffSpan at hf
  refine Submodule.span_induction (p := fun (x : C(SU2, ℂ)) _ => (x : SU2 → ℂ) ∈ spinSpan)
    ?_ ?_ ?_ ?_ hf
  · rintro x ⟨ι, _, _, ρ, i, j, hx⟩
    have : (x : SU2 → ℂ) = fun g => ρ.mat g i j := funext hx
    rw [this]
    exact entry_mem_spinSpan ρ i j
  · exact spinSpan.zero_mem
  · intro x y _ _ hx hy
    exact spinSpan.add_mem hx hy
  · intro a x _ hx
    exact spinSpan.smul_mem a hx

end

end Lightlike.Rows.G2_010
