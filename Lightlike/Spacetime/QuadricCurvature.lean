import Lightlike.Spacetime.InducedKilling
import Lightlike.Spacetime.ConstantCurvature
import Lightlike.Spacetime.Corners.CurvatureSymmetries

/-!
# The curvature of a quadric

Let `ι : M → V` be a smooth immersion into a finite-dimensional space with a symmetric bilinear form `L` (any
signature), let the metric of `M` be induced, `g(u, v) = L(dι u, dι v)`, and let the image lie on the quadric
`L(x, x) = c`, `c ≠ 0`, with `dι` onto the `L`-orthogonal complement of the point (the tangent space of the quadric).
Then every locally smooth Levi-Civita connection of `g` has constant curvature `1 / c`:
`R(X, Y) Z = (1/c) (g(Y, Z) X - g(X, Z) Y)` (`hasConstantCurvature_of_quadric`).

The proof is the Gauss formula, intrinsically on `M`. Write `D_X F` for the derivative of a `V`-valued function along
`X` (`mvfderiv`); `D` is the flat connection of `V`:
* `mvfderiv_mlieBracket_vec`: `D_{[X,Y]} F = D_X D_Y F - D_Y D_X F` (`mfderiv_mlieBracketW` tested against linear
  functionals); with `F = ι` this is `dι [X, Y] = D_X (dι Y) - D_Y (dι X)`;
* `g_cov_eq_of_induced`: `g(∇_X Y, Z) = L(D_X (dι Y), dι Z)` for a Levi-Civita connection (the Koszul formula);
* `dι_cov_quadric`: `dι (∇_Y Z) = D_Y (dι Z) + (g(Y, Z)/c) ι`, the tangential part of the ambient derivative,
  the normal part being `L(D_Y dι Z, ι) = -g(Y, Z)`;
* applied twice, with `D` flat and `∇` torsion free, it gives `dι (R(X, Y) Z) = (1/c) dι (g(Y, Z) X - g(X, Z) Y)`.

The sphere (`L` Euclidean, `c = r²`), de Sitter space (`L` Minkowski, `c = L²`), anti-de Sitter space (signature
`(2, m)`, `c = -L²`) and the hyperboloid model of hyperbolic space (`c = -1`) are instances; the de Sitter one is
`hasConstantCurvature_deSitterSpace` (`SpaceForms/DeSitterCurvature.lean`), the non-vacuity of this theorem.

**References.** S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), section 8.1 (maximally symmetric spaces
as quadrics); the Gauss formula: B. O'Neill, *Semi-Riemannian Geometry* (Academic Press, 1983), ch. 4, Theorem 5.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Derivatives of vector-valued functions along fields -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- **The derivative of a `C²` function along a differentiable field is differentiable**: `q ↦ D_Z F (q)`. -/
theorem mdiffAt_mvfderiv_section {F : M → V} {p : M} (hF : ContMDiffAt I 𝓘(ℝ, V) ∞ F p)
    {Z : Π q : M, TangentSpace I q}
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, Z q⟩ : TangentBundle I M)) p) :
    MDifferentiableAt I 𝓘(ℝ, V) (fun q => mvfderiv I F q (Z q)) p := by
  have hA : MDifferentiableAt I 𝓘(ℝ, V).tangent
      (tangentMap I 𝓘(ℝ, V) F ∘ fun q => (⟨q, Z q⟩ : TangentBundle I M)) p :=
    (((hF.contMDiffAt_tangentMap (X := (⟨p, Z p⟩ : TangentBundle I M)) (m := 1) (by simp))).mdifferentiableAt
      one_ne_zero).comp p hZ
  have hB := ((mdifferentiableAt_totalSpace _ _).1 hA).2
  simp only [Function.comp_apply, trivializationAt_model_space_apply] at hB
  exact hB

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- A `C^∞` field gives a `C^∞` function `q ↦ dι_q (Z q)`. -/
theorem contMDiffAt_dι_section {ι : M → V} (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι) {Z : Π q : M, TangentSpace I q} {p : M}
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (fun q : M => (⟨q, Z q⟩ : TangentBundle I M)) p) :
    ContMDiffAt I 𝓘(ℝ, V) ∞ (fun q => dι (I := I) ι q (Z q)) p := by
  have hA : ContMDiffAt I 𝓘(ℝ, V).tangent ∞
      (tangentMap I 𝓘(ℝ, V) ι ∘ fun q => (⟨q, Z q⟩ : TangentBundle I M)) p :=
    ((hι.contMDiff_tangentMap (m := ∞) (by simp)) _).comp p hZ
  have hB := (contMDiffAt_totalSpace.1 hA).2
  simp only [Function.comp_apply, trivializationAt_model_space_apply] at hB
  exact hB

omit [FiniteDimensional ℝ V] in
/-- **The product rule for a bilinear form**: `D_v L(F, G) = L(D_v F, G) + L(F, D_v G)`. -/
theorem mvfderiv_bilin (L : V →L[ℝ] V →L[ℝ] ℝ) {F G : M → V} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, V) F x) (hG : MDifferentiableAt I 𝓘(ℝ, V) G x) (v : TangentSpace I x) :
    mvfderiv I (fun q => L (F q) (G q)) x v = L (mvfderiv I F x v) (G x) + L (F x) (mvfderiv I G x v) := by
  have h := mvfderiv_clm_applyW (fun q => L (F q)) G x (L.mdifferentiableAt.comp x hF) hG v
  rw [h, mvfderiv_clm_comp_left L hF v]

variable [IsManifold I 2 M] [CompleteSpace E]

omit [FiniteDimensional ℝ V] in
/-- **The ambient derivative is flat**: `D_{[X,Y]} F = D_X D_Y F - D_Y D_X F` for `F` smooth near `x`. -/
theorem mvfderiv_mlieBracket_vec {F : M → V} {x : M} (hF : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, V) ∞ F y)
    {X Y : Π q : M, TangentSpace I q}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, X q⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, Y q⟩ : TangentBundle I M)) x) :
    mvfderiv I F x (mlieBracket I X Y x) =
      mvfderiv I (fun q => mvfderiv I F q (Y q)) x (X x) - mvfderiv I (fun q => mvfderiv I F q (X q)) x (Y x) := by
  have hFx : ContMDiffAt I 𝓘(ℝ, V) ∞ F x := hF.self_of_nhds
  rw [← sub_eq_zero]
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ => ?_
  have hd : ∀ W : Π q : M, TangentSpace I q,
      dirDerivW (ℓ ∘ F) W =ᶠ[𝓝 x] fun q => ℓ (mvfderiv I F q (W q)) := by
    intro W
    filter_upwards [hF] with q hq
    exact mvfderiv_clm_comp_left ℓ (hq.mdifferentiableAt (by simp)) (W q)
  have hg : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (ℓ ∘ F) y := by
    filter_upwards [hF] with y hy
    exact (ℓ.contMDiff.contMDiffAt).comp y hy
  have key := mfderiv_mlieBracketW (ℓ ∘ F) X Y x hg hX hY
  have e1 : (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (ℓ ∘ F) x (mlieBracket I X Y x)) =
      ℓ (mvfderiv I F x (mlieBracket I X Y x)) := mvfderiv_clm_comp_left ℓ (hFx.mdifferentiableAt (by simp)) _
  have e2 : ∀ (A B : Π q : M, TangentSpace I q),
      MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, B q⟩ : TangentBundle I M)) x →
      (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (dirDerivW (ℓ ∘ F) B) x (A x)) =
        ℓ (mvfderiv I (fun q => mvfderiv I F q (B q)) x (A x)) := by
    intro A B hB
    rw [(hd B).mfderiv_eq]
    exact mvfderiv_clm_comp_left ℓ (mdiffAt_mvfderiv_section hFx hB) (A x)
  rw [e1, e2 X Y hY, e2 Y X hX] at key
  simp [map_sub, key]

/-! ## The induced connection and its curvature -/

section Induced

variable {L : V →L[ℝ] V →L[ℝ] ℝ} {ι : M → V} {g : NondegMetric I M}

omit [FiniteDimensional ℝ V] in
/-- **The Levi-Civita connection of an induced metric**: `g(∇_X Y, Z) = L(D_X (dι Y), dι Z)`. -/
theorem g_cov_eq_of_induced (hL : ∀ a b, L a b = L b a) (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι)
    (hg : ∀ q u v, g.g q u v = L (dι (I := I) ι q u) (dι (I := I) ι q v))
    {cov : Connection I M} (h : cov.IsLeviCivita g) {X Y Z : Π q : M, TangentSpace I q} {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, X q⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, Y q⟩ : TangentBundle I M)) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, Z q⟩ : TangentBundle I M)) x) :
    g.g x (cov Y x (X x)) (Z x) =
      L (mvfderiv I (fun q => dι (I := I) ι q (Y q)) x (X x)) (dι (I := I) ι x (Z x)) := by
  have hιs : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, V) ∞ ι y := Eventually.of_forall fun y => hι y
  have br : ∀ {A B : Π q : M, TangentSpace I q},
      MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, A q⟩ : TangentBundle I M)) x →
      MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, B q⟩ : TangentBundle I M)) x →
      dι (I := I) ι x (mlieBracket I A B x) =
        mvfderiv I (fun q => dι (I := I) ι q (B q)) x (A x) - mvfderiv I (fun q => dι (I := I) ι q (A q)) x (B x) :=
    fun hA hB => mvfderiv_mlieBracket_vec hιs hA hB
  have gp : ∀ A B : Π q : M, TangentSpace I q, gpair g A B = fun q => L (dι (I := I) ι q (A q)) (dι (I := I) ι q (B q)) :=
    fun A B => funext fun q => hg q (A q) (B q)
  have pr : ∀ {A B : Π q : M, TangentSpace I q},
      MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, A q⟩ : TangentBundle I M)) x →
      MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, B q⟩ : TangentBundle I M)) x →
      ∀ v, mvfderiv I (gpair g A B) x v =
        L (mvfderiv I (fun q => dι (I := I) ι q (A q)) x v) (dι (I := I) ι x (B x)) +
          L (dι (I := I) ι x (A x)) (mvfderiv I (fun q => dι (I := I) ι q (B q)) x v) :=
    fun hA hB v => by
      rw [gp]; exact mvfderiv_bilin L (mdiffAt_dι_section hι hA) (mdiffAt_dι_section hι hB) v
  rw [koszul_of_isLeviCivita g h hX hY hZ]
  unfold koszul
  rw [pr hY hZ, pr hZ hX, pr hX hY, hg, hg, hg, br hX hZ, br hY hX, br hZ hY]
  set aXY := mvfderiv I (fun q => dι (I := I) ι q (Y q)) x (X x)
  set aXZ := mvfderiv I (fun q => dι (I := I) ι q (Z q)) x (X x)
  set aYX := mvfderiv I (fun q => dι (I := I) ι q (X q)) x (Y x)
  set aYZ := mvfderiv I (fun q => dι (I := I) ι q (Z q)) x (Y x)
  set aZX := mvfderiv I (fun q => dι (I := I) ι q (X q)) x (Z x)
  set aZY := mvfderiv I (fun q => dι (I := I) ι q (Y q)) x (Z x)
  set bX := dι (I := I) ι x (X x)
  set bY := dι (I := I) ι x (Y x)
  set bZ := dι (I := I) ι x (Z x)
  simp only [map_sub]
  have e1 := hL bZ aXY
  have e2 := hL aYZ bX
  have e3 := hL aZX bY
  linear_combination (e1 + e2 - e3) / 2

omit [FiniteDimensional ℝ V] [IsManifold I 2 M] [CompleteSpace E] in
/-- On the quadric `L(ι, ι) = c`: `L(ι, dι w) = 0`. -/
theorem L_ι_dι_of_quadric (hL : ∀ a b, L a b = L b a) (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι) {c : ℝ}
    (hq : ∀ q, L (ι q) (ι q) = c) (q : M) (w : TangentSpace I q) : L (ι q) (dι (I := I) ι q w) = 0 := by
  have hιd : MDifferentiableAt I 𝓘(ℝ, V) ι q := (hι q).mdifferentiableAt (by simp)
  have h : mvfderiv I (fun q => L (ι q) (ι q)) q w = L (mvfderiv I ι q w) (ι q) + L (ι q) (mvfderiv I ι q w) :=
    mvfderiv_bilin (I := I) L hιd hιd w
  have hc : (fun q => L (ι q) (ι q)) = fun _ => c := funext hq
  rw [hc, mvfderiv_const, zero_apply] at h
  rw [show mvfderiv I ι q w = dι (I := I) ι q w from rfl, hL (dι (I := I) ι q w)] at h
  linarith

omit [FiniteDimensional ℝ V] [CompleteSpace E] in
/-- **The normal part of the ambient derivative**: `L(D_Y (dι Z), ι) = -g(Y, Z)` on the quadric. -/
theorem L_mvfderiv_dι_ι (hL : ∀ a b, L a b = L b a) (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι)
    (hg : ∀ q u v, g.g q u v = L (dι (I := I) ι q u) (dι (I := I) ι q v)) {c : ℝ}
    (hq : ∀ q, L (ι q) (ι q) = c) {Z : Π q : M, TangentSpace I q} {q : M} (v : TangentSpace I q)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, Z q⟩ : TangentBundle I M)) q) :
    L (mvfderiv I (fun q => dι (I := I) ι q (Z q)) q v) (ι q) = -g.g q v (Z q) := by
  have hιd : MDifferentiableAt I 𝓘(ℝ, V) ι q := (hι q).mdifferentiableAt (by simp)
  have h : mvfderiv I (fun q => L (dι (I := I) ι q (Z q)) (ι q)) q v =
      L (mvfderiv I (fun q => dι (I := I) ι q (Z q)) q v) (ι q) + L (dι (I := I) ι q (Z q)) (mvfderiv I ι q v) :=
    mvfderiv_bilin (I := I) L (mdiffAt_dι_section hι hZ) hιd v
  have h0 : (fun q => L (dι (I := I) ι q (Z q)) (ι q)) = fun _ => 0 :=
    funext fun q' => by rw [hL]; exact L_ι_dι_of_quadric hL hι hq q' (Z q')
  rw [h0, mvfderiv_const, zero_apply] at h
  rw [show mvfderiv I ι q v = dι (I := I) ι q v from rfl, hL (dι (I := I) ι q (Z q))] at h
  rw [hg]
  linarith

omit [FiniteDimensional ℝ V] in
/-- **The induced connection is the tangential part of the ambient derivative**:
`dι (∇_Y Z) = D_Y (dι Z) + (g(Y, Z)/c) ι` on the quadric `L(ι, ι) = c`. -/
theorem dι_cov_quadric (hL : ∀ a b, L a b = L b a) (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι)
    (hg : ∀ q u v, g.g q u v = L (dι (I := I) ι q u) (dι (I := I) ι q v)) {c : ℝ} (hc : c ≠ 0)
    (hq : ∀ q, L (ι q) (ι q) = c) (hsurj : ∀ q z, L (ι q) z = 0 → ∃ w, dι (I := I) ι q w = z)
    {cov : Connection I M} (h : cov.IsLeviCivita g) {Y Z : Π q : M, TangentSpace I q} {q : M}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, Y q⟩ : TangentBundle I M)) q)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, Z q⟩ : TangentBundle I M)) q) :
    dι (I := I) ι q (cov Z q (Y q)) =
      mvfderiv I (fun q => dι (I := I) ι q (Z q)) q (Y q) + (g.g q (Y q) (Z q) / c) • ι q := by
  set R := mvfderiv I (fun q => dι (I := I) ι q (Z q)) q (Y q) + (g.g q (Y q) (Z q) / c) • ι q with hR
  have hRperp : L (ι q) R = 0 := by
    rw [hR, map_add, map_smul, hL (ι q), L_mvfderiv_dι_ι hL hι hg hq (Y q) hZ, hq, smul_eq_mul,
      div_mul_cancel₀ _ hc]
    ring
  obtain ⟨w, hw⟩ : ∃ w : TangentSpace I q, dι (I := I) ι q w = R := hsurj q R hRperp
  have hwc : w = cov Z q (Y q) := by
    have : ∀ v, g.g q (w - cov Z q (Y q)) v = 0 := by
      intro v
      set W := FiberBundle.extend E v
      have hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun q : M => (⟨q, W q⟩ : TangentBundle I M)) q :=
        mdifferentiableAt_extend _ _ v
      have hWq : W q = v := FiberBundle.extend_apply_self _ v
      have hC := g_cov_eq_of_induced hL hι hg h hY hZ hW
      rw [hWq] at hC
      rw [map_sub, sub_apply, hC, hg, hw, hR, map_add, add_apply,
        map_smul, smul_apply, L_ι_dι_of_quadric hL hι hq q v]
      simp
    exact sub_eq_zero.1 (g.nondegenerate q _ this)
  rw [← hwc, hw]

end Induced

/-! ## Constant curvature of a quadric -/

variable {n : ℕ} {I' : ModelWithCorners ℝ (Fin n → ℝ) H} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  [IsManifold I' ∞ M'] [IsManifold I' 2 M']

omit [FiniteDimensional ℝ V] in
/-- **A quadric has constant curvature `1/c`.** For a metric induced by a smooth map `ι` into a space with a symmetric
bilinear form `L`, `g(u, v) = L(dι u, dι v)`, whose image lies on `L(x, x) = c ≠ 0` with `dι` injective onto the
`L`-orthogonal complement of the point, every locally smooth Levi-Civita connection has
`R(X, Y) Z = (1/c) (g(Y, Z) X - g(X, Z) Y)`. -/
theorem hasConstantCurvature_of_quadric {L : V →L[ℝ] V →L[ℝ] ℝ} {ι : M' → V} {g : NondegMetric I' M'}
    (hL : ∀ a b, L a b = L b a) (hι : ContMDiff I' 𝓘(ℝ, V) ∞ ι)
    (hg : ∀ q u v, g.g q u v = L (dι (I := I') ι q u) (dι (I := I') ι q v)) {c : ℝ} (hc : c ≠ 0)
    (hq : ∀ q, L (ι q) (ι q) = c) (hinj : ∀ q, Function.Injective (dι (I := I') ι q))
    (hsurj : ∀ q z, L (ι q) z = 0 → ∃ w, dι (I := I') ι q w = z) :
    HasConstantCurvature g (1 / c) := by
  intro cov _ h x X₀ Y₀ Z₀
  set X := FiberBundle.extend (Fin n → ℝ) X₀
  set Y := FiberBundle.extend (Fin n → ℝ) Y₀
  set Z := FiberBundle.extend (Fin n → ℝ) Z₀
  have hXs : SmoothNearW X x := eventually_extendW x X₀
  have hYs : SmoothNearW Y x := eventually_extendW x Y₀
  have hZs : SmoothNearW Z x := eventually_extendW x Z₀
  have md : ∀ {A : Π q : M', TangentSpace I' q} {y : M'},
      ContMDiffAt I' (I'.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun q : M' => (⟨q, A q⟩ : TangentBundle I' M')) y →
      MDifferentiableAt I' (I'.prod 𝓘(ℝ, Fin n → ℝ)) (fun q : M' => (⟨q, A q⟩ : TangentBundle I' M')) y :=
    fun hA => hA.mdifferentiableAt (by simp)
  have hX := md hXs.self_of_nhds
  have hY := md hYs.self_of_nhds
  have hZ := md hZs.self_of_nhds
  have eX : X x = X₀ := FiberBundle.extend_apply_self _ X₀
  have eY : Y x = Y₀ := FiberBundle.extend_apply_self _ Y₀
  have eZ : Z x = Z₀ := FiberBundle.extend_apply_self _ Z₀
  rw [← eX, ← eY, ← eZ, curvatureAt_apply_eventuallyW cov X Y Z x hXs hYs hZs]
  apply hinj x
  -- the fields `∇_Y Z` and `∇_X Z` near `x`
  set U := fun y => cov Z y (Y y) with hU
  set U' := fun y => cov Z y (X y) with hU'
  have hUs : SmoothNearW U x := by
    filter_upwards [hYs, eventually_eventually_nhds.2 hZs] with y hy hz
    exact contMDiffAt_covApplyW cov hy hz
  have hU's : SmoothNearW U' x := by
    filter_upwards [hXs, eventually_eventually_nhds.2 hZs] with y hy hz
    exact contMDiffAt_covApplyW cov hy hz
  have hB := smoothNear_mlieBracketW hXs hYs
  -- `dι U` near `x`
  have hdU : (fun q => dι (I := I') ι q (U q)) =ᶠ[𝓝 x]
      fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (Y q) + (g.g q (Y q) (Z q) / c) • ι q := by
    filter_upwards [hYs, hZs] with q hy hz
    exact dι_cov_quadric hL hι hg hc hq hsurj h (md hy) (md hz)
  have hdU' : (fun q => dι (I := I') ι q (U' q)) =ᶠ[𝓝 x]
      fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (X q) + (g.g q (X q) (Z q) / c) • ι q := by
    filter_upwards [hXs, hZs] with q hy hz
    exact dι_cov_quadric hL hι hg hc hq hsurj h (md hy) (md hz)
  have hιd : MDifferentiableAt I' 𝓘(ℝ, V) ι x := (hι x).mdifferentiableAt (by simp)
  have hFZ : ∀ᶠ y in 𝓝 x, ContMDiffAt I' 𝓘(ℝ, V) ∞ (fun q => dι (I := I') ι q (Z q)) y := by
    filter_upwards [hZs] with y hy
    exact contMDiffAt_dι_section hι hy
  have hDYZ : MDifferentiableAt I' 𝓘(ℝ, V) (fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (Y q)) x :=
    mdiffAt_mvfderiv_section hFZ.self_of_nhds hY
  have hDXZ : MDifferentiableAt I' 𝓘(ℝ, V) (fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (X q)) x :=
    mdiffAt_mvfderiv_section hFZ.self_of_nhds hX
  have hdiv : ∀ {f : M' → ℝ}, MDifferentiableAt I' 𝓘(ℝ, ℝ) f x →
      MDifferentiableAt I' 𝓘(ℝ, ℝ) (fun q => f q / c) x := fun hf => by
    have := hf.mul (mdifferentiableAt_const (c := c⁻¹))
    exact this.congr_of_eventuallyEq (Eventually.of_forall fun q => by simp [div_eq_mul_inv])
  have hgYZ : MDifferentiableAt I' 𝓘(ℝ, ℝ) (fun q => g.g q (Y q) (Z q) / c) x := hdiv (mdiffAt_gpair g hY hZ)
  have hgXZ : MDifferentiableAt I' 𝓘(ℝ, ℝ) (fun q => g.g q (X q) (Z q) / c) x := hdiv (mdiffAt_gpair g hX hZ)
  -- derivative of `(g(A, Z)/c) ι` along `B`
  have dsm : ∀ {A : Π q : M', TangentSpace I' q} (B : Π q : M', TangentSpace I' q),
      MDifferentiableAt I' 𝓘(ℝ, ℝ) (fun q => g.g q (A q) (Z q) / c) x →
      mvfderiv I' (fun q => (g.g q (A q) (Z q) / c) • ι q) x (B x) =
        (g.g x (A x) (Z x) / c) • dι (I := I') ι x (B x) +
          (mvfderiv I' (fun q => g.g q (A q) (Z q) / c) x (B x)) • ι x := by
    intro A B hA
    have := mvfderiv_smul (I := I') hA hιd
    exact congrArg (fun T => T (B x)) this
  have dgc : ∀ {A : Π q : M', TangentSpace I' q},
      MDifferentiableAt I' (I'.prod 𝓘(ℝ, Fin n → ℝ)) (fun q : M' => (⟨q, A q⟩ : TangentBundle I' M')) x →
      ∀ (B : Π q : M', TangentSpace I' q),
      mvfderiv I' (fun q => g.g q (A q) (Z q) / c) x (B x) = mvfderiv I' (gpair g A Z) x (B x) / c := by
    intro A hA B
    have := mvfderiv_clm_comp_left (I := I') ((1 / c) • ContinuousLinearMap.id ℝ ℝ) (mdiffAt_gpair g hA hZ) (B x)
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] at this
    rw [show (fun q => g.g q (A q) (Z q) / c) = fun q => 1 / c * gpair g A Z q from
      funext fun q => by simp [gpair, div_eq_mul_inv, mul_comm]]
    rw [this]; ring
  have haddY : mvfderiv I' (fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (Y q) +
      (g.g q (Y q) (Z q) / c) • ι q) x =
      mvfderiv I' (fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (Y q)) x +
        mvfderiv I' (fun q => (g.g q (Y q) (Z q) / c) • ι q) x := mvfderiv_add hDYZ (hgYZ.smul hιd)
  have haddX : mvfderiv I' (fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (X q) +
      (g.g q (X q) (Z q) / c) • ι q) x =
      mvfderiv I' (fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (X q)) x +
        mvfderiv I' (fun q => (g.g q (X q) (Z q) / c) • ι q) x := mvfderiv_add hDXZ (hgXZ.smul hιd)
  -- the three terms of the curvature
  have t1 : dι (I := I') ι x (cov U x (X x)) =
      mvfderiv I' (fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (Y q)) x (X x) +
        (g.g x (Y x) (Z x) / c) • dι (I := I') ι x (X x) +
        (mvfderiv I' (gpair g Y Z) x (X x) / c) • ι x + (g.g x (X x) (U x) / c) • ι x := by
    rw [dι_cov_quadric hL hι hg hc hq hsurj h hX (md hUs.self_of_nhds), mvfderiv_congrW hdU,
      haddY, add_apply, dsm X hgYZ, dgc hY X]
    abel
  have t2 : dι (I := I') ι x (cov U' x (Y x)) =
      mvfderiv I' (fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (X q)) x (Y x) +
        (g.g x (X x) (Z x) / c) • dι (I := I') ι x (Y x) +
        (mvfderiv I' (gpair g X Z) x (Y x) / c) • ι x + (g.g x (Y x) (U' x) / c) • ι x := by
    rw [dι_cov_quadric hL hι hg hc hq hsurj h hY (md hU's.self_of_nhds), mvfderiv_congrW hdU',
      haddX, add_apply, dsm Y hgXZ, dgc hX Y]
    abel
  have t3 : dι (I := I') ι x (cov Z x (mlieBracket I' X Y x)) =
      mvfderiv I' (fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (Y q)) x (X x) -
        mvfderiv I' (fun q => mvfderiv I' (fun q => dι (I := I') ι q (Z q)) q (X q)) x (Y x) +
        (g.g x (mlieBracket I' X Y x) (Z x) / c) • ι x := by
    rw [dι_cov_quadric hL hι hg hc hq hsurj h (md hB.self_of_nhds) hZ, mvfderiv_mlieBracket_vec hFZ hX hY]
  -- metric compatibility and torsion
  have cY : mvfderiv I' (gpair g Y Z) x (X x) = g.g x (cov Y x (X x)) (Z x) + g.g x (Y x) (cov Z x (X x)) :=
    h.2 X Y Z x hX hY hZ
  have cX : mvfderiv I' (gpair g X Z) x (Y x) = g.g x (cov X x (Y x)) (Z x) + g.g x (X x) (cov Z x (Y x)) :=
    h.2 Y X Z x hY hX hZ
  have tor := cov_torsionW h.1 (X := X) (Y := Y) (x := x) hX hY
  have hcoef : mvfderiv I' (gpair g Y Z) x (X x) / c + g.g x (X x) (U x) / c -
      (mvfderiv I' (gpair g X Z) x (Y x) / c + g.g x (Y x) (U' x) / c) -
      g.g x (mlieBracket I' X Y x) (Z x) / c = 0 := by
    rw [cY, cX, ← tor, hU, hU']
    simp only [map_sub, sub_apply]
    rw [g.symm x (X x) (cov Z x (Y x)), g.symm x (Y x) (cov Z x (X x))]
    ring
  have hz : (mvfderiv I' (gpair g Y Z) x (X x) / c + g.g x (X x) (U x) / c -
      (mvfderiv I' (gpair g X Z) x (Y x) / c + g.g x (Y x) (U' x) / c) -
      g.g x (mlieBracket I' X Y x) (Z x) / c) • ι x = 0 := by
    rw [hcoef, zero_smul]
  erw [map_sub, map_sub, map_smul, map_sub, map_smul, map_smul]
  rw [t1, t2, t3]
  linear_combination (norm := module) hz

end Lightlike
