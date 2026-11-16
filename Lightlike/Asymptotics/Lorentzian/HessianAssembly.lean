import Lightlike.Asymptotics.Lorentzian.HessianNode

/-!
# The Hessian of the Lorentzian vertex action, assembled from its blocks

`hessZZ_cross`, `hessXX_cross`: the mixed second derivatives along two different spinors, or two different
nodes, vanish (BDFHP Appendix A, p. 32, eqs. (58), (59)). `nodeQuad`, `nodeBilin`: the node block as a quadratic
form on `ℝ⁶` (rotations and boosts) and its polarisation (`nodeBilin_self`, `nodeBilin_comm`).
`hessBlockMatrix`: the `44 × 44` matrix of the blocks `H^{XX}` (`hessXX_block`), `H^{zz}` (`hessZZ_block`) and
`H^{Xz}` (`hessXZ_block`), symmetric (`hessBlockMatrix_symm`). That it equals the matrix of second derivatives of
the action in a chart at a critical point is not proved here (it needs the chart and the vanishing of the first
derivative).
-/

open Complex
open Lightlike.Lorentz (SL2C)
open Lightlike.Asymptotics.EPRL
open scoped ComplexConjugate Matrix

namespace Lightlike.Asymptotics.Lorentzian

/-- **The spinor blocks are decoupled over the edges** (the structure of `H^{zz}` in BDFHP Appendix A, p. 33:
a 20 × 20 matrix of 2 × 2 blocks on the diagonal): for two different edges the mixed second derivative of the
vertex action along `z_e ↦ z_e + s δ` and `z_{e'} ↦ z_{e'} + t δ'` is `0`, because `z_e` appears only in the
term of the edge `e`. -/
theorem hessZZ_cross (j p : Fin 10 → ℝ) (g : BdryData) (X : Fin 5 → SL2C) (z : Fin 10 → Spinor)
    {e e' : Fin 10} (hee : e ≠ e') (δ δ' : Spinor) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => lorAction j p g X
      (Function.update (Function.update z e (z e + s • δ)) e' (z e' + t • δ'))) 0) 0 = 0 := by
  set T : Fin 10 → Spinor → ℂ := fun k v => triAction (j k) (p k)
    (spinAct (X (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ v) (firstCol (g k 0))
    (spinAct (X (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ v) (firstCol (g k 1)) with hT
  set K : ℂ := ∑ k ∈ (Finset.univ.erase e).erase e', T k (z k) with hK
  have hsplit : ∀ s t : ℝ, lorAction j p g X
      (Function.update (Function.update z e (z e + s • δ)) e' (z e' + t • δ')) =
      (T e (z e + s • δ) + K) + T e' (z e' + t • δ') := by
    intro s t
    have h1 : lorAction j p g X (Function.update (Function.update z e (z e + s • δ)) e' (z e' + t • δ')) =
        ∑ k, T k (Function.update (Function.update z e (z e + s • δ)) e' (z e' + t • δ') k) := rfl
    rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ e),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hee.symm, Finset.mem_univ e'⟩)]
    have hA : Function.update (Function.update z e (z e + s • δ)) e' (z e' + t • δ') e =
        z e + s • δ := by
      rw [Function.update_of_ne hee, Function.update_self]
    have hB : Function.update (Function.update z e (z e + s • δ)) e' (z e' + t • δ') e' =
        z e' + t • δ' := Function.update_self _ _ _
    have hC : ∑ k ∈ (Finset.univ.erase e).erase e',
        T k (Function.update (Function.update z e (z e + s • δ)) e' (z e' + t • δ') k) = K := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : k ≠ e' := Finset.ne_of_mem_erase hk
      have hk2 : k ≠ e := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
      rw [Function.update_of_ne hk1, Function.update_of_ne hk2]
    rw [hA, hB, hC]; ring
  have hfun : (fun s : ℝ => deriv (fun t : ℝ => lorAction j p g X
      (Function.update (Function.update z e (z e + s • δ)) e' (z e' + t • δ'))) 0) =
      fun _ => deriv (fun t : ℝ => T e' (z e' + t • δ')) 0 := by
    funext s
    have : (fun t : ℝ => lorAction j p g X
      (Function.update (Function.update z e (z e + s • δ)) e' (z e' + t • δ'))) =
        fun t => (T e (z e + s • δ) + K) + T e' (z e' + t • δ') := funext fun t => hsplit s t
    rw [this, deriv_const_add]
  rw [hfun]
  exact deriv_const _ _

/-- **The node blocks are decoupled** (BDFHP (59): "derivatives with respect to two different variables will be
zero"): for two different nodes `a ≠ b` the mixed second derivative of the vertex action along
`X_a ↦ X_a Ya(s)` and `X_b ↦ X_b Yb(t)` (`Yb 0 = 1`, `Yb' = Yb L`) is `0`. The first variation in `t` at a
fixed `s` involves only the ends at `b`, whose spinors do not depend on `s`. The hypothesis `hslit` is that the
overlap products are off the cut at the moved configuration `X_a ↦ X_a Ya(s)`, for `s` near `0`.  The curve `Yb` is only assumed to have the entrywise derivative `Yb 0 · L` at `0`. -/
theorem hessXX_cross {j p : Fin 10 → ℝ} {n : Fin 10 → ℕ} (hj : ∀ e, j e = (n e : ℝ) / 2)
    (g : BdryData) (X : Fin 5 → SL2C) (z : Fin 10 → Spinor) {a b : Fin 5} (hab : a ≠ b)
    (Ya Yb : ℝ → SL2C) (L : Matrix (Fin 2) (Fin 2) ℂ) (hYb0 : Yb 0 = 1)
    (hYb : ∀ i k, HasDerivAt (fun s => (Yb s : Matrix (Fin 2) (Fin 2) ℂ) i k)
      (((Yb 0 : Matrix (Fin 2) (Fin 2) ℂ) * L) i k) 0)
    (hslit : ∀ᶠ s : ℝ in nhds 0, ∀ e, inner ℂ
        (spinAct ((Function.update X a (X a * Ya s) (edgeSrc e) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))
        (firstCol (g e 0)) *
      inner ℂ (jMap (firstCol (g e 1)))
        (spinAct ((Function.update X a (X a * Ya s) (edgeTgt e) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          (z e)) ∈ Complex.slitPlane) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => lorAction j p g
      (Function.update (Function.update X a (X a * Ya s)) b (X b * Yb t)) z) 0) 0 = 0 := by
  set Xs : ℝ → Fin 5 → SL2C := fun s => Function.update X a (X a * Ya s) with hXs
  have hXsb : ∀ s, Xs s b = X b := fun s => Function.update_of_ne hab.symm _ _
  set Zs : Fin 10 → ℝ → ℝ → Spinor := fun e s u =>
    spinAct ((Function.update (Xs s) b (X b * Yb u) (edgeSrc e) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)
    with hZs
  set Zt : Fin 10 → ℝ → ℝ → Spinor := fun e s u =>
    spinAct ((Function.update (Xs s) b (X b * Yb u) (edgeTgt e) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)
    with hZt
  have hX0 : ∀ s, Function.update (Xs s) b (X b * Yb 0) = Xs s := fun s => by
    rw [hYb0, mul_one]; exact Function.update_eq_self_iff.2 (hXsb s).symm
  have hdZs : ∀ e s, HasDerivAt (Zs e s) (if edgeSrc e = b then
      spinAct Lᴴ (Zs e s 0) else 0) 0 := by
    intro e s
    by_cases h : edgeSrc e = b
    · have hfun : Zs e s = fun u => spinAct (Yb u : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          (spinAct (X b : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) := by
        funext u
        simp only [hZs, h, Function.update_self, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.conjTranspose_mul, spinAct_mul]
      rw [hfun]
      simp only [h, ↓reduceIte]
      exact hasDerivAt_orbit_pt L Yb 0 hYb _
    · have hfun : Zs e s = fun _ => spinAct ((Xs s (edgeSrc e) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) := by
        funext u
        simp only [hZs, Function.update_of_ne h]
      rw [hfun]
      simp only [h, ↓reduceIte]
      exact hasDerivAt_const 0 _
  have hdZt : ∀ e s, HasDerivAt (Zt e s) (if edgeTgt e = b then
      spinAct Lᴴ (Zt e s 0) else 0) 0 := by
    intro e s
    by_cases h : edgeTgt e = b
    · have hfun : Zt e s = fun u => spinAct (Yb u : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          (spinAct (X b : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) := by
        funext u
        simp only [hZt, h, Function.update_self, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.conjTranspose_mul, spinAct_mul]
      rw [hfun]
      simp only [h, ↓reduceIte]
      exact hasDerivAt_orbit_pt L Yb 0 hYb _
    · have hfun : Zt e s = fun _ => spinAct ((Xs s (edgeTgt e) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) := by
        funext u
        simp only [hZt, Function.update_of_ne h]
      rw [hfun]
      simp only [h, ↓reduceIte]
      exact hasDerivAt_const 0 _
  set Ws : Fin 10 → ℝ → Spinor := fun e s =>
    if edgeSrc e = b then spinAct Lᴴ (Zs e s 0) else 0 with hWs
  set Wt : Fin 10 → ℝ → Spinor := fun e s =>
    if edgeTgt e = b then spinAct Lᴴ (Zt e s 0) else 0 with hWt
  set D : Fin 10 → ℝ → ℂ := fun e s =>
    srcCoeff (n e) (p e) (firstCol (g e 0)) (Zs e s 0) (Ws e s) +
      tgtCoeff (n e) (p e) (firstCol (g e 1)) (Zt e s 0) (Wt e s) with hD
  have hZ0s : ∀ e s, Zs e s 0 = spinAct ((Xs s (edgeSrc e) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) := by
    intro e s; simp only [hZs, hX0]
  have hZ0t : ∀ e s, Zt e s 0 = spinAct ((Xs s (edgeTgt e) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) := by
    intro e s; simp only [hZt, hX0]
  have hev : ∀ᶠ s : ℝ in nhds 0, ∀ e, HasDerivAt
      (fun u => triAction (j e) (p e) (Zs e s u) (firstCol (g e 0)) (Zt e s u) (firstCol (g e 1)))
      (D e s) 0 := by
    filter_upwards [hslit] with s hs e
    have hpr := hs e
    have h0 : (0 : ℂ) ∉ Complex.slitPlane := by simp [Complex.slitPlane]
    have hne0 : inner ℂ (Zs e s 0) (firstCol (g e 0)) * inner ℂ (jMap (firstCol (g e 1))) (Zt e s 0) ≠ 0 := by
      rw [hZ0s, hZ0t]; exact fun h => h0 (h ▸ hpr)
    have h1 := left_ne_zero_of_mul hne0
    have h2 := right_ne_zero_of_mul hne0
    have hz : Zs e s 0 ≠ 0 := fun h => h1 (by rw [h]; simp)
    have hz' : Zt e s 0 ≠ 0 := fun h => h2 (by rw [h]; simp)
    rw [hj e]
    exact hasDerivAt_triAction_curve_at (n e) (p e) (Ws e s) (Wt e s) (by simpa [hWs] using hdZs e s)
      (by simpa [hWt] using hdZt e s) hz hz' h1 h2 (by rw [hZ0s, hZ0t]; exact hpr)
  set E : Fin 10 → ℂ := fun e =>
    (if edgeSrc e = b then srcCoeff (n e) (p e) (firstCol (g e 0))
      (spinAct (X b : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))
      (spinAct Lᴴ (spinAct (X b : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))) else 0) +
    (if edgeTgt e = b then tgtCoeff (n e) (p e) (firstCol (g e 1))
      (spinAct (X b : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))
      (spinAct Lᴴ (spinAct (X b : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))) else 0) with hE
  have hDE : ∀ e s, D e s = E e := by
    intro e s
    have hsrc : (srcCoeff (n e) (p e) (firstCol (g e 0)) (Zs e s 0) (Ws e s)) =
        if edgeSrc e = b then srcCoeff (n e) (p e) (firstCol (g e 0))
          (spinAct (X b : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))
          (spinAct Lᴴ (spinAct (X b : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))) else 0 := by
      by_cases h : edgeSrc e = b
      · simp only [h, ↓reduceIte, hWs, hZ0s, hXsb]
      · simp only [h, ↓reduceIte, hWs, srcCoeff_zero_dir]
    have htgt : (tgtCoeff (n e) (p e) (firstCol (g e 1)) (Zt e s 0) (Wt e s)) =
        if edgeTgt e = b then tgtCoeff (n e) (p e) (firstCol (g e 1))
          (spinAct (X b : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))
          (spinAct Lᴴ (spinAct (X b : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))) else 0 := by
      by_cases h : edgeTgt e = b
      · simp only [h, ↓reduceIte, hWt, hZ0t, hXsb]
      · simp only [h, ↓reduceIte, hWt, tgtCoeff_zero_dir]
    simp only [hD, hsrc, htgt, hE]
  have hEq : (fun s : ℝ => deriv (fun t : ℝ => lorAction j p g
      (Function.update (Function.update X a (X a * Ya s)) b (X b * Yb t)) z) 0) =ᶠ[nhds 0]
      fun _ => ∑ e, E e := by
    filter_upwards [hev] with s hs
    have hfun : (fun t : ℝ => lorAction j p g
        (Function.update (Function.update X a (X a * Ya s)) b (X b * Yb t)) z) =
        fun u => ∑ e, triAction (j e) (p e) (Zs e s u) (firstCol (g e 0)) (Zt e s u) (firstCol (g e 1)) :=
      rfl
    rw [hfun, (HasDerivAt.fun_sum (u := Finset.univ) (fun e _ => hs e)).deriv]
    exact Finset.sum_congr rfl fun e _ => hDE e s
  rw [hEq.deriv_eq]
  exact deriv_const _ _

/-- The quadratic form of the node block of the Hessian at node `a` on `v = (α, β) ∈ ℝ⁶` (rotation `α`, boost
`β`): the sum over the ends at `a` of `endForm` (the closed form of `hessXX_block`, BDFHP Appendix A (60), (61) for
the source ends up to the factor documented there). -/
noncomputable def nodeQuad (j p : Fin 10 → ℝ) (g : BdryData) (a : Fin 5) (v : Fin 6 → ℝ) : ℂ :=
  ∑ e, if edgeSrc e = a ∨ edgeTgt e = a then
    endForm (j e) (p e) (endSign e a) (endVec g e a) (fun i : Fin 3 => v ⟨i.val, by omega⟩)
      (fun i : Fin 3 => v ⟨i.val + 3, by omega⟩) else 0

/-- The symmetric bilinear form of `nodeQuad` by polarisation. -/
noncomputable def nodeBilin (j p : Fin 10 → ℝ) (g : BdryData) (a : Fin 5) (v w : Fin 6 → ℝ) : ℂ :=
  (nodeQuad j p g a (v + w) - nodeQuad j p g a v - nodeQuad j p g a w) / 2

/-- `nodeQuad` is homogeneous of degree two. -/
theorem nodeQuad_smul (j p : Fin 10 → ℝ) (g : BdryData) (a : Fin 5) (c : ℝ) (v : Fin 6 → ℝ) :
    nodeQuad j p g a (c • v) = (c : ℂ) ^ 2 * nodeQuad j p g a v := by
  unfold nodeQuad
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs
  · simp only [endForm, projForm, tripleForm, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
    push_cast
    ring
  · simp

/-- Polarisation recovers the quadratic form: `nodeBilin v v = nodeQuad v`. -/
theorem nodeBilin_self (j p : Fin 10 → ℝ) (g : BdryData) (a : Fin 5) (v : Fin 6 → ℝ) :
    nodeBilin j p g a v v = nodeQuad j p g a v := by
  have h2 : v + v = (2 : ℝ) • v := by rw [two_smul]
  unfold nodeBilin
  rw [h2, nodeQuad_smul]
  push_cast
  ring

/-- `nodeBilin` is symmetric. -/
theorem nodeBilin_comm (j p : Fin 10 → ℝ) (g : BdryData) (a : Fin 5) (v w : Fin 6 → ℝ) :
    nodeBilin j p g a v w = nodeBilin j p g a w v := by
  unfold nodeBilin
  rw [add_comm v w]
  ring

/-- The unit vector `e_k` of `ℝ⁶` (the first three coordinates are rotations, the last three boosts). -/
noncomputable def unitDir (k : Fin 6) : Fin 6 → ℝ := Pi.single k 1

/-- The Lie algebra element `genMat (β + i α)` of the direction `v = (α, β)`: the orbit `Y' = Y · genDir v`. -/
noncomputable def genDir (v : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  genMat (fun i : Fin 3 => (v ⟨i.val + 3, by omega⟩ : ℂ) + Complex.I * (v ⟨i.val, by omega⟩ : ℂ))

/-- The pair `(f_w', f_w̄')` of the mixed block `H^{Xz}` for the node `a`, the edge `e` and the Lie algebra
element `L` (`xzSource` at a source end, `xzTarget` at a target end, `0` otherwise). -/
noncomputable def mixedPair (j p : Fin 10 → ℝ) (g : BdryData) (X : Fin 5 → SL2C) (w : Fin 10 → ℂ)
    (a : Fin 5) (e : Fin 10) (L : Matrix (Fin 2) (Fin 2) ℂ) : ℂ × ℂ :=
  (if edgeSrc e = a then xzSource (j e) (p e) (X a : Matrix (Fin 2) (Fin 2) ℂ) L (firstCol (g e 0)) (w e)
    else 0) +
  (if edgeTgt e = a then xzTarget (j e) (p e) (X a : Matrix (Fin 2) (Fin 2) ℂ) L (firstCol (g e 1)) (w e)
    else 0)

/-- The entry of `H^{Xz}` for the generator `k` of the node `a` and the component `c` (`0`: `u`, `1`: `v`,
`w = u + i v`) of the edge `e`: `f_w' + f_w̄'` and `i (f_w' - f_w̄')`. -/
noncomputable def mixedEntry (j p : Fin 10 → ℝ) (g : BdryData) (X : Fin 5 → SL2C) (w : Fin 10 → ℂ)
    (a : Fin 5) (e : Fin 10) (k : Fin 6) (c : Fin 2) : ℂ :=
  if c = 0 then (mixedPair j p g X w a e (genDir (unitDir k))).1 + (mixedPair j p g X w a e (genDir (unitDir k))).2
  else Complex.I * ((mixedPair j p g X w a e (genDir (unitDir k))).1 -
    (mixedPair j p g X w a e (genDir (unitDir k))).2)

/-- The `2 × 2` block `H^{zz}` of the edge `e` in the real coordinates `(u, v)` of `w = u + i v`, from the Wirtinger
entries: `H_uu = f_ww + f_w̄w̄ + 2 f_ww̄`, `H_vv = -(f_ww + f_w̄w̄) + 2 f_ww̄`, `H_uv = i (f_ww - f_w̄w̄)`. -/
noncomputable def zzEntry (j p : Fin 10 → ℝ) (g : BdryData) (X : Fin 5 → SL2C) (w : Fin 10 → ℂ)
    (e : Fin 10) (c d : Fin 2) : ℂ :=
  if c = d then
    (if c = 0 then
      (zzWirtinger (j e) (p e) (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ) (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)
        (firstCol (g e 0)) (firstCol (g e 1)) (w e)).1 +
      (zzWirtinger (j e) (p e) (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ) (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)
        (firstCol (g e 0)) (firstCol (g e 1)) (w e)).2.2 +
      2 * (zzWirtinger (j e) (p e) (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)
        (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ) (firstCol (g e 0)) (firstCol (g e 1)) (w e)).2.1
    else
      -((zzWirtinger (j e) (p e) (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ) (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)
        (firstCol (g e 0)) (firstCol (g e 1)) (w e)).1 +
      (zzWirtinger (j e) (p e) (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ) (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)
        (firstCol (g e 0)) (firstCol (g e 1)) (w e)).2.2) +
      2 * (zzWirtinger (j e) (p e) (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)
        (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ) (firstCol (g e 0)) (firstCol (g e 1)) (w e)).2.1)
  else Complex.I * ((zzWirtinger (j e) (p e) (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)
      (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ) (firstCol (g e 0)) (firstCol (g e 1)) (w e)).1 -
    (zzWirtinger (j e) (p e) (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ) (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)
      (firstCol (g e 0)) (firstCol (g e 1)) (w e)).2.2)

/-- **The assembled Hessian** (BDFHP Appendix A, (58)): the `44 × 44` matrix of the second derivatives of the
vertex action in the coordinates `(θ₁, θ₂, θ₃, φ₁, φ₂, φ₃)` of each of the nodes `X_1, ..., X_4` (the node `X_5`
is gauge fixed) followed by `(u, v)` of each edge. `XX` is block diagonal over the nodes (`hessXX_cross`), `zz` is
block diagonal over the edges (`hessZZ_cross`), and the mixed block is `mixedEntry`. -/
noncomputable def hessBlockMatrix (j p : Fin 10 → ℝ) (g : BdryData) (X : Fin 5 → SL2C) (w : Fin 10 → ℂ) :
    Matrix (Fin 44) (Fin 44) ℂ :=
  Matrix.of fun i k =>
    if hi : i.val < 24 then
      if hk : k.val < 24 then
        (if i.val / 6 = k.val / 6 then
          nodeBilin j p g ⟨i.val / 6, by omega⟩ (unitDir ⟨i.val % 6, by omega⟩) (unitDir ⟨k.val % 6, by omega⟩)
        else 0)
      else mixedEntry j p g X w ⟨i.val / 6, by omega⟩ ⟨(k.val - 24) / 2, by omega⟩ ⟨i.val % 6, by omega⟩
        ⟨(k.val - 24) % 2, by omega⟩
    else
      if hk : k.val < 24 then
        mixedEntry j p g X w ⟨k.val / 6, by omega⟩ ⟨(i.val - 24) / 2, by omega⟩ ⟨k.val % 6, by omega⟩
          ⟨(i.val - 24) % 2, by omega⟩
      else
        (if (i.val - 24) / 2 = (k.val - 24) / 2 then
          zzEntry j p g X w ⟨(i.val - 24) / 2, by omega⟩ ⟨(i.val - 24) % 2, by omega⟩
            ⟨(k.val - 24) % 2, by omega⟩
        else 0)

/-- The assembled Hessian is symmetric. -/
theorem hessBlockMatrix_symm (j p : Fin 10 → ℝ) (g : BdryData) (X : Fin 5 → SL2C) (w : Fin 10 → ℂ) :
    (hessBlockMatrix j p g X w)ᵀ = hessBlockMatrix j p g X w := by
  ext i k
  rcases lt_or_ge i.val 24 with hi | hi <;> rcases lt_or_ge k.val 24 with hk | hk
  · simp only [hessBlockMatrix, Matrix.transpose_apply, Matrix.of_apply, hi, hk, ↓reduceDIte]
    by_cases h : i.val / 6 = k.val / 6
    · have h' : k.val / 6 = i.val / 6 := h.symm
      simp only [eq_true h, eq_true h', ↓reduceIte]
      have : (⟨k.val / 6, by omega⟩ : Fin 5) = ⟨i.val / 6, by omega⟩ := Fin.ext h'
      rw [this, nodeBilin_comm]
    · have h' : ¬ k.val / 6 = i.val / 6 := fun e => h e.symm
      simp only [h, h', ↓reduceIte]
  · have hk' : ¬ k.val < 24 := not_lt.2 hk
    simp only [hessBlockMatrix, Matrix.transpose_apply, Matrix.of_apply, hi, hk', ↓reduceDIte]
  · have hi' : ¬ i.val < 24 := not_lt.2 hi
    simp only [hessBlockMatrix, Matrix.transpose_apply, Matrix.of_apply, hi', hk, ↓reduceDIte]
  · have hi' : ¬ i.val < 24 := not_lt.2 hi
    have hk' : ¬ k.val < 24 := not_lt.2 hk
    simp only [hessBlockMatrix, Matrix.transpose_apply, Matrix.of_apply, hi', hk', ↓reduceDIte]
    by_cases h : (i.val - 24) / 2 = (k.val - 24) / 2
    · have h' : (k.val - 24) / 2 = (i.val - 24) / 2 := h.symm
      simp only [eq_true h, eq_true h', ↓reduceIte]
      have : (⟨(k.val - 24) / 2, by omega⟩ : Fin 10) = ⟨(i.val - 24) / 2, by omega⟩ := Fin.ext h'
      rw [this]
      by_cases h01 : (⟨(k.val - 24) % 2, by omega⟩ : Fin 2) = ⟨(i.val - 24) % 2, by omega⟩
      · rw [h01]
      · have h10 : ¬ (⟨(i.val - 24) % 2, by omega⟩ : Fin 2) = ⟨(k.val - 24) % 2, by omega⟩ :=
          fun e => h01 e.symm
        unfold zzEntry
        simp only [h01, h10, ↓reduceIte]
    · have h' : ¬ (k.val - 24) / 2 = (i.val - 24) / 2 := fun e => h e.symm
      simp only [h, h', ↓reduceIte]

end Lightlike.Asymptotics.Lorentzian
