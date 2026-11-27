/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Bundle

/-!
# Fibrewise actions on total spaces

Adapted from Tau Ceti (module TauCeti.Algebra.Group.Action.TotalSpace,
revision 2a9233e5b, Apache 2.0 license).

An action on each fibre acts on the total space without changing the base point. This lets
fibrewise bundle actions use the usual group-action interfaces on their total spaces.
-/


namespace Bundle.TotalSpace

variable {B F G : Type*} {E : B → Type*}

instance instSMul [∀ b, SMul G (E b)] : SMul G (TotalSpace F E) where
  smul g p := ⟨p.proj, g • p.snd⟩

@[simp]
theorem smul_mk [∀ b, SMul G (E b)] (g : G) (b : B) (v : E b) :
    g • (⟨b, v⟩ : TotalSpace F E) = ⟨b, g • v⟩ := rfl

@[simp]
theorem proj_smul [∀ b, SMul G (E b)] (g : G) (p : TotalSpace F E) :
    (g • p).proj = p.proj := rfl

@[simp]
theorem snd_smul [∀ b, SMul G (E b)] (g : G) (p : TotalSpace F E) :
    (g • p).snd = g • p.snd := rfl

instance instMulAction [Monoid G] [∀ b, MulAction G (E b)] : MulAction G (TotalSpace F E) where
  one_smul p := by cases p; simp
  mul_smul g h p := by cases p; simp [mul_smul]

end Bundle.TotalSpace
