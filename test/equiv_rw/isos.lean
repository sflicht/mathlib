/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.equiv_rw
import category_theory.functorial
import category_theory.types
import algebra.category.CommRing.basic

universes u

open category_theory

-- TODO eventually, we should move this lemma (and its analogues for all concrete categories)
-- to the files where those categories are set up.
-- While `equiv_rw` is being actively developed, I'd prefer not to do that, so as not to
-- make all the concrete categories dependent on `equiv_rw`.
-- (We probably should write a command that synthesizes all the apparatus of a concrete category!)
@[functoriality]
lemma coe_as_forget_obj (R : Ring.{u}) : (R : Type u) = (forget Ring.{u}).obj R := rfl

set_option trace.equiv_rw_type true

example (R S : Ring.{u}) (i : R ≅ S) (r : R) : S :=
begin
  equiv_rw i at r,
  exact r,
end

example (R S : Ring.{u}) (i : R ≅ S) (s : S) : R :=
begin
  equiv_rw i,
  dsimp,
  exact s,
end
