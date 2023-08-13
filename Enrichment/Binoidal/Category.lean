/- Adapted from https://github.com/leanprover-community/mathlib4/blob/9f8f772f02755375a8301679aeb67186742c59fa/Mathlib/CategoryTheory/Monoidal/Category.lean#L73-L147 -/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Order.Monotone.Basic
open CategoryTheory
open Quiver

class BinoidalCategory (C: Type u) [Category C] :=
  /-- curried tensor product of objects -/
  tensorObj: C -> C -> C
  /-- left whiskering for morphisms -/
  whiskerLeft: (X: C) -> {Y₁ Y₂: C} -> (Y₁ ⟶ Y₂) -> (tensorObj X Y₁ ⟶ tensorObj X Y₂)
  /-- right whiskering for morphisms -/
  whiskerRight: {X₁ X₂: C} -> (X₁ ⟶ X₂) -> (Y: C) -> (tensorObj X₁ Y ⟶ tensorObj X₂ Y)
  /-- left tensor product `f ⋉ g` -/
  leftTensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) :=
    whiskerRight f _ ≫ whiskerLeft _ g
  /-- right tensor product `f ⋊ g` -/
  rightTensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) :=
    whiskerLeft _ g ≫ whiskerRight f _
  leftTensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) :
    leftTensorHom f g = whiskerRight f _ ≫ whiskerLeft _ g := by
      aesop_cat
  rightTensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) :
    rightTensorHom f g = whiskerLeft _ g ≫ whiskerRight f _ := by
      aesop_cat

/- Notation based on https://www.dpmms.cam.ac.uk/~martin/Research/Publications/2002/bh02.pdf -/

namespace BinoidalCategory

/-- Notation for `tensorObj`, the tensor product of objects in a binoidal category -/
scoped infixr:70 " ⊗ " => tensorObj

/-- Notation for the `whiskerLeft` operator of binoidal categories -/
scoped infixr:81 " ◁ " => whiskerLeft

/-- Notation for the `whiskerRight` operator of binoidal categories -/
scoped infixl:81 " ▷ " => whiskerRight

/-- Notation for the `leftTensorHom` operator of binoidal categories -/
scoped infixr:81 " ⋉ " => leftTensorHom

/-- Notation for the `rightTensorHom` operator of binoidal categories -/
scoped infixl:81 " ⋊ " => rightTensorHom

def OrdCommute {C} [Category C] [BinoidalCategory C] {X Y Z W: C} (f: X ⟶ Y) (g: Z ⟶ W)
  := f ⋉ g = f ⋊ g

def Commute {C} [Category C] [BinoidalCategory C] {X Y Z W: C} (f: X ⟶ Y) (g: Z ⟶ W)
  := OrdCommute f g ∧ OrdCommute g f 

def Central {C} [Category C] [BinoidalCategory C] {X Y: C} (f: X ⟶ Y)
  := ∀{Z W}, ∀g: Z ⟶ W, Commute f g

def CentralIso {C} [Category C] [BinoidalCategory C] {X Y: C} (f: X ≅ Y)
  := Central f.hom ∧ Central f.inv