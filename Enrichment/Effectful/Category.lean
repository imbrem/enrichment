/- Adapted from https://github.com/leanprover-community/mathlib4/blob/9f8f772f02755375a8301679aeb67186742c59fa/Mathlib/CategoryTheory/Monoidal/Category.lean#L73-L147 -/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Functorial
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Order.Monotone.Basic

import Enrichment.Binoidal.Category
import Enrichment.Premonoidal.Category
import Enrichment.Premonoidal.Monoidal'

open CategoryTheory
open BinoidalCategory

def Value (C: Type u): Type u := C

instance valueTensorProduct {C: Type u} [T: TensorProduct C]: TensorProduct (Value C) := T
instance valueTensorMonoid {C: Type u} [T: TensorMonoid C]: TensorMonoid (Value C) := T

def Value.inclusion {C: Type u} (A: Value C): C := A
def Value.box {C: Type u} (A: C): Value C := A
def Value.inclusion_def {C: Type u} (A: Value C): inclusion A = A := rfl

class EffectfulCategory (C: Type u) 
  [TensorMonoid C]
  [Category (Value C)]
  [𝒱: PremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [Category C]
  [𝒞: PremonoidalCategory C] where
  inclusion: Functorial (@Value.inclusion C)
  inclusion_central: ∀{X Y}, ∀f: X ⟶ Y, Central (inclusion.map' f)
  inclusion_associator: ∀X Y Z, inclusion.map' (𝒱.associator X Y Z).hom = (𝒞.associator X Y Z).hom
  inclusion_leftUnitor: ∀Z, inclusion.map' (𝒱.leftUnitor Z).hom = (𝒞.leftUnitor Z).hom
  inclusion_rightUnitor: ∀Z, inclusion.map' (𝒱.rightUnitor Z).hom = (𝒞.rightUnitor Z).hom
  inclusion_whiskerLeft: ∀{X Y Z}, ∀f: X ⟶ Y, 
    inclusion.map' (𝒱.whiskerLeft Z f) = 𝒞.whiskerLeft Z (inclusion.map' f)
  inclusion_whiskerRight: ∀{X Y Z}, ∀f: X ⟶ Y, 
    inclusion.map' (𝒱.whiskerRight f Z) = 𝒞.whiskerRight (inclusion.map' f) Z