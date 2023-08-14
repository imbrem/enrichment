import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Order.Monotone.Basic

import Enrichment.Premonoidal.Category

open CategoryTheory
open PremonoidalCategory
open BinoidalCategory

class BraidedPremonoidalCategory (C: Type u) [Category C] [TensorMonoid C] [PremonoidalCategory C] 
where  
  braiding : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X
  braiding_left_naturality : ∀ {X Y Z: C} (f: X ⟶ Y),
    (braiding X Z).hom ≫ whiskerLeft Z f = whiskerRight f Z ≫ (braiding Y Z).hom
  braiding_right_naturality : ∀ {X Y Z: C} (f: X ⟶ Y),
    (braiding Z X).hom ≫ whiskerRight f Z = whiskerLeft Z f ≫ (braiding Z Y).hom
  hexagon_forward : ∀ X Y Z: C, 
    (associator X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (associator Y Z X).hom =
    whiskerRight (braiding X Y).hom Z ≫ (associator Y X Z).hom ≫ whiskerLeft Y (braiding X Z).hom
  hexagon_reverse : ∀ X Y Z: C,
    (associator X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (associator Z X Y).inv =
    whiskerLeft X (braiding Y Z).hom ≫ (associator X Z Y).inv ≫ whiskerRight (braiding X Z).hom Y  

class SymmetricPremonoidalCategory (C: Type u) [Category C] [TensorMonoid C] [PremonoidalCategory C] 
extends BraidedPremonoidalCategory C where
  symmetry : ∀ X Y : C, (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (X ⊗ Y)