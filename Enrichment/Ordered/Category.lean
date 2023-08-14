import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Order.Monotone.Basic
import Enrichment.Binoidal.Category

open CategoryTheory
open Quiver

class OrderedQuiver (C: Type u) [Quiver C] :=
  hom_ord {X Y: C}: PartialOrder (Hom X Y)

open OrderedQuiver

class OrderedCategory (C: Type u) [Category C] extends OrderedQuiver C :=
  congr_left_comp {X Y Z: C} (g: Hom Y Z)
    : @Monotone (Hom X Y) _ hom_ord.toPreorder hom_ord.toPreorder (λf => f ≫ g)
  congr_right_comp {X Y Z: C} (f: Hom X Y)
    : @Monotone (Hom Y Z) _ hom_ord.toPreorder hom_ord.toPreorder (λg => f ≫ g)

set_option checkBinderAnnotations false

class OrderedBinoidalCategory (C: Type u) [Category C] [TensorProduct C] [BinoidalCategory C] extends OrderedCategory C :=
  congr_whiskerLeft {Z X Y: C}
    : @Monotone (Hom X Y) _ hom_ord.toPreorder hom_ord.toPreorder (BinoidalCategory.whiskerLeft Z)
  congr_whiskerRight {Z X Y: C}
    : @Monotone (Hom X Y) _ hom_ord.toPreorder hom_ord.toPreorder (λf => BinoidalCategory.whiskerRight f Z)

class MonoFunctor {C D} [Category C] [OrderedCategory C] [Category D] [OrderedCategory D] (F: Functor C D) :=
  monotone {X Y: C}
    : @Monotone (Hom X Y) _ hom_ord.toPreorder hom_ord.toPreorder F.map