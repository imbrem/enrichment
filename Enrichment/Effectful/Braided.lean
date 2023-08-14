import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Order.Monotone.Basic

import Enrichment.Binoidal.Category
import Enrichment.Premonoidal.Category
import Enrichment.Premonoidal.Monoidal'
import Enrichment.Premonoidal.Braided
import Enrichment.Effectful.Category

open CategoryTheory
open PremonoidalCategory
open BinoidalCategory

class BraidedEffectfulCategory (C: Type u) 
  [TensorMonoid C]
  [Category (Value C)]
  [PremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [Category C]
  [PremonoidalCategory C]
  [ℰ: EffectfulCategory C]
  [𝒱: BraidedPremonoidalCategory (Value C)]
  [𝒞: BraidedPremonoidalCategory C]
where
  inclusion_braiding : ∀X Y, ℰ.inclusion.map' (𝒱.braiding X Y).hom = (𝒞.braiding X Y).hom

class SymmetricEffectfulCategory (C: Type u) 
  [TensorMonoid C]
  [Category (Value C)]
  [PremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [Category C]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  [SymmetricPremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory C]
extends BraidedEffectfulCategory C