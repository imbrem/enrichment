import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Order.Monotone.Basic

import Enrichment.Premonoidal.Category

open CategoryTheory
open PremonoidalCategory
open BinoidalCategory


class MonoidalCategory' (C: Type u) [Category C] [TensorMonoid C] [PremonoidalCategory C] :=
  /-- Sliding -/
  sliding: ∀{X₁ Y₁ X₂ Y₂: C}, ∀f: X₁ ⟶ Y₁, ∀g: X₂ ⟶ Y₂, f ⋉ g = f ⋊ g
  /-- Centrality -/
  centrality: ∀{X Y: C}, ∀f: X ⟶ Y, Central f := λ{_ _} f => {
    commute := λg => ⟨sliding f g, sliding g f⟩
  }

namespace MonoidalCategory'

instance fromMonoidalCategory (C: Type u) [Category C] [MonoidalCategory C]: MonoidalCategory' C := {
  sliding := OrdCommute.monoidal
}