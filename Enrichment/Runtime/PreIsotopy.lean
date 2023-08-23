import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Order.Monotone.Basic

import Enrichment.Binoidal.Category
import Enrichment.Premonoidal.Category
import Enrichment.Effectful.Braided
import Enrichment.Ordered.Category
import Enrichment.Runtime.Diagram
import Enrichment.Runtime.Association

open CategoryTheory
open BinoidalCategory
open PremonoidalCategory
open DiagramPort
open Diagram.association

-- theorem Diagram.association.slide_semantics {C: Type u}
--   [TensorMonoid C]
--   [CV: Category (Value C)]
--   [CC: Category C]
--   [PremonoidalCategory (Value C)]
--   [SymmetricPremonoidalCategory (Value C)]
--   [MonoidalCategory' (Value C)]
--   [𝒞: PremonoidalCategory C]
--   [𝒮: SymmetricPremonoidalCategory C]
--   [ℰ: EffectfulCategory C]
--   [ℬ: SymmetricEffectfulCategory C]
--   {X Y: DiagramPort C} 
--   {f g: Diagram X Y}
--   : f.association (Diagram.friction.commute C) g -> f.semantics = g.semantics
  -- | hoop => (𝒞.leftUnitor _).inv_hom_id
  -- | split_assoc => sorry
  -- | split_braiding => sorry
  -- | join_assoc => sorry
  -- | braiding_join => sorry
  -- | comp_id _ => CC.comp_id _
  -- | id_comp _ => CC.id_comp _
  -- | comp_assoc f g h => CC.assoc f.semantics g.semantics h.semantics
  -- | inv_comp I => I.semantics
  -- | whiskerLeft_identity _ _ => sorry
  -- | whiskerRight_identity _ _ => sorry
  -- | sliding _ _ H  => H.left
  -- | associator_left _ => sorry
  -- | associator_mid _ => sorry
  -- | associator_right _ => sorry
  -- | association.leftUnitor _ => sorry
  -- | association.rightUnitor _ => sorry
  -- | braiding_left _ => sorry
  -- | braiding_right _ => sorry
  -- | association.triangle _ _ => sorry
  -- | association.pentagon _ _ _ _ => sorry
  -- | association.hexagon _ _ _ => sorry
  -- | pure_identity _ => sorry
  -- | pure_composes _ _ => sorry
  -- | pure_left _ => sorry
  -- | pure_right _ => sorry
  -- | pure_associator X Y Z => ℰ.inclusion_associator X Y Z
  -- | pure_leftUnitor X => ℰ.inclusion_leftUnitor X
  -- | pure_rightUnitor X => ℰ.inclusion_rightUnitor X
  -- | pure_braiding X Y => ℬ.inclusion_braiding X Y
  -- | effectful_identity _ => sorry
  -- | effectful_inclusion_left _ _ => sorry
  -- | effectful_inclusion_right _ _ => sorry
  -- | association.symm H => sorry

def Diagram.pre_isotopy {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
  := Diagram.association (Diagram.friction.unary Diagram.is_pure)

-- theorem Diagram.pre_isotopy.semantics {C: Type u}
--   [TensorMonoid C]
--   [Category (Value C)]
--   [Category C]
--   [PremonoidalCategory (Value C)]
--   [SymmetricPremonoidalCategory (Value C)]
--   [MonoidalCategory' (Value C)]
--   [PremonoidalCategory C]
--   [SymmetricPremonoidalCategory C]
--   [EffectfulCategory C]
--   [SymmetricEffectfulCategory C]
--   {X Y: DiagramPort C} 
--   {f g: Diagram X Y}
--   (H: f.pre_isotopy g): f.semantics = g.semantics
--   := (H.weaken (Diagram.friction.pure_commutes C)).slide_semantics

def Diagram.associated {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
  := Diagram.congruent_mod Diagram.pre_isotopy