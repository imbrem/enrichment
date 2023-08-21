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
  := Diagram.association Diagram.is_pure

-- theorem Diagram.pre_isotopy.semantics {C: Type u}
--   [TensorMonoid C]
--   [CV: Category (Value C)]
--   [CC: Category C]
--   [PremonoidalCategory (Value C)]
--   [SymmetricPremonoidalCategory (Value C)]
--   [MonoidalCategory' (Value C)]
--   [𝒞: PremonoidalCategory C]
--   [𝒮: SymmetricPremonoidalCategory C]
--   [ℰ: EffectfulCategory C]
--   {X Y: DiagramPort C} 
--   {f g: Diagram X Y}
--   : f.pre_isotopy g -> f.semantics = g.semantics
--   | hoop => (𝒞.leftUnitor _).inv_hom_id
--   | comp_id _ => CC.comp_id _
--   | id_comp _ => CC.id_comp _
--   | comp_assoc f g h => CC.assoc f.semantics g.semantics h.semantics
--   | inv_comp I => I.semantics
--   | whiskerLeft_identity _ _ => sorry
--   | whiskerRight_identity _ _ => sorry
--   | sliding _ _ H => sorry
--   | _ => sorry

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