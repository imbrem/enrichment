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

theorem Diagram.association.slide_semantics {C: Type u}
  [TensorMonoid C]
  [CV: Category (Value C)]
  [CC: Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [𝒞: PremonoidalCategory C]
  [𝒮: SymmetricPremonoidalCategory C]
  [ℰ: EffectfulCategory C]
  [ℬ: SymmetricEffectfulCategory C]
  {X Y: DiagramPort C} 
  {f g: Diagram X Y}
  (H: f.association (Diagram.friction.commute C) g)
  : f.semantics = g.semantics := by induction H with
  | hoop => exact (𝒞.leftUnitor _).inv_hom_id
  | split_assoc => sorry -- by coherence
  | split_braiding => sorry -- by braiding(I, I) = id
  | join_assoc => sorry -- by coherence
  | braiding_join => sorry -- by braiding(I, I) = id
  | comp_id => exact CC.comp_id _
  | id_comp => exact CC.id_comp _
  | comp_assoc f g h => exact CC.assoc f.semantics g.semantics h.semantics
  | inv_comp I => exact I.semantics
  | whiskerLeft_identity => exact 𝒞.whiskerLeft_id _ _
  | whiskerRight_identity => exact 𝒞.id_whiskerRight _ _
  | sliding _ _ H  => exact H.left
  | associator_left => exact 𝒞.associator_left_naturality _
  | associator_mid => exact 𝒞.associator_mid_naturality _
  | associator_right => exact 𝒞.associator_right_naturality _
  | leftUnitor => exact 𝒞.leftUnitor_naturality _
  | rightUnitor => exact 𝒞.rightUnitor_naturality _
  | braiding_left => exact 𝒮.braiding_left_naturality _ _
  | braiding_right => exact 𝒮.braiding_right_naturality _ _
  | triangle => exact 𝒞.triangle _ _
  | pentagon => exact 𝒞.pentagon _ _ _ _
  | hexagon => exact 𝒮.hexagon_forward _ _ _
  | pure_identity => exact ℰ.inclusion.map_id
  | pure_composes => exact ℰ.inclusion.map_comp' _ _
  | pure_left => exact ℰ.inclusion_whiskerLeft _
  | pure_right => exact ℰ.inclusion_whiskerRight _
  | pure_associator X Y Z => exact ℰ.inclusion_associator X Y Z
  | pure_leftUnitor X => exact ℰ.inclusion_leftUnitor X
  | pure_rightUnitor X => exact ℰ.inclusion_rightUnitor X
  | pure_braiding X Y => exact ℬ.inclusion_braiding X Y
  | effectful_identity _ => simp [semantics]
  | effectful_inclusion_left _ _ => 
    simp only [semantics, Category.assoc, Iso.cancel_iso_hom_left]
    rw [<-Iso.cancel_iso_hom_right _ _ (PremonoidalCategory.leftUnitor _)]
    simp [𝒞.leftUnitor_naturality]
  | effectful_inclusion_right _ _ => 
    simp only [semantics, Category.assoc]
    rw [<-Iso.cancel_iso_hom_right _ _ (PremonoidalCategory.leftUnitor _)]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [<-CC.assoc]
    rw [<-𝒞.leftUnitor_naturality]
    simp [Value.inclusion, Value.box]
  | symm _ I => exact I.symm

-- def Diagram.congruent_mod.eq_semantics {C: Type u}
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
--   (H: f.congruent_mod (Diagram.relation.diagonal C) g)
--   : f.semantics = g.semantics
--   := sorry

-- def Diagram.congruent_mod.slide_semantics {C: Type u}
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
--   (H: f.congruent_mod (Diagram.friction.commute C).association g)
--   : f.semantics = g.semantics
--   := sorry

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

theorem Diagram.pre_isotopy.semantics {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  [EffectfulCategory C]
  [SymmetricEffectfulCategory C]
  {X Y: DiagramPort C} 
  {f g: Diagram X Y}
  (H: f.pre_isotopy g): f.semantics = g.semantics
  := (H.weaken (Diagram.friction.pure_commutes C)).slide_semantics

def Diagram.pre_isotopic {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
  := Diagram.congruent_mod ⟨Diagram.pre_isotopy⟩ 

def Diagram.relation.pre_isotopy (C: Type u)
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  : Diagram.relation C
  := ⟨Diagram.pre_isotopy⟩ 

def Diagram.relation.pre_isotopic (C: Type u)
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  : Diagram.relation C
  := (Diagram.relation.pre_isotopy C).congruent_mod