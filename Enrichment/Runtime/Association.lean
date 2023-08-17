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

open CategoryTheory
open BinoidalCategory
open PremonoidalCategory
open DiagramPort

inductive Diagram.inverses {C: Type u}
  [TensorMonoid C]
  [Quiver.{v} (Value C)]
  [Quiver.{v} C]
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram Y X -> Prop
| associator (X Y Z): inverses (associator X Y Z) (associator_inv X Y Z)
| leftUnitor (X): inverses (leftUnitor X) (leftUnitor_inv X)
| rightUnitor (X): inverses (rightUnitor X) (rightUnitor_inv X)
| braiding (X Y): inverses (braiding X Y) (braiding Y X)

theorem Diagram.inverses.semantics {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [𝒮: SymmetricPremonoidalCategory C]
  [EffectfulCategory C]
  {X Y: DiagramPort C}
  (f: Diagram X Y) (g: Diagram Y X)
  (I: f.inverses g) 
  : f.semantics ≫ g.semantics = 𝟙 X.value ∧ g.semantics ≫ f.semantics = 𝟙 Y.value
  := by cases I <;> constructor <;> simp [Diagram.semantics, 𝒮.symmetry] <;> rfl

inductive Diagram.association {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [𝒱: PremonoidalCategory (Value C)]
  [𝒮: SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [ℰ: EffectfulCategory C]
  (P: {X Y: DiagramPort C} -> Diagram X Y -> Prop)
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
  | hoop: association P (comp split join) (identity state')
  | identity_left {X Y} (f: Diagram X Y): association P (comp f (identity Y)) f
  | identity_right {X Y} (f: Diagram X Y): association P (comp (identity X) f) f
  | comp_assoc {X Y Z W} {f: Diagram X Y} {g: Diagram Y Z} {h: Diagram Z W}
    : association P (comp f (comp g h)) (comp (comp f g) h)
  | inv_comp {X Y} {f: Diagram X Y} {g: Diagram Y X}
    : inverses f g -> association P (comp f g) (identity X)
  | whiskerLeft_identity (X Y)
    : association P (whiskerLeft X (identity Y)) (identity (X ⊗ Y))
  | whiskerRight_identity (X Y)
    : association P (whiskerRight (identity X) Y) (identity (X ⊗ Y))
  | sliding {X₁ Y₁ X₂ Y₂} (f: Diagram X₁ Y₁) (g: Diagram X₂ Y₂)
    : P f ∨ P g -> association P 
      (comp (whiskerRight f X₂) (whiskerLeft Y₁ g)) 
      (comp (whiskerLeft X₁ g) (whiskerRight f Y₂))
  | associator_left {X Y Z X'} (f: Diagram X X')
    : association P
      (comp (whiskerRight (whiskerRight f Y) Z) (associator X' Y Z))
      (comp (associator X Y Z) (whiskerRight f (Y ⊗ Z)))
  | associator_mid {X Y Z Y'} (f: Diagram Y Y')
    : association P
      (comp (whiskerRight (whiskerLeft X f) Z) (associator X Y' Z))
      (comp (associator X Y Z) (whiskerLeft X (whiskerRight f Z)))
  | associator_right {X Y Z Z'} (f: Diagram Z Z')
    : association P
      (comp (whiskerLeft (X ⊗ Y) f) (associator X Y Z'))
      (comp (associator X Y Z) (whiskerLeft X (whiskerLeft Y f)))
  | leftUnitor {X Y} (f: Diagram X Y)
    : association P
      (comp (leftUnitor X) f)
      (comp (whiskerLeft tensorUnit' f) (leftUnitor Y))
  | rightUnitor {X Y} (f: Diagram X Y)
    : association P
      (comp (rightUnitor X) f)
      (comp (whiskerRight f tensorUnit') (rightUnitor Y))
  | braiding_left {X Y Z} (f: Diagram X Y)
    : association P
      (comp (whiskerLeft Z f) (braiding Z Y))
      (comp (braiding Z X) (whiskerRight f Z))
  | braiding_right {X Y Z} (f: Diagram X Y)
    : association P
      (comp (whiskerRight f Z) (braiding Y Z))
      (comp (braiding X Z) (whiskerLeft Z f))
  | triangle (X Y)
    : association P
      (comp (associator X tensorUnit' Y) (whiskerLeft X (leftUnitor Y)))
      (whiskerRight (rightUnitor X) Y)
  | pentagon (X Y Z W)
    : association P
      (comp (associator (X ⊗ Y) Z W) (associator X Y (Z ⊗ W)))
      (comp (whiskerRight (associator X Y Z) W) 
        (comp (associator X (Y ⊗ Z) W) (whiskerLeft X (associator Y Z W))))
  | hexagon (X Y Z)
    : association P
      (comp (associator X Y Z) (comp (braiding X (Y ⊗ Z)) (associator Y Z X)))
      (comp (whiskerRight (braiding X Y) Z) (comp (associator Y X Z) (whiskerLeft Y (braiding X Z))))
  | pure_identity (X): association P (pure (𝟙 X)) (identity _)
  | pure_composes {X Y Z: C} (f: Value.box X ⟶ Value.box Y) (g: Value.box Y ⟶ Value.box Z)
    : association P (comp (pure f) (pure g)) (pure (f ≫ g))
  | pure_left {X Y Z: C} (f: Value.box X ⟶ Value.box Y)
    : association P (whiskerLeft ⟨Z, 0⟩ (pure f)) (pure (𝒱.whiskerLeft Z f))
  | pure_right {X Y Z: C} (f: Value.box X ⟶ Value.box Y)
    : association P (whiskerRight (pure f) ⟨Z, 0⟩) (pure (𝒱.whiskerRight f Z))
  | pure_associator (X Y Z: C)
    : association P (@pure C _ _ _ _ _ (𝒱.associator X Y Z).hom) (associator ⟨X, 0⟩ ⟨Y, 0⟩ ⟨Z, 0⟩)
  | pure_leftUnitor (X: C)
    : association P (@pure C _ _ _ _ _ (𝒱.leftUnitor X).hom) (leftUnitor ⟨X, 0⟩)
  | pure_rightUnitor (X: C)
    : association P (@pure C _ _ _ _ _ (𝒱.rightUnitor X).hom) (rightUnitor ⟨X, 0⟩)
  | pure_braiding (X Y: C)
    : association P (@pure C _ _ _ _ _ (𝒮.braiding X Y).hom) (braiding ⟨X, 0⟩ ⟨Y, 0⟩)
  | effectful_identity (X: C)
    : association P (effectful (𝟙 X)) (identity ⟨tensorUnit' ⊗ X, 1⟩)
  --TODO: effectful whiskering?
  | effectful_inclusion_left {X Y Z: C} (f: X ⟶ Y) (g: Value.box Y ⟶ Value.box Z)
    : association P 
      (effectful (f ≫ ℰ.inclusion.map' g))
      (comp (effectful f) (whiskerLeft state' (pure g)))
  | effectful_inclusion_right {X Y Z: C} (f: Value.box X ⟶ Value.box Y) (g: Y ⟶ Z)
    : association P 
      (effectful (ℰ.inclusion.map' f ≫ g))
      (comp (whiskerLeft state' (pure f)) (effectful g))
  | symm {X Y} {f g: Diagram X Y}: association P f g -> association P g f

def Diagram.association.weaken {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [𝒱: PremonoidalCategory (Value C)]
  [𝒮: SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [ℰ: EffectfulCategory C]
  {X Y: DiagramPort C}
  {f g: Diagram X Y}
  {P: {X Y: DiagramPort C} -> Diagram X Y -> Prop}
  (A: f.association P g)
  (Q: {X Y: DiagramPort C} -> Diagram X Y -> Prop)
  (WP: ∀{X Y: DiagramPort C}, ∀{f: Diagram X Y}, P f -> Q f)
  :  f.association Q g
  := by induction A with
  | symm => apply symm; assumption
  | sliding _ _ H => 
    apply sliding; 
    exact match H with
    | Or.inl H => Or.inl (WP H)
    | Or.inr H => Or.inr (WP H)
  | _ => constructor <;> assumption

inductive Diagram.congruent_mod {C: Type u}
  [TensorMonoid C]
  [Quiver (Value C)]
  [Quiver C]
  (R: {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop)
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
| refl (D: Diagram X Y): D.congruent_mod R D
| congr_comp {D D': Diagram X Y} {E E': Diagram Y Z}
  : D.congruent_mod R D' -> E.congruent_mod R E' -> (comp D E).congruent_mod R (comp D' E')
| congr_whiskerLeft {D D': Diagram X Y} (Z)
  : D.congruent_mod R D' -> (whiskerLeft Z D).congruent_mod R (whiskerLeft Z D')
| congr_whiskerRight {D D': Diagram X Y}
  : D.congruent_mod R D' -> (Z: DiagramPort C) -> (whiskerRight D Z).congruent_mod R (whiskerRight D' Z)
| rel {D E: Diagram X Y}: R D E -> D.congruent_mod R E
| trans {D E F: Diagram X Y}: D.congruent_mod R E -> E.congruent_mod R F -> D.congruent_mod R F

def Diagram.congruent_mod.weaken {C: Type u}
  [TensorMonoid C]
  [Quiver (Value C)]
  [Quiver C]
  {X Y: DiagramPort C}
  {f g: Diagram X Y}
  {R: {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop}
  (A: f.congruent_mod R g)
  (S: {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop)
  (WR: ∀{X Y: DiagramPort C}, ∀{f g: Diagram X Y}, R f g -> S f g)
  :  f.congruent_mod S g
  := by induction A with
  | rel H => exact rel (WR H)
  | trans _ _ Il Ir => exact trans Il Ir
  | _ => constructor <;> assumption

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

def Diagram.isotopy {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
  := Diagram.association (λ_ => True)

def Diagram.isotopic {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
  := Diagram.congruent_mod Diagram.isotopy

inductive Diagram.homotopy {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  [𝒱: OrderedCategory (Value C)]
  [𝒞: OrderedCategory C]
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
| isotopy {D E: Diagram X Y}: D.isotopy E -> D.homotopy E
| congr_pure {X Y: C} (f g: Value.box X ⟶ Value.box Y)
  : 𝒱.hom_ord.le f g -> (pure f).homotopy (pure g)
| congr_effectful {X Y: C} (f g: X ⟶ Y)
  : 𝒞.hom_ord.le f g -> (effectful f).homotopy (effectful g)

def Diagram.homotopic {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  [OrderedCategory (Value C)]
  [OrderedCategory C]
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
  := Diagram.congruent_mod Diagram.homotopy