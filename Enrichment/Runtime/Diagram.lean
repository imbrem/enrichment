import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Order.Monotone.Basic

import Enrichment.Binoidal.Category
import Enrichment.Premonoidal.Category
import Enrichment.Effectful.Braided
import Enrichment.Ordered.Category

open CategoryTheory
open BinoidalCategory
open PremonoidalCategory

structure DiagramPort (C: Type u) where
  value: C
  states: ℕ

abbrev DiagramPort.state' {C: Type u} [TensorMonoid C]: DiagramPort C := ⟨tensorUnit', 1⟩
abbrev DiagramPort.state (C: Type u) [TensorMonoid C]: DiagramPort C := ⟨tensorUnit', 1⟩

open DiagramPort

instance {C: Type u} [TensorProduct C]: TensorProduct (DiagramPort C) where
  tensorObj := λ⟨X, n⟩ ⟨Y, m⟩ => ⟨X ⊗ Y, n + m⟩     

theorem DiagramPort.zero_tensor_left {C} [TensorProduct C] {X Y: DiagramPort C}
  (H: (X ⊗ Y).states = 0)
  : X.states = 0
  := Nat.le_zero.mp (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_zero.mpr H))

theorem DiagramPort.zero_tensor_right {C} [TensorProduct C] {X Y: DiagramPort C} 
  (H: (X ⊗ Y).states = 0)
  : Y.states = 0
  := Nat.le_zero.mp (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_zero.mpr H))

instance {C: Type u} [TensorMonoid C]: TensorMonoid (DiagramPort C) where
  tensorUnit' := ⟨tensorUnit', 0⟩ 

inductive Diagram {C: Type u}
  [TensorMonoid C]
  [Quiver.{v} (Value C)]
  [Quiver.{v} C]
  : DiagramPort C -> DiagramPort C -> Type (max u v)
| identity (X): Diagram X X
| comp {X Y Z}: Diagram X Y -> Diagram Y Z -> Diagram X Z
| whiskerLeft {Y Z} (X): Diagram Y Z -> Diagram (X ⊗ Y) (X ⊗ Z) 
| whiskerRight {Y Z}: Diagram Y Z -> (X: DiagramPort C) -> Diagram (Y ⊗ X) (Z ⊗ X) 
| associator (X Y Z): Diagram ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)) 
| associator_inv (X Y Z): Diagram (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z)
| leftUnitor (X): Diagram (tensorUnit' ⊗ X) X
| leftUnitor_inv (X): Diagram X (tensorUnit' ⊗ X)
| rightUnitor (X): Diagram (X ⊗ tensorUnit') X
| rightUnitor_inv (X): Diagram X (X ⊗ tensorUnit')
| braiding (X Y): Diagram (X ⊗ Y) (Y ⊗ X)
| split: Diagram state' (state' ⊗ state')
| join: Diagram (state'⊗ state') state'
| pure {X Y: C}: (Value.box X ⟶ Value.box Y) -> Diagram ⟨X, 0⟩ ⟨Y, 0⟩
| effectful {X Y: C}: (X ⟶ Y) -> Diagram ⟨tensorUnit' ⊗ X, 1⟩ ⟨tensorUnit' ⊗ Y, 1⟩

def Diagram.is_pure {C: Type u}
  [TensorMonoid C]
  [Quiver.{v} (Value C)]
  [Quiver.{v} C]
  {X Y: DiagramPort C}: Diagram X Y -> Prop
  | identity X => True
  | comp f g => f.is_pure ∧ g.is_pure 
  | whiskerLeft X f => f.is_pure
  | whiskerRight f X => f.is_pure
  | effectful _ => False
  | _ => True

theorem Diagram.state_conservation
  {C: Type u}
  [TensorMonoid C]
  [Quiver.{v} (Value C)]
  [Quiver.{v} C]
  {X Y: DiagramPort C}
  : Diagram X Y -> (X.states = 0 ↔ Y.states = 0)
  | identity _ => by rfl
  | comp f g => by rw [f.state_conservation, g.state_conservation]
  | whiskerLeft ⟨_, n⟩ f => by
    cases X; cases Y; cases n <;> simp_arith [tensorObj, f.state_conservation]
  | whiskerRight f ⟨_, n⟩ => by
    cases X; cases Y; cases n <;> simp_arith [tensorObj, f.state_conservation]
  | associator ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ => by simp [tensorObj, Nat.add_assoc]
  | associator_inv ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ => by simp [tensorObj, Nat.add_assoc]
  | leftUnitor ⟨_, _⟩ 
  | leftUnitor_inv ⟨_, _⟩
  | rightUnitor ⟨_, _⟩
  | rightUnitor_inv ⟨_, _⟩ => by simp [tensorObj]
  | braiding ⟨_, _⟩ ⟨_, _⟩ => by simp [tensorObj, Nat.add_comm]
  | split | join | pure _ | effectful _ => by simp

theorem Diagram.no_forgetting
  {C: Type u}
  [TensorMonoid C]
  [Quiver.{v} (Value C)]
  [Quiver.{v} C]
  {X Y: DiagramPort C}
  (D: Diagram X Y): X.states = 0 -> Y.states = 0
  := by simp [D.state_conservation]

theorem Diagram.zero_left_pure {C: Type u}
  [TensorMonoid C]
  [Quiver.{v} (Value C)]
  [Quiver.{v} C]
  {X Y: DiagramPort C} (D: Diagram X Y)
  (HX: X.states = 0)
  : D.is_pure
  := by induction D with
  | comp f g If Ig => exact ⟨(If HX), (Ig (f.no_forgetting HX))⟩
  | whiskerLeft X _ If => exact If (DiagramPort.zero_tensor_right HX)
  | whiskerRight _ X If => exact If (DiagramPort.zero_tensor_left HX)
  | effectful _ => cases HX
  | _ => constructor

def Diagram.semantics {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [𝒞: PremonoidalCategory C]
  [𝒮: SymmetricPremonoidalCategory C]
  [ℰ: EffectfulCategory C]
  {X Y: DiagramPort C}
  : Diagram X Y -> (X.value ⟶ Y.value)
| identity X => 𝟙 X.value
| comp f g => f.semantics ≫ g.semantics
| whiskerLeft Z f => 𝒞.whiskerLeft Z.value f.semantics
| whiskerRight f Z => 𝒞.whiskerRight f.semantics Z.value
| associator X Y Z => (𝒞.associator X.value Y.value Z.value).hom
| associator_inv X Y Z => (𝒞.associator X.value Y.value Z.value).inv
| leftUnitor X => (𝒞.leftUnitor X.value).hom
| leftUnitor_inv X => (𝒞.leftUnitor X.value).inv
| rightUnitor X => (𝒞.rightUnitor X.value).hom
| rightUnitor_inv X => (𝒞.rightUnitor X.value).inv
| braiding X Y => (𝒮.braiding X.value Y.value).hom
| split => (𝒞.leftUnitor _).inv
| join => (𝒞.leftUnitor _).hom
| pure f => ℰ.inclusion.map' f
| effectful f => (𝒞.leftUnitor _).hom ≫ f ≫ (𝒞.leftUnitor _).inv

def Diagram.pure_semantics {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [𝒱: PremonoidalCategory (Value C)]
  [𝒮: SymmetricPremonoidalCategory (Value C)]
  {X Y: DiagramPort C}
  : (D: Diagram X Y) -> D.is_pure -> (Value.box X.value ⟶ Value.box Y.value)
| identity X, _ => 𝟙 (Value.box X.value)
| comp f g, Hx => f.pure_semantics Hx.1 ≫ g.pure_semantics Hx.2
| whiskerLeft X f, Hx => 𝒱.whiskerLeft X.value (f.pure_semantics Hx)
| whiskerRight f X, Hx => 𝒱.whiskerRight (f.pure_semantics Hx) X.value
| associator X Y Z, _ => (𝒱.associator X.value Y.value Z.value).hom
| associator_inv X Y Z, _ => (𝒱.associator X.value Y.value Z.value).inv
| leftUnitor X, _ => (𝒱.leftUnitor X.value).hom
| leftUnitor_inv X, _ => (𝒱.leftUnitor X.value).inv
| rightUnitor X, _ => (𝒱.rightUnitor X.value).hom
| rightUnitor_inv X, _ => (𝒱.rightUnitor X.value).inv
| braiding X Y, _ => (𝒮.braiding X.value Y.value).hom
| split, Hx => (𝒱.leftUnitor tensorUnit').inv
| join, Hx => (𝒱.leftUnitor tensorUnit').hom
| pure f, _ => f
| effectful _, Hx => Hx.elim

abbrev Diagram.is_pure.semantics {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  {X Y: DiagramPort C}
  {D: Diagram X Y} 
  (H: D.is_pure): Value.box X.value ⟶ Value.box Y.value
  := D.pure_semantics H

theorem Diagram.semantic_inclusion {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  [ℰ: EffectfulCategory C]
  [𝒮: SymmetricEffectfulCategory C]
  {X Y: DiagramPort C}
  : (D: Diagram X Y) -> (H: D.is_pure) -> ℰ.inclusion.map' (D.pure_semantics H) = D.semantics
  | identity _, _ => ℰ.inclusion.map_id
  | comp f g, Hx => by
    rw [
      pure_semantics,
      ℰ.inclusion.map_comp',
      f.semantic_inclusion Hx.1,
      g.semantic_inclusion Hx.2
    ]
    rfl
  | whiskerLeft Z f, Hx => by
    rw [
      pure_semantics,
      ℰ.inclusion_whiskerLeft,
      f.semantic_inclusion Hx
    ]
    rfl
  | whiskerRight f Z, Hx => by
    rw [
      pure_semantics,
      ℰ.inclusion_whiskerRight,
      f.semantic_inclusion Hx
    ]
    rfl
  | associator X Y Z, _ => ℰ.inclusion_associator X.value Y.value Z.value
  | associator_inv X Y Z, _ => ℰ.inclusion_associator_inv X.value Y.value Z.value
  | leftUnitor X, _ => ℰ.inclusion_leftUnitor X.value
  | leftUnitor_inv X, _ => ℰ.inclusion_leftUnitor_inv X.value
  | rightUnitor X, _ => ℰ.inclusion_rightUnitor X.value
  | rightUnitor_inv X, _ => ℰ.inclusion_rightUnitor_inv X.value
  | braiding X Y, _ => 𝒮.inclusion_braiding X.value Y.value
  | pure _, _ => rfl
  | split, Hx => ℰ.inclusion_leftUnitor_inv _
  | join, Hx => ℰ.inclusion_leftUnitor _
  | effectful _, Hx => by cases Hx

theorem Diagram.is_pure.semantic_inclusion {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  [ℰ: EffectfulCategory C]
  [SymmetricEffectfulCategory C]
  {X Y: DiagramPort C}
  {D: Diagram X Y} (H: D.is_pure): ℰ.inclusion.map' (D.pure_semantics H) = D.semantics
  := D.semantic_inclusion H

theorem Diagram.pure_central {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  [ℰ: EffectfulCategory C]
  [SymmetricEffectfulCategory C]
  {X Y: DiagramPort C}
  (D: Diagram X Y) (H: D.is_pure): Central D.semantics
  := H.semantic_inclusion ▸ ℰ.inclusion_central _

theorem Diagram.is_pure.central {C: Type u}
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
  {D: Diagram X Y} (H: D.is_pure): Central D.semantics
  := D.pure_central H