import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Order.Monotone.Basic

import Enrichment.Binoidal.Category
import Enrichment.Premonoidal.Category
import Enrichment.Effectful.Braided

open BinoidalCategory

inductive DiagramPort (C: Type u)
| state
| unit
| tensor (A B: DiagramPort C)
| pure (X: C)

instance {C: Type u}: TensorProduct (DiagramPort C) where
  tensorObj := DiagramPort.tensor

instance {C: Type u}: TensorMonoid (DiagramPort C) where
  tensorUnit' := DiagramPort.unit

inductive DiagramPort.is_pure {C: Type u}: DiagramPort C -> Prop
| unit: is_pure DiagramPort.unit
| pure (X): is_pure (pure X)
| tensor {A B}: is_pure A -> is_pure B -> is_pure (A ⊗ B)

inductive DiagramPort.is_left_threaded {C: Type u}: DiagramPort C -> Prop
| tensor {A}: is_pure A -> is_left_threaded (state ⊗ A)

inductive DiagramPort.is_right_threaded {C: Type u}: DiagramPort C -> Prop
| tensor {A}: is_pure A -> is_right_threaded (state ⊗ A)

inductive Diagram {C: Type u}
  [Quiver.{v} (Value C)]
  [Quiver.{v} C]
  : DiagramPort C -> DiagramPort C -> Type (max u v)
| identity (X): Diagram X X
| comp {X Y Z}: Diagram X Y -> Diagram Y Z -> Diagram X Z
| whiskerLeft {X Y}: (Z: DiagramPort C) -> Diagram X Y -> Diagram (Z ⊗ X) (Z ⊗ Y) 
| whiskerRight {X Y}: Diagram X Y -> (Z: DiagramPort C) -> Diagram (X ⊗ Z) (Y ⊗ Z)
| associator (X Y Z): Diagram ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)) 
| associator_inv (X Y Z): Diagram (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z)
| leftUnitor (X): Diagram (unit ⊗ X) X
| leftUnitor_inv (X): Diagram X (unit ⊗ X)
| rightUnitor (X): Diagram (X ⊗ unit) X
| rightUnitor_inv (X): Diagram X (X ⊗ unit)
| braiding (X Y): Diagram (X ⊗ Y) (Y ⊗ X)
| split: Diagram state (state ⊗ state)
| join: Diagram (state ⊗ state) state
| pure {X Y: Value C}: (X ⟶ Y) -> Diagram (DiagramPort.pure X.inclusion) (DiagramPort.pure Y.inclusion) 
| effectful {X Y: C}: (X ⟶ Y) -> Diagram ((DiagramPort.pure X) ⊗ state)  ((DiagramPort.pure Y) ⊗ state)