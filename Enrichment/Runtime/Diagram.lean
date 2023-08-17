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
  | hoop: association P (comp split join) (identity state')
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

inductive Diagram.isotopic {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [PremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
| isotopy {D E: Diagram X Y}: D.isotopy E -> D.isotopic E
| isotopy_inv {D E: Diagram X Y}: E.isotopy D -> D.isotopic E
| congr_comp {D D': Diagram X Y} {E E': Diagram Y Z}
  : D.isotopic D' -> E.isotopic E' -> (comp D E).isotopic (comp D' E')
| congr_whiskerLeft {D D': Diagram X Y} (Z)
  : D.isotopic D' -> (whiskerLeft Z D).isotopic (whiskerLeft Z D')
| congr_whiskerRight {D D': Diagram X Y}
  : D.isotopic D' -> (Z: DiagramPort C) -> (whiskerRight D Z).isotopic (whiskerRight D' Z)
| refl (D: Diagram X Y): D.isotopic D
| trans (D E F: Diagram X Y): D.isotopic E -> E.isotopic F -> D.isotopic F

inductive Diagram.homotopic {C: Type u}
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
| isotopy {D E: Diagram X Y}: D.isotopy E -> D.homotopic E
| isotopy_inv {D E: Diagram X Y}: E.isotopy D -> D.homotopic E
| congr_pure {X Y: C} (f g: Value.box X ⟶ Value.box Y)
  : 𝒱.hom_ord.le f g -> (pure f).homotopic (pure g)
| congr_effectful {X Y: C} (f g: X ⟶ Y)
  : 𝒞.hom_ord.le f g -> (effectful f).homotopic (effectful g)
| congr_comp {D D': Diagram X Y} {E E': Diagram Y Z}
  : D.homotopic D' -> E.homotopic E' -> (comp D E).homotopic (comp D' E')
| congr_whiskerLeft {D D': Diagram X Y} (Z)
  : D.homotopic D' -> (whiskerLeft Z D).homotopic (whiskerLeft Z D')
| congr_whiskerRight {D D': Diagram X Y}
  : D.homotopic D' -> (Z: DiagramPort C) -> (whiskerRight D Z).homotopic (whiskerRight D' Z)
| refl (D: Diagram X Y): D.homotopic D
| trans (D E F: Diagram X Y): D.homotopic E -> E.homotopic F -> D.homotopic F
