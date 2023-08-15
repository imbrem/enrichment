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

inductive Diagram.inverses {C: Type u}
  [TensorMonoid C]
  [Quiver.{v} (Value C)]
  [Quiver.{v} C]
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram Y X -> Prop
| associator (X Y Z): inverses (associator X Y Z) (associator_inv X Y Z)
| leftUnitor (X): inverses (leftUnitor X) (leftUnitor_inv X)
| rightUnitor (X): inverses (rightUnitor X) (rightUnitor_inv X)
| braiding (X Y): inverses (braiding X Y) (braiding Y X)
| symm {X Y} {f: Diagram X Y} {g: Diagram Y X}: inverses f g -> inverses g f

inductive Diagram.isotopy {C: Type u}
  [TensorMonoid C]
  [Category (Value C)]
  [Category C]
  [𝒱: PremonoidalCategory (Value C)]
  [𝒮: SymmetricPremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [PremonoidalCategory C]
  [ℰ: EffectfulCategory C]
  : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
| identity_left {X Y} (f: Diagram X Y): isotopy (comp f (identity Y)) f
| identity_right {X Y} (f: Diagram X Y): isotopy (comp (identity X) f) f
| comp_assoc {X Y Z W} {f: Diagram X Y} {g: Diagram Y Z} {h: Diagram Z W}
  : isotopy (comp f (comp g h)) (comp (comp f g) h)
| inv_comp {X Y} {f: Diagram X Y} {g: Diagram Y X}
  : inverses f g -> isotopy (comp f g) (identity X)
| whiskerLeft_identity (X Y)
  : isotopy (whiskerLeft X (identity Y)) (identity (X ⊗ Y))
| whiskerRight_identity (X Y)
  : isotopy (whiskerRight (identity X) Y) (identity (X ⊗ Y))
| sliding {X₁ Y₁ X₂ Y₂} (f: Diagram X₁ Y₁) (g: Diagram X₂ Y₂)
  : isotopy 
    (comp (whiskerRight f X₂) (whiskerLeft Y₁ g)) 
    (comp (whiskerLeft X₁ g) (whiskerRight f Y₂))
| associator_left {X Y Z X'} (f: Diagram X X')
  : isotopy
    (comp (whiskerRight (whiskerRight f Y) Z) (associator X' Y Z))
    (comp (associator X Y Z) (whiskerRight f (Y ⊗ Z)))
| associator_mid {X Y Z Y'} (f: Diagram Y Y')
  : isotopy
    (comp (whiskerRight (whiskerLeft X f) Z) (associator X Y' Z))
    (comp (associator X Y Z) (whiskerLeft X (whiskerRight f Z)))
| associator_right {X Y Z Z'} (f: Diagram Z Z')
  : isotopy
    (comp (whiskerLeft (X ⊗ Y) f) (associator X Y Z'))
    (comp (associator X Y Z) (whiskerLeft X (whiskerLeft Y f)))
| leftUnitor {X Y} (f: Diagram X Y)
  : isotopy
    (comp (leftUnitor X) f)
    (comp (whiskerLeft tensorUnit' f) (leftUnitor Y))
| rightUnitor {X Y} (f: Diagram X Y)
  : isotopy
    (comp (rightUnitor X) f)
    (comp (whiskerRight f tensorUnit') (rightUnitor Y))
| braiding_left {X Y Z} (f: Diagram X Y)
  : isotopy
    (comp (whiskerLeft Z f) (braiding Z Y))
    (comp (braiding Z X) (whiskerRight f Z))
| braiding_right {X Y Z} (f: Diagram X Y)
  : isotopy
    (comp (whiskerRight f Z) (braiding Y Z))
    (comp (braiding X Z) (whiskerLeft Z f))
| triangle (X Y)
  : isotopy
    (comp (associator X tensorUnit' Y) (whiskerLeft X (leftUnitor Y)))
    (whiskerRight (rightUnitor X) Y)
| pentagon (X Y Z W)
  : isotopy
    (comp (associator (X ⊗ Y) Z W) (associator X Y (Z ⊗ W)))
    (comp (whiskerRight (associator X Y Z) W) 
      (comp (associator X (Y ⊗ Z) W) (whiskerLeft X (associator Y Z W))))
| hexagon (X Y Z)
  : isotopy
    (comp (associator X Y Z) (comp (braiding X (Y ⊗ Z)) (associator Y Z X)))
    (comp (whiskerRight (braiding X Y) Z) (comp (associator Y X Z) (whiskerLeft Y (braiding X Z))))
| hoop: isotopy (comp split join) (identity state')
| pure_identity (X): isotopy (pure (𝟙 X)) (identity _)
| pure_composes {X Y Z: C} (f: Value.box X ⟶ Value.box Y) (g: Value.box Y ⟶ Value.box Z)
  : isotopy (comp (pure f) (pure g)) (pure (f ≫ g))
| pure_left {X Y Z: C} (f: Value.box X ⟶ Value.box Y)
  : isotopy (whiskerLeft ⟨Z, 0⟩ (pure f)) (pure (𝒱.whiskerLeft Z f))
| pure_right {X Y Z: C} (f: Value.box X ⟶ Value.box Y)
  : isotopy (whiskerRight (pure f) ⟨Z, 0⟩) (pure (𝒱.whiskerRight f Z))
| pure_associator (X Y Z: C)
  : isotopy (@pure C _ _ _ _ _ (𝒱.associator X Y Z).hom) (associator ⟨X, 0⟩ ⟨Y, 0⟩ ⟨Z, 0⟩)
| pure_leftUnitor (X: C)
  : isotopy (@pure C _ _ _ _ _ (𝒱.leftUnitor X).hom) (leftUnitor ⟨X, 0⟩)
| pure_rightUnitor (X: C)
  : isotopy (@pure C _ _ _ _ _ (𝒱.rightUnitor X).hom) (rightUnitor ⟨X, 0⟩)
| pure_braiding (X Y: C)
  : isotopy (@pure C _ _ _ _ _ (𝒮.braiding X Y).hom) (braiding ⟨X, 0⟩ ⟨Y, 0⟩)
| effectful_identity (X: C)
  : isotopy (effectful (𝟙 X)) (identity ⟨tensorUnit' ⊗ X, 1⟩)
--TODO: effectful whiskering?
| effectful_inclusion_left {X Y Z: C} (f: X ⟶ Y) (g: Value.box Y ⟶ Value.box Z)
  : isotopy 
    (effectful (f ≫ ℰ.inclusion.map' g))
    (comp (effectful f) (whiskerLeft state' (pure g)))
| effectful_inclusion_right {X Y Z: C} (f: Value.box X ⟶ Value.box Y) (g: Y ⟶ Z)
  : isotopy 
    (effectful (ℰ.inclusion.map' f ≫ g))
    (comp (whiskerLeft state' (pure f)) (effectful g))

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
| identity ⟨X, _⟩ => 𝟙 X
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

-- inductive DiagramPort (C: Type u)
-- | state
-- | tensor (A B: DiagramPort C)
-- | pure (X: C)


-- open DiagramPort
-- open TensorMonoid

-- inductive DiagramPort.is_pure {C: Type u}: DiagramPort C -> Prop
-- | pure (X): is_pure (pure X)
-- | tensor {A B}: is_pure A -> is_pure B -> is_pure (A ⊗ B)

-- inductive DiagramPort.is_left_threaded {C: Type u}: DiagramPort C -> Prop
-- | tensor {A}: is_pure A -> is_left_threaded (state ⊗ A)

-- inductive DiagramPort.is_right_threaded {C: Type u}: DiagramPort C -> Prop
-- | tensor {A}: is_pure A -> is_right_threaded (A ⊗ state)

-- inductive Diagram {C: Type u}
--   [TensorMonoid C]
--   [Quiver.{v} (Value C)]
--   [Quiver.{v} C]
--   : DiagramPort C -> DiagramPort C -> Type (max u v)
-- | identity (X): Diagram X X
-- | comp {X Y Z}: Diagram X Y -> Diagram Y Z -> Diagram X Z
-- | whiskerLeft {X Y}: (Z: DiagramPort C) -> Diagram X Y -> Diagram (Z ⊗ X) (Z ⊗ Y) 
-- | whiskerRight {X Y}: Diagram X Y -> (Z: DiagramPort C) -> Diagram (X ⊗ Z) (Y ⊗ Z)
-- | associator (X Y Z): Diagram ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)) 
-- | associator_inv (X Y Z): Diagram (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z)
-- | leftUnitor (X): Diagram (tensorUnit' ⊗ X) X
-- | leftUnitor_inv (X): Diagram X (tensorUnit' ⊗ X)
-- | rightUnitor (X): Diagram (X ⊗ tensorUnit') X
-- | rightUnitor_inv (X): Diagram X (X ⊗ tensorUnit')
-- | braiding (X Y): Diagram (X ⊗ Y) (Y ⊗ X)
-- | split: Diagram state (state ⊗ state)
-- | join: Diagram (state ⊗ state) state
-- | merge (X Y: C): Diagram (DiagramPort.pure X ⊗ DiagramPort.pure Y) (DiagramPort.pure (X ⊗ Y))
-- | merge_inv (X Y: C): Diagram (DiagramPort.pure (X ⊗ Y)) (DiagramPort.pure X ⊗ DiagramPort.pure Y)
-- | pure {X Y: Value C}: (X ⟶ Y) -> Diagram (DiagramPort.pure X.inclusion) (DiagramPort.pure Y.inclusion) 
-- | effectful {X Y: C}: (X ⟶ Y) -> Diagram ((DiagramPort.pure X) ⊗ state)  ((DiagramPort.pure Y) ⊗ state)

-- inductive Diagram.inverses {C: Type u}
--   [TensorMonoid C]
--   [Quiver.{v} (Value C)]
--   [Quiver.{v} C]
--   : {X Y: DiagramPort C} -> Diagram X Y -> Diagram Y X -> Prop
-- | associator (X Y Z): inverses (associator X Y Z) (associator_inv X Y Z)
-- | leftUnitor (X): inverses (leftUnitor X) (leftUnitor_inv X)
-- | rightUnitor (X): inverses (rightUnitor X) (rightUnitor_inv X)
-- | braiding (X Y): inverses (braiding X Y) (braiding Y X)
-- | merge (X Y): inverses (merge X Y) (merge_inv X Y)
-- | symm {X Y} {f: Diagram X Y} {g: Diagram Y X}: inverses f g -> inverses g f

-- inductive Diagram.isotopy {C: Type u}
--   [TensorMonoid C]
--   [Category (Value C)]
--   [Category C]
--   [𝒱: PremonoidalCategory (Value C)]
--   [PremonoidalCategory C]
--   : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
-- | identity_left {X Y} (f: Diagram X Y): isotopy (comp f (identity Y)) f
-- | identity_right {X Y} (f: Diagram X Y): isotopy (comp (identity X) f) f
-- | comp_assoc {X Y Z W} {f: Diagram X Y} {g: Diagram Y Z} {h: Diagram Z W}
--   : isotopy (comp f (comp g h)) (comp (comp f g) h)
-- | inv_comp {X Y} {f: Diagram X Y} {g: Diagram Y X}
--   : inverses f g -> isotopy (comp f g) (identity X)
-- | whiskerLeft_identity (X Y)
--   : isotopy (whiskerLeft X (identity Y)) (identity (X ⊗ Y))
-- | whiskerRight_identity (X Y)
--   : isotopy (whiskerRight (identity X) Y) (identity (X ⊗ Y))
-- | sliding {X₁ Y₁ X₂ Y₂} (f: Diagram X₁ Y₁) (g: Diagram X₂ Y₂)
--   : isotopy 
--     (comp (whiskerRight f X₂) (whiskerLeft Y₁ g)) 
--     (comp (whiskerLeft X₁ g) (whiskerRight f Y₂))
-- | associator_left {X Y Z X'} (f: Diagram X X')
--   : isotopy
--     (comp (whiskerRight (whiskerRight f Y) Z) (associator X' Y Z))
--     (comp (associator X Y Z) (whiskerRight f (Y ⊗ Z)))
-- | associator_mid {X Y Z Y'} (f: Diagram Y Y')
--   : isotopy
--     (comp (whiskerRight (whiskerLeft X f) Z) (associator X Y' Z))
--     (comp (associator X Y Z) (whiskerLeft X (whiskerRight f Z)))
-- | associator_right {X Y Z Z'} (f: Diagram Z Z')
--   : isotopy
--     (comp (whiskerLeft (X ⊗ Y) f) (associator X Y Z'))
--     (comp (associator X Y Z) (whiskerLeft X (whiskerLeft Y f)))
-- | leftUnitor {X Y} (f: Diagram X Y)
--   : isotopy
--     (comp (leftUnitor X) f)
--     (comp (whiskerLeft tensorUnit' f) (leftUnitor Y))
-- | rightUnitor {X Y} (f: Diagram X Y)
--   : isotopy
--     (comp (rightUnitor X) f)
--     (comp (whiskerRight f tensorUnit') (rightUnitor Y))
-- | braiding_left {X Y Z} (f: Diagram X Y)
--   : isotopy
--     (comp (whiskerLeft Z f) (braiding Z Y))
--     (comp (braiding Z X) (whiskerRight f Z))
-- | braiding_right {X Y Z} (f: Diagram X Y)
--   : isotopy
--     (comp (whiskerRight f Z) (braiding Y Z))
--     (comp (braiding X Z) (whiskerLeft Z f))
-- | merge_left {X Y Z: C} (f: Value.box X ⟶ Value.box Y)
--   : isotopy
--     (comp (merge Z X) (pure (𝒱.whiskerLeft Z f)))
--     (comp (whiskerLeft _ (pure f)) (merge Z Y))
-- | merge_right {X Y Z: C} (f: Value.box X ⟶ Value.box Y)
--   : isotopy
--     (comp (merge X Z) (pure (𝒱.whiskerRight f Z)))
--     (comp (whiskerRight (pure f) _) (merge Y Z))
-- | triangle (X Y)
--   : isotopy
--     (comp (associator X tensorUnit' Y) (whiskerLeft X (leftUnitor Y)))
--     (whiskerRight (rightUnitor X) Y)
-- | pentagon (X Y Z W)
--   : isotopy
--     (comp (associator (X ⊗ Y) Z W) (associator X Y (Z ⊗ W)))
--     (comp (whiskerRight (associator X Y Z) W) 
--       (comp (associator X (Y ⊗ Z) W) (whiskerLeft X (associator Y Z W))))
-- | hexagon (X Y Z)
--   : isotopy
--     (comp (associator X Y Z) (comp (braiding X (Y ⊗ Z)) (associator Y Z X)))
--     (comp (whiskerRight (braiding X Y) Z) (comp (associator Y X Z) (whiskerLeft Y (braiding X Z))))
-- | hoop: isotopy (comp split join) (identity state)
-- -- ...

-- inductive Diagram.redex {C: Type u}
--   [TensorMonoid C]
--   [Quiver.{v} (Value C)]
--   [Quiver.{v} C]
--   : {X Y: DiagramPort C} -> Diagram X Y -> Diagram X Y -> Prop
-- | congr_comp {X Y} {f f': Diagram X Y} {g g': Diagram Y Z}:
--   redex f f' -> redex g g' -> redex (comp f g) (comp f' g')
-- | congr_whiskerLeft {X Y Z} {f g: Diagram X Y}:
--   redex f g -> redex (whiskerLeft Z f) (whiskerLeft Z g)
-- | congr_whiskerRight {X Y Z} {f g: Diagram X Y}:
--   redex f g -> redex (whiskerRight f Z) (whiskerRight g Z)
-- | identity_left {X Y} (f: Diagram X Y): redex (comp f (identity Y)) f
-- | identity_left_inv {X Y} (f: Diagram X Y): redex f (comp f (identity Y))
-- | identity_right {X Y} (f: Diagram X Y): redex (comp (identity X) f) f
-- | identity_right_inv {X Y} (f: Diagram X Y): redex f (comp (identity X) f)
-- | assoc_comp {X Y Z W} {f: Diagram X Y} {g: Diagram Y Z} {h: Diagram Z W}
--   : redex (comp f (comp g h)) (comp (comp f g) h)
-- | assoc_comp_inv {X Y Z W} {f: Diagram X Y} {g: Diagram Y Z} {h: Diagram Z W}
--   : redex (comp (comp f g) h) (comp f (comp g h))
-- | whiskerLeft_identity (X Y)
--   : redex (whiskerLeft X (identity Y)) (identity (X ⊗ Y))
-- | whiskerLeft_identity_inv (X Y)
--   : redex (identity (X ⊗ Y)) (whiskerLeft X (identity Y))
-- | whiskerRight_identity (X Y)
--   : redex (whiskerRight (identity X) Y) (identity (X ⊗ Y))
-- | whiskerRight_identity_inv (X Y)
--   : redex (identity (X ⊗ Y)) (whiskerRight (identity X) Y)
-- -- ...