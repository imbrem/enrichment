import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sum.Order
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Basic

structure Pom (L: Type) where
  carrier: Type
  order: PartialOrder carrier
  action: carrier -> L

instance {L}: CoeOut (Pom L) (Type) where
  coe := Pom.carrier

structure FPom (L: Type) extends Pom L where
  finite: Finite carrier

instance {L}: Coe (FPom L) (Pom L) where
  coe := FPom.toPom

abbrev FPom.mk' {L: Type} (α: Type) 
  [H: Finite α] (order: PartialOrder α) (action: α -> L): FPom L where
  carrier := α
  order := order
  action := action
  finite := H

abbrev Pom.toFPom {L: Type} (α: Pom L) [H: Finite α.carrier]: FPom L where
  toPom := α
  finite := H

def Pom.empty (L: Type): Pom L where
  carrier := Empty
  order := {
    le := λ_ _ => True,
    le_refl := (λa => match a with .),
    le_trans := (λa => match a with .),
    le_antisymm := (λa => match a with .)
  }
  action e := match e with.

def FPom.empty (L: Type): FPom L where
  toPom := Pom.empty L
  finite := @Finite.intro Empty 0 ⟨λ., λ., λ., λ.⟩

def PomFamily (N: Type) (L) := N -> Pom L
def PomFamily.mk {L} {N}: (N -> Pom L) -> PomFamily N L := id

def PomFamily.map_index {L N M} (F: PomFamily N L) (f: M -> N): PomFamily M L
  := λm => F (f m)
def PomFamily.succ {L} (F: PomFamily ℕ L): PomFamily ℕ L 
  := F.map_index Nat.succ

def Pom.sigma {L} {N: Type} [PartialOrder N] (F: PomFamily N L): Pom L where
  carrier := Lex (Sigma (λn => (F n).carrier))
  order := @Sigma.Lex.partialOrder _ _ _ (λn => (F n).order)
  action := (λ⟨n, e⟩ => (F n).action e)

abbrev PomFamily.toPom {N} [PartialOrder N] {L} (F: PomFamily N L): Pom L 
  := Pom.sigma F

def Pom.seq {L} (α β: Pom L): Pom L where
  carrier := Lex (α.carrier ⊕ β.carrier)
  order := @Sum.Lex.partialOrder _ _ α.order β.order
  action := Sum.elim α.action β.action

def FPom.seq {L} (α β: FPom L): FPom L where
  toPom := α.toPom.seq β.toPom
  finite := @Finite.instFiniteSum α.carrier β.carrier α.finite β.finite

def Pom.par_order {L} (α β: Pom L)
  : PartialOrder (α.carrier ⊕ β.carrier)
  := @Sum.instPartialOrderSum _ _ α.order β.order

@[simp]
def Pom.par_order_ll {L} {α β: Pom L}
  {a: α.carrier} {b: α.carrier}
  : ((α.par_order β).le (Sum.inl a) (Sum.inl b)) <-> α.order.le a b
  := by simp [LE.le, par_order]

@[simp]
def Pom.par_order_lr {L} {α β: Pom L}
  {a: α.carrier} {b: β.carrier}
  : ¬((α.par_order β).le (Sum.inl a) (Sum.inr b))
  := by simp [LE.le, par_order]

@[simp]
def Pom.par_order_rl {L} {α β: Pom L}
  {a: α.carrier} {b: β.carrier}
  : ¬((α.par_order β).le (Sum.inr b) (Sum.inl a))
  := by simp [LE.le, par_order]

@[simp]
def Pom.par_order_rr {L} {α β: Pom L}
  {a: β.carrier} {b: β.carrier}
  : ((α.par_order β).le (Sum.inr a) (Sum.inr b)) <-> β.order.le a b
  := by simp [LE.le, par_order]

def Pom.par {L} (α β: Pom L): Pom L where
  carrier := α.carrier ⊕ β.carrier
  order := α.par_order β
  action := Sum.elim α.action β.action

def FPom.par {L} (α β: FPom L): FPom L where
  toPom := α.toPom.par β.toPom
  finite := @Finite.instFiniteSum α.carrier β.carrier α.finite β.finite