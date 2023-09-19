import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.UpperLower
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice

class OrderedMonoid (α) extends Monoid α, PartialOrder α where
  mul_le_mul_left : ∀ (a b: α), a ≤ b -> ∀c: α, c * a ≤ c * b
  mul_le_mul_right : ∀ (a b: α), a ≤ b -> ∀c: α, a * c ≤ b * c

def binary_product {α} [Mul α] (ls rs: Set α): Set α
  := { p | ∃l ∈ ls, ∃r ∈ rs, p = l * r }

def lower_binary_product' {α} [Mul α] [PartialOrder α] (ls rs: Set α)
  : LowerSet α where
  carrier := { p | ∃l ∈ ls, ∃r ∈ rs, p ≤ l * r }
  lower' := λ_ _ Hab ⟨l, Hl, r, Hr, Ha⟩ => ⟨l, Hl, r, Hr, Hab.trans Ha⟩  

def lower_binary_product_spec' {α} [Mul α] [PartialOrder α] (ls rs: Set α)
  : lower_binary_product' ls rs = lowerClosure (binary_product ls rs)
  := LowerSet.ext (Set.ext (λ_ => ⟨
    λ⟨l, Hl, r, Hr, Hx⟩ => ⟨l*r, ⟨l, Hl, r, Hr, rfl⟩, Hx⟩,
    λ⟨_, ⟨l, Hl, r, Hr, rfl⟩, Hx⟩ => ⟨l, Hl, r, Hr, Hx⟩ 
  ⟩))
  
def lower_binary_product {α} [Mul α] [PartialOrder α] (ls rs: LowerSet α)
  : LowerSet α where
  carrier := { p | ∃l ∈ ls, ∃r ∈ rs, p ≤ l * r }
  lower' := λ_ _ Hab ⟨l, Hl, r, Hr, Ha⟩ => ⟨l, Hl, r, Hr, Hab.trans Ha⟩  

def lower_binary_product_spec {α} [Mul α] [PartialOrder α] (ls rs: LowerSet α)
  : lower_binary_product ls rs = lowerClosure (binary_product ls rs)
  := LowerSet.ext (Set.ext (λ_ => ⟨
    λ⟨l, Hl, r, Hr, Hx⟩ => ⟨l*r, ⟨l, Hl, r, Hr, rfl⟩, Hx⟩,
    λ⟨_, ⟨l, Hl, r, Hr, rfl⟩, Hx⟩ => ⟨l, Hl, r, Hr, Hx⟩ 
  ⟩))

def sub_id {α} [One α] [PartialOrder α]: LowerSet α where 
  carrier := λx => x ≤ 1 
  lower' := λ_ _ Hab H => Hab.trans H

theorem sub_id_spec {α} [H: One α] [O: PartialOrder α]: 1 ∈ @sub_id α H O
  := O.le_refl 1

class LowerMonoid (α) [Monoid α] [PartialOrder α] where
  sub_id_lower_binary_product: ∀(m: LowerSet α), lower_binary_product sub_id m = m
  lower_binary_product_sub_id: ∀(m: LowerSet α), lower_binary_product m sub_id = m
  lower_binary_product_assoc: ∀(a b c: LowerSet α), 
    lower_binary_product (lower_binary_product a b) c 
    = lower_binary_product a (lower_binary_product b c)

instance OrderedMonoid.instLowerMonoid {α} [M: OrderedMonoid α]
  : LowerMonoid α where
  sub_id_lower_binary_product m := LowerSet.ext (Set.ext (λx => ⟨
    λ⟨l, Hl, r, Hr, Hx⟩ => 
      m.lower' ((Hx.trans (M.mul_le_mul_right _ _ Hl _)).trans (le_of_eq (M.one_mul r))) Hr,
    λH => ⟨1, M.le_refl 1, x, H, by simp⟩ 
  ⟩))
  lower_binary_product_sub_id m := LowerSet.ext (Set.ext (λx => ⟨
    λ⟨l, Hl, r, Hr, Hx⟩ => 
      m.lower' ((Hx.trans (M.mul_le_mul_left _ _ Hr _)).trans (le_of_eq (M.mul_one l))) Hl,
    λH => ⟨x, H, 1, M.le_refl 1, by simp⟩ 
  ⟩))
  lower_binary_product_assoc a b c := LowerSet.ext (Set.ext (λx => ⟨
    λ⟨l, ⟨il, Hil, ir, Hir, Hlr⟩, r, Hr, Hx⟩ => ⟨il, Hil, ir * r, ⟨ir, Hir, r, Hr, le_refl _⟩, 
      by
        apply le_trans Hx
        rw [<-M.mul_assoc]
        apply M.mul_le_mul_right
        exact Hlr
      ⟩,
    λ⟨l, Hl, r, ⟨il, Hil, ir, Hir, Hlr⟩, Hx⟩ => ⟨l * il, ⟨l, Hl, il, Hil, le_refl _⟩, ir, Hir, 
      by
        apply le_trans Hx
        rw [M.mul_assoc]
        apply M.mul_le_mul_left
        exact Hlr
    ⟩
  ⟩))

instance LowerMonoid.instMonoidLowerSet {α} [Monoid α] [PartialOrder α] [M: LowerMonoid α]: Monoid (LowerSet α) where
  mul := lower_binary_product
  mul_assoc := M.lower_binary_product_assoc
  one := sub_id
  one_mul := M.sub_id_lower_binary_product
  mul_one := M.lower_binary_product_sub_id