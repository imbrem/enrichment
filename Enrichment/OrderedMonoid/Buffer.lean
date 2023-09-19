import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.UpperLower
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice

import Enrichment.InvlessMonoid.Basic
import Enrichment.OrderedMonoid.Basic

structure Buffer {α ε} [Monoid α] [Monoid ε] (φ: MonoidHom α ε) where
  state: ε
  buffer: α

def Buffer.flush {α ε} [Monoid α] [Monoid ε] {φ: MonoidHom α ε} (b: Buffer φ): ε
  := b.state * φ b.buffer
  
def Buffer.flushed {α ε} [Monoid α] [Monoid ε] {φ: MonoidHom α ε} (b: Buffer φ)
  : Buffer φ where
  state := b.flush
  buffer := 1

instance Buffer.instPartialOrder {α: Type u} {ε: Type v} [ma: InvlessMonoid α] [me: Monoid ε] {φ: MonoidHom α ε}
  : PartialOrder (Buffer φ) where
  le l h := ∃a: α, l.state = h.state * (φ a) ∧ h.buffer = a * l.buffer
  le_refl b := ⟨1, by simp⟩
  le_trans x y z := 
    λ⟨axy, Hsxy, Hbxy⟩ ⟨ayz, Hsyz, Hbyz⟩ => ⟨
      ayz * axy, 
      by rw [Hsxy, Hsyz, φ.map_mul, me.mul_assoc],
      by rw [Hbyz, Hbxy, ma.mul_assoc]⟩     
  le_antisymm x y Hxy Hyx :=
    by
      cases x; 
      cases y; 
      case mk ys yb =>
      cases Hxy;
      case intro axy Hxy => 
      cases Hyx;
      case intro ayx Hyx =>
      simp only [mk.injEq] at *
      have p: (axy * ayx) * yb = 1 * yb
        := by rw [ma.mul_assoc, <-Hyx.2, <-Hxy.2, ma.one_mul]
      have p: axy = 1 
        := ma.mul_id_left _ _ (ma.mul_right_cancel _ _ _ p)
      simp [p] at Hxy
      exact ⟨Hxy.1, Hxy.2.symm⟩

instance Buffer.instMonoid {α: Type u} {ε: Type v} [ma: Monoid α] [me: Monoid ε] {φ: MonoidHom α ε}
  : Monoid (Buffer φ) where
  mul l r := { state := l.state * r.state, buffer := l.buffer * r.buffer }
  mul_assoc a b c := by
    cases a; cases b; cases c
    simp only [HMul.hMul, mk.injEq]
    exact ⟨mul_assoc _ _ _, mul_assoc _ _ _⟩  
  one := { state := 1, buffer := 1 }
  one_mul a := by 
    cases a; 
    simp only [HMul.hMul, mk.injEq]; 
    exact ⟨one_mul _, one_mul _⟩
  mul_one a := by 
    cases a; 
    simp only [HMul.hMul, mk.injEq]; 
    exact ⟨mul_one _, mul_one _⟩

def Buffer.eq_one_of_le_one {α: Type u} {ε: Type v} [ma: InvlessMonoid α] [me: Monoid ε] {φ: MonoidHom α ε}
  : {x: Buffer φ} -> x ≤ 1 -> x = 1
  | ⟨b, s⟩, ⟨a, Hb, Hs⟩ => by
    simp only [OfNat.ofNat, One.one, mk.injEq] at *
    constructor
    . have Hb': b = 1 * φ 1 := (ma.mul_id_left _ _ Hs.symm) ▸ Hb; 
      rw [Hb', φ.map_one]
      exact mul_one _
    . exact ma.mul_id_right _ _ Hs.symm

def Buffer.le_one_iff_eq_one {α: Type u} {ε: Type v} [InvlessMonoid α] [Monoid ε] {φ: MonoidHom α ε}
  (b: Buffer φ): b ≤ 1 ↔ b = 1
  := ⟨eq_one_of_le_one, λH => H ▸ (le_refl _)⟩

def Buffer.state_mul {α ε} [Monoid α] [Monoid ε] {φ: MonoidHom α ε} (l r: Buffer φ):
  (l * r).state = l.state * r.state
  := rfl

def Buffer.buffer_mul {α ε} [Monoid α] [Monoid ε] {φ: MonoidHom α ε} (l r: Buffer φ):
  (l * r).buffer = l.buffer * r.buffer
  := rfl

-- THIS IS PROBABLY FALSE
-- instance Buffer.instLowerMonoid {α: Type u} {ε: Type v} [ma: InvlessMonoid α] [me: Monoid ε] {φ: MonoidHom α ε}
--   : LowerMonoid (Buffer φ) where
--   sub_id_lower_binary_product m := LowerSet.ext (Set.ext λx => ⟨
--     λ⟨l, Hl, r, Hr, H⟩  => m.lower' 
--       (by rw [eq_one_of_le_one Hl, one_mul] at H; exact H) 
--       Hr,
--     λH => ⟨1, sub_id_spec, x, H, by simp⟩ 
--   ⟩)
--   lower_binary_product_sub_id m := LowerSet.ext (Set.ext λx => ⟨
--     λ⟨l, Hl, r, Hr, H⟩  => m.lower' 
--       (by rw [eq_one_of_le_one Hr, mul_one] at H; exact H) 
--       Hl,
--     λH => ⟨x, H, 1, sub_id_spec, by simp⟩ 
--   ⟩)
--   lower_binary_product_assoc x y z := LowerSet.ext (Set.ext λw => ⟨
--     λ⟨l, ⟨il, Hil, ir, Hir, ⟨b, Hsl, Hbl⟩⟩, r, Hr, ⟨a, Hsx, Hbx⟩⟩  => 
--       have t: Buffer φ := Buffer.mk (ir.state * φ b * r.state) ir.buffer;
--       have Ht: t ∈ lower_binary_product y z := ⟨sorry, sorry, sorry, sorry, sorry⟩
--       sorry
--       ,
--     λH => sorry
--   ⟩)