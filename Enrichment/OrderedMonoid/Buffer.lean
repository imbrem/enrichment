import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.UpperLower
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice

import Enrichment.InvlessMonoid.Basic

structure Buffer {α ε} [Monoid α] [Monoid ε] (φ: MonoidHom α ε) where
  state: ε
  buffer: α

def Buffer.flush {α ε} [Monoid α] [Monoid ε] {φ: MonoidHom α ε} (b: Buffer φ): ε
  := b.state * φ b.buffer
  
def Buffer.flushed {α ε} [Monoid α] [Monoid ε] {φ: MonoidHom α ε} (b: Buffer φ)
  : Buffer φ where
  state := b.flush
  buffer := 1

--TODO: instOrderedMonoid
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