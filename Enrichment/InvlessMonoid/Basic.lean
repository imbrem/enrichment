
import Mathlib.Algebra.Group.Defs

class InvlessMonoid (α) extends CancelMonoid α where
  mul_id_left: ∀a b: α, a * b = 1 -> a = 1
  mul_id_right: ∀a b: α, a * b = 1 -> b = 1
    := λa b H => by rw [<-H, mul_id_left a b H]; simp
  mul_id_iff: ∀a b: α, a * b = 1 ↔ a = 1 ∧ b = 1
    := λa b => ⟨
      λH => ⟨mul_id_left a b H, mul_id_right a b H⟩, 
      λ⟨Ha, Hb⟩ => by rw [Ha, Hb]; simp⟩ 