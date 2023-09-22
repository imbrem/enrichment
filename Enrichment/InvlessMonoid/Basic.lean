
import Mathlib.Algebra.Group.Defs

class InvlessMonoid (α) extends CancelMonoid α where
  mul_id_left: ∀a b: α, a * b = 1 -> a = 1

theorem InvlessMonoid.mul_id_right {α} [InvlessMonoid α]
  : ∀a b: α, a * b = 1 -> b = 1
  := λa b H => by rw [<-H, mul_id_left a b H]; simp

theorem InvlessMonoid.mul_id_iff {α} [InvlessMonoid α]
  : ∀a b: α, a * b = 1 ↔ a = 1 ∧ b = 1
  := λa b => ⟨
      λH => ⟨mul_id_left a b H, mul_id_right a b H⟩, 
      λ⟨Ha, Hb⟩ => by rw [Ha, Hb]; simp⟩

instance listInvlessMonoid (α): InvlessMonoid (List α) where
  one := []
  mul l r := l ++ r
  mul_assoc := List.append_assoc
  mul_one := List.append_nil
  one_mul := List.nil_append
  mul_left_cancel a b c := (List.append_right_inj a).mp
  mul_right_cancel a b c := (List.append_left_inj b).mp 
  mul_id_left a b H := by cases a with
    | nil => rfl
    | cons => contradiction