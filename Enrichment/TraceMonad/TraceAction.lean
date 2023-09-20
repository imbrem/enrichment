import Mathlib.Data.Stream.Defs
import Mathlib.Algebra.Group.Defs

class FromTrace (α β) where
  fromTrace: (Stream' α) -> β

class TraceAction (α: Type u) (β: Type v)
  [SMul α β]
  extends FromTrace α β: Type (max u v)
  where
  fromTrace_assoc: ∀f: Stream' α, fromTrace f = f 0 • fromTrace f.tail

theorem TraceAction.fromTrace_assoc' {α β}
  [SMul α β] [A: TraceAction α β]
  (a: α) (f: Stream' α)
  : a • A.fromTrace f = A.fromTrace (f.cons a)
  := by 
    rw [fromTrace_assoc (f.cons a)]
    apply congr rfl
    apply congr rfl
    funext n
    cases n <;> rfl