import Mathlib.Data.Stream.Defs
import Mathlib.Algebra.Group.Defs

class FromTrace (α β) where
  fromTrace: (Stream' α) -> β

class TraceAction (α: Type u) (β: Type v)
  [SMul α β]
  extends FromTrace α β: Type (max u v)
  where
  fromTrace_assoc: ∀a: α, ∀f: Stream' α, a • fromTrace f = fromTrace (f.cons a)