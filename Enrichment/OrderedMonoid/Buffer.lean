import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.UpperLower
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice

structure Buffer (α ε) where
  buffer: List α
  state: ε

class BufferAction (α ε) where
  append: ε -> α -> ε

def BufferAction.flush {α ε} [BufferAction α ε] (state: ε): List α -> ε
  | [] => state
  | a::buffer => append (flush state buffer) a

def Buffer.flush {α ε} [BufferAction α ε] (b: Buffer α ε): ε
  := BufferAction.flush b.state b.buffer
  
def Buffer.flushed {α ε} [BufferAction α ε] (b: Buffer α ε)
  : Buffer α ε where
  buffer := []
  state := b.flush

instance Buffer.instPartialOrder {α: Type u} {ε: Type v} [BufferAction α ε]
  : PartialOrder (Buffer α ε) where
  le := sorry
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry