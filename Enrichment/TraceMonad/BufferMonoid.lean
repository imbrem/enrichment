import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs

structure BufferMonoid (β ε) where
  buffer: β
  state: ε

def BufferMonoid.mul' {β ε} [Mul β] [Mul ε] (l r: BufferMonoid β ε): BufferMonoid β ε
  := ⟨r.buffer * l.buffer, l.state * r.state⟩

instance bufferMonoidMul [Mul β] [Mul ε]: Mul (BufferMonoid β ε) where
  mul l r := ⟨r.buffer * l.buffer, l.state * r.state⟩

def BufferMonoid.one' (β ε) [One β] [One ε]: BufferMonoid β ε
  := ⟨1, 1⟩

instance bufferMonoidOne [One β] [One ε]: One (BufferMonoid β ε) where
  one := ⟨1, 1⟩

def BufferMonoid.mul_def {β ε} [Mul β] [Mul ε] (l r: BufferMonoid β ε):
  l * r = ⟨r.buffer * l.buffer, l.state * r.state⟩
  := rfl

instance [B: Monoid β] [M: Monoid ε]: Monoid (BufferMonoid β ε) where
  mul_assoc a b c := by 
    cases a; cases b; cases c; 
    simp [HMul.hMul, Mul.mul, BufferMonoid.mk.injEq]
    constructor
    apply Eq.symm 
    apply B.mul_assoc
    apply M.mul_assoc
  mul_one a := by 
    cases a;
    simp only [HMul.hMul, Mul.mul, BufferMonoid.mk.injEq]
    constructor
    apply B.one_mul
    apply M.mul_one
  one_mul a := by 
    cases a;
    simp only [HMul.hMul, Mul.mul, BufferMonoid.mk.injEq]
    constructor
    apply B.mul_one
    apply M.one_mul

-- NOTE: our convention is that scalar multiplication sticks buffers onto the END, not the beginning

def BufferMonoid.flush_state {β ε} [SMul β ε] (t: BufferMonoid β ε)
  := t.buffer • t.state

def BufferMonoid.flush_state_one {β ε} [Monoid β] [One ε] [A: MulAction β ε]
  : @BufferMonoid.flush_state β ε _ 1 = 1
  := A.one_smul 1

def BufferMonoid.flush_state_mul {β ε} [SMul β ε] [Mul β] [Mul ε] (l r: BufferMonoid β ε)
  : @BufferMonoid.flush_state β ε _ (l * r) = (r.buffer * l.buffer) • (l.state * r.state)
  := rfl
 
def BufferMonoid.flush {β ε} [One β] [SMul β ε] [Mul ε] (t: BufferMonoid β ε)
  : BufferMonoid β ε
  := ⟨1, t.flush_state⟩

instance [SMul β ε] [Mul ε]: SMul (BufferMonoid β ε) ε where
  smul t e := e * t.flush_state

def BufferMonoid.smul_def {β ε} [SMul β ε] [Mul ε] (b: BufferMonoid β ε) (e: ε):
  b • e = e * b.flush_state 
  := rfl

-- instance {β ε} [Monoid β] [Monoid ε] [A: MulAction β ε]: MulAction (BufferMonoid β ε) ε where
--   one_smul b := by simp [BufferMonoid.smul_def, BufferMonoid.flush_state_one]
--   mul_smul x y e := by simp [
--     BufferMonoid.smul_def, BufferMonoid.flush_state_mul, BufferMonoid.flush_state, 
--     BufferMonoid.mul_def
--   ]