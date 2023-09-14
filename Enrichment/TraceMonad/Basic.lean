import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Set.Image

inductive Trace (ε: Type u1) (τ: Type u2) (α: Type u3): Type (max u1 (max u2 u3))
  | terminating (a: α) (e: ε)
  | nonterminating (t: τ)

def Trace.before {ε τ α} [Mul ε] [SMul ε τ] (e: ε): Trace ε τ α -> Trace ε τ α
  | terminating a e' => terminating a (e * e')
  | nonterminating t => nonterminating (e • t)

def Trace.after {ε τ α} [Mul ε] [SMul ε τ] (e: ε): Trace ε τ α -> Trace ε τ α
  | terminating a e' => terminating a (e' * e)
  | nonterminating t => nonterminating t

def Terminates: Type := Empty

instance {ε} [Monoid ε]: MulAction ε Terminates where
  smul := λ_ t => match t with .
  one_smul := λt => match t with .
  mul_smul := λ_ _ t => match t with .

def Trace.map' {ε τ α β} (f: α -> β): Trace ε τ α -> Trace ε τ β
  | terminating a e => terminating (f a) e
  | nonterminating t => nonterminating t

def Trace.pure' {α} (ε τ) [One ε] (a: α): Trace ε τ α 
  := terminating a 1

def Trace.bind' {ε τ α β} [Mul ε] [One ε] [SMul ε τ] (x: Trace ε τ α) (f: α -> Trace ε τ β)
  : Trace ε τ β
  := match x with
  | terminating a e => 
    match f a with
    | terminating b e' => terminating b (e * e')
    | nonterminating t => nonterminating (e • t)
  | nonterminating t => nonterminating t

instance Trace.instMonad {ε τ} [Mul ε] [One ε] [SMul ε τ]: Monad (Trace ε τ) where
  pure := Trace.pure' _ _
  bind := Trace.bind'

--TODO: Trace lawful monad