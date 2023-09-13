import Enrichment.TraceMonad.Basic
import Enrichment.Elgot.Monad
import Mathlib.Data.Stream.Defs
open Classical

class FromTrace (α β) where
  fromTrace: (Stream' α) -> β

class TraceAction (α: Type u) (β: Type v)
  [SMul α β]
  extends FromTrace α β: Type (max u v)
  where
  fromTrace_assoc: ∀a: α, ∀f: Stream' α, a • fromTrace f = fromTrace (f.cons a)

def TraceMonad.iterated {ε τ α β} 
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> TraceMonad ε τ (β ⊕ α))
  : ℕ -> α-> TraceMonad ε τ (β ⊕ α)
  | 0, a => pure (Sum.inr a)
  | n + 1, a => (TraceMonad.iterated f n a) >>= Sum.elim (pure ∘ Sum.inl) f

def TraceMonad.iterated_terminating {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> TraceMonad ε τ (β ⊕ α))
  (a: α) (b: β) (e: ε): Prop
  := ∃n: ℕ, (TraceMonad.iterated f n a).terminating (Sum.inl b) e

def TraceMonad.iterated_nonterminating {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> TraceMonad ε τ (β ⊕ α))
  (a: α) (t: τ): Prop
  := ∃n: ℕ, (TraceMonad.iterated f n a).nonterminating t

def TraceMonad.is_trace_step {ε τ α β}
  (f: α -> TraceMonad ε τ (β ⊕ α))
  (a a': α)
  (e: ε)
  : Prop
  := (f a).terminating (Sum.inr a') e

def TraceMonad.is_infinite_trace {ε τ α β}
  (f: α -> TraceMonad ε τ (β ⊕ α))
  (as: Stream' α)
  (es: Stream' ε)
  : Prop
  := ∀n: ℕ, TraceMonad.is_trace_step f (as n) (as n.succ) (es n)

def TraceMonad.infinitely_iterated {ε τ α β}
  [FromTrace ε τ]
  (f: α -> TraceMonad ε τ (β ⊕ α))
  (a: α)
  (t: τ): Prop
  := ∃(as: Stream' α) (es: Stream' ε),
    as 0 = a ∧
    FromTrace.fromTrace es = t ∧ 
    is_infinite_trace f as es

instance {ε τ} [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]: DaggerMonad (TraceMonad ε τ)
  where
  dagger f a := {
    terminating := TraceMonad.iterated_terminating f a,
    nonterminating := λt => 
      TraceMonad.iterated_nonterminating f a t ∨ 
      TraceMonad.infinitely_iterated f a t,
    nonempty := if p: ∃t, TraceMonad.iterated_nonterminating f a t 
      then let ⟨t, H⟩ := p; Or.inr ⟨t, Or.inl H⟩ 
      else if q: ∃b e, TraceMonad.iterated_terminating f a b e
      then Or.inl q
      else 
        have p: ¬∃n t, (TraceMonad.iterated f n a).nonterminating t := sorry;
        have p: ∀n, ∃c e, (TraceMonad.iterated f n a).terminating c e := sorry;
        have p: ∀n, ∃a' e, (TraceMonad.iterated f n a).terminating (Sum.inr a') e := sorry;
        have p: ∀n a' e, (TraceMonad.iterated f n a).terminating (Sum.inr a') e 
          -> ∃a'' e', TraceMonad.is_trace_step f a' a'' e'
          := sorry
        sorry
  }