import Enrichment.TraceMonad.Basic
import Enrichment.TraceMonad.TraceAction
import Enrichment.Elgot.Monad
open Classical

def Trace.steps {ε τ α β}
  (f: α -> Trace ε τ (β ⊕ α))
  (a: α)
  : ℕ -> Trace ε τ (β ⊕ α)
  | 0 => f a
  | n + 1 => match Trace.steps f a n with
    | terminating (Sum.inr a) _ => f a
    | t => t

def Trace.stepped {ε τ α β} [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
  (f: α -> Trace ε τ (β ⊕ α))
  (a: α)
  : ℕ -> Trace ε τ (β ⊕ α)
  | 0 => f a
  | n + 1 => match Trace.stepped f a n with
    | terminating (Sum.inr a) e => (f a).prepend e
    | t => t

def Trace.stops {ε τ α β}
  (f: α -> Trace ε τ (β ⊕ α)) (a: α) (n: ℕ)
  : Bool := match steps f a n with
  | terminating (Sum.inr _) _ => false
  | _ => true

def Trace.stops' {ε τ α β} [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
  (f: α -> Trace ε τ (β ⊕ α)) (a: α) (n: ℕ)
  : Bool := match stepped f a n with
  | terminating (Sum.inr _) _ => false
  | _ => true

-- def Trace.stops_spec {ε τ α β} [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
--   : @stops ε τ α β = stops'
--   := sorry

-- def Trace.effect {ε τ α β} [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
--   (f: α -> Trace ε τ (β ⊕ α)) (a: α) (n: ℕ) (H: ¬stops f a n)
--   : ε := by
--   simp only [stops] at H;
--   generalize Hs: steps f a n = s;
--   rw [Hs] at H
--   exact match s with
--   | terminating (Sum.inr _) e => e
--   | terminating (Sum.inl _) _ | nonterminating _ => (H rfl).elim

-- def Trace.effects {ε τ α β} [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
--   (f: α -> Trace ε τ (β ⊕ α)) (a: α)
--   (H: ∀n, ¬stops f a n) (n: ℕ)
--   : ε := effect f a n (H n)

-- def Trace.result_at {ε τ α β} [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
--   (f: α -> Trace ε τ (β ⊕ α)) (a: α)
--   (n: ℕ) (H: stops f a n)
--   : Trace ε τ β := by
--   simp only [stops_spec, stops'] at H;
--   generalize Hs: stepped f a n = s;
--   rw [Hs] at H
--   match s with
--   | terminating (Sum.inl b) e => exact terminating b e
--   | terminating (Sum.inr _) e => contradiction 
--   | nonterminating t => exact nonterminating t
  
-- noncomputable def Trace.result {ε τ α β}
--   [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
--   (f: α -> Trace ε τ (β ⊕ α)) (a: α)
--   (H: ∃n, stops f a n)
--   : Trace ε τ β
--   := result_at f a (choose H) (choose_spec H)

-- noncomputable instance Trace.instDaggerMonad [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
--   : DaggerMonad (Trace ε τ)
--   where
--   dagger f a := if H: ∃n, stops f a n then result f a H else nonterminating (FromTrace.fromTrace (effects f a (λn C => H ⟨n, C⟩)))