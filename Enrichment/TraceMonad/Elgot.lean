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

def OptTraces.iterated {ε τ α β} 
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  : ℕ -> α-> OptTraces ε τ (β ⊕ α)
  | 0, a => pure (Sum.inr a)
  | n + 1, a => (OptTraces.iterated f n a) >>= Sum.elim (pure ∘ Sum.inl) f

def OptTraces.is_trace_step {ε τ α β}
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (r: α)
  (e: ε)
  : Prop
  := (f a).terminating (Sum.inr r) e

theorem OptTraces.iterated_terminating_zero {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (c e)
  : (iterated f 0 a).terminating c e ↔ (c = Sum.inr a ∧ e = 1)
  := by rfl

theorem OptTraces.iterated_nonterminating_zero {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (t)
  : (iterated f 0 a).nonterminating t ↔ False
  := by rfl

theorem OptTraces.iterated_terminating_succ {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (n: ℕ)
  (a: α)
  (c e)
  : (iterated f n.succ a).terminating c e ↔ 
  (∃ c' e' e'',
    terminating (iterated f n a) c' e' ∧ 
      terminating (Sum.elim (pure ∘ Sum.inl) f c') c e'' ∧ 
      e = e' * e'')
  := by rfl

theorem OptTraces.iterated_nonterminating_succ {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (n: ℕ)
  (a: α)
  (t)
  : (iterated f n.succ a).nonterminating t ↔ 
    (iterated f n a).nonterminating t 
      ∨ ∃c e t', (iterated f n a).terminating c e 
        ∧ (Sum.elim (pure ∘ Sum.inl) f c).nonterminating t'
        ∧ t = e • t'
  := by rfl

theorem OptTraces.iterated_terminating_succ' {ε τ α β}
  [Monoid ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (n: ℕ)
  (a: α)
  (c e)
  : (iterated f n.succ a).terminating c e ↔
    ((∃b, (iterated f n a).terminating (Sum.inl b) e ∧ c = Sum.inl b) ∨ (∃a' e' e'', 
      (iterated f n a).terminating (Sum.inr a') e' ∧ 
        (f a').terminating c e'' ∧ e = e' * e''))
  := ⟨
      λ
      | ⟨Sum.inl b, e', e'', Hfn, ⟨Hb, He''⟩, He⟩ => 
        have p: e = e' := by simp [He, He''];
        Or.inl ⟨b, p ▸ Hfn, Hb⟩
      | ⟨Sum.inr a', e', e'', Hfn, Hf, He⟩ => Or.inr ⟨a', e', e'', Hfn, Hf, He⟩,
      λ
      | Or.inl ⟨b, Hfn, Hb⟩ => ⟨Sum.inl b, e, 1, Hfn, ⟨Hb, rfl⟩, by simp⟩ 
      | Or.inr ⟨a', e', e'', Hfn, Hf, He⟩ => ⟨Sum.inr a', e', e'', Hfn, Hf, He⟩
    ⟩

theorem OptTraces.iterated_nonterminating_succ' {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (n: ℕ)
  (a: α)
  (t)
  : (iterated f n.succ a).nonterminating t ↔ 
    (iterated f n a).nonterminating t 
      ∨ ∃a' e t', (iterated f n a).terminating (Sum.inr a') e 
        ∧ (f a').nonterminating t'
        ∧ t = e • t'
  := ⟨
    λ
    | Or.inl H => Or.inl H
    | Or.inr ⟨Sum.inr a', e, t', Ha', Ht', Ht⟩ => Or.inr ⟨a', e, t', Ha', Ht', Ht⟩,
    λ
    | Or.inl H => Or.inl H
    | Or.inr ⟨a', e, t', Ha', Ht', Ht⟩ => Or.inr ⟨Sum.inr a', e, t', Ha', Ht', Ht⟩   
  ⟩ 

theorem OptTraces.iterated_terminating_succ_inr {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (n: ℕ)
  (a: α)
  (a' e)
  : (iterated f n.succ a).terminating (Sum.inr a') e ↔ 
    ∃a'' e' e'', 
      (iterated f n a).terminating (Sum.inr a'') e' 
        ∧ is_trace_step f a'' a' e'' 
        ∧ e = e' * e''
  := ⟨
      λ
      | ⟨Sum.inl b, _, _, _, ⟨Hb, _⟩, _⟩ => by contradiction
      | ⟨Sum.inr a', e', e'', Hfn, Hf, He⟩ => ⟨a', e', e'', Hfn, Hf, He⟩,
      λ ⟨a', e', e'', Hfn, Hf, He⟩ => ⟨Sum.inr a', e', e'', Hfn, Hf, He⟩
    ⟩

def OptTraces.iterated_terminating {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α) (b: β) (e: ε): Prop
  := ∃n: ℕ, (OptTraces.iterated f n a).terminating (Sum.inl b) e

def OptTraces.iterated_nonterminating {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α) (t: τ): Prop
  := ∃n: ℕ, (OptTraces.iterated f n a).nonterminating t

def accumulate_stream {ε} [Mul ε] [One ε] (es: Stream' ε): Stream' ε
  | 0 => 1
  | n + 1 => accumulate_stream es n * es n

def OptTraces.is_preinfinite_trace {ε τ α β}
  (f: α -> OptTraces ε τ (β ⊕ α))
  (as: Stream' α)
  : Prop
  := ∀n: ℕ, ∃e, OptTraces.is_trace_step f (as n) (as n.succ) e

def OptTraces.is_infinite_trace {ε τ α β}
  (f: α -> OptTraces ε τ (β ⊕ α))
  (as: Stream' α)
  (es: Stream' ε)
  : Prop
  := ∀n: ℕ, OptTraces.is_trace_step f (as n) (as n.succ) (es n)

noncomputable def OptTraces.is_preinfinite_trace.to_event_trace {ε τ α β}
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  (H: is_preinfinite_trace f as)
  : Stream' ε
  := λn => choose (H n)

theorem OptTraces.is_preinfinite_trace.to_infinite_trace {ε τ α β}
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  (H: is_preinfinite_trace f as)
  : is_infinite_trace f as H.to_event_trace
  := λn => choose_spec (H n)

noncomputable def OptTraces.is_preinfinite_trace.to_effect {ε τ α β}
  [FromTrace ε τ]
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  (H: is_preinfinite_trace f as)
  : τ := FromTrace.fromTrace H.to_event_trace

theorem OptTraces.is_infinite_trace_spec {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (as: Stream' α)
  (es: Stream' ε)
  (H: is_infinite_trace f as es)
  : ∀n, (iterated f n (as 0)).terminating (Sum.inr (as n)) (accumulate_stream es n)
  | 0 => ⟨rfl, rfl⟩   
  | n + 1 => ⟨
      (Sum.inr (as n)), (accumulate_stream es n), es n, 
        by simp [is_infinite_trace_spec f as es H n], 
        H n, rfl⟩ 

def OptTraces.infinitely_iterated {ε τ α β}
  [FromTrace ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (t: τ): Prop
  := ∃(as: Stream' α) (es: Stream' ε),
    as 0 = a ∧
    FromTrace.fromTrace es = t ∧ 
    is_infinite_trace f as es

theorem OptTraces.is_infinite_trace.to_infinitely_iterated {ε τ α β}
  [FromTrace ε τ]
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  {es: Stream' ε}
  (H: is_infinite_trace f as es)
  : infinitely_iterated f (as 0) (FromTrace.fromTrace es)
  := ⟨as, es, rfl, rfl, H⟩ 

theorem OptTraces.is_preinfinite_trace.to_infinitely_iterated {ε τ α β}
  [FromTrace ε τ]
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  (H: is_preinfinite_trace f as)
  : infinitely_iterated f (as 0) (H.to_effect)
  := H.to_infinite_trace.to_infinitely_iterated

theorem OptTraces.is_infinite_trace.to_infinitely_iterated' {ε τ α β}
  [FromTrace ε τ]
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  {es: Stream' ε}
  (H: is_infinite_trace f as es)
  (a: α)
  (Ha: as 0 = a)
  (e: τ)
  (He: FromTrace.fromTrace es = e)
  : infinitely_iterated f a e
  := ⟨as, es, Ha, He, H⟩ 

theorem OptTraces.is_preinfinite_trace.to_infinitely_iterated' {ε τ α β}
  [FromTrace ε τ]
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  (H: is_preinfinite_trace f as)
  (a: α)
  (Ha: as 0 = a)
  (e: τ)
  (He: H.to_effect = e)
  : infinitely_iterated f a e
  := H.to_infinite_trace.to_infinitely_iterated' a Ha e He

def exists_nfn {α} {β: α -> Prop}: (¬∀a: α, ¬β a) -> ∃a: α, β a 
  := λk => by_contradiction (λk' => k (λa h => k' ⟨a, h⟩))

noncomputable def OptTraces.iterated_sequence_helper {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e', 
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e') 
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  : (n: ℕ) -> {p: α × ε | ∃e', (OptTraces.iterated f n a).terminating (Sum.inr p.1) e'}
  | 0 => ⟨⟨a, 1⟩, 1, rfl, rfl⟩
  | n + 1 =>
    let Hv := iterated_sequence_helper f a I n;
    let HI := I n Hv.1.1 (choose Hv.2) (choose_spec Hv.2)
    let a'' := choose HI;
    let e' := choose (choose_spec HI);
    let HI' := choose_spec (choose_spec HI);
    ⟨⟨a'', e'⟩, _, HI'.1⟩

noncomputable def OptTraces.iterated_sequence {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e', 
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e') 
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  : Stream' α
  := λn => (iterated_sequence_helper f a I n).1.1

noncomputable def OptTraces.iterated_event_sequence {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e', 
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e') 
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  : Stream' ε
  := λn => (iterated_sequence_helper f a I n.succ).1.2

theorem OptTraces.iterated_sequence_zero {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e', 
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e') 
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  : (iterated_sequence f a I) 0 = a
  := rfl

theorem OptTraces.iterated_sequence_succ {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e', 
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e') 
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  (n: ℕ)
  : (iterated_sequence f a I) n.succ = 
    let Hv := iterated_sequence_helper f a I n;
    let HI := I n Hv.1.1 (choose Hv.2) (choose_spec Hv.2)
    choose HI
  := rfl

theorem OptTraces.iterated_sequence_spec {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e', 
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e') 
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  : is_infinite_trace f (iterated_sequence f a I) (iterated_event_sequence f a I)
  := λn =>
    let Hv := iterated_sequence_helper f a I n;
    let HI := I n Hv.1.1 (choose Hv.2) (choose_spec Hv.2)
    (choose_spec (choose_spec HI)).2

instance {ε τ} [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ]: DaggerMonad (OptTraces ε τ)
  where
  dagger f a := {
    terminating := OptTraces.iterated_terminating f a,
    nonterminating := λt => 
      OptTraces.iterated_nonterminating f a t ∨ 
      OptTraces.infinitely_iterated f a t
  }

theorem OptTraces.dagger_nonempty {ε τ α β} [Mul ε] [One ε] [SMul ε τ] [FromTrace ε τ] 
  (f: α -> OptTraces ε τ (β ⊕ α))
  (Hf: ∀a, (f a).is_nonempty)
  (a: α)
  : (DaggerMonad.dagger f a).is_nonempty
  := if p: ∃t, OptTraces.iterated_nonterminating f a t 
  then let ⟨t, H⟩ := p; Or.inr ⟨t, Or.inl H⟩ 
  else if q: ∃b e, OptTraces.iterated_terminating f a b e
  then Or.inl q
  else 
    have p: ¬∃n t, (OptTraces.iterated f n a).nonterminating t
      := λ⟨n, t, H⟩ => p ⟨t, n, H⟩;
    have q: ∀n c e, (OptTraces.iterated f n a).terminating c e -> c.isRight
      := λn c e h => match c with 
        | Sum.inl b => (q ⟨b, e, n, h⟩).elim 
        | Sum.inr _ => rfl
      ;
    have I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
      ∃a'' e', 
        (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e') 
          ∧ (OptTraces.is_trace_step f a' a'' e')
      := λn a' e H => 
        match (Hf a') with
        | Or.inl ⟨Sum.inl b, e', Hae⟩ => 
          have ca := q n.succ (Sum.inl b) (e * e') 
            ⟨Sum.inr a', e, e', H, Hae, rfl⟩;
          by contradiction
        | Or.inl ⟨Sum.inr a'', e', Hae⟩ => ⟨a'', 
          e', 
          (OptTraces.iterated_terminating_succ_inr f n a a'' _).mpr 
            ⟨a', e, e', H, Hae, rfl⟩,
          Hae⟩ 
        | Or.inr ⟨t, Ht⟩ => 
          (p ⟨n.succ, e • t, 
            (OptTraces.iterated_nonterminating_succ' f n a _).mpr
              (Or.inr ⟨a', e, t, H, Ht, rfl⟩)
          ⟩).elim
      ;
    Or.inr ⟨_, Or.inr (OptTraces.iterated_sequence_spec f a I).to_infinitely_iterated⟩ 