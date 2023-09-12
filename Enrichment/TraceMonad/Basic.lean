import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Set.Image

structure TraceMonad (ε: Type u1) (τ: Type u2) (α: Type u3): Type (max u1 (max u2 u3)) where
  terminating: α -> ε -> Prop
  nonterminating: τ -> Prop
  nonempty: (∃a e, terminating a e) ∨ (∃t, nonterminating t)

theorem TraceMonad.mk.injEq' {ε τ α} (t t': TraceMonad ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating ↔ t = t'
  := by cases t; cases t'; simp

theorem TraceMonad.mk.injEq_mp {ε τ α} (t t': TraceMonad ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating -> t = t'
  := by cases t; cases t'; simp

instance {ε τ α}: PartialOrder (TraceMonad ε τ α) where
  le t t' := t.terminating ≤ t'.terminating ∧ t.nonterminating ≤ t'.nonterminating 
  le_refl t := ⟨le_refl _, le_refl _⟩
  le_trans a b c Hab Hbc := ⟨le_trans Hab.1 Hbc.1, le_trans Hab.2 Hbc.2⟩ 
  le_antisymm t t' H H' := by
    have e1 := le_antisymm H.1 H'.1;
    have e2 := le_antisymm H.2 H'.2;
    cases t; cases t';
    simp only [] at e1 e2
    simp only [*]

def Terminates: Type := Empty

instance {ε} [Monoid ε]: MulAction ε Terminates where
  smul := λ_ t => match t with .
  one_smul := λt => match t with .
  mul_smul := λ_ _ t => match t with .

def TraceMonad.map_terminating {ε τ α ε'} (f: ε -> ε') (t: TraceMonad ε τ α)
  : TraceMonad ε' τ α where
  terminating a := f '' (t.terminating a)
  nonterminating := t.nonterminating
  nonempty := match t.nonempty with
    | Or.inl ⟨a, e, H⟩ => Or.inl ⟨a, f e, e, H, rfl⟩ 
    | Or.inr H => Or.inr H

theorem TraceMonad.map_terminating_id {ε τ α}
  : (t: TraceMonad α ε τ) -> t.map_terminating id = t
  | ⟨tt, tl, tne⟩ => by simp [map_terminating]

def TraceMonad.map_nonterminating {ε τ α τ'} (f: τ -> τ') (t: TraceMonad ε τ α)
  : TraceMonad ε τ' α where
  terminating := t.terminating
  nonterminating := f '' t.nonterminating
  nonempty := match t.nonempty with
    | Or.inl H => Or.inl H
    | Or.inr ⟨t, H⟩ => Or.inr ⟨f t, t, H, rfl⟩

theorem TraceMonad.map_nonterminating_id {α ε τ}
  : (t: TraceMonad α ε τ) -> t.map_nonterminating id = t
  | ⟨tt, tl, tne⟩ => by simp [map_nonterminating]

def TraceMonad.map' {ε τ α β} (f: α -> β) (x: TraceMonad ε τ α): TraceMonad ε τ β where
  terminating b e := ∃a, x.terminating a e ∧ b = f a
  nonterminating := x.nonterminating
  nonempty := match x.nonempty with
    | Or.inl ⟨a, e, H⟩ => Or.inl ⟨f a, e, a, H, rfl⟩ 
    | Or.inr H => Or.inr H

def TraceMonad.pure' {α} (ε τ) [Mul ε] [One ε] (a: α): TraceMonad ε τ α where
  terminating a' e := a = a' ∧ e = 1
  nonterminating _ := False
  nonempty := Or.inl ⟨a, 1, rfl, rfl⟩

def TraceMonad.bind' {ε τ α β} [Mul ε] [One ε] [SMul ε τ] (x: TraceMonad ε τ α) (f: α -> TraceMonad ε τ β)
  : TraceMonad ε τ β where
  terminating := λb e'' => ∃a e e', x.terminating a e ∧ (f a).terminating b e' ∧ e'' = e * e'
  nonterminating := λt' => 
    x.nonterminating t' ∨ 
    ∃a e t, x.terminating a e ∧ (f a).nonterminating t ∧ t' = e • t
  nonempty := match x.nonempty with
    | Or.inl ⟨a, e, Hae⟩ => match (f a).nonempty with
      | Or.inl ⟨b, e', H⟩ => Or.inl ⟨b, e * e', a, e, e', Hae, H, rfl⟩ 
      | Or.inr ⟨t, H⟩ => Or.inr ⟨e • t, Or.inr ⟨a, e, t, Hae, H, rfl⟩⟩  
    | Or.inr ⟨t, H⟩ => Or.inr ⟨t, Or.inl H⟩ 

instance {ε τ} [Mul ε] [One ε] [SMul ε τ]: Monad (TraceMonad ε τ) where
  pure := TraceMonad.pure' _ _
  bind := TraceMonad.bind' --TODO: why does stuff fail to infer without this?

instance {ε τ} [M: Monoid ε] [A: MulAction ε τ]: LawfulMonad (TraceMonad ε τ) :=
  LawfulMonad.mk' (TraceMonad ε τ) 
    (λ⟨xt, xl, _xne⟩ => by
      apply TraceMonad.mk.injEq_mp
      constructor
      . funext b e''
        exact propext ⟨
          λ⟨_a, e, e', H, ⟨Ha, He'⟩, He''⟩ => (M.mul_one e ▸ He' ▸ He'') ▸ Ha ▸ H,
          λH => ⟨b, e'', 1, H, ⟨rfl, rfl⟩, (M.mul_one e'').symm⟩ 
        ⟩
      . funext t'
        exact propext ⟨
          λ (Or.inl H) => H,
          Or.inl
        ⟩ 
    ) 
    (λx f => by
      apply TraceMonad.mk.injEq_mp
      constructor
      . funext b e''
        exact propext ⟨
          λ⟨_a, e, e', ⟨Ha, He⟩, H, He''⟩ => (M.one_mul e' ▸ He ▸ He'') ▸ Ha ▸ H,
          λH => ⟨x, 1, e'', ⟨rfl, rfl⟩, H, (M.one_mul e'').symm⟩  
        ⟩  
      . funext t'
        exact propext ⟨
          λ(Or.inr ⟨_a, e, t, ⟨Ha, He⟩, H, Ht'⟩) => (A.one_smul t ▸ He ▸ Ht') ▸ Ha ▸ H,
          λH => Or.inr ⟨x, 1, t', ⟨rfl, rfl⟩, H, (A.one_smul _).symm⟩ 
        ⟩
    ) 
    (λ⟨xt, xl, _xne⟩ f g => by
      apply TraceMonad.mk.injEq_mp
      constructor
      . funext d e'
        exact propext ⟨
          λ⟨b, el, er, ⟨a, el', er', Hel', Her', Helr'⟩, Her, He'⟩ => 
            ⟨a, el', er' * er, Hel', ⟨b, er', er, Her', Her, rfl⟩, 
              by simp [He', Helr', M.mul_assoc]⟩,
          λ⟨a, el, er, Hel, ⟨b, el', er', Hel', Her', Helr'⟩, He'⟩ => 
            ⟨b, el * el', er', ⟨a, el, el', Hel, Hel', rfl⟩, Her', 
              by simp [He', Helr', M.mul_assoc]⟩
        ⟩  
      . funext t'
        exact propext ⟨
          λ
          | Or.inl (Or.inl H) => Or.inl H
          | Or.inl (Or.inr ⟨a, el, t, Hel, Ht, Ht'⟩) => Or.inr ⟨a, el, t, Hel, Or.inl Ht, Ht'⟩
          | Or.inr ⟨b, eb, t, ⟨a, ea, ea', Hea, Hea', Heb⟩, Ht, Ht'⟩ => 
            Or.inr ⟨a, ea, ea' • t, Hea, Or.inr ⟨b, ea', t, Hea', Ht, rfl⟩, 
              by simp [Ht', Heb, A.mul_smul]⟩,
          λ
          | Or.inl H => Or.inl (Or.inl H)
          | Or.inr ⟨a, el, t, Hel, Or.inl Ht, Ht'⟩ => Or.inl (Or.inr ⟨a, el, t, Hel, Ht, Ht'⟩)
          | Or.inr ⟨a, el, tl, Hel, Or.inr ⟨b, er, tr, Her, Htr, Htl⟩, Ht'⟩ => 
            Or.inr ⟨b, el * er, tr, ⟨a, el, er, Hel, Her, rfl⟩, Htr, 
              by simp [Ht', Htl, A.mul_smul]⟩  
        ⟩
    )