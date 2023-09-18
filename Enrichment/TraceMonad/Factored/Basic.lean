import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Set.Image

import Enrichment.TraceMonad.Basic

structure OptTraces (ε: Type u1) (τ: Type u2) (α: Type u3): Type (max u1 (max u2 u3)) where
  terminating: α -> ε -> Prop
  nonterminating: τ -> Prop

def Trace.toOptTraces {ε τ α}: Trace ε τ α -> OptTraces ε τ α
  | terminating a e => { terminating := λa' e' => a' = a ∧ e' = e, nonterminating := λ_ => False }
  | nonterminating t => { terminating := λ_ _ => False, nonterminating := λt' => t = t' }

--TODO: OptTraces.{before, after}

def OptTraces.is_nonempty {ε τ α} (t: OptTraces ε τ α) := (∃a e, t.terminating a e) ∨ (∃e, t.nonterminating e)

class Traces (ε τ α) extends OptTraces ε τ α where
  nonempty: (∃a e, terminating a e) ∨ (∃e, nonterminating e)

def Trace.toOptTraces_is_nonempty {ε τ α}: (t: Trace ε τ α) -> t.toOptTraces.is_nonempty
  | terminating a e => Or.inl ⟨a, e, rfl, rfl⟩ 
  | nonterminating t => Or.inr ⟨t, rfl⟩

def Trace.toTraces {ε τ α} (t: Trace ε τ α): Traces ε τ α where
  toOptTraces := t.toOptTraces
  nonempty := t.toOptTraces_is_nonempty  

--TODO: Traces.{before, after}

theorem OptTraces.injEq' {ε τ α} (t t': OptTraces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating ↔ t = t'
  := by cases t; cases t'; simp

theorem OptTraces.injEq_mp {ε τ α} (t t': OptTraces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating -> t = t'
  := (t.injEq' t').mp

theorem Traces.injOpt_mp {ε τ α} (t t': Traces ε τ α)
  : t.toOptTraces = t'.toOptTraces -> t = t'
  := λH => by 
      cases t; cases t'; 
      let ⟨_, _⟩ := (OptTraces.injEq' _ _).mpr H; 
      simp only at *; 
      simp [*]

--TODO: there must be a better way...
theorem Traces.injOpt {ε τ α} (t t': Traces ε τ α)
  : t.toOptTraces = t'.toOptTraces ↔ t = t'
  := ⟨
    t.injOpt_mp t',
    λH => by rw [H]
  ⟩

theorem Traces.injEq' {ε τ α} (t t': Traces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating ↔ t = t'
  := Iff.trans (OptTraces.injEq' t.toOptTraces t'.toOptTraces) (Traces.injOpt t t')

theorem Traces.injEq_mp {ε τ α} (t t': Traces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating -> t = t'
  := (Traces.injEq' t t').mp

instance {ε τ α}: PartialOrder (OptTraces ε τ α) where
  le t t' := t.terminating ≤ t'.terminating ∧ t.nonterminating ≤ t'.nonterminating 
  le_refl t := ⟨le_refl _, le_refl _⟩
  le_trans a b c Hab Hbc := ⟨le_trans Hab.1 Hbc.1, le_trans Hab.2 Hbc.2⟩ 
  le_antisymm t t' H H' := by
    have e1 := le_antisymm H.1 H'.1;
    have e2 := le_antisymm H.2 H'.2;
    cases t; cases t';
    simp only [] at e1 e2
    simp only [*]

def OptTraces.map_terminating {ε τ α ε'} (f: ε -> ε') (t: OptTraces ε τ α)
  : OptTraces ε' τ α where
  terminating a := f '' (t.terminating a)
  nonterminating := t.nonterminating

theorem OptTraces.map_terminating_nonempty {ε τ α ε'} (f: ε -> ε') (t: OptTraces ε τ α)
  : t.is_nonempty -> (t.map_terminating f).is_nonempty
  | Or.inl ⟨a, e, H⟩ => Or.inl ⟨a, f e, e, H, rfl⟩
  | Or.inr H => Or.inr H

def Traces.map_terminating {ε τ α ε'} (f: ε -> ε') (t: Traces ε τ α)
  : Traces ε' τ α where
  toOptTraces := t.toOptTraces.map_terminating f
  nonempty := t.toOptTraces.map_terminating_nonempty f t.nonempty

theorem OptTraces.map_terminating_id {ε τ α}
  : (t: OptTraces α ε τ) -> t.map_terminating id = t
  | ⟨tt, tl⟩ => by simp [map_terminating]

theorem Traces.map_terminating_id {ε τ α} (t: Traces α ε τ) 
  : t.map_terminating id = t
  := Traces.injOpt_mp _ _ t.toOptTraces.map_terminating_id

def OptTraces.map_nonterminating {ε τ α τ'} (f: τ -> τ') (t: OptTraces ε τ α)
  : OptTraces ε τ' α where
  terminating := t.terminating
  nonterminating := f '' t.nonterminating

theorem OptTraces.map_nonterminating_nonempty {ε τ α τ'} (f: τ -> τ') (t: OptTraces ε τ α)
  : t.is_nonempty -> (t.map_nonterminating f).is_nonempty
  | Or.inl H => Or.inl H
  | Or.inr ⟨t, H⟩ => Or.inr ⟨f t, t, H, rfl⟩

def Traces.map_nonterminating {ε τ α τ'} (f: τ -> τ') (t: Traces ε τ α)
  : Traces ε τ' α where
  toOptTraces := t.toOptTraces.map_nonterminating f
  nonempty := t.toOptTraces.map_nonterminating_nonempty f t.nonempty

theorem OptTraces.map_nonterminating_id {α ε τ}
  : (t: OptTraces α ε τ) -> t.map_nonterminating id = t
  | ⟨tt, tl⟩ => by simp [map_nonterminating]

theorem Traces.map_nonterminating_id {ε τ α} (t: Traces α ε τ) 
  : t.map_nonterminating id = t
  := Traces.injOpt_mp _ _ t.toOptTraces.map_nonterminating_id

def OptTraces.map' {ε τ α β} (f: α -> β) (x: OptTraces ε τ α): OptTraces ε τ β where
  terminating b e := ∃a, x.terminating a e ∧ b = f a
  nonterminating := x.nonterminating

theorem OptTraces.map_nonempty' {ε τ α β} (f: α -> β) (t: OptTraces ε τ α)
  : t.is_nonempty -> (t.map' f).is_nonempty
  | Or.inl ⟨a, e, H⟩ => Or.inl ⟨f a, e, a, H, rfl⟩ 
  | Or.inr H => Or.inr H

def Traces.map' {ε τ α β} (f: α -> β) (x: Traces ε τ α): Traces ε τ β where
  toOptTraces := x.toOptTraces.map' f
  nonempty := x.toOptTraces.map_nonempty' f x.nonempty

def OptTraces.pure' {α} (ε τ) [One ε] (a: α): OptTraces ε τ α where
  terminating a' e := a' = a ∧ e = 1
  nonterminating _ := False

def OptTraces.pure_spec' {α} (ε τ) [One ε] (a: α): OptTraces.pure' ε τ a = (Trace.pure' ε τ a).toOptTraces
  := rfl

theorem OptTraces.pure_nonempty' (ε τ) [One ε] (a: α)
  : (OptTraces.pure' ε τ a).is_nonempty
  := Or.inl ⟨a, 1, rfl, rfl⟩

def Traces.pure' {α} (ε τ) [One ε] (a: α): Traces ε τ α where
  toOptTraces := OptTraces.pure' ε τ a
  nonempty := OptTraces.pure_nonempty' ε τ a

def Traces.pure_spec' {α} (ε τ) [One ε] (a: α): Traces.pure' ε τ a = (Trace.pure' ε τ a).toTraces
  := rfl

def OptTraces.bind' {ε τ α β} [Mul ε] [One ε] [SMul ε τ] (x: OptTraces ε τ α) (f: α -> OptTraces ε τ β)
  : OptTraces ε τ β where
  terminating := λb e'' => ∃a e e', x.terminating a e ∧ (f a).terminating b e' ∧ e'' = e * e'
  nonterminating := λt' => 
    x.nonterminating t' ∨ 
    ∃a e t, x.terminating a e ∧ (f a).nonterminating t ∧ t' = e • t

theorem OptTraces.bind_nonempty {ε τ α β} [Mul ε] [One ε] [SMul ε τ] (x: OptTraces ε τ α) (f: α -> OptTraces ε τ β)
  (Hx: x.is_nonempty)
  (Hf: ∀a, (f a).is_nonempty)
  : (x.bind' f).is_nonempty :=
  match Hx with
  | Or.inl ⟨a, e, Hae⟩ => match (Hf a) with
    | Or.inl ⟨b, e', H⟩ => Or.inl ⟨b, e * e', a, e, e', Hae, H, rfl⟩ 
    | Or.inr ⟨t, H⟩ => Or.inr ⟨e • t, Or.inr ⟨a, e, t, Hae, H, rfl⟩⟩  
  | Or.inr ⟨t, H⟩ => Or.inr ⟨t, Or.inl H⟩

def Traces.bind' {ε τ α β} [Mul ε] [One ε] [SMul ε τ] (x: Traces ε τ α) (f: α -> Traces ε τ β)
  : Traces ε τ β where
  toOptTraces := OptTraces.bind' x.toOptTraces (λa => (f a).toOptTraces)
  nonempty := OptTraces.bind_nonempty 
    x.toOptTraces 
    (λa => (f a).toOptTraces)
    x.nonempty
    (λa => (f a).nonempty)

instance OptTraces.instMonad {ε τ} [Mul ε] [One ε] [SMul ε τ]: Monad (OptTraces ε τ) where
  pure := OptTraces.pure' _ _
  bind := OptTraces.bind' --TODO: why does stuff fail to infer when bind is defined inline

instance Traces.instMonad {ε τ} [Mul ε] [One ε] [SMul ε τ]: Monad (Traces ε τ) where
  pure := Traces.pure' _ _
  bind := Traces.bind'

instance OptTraces.instLawfulMonad {ε τ} [M: Monoid ε] [A: MulAction ε τ]: LawfulMonad (OptTraces ε τ) :=
  LawfulMonad.mk' (OptTraces ε τ) 
    (λ⟨xt, xl⟩ => by
      apply OptTraces.injEq_mp
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
      apply OptTraces.injEq_mp
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
    (λ⟨xt, xl⟩ f g => by
      apply OptTraces.injEq_mp
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

instance Traces.instLawfulMonad {ε τ} [M: Monoid ε] [A: MulAction ε τ]: LawfulMonad (Traces ε τ) :=
  LawfulMonad.mk' (Traces ε τ) 
    (λ_ => Traces.injOpt_mp _ _ (OptTraces.instLawfulMonad.id_map _)) 
    (λ_ _ => Traces.injOpt_mp _ _ (OptTraces.instLawfulMonad.pure_bind _ _))
    (λ_ _ _ => Traces.injOpt_mp _ _ (OptTraces.instLawfulMonad.bind_assoc _ _ _))