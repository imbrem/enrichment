import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Set.Image

import Enrichment.TraceMonad.Basic

structure OptFTraces (ε: Type u1) (τ: Type u2) (α: Type u3): Type (max u1 (max u2 u3)) where
  terminating: α -> ε -> Prop
  nonterminating: τ -> Prop

def Trace.toOptFTraces {ε τ α}: Trace ε τ α -> OptFTraces ε τ α
  | terminating a e => { terminating := λa' e' => a' = a ∧ e' = e, nonterminating := λ_ => False }
  | nonterminating t => { terminating := λ_ _ => False, nonterminating := λt' => t = t' }

--TODO: OptFTraces.{before, after}

def OptFTraces.is_nonempty {ε τ α} (t: OptFTraces ε τ α) := (∃a e, t.terminating a e) ∨ (∃e, t.nonterminating e)

class FTraces (ε τ α) extends OptFTraces ε τ α where
  nonempty: (∃a e, terminating a e) ∨ (∃e, nonterminating e)

def Trace.toOptFTraces_is_nonempty {ε τ α}: (t: Trace ε τ α) -> t.toOptFTraces.is_nonempty
  | terminating a e => Or.inl ⟨a, e, rfl, rfl⟩ 
  | nonterminating t => Or.inr ⟨t, rfl⟩

def Trace.toFTraces {ε τ α} (t: Trace ε τ α): FTraces ε τ α where
  toOptFTraces := t.toOptFTraces
  nonempty := t.toOptFTraces_is_nonempty  

--TODO: FTraces.{before, after}

theorem OptFTraces.injEq' {ε τ α} (t t': OptFTraces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating ↔ t = t'
  := by cases t; cases t'; simp

theorem OptFTraces.injEq_mp {ε τ α} (t t': OptFTraces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating -> t = t'
  := (t.injEq' t').mp

theorem FTraces.injOpt_mp {ε τ α} (t t': FTraces ε τ α)
  : t.toOptFTraces = t'.toOptFTraces -> t = t'
  := λH => by 
      cases t; cases t'; 
      let ⟨_, _⟩ := (OptFTraces.injEq' _ _).mpr H; 
      simp only at *; 
      simp [*]

--TODO: there must be a better way...
theorem FTraces.injOpt {ε τ α} (t t': FTraces ε τ α)
  : t.toOptFTraces = t'.toOptFTraces ↔ t = t'
  := ⟨
    t.injOpt_mp t',
    λH => by rw [H]
  ⟩

theorem FTraces.injEq' {ε τ α} (t t': FTraces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating ↔ t = t'
  := Iff.trans (OptFTraces.injEq' t.toOptFTraces t'.toOptFTraces) (FTraces.injOpt t t')

theorem FTraces.injEq_mp {ε τ α} (t t': FTraces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating -> t = t'
  := (FTraces.injEq' t t').mp

instance {ε τ α}: PartialOrder (OptFTraces ε τ α) where
  le t t' := t.terminating ≤ t'.terminating ∧ t.nonterminating ≤ t'.nonterminating 
  le_refl t := ⟨le_refl _, le_refl _⟩
  le_trans a b c Hab Hbc := ⟨le_trans Hab.1 Hbc.1, le_trans Hab.2 Hbc.2⟩ 
  le_antisymm t t' H H' := by
    have e1 := le_antisymm H.1 H'.1;
    have e2 := le_antisymm H.2 H'.2;
    cases t; cases t';
    simp only [] at e1 e2
    simp only [*]

def OptFTraces.map_terminating {ε τ α ε'} (f: ε -> ε') (t: OptFTraces ε τ α)
  : OptFTraces ε' τ α where
  terminating a := f '' (t.terminating a)
  nonterminating := t.nonterminating

theorem OptFTraces.map_terminating_nonempty {ε τ α ε'} (f: ε -> ε') (t: OptFTraces ε τ α)
  : t.is_nonempty -> (t.map_terminating f).is_nonempty
  | Or.inl ⟨a, e, H⟩ => Or.inl ⟨a, f e, e, H, rfl⟩
  | Or.inr H => Or.inr H

def FTraces.map_terminating {ε τ α ε'} (f: ε -> ε') (t: FTraces ε τ α)
  : FTraces ε' τ α where
  toOptFTraces := t.toOptFTraces.map_terminating f
  nonempty := t.toOptFTraces.map_terminating_nonempty f t.nonempty

theorem OptFTraces.map_terminating_id {ε τ α}
  : (t: OptFTraces α ε τ) -> t.map_terminating id = t
  | ⟨tt, tl⟩ => by simp [map_terminating]

theorem FTraces.map_terminating_id {ε τ α} (t: FTraces α ε τ) 
  : t.map_terminating id = t
  := FTraces.injOpt_mp _ _ t.toOptFTraces.map_terminating_id

def OptFTraces.map_nonterminating {ε τ α τ'} (f: τ -> τ') (t: OptFTraces ε τ α)
  : OptFTraces ε τ' α where
  terminating := t.terminating
  nonterminating := f '' t.nonterminating

theorem OptFTraces.map_nonterminating_nonempty {ε τ α τ'} (f: τ -> τ') (t: OptFTraces ε τ α)
  : t.is_nonempty -> (t.map_nonterminating f).is_nonempty
  | Or.inl H => Or.inl H
  | Or.inr ⟨t, H⟩ => Or.inr ⟨f t, t, H, rfl⟩

def FTraces.map_nonterminating {ε τ α τ'} (f: τ -> τ') (t: FTraces ε τ α)
  : FTraces ε τ' α where
  toOptFTraces := t.toOptFTraces.map_nonterminating f
  nonempty := t.toOptFTraces.map_nonterminating_nonempty f t.nonempty

theorem OptFTraces.map_nonterminating_id {α ε τ}
  : (t: OptFTraces α ε τ) -> t.map_nonterminating id = t
  | ⟨tt, tl⟩ => by simp [map_nonterminating]

theorem FTraces.map_nonterminating_id {ε τ α} (t: FTraces α ε τ) 
  : t.map_nonterminating id = t
  := FTraces.injOpt_mp _ _ t.toOptFTraces.map_nonterminating_id

def OptFTraces.map' {ε τ α β} (f: α -> β) (x: OptFTraces ε τ α): OptFTraces ε τ β where
  terminating b e := ∃a, x.terminating a e ∧ b = f a
  nonterminating := x.nonterminating

theorem OptFTraces.map_nonempty' {ε τ α β} (f: α -> β) (t: OptFTraces ε τ α)
  : t.is_nonempty -> (t.map' f).is_nonempty
  | Or.inl ⟨a, e, H⟩ => Or.inl ⟨f a, e, a, H, rfl⟩ 
  | Or.inr H => Or.inr H

def FTraces.map' {ε τ α β} (f: α -> β) (x: FTraces ε τ α): FTraces ε τ β where
  toOptFTraces := x.toOptFTraces.map' f
  nonempty := x.toOptFTraces.map_nonempty' f x.nonempty

def OptFTraces.pure' {α} (ε τ) [One ε] (a: α): OptFTraces ε τ α where
  terminating a' e := a' = a ∧ e = 1
  nonterminating _ := False

def OptFTraces.pure_spec' {α} (ε τ) [One ε] (a: α): OptFTraces.pure' ε τ a = (Trace.pure' ε τ a).toOptFTraces
  := rfl

theorem OptFTraces.pure_nonempty' (ε τ) [One ε] (a: α)
  : (OptFTraces.pure' ε τ a).is_nonempty
  := Or.inl ⟨a, 1, rfl, rfl⟩

def FTraces.pure' {α} (ε τ) [One ε] (a: α): FTraces ε τ α where
  toOptFTraces := OptFTraces.pure' ε τ a
  nonempty := OptFTraces.pure_nonempty' ε τ a

def FTraces.pure_spec' {α} (ε τ) [One ε] (a: α): FTraces.pure' ε τ a = (Trace.pure' ε τ a).toFTraces
  := rfl

def OptFTraces.bind' {ε τ α β} [Mul ε] [One ε] [SMul ε τ] (x: OptFTraces ε τ α) (f: α -> OptFTraces ε τ β)
  : OptFTraces ε τ β where
  terminating := λb e'' => ∃a e e', x.terminating a e ∧ (f a).terminating b e' ∧ e'' = e * e'
  nonterminating := λt' => 
    x.nonterminating t' ∨ 
    ∃a e t, x.terminating a e ∧ (f a).nonterminating t ∧ t' = e • t

theorem OptFTraces.bind_nonempty {ε τ α β} [Mul ε] [One ε] [SMul ε τ] (x: OptFTraces ε τ α) (f: α -> OptFTraces ε τ β)
  (Hx: x.is_nonempty)
  (Hf: ∀a, (f a).is_nonempty)
  : (x.bind' f).is_nonempty :=
  match Hx with
  | Or.inl ⟨a, e, Hae⟩ => match (Hf a) with
    | Or.inl ⟨b, e', H⟩ => Or.inl ⟨b, e * e', a, e, e', Hae, H, rfl⟩ 
    | Or.inr ⟨t, H⟩ => Or.inr ⟨e • t, Or.inr ⟨a, e, t, Hae, H, rfl⟩⟩  
  | Or.inr ⟨t, H⟩ => Or.inr ⟨t, Or.inl H⟩

def FTraces.bind' {ε τ α β} [Mul ε] [One ε] [SMul ε τ] (x: FTraces ε τ α) (f: α -> FTraces ε τ β)
  : FTraces ε τ β where
  toOptFTraces := OptFTraces.bind' x.toOptFTraces (λa => (f a).toOptFTraces)
  nonempty := OptFTraces.bind_nonempty 
    x.toOptFTraces 
    (λa => (f a).toOptFTraces)
    x.nonempty
    (λa => (f a).nonempty)

instance OptFTraces.instMonad {ε τ} [Mul ε] [One ε] [SMul ε τ]: Monad (OptFTraces ε τ) where
  pure := OptFTraces.pure' _ _
  bind := OptFTraces.bind' --TODO: why does stuff fail to infer when bind is defined inline

instance FTraces.instMonad {ε τ} [Mul ε] [One ε] [SMul ε τ]: Monad (FTraces ε τ) where
  pure := FTraces.pure' _ _
  bind := FTraces.bind'

instance OptFTraces.instLawfulMonad {ε τ} [M: Monoid ε] [A: MulAction ε τ]: LawfulMonad (OptFTraces ε τ) :=
  LawfulMonad.mk' (OptFTraces ε τ) 
    (λ⟨xt, xl⟩ => by
      apply OptFTraces.injEq_mp
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
      apply OptFTraces.injEq_mp
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
      apply OptFTraces.injEq_mp
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

instance FTraces.instLawfulMonad {ε τ} [M: Monoid ε] [A: MulAction ε τ]: LawfulMonad (FTraces ε τ) :=
  LawfulMonad.mk' (FTraces ε τ) 
    (λ_ => FTraces.injOpt_mp _ _ (OptFTraces.instLawfulMonad.id_map _)) 
    (λ_ _ => FTraces.injOpt_mp _ _ (OptFTraces.instLawfulMonad.pure_bind _ _))
    (λ_ _ _ => FTraces.injOpt_mp _ _ (OptFTraces.instLawfulMonad.bind_assoc _ _ _))