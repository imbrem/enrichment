import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Set.Image

structure OptTraces (ε: Type u1) (τ: Type u2) (α: Type u3): Type (max u1 (max u2 u3)) where
  terminating: α -> ε -> Prop
  nonterminating: τ -> Prop

def OptTraces.is_nonempty {ε τ α} (t: OptTraces ε τ α) := (∃a e, t.terminating a e) ∨ (∃e, t.nonterminating e)

theorem OptTraces.mk.injEq' {ε τ α} (t t': OptTraces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating ↔ t = t'
  := by cases t; cases t'; simp

theorem OptTraces.mk.injEq_mp {ε τ α} (t t': OptTraces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating -> t = t'
  := by cases t; cases t'; simp

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

def Terminates: Type := Empty

instance {ε} [Monoid ε]: MulAction ε Terminates where
  smul := λ_ t => match t with .
  one_smul := λt => match t with .
  mul_smul := λ_ _ t => match t with .

def OptTraces.map_terminating {ε τ α ε'} (f: ε -> ε') (t: OptTraces ε τ α)
  : OptTraces ε' τ α where
  terminating a := f '' (t.terminating a)
  nonterminating := t.nonterminating

theorem OptTraces.map_terminating_nonempty {ε τ α ε'} (f: ε -> ε') (t: OptTraces ε τ α)
  : t.is_nonempty -> (t.map_terminating f).is_nonempty
  | Or.inl ⟨a, e, H⟩ => Or.inl ⟨a, f e, e, H, rfl⟩
  | Or.inr H => Or.inr H

theorem OptTraces.map_terminating_id {ε τ α}
  : (t: OptTraces α ε τ) -> t.map_terminating id = t
  | ⟨tt, tl⟩ => by simp [map_terminating]

def OptTraces.map_nonterminating {ε τ α τ'} (f: τ -> τ') (t: OptTraces ε τ α)
  : OptTraces ε τ' α where
  terminating := t.terminating
  nonterminating := f '' t.nonterminating

theorem OptTraces.map_nonterminating_nonempty {ε τ α τ'} (f: τ -> τ') (t: OptTraces ε τ α)
  : t.is_nonempty -> (t.map_nonterminating f).is_nonempty
  | Or.inl H => Or.inl H
  | Or.inr ⟨t, H⟩ => Or.inr ⟨f t, t, H, rfl⟩

theorem OptTraces.map_nonterminating_id {α ε τ}
  : (t: OptTraces α ε τ) -> t.map_nonterminating id = t
  | ⟨tt, tl⟩ => by simp [map_nonterminating]

def OptTraces.map' {ε τ α β} (f: α -> β) (x: OptTraces ε τ α): OptTraces ε τ β where
  terminating b e := ∃a, x.terminating a e ∧ b = f a
  nonterminating := x.nonterminating

theorem OptTraces.map_nonempty {ε τ α β} (f: α -> β) (t: OptTraces ε τ α)
  : t.is_nonempty -> (t.map' f).is_nonempty
  | Or.inl ⟨a, e, H⟩ => Or.inl ⟨f a, e, a, H, rfl⟩ 
  | Or.inr H => Or.inr H

def OptTraces.pure' {α} (ε τ) [One ε] (a: α): OptTraces ε τ α where
  terminating a' e := a = a' ∧ e = 1
  nonterminating _ := False

theorem OptTraces.pure_nonempty' (ε τ) [One ε] (a: α)
  : (OptTraces.pure' ε τ a).is_nonempty
  := Or.inl ⟨a, 1, rfl, rfl⟩

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

instance {ε τ} [Mul ε] [One ε] [SMul ε τ]: Monad (OptTraces ε τ) where
  pure := OptTraces.pure' _ _
  bind := OptTraces.bind' --TODO: why does stuff fail to infer without this?

instance {ε τ} [M: Monoid ε] [A: MulAction ε τ]: LawfulMonad (OptTraces ε τ) :=
  LawfulMonad.mk' (OptTraces ε τ) 
    (λ⟨xt, xl⟩ => by
      apply OptTraces.mk.injEq_mp
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
      apply OptTraces.mk.injEq_mp
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
      apply OptTraces.mk.injEq_mp
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