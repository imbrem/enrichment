import Enrichment.Pom.Basic
import Enrichment.Pom.SubPom

class Ticked (L: Type) :=
  δ: L

def Pom.tick (L: Type) [Ticked L]: Pom L := {
  carrier := Unit,
  order := {
    le_antisymm := λa b _ _ => by cases a; cases b; rfl
  },
  action := λ_ => Ticked.δ
}

structure SubPomReduces {L} [Ticked L] {α: Pom L} (ρ σ: SubPom α): Prop where
  subset: σ.contains ⊆ ρ.contains
  infinite_or_tick: ∀p: ρ.contains,
    σ.contains p ∨
    Infinite (ρ.pred p) ∨
    α.action p = Ticked.δ
  infinite_preserved: ∀p: σ.carrier,
    Infinite (ρ.pred ⟨p.val, subset p.property⟩) -> Infinite (σ.pred p)
  infinite_shared: Infinite ρ -> Infinite σ
  empty_shared: IsEmpty σ -> IsEmpty ρ  

-- structure FSubPomReduces {L} [Ticked L] {α: Pom L} (ρ σ: FSubPom α): Prop where
--   subset: σ.contains ⊆ ρ.contains
--   empty_shared: IsEmpty σ -> IsEmpty ρ  

theorem SubPomReduces.infinite_iff {L} [Ticked L] {α: Pom L} {ρ σ: SubPom α}
  (S: SubPomReduces ρ σ)
  : Infinite ρ ↔ Infinite σ
  := ⟨
    S.infinite_shared, 
    λH => @Infinite.of_injective _ _ H
      (λ⟨e, H⟩ => ⟨e, S.subset H⟩)
      λ{a b} H => by cases a; cases b; cases H; rfl
  ⟩

theorem SubPomReduces.pred_infinite_iff {L} [Ticked L] {α: Pom L} 
  {ρ σ: SubPom α} (S: SubPomReduces ρ σ) (p: σ.carrier)
  : Infinite (ρ.pred ⟨p.val, S.subset p.property⟩) ↔ Infinite (σ.pred p)
  := ⟨
    S.infinite_preserved p, 
    λH => @Infinite.of_injective _ _ H
      (λ⟨e, H, H'⟩ => ⟨e, S.subset H, H'⟩)
      λ⟨_, _, _⟩ ⟨_, _, _⟩ H => by cases H; rfl
  ⟩

theorem SubPomReduces.pred_infinite_iff' {L} [Ticked L] {α: Pom L} 
  {ρ σ: SubPom α} (S: SubPomReduces ρ σ) (p: σ.carrier)
  : Infinite (ρ.toPom.pred ⟨p.val, S.subset p.property⟩) 
  ↔ Infinite (σ.toPom.pred p)
  := by
    rw [(SubPom.pred_iso _ _).infinite_iff]
    rw [(SubPom.pred_iso _ _).infinite_iff]
    exact S.pred_infinite_iff p

theorem SubPomReduces.empty_iff {L} [Ticked L] {α: Pom L} {ρ σ: SubPom α}
  (S: SubPomReduces ρ σ)
  : IsEmpty ρ ↔ IsEmpty σ
  := ⟨
    λH => IsEmpty.mk (λ⟨e, He⟩ => H.elim ⟨e, (S.subset He)⟩), 
    S.empty_shared
  ⟩

def PomReduces {L} [Ticked L] {α: Pom L} (ρ: SubPom α) := SubPomReduces (SubPom.univ α) ρ

def PomReduces.infinite_iff' {L} [Ticked L] {α: Pom L} {ρ: SubPom α}
  (P: PomReduces ρ)
  : Infinite ρ ↔ Infinite α
  := by 
    rw [
      <-@Set.infinite_univ_iff α, 
      <-Set.infinite_coe_iff,
      <-P.infinite_iff
    ]; rfl

def PomReduces.empty_iff' {L} [Ticked L] {α: Pom L} {ρ: SubPom α}
  (P: PomReduces ρ)
  : IsEmpty ρ ↔ IsEmpty α
  := ⟨
    λH => IsEmpty.mk (λe => (P.empty_shared H).elim ⟨e, True.intro⟩),
    λH => IsEmpty.mk (λe => H.elim e.val)
  ⟩

theorem SubPomReduces.refl {L} [Ticked L] {α: Pom L} (ρ: SubPom α):
  SubPomReduces ρ ρ
  := {
    subset := subset_rfl,
    infinite_or_tick := λ⟨_, H⟩ => Or.inl H,
    infinite_preserved := λ_ H => H,
    infinite_shared := λH => H,
    empty_shared := λH => H,
  }

theorem PomReduces.refl {L} [Ticked L] (α: Pom L): PomReduces (SubPom.univ α)
  := SubPomReduces.refl (SubPom.univ α)

theorem SubPomReduces.trans {L} [Ticked L] {α: Pom L} {ρ σ τ: SubPom α}
  (Hρσ: SubPomReduces ρ σ) (Hστ: SubPomReduces σ τ)
  : SubPomReduces ρ τ
  := {
    subset := subset_trans Hστ.subset Hρσ.subset,
    infinite_or_tick := λe => 
      match Hρσ.infinite_or_tick e with
      | Or.inl H => 
        match Hστ.infinite_or_tick ⟨e.val, H⟩ with
        | Or.inl H => Or.inl H
        | Or.inr (Or.inl I) => Or.inr (Or.inl (
          @Infinite.of_injective
          _ _ I
          (λ⟨e, ⟨Hc, Hp⟩ ⟩  => ⟨e, ⟨Hρσ.subset Hc, Hp⟩⟩)
          (λ⟨_, ⟨_, _⟩⟩ ⟨_, ⟨_, _⟩⟩ H => by cases H; rfl)
        ))
        | Or.inr (Or.inr H) => Or.inr (Or.inr H)
      | Or.inr H => Or.inr H,
    infinite_preserved := λe => 
      Hστ.infinite_preserved e ∘ Hρσ.infinite_preserved ⟨e.val, Hστ.subset e.property⟩,
    infinite_shared := Hστ.infinite_shared ∘ Hρσ.infinite_shared,
    empty_shared := Hρσ.empty_shared ∘ Hστ.empty_shared,
  }

theorem SubPomReduces.antisymm {L} [Ticked L] 
  {α: Pom L} {ρ σ: SubPom α}
  (H: SubPomReduces ρ σ) (H': SubPomReduces σ ρ)
  : ρ = σ
  := SubPom.ext (subset_antisymm H'.subset H.subset)

structure PomReduct {L} [Ticked L] (α: Pom L) :=
  shared: SubPom α
  is_reduct: PomReduces shared

instance {L} [Ticked L] {α: Pom L}: Coe (PomReduct α) (SubPom α) := {
  coe := PomReduct.shared
}

instance {L} [Ticked L] {α: Pom L}: CoeOut (PomReduct α) (Pom L) := {
  coe := λe => e.shared.toPom
}

def PomReduct.univ {L} [Ticked L] (α: Pom L): PomReduct α := {
  shared := SubPom.univ α
  is_reduct := PomReduces.refl α
}

def PomReduces.toReduct {L} [Ticked L] {α: Pom L} {ρ: SubPom α} 
  (P: PomReduces ρ):
  PomReduct α
  := {
    shared := ρ,
    is_reduct := P
  }

def PomReduct.refl {L} [Ticked L] (α: Pom L):
  PomReduct α
  := (PomReduces.refl α).toReduct

def SubPomReduces.sigma
  {L} [Ticked L]
  {N} [PartialOrder N]
  {F: N -> Pom L}
  (S: (n: N) -> SubPom (F n))
  (R: (n: N) -> SubPom (F n))
  (H: ∀(n: N), SubPomReduces (S n) (R n))
  : SubPomReduces (SubPom.sigma S) (SubPom.sigma R)
  := {
    subset := λ⟨n, e⟩ Hs => (H n).subset Hs,
    infinite_or_tick := λ⟨⟨n, e⟩, Hs⟩ => match (H n).infinite_or_tick ⟨e, Hs⟩ with
    | Or.inl Hi => Or.inl Hi
    | Or.inr (Or.inl Hi) => Or.inr (Or.inl (
      @Infinite.of_injective _ _ Hi 
        (λ⟨p, Hsp, Hep⟩  => ⟨⟨n, p⟩, Hsp, Sigma.Lex.right _ _ Hep⟩) 
        (λ⟨_, _, _⟩ ⟨_, _, _⟩ H => by cases H; rfl)
    ))
    | Or.inr (Or.inr Hi) => Or.inr (Or.inr Hi)
    ,
    infinite_preserved := sorry,
    infinite_shared := sorry,
    empty_shared := λHe =>
      have He := (SubPom.sigma_empty _).mp He;
      (SubPom.sigma_empty _).mpr (λn => (H n).empty_shared (He n))
  }

def PomReduces.sigma
  {L} [Ticked L]
  {N} [PartialOrder N]
  {F: N -> Pom L}
  (S: (n: N) -> SubPom (F n))
  (H: ∀(n: N), PomReduces (S n))
  : PomReduces (SubPom.sigma S)
  := SubPomReduces.sigma (λn => SubPom.univ (F n)) S H

def PomReduct.sigma
  {L} [Ticked L]
  {N} [PartialOrder N]
  {F: N -> Pom L}
  (P: ∀(n: N), PomReduct (F n))
  : PomReduct (Pom.sigma F)
  := {
    shared := SubPom.sigma (λn => (P n).shared),
    is_reduct := PomReduces.sigma _ (λn => (P n).is_reduct)
  }