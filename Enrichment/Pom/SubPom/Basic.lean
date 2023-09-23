import Mathlib.Data.Set.Finite

import Enrichment.Pom.Basic
import Enrichment.Pom.Iso

structure SubPom {L} (α: Pom L): Type where
  contains: Set α
  
theorem SubPom.ext {L} {α: Pom L} {ρ σ: SubPom α} (H: ρ.contains = σ.contains): ρ = σ
  := by rw [SubPom.mk.injEq]; exact H
  
structure FSubPom {L} (α: Pom L) extends SubPom α where
  finite: Finite contains

theorem FSubPom.ext {L} {α: Pom L} {ρ σ: FSubPom α} (H: ρ.toSubPom = σ.toSubPom): ρ = σ
  := by rw [FSubPom.mk.injEq]; exact H
theorem FSubPom.ext' {L} {α: Pom L} {ρ σ: FSubPom α} (H: ρ.contains = σ.contains): ρ = σ
  := FSubPom.ext (SubPom.ext H)

def SubPom.univ {L} (α: Pom L): SubPom α := ⟨ Set.univ ⟩
def SubPom.empty {L} (α: Pom L): SubPom α := ⟨ ∅ ⟩ 
def SubPom.union {L} {α: Pom L} (ρ σ: SubPom α): SubPom α := 
   ⟨ ρ.contains ∪ σ.contains ⟩
def SubPom.inter {L} {α: Pom L} (ρ σ: SubPom α): SubPom α
  := ⟨ ρ.contains ∩ σ.contains ⟩ 
def SubPom.complement {L} {α: Pom L} (ρ: SubPom α): SubPom α 
  := ⟨ ρ.containsᶜ ⟩
def SubPom.deletion {L} {α: Pom L} (ρ σ: SubPom α): SubPom α
  := ⟨ ρ.contains ∩ σ.containsᶜ ⟩  

def FSubPom.univ {L} (α: FPom L): FSubPom α.toPom 
  := ⟨ SubPom.univ α, @Subtype.finite _ α.finite _ ⟩ 
def FSubPom.empty {L} (α: Pom L): FSubPom α
  := ⟨ SubPom.empty α, @Finite.intro _ 0 ⟨λ., λ., λ., λ.⟩ ⟩ 
def FSubPom.union {L} {α: Pom L} (ρ σ: FSubPom α): FSubPom α :=
  ⟨ ρ.toSubPom.union σ.toSubPom, 
    @Finite.Set.finite_union _ ρ.contains σ.contains ρ.finite σ.finite ⟩  
def FSubPom.inter_left {L} {α: Pom L} (ρ: FSubPom α) (σ: SubPom α): FSubPom α :=
  ⟨ ρ.toSubPom.inter σ, 
    @Finite.Set.finite_inter_of_left _ ρ.contains σ.contains ρ.finite ⟩ 
def FSubPom.inter_right {L} {α: Pom L} (ρ: SubPom α) (σ: FSubPom α): FSubPom α :=
  ⟨ ρ.inter σ.toSubPom, 
    @Finite.Set.finite_inter_of_right _ ρ.contains σ.contains σ.finite ⟩ 
def FSubPom.inter {L} {α: Pom L} (ρ σ: FSubPom α): FSubPom α :=
  ⟨ ρ.toSubPom.inter σ.toSubPom, 
    @Finite.Set.finite_inter_of_left _ ρ.contains σ.contains ρ.finite ⟩  

theorem SubPom.inter_comm {L} {α: Pom L} (ρ σ: SubPom α)
  : ρ.inter σ = σ.inter ρ
  := by simp [inter, Set.inter_comm]
theorem SubPom.inter_assoc {L} {α: Pom L} (ρ σ τ: SubPom α)
  : (ρ.inter σ).inter τ = ρ.inter (σ.inter τ)
  := by simp [inter, Set.inter_assoc]
theorem SubPom.inter_idem {L} {α: Pom L} (ρ: SubPom α)
  : ρ.inter ρ = ρ
  := by simp [inter]
theorem SubPom.inter_univ {L} {α: Pom L} (ρ: SubPom α)
  : ρ.inter (univ α) = ρ
  := by simp [inter, univ]
theorem SubPom.univ_inter {L} {α: Pom L} (ρ: SubPom α)
  : (univ α).inter ρ = ρ
  := by simp [inter, univ]

theorem FSubPom.inter_comm {L} {α: Pom L} (ρ σ: FSubPom α)
  : ρ.inter σ = σ.inter ρ
  := FSubPom.ext (SubPom.inter_comm ρ.toSubPom σ.toSubPom)
theorem FSubPom.inter_assoc {L} {α: Pom L} (ρ σ τ: FSubPom α)
  : (ρ.inter σ).inter τ = ρ.inter (σ.inter τ)
  := FSubPom.ext (SubPom.inter_assoc ρ.toSubPom σ.toSubPom τ.toSubPom)
theorem FSubPom.inter_idem {L} {α: Pom L} (ρ: FSubPom α)
  : ρ.inter ρ = ρ
  := FSubPom.ext (SubPom.inter_idem ρ.toSubPom)
theorem FSubPom.inter_univ {L} {α: Pom L} (ρ: FSubPom α)
  : ρ.inter_left (SubPom.univ α) = ρ
  := FSubPom.ext (SubPom.inter_univ ρ.toSubPom)
theorem FSubPom.univ_inter {L} {α: Pom L} (ρ: FSubPom α)
  : FSubPom.inter_right (SubPom.univ α) ρ = ρ
  := FSubPom.ext (SubPom.univ_inter ρ.toSubPom)

theorem SubPom.union_comm {L} {α: Pom L} (ρ σ: SubPom α)
  : ρ.union σ = σ.union ρ
  := by simp [union, Set.union_comm]

theorem FSubPom.union_comm {L} {α: Pom L} (ρ σ: FSubPom α)
  : ρ.union σ = σ.union ρ
  := FSubPom.ext (SubPom.union_comm ρ.toSubPom σ.toSubPom)

def SubPom.seq {L} {A B: Pom L} (SA: SubPom A) (SB: SubPom B)
  : SubPom (A.seq B)
  := ⟨ Sum.elim SA.contains SB.contains ⟩

def SubPom.par {L} {A B: Pom L} (SA: SubPom A) (SB: SubPom B)
  : SubPom (A.par B)
  := ⟨ Sum.elim SA.contains SB.contains ⟩

def SubPom.carrier {L} {α: Pom L} (σ: SubPom α): Type
  := ↑σ.contains
def SubPom.order {L} {α: Pom L} (σ: SubPom α): PartialOrder σ.carrier
  := @Subtype.partialOrder α.carrier α.order σ.contains
def SubPom.action {L} {α: Pom L} (σ: SubPom α) (p: σ.carrier): L
  := α.action p.val
def SubPom.toPom {L} {α: Pom L} (σ: SubPom α): Pom L where
  carrier := σ.carrier
  order := σ.order
  action := σ.action

def FSubPom.carrier {L} {α: Pom L} (σ: FSubPom α): Type
  := σ.toSubPom.carrier
def FSubPom.order {L} {α: Pom L} (σ: FSubPom α): PartialOrder σ.carrier
  := σ.toSubPom.order
def FSubPom.action {L} {α: Pom L} (σ: FSubPom α): σ.carrier -> L
  := σ.toSubPom.action
def FSubPom.toPom {L} {α: Pom L} (σ: FSubPom α): Pom L
  := σ.toSubPom.toPom

instance {L} {α: Pom L}: CoeOut (SubPom α) (Pom L) where
  coe := SubPom.toPom
instance {L} {α: Pom L}: CoeOut (SubPom α) (Type) where
  coe := SubPom.carrier


instance {L} {α: Pom L}: Coe (FSubPom α) (SubPom α) where
  coe := FSubPom.toSubPom
instance {L} {α: Pom L}: CoeOut (FSubPom α) (Pom L) where
  coe := FSubPom.toPom
instance {L} {α: Pom L}: CoeOut (FSubPom α) (Type) where
  coe := FSubPom.carrier

def Pom.pred {L} (α: Pom L) (p: α.carrier): SubPom α
  := ⟨ λ x => α.order.le x p ⟩

theorem Pom.pred_def {L} {α: Pom L} (p e: α.carrier)
  : (e ∈ (α.pred p).contains) ↔ (α.order.le e p)
  := by rfl

theorem Pom.sub_pred_def {L} {α: Pom L} {ρ: SubPom α} (p e: ρ.carrier)
  : (e ∈ (ρ.toPom.pred p).contains) ↔ (α.order.le e.val p.val)
  := by rfl

def SubPom.pred {L} {α: Pom L} (ρ: SubPom α) (p: ρ.carrier) 
  := ρ.inter (α.pred p.val)

theorem SubPom.carrier.pred_def {L} {α: Pom L} {ρ: SubPom α} (p e: ρ.carrier)
  : (e.val ∈ (ρ.pred p).contains) ↔ (α.order.le e.val p.val)
  := ⟨
    λ⟨_, H⟩ => H,
    λH => ⟨e.property, H⟩
  ⟩

theorem SubPom.carrier.pred_def' {L} {α: Pom L} {ρ: SubPom α} (p e: ρ.carrier)
  : (e.val ∈ (ρ.pred p).contains) ↔ (e.val ∈ ρ.contains ∧ α.order.le e.val p.val)
  := by rfl

theorem SubPom.pred_char {L} {α: Pom L} {ρ: SubPom α} {p e: ρ.carrier}
  (H: e.val ∈ (ρ.pred p).contains): α.order.le e.val p.val
  := (p.pred_def e).mp H

def SubPom.happens {L} {α: Pom L} (ρ: SubPom α): SubPom α
  := ⟨ λe => ∃p: ρ.contains e, Finite (ρ.pred ⟨e, p⟩) ⟩ 
def SubPom.never {L} {α: Pom L} (ρ: SubPom α): SubPom α
  := ⟨ λe => ∃p: ρ.contains e, Finite (ρ.pred ⟨e, p⟩) ⟩
def SubPom.truncation {L} {α: Pom L} (ρ: SubPom α)
  := ρ.inter ρ.happens
def SubPom.t_inter {L} {α: Pom L} (ρ σ: SubPom α)
  := ρ.truncation.inter σ.truncation

def Pom.pred_carrier {L} (α: Pom L) (p: α.carrier):
  α.pred p = (SubPom.univ α).pred ⟨p, True.intro⟩
  := by simp [SubPom.pred, SubPom.inter, SubPom.univ]

def PomIso.pred {L} {α β: Pom L} (φ: PomIso α β) (p: α.carrier):
  PomIso (α.pred p) (β.pred (φ.toFun p)).toPom
  := {
    toFun := λ⟨e, He⟩ => ⟨φ.toFun e, φ.map_rel_iff.mpr He⟩,
    invFun := λ⟨e, He⟩ => ⟨
      φ.invFun e, by
        have He': e = φ.toFun (φ.invFun e) := by simp;
        rw [He'] at He;
        exact φ.map_rel_iff.mp He;
      ⟩,
    left_inv := λ⟨e, _⟩ => Subtype.eq (φ.left_inv e),
    right_inv := λ⟨e, _⟩ => Subtype.eq (φ.right_inv e),
    map_rel_iff' := λ{a b} => by
      cases a; cases b;
      exact φ.map_rel_iff',
    action_eq := λ{a} => by cases a; exact φ.action_eq
  }

theorem PomIso.pred_infinite_iff {L} {α β: Pom L} (φ: PomIso α β) (p: α.carrier):
  Infinite (α.pred p) ↔ Infinite (β.pred (φ.toFun p))
  := (φ.pred p).infinite_iff

theorem PomIso.pred_infinite_iff' {L} {α β: Pom L} (φ: PomIso α β) 
  (p: β.carrier):
  Infinite (α.pred (φ.invFun p)) ↔ Infinite (β.pred p)
  := by rw [
      pred_infinite_iff φ,
      φ.right_inv
    ]

theorem PomIso.pred_empty_iff {L} {α β: Pom L} (φ: PomIso α β) (p: α.carrier):
  IsEmpty (α.pred p) ↔ IsEmpty (β.pred (φ.toFun p))
  := (φ.pred p).empty_iff

def SubPom.pred_iso {L} {α: Pom L} (ρ: SubPom α) (p: ρ.carrier)
  : PomIso (ρ.toPom.pred p).toPom (ρ.pred p).toPom
  := {
    toFun := λ⟨e, He⟩ => ⟨e.val, ⟨e.property, He⟩⟩,
    invFun := λ⟨e, He⟩ => ⟨⟨e, He.left⟩, He.right⟩,
    left_inv := λ⟨⟨_, _⟩, _⟩ => rfl,
    right_inv := λ⟨_, _, _⟩ => rfl,
    map_rel_iff' := λ{a b} => by rfl,
    action_eq := λ{a} => rfl 
  }

def PomIso.pred_sub {L} {α: Pom L} {ρ σ: SubPom α} 
  (φ: PomIso ρ.toPom σ.toPom) (p: ρ.carrier):
  PomIso (ρ.pred p).toPom (σ.pred (φ.toFun p)).toPom
  := PomIso.trans (ρ.pred_iso _).symm (PomIso.trans (φ.pred _) (σ.pred_iso _))

theorem PomIso.pred_sub_infinite_iff {L} {α: Pom L} {ρ σ: SubPom α} 
  (φ: PomIso ρ.toPom σ.toPom) (p: ρ.carrier):
  Infinite (ρ.pred p) ↔ Infinite (σ.pred (φ.toFun p))
  := (φ.pred_sub p).infinite_iff

theorem PomIso.pred_sub_empty_iff {L} {α: Pom L} {ρ σ: SubPom α} 
  (φ: PomIso ρ.toPom σ.toPom) (p: ρ.carrier):
  IsEmpty (ρ.pred p) ↔ IsEmpty (σ.pred (φ.toFun p))
  := (φ.pred_sub p).empty_iff

def PomIso.pred_inv {L} {α β: Pom L} (φ: PomIso α β) (p: β.carrier):
  PomIso (α.pred (φ.invFun p)) (β.pred p).toPom
  :=
    have H: φ.toFun (φ.invFun p) = p := by simp; 
    have H' := φ.pred (φ.invFun p);
    by {
      rw [H] at H';
      exact H ▸ H' 
    }

def SubPom.univ_pred_pred_univ {L} (α: Pom L) (p)
  : (univ α).pred p = α.pred p.val
  := univ_inter (α.pred p.val)

theorem Pom.univ_carrier_equiv {L} (α: Pom L)
  : α.carrier ≃ (SubPom.univ α).carrier
  := ⟨
    λa => ⟨a, True.intro⟩,
    λ⟨a, True.intro⟩ => a,
    λ_ => rfl,
    λ⟨_, _⟩ => rfl
  ⟩

def SubPom.iso_univ {L} (α: Pom L): PomIso (SubPom.univ α) α
  := {
    toFun := λ⟨e, _⟩ => e,
    invFun := λe => ⟨e, True.intro⟩,
    left_inv := λ_ => rfl,
    right_inv := λ_ => rfl,
    map_rel_iff' := Iff.rfl,
    action_eq := rfl
  }


def SubPom.flatten {L} {α: Pom L} {ρ: SubPom α} 
  (σ: SubPom ρ.toPom)
  : SubPom α
  := ⟨λe => (p: ρ.contains e) -> σ.contains ⟨e, p⟩⟩

theorem SubPom.order_char {L} {α: Pom L} {ρ: SubPom α}
  (a b: ρ.carrier)
  : ρ.order.le a b ↔ α.order.le a.val b.val
  := by rfl

theorem SubPom.order_char' {L} {α: Pom L} {ρ: SubPom α}
  (a b: ρ.carrier)
  : ρ.toPom.order.le a b ↔ α.order.le a.val b.val
  := by rfl

theorem SubPom.order_mk_char {L} {α: Pom L} {ρ: SubPom α}
  (a b: α.carrier)
  (Ha Hb)
  : ρ.order.le ⟨a, Ha⟩ ⟨b, Hb⟩ ↔ α.order.le a b
  := by rfl

theorem SubPom.order_mk_char' {L} {α: Pom L} {ρ: SubPom α}
  (a b: α.carrier)
  (Ha Hb)
  : ρ.toPom.order.le ⟨a, Ha⟩ ⟨b, Hb⟩ ↔ α.order.le a b
  := by rfl