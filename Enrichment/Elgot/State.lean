import Enrichment.Elgot.Monad

def destate {σ: Type u} {m: Type u -> Type v} {α β} (f: α -> StateT σ m β) (a: α × σ): m (β × σ)
  := f a.1 a.2
def destate_spec {σ m} {α β} (f: α -> StateT σ m β) (a s): destate f (a, s) = f a s := rfl
def destate_spec' {σ m} {α β} (f: α -> StateT σ m β) (a): destate f a = f a.1 a.2 := rfl

def restate {σ: Type u} {m: Type u -> Type v} {α β} (f: α × σ -> m (β × σ)): α -> StateT σ m β
  | a, s => f (a, s)
def restate_spec {σ: Type u} {m: Type u -> Type v} {α β} (f: α × σ -> m (β × σ)) (a s)
  : restate f a s = f (a, s) := rfl

def destate_restate {σ: Type u} {m: Type u -> Type v} {α β} (f: α × σ -> m (β × σ))
  : destate (restate f) = f
  := rfl
def restate_destate {σ: Type u} {m: Type u -> Type v} {α β} (f: α -> StateT σ m β)
  : restate (destate f) = f
  := rfl

def destate_kleisli {σ: Type u} {m: Type u -> Type v} {α β γ: Type u} [Monad m]
  (f: α -> StateT σ m β) (g: β -> StateT σ m γ):
  destate (f >=> g) = destate f >=> destate g
  := rfl
def restate_kleisli {σ: Type u} {m: Type u -> Type v} {α β γ: Type u} [Monad m]
  (f: α × σ -> m (β × σ)) (g: β × σ -> m (γ × σ)):
  restate (f >=> g) = restate f >=> restate g
  := rfl

def destate_inj {σ: Type u} {m: Type u -> Type v} {α β} (f g: α -> StateT σ m β) 
  (H: destate f = destate g): f = g 
  := by rw [<-restate_destate f, <-restate_destate g, H]
def restate_inj {σ: Type u} {m: Type u -> Type v} {α β} (f g: α × σ -> m (β × σ)) 
  (H: restate f = restate g): f = g 
  := by rw [<-destate_restate f, <-destate_restate g, H]

def dist_fn {σ β γ}: (β ⊕ γ) × σ -> (β × σ) ⊕ (γ × σ)
  | (Sum.inl b, s) => Sum.inl (b, s) 
  | (Sum.inr c, s) => Sum.inr (c, s)

def destate_sum {σ: Type u} {m: Type u -> Type v} {α β γ: Type u} [Monad m]
  (f: α -> StateT σ m γ) (g: β -> StateT σ m γ)
  : destate (Sum.elim f g) = (Sum.elim (destate f) (destate g)) ∘ dist_fn
  := by funext ⟨c, s⟩; cases c <;> rfl
def destate_sum' {σ: Type u} {m: Type u -> Type v} {α β γ δ: Type u} [Monad m] [LawfulMonad m]
  (f: α -> StateT σ m (γ ⊕ δ)) (g: β -> StateT σ m (γ ⊕ δ))
  : let e := Sum.elim (destate f >=> pure ∘ dist_fn) (destate g >=> pure ∘ dist_fn); 
  destate (Sum.elim f g) >=> pure ∘ dist_fn 
  = pure ∘ dist_fn >=> e
  := by funext ⟨c, s⟩; cases c <;> simp [destate, pure, Bind.kleisliRight, dist_fn]
def destate_sum_inr {σ: Type u} {m: Type u -> Type v} {α γ δ: Type u} [Monad m] [LawfulMonad m]
  (f: α -> StateT σ m (γ ⊕ δ))
  : let e := Sum.elim (destate f >=> pure ∘ dist_fn) (pure ∘ Sum.inr); 
  destate (Sum.elim f (pure ∘ Sum.inr)) >=> pure ∘ dist_fn 
  = pure ∘ dist_fn >=> e
  := by funext ⟨c, s⟩; cases c <;> simp [destate, pure, Bind.kleisliRight, dist_fn, StateT.pure]

instance stateDaggerMonad {σ} {m: Type u -> Type v} [Monad m] [d: DaggerMonad m]
  : DaggerMonad (StateT σ m)
  where
  dagger f := restate (d.dagger (destate f >=> (pure ∘ dist_fn)))

def destate_state_dagger {σ: Type u} {m: Type u -> Type v} [Monad m] [d: DaggerMonad m] {α β: Type u}
  (f: α -> StateT σ m (β ⊕ α))
  : destate (DaggerMonad.dagger f) = d.dagger (destate f >=> (pure ∘ dist_fn))
  := rfl

def kleisli_assoc {m: Type u -> Type v} [Monad m] [LawfulMonad m] {α β γ δ}
  (f: α -> m β) (g: β -> m γ) (h: γ -> m δ)
  : f >=> g >=> h = (f >=> g) >=> h
  := by funext a; unfold Bind.kleisliRight; rw [bind_assoc]

def kleisli_pure_comp {m: Type u -> Type v} [Monad m] [LawfulMonad m] {α β γ: Type u}
  (f: α -> m β) (g: β -> γ) (a)
  : (f >=> pure ∘ g) a = (g <$> f a)
  := by simp only [Bind.kleisliRight, <-bind_pure_comp]; rfl

def kleisli_comp_app {m: Type u -> Type v} [Monad m] {α β γ: Type u}
  (f: α -> m β) (g: β -> m γ) (a: α)
  : (f >=> g) a = f a >>= g
  := rfl

def kleisli_pure_comp' {m: Type u -> Type v} [Monad m] [LawfulMonad m] {α β γ: Type u}
  (f: α -> m β) (g: β -> γ)
  : (f >=> pure ∘ g) = (λa => g <$> f a)
  := by simp only [Bind.kleisliRight, <-bind_pure_comp]; rfl

def destate_inl_dist_fn {σ: Type u} {m: Type u -> Type v} {α β γ: Type u} [Monad m] [LawfulMonad m]
  (f: α -> StateT σ m β)
  : destate (f >=> pure ∘ @Sum.inl β γ) >=> pure ∘ dist_fn = destate f >=> pure ∘ Sum.inl
  := by 
    rw [
      destate_kleisli, 
      <-kleisli_assoc,
    ]
    apply congr rfl
    funext ⟨a, s⟩  
    simp [destate, pure, StateT.pure, Bind.kleisliRight, dist_fn]

def destate_inr_dist_fn {σ: Type u} {m: Type u -> Type v} {α β γ: Type u} [Monad m] [LawfulMonad m]
  (f: α -> StateT σ m γ)
  : destate (f >=> pure ∘ @Sum.inr β γ) >=> pure ∘ dist_fn = destate f >=> pure ∘ Sum.inr
  := by 
    rw [
      destate_kleisli, 
      <-kleisli_assoc,
    ]
    apply congr rfl
    funext ⟨a, s⟩  
    simp [destate, pure, StateT.pure, Bind.kleisliRight, dist_fn]

instance stateElgotMonad {σ} {m: Type u -> Type v} [Monad m] [LawfulMonad m] [e: ElgotMonad m]
  : ElgotMonad (StateT σ m)
  where
  fixpoint f := by 
    apply destate_inj
    rw [destate_state_dagger, destate_kleisli, <-e.fixpoint]
    rw [<-kleisli_assoc]
    apply congr rfl
    funext ⟨c, s⟩ 
    cases c 
    <;> simp only [Bind.kleisliRight, Function.comp_apply, pure_bind] 
    <;> rfl
  naturality f g := by
    apply destate_inj
    rw [
      destate_kleisli, 
      destate_state_dagger, 
      destate_state_dagger,
      destate_kleisli,
      <-kleisli_assoc,
      destate_sum_inr,
      destate_inl_dist_fn,
      <-e.naturality,
      kleisli_assoc
    ]
  codiagonal f := by
    apply destate_inj
    rw [
      destate_state_dagger,
      destate_state_dagger,
      destate_state_dagger,
      <-e.naturality,
      <-e.codiagonal
    ]
    apply congr rfl
    funext ⟨a, s⟩
    rw [
      kleisli_pure_comp,
      <-kleisli_assoc,
      kleisli_comp_app,
      kleisli_pure_comp,
      destate_kleisli,
      kleisli_comp_app,
      map_eq_pure_bind,
      map_eq_pure_bind,
      bind_assoc,
      bind_assoc,
    ]
    apply congr rfl
    simp only [pure_bind, Bind.kleisliRight]
    funext ⟨c, s⟩ 
    cases c <;> 
    (try rename _ ⊕ _ => c; cases c) <;> 
    simp [
      destate, dist_fn,
      StateT.pure, pure
    ]
  uniformity f g h H := by
    apply destate_inj
    rw [destate_kleisli]
    apply e.uniformity
    sorry