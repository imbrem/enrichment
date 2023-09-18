import Enrichment.Elgot.Monad

def state_t_dist_fn {σ} {m} [Monad m] {α β γ}
  (f: α -> StateT σ m (β ⊕ γ))
  : α × σ -> m (β × σ ⊕ γ × σ)
  := λ(a, s) => (λ| (Sum.inl b, s) => Sum.inl (b, s) | (Sum.inr c, s) => Sum.inr (c, s)) <$> f a s

instance stateDaggerMonad {σ} {m: Type u -> Type v} [Monad m] [d: DaggerMonad m]
  : DaggerMonad (StateT σ m)
  where
  dagger f a s := d.dagger (state_t_dist_fn f) (a, s)

-- instance stateElgotMonad {σ} {m: Type u -> Type v} [Monad m] [LawfulMonad m] [e: ElgotMonad m]
--   : ElgotMonad (StateT σ m)
--   where
--   fixpoint f := by 
--     simp only [DaggerMonad.dagger]
--     rw [<-e.fixpoint]
--     funext a s
--     simp only [pure, StateT.pure, Bind.kleisliRight, bind, StateT.bind] 
--     sorry
--     -- simp only [DaggerMonad.dagger]
--   naturality := by
--     simp only [DaggerMonad.dagger]
--     rw [<-e.naturality]
--   codiagonal := sorry
--   uniformity := sorry