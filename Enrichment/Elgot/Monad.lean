import Mathlib.Data.Sum.Basic

class DaggerMonad (m: Type u -> Type v): Type (max (u + 1) v) where
  dagger: ∀{α β: Type u}, (α -> m (β ⊕ α)) -> α -> m β

class ElgotMonad (m: Type u -> Type v) [Monad m] [LawfulMonad m] extends DaggerMonad m
  where
  fixpoint: ∀{α β: Type u}
    (f: α -> m (β ⊕ α)),
    f >=> Sum.elim pure (dagger f) = dagger f
  naturality: ∀{α β γ: Type u}
    (f: α -> m (β ⊕ α))
    (g: β -> m γ),
    dagger (f >=> Sum.elim (g >=> (pure ∘ Sum.inl)) (pure ∘ Sum.inr)) 
      = (dagger f) >=> g
  dinaturality: ∀{α β γ: Type u}
    (g: α -> m (β ⊕ γ))
    (h: γ -> m (β ⊕ α)),
    dagger (g >=> Sum.elim (pure ∘ Sum.inl) h) 
      = g >=> Sum.elim pure (dagger (h >=> Sum.elim (pure ∘ Sum.inl) g))
  uniformity: ∀{α β γ: Type u}
    (f: α -> m (β ⊕ α))
    (g: γ -> m (β ⊕ γ))
    (h: γ -> m α),
    g >=> Sum.elim (pure ∘ Sum.inl) (h >=> (pure ∘ Sum.inr)) 
      = h >=> f
    -> dagger g
      = h >=> dagger f