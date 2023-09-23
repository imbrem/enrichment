import Mathlib.Data.Sum.Basic

class DaggerMonad (m: Type u -> Type v): Type (max (u + 1) v) where
  dagger: ∀{α β: Type u}, (α -> m (β ⊕ α)) -> α -> m β
  diverge (α: Type u) [Monad m]: m α := dagger (pure ∘ Sum.inr) PUnit.unit

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
  -- Derivable from fixpoint + naturality + codiagonal + uniformaity 
  -- by proposition 17 of Levy and Goncharov 2012 (Coinductive Resumption Monads: Guarded Iterative and Guarded Elgot)
  -- dinaturality: ∀{α β γ: Type u}
  --   (g: α -> m (β ⊕ γ))
  --   (h: γ -> m (β ⊕ α)),
  --   dagger (g >=> Sum.elim (pure ∘ Sum.inl) h) 
  --     = g >=> Sum.elim pure (dagger (h >=> Sum.elim (pure ∘ Sum.inl) g))
  codiagonal: ∀{α β: Type u}
    (f: α -> m ((β ⊕ α) ⊕ α)),
    dagger (f >=> Sum.elim pure (pure ∘ Sum.inr)) = dagger (dagger f)
  uniformity: ∀{α β γ: Type u}
    (f: α -> m (β ⊕ α))
    (g: γ -> m (β ⊕ γ))
    (h: γ -> m α),
    g >=> Sum.elim (pure ∘ Sum.inl) (h >=> (pure ∘ Sum.inr)) 
      = h >=> f
    -> dagger g
      = h >=> dagger f

class IterativeMonad (m: Type u -> Type v) [Monad m] [LawfulMonad m] extends ElgotMonad m
  where
  uniqueness: ∀{α β: Type u}
    (f: α -> m (β ⊕ α))
    (g: α -> m β),
    f >=> Sum.elim pure (g) = g 
      -> g = dagger f

-- Proposition 18 of Levy and Goncharov 2012 (Coinductive Resumption Monads: Guarded Iterative and Guarded Elgot)
-- def IterativeMonad.mk' (m: Type u -> Type v) [Monad m] [LawfulMonad m]
--   (dagger: ∀{α β: Type u}, (α -> m (β ⊕ α)) -> α -> m β)
--   (fixpoint: ∀{α β: Type u}
--     (f: α -> m (β ⊕ α)),
--     f >=> Sum.elim pure (dagger f) = dagger f)
--   (uniqueness: ∀{α β: Type u}
--     (f: α -> m (β ⊕ α))
--     (g: α -> m β),
--     f >=> Sum.elim pure (g) = g 
--       -> g = dagger f)
--   : IterativeMonad m where
--   dagger := dagger
--   fixpoint := fixpoint
--   naturality := sorry
--   dinaturality := sorry
--   uniformity := sorry
--   uniqueness := uniqueness