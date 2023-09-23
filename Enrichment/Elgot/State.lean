import Enrichment.Elgot.Monad
import Enrichment.Utils.Monad

instance stateDaggerMonad {σ} {m: Type u -> Type v} [Monad m] [d: DaggerMonad m]
  : DaggerMonad (StateT σ m)
  where
  dagger f := restate (d.dagger (destate f >=> (pure ∘ dist_fn)))

def destate_state_dagger {σ: Type u} {m: Type u -> Type v} [Monad m] [d: DaggerMonad m] {α β: Type u}
  (f: α -> StateT σ m (β ⊕ α))
  : destate (DaggerMonad.dagger f) = d.dagger (destate f >=> (pure ∘ dist_fn))
  := rfl

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
    rw [
      kleisli_assoc (destate h) (destate f),
      <-destate_kleisli h f,
      <-H,
      destate_kleisli,
      <-kleisli_assoc,
      <-kleisli_assoc
    ]
    apply congr rfl;
    funext ⟨c, s⟩
    cases c with
    | inl b => simp [pure, StateT.pure, dist_fn, kleisli_comp_app, destate]
    | inr c => 
      rw [
        Bind.kleisliRight,
        Function.comp_apply,
        pure_bind,
        dist_fn_inr,
        Sum.elim_inr,
        Bind.kleisliRight,
        destate,
        Bind.kleisliRight,
        destate,
        Sum.elim_inr,
        kleisli_comp_app
      ]
      simp only [bind, StateT.bind, pure, StateT.pure, bind_assoc]
      apply congr rfl
      funext ⟨a, s⟩
      simp [dist_fn]