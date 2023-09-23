import Enrichment.TraceMonad.Factored.Basic
import Enrichment.Elgot.State

structure SplitTraces (ε τ σ α) where
  computation: StateT σ (Traces ε τ) α