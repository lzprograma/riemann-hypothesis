module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL

structure SmRep (G : Type) [Group G] [TopologicalSpace G] : Type 1 where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : IsSmooth ρ

attribute [instance] SmRep.acg SmRep.mod

def SmRep.ofIrr {G : Type} [Group G] [TopologicalSpace G] (σ : IrrRep G) : SmRep G :=
  ⟨σ.V, σ.ρ, σ.smooth⟩

end GlobalTheory.SmGL
