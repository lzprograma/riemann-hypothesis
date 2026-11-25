module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridRouteKernelEqDetCharactersMulThetaKerne

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr


theorem _root_.GlobalTheory.T.thetaGridRouteKernel_eq_detCharacters_mul_thetaKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerBig W Θ g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωA u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumA W Θ) := by
  first | exact @GlobalTheory.SquareDict.ExactBig.kerBig_eq
