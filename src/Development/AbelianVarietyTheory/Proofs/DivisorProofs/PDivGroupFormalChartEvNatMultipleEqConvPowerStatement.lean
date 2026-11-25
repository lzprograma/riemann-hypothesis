module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct WithConv Coalgebra

theorem _root_.GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
      [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
      ∀ (G : GlobalTheory.PDivGroup p O) (d : ℕ) (c : GlobalTheory.QLog.Chart G d)
        (n k : ℕ) (i : Fin d),
        c.ev n (nmul c.μ k i) = PDiv.mulBy (R := O) (A := G.A n) k (c.x n i) :=
  @GlobalTheory.NMul.ev_nmul
