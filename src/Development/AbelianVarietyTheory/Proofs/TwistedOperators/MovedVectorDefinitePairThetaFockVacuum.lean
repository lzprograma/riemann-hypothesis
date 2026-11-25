module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

namespace GlobalTheory.RowReal

theorem movedVec_theta_fockVac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) (t : T) (p : Pair T), DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (movedVec t S d) ∧
      ∀ ρ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) (movedVec t S d) := by
  intro D T L sc G W U S t p hp d hd
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by
    cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  obtain ⟨h1, h2⟩ := GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd
  have mem : (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).1 ∈ GfC (G.pS p) ∧
      (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | mu t i j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
    | core i => exact ⟨GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | top t j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
  exact GlobalTheory.FockRealMove.om_fin_fockVac D W.ψ W.θ _ _ _ _ (W.om p) hom W.θ_is _ _ _ h1 h2 _ mem.1 _ mem.2

end GlobalTheory.RowReal

end
