module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


noncomputable section

namespace GlobalTheory.RatMoveJets

def RatCoord {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : GfC V)
    (U : Matrix.unitaryGroup (Fin V.rank) D.host.E) : Prop :=
  ∃ γ ∈ GQ V, finHom V γ = finHom V (g : GA D V) ∧
    Formalism.L2.Theta.mt V γ = (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (incA D)

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc}

def srcU : ∀ p : GlobalTheory.ChiGrid.Pair T, Matrix.unitaryGroup (Fin (G.V p.small).rank) D.host.E →
    Matrix.unitaryGroup (Fin (G.V p.big).rank) D.host.E → Matrix.unitaryGroup (Fin (G.pS p).rank) D.host.E
  | .chi _ _, _, U' => U'
  | .mu _ _ _, U, _ => U
  | .core _, _, U' => U'
  | .top _ _, U, _ => U

def tgtU : ∀ p : GlobalTheory.ChiGrid.Pair T, Matrix.unitaryGroup (Fin (G.V p.small).rank) D.host.E →
    Matrix.unitaryGroup (Fin (G.V p.big).rank) D.host.E → Matrix.unitaryGroup (Fin (G.pT p).rank) D.host.E
  | .chi _ _, U, _ => U
  | .mu _ _ _, _, U' => U'
  | .core _, U, _ => U
  | .top _ _, _, U' => U'

end

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetTh (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big)
    (Θ : VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ) : Prop :=
  ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ)

theorem jetKap_iff (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ) :
    GlobalTheory.MovedKappaEx.JetKap ch p x y κ ↔ JetTh ch p x y (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ)
      (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ)
        (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) :=
  Iff.rfl

end

end GlobalTheory.RatMoveJets
