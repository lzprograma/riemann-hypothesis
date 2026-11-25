module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SatakeDualWeyl.StatementG
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Polynomial
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert

variable {D : D7}

abbrev plF (PP : Pl D.host.E) : HeightOneSpectrum (𝓞 D.host.F) := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def IsInertPl (PP : Pl D.host.E) : Prop :=
  Formalism.UG.IsInertAt D.host.F D.host.E (plF PP) PP

def LocAt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) : Prop :=
  ∀ v', v' ≠ v →
    ((x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (evalV D.host.F v') (AlgHom.id D.host.F D.host.E)) = 1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev levX (R : RealDat D A Ks) (t : T) : Subgroup (Bridge.Gf D.sp.X') := (levEnv D.sp.X' R.βX (R.datXt t)).J

def IsInertDC (R : RealDat D A Ks) (t : T) (PP : Pl D.host.E) (x : Bridge.Gf D.sp.X') (B : Finset (Bridge.Gf D.sp.X')) : Prop :=
  IsInertPl PP ∧ PP ∉ R.Sb ∧ PP ∉ R.Q t ∧ LocAt D.sp.X' (plF PP) x ∧ (∀ b ∈ B, LocAt D.sp.X' (plF PP) b) ∧
    Bridge.IsDC (levX R t) x B

abbrev InertIx (R : RealDat D A Ks) (t : T) : Type :=
  {a : Pl D.host.E × Bridge.Gf D.sp.X' × Finset (Bridge.Gf D.sp.X') // IsInertDC R t a.1 a.2.1 a.2.2}

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert

end
