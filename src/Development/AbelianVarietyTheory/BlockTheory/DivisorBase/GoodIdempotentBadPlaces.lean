module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Lev Formalism.IndefR.Mult
open Formalism.L2.DIV (Pl kP primesOf IsTypeDatum G0 LevDat P0 IsGenericPsi)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (SSParam GoodAt typeChar centralIdem chiTame IsGeneratorFamily)
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodIdempotentBadPlaces

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

variable {D : D7}

abbrev typePl (pb : Fin 2 → 𝓞 D.host.E) : Finset (Pl D.host.E) := primesOf (pb 0 * pb 1)

instance finite_kP (w : Pl D.host.E) : Finite (kP w) :=
  Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot


variable (D) in
def badPl : Finset (HeightOneSpectrum (𝓞 D.host.F)) := primesOf ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)

abbrev Model (D : D7) (j : ℕ) : Type 1 := DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))

end GlobalTheory.IndefiniteRowSideFullHecke.GoodIdempotentBadPlaces
