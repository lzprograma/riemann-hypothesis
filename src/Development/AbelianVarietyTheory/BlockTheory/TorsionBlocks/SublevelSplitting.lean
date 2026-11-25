module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

variable {D : D7}

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

def matF (V : HSp D) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
  Units.val (h : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))

def compAtPl (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  (matF V h).map (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E))


variable (D) in
def IsSplitPl (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∃ P P' : HeightOneSpectrum (𝓞 D.host.E), P ≠ P' ∧ P.under (𝓞 D.host.F) = v ∧ P'.under (𝓞 D.host.F) = v

def SuppSplitOff (V : HSp D) (bad : ℕ) (h : Bridge.Gf V) : Prop :=
  ∃ Sp : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    (∀ v ∈ Sp, IsSplitPl D v ∧ (bad : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, v ∉ Sp → compAtPl V v h = 1

def IsOpenLev (V : HSp D) (J' : Subgroup (Bridge.Gf V)) : Prop :=
  IsOpen ((J'.comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V))

end GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

end
