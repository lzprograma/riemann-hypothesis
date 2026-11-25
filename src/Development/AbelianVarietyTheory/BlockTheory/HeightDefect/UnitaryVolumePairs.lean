module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs

section Volume

variable {D : D7}

variable (D)

end Volume

section Ideles

variable (D : D7)

abbrev AE : Type := AF D.host.F ⊗[D.host.F] D.host.E

abbrev IdE : Type := (AE D)ˣ

abbrev IdF : Type := (AF D.host.F)ˣ

def resF : IdF D →* IdE D :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom :
    AF D.host.F →+* AF D.host.F ⊗[D.host.F] D.host.E).toMonoidHom

def ratF : D.host.Fˣ →* IdF D := Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom

def conjId : IdE D →* IdE D := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def normId : IdE D →* IdE D := MonoidHom.id (IdE D) * conjId D

end Ideles

section Hecke

variable (D : D7)

def normGroup : Subgroup (IdF D) := (ratF D).range ⊔ (normId D).range.comap (resF D)


variable {D}


variable (D)

end Hecke

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs

end
