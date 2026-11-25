module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponent
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
public import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Formalism.LocalToGlobal.ProjectiveLattices.CompData
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegLaw

@[expose] public section

noncomputable section

namespace GlobalTheory.TrivOrderTieCompare

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem isClopen_comp (Z : Comp Xo c) : IsClopen (Z : Set (Xo.XF c)) := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have hZ : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
  obtain ⟨z, hz⟩ := hZ.nonempty
  have h1 : (Z : Set (Xo.XF c)) ⊆ connectedComponent z :=
    hZ.isConnected.isPreconnected.subset_connectedComponent hz
  have h2 : IsIrreducible (connectedComponent z) :=
    ⟨⟨z, mem_connectedComponent⟩, GlobalTheory.KeyFam.isPreirreducible_connectedComponent_of_smooth (strK (Xo := Xo) (c := c)) z⟩
  rw [Set.Subset.antisymm h1 (Z.2.2 h2 h1)]
  exact ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_noetherianSpace z⟩

variable [Fintype (Comp Xo c)]

end GlobalTheory.TrivOrderTieCompare
