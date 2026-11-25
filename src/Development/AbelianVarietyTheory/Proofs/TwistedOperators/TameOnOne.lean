module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts

namespace GlobalTheory.StepLaw

variable {D : D7}

def TameOn (χ : (AE D)ˣ →* Circle) (e : AE D) (P : Finset (Pl D.host.E))
    (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
    toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → cA D e * (x : AE D) = cA D e →
    ∀ u : ∀ PP : Pl D.host.E, (kP PP)ˣ, (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩) →
      ((χ x : Circle) : ℂ) = ∏ PP ∈ P, ((c PP (u PP) : ℂˣ) : ℂ)

def vacScal {S T : HSp D} (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (g : GA D S) (h : GA D T) : ℂ :=
  ∏ PP ∈ P, (((cT PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ)⁻¹ *
    ((cS PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ))


open Classical in
def resChr {T0 : Type} (L : LevCh D T0) (t : T0) (n : ℕ) (PP : Pl D.host.E) : (kP PP)ˣ →* ℂˣ :=
  if PP ∈ L.Pg then (L.chi n PP)⁻¹ else L.xiR t PP

end GlobalTheory.StepLaw

end
