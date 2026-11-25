module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum

namespace GlobalTheory.KFinCuspApprox

variable {D : D7}

abbrev avgN (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ)
    (φ : GA D N.V → ℂ) : GA D N.V → ℂ :=
  GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e φ

def KStab (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (s : Set D.what₂.Tau) (W : Submodule ℂ (GA D N.V → ℂ)) : Prop :=
  ∀ τ ∈ s, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), N.M.fr τ * g * (N.M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (N.M.ε τ) →
    ∀ f ∈ W, rTr N.V (atTau θ N.V τ g) f ∈ W

theorem kStab_empty (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (W : Submodule ℂ (GA D N.V → ℂ)) : KStab θ N ∅ W := fun _ h => h.elim

end GlobalTheory.KFinCuspApprox

end
