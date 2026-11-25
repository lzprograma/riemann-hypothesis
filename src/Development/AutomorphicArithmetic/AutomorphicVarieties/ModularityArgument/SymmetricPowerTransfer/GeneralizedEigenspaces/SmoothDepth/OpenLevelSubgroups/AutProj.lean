module

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DecompA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCompactFundamentalSetUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEquivariantProjectionsOfSumIrreducible
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNondegenerateRightInvariantFormOfCompactQu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupAutomorphicRepsOfInvariantForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnitaryAdelicGroupTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.Wcount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

open UpperTheory.V.Z.Sym.Al

open GlobalTheory.DefU in
theorem UpperTheory.V.Z.Sym.Al.autProj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (M : Submodule ℂ (GlobalTheory.DefU.autU L n)), FiniteDimensional ℂ M →
        ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Submodule ℂ (UA L n → ℂ)) (P : κ → GlobalTheory.DefU.autU L n →ₗ[ℂ] GlobalTheory.DefU.autU L n),
          (∀ i, IsAutRepU (σ i)) ∧ (∀ i φ, (P i φ).1 ∈ σ i) ∧
          (∀ i x φ, P i (GlobalTheory.DefU.autRep L n x φ) = GlobalTheory.DefU.autRep L n x (P i φ)) ∧ ∀ φ ∈ M, ∑ i, P i φ = φ := @_root_.UpperTheory.V.Z.J.D.Dc.autProj
