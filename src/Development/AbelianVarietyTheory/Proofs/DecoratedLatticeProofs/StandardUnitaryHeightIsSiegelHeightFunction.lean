module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnnStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEqStatement
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)

namespace GlobalTheory.StdUnn

theorem isHeight_hgtStd : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → IsHeight (hgtStd A a κ p) := by
  intro D A μ hμ κ hκ a p hc p₁ hp₁ α hα k hk
  have hq : κ.symm p₁ ∈ siegel A := (GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ (κ.symm p₁)).2 (by simpa using hp₁)
  set q : siegel A := ⟨κ.symm p₁, hq⟩ with hqdef
  have hk' : (p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
    rw [hc]; simpa [mul_assoc] using hk
  have e : κ.symm (p₁ * k) * (p : GA D (dblSp A))⁻¹ =
      ((q * p⁻¹ : siegel A) : GA D (dblSp A)) * ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹) := by
    simp [hqdef, map_mul, mul_assoc]
  have hdet : aP A q = Matrix.GeneralLinearGroup.det α :=
    GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq D A μ hμ κ hκ q α (by simpa [hqdef] using hα)
  show hgt A a (κ.symm (p₁ * k) * (p : GA D (dblSp A))⁻¹) * absA D (aP A p) = absA D (Matrix.GeneralLinearGroup.det α)
  rw [e, hgt_mul A a (q * p⁻¹) hk', ← map_mul, ← map_mul, inv_mul_cancel_right, hdet]

end GlobalTheory.StdUnn
