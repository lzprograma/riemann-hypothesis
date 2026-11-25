module

public import GroundTheory.GlobalFields.CompletionAtPlace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.FunExt

namespace GlobalTheory.BCChar

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def normU (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] :
    (u.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ :=
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  Units.map (Algebra.norm (v.adicCompletion K) : u.adicCompletion L →* v.adicCompletion K)

theorem isSmoothChar_comp_normU (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L))
    [u.asIdeal.LiesOver v.asIdeal] {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsSmoothChar (χ.comp (normU v u)) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion L) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K L (u.adicCompletion L)]
  have hfd : FiniteDimensional (v.adicCompletion K) (u.adicCompletion L) := GroundTheory.Global.finite_adicCompletion v u
  have hc := (GlobalTheory.adicCompletion_trace_norm_continuous K L v u _ (GroundTheory.Global.continuous_adicCompletionMap v u) hfd).2
  unfold IsSmoothChar at hχ ⊢
  rw [← MonoidHom.comap_ker]
  exact hχ.preimage (Continuous.units_map _ hc)

end GlobalTheory.BCChar

end
