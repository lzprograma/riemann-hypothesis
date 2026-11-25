module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)

namespace GlobalTheory.StdUnn

section
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

private theorem realIdem_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] (f : R →ₐ[F] S)
    (σ : E →ₐ[F] E) (x : R) :
    (Algebra.TensorProduct.map f σ).toRingHom (x ⊗ₜ[F] (1 : E)) = f x ⊗ₜ[F] (1 : E) := by
  change Algebra.TensorProduct.map f σ (x ⊗ₜ[F] (1 : E)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem realIdem_gen (σ : E →ₐ[F] E) : ∃ e : AF F ⊗[F] E, e * e = e ∧ sigR (AF F) σ e = e ∧
    (∀ v, compFin F E v e = 0) ∧ (∀ w, compInf F E w e = 1) ∧
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom e = 0 ∧
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom e = 1 := by
  have hp : pairA F 1 0 * pairA F 1 0 = pairA F 1 0 :=
    Prod.ext (mul_one (1 : Ainf F)) (mul_zero (0 : Af F))
  have h0 : sndA F (pairA F 1 0) = 0 := rfl
  have h1 : fstA F (pairA F 1 0) = 1 := rfl
  refine ⟨pairA F 1 0 ⊗ₜ[F] (1 : E), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  · exact realIdem_map F E (AlgHom.id F (AF F)) σ _
  · intro v
    refine (realIdem_map F E (evFin F v) (AlgHom.id F E) _).trans ?_
    rw [evFin, AlgHom.comp_apply, h0, map_zero, TensorProduct.zero_tmul]
  · intro w
    refine (realIdem_map F E (evInf F w) (AlgHom.id F E) _).trans ?_
    rw [evInf, AlgHom.comp_apply, h1, map_one, Algebra.TensorProduct.one_def]
  · rw [realIdem_map, h0, TensorProduct.zero_tmul]
  · rw [realIdem_map, h1, Algebra.TensorProduct.one_def]

end

theorem realIdem_exists : ∀ D : D7, ∃ e : AE D, e * e = e ∧ cA D e = e ∧ (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ w, compInf D.host.F D.host.E w e = 1) ∧ finPart D e = 0 ∧ infPart D e = 1 :=
  fun D => realIdem_gen D.host.F D.host.E _

end GlobalTheory.StdUnn
