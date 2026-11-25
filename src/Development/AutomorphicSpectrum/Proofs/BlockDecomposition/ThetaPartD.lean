module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND

section Adelic

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def starN (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
    (b : HermR (AF F) σ n) : ℂ :=
  ∫ X, Φ X * ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) ∂dx

def coefN (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E) : ℂ :=
  ∫ b, starN σ J ψ dx Φ b * ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
    (Matrix.trace (T.map (inclR (AF F)) * (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) ∂db

end Adelic

section Glue

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

def tupOf {D : D7} {m r : ℕ} (X : Fin r → Fin m → AE D) : Mx D m r := Matrix.of fun i a => X a i

def thetaPartD {D : D7} (V : HSp D) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) {r : ℕ}
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) : ℂ :=
  ∫ X, φ (tupOf X) ∂(GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram μH 𝓕
    {X : Fin r → Fin V.rank → D.host.E | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1})

end Glue

end GlobalTheory.CompanionTheory.SiegelND
