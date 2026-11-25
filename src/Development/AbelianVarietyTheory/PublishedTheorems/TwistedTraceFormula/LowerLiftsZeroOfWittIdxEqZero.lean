module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
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

open scoped ComplexConjugate
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Cusp
open GlobalTheory.Mem.Th (InfF CptF)

namespace GlobalTheory.RallisIP

variable {D : D7} {A B : HSp D} (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (m : Measure (GA D A))

def thetaLift (Φ : WO A B → ℂ) (f : GA D A → ℂ) : GA D B → ℂ :=
  fun h => petersson A m (fun g => thetaKO ω g h Φ) f

def LiftConv (Φ : WO A B → ℂ) (f : GA D A → ℂ) : Prop :=
  ∀ h, Integrable (descend (GQ A) fun g => thetaKO ω g h Φ * conj (f g)) (autMeasure A m)

end GlobalTheory.RallisIP

namespace GlobalTheory.Published

open GlobalTheory.RallisIP
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (delta swSec sZero IsKFinVec ThetaClause)

end GlobalTheory.Published

namespace GlobalTheory.RallisIP

variable {D : D7} {A B : HSp D}

theorem wittIdx_eq_wittIndex (B : HSp D) : Formalism.MainNotions.SchurIrreducible.wittIdx B = wittIndex B := by
  unfold Formalism.MainNotions.SchurIrreducible.wittIdx wittIndex
  congr 1
  ext k
  refine exists_congr fun W => and_comm.trans (and_congr_left' ⟨fun h y hy => mem_perp.2 fun x hx => ?_, fun h x hx y hy => ?_⟩)
  · exact h x hx y hy
  · exact mem_perp.1 (h hy) x hx

variable {ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)} {m : Measure (GA D A)} {Φ : WO A B → ℂ} {f : GA D A → ℂ}

end GlobalTheory.RallisIP

end
