module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
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

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.RegSch

variable {D : D7}

structure Lvl (V : HSp D) where

  L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

  c : GL (Fin V.rank) (AE D)

def Lvl.K {V : HSp D} (l : Lvl V) : Subgroup (GA D V) := levelAll D.sp.cm.sig V.gram l.L l.c

def Lvl.Good {V : HSp D} (l : Lvl V) : Prop :=
  Submodule.IsFullLattice D.host.E l.L ∧ (∀ v, IsSelfDualAt D.sp.cm.sig V.gram l.L v) ∧ IsMaj V l.c

def Lvl.form {V : HSp D} (l : Lvl V) : Mx D V.rank V.rank := adj (l.c⁻¹).1 * (l.c⁻¹).1

theorem Lvl.Good.isCompact_K {V : HSp D} {l : Lvl V} (h : l.Good) : IsCompact (l.K : Set (GA D V)) :=
  haveI := h.1
  isCompact_levelAll (isCMExt_host D) _ _ _

section SlopeTestRemainingChoices

variable {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (K : Subgroup (GA D T))

def sphericalSectionIwasawa (s : ℂ) : GA D T → ℂ := fun h => npow (iwAbs (absDet d) K h) (s + rhoH T r)

def sphericalEisensteinSeriesOnGroup (h : GA D T) : ℂ → ℂ := fun s => cosetSum (stab d) (GQ T) (sphericalSectionIwasawa d K s) h

end SlopeTestRemainingChoices

section Ops

variable {n : ℕ}

def projS {T : HSp D} {K : Subgroup (GA D T)} (ν : Measure K) (Φ : Mx D T.rank n → ℂ) : Mx D T.rank n → ℂ :=
  fun x => ∫ k, Φ (mt T (k : GA D T)⁻¹ * x) ∂ν

def ikS {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) (μ : Measure (Mx D t n)) (Φ : Mx D T.rank n → ℂ) : Mx D T'.rank n → ℂ :=
  fun a => ∫ x, Φ (d.jX * x + d.j0 * a) ∂μ

variable (θ : InfFam D) (τ : D.what₂.Tau)

variable {θ} {V V₀ : HSp D} {r : ℕ} (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n))

variable (d : HypDec V V₀ r) (K : Subgroup (GA D V))

end Ops

end GlobalTheory.RegSch

end
