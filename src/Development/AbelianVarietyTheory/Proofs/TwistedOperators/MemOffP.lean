module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace

noncomputable section

namespace GlobalTheory.FibreAtTau

variable {D : D7} (θ : InfFam D) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau)

def atP : Subgroup (NI V C) :=
  (GinfC V ⊓ ⨅ (τ' : D.what₂.Tau) (_ : τ' ≠ τ), (GlobalTheory.RowReal.infMatHom V (θ τ')).ker).subgroupOf (NI V C)

def offP : Subgroup (NI V C) := ((GlobalTheory.RowReal.infMatHom V (θ τ)).ker).subgroupOf (NI V C)

variable {θ V C τ}

theorem mem_atP {p : NI V C} :
    p ∈ atP θ V C τ ↔ (p : GA D V) ∈ GinfC V ∧ ∀ τ', τ' ≠ τ → cmp θ τ' (p : GA D V) = 1 := by
  simp only [atP, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rfl

theorem mem_offP {q : NI V C} : q ∈ offP θ V C τ ↔ cmp θ τ (q : GA D V) = 1 := by
  simp only [offP, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  rfl

end GlobalTheory.FibreAtTau
