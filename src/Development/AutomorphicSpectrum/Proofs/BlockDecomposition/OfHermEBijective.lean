module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {r : ℕ}

theorem rat_mem_hermA (β : HermE D r) : rat β.1 ∈ hermA D r := by
  show adj (rat β.1) = rat β.1
  rw [← rat_conjTranspose]
  congr 1
  exact β.2

def ofHermE (β : HermE D r) : ratHerm D r :=
  ⟨⟨rat β.1, rat_mem_hermA β⟩, ⟨β.1, rfl⟩⟩

theorem ofHermE_val (β : HermE D r) : (ofHermE β).1.1 = β.1.map (incA D) := rfl

theorem ofHermE_bijective : Function.Bijective (ofHermE (D := D) (r := r)) := by
  refine ⟨fun a b h => Subtype.ext (rat_injective (congrArg (fun c : ratHerm D r => c.1.1) h)), ?_⟩
  rintro ⟨⟨x, hx⟩, hr⟩
  obtain ⟨γ, hγ⟩ := (mem_ratMx).1 (AddSubgroup.mem_comap.1 hr)
  have hγ' : rat γ = x := hγ
  refine ⟨⟨γ, rat_injective ?_⟩, Subtype.ext (Subtype.ext hγ')⟩
  have hx' : adj x = x := hx
  have : rat γᴴ = rat γ := by rw [rat_conjTranspose, hγ', hx']
  exact this

def hermEquiv : HermE D r ≃ ratHerm D r := Equiv.ofBijective _ ofHermE_bijective

theorem W_eq (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r))
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) :
    W ψ V μ lam φ β = ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul (ofHermE β).1.1 b.1 : Mx D r r))) ∂lam := rfl

end GlobalTheory.CompanionTheory.HermPoisson
