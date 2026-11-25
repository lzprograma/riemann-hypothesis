module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.openLev :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ φ : UA L n → V, CoefIn φ π →
        ∃ U : Subgroup (UA L n), IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∧ ∀ u ∈ U, ∀ g, φ (g * u) = φ g := by
  intro L _ _ _ n V _ _ _ π hπ φ hc
  let U : Subgroup (UA L n) :=
    { carrier := {u | ∀ g, φ (g * u) = φ g}
      one_mem' := fun g => by rw [mul_one]
      mul_mem' := fun {a b} ha hb g => by rw [← mul_assoc, hb, ha]
      inv_mem' := fun {a} ha g => by rw [← ha, inv_mul_cancel_right] }
  refine ⟨U, ?_, fun u hu => hu⟩
  let b := Module.finBasis ℂ V
  have e : {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} = ⋂ i, {k : finU (E := L) (n := n) | RU L n k (b.coord i ∘ φ) = b.coord i ∘ φ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun h i => funext fun g => congrArg (b.coord i) (h g), fun h g => b.ext_elem fun i => congrFun (h i) g⟩
  rw [e]
  exact isOpen_iInter_of_finite fun i => (hπ.aut _ (hc _)).level
