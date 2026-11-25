module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory

theorem mult_value_left_cont_level :
    ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ, ∀ T ∈ Mult θ M J χ, ∀ v, (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ Continuous (T v) ∧ ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  intro D V S θ M J χ T hT v
  induction hT using Submodule.span_induction with
  | mem x hx =>
    exact ⟨(hx.aut v).left, (hx.aut v).cont, hx.lev v⟩
  | zero =>
    refine ⟨fun γ _ g => ?_, ?_, fun k _ g => ?_⟩
    · simp
    · simp only [MultilinearMap.zero_apply]
      exact continuous_zero
    · simp
  | add x y _ _ hx hy =>
    refine ⟨fun γ hγ g => ?_, ?_, fun k hk g => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.1 γ hγ g, hy.1 γ hγ g]
    · simpa only [MultilinearMap.add_apply] using hx.2.1.add hy.2.1
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.2.2 k hk g, hy.2.2 k hk g, mul_add]
  | smul c x _ hx =>
    refine ⟨fun γ hγ g => ?_, ?_, fun k hk g => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.1 γ hγ g]
    · simpa only [MultilinearMap.smul_apply] using hx.2.1.const_smul c
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.2.2 k hk g]
      ring

end GlobalTheory
