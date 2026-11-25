module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermArchSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct

theorem UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), ∃ f : automorphicForms K n →ₗ[ℂ] archSmooth K n, (∀ φ, (f φ).1 = constantTerm r φ.1) ∧ ∀ u φ, f (uActionAF K n u φ) = uAction u (f φ) := by
  intro K _ _ n r
  have h := fun φ : automorphicForms K n =>
    UpperTheory.constantTerm_archSmooth K n r ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩ φ.2
  choose hs hX using h
  let f : automorphicForms K n →ₗ[ℂ] archSmooth K n :=
    { toFun := fun φ => ⟨constantTerm r φ.1, hs φ⟩
      map_add' := fun φ ψ => Subtype.ext (funext fun g =>
        constantTerm_add (IsAutomorphicForm.continuous φ.2) (IsAutomorphicForm.continuous ψ.2) g)
      map_smul' := fun c φ => Subtype.ext (funext fun g => constantTerm_smul c φ.1 g) }
  refine ⟨f, fun _ => rfl, fun u => ?_⟩
  induction u using UEnv.induction with
  | halg c =>
    intro φ
    have e : uActionAF K n (algebraMap ℝ (UEnv K n) c) φ = (c : ℂ) • φ :=
      Subtype.ext (coe_uAction_algebraMap c ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩)
    rw [e, map_smul]
    exact Subtype.ext (coe_uAction_algebraMap c (f φ)).symm
  | hι X => exact fun φ => Subtype.ext (hX φ X).symm
  | hmul a b ha hb =>
    intro φ
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | hadd a b ha hb =>
    intro φ
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), ha, hb]
