module

public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Smoothing
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import GroundTheory.AutomorphicForms.L2LocalComponents.ArchHaar
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
public import GroundTheory.AutomorphicForms.TraceFormulaWeil
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Tactic.Linter.HaveILetI
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.unimod :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), (∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure], ν.IsMulRightInvariant ∧ ν.IsInvInvariant) ∧
      ∀ (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], m.IsMulRightInvariant ∧ m.IsInvInvariant := by
  intro K _ _ n
  refine ⟨fun ν _ => ⟨isMulRightInvariant_archGroup ν, isInvInvariant_archGroup ν⟩, fun m _ => ?_⟩
  haveI hr : m.IsMulRightInvariant := Whittaker.isMulRightInvariant_finite K n m
  exact ⟨hr, ⟨inv_eq_self_of_isMulRightInvariant m⟩⟩
