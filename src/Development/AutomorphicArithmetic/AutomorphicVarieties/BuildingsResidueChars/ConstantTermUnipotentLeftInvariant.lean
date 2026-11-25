module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
import GroundTheory.GlobalFields.Adele.Topology
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
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct

theorem UpperTheory.constantTerm_unipotent_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ),
      IsLeftInvariant φ → ∀ (X : UPos n r → AdeleRing (𝓞 K) K) g,
        constantTerm (r := r) φ (unipGL X * g) = constantTerm (r := r) φ g := by
  intro K _ _ n r φ hφ X g
  have hfd := isAddFundamentalDomain_unipFundamentalDomain (K := K) (n := n) (r := r)
  have hfd' := hfd.vadd_of_comm X
  rw [constantTerm_eq_setIntegral hφ hfd, constantTerm_eq_setIntegral hφ hfd' g, ← Set.image_vadd]
  simp only [vadd_eq_add]
  rw [(measurePreserving_add_left (unipMeasure K n r) X).setIntegral_image_emb
      (MeasurableEquiv.addLeft X).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
  show φ (unipGL Y * (unipGL X * g)) = φ (unipGL (X + Y) * g)
  rw [add_comm X Y, unipGL_add, mul_assoc]
