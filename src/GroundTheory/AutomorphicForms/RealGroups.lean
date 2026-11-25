module

public import GroundTheory.AutomorphicForms.RealGroupsIwasawaHaar
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.CategoryTheory.Countable
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Star.Unitary

@[expose] public section

namespace GroundTheory.Automorphic

open Matrix Set
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [LinearOrder n]

section HaarKBComplex

open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator

instance : SecondCountableTopology (Matrix n n ℂ) :=
  inferInstanceAs (SecondCountableTopology (n → n → ℂ))

instance : SecondCountableTopology (GL n ℂ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℂ)).isEmbedding.secondCountableTopology

instance : LocallyCompactSpace (GL n ℂ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℂ)).locallyCompactSpace

instance : SecondCountableTopology (upperPosSubgroup n ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem isClosed_upperPosSubgroupC : IsClosed (upperPosSubgroup n ℂ : Set (GL n ℂ)) :=
  isClosed_upperPosSubgroup_RCLike

instance : LocallyCompactSpace (upperPosSubgroup n ℂ) :=
  isClosed_upperPosSubgroupC.locallyCompactSpace

noncomputable def kbInvHomeomorphC : GL n ℂ ≃ₜ unitaryGroup n ℂ × upperPosSubgroup n ℂ :=
  kbInvHomeomorph_RCLike

theorem lintegral_haarGLComplex_iwasawa (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℂ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℂ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(haarGLComplex μ₀) =
        c * ∫⁻ k, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv ∂μK :=
  lintegral_haarGL_iwasawa (haarGLComplex μ₀) μK μB

end HaarKBComplex

end GroundTheory.Automorphic
