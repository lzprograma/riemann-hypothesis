module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct

theorem UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (α : (UPos n r → AdeleRing (𝓞 K) K) ≃ₜ+ (UPos n r → AdeleRing (𝓞 K) K)), (∀ X, α X ∈ unipLattice K n r ↔ X ∈ unipLattice K n r) → ∀ F : (UPos n r → AdeleRing (𝓞 K) K) → ℂ, (∀ ξ ∈ unipLattice K n r, ∀ X, F (ξ + X) = F X) → ∫ X in unipFundamentalDomain K n r, F (α X) ∂unipMeasure K n r = ∫ X in unipFundamentalDomain K n r, F X ∂unipMeasure K n r := by
  intro K _ _ n r α hα F hF
  haveI : TopologicalSpace.MetrizableSpace (UPos n r → AdeleRing (𝓞 K) K) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  haveI : (unipMeasure K n r).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hfd : IsAddFundamentalDomain (unipLattice K n r) (unipFundamentalDomain K n r) (unipMeasure K n r) :=
    isAddFundamentalDomain_unipFundamentalDomain
  have hsm := addEquivAddHaarChar_smul_map (unipMeasure K n r) α.symm
  have hpos := addEquivAddHaarChar_pos α.symm
  have hmap : (unipMeasure K n r).map α.symm = (addEquivAddHaarChar α.symm)⁻¹ • unipMeasure K n r := by
    conv_rhs => rw [← hsm]
    rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  have hqmp : Measure.QuasiMeasurePreserving α.symm (unipMeasure K n r) (unipMeasure K n r) :=
    ⟨α.symm.continuous.measurable.aemeasurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  let e : unipLattice K n r → unipLattice K n r := fun g => ⟨α g, (hα g).2 g.2⟩
  have he : Function.Bijective e := by
    refine ⟨fun g h hgh => ?_, fun g => ⟨⟨α.symm g, (hα (α.symm g)).1 (by simpa using g.2)⟩, ?_⟩⟩
    · apply Subtype.ext
      apply α.injective
      exact congrArg Subtype.val hgh
    · apply Subtype.ext
      simp [e]
  have hfd' : IsAddFundamentalDomain (unipLattice K n r) (α.symm ⁻¹' unipFundamentalDomain K n r)
      (unipMeasure K n r) :=
    hfd.preimage_of_equiv hqmp he (fun g x => by
      show α.symm (α g + x) = g + α.symm x
      simp [map_add (f := _)])
  have hmeas := hfd'.measure_eq hfd
  have hpre := addEquivAddHaarChar_smul_preimage (unipMeasure K n r) (X := unipFundamentalDomain K n r) α.symm
  rw [hmeas, unipMeasure_unipFundamentalDomain, ENNReal.smul_def, smul_eq_mul, mul_one,
    ENNReal.coe_eq_one] at hpre
  have hmp : MeasurePreserving α.symm (unipMeasure K n r) (unipMeasure K n r) :=
    ⟨α.symm.continuous.measurable, by rw [hmap, hpre, inv_one, one_smul]⟩
  have key := hmp.setIntegral_preimage_emb α.symm.toHomeomorph.measurableEmbedding
    (fun y => F (α y)) (unipFundamentalDomain K n r)
  simp only [ContinuousAddEquiv.apply_symm_apply] at key
  rw [← key]
  exact hfd'.setIntegral_eq hfd (fun g x => hF g g.2 x)
