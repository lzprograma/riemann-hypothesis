module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WBEqPrimeComap
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
open scoped TensorProduct

open IsDedekindDomain

namespace GlobalTheory.FixedConj

theorem comm_tensCastR_symm_mem_intAf {E : Type} [Field E] [NumberField E] {F₁ F₂ : Subfield E} (h : F₁ = F₂)
    (x : E ⊗[F₂] FiniteAdeleRing (𝓞 F₂) F₂)
    (hx : x ∈ Subring.closure ({x | ∃ y : 𝓞 E, x = (y : E) ⊗ₜ[F₂] (1 : FiniteAdeleRing (𝓞 F₂) F₂)} ∪
      {x | ∃ a : FiniteAdeleRing (𝓞 F₂) F₂, (∀ v, a v ∈ v.adicCompletionIntegers F₂) ∧ x = (1 : E) ⊗ₜ[F₂] a})) :
    (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).toRingEquiv
      ((GlobalTheory.StdFrame.tensCastR h).symm x) ∈ Formalism.L2.Herm.intAf (↥F₁) E := by
  subst h
  have hS : Subring.closure ({x | ∃ y : 𝓞 E, x = (y : E) ⊗ₜ[F₁] (1 : FiniteAdeleRing (𝓞 F₁) F₁)} ∪
      {x | ∃ a : FiniteAdeleRing (𝓞 F₁) F₁, (∀ v, a v ∈ v.adicCompletionIntegers F₁) ∧ x = (1 : E) ⊗ₜ[F₁] a}) ≤
      (Formalism.L2.Herm.intAf (↥F₁) E).comap
        (((GlobalTheory.StdFrame.tensCastR (rfl : F₁ = F₁)).symm.trans
          (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).toRingEquiv : _ ≃+* _) : _ →+* _) := by
    rw [Subring.closure_le]
    rintro z (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · show (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E)
          ((Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).symm ((y : E) ⊗ₜ[F₁] 1)) ∈ _
      rw [AlgEquiv.apply_symm_apply]
      exact Subring.subset_closure (Or.inl ⟨⟨(y : E), ⟨y, rfl⟩⟩, rfl⟩)
    · show (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E)
          ((Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).symm ((1 : E) ⊗ₜ[F₁] a)) ∈ _
      rw [AlgEquiv.apply_symm_apply]
      exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact hS hx

theorem adeleEquiv_mem_intAf : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E),
    a ∈ ReciprocityTheory.Aut.ALint D.host.E → GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
  intro D hF a ha
  exact comm_tensCastR_symm_mem_intAf hF a ha

end GlobalTheory.FixedConj
