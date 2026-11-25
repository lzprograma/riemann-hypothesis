module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.DiagSubIsKIrrHW
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.InKRealSmul
public import Mathlib.Analysis.Normed.Lp.WithLp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquivA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IrredA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOneA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RigidUniversal

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidUniversal, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsEquiv

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

theorem rigid_orth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (j' : V →ₗ[ℂ] H) (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j' w = σ k (j' v))
    (horth : ∀ v v' : V, inner ℂ (j' v') ((v : D) : H) = 0) :
    ∀ g ∈ UJset ε, ∀ v v' : V, inner ℂ (j' v') (σ g ((v : D) : H)) = 0 := by
  intro g hg v v'
  refine rigid_orth_closure hgap hσ hD hV hc hVK j' hj horth v' _ ?_
  refine closure_genSub_stable hσ hD hV.1 hV.2.1 hc g hg _ ?_
  exact Submodule.le_topologicalClosure _ ⟨v, rorth_le_genSub v.2, rfl⟩

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidUniversal =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidUniversal", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.DiagSubIsKIrrHW\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.InKRealSmul\npublic import Mathlib.Analysis.Normed.Lp.WithLp\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

theorem rigid_universal {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} (hσ₁ : IsURepOn (UJset ε) σ₁)
    {D₁ : Submodule ℂ H₁} {E₁ : Fin n → Fin n → Module.End ℂ D₁} (hD₁ : IsDerivedOn ε σ₁ D₁ E₁)
    {V₁ : Submodule ℂ D₁} (hV₁ : IsKIrrHW ε E₁ (lowK ε lam) V₁)
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = (casVal lam : ℂ) • v)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v)
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} (hσ₂ : IsURepOn (UJset ε) σ₂)
    {D₂ : Submodule ℂ H₂} {E₂ : Fin n → Fin n → Module.End ℂ D₂} (hD₂ : IsDerivedOn ε σ₂ D₂ E₂)
    {V₂ : Submodule ℂ D₂} (hV₂ : IsKIrrHW ε E₂ (lowK ε lam) V₂)
    (hc₂ : ∀ v ∈ V₂, casimir E₂ v = (casVal lam : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : H₂) = σ₂ k v)
    (hgap : StdGap ε lam) (φ : V₁ →ₗ[ℂ] V₂)
    (hφK : ∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂))
    (hφI : ∀ v v' : V₁, inner ℂ (((φ v' : V₂) : D₂) : H₂) (((φ v : V₂) : D₂) : H₂) =
      inner ℂ ((v' : D₁) : H₁) ((v : D₁) : H₁)) :
    ∀ g ∈ UJset ε, ∀ v v' : V₁,
      inner ℂ (((φ v' : V₂) : D₂) : H₂) (σ₂ g (((φ v : V₂) : D₂) : H₂)) =
        inner ℂ ((v' : D₁) : H₁) (σ₁ g ((v : D₁) : H₁)) :=
  DS.rigid_universal_of hD₁ hV₁ hc₁ hVK₁ hD₂ hc₂ φ hφK hφI fun hV hc hVK j' hj horth =>
    rigid_orth hgap (USum.isURepOn_sσ hσ₁ hσ₂) (USum.isDerivedOn_sσ hD₁ hD₂) hV hc hVK j' hj horth

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidUniversal =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsEquiv =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsEquiv", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquivA\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidUniversal\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IrredA\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOneA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

theorem data_unitary_equiv (hgap : StdGap ε lam)
    (hσ₁ : IsURepOn (UJset ε) σ₁) (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hV₁ : IsKIrrHW ε E₁ (lowK ε lam) V₁)
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = (casVal lam : ℂ) • v)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v) (hV₁0 : V₁ ≠ ⊥)
    (hσ₂ : IsURepOn (UJset ε) σ₂) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) (hV₂ : IsKIrrHW ε E₂ (lowK ε lam) V₂)
    (hc₂ : ∀ v ∈ V₂, casimir E₂ v = (casVal lam : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : H₂) = σ₂ k v) (hV₂0 : V₂ ≠ ⊥) :
    ∃ U : closGen E₁ V₁ ≃ₗᵢ[ℂ] closGen E₂ V₂, ∀ g ∈ UJset ε, ∀ x y : closGen E₁ V₁,
      (x : H₁) = σ₁ g (y : H₁) → ((U x : closGen E₂ V₂) : H₂) = σ₂ g ((U y : closGen E₂ V₂) : H₂) := by
  obtain ⟨φ, hφK, hφI⟩ := KTypeIsomorphism.exists_phi hσ₁ hD₁ hV₁ hσ₂ hD₂ hV₂
  have huniv := rigid_universal hσ₁ hD₁ hV₁ hc₁ hVK₁ hσ₂ hD₂ hV₂ hc₂ hVK₂ hgap φ hφK hφI
  exact KTypeIsomorphism.unitary_equiv_of_matrix_coefficients hσ₁ hσ₂ hV₁0 φ huniv
    (closGen_stable hgap hσ₁ hD₁ hV₁ hc₁ hVK₁) (closGen_stable hgap hσ₂ hD₂ hV₂ hc₂ hVK₂)
    (rigid_irred hgap hσ₁ hD₁ hV₁ hc₁ hVK₁) (rigid_irred hgap hσ₂ hD₂ hV₂ hc₂ hVK₂)

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsEquiv =====
