module

public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
public import GroundTheory.HeightsAndTheta.Heights.HermitianSum
public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
public import Mathlib.RingTheory.Flat.TorsionFree
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocal, GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocal =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocal", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact\npublic import GroundTheory.HeightsAndTheta.Heights.HermitianSum\npublic import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.RingTheory.Flat.TorsionFree\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain

noncomputable section

structure HermitianNorms (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V]
    [Module (𝓞 K) V] where

  form : ∀ σ : K →+* ℂ, InnerProductSpace.Core ℂ (Fibre σ V)

  form_conj : ∀ (σ : K →+* ℂ) (x y : Fibre σ V),
    (form (conjugate σ)).inner (conjMap σ V x) (conjMap σ V y) = starRingEnd ℂ ((form σ).inner x y)

structure FullLattice (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] where

  carrier : Submodule (𝓞 K) V
  fg : carrier.FG
  span_eq : Submodule.span K (carrier : Set V) = ⊤

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [NumberField K] in
theorem isTorsionFree_of_vectorSpace : Module.IsTorsionFree (𝓞 K) V :=
  Module.IsTorsionFree.of_smul_eq_zero fun a x hax ↦ by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      have ha' : (a : K) ≠ 0 := by exact_mod_cast ha
      have : (a : K) • x = 0 := by rw [← hax]; exact algebraMap_smul K a x
      exact (smul_eq_zero.mp this).resolve_left ha'

def HermitianNorms.restrict (N : HermitianNorms K V) (L : Submodule (𝓞 K) V)
    [Module.Finite (𝓞 K) L] [Module.Projective (𝓞 K) L] : HermitianMetric K L :=
  let inclusion (σ : K →+* ℂ) : Fibre σ L →ₗ[ℂ] Fibre σ V :=
    { toFun := L.subtype.lTensor (ComplexAt σ)
      map_add' := map_add _
      map_smul' := lTensor_complex_smul σ L.subtype }
  have inclusion_injective (σ : K →+* ℂ) : Function.Injective (inclusion σ) :=
    Module.Flat.lTensor_preserves_injective_linearMap L.subtype L.injective_subtype
  have conj_inclusion (σ : K →+* ℂ) (x : Fibre σ L) :
      conjMap σ V (inclusion σ x) = inclusion (conjugate σ) (conjMap σ L x) := by
    induction x using TensorProduct.inductionOn with
    | tmul z x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  { form := fun σ ↦ coreComap (N.form σ) (inclusion σ) (inclusion_injective σ)
    form_conj := fun σ x y ↦ by
      rw [coreComap_inner, coreComap_inner, ← conj_inclusion, ← conj_inclusion, N.form_conj] }

namespace FullLattice

variable (L : FullLattice K V)

instance : Module.Finite (𝓞 K) L.carrier := Module.Finite.iff_fg.mpr L.fg

instance : Module.Projective (𝓞 K) L.carrier :=
  haveI : Module.IsTorsionFree (𝓞 K) V := isTorsionFree_of_vectorSpace
  projective_of_isTorsionFree _

end FullLattice

section Local

variable (v : HeightOneSpectrum (𝓞 K))

end Local

end

end GroundTheory.Heights₂.Heights
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocal =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
open GroundTheory.Heights₂.Heights

universe u v w

noncomputable section

def BaseChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type w) [Field L] [NumberField L] [Algebra K L]
    (M : HermitianBundle.{v} K), (M.baseChange L).deg = M.deg

section Witnesses

variable (K : Type u) [Field K] [NumberField K]


end Witnesses

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements =====
