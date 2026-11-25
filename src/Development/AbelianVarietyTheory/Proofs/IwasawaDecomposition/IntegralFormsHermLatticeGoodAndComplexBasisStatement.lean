module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasisStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining\npublic import Formalism.LocalToGlobal.Columns.ToHLatLemmas\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

theorem toCx_smul {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (c : B.LL) (x : (MtHL I hX a).V) :
    toCx I hX a (c • x) = B.embLL c • toCx I hX a x := by
  have h1 : toCx I hX a (c • x) = toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL
      (c • (show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from x)) := rfl
  rw [h1, LinearMap.map_smulₛₗ]
  rfl

theorem toCx_add {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x y : (MtHL I hX a).V) :
    toCx I hX a (x + y) = toCx I hX a x + toCx I hX a y := by
  have h1 : toCx I hX a (x + y) = toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL
      ((show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from x) + (show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from y)) := rfl
  rw [h1, map_add (f := _)]
  rfl

noncomputable def toCxₛₗ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a where
  toFun := toCx I hX a
  map_add' := toCx_add I hX a
  map_smul' := toCx_smul I hX a

theorem toCx_linearIndependent {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) :
    LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) :=
  toMtilde_linearIndependent _ _ _ _ _ _ (MtHL I hX a).b.linearIndependent

theorem toCx_span {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) :
    Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  rw [eq_top_iff, ← toMtilde_span B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL hX, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have hle : Submodule.span B.LL (Set.range (MtHL I hX a).b) ≤
      Submodule.comap (toCxₛₗ I hX a) (Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [(MtHL I hX a).b.span_eq] at hle
  exact hle (Submodule.mem_top (x := (x : (MtHL I hX a).V)))

end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

theorem mtHL_good {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) : (MtHL I hX a).Good :=
  MtildeH_good _ _ _ _ _ _
end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

theorem mtHL_good_basis : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι), (MtHL I hX a).Good ∧ (∃ j : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a, ∀ x, j x = toCx I hX a x) ∧ LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) ∧ Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  intro B X I hX a
  refine ⟨?_, ⟨{ toFun := toCx I hX a, map_add' := fun x y => ?_, map_smul' := fun c x => ?_ }, fun _ => rfl⟩,
    toCx_linearIndependent I hX a, toCx_span I hX a⟩
  · exact mtHL_good I hX a
  · exact toCx_add I hX a x y
  · exact toCx_smul I hX a c x

end GlobalTheory.Mem.Df
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasisStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasisStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasisStatement =====
