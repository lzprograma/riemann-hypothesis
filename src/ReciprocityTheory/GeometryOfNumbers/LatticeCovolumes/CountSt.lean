module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidSt
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStB
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStC, ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt

-- ===== clump member: ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStC =====
-- clump-header: {"m": "ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStC", "h": "module\n\npublic import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic\npublic import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm\npublic import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidSt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def gramR (h : HermFam K V) {r : ℕ} (v : Fin r → V)
    (w : {w : InfinitePlace K // w.IsReal}) : Matrix (Fin r) (Fin r) ℝ :=
  (h.gram w.1.embedding v).map Complex.re

def psi (K : Type*) [Field K] [NumberField K] (r : ℕ) (y : Fin r → mixedEmbedding.mixedSpace K) :
    ({w : InfinitePlace K // w.IsReal} → Fin r → ℝ) × ({w : InfinitePlace K // w.IsComplex} → Fin r → ℂ) :=
  (fun w i => (y i).1 w, fun w i => (y i).2 w)

end ReciprocityTheory.GeometryOfNumbersTheory

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]

def ellT (h : HermFam K V) {r : ℕ} (v : Fin r → V) (R : ℝ) :
    Set (({w : InfinitePlace K // w.IsReal} → Fin r → ℝ) ×
      ({w : InfinitePlace K // w.IsComplex} → Fin r → ℂ)) :=
  (Set.pi univ fun w => {u | qR (gramR h v w) u ≤ R ^ 2}) ×ˢ
    (Set.pi univ fun w : {w : InfinitePlace K // w.IsComplex} =>
      {u | qC (h.gram w.1.embedding v) u ≤ R ^ 2})

def psiL (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    (Fin r → mixedEmbedding.mixedSpace K) →ₗ[ℝ]
      (({w : InfinitePlace K // w.IsReal} → Fin r → ℝ) ×
        ({w : InfinitePlace K // w.IsComplex} → Fin r → ℂ)) where
  toFun := psi K r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ReciprocityTheory.GeometryOfNumbersTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStC =====

-- ===== clump member: ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt =====
-- clump-header: {"m": "ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt", "h": "module\n\npublic import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStC\npublic import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStB\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder
open MeasureTheory

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def HermFam.IsConjInv (h : HermFam K V) : Prop :=
  ∀ (σ : K →+* ℂ) (x y : V),
    h.form (ComplexEmbedding.conjugate σ) x y = starRingEnd ℂ (h.form σ x y)

theorem det_gram_conj_re (h : HermFam K V) (hinv : h.IsConjInv) (σ : K →+* ℂ) {r : ℕ}
    (v : Fin r → V) :
    (h.gram (ComplexEmbedding.conjugate σ) v).det.re = (h.gram σ v).det.re := by
  have hg : h.gram (ComplexEmbedding.conjugate σ) v = (h.gram σ v).map (starRingEnd ℂ) := by
    ext i j
    simp only [HermFam.gram, Matrix.map_apply, Matrix.of_apply]
    exact hinv σ (v i) (v j)
  rw [hg, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_re]

end ReciprocityTheory.GeometryOfNumbersTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt =====
