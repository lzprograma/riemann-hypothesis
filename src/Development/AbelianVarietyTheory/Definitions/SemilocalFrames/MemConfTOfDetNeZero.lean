module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Partners, Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Partners =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Partners", "h": "module\n\npublic import Mathlib.Algebra.BigOperators.Group.Finset.Defs\npublic import Mathlib.Basic.Real.Basic\npublic import Mathlib.Order.Interval.Finset.Nat\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq\npublic import Mathlib.Algebra.Algebra.Defs\npublic import Mathlib.MeasureTheory.MeasurableSpace.Defs\npublic import Mathlib.RingTheory.Valuation.ValuativeRel.Basic\npublic import Mathlib.Topology.Defs.Basic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc Matrix

namespace GlobalTheory.SgDen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]


def densF (q : ℕ) (η : ℝ) (n a c : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc (n + 1 - a - c) n, (1 - (η * (q : ℝ)⁻¹) ^ i)

variable [MeasurableSpace E]


end GlobalTheory.SgDen
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Partners =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Partners\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats\npublic import Formalism.FormalDegreeBessel.StatementBF\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\nimport Mathlib.Algebra.AffineMonoid.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\npublic import Mathlib.RingTheory.Ideal.Norm.RelNorm\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Formalism.SharpRestriction.CuspSpanNormBounds.Point\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass

abbrev HCo (a : ℕ) : Type := (Fin a → ℝ) × ({p : Fin a × Fin a // p.1 < p.2} → ℂ)

def hOf {a : ℕ} (t : HCo a) : Matrix (Fin a) (Fin a) ℂ := fun i j =>
  if h : i < j then t.2 ⟨(i, j), h⟩ else if h' : j < i then star (t.2 ⟨(j, i), h'⟩) else (t.1 i : ℂ)

abbrev Tup (k r a : ℕ) : Type := Fin (2 * r + k + 1) → Fin a → ℂ

def gramC {k r a : ℕ} (X : Tup k r a) : Matrix (Fin a) (Fin a) ℂ :=
  (Matrix.of X)ᴴ * Hpk k r * Matrix.of X

section Glob

variable {E : Type} [Field E] [NumberField E]

def tupLat {n a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E) (P : Matrix (Fin n) (Fin a) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin a) (x : E), x ∈ 𝔞 b ∧ v = x • fun i => P i b}

def dualM (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E) (T : Matrix (Fin a) (Fin a) E) :
    Submodule (𝓞 E) (Fin a → E) :=
  Submodule.span (𝓞 E) {x | ∀ y ∈ tupLat 𝔞 (1 : Matrix (Fin a) (Fin a) E),
    form σ T x y ∈ (algebraMap (𝓞 E) E).range}

variable {F : Type} [Field F] [NumberField F] [Algebra F E]


open scoped Classical in
def eta₃ (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if (v.asIdeal.primesOver (𝓞 E)).ncard = 2 then 1 else -1

def StdAt (v : HeightOneSpectrum (𝓞 F)) (ψ : Fv F v → ℂ) : Prop :=
  ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔
    ∀ d ∈ differentIdeal ℤ (𝓞 F), x * algebraMap F (Fv F v) (d : F) ∈ v.adicCompletionIntegers F

def IsStdChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) : Prop :=
  IsCharAF F ψ ∧ (∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))) ∧
    ∀ v, StdAt v (psiV F ψ v)

variable (σ : E →ₐ[F] E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)

def IsModelAt (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ w, (A w)ᴴ * Hpk k r * A w = J.map w.embedding

end Glob

end GlobalTheory.SnMass
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero =====
