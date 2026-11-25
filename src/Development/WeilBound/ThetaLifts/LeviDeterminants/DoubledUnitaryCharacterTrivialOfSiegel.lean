module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FiniteNonunitMatrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
public import Mathlib.RingTheory.TensorProduct.Pi
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegelStatement

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmAlgebraSplitInvolution, Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianDarbouxSplitProduct, Development.WeilBound.ThetaLifts.LeviDeterminants.DoubledUnitaryCharacterTrivialOfSiegel

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmAlgebraSplitInvolution =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmAlgebraSplitInvolution", "h": "module\n\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver\nimport Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FiniteNonunitMatrix\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Matrix
open scoped NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.ArchRing

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


end GlobalTheory.CompanionTheory.Ar.RT.ArchRing
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmAlgebraSplitInvolution =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianDarbouxSplitProduct =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianDarbouxSplitProduct", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff\npublic import Mathlib.Analysis.CStarAlgebra.CStarMatrix\npublic import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FiniteNonunitMatrix\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.Ar.RT.CellSplit

open GlobalTheory.WeilM

section Lift

variable {S E₁ E₂ : Type} [CommRing S] [CommRing E₁] [CommRing E₂] (s : S ≃+* E₁ × E₂)

variable {n : Type} [DecidableEq n]

def lift (x : Matrix n n E₁) : Matrix n n S :=
  Matrix.of fun i j => s.symm (x i j, (1 : Matrix n n E₂) i j)

theorem map_one' {T : Type} [CommRing T] (f : S →+* T) : (1 : Matrix n n S).map f = 1 := by
  exact Matrix.map_one f (map_zero f) (map_one f)

variable [Fintype n]

end Lift

section Unitary

variable {k R S E₁ E₂ : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra R S] [CommRing E₁] [Algebra k E₁] [CommRing E₂]
  (c : S →ₐ[R] S) (c₁ : E₁ →ₐ[k] E₁) (c₂ : E₂ →+* E₂) (s : S ≃+* E₁ × E₂)
  (hc1 : ∀ x, (s (c x)).1 = c₁ (s x).1) (hc2 : ∀ x, (s (c x)).2 = c₂ (s x).2)

variable {β : Type} [Fintype β] [DecidableEq β] (J : Matrix β β S)

end Unitary

end GlobalTheory.CompanionTheory.Ar.RT.CellSplit
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianDarbouxSplitProduct =====

-- ===== clump member: Development.WeilBound.ThetaLifts.LeviDeterminants.DoubledUnitaryCharacterTrivialOfSiegel =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.LeviDeterminants.DoubledUnitaryCharacterTrivialOfSiegel", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal\npublic import Mathlib.RingTheory.TensorProduct.Pi\npublic import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmAlgebraSplitInvolution\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff\npublic import Mathlib.Analysis.CStarAlgebra.CStarMatrix\npublic import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianDarbouxSplitProduct\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegelStatement\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

noncomputable section

namespace PositivityTheory.ThKF0.Sg

section Split

variable {F A R₁ R₂ : Type} (E : Type) [Field F] [CommRing A] [Algebra F A] [CommRing R₁] [Algebra F R₁] [CommRing R₂]
  [Algebra F R₂] [CommRing E] [Algebra F E]

def split (s : A ≃ₐ[F] R₁ × R₂) : A ⊗[F] E ≃ₐ[F] (R₁ ⊗[F] E) × (R₂ ⊗[F] E) :=
  (Algebra.TensorProduct.congr s AlgEquiv.refl).trans
    (((Algebra.TensorProduct.comm F (R₁ × R₂) E).trans (Algebra.TensorProduct.prodRight F F E R₁ R₂)).trans
      (AlgEquiv.prodCongr (Algebra.TensorProduct.comm F E R₁) (Algebra.TensorProduct.comm F E R₂)))

variable {E}

end Split

section Piece

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {c : S →ₐ[R] S} {ι : Type} [Fintype ι] [DecidableEq ι]

end Piece

variable {F : Type} [Field F] [NumberField F]

open GlobalTheory.LocalGlobalChar


variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.ThKF0.Sg

open PositivityTheory.ThKF0.Sg GlobalTheory.LocalGlobalChar in
theorem PositivityTheory.ThKF0.parabolic_character_trivial_on_diagonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1 :=
  _root_.GlobalTheory.T.doubledUnitary_character_trivial_of_siegel

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.LeviDeterminants.DoubledUnitaryCharacterTrivialOfSiegel =====
