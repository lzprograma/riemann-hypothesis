module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSmallRankStageHolds
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MassFormulaPositivity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingTripleSignature
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralVanishesOnFiniteRelations
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupFockOrbitFiniteDimensional, Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftVanishesOfIrreducibleDefect

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupFockOrbitFiniteDimensional =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupFockOrbitFiniteDimensional", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem\npublic import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MassFormulaPositivity\nimport Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle\nimport Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder\nimport Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver\nimport Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
open scoped ComplexOrder Matrix

namespace GlobalTheory.OneParamOrbit

theorem eps_true_of_posDef {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) (i : Fin X.rank) : B.ε τ i = true := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hinj : Function.Injective ((B.fr τ)⁻¹).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_nonsing_inv_iff).mpr (B.fr_unit τ))
  have hJ : ((B.fr τ)⁻¹)ᴴ * gramAt D X τ * (B.fr τ)⁻¹ = Formalism.REAL.Jm (B.ε τ) := by
    rw [← B.fr_gram τ]
    have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
    calc ((B.fr τ)⁻¹)ᴴ * ((B.fr τ)ᴴ * Formalism.REAL.Jm (B.ε τ) * B.fr τ) * (B.fr τ)⁻¹
        = (((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ) * Formalism.REAL.Jm (B.ε τ) * (B.fr τ * (B.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (B.ε τ) := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
  have hpos := (hG.conjTranspose_mul_mul_same hinj).diag_pos (i := i)
  rw [hJ] at hpos
  by_contra hne
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hne] at hpos
  norm_num at hpos

theorem conj_mem_Kset {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) {E : Matrix (Fin X.rank) (Fin X.rank) ℂ}
    (hE : Eᴴ * gramAt D X τ * E = gramAt D X τ) :
    B.fr τ * E * (B.fr τ)⁻¹ ∈ Formalism.REAL.Kset (B.ε τ) := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hJ1 : Formalism.REAL.Jm (B.ε τ) = 1 := by
    have : B.ε τ = fun _ => true := funext (eps_true_of_posDef B τ hG)
    rw [this]; simp [Formalism.REAL.Jm]
  have hgram : (B.fr τ)ᴴ * B.fr τ = gramAt D X τ := by
    rw [← B.fr_gram τ, hJ1, Matrix.mul_one]
  refine ⟨?_, by rw [hJ1, Matrix.mul_one, Matrix.one_mul]⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
  calc (B.fr τ * E * (B.fr τ)⁻¹)ᴴ * (B.fr τ * E * (B.fr τ)⁻¹)
      = ((B.fr τ)⁻¹)ᴴ * (Eᴴ * ((B.fr τ)ᴴ * B.fr τ) * E) * (B.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ * (B.fr τ * (B.fr τ)⁻¹) := by
        rw [hgram, hE, ← hgram]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem orbit_finiteDimensional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X),
    GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, ∃ a b : ℚ, HasInfExp D χ τ a ∧ HasInfExp D χ' τ b) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D X τ) X.rank 0) →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A B,
      ∃ V : Submodule ℂ (WO M X → ℂ), FiniteDimensional ℂ V ∧ ∀ t : ℝ, ω (1, oneP θ X τ Y t) Φ ∈ V := by
  intro D ψ θ _hψ hθ M X A B χ χ' ω hω hexp hsig τ Y hY Φ hΦ
  have hG : (gramAt D X τ).PosDef := GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hsig τ)
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    by_cases hf0 : f = 0
    · subst hf0
      have h0 : fockF ψ θ false A B 0 P = 0 := by
        have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ (GlobalTheory.Grid.sgn false M) X (frSgn false A).cart B.cart
          A.onb B.onb 0 0 P
        rwa [zero_smul, zero_smul] at this
      refine ⟨⊥, inferInstance, fun t => ?_⟩
      rw [h0, map_zero]; exact zero_mem _
    · obtain ⟨a, b, ha, hb⟩ := hexp τ
      obtain ⟨x, y, -, -, hK⟩ := GlobalTheory.CompactFockAction.compactFockAll D (GlobalTheory.Grid.sgn false M) X
        (frSgn false A) B θ ψ χ χ' (ω.toSgn false) f τ a b hθ hω ha hb hf hf0
      refine ⟨(MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (fockF ψ θ false A B f),
        inferInstance, fun t => ?_⟩
      have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
      have hE : (NormedSpace.exp (t • Y))ᴴ * gramAt D X τ * NormedSpace.exp (t • Y) = gramAt D X τ :=
        GlobalTheory.SmoothAutCheck.exp_mem_UH (Matrix.isUnit_iff_isUnit_det _ |>.mp hG.isUnit) hY t
      have hk := conj_mem_Kset B τ hG hE
      have hA1 : (frSgn false A).elt θ τ 1 = 1 := by
        have hAu : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (A.fr_unit τ)
        show atTau θ _ τ ((A.fr τ)⁻¹ * 1 * A.fr τ) = 1
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hAu]
        exact GlobalTheory.PointAtPlaceHom.atTau_one hθ _ τ
      have hBk : B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) = oneP θ X τ Y t := by
        show atTau θ X τ ((B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ) = _
        rw [show (B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ
            = ((B.fr τ)⁻¹ * B.fr τ) * NormedSpace.exp (t • Y) * ((B.fr τ)⁻¹ * B.fr τ) by
              simp only [Matrix.mul_assoc],
          Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]
        rfl
      have hω1 : ω (1, oneP θ X τ Y t)
          = (ω.toSgn false) ((frSgn false A).elt θ τ 1, B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹)) := by
        rw [hA1, hBk]
        show ω (1, _) = ω ((GlobalTheory.Grid.ofSgn false M) 1, _)
        rw [map_one]
      have key := hK 1 (_root_.GlobalTheory.SourceOperatorLemmas.one_mem_K _) _ hk P
      have hfock : fockF ψ θ false A B f P = GlobalTheory.ChainFr.ptF ψ θ (frSgn false A) B f P := rfl
      rw [hfock, hω1, key]
      refine Submodule.smul_mem _ _ ⟨_, (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _), rfl⟩
  | zero => exact ⟨⊥, inferInstance, fun t => by rw [map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨V₁, h₁, hV₁⟩ := hx
    obtain ⟨V₂, h₂, hV₂⟩ := hy
    exact ⟨V₁ ⊔ V₂, Submodule.finiteDimensional_sup V₁ V₂, fun t => by
      rw [map_add]; exact add_mem (Submodule.mem_sup_left (hV₁ t)) (Submodule.mem_sup_right (hV₂ t))⟩
  | smul c x _ hx =>
    obtain ⟨V, h, hV⟩ := hx
    exact ⟨V, h, fun t => by rw [map_smul]; exact Submodule.smul_mem _ _ (hV t)⟩

end GlobalTheory.OneParamOrbit
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupFockOrbitFiniteDimensional =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftVanishesOfIrreducibleDefect =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftVanishesOfIrreducibleDefect", "h": "module\n\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible\npublic import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingTripleSignature\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupFockOrbitFiniteDimensional\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralVanishesOnFiniteRelations\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.Finiteness.ModuleFinitePresentation\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Std.Tactic.BVDecide.Normalize.Prop\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle\nimport Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver\nimport Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall\n\n"}
section -- clump:auto
@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.DefIrred
theorem theta_vanish_all_of_irreducible : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) W.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D X τ) X.rank 0) → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ → ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ Φ' ∈ algF ψ θ false A₁ B, p' Φ' ≠ 0 → thetaInt ωB ν₁ 𝓕₁ Φ' = 0 → ∀ Φ'' ∈ algF ψ θ false A₁ B, thetaInt ωB ν₁ 𝓕₁ Φ'' = 0 :=
  fun _ hP hTK hLM _ D ψ θ hψ hθ W W₁ X A A₁ B α β hT _ hs₁ _ ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm Φ₁ hΦ₁ hp₁ hz₁ Φ₂ hΦ₂ =>
    _root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible hP hTK hLM D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm Φ₁ hΦ₁ hp₁ hz₁ Φ₂ hΦ₂
end GlobalTheory.DefIrred
end
end

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftVanishesOfIrreducibleDefect =====
