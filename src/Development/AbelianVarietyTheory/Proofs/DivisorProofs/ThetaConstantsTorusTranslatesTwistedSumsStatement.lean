module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityFractionFieldMemberEqZetaPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFraStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsYy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShiftStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemThetaConstantNegEvenUpToRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermsEqUpToNormalisingThetaConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionTorusExtensionRespectCubicalStatement
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndependentMember, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSumsStatement

@[expose] public noncomputable section

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndependentMember =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndependentMember", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermsDividingLabelGroupMemberStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaModelPointStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistWeightWellDefinedOnLatticeClassStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsAffineTwoMembersStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaPowerResidueDividingLabelStatement\n\n"}
namespace GlobalTheory.Poinc.Sep.TwistIndep

theorem affine_zero {G : Type} [AddCommGroup G] {M : ℕ} (hM : Odd M) (S : Set G) (hS : ∀ s ∈ S, -s ∈ S)
    (hne : S.Nonempty) (κ : ZMod M) (h : AddSubgroup.closure S →+ ZMod M)
    (hz : ∀ s (hs : s ∈ S), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0) :
    ∀ a (ha : a ∈ AddSubgroup.closure S), κ + h ⟨a, ha⟩ = 0 := by
  obtain ⟨s₀, hs₀⟩ := hne
  have h2 := hz (-s₀) (hS s₀ hs₀)
  rw [show (⟨-s₀, AddSubgroup.subset_closure (hS s₀ hs₀)⟩ : AddSubgroup.closure S) =
      -⟨s₀, AddSubgroup.subset_closure hs₀⟩ from rfl, map_neg] at h2
  have hu : IsUnit (2 : ZMod M) := by
    have := (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.2 hM)).isUnit
    rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
  obtain rfl : κ = 0 := hu.mul_right_eq_zero.1 (by linear_combination hz s₀ hs₀ + h2)
  intro a ha; rw [zero_add]
  refine AddSubgroup.closure_induction (p := fun x hx => h ⟨x, hx⟩ = 0)
    (fun x hx => by simpa using hz x hx) (map_zero h)
    (fun x y hx hy h1 h2 => by
      rw [show (⟨x + y, add_mem hx hy⟩ : AddSubgroup.closure S) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add (f := _), h1, h2, add_zero])
    (fun x hx h1 => by
      rw [show (⟨-x, neg_mem hx⟩ : AddSubgroup.closure S) = -⟨x, hx⟩ from rfl, map_neg, h1, neg_zero]) ha

end GlobalTheory.Poinc.Sep.TwistIndep
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndependentMember =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSumsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSumsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSums\n\n"}
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSumsStatement =====
