module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSumsStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigTorsFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusCharOfLabelOrthogonalDividing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedAdicSumTermsOfFractionFieldSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemThetaConstantNegEvenUpToRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotTwistSumZeroFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermNonzeroIndexMemMaximalIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTwistWeightWellDefinedLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsDividingGroupLabelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsDifferAffineTwoMembersStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsion
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NsmulEqZeroOfCast
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsYyAlt, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCharEqWeilGen, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMember, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMemberStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystem, Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystemStatement, Development.AbelianVarietyTheory.Definitions.Divisors.IsMemberPOfIsMember, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioMod, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioModStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabel, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabelStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMember, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMemberStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSums, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSumsStatement

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsYyAlt =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsYyAlt", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing\n\n"}
namespace GlobalTheory.GSep.GMem

theorem exists_yy : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (mu : X), ∃ a : X₁.S.Gam, 𝔪.YY a mu := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 mu
  have : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; lia)
  obtain ⟨h, hh⟩ := GlobalTheory.TorusExt.exists_iota (F := AlgebraicClosure (FractionRing V)) 𝔪.D.tau_bimult (𝔪.e₈ mu)
  obtain ⟨g', hg'⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D
    (AlgebraicClosure (FractionRing V))).2.1 _ hk h
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) := ⟨𝔪.e₈ mu, g', h, hg', hh⟩
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk
  have hx := (hf p (f p)).2 rfl
  obtain ⟨w, hw⟩ := 𝔪.U.ext
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _
    (pushHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V))) (f p))
    (by rw [← map_pow, (hx w hw).1, map_one])
  refine ⟨a, p, f p, rfl, hx, ?_⟩
  have e := congrArg Over.Hom.left ha
  simp only [Over.comp_left, Over.homMk_left] at e
  rw [show spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) =
    jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ spMap 𝔪.yK by simp [spMap, jFK, ← Spec.map_comp]]
  exact e.symm

end GlobalTheory.GSep.GMem
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsYyAlt =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCharEqWeilGen =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCharEqWeilGen", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP\npublic import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration\nimport Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs\nimport Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural\nimport Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsion\nimport Mathlib.Tactic.Linter.Style\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc\n\n"}
namespace GlobalTheory.GSep

open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

theorem torusChar_eq_weil_gen : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) := by
  refine fun I X₁ z₁ act => ⟨1, fun V _ _ _ ev X _ t δ 𝔪 τ χ hχ hpt a mu hY => ?_⟩
  have : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; lia)
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) := by simp [Algebra.algebraMap_self]
  obtain ⟨p, x, hpy, hpg, hpx, hxo⟩ := hpt (torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ))
    ((isTor_iff _ _).2 (isTorusPtF_torusPt χ))
  obtain ⟨p', x', hp'y, hp'x, hx'o⟩ := hY
  obtain ⟨p₁, hext, -⟩ := existsUnique_qkExt 𝔪.D.tau_bimult (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf p
  set χ₁ : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ :=
    (Units.map (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).toMonoidHom).comp χ with hχ₁
  have hp₁g : p₁.g = torusPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (Additive.ofMul χ₁) := by
    rw [(eq_gtExt_iff _ hf _ _).2 hext.2, hpg]; exact gtExt_torusPt _ hf χ
  have W₁ := weilQkIs_tor hG p₁ p' (hext.1.trans hpy) (by rw [hp₁g]; exact (isTor_iff _ _).2 (isTorusPtF_torusPt χ₁))
  have W₂ := (GlobalTheory.UT.weilQkIs_iff_weilIs hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk p₁ p' _ x'
    ((qkToAkU_iff_of_algebra hG hL.1.kerPow 𝔪.U hk hext x).1 hpx) hp'x (χ₁ (Multiplicative.ofAdd p'.y))).1 W₁
  have := X₁.ρ.P.isAb.comm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := (spMap_comp _ _).symm
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom
    ((X₁.S.prim.pow (pow_pos hk 2) (pow_two _)).isUnit (by lia)).unit
  have W₃ := (_root_.GlobalTheory.weilIs_grpPullback_of_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩
    (TFK (R := V) (AlgebraicClosure (FractionRing V))) _
    (fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x) x' (h ≫ X₁.ρ.pt τ) (h ≫ X₁.ρ.pt a) _
    (by show h.left ≫ (X₁.ρ.pt τ).left = _; rw [Over.comp_left, Category.assoc, hxo]; rfl)
    (by show h.left ≫ (X₁.ρ.pt a).left = _; rw [hx'o, hh])).2
    (GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h
      (X₁.ρ.weil τ a (c₀ ^ (eStd X₁.S.g _ τ a).val) (by rw [pow_mul, map_pow]; rfl)))
  rw [hh, map_unitOn] at W₃
  have e := congrArg Units.val (unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB W₂ W₃))
  simp only [hp'y, hχ₁, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe,
    RingHom.coe_comp, Function.comp_apply, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec] at e
  rw [Units.val_one, one_smul]
  refine (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective ?_
  rw [e]; simp only [pow_mul, ← map_pow]

end GlobalTheory.GSep
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCharEqWeilGen =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMember =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMember", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigTorsFrame\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusCharOfLabelOrthogonalDividing\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsYyAlt\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCharEqWeilGen\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedAdicSumTermsOfFractionFieldSum\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero\n\n"}
theorem GlobalTheory.GSep.twistAtEach_exists : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  intro I X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg⟩ := GlobalTheory.GSep.torusChar_eq_weil_gen I X₁ z₁ act
  refine ⟨sg, fun V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c τ hτ => ?_, hsg⟩
  obtain ⟨χ, hχN, hχo⟩ := GlobalTheory.GSep.TorPt.exists_torus_char I X₁ z₁ act V ev X t δ 𝔪 τ hτ
  obtain ⟨e, he⟩ := GlobalTheory.GSep.TwistTranslate.twistSum_translate I X₁ z₁ act V ev X t δ 𝔪 x₀ C lab hlab T hT c τ hτ χ hχN hχo
  exact ⟨e, GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF I X₁ z₁ act V ev X t δ 𝔪 x₀ C lab T sg c τ χ e
    (GlobalTheory.GSep.GMem.yK_th_ne_zero I X₁ z₁ act V ev X t δ 𝔪 x₀ hdiv)
    (GlobalTheory.GSep.GMem.exists_yy I X₁ z₁ act V ev X t δ 𝔪) (hsg V ev X t δ 𝔪 τ χ hχN hχo) he⟩
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMember =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMemberStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMemberStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMember\n\n"}
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMemberStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystem =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystem", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP\nimport Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NsmulEqZeroOfCast\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemThetaConstantNegEvenUpToRoot\n\n"}
namespace GlobalTheory.GSep.SupISymm

theorem exists_unit_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    {c ε : Ω} (hc : c ^ 2 = 1) (hε : ε ^ ((S.r * S.N) ^ 2) = 1) : ∃ u : oˣ, c * ε = algebraMap o Ω (u : o) := by
  obtain ⟨k, -, hk⟩ := (S.prim.map_of_injective ArithBase.inj).eq_pow_of_pow_eq_one hε
  have hζu : IsUnit S.ζ := S.prim.isUnit (by have := S.r_pos; have := S.N_ge; positivity)
  have hc' : c * c = 1 := by rw [← sq]; exact hc
  rcases mul_self_eq_one_iff.1 hc' with rfl | rfl
  · exact ⟨hζu.unit ^ k, by simp [← hk, map_pow]⟩
  · exact ⟨-(hζu.unit ^ k), by simp [← hk, map_pow]⟩

theorem exists_unit_th_neg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a) (a : S.Gam) :
    ∃ u : oˣ, S.th (-a) = algebraMap o Ω (u : o) * S.th a := by
  obtain ⟨c, ε, hc, hε, h⟩ := H a
  obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one S hc hε
  exact ⟨u, by rw [h, hu]⟩

theorem neg_mem_supI_of_parity {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a)
    (z : M.Z) (a : S.Gam) (ha : a ∈ S.supI M z) : -a ∈ S.supI M z := by
  obtain ⟨u, hu⟩ := exists_unit_th_neg S H a
  refine ⟨by rw [hu]; exact mul_ne_zero (u.isUnit.map _).ne_zero ha.1, fun j => ?_⟩
  obtain ⟨v, hv⟩ := exists_unit_th_neg S H (-j)
  rw [neg_neg] at hv
  have hi : algebraMap o Ω ((u⁻¹ : oˣ) : o) = (algebraMap o Ω (u : o))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
  rw [show S.th j / S.th (-a) = algebraMap o Ω ((v : o) * ((u⁻¹ : oˣ) : o)) * (S.th (-j) / S.th a) by
    rw [hv, hu, map_mul, hi]; field_simp]
  exact (M.O z).mul_mem (Subalgebra.algebraMap_mem _ _) (ha.2 (-j))

end GlobalTheory.GSep.SupISymm

theorem GlobalTheory.GSep.neg_mem_supI : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ :=
  fun X₁ z₁ a => GlobalTheory.GSep.SupISymm.neg_mem_supI_of_parity X₁.S X₁.M
    (GlobalTheory.ThetaParity.theta_neg X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ) z₁ a
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystem =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystemStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystemStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystem\n\n"}
theorem _root_.GlobalTheory.T.neg_mem_dividingLabels_thetaSystem : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ :=
  GlobalTheory.GSep.neg_mem_supI
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystemStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.Divisors.IsMemberPOfIsMember =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.Divisors.IsMemberPOfIsMember", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP\n\n"}
namespace GlobalTheory.GSep.MemberModel

section
variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {L : Type} [AddCommGroup L] {mo : L → V} {hL : I → L → L}

theorem terms_sum (𝔪 : GMem X₁ z₁ act V ev L mo hL) {x₀ : X₁.S.Gam} {C : Type} {lab : C → X₁.S.Gam}
    {T : L → C → V} (h : 𝔪.Terms x₀ lab T) (c : C) :
    SumF (maximalIdeal V) (FractionRing V)
      (fun χ => algebraMap V (FractionRing V) (T (𝔪.e₈.symm χ) c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)
      (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩) := by
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hs, hc, hT⟩ := h
  have := (hc c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hc c).2.1 th s _ hs (hth (lab c))
  convert this using 2 with χ
  rw [hT, AddEquiv.apply_symm_apply]
end

end GlobalTheory.GSep.MemberModel
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.Divisors.IsMemberPOfIsMember =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioMod =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioMod", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsMemberPOfIsMember\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.NotTwistSumZeroFamily\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermNonzeroIndexMemMaximalIdealStatement\n\n"}
namespace GlobalTheory.GSep.ConstTerm

theorem sub_mem_of_sumI {V Ix : Type} [CommRing V] {I : Ideal V} {y : Ix → V} {v : V} (h : SumI I y v) (i₀ : Ix)
    (hy : ∀ j, j ≠ i₀ → y j ∈ I) : v - y i₀ ∈ I := by
  classical
  obtain ⟨N, -, -, -, hS⟩ := h
  obtain ⟨S, hS⟩ := hS 1
  have h1 := Submodule.smul_mono le_rfl (le_top : N ≤ ⊤) (hS (insert i₀ S) (Finset.subset_insert _ _))
  rw [pow_one, smul_eq_mul, Ideal.mul_top, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S)] at h1
  have h2 : ∑ j ∈ (insert i₀ S).erase i₀, y j ∈ I :=
    Submodule.sum_mem _ fun j hj => hy j (Finset.ne_of_mem_erase hj)
  have := add_mem h1 h2
  convert this using 1; ring

theorem const_term_sub_mem : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (r : X₁.M.Z.presheaf.stalk z₁), X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ → ev1 r - T 0 c ∈ maximalIdeal V1 := by
  intro I X₁ z₁ act x₀ hd V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c r hr
  have : IsNoetherianRing V := 𝔪.cn.1
  have : IsLocalHom ev := 𝔪.loc
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)))
    (by have : X₁.M.Z.fromSpecStalk z₁ ((jK V ≫ spMap ev) (closedPoint (FractionRing V))) ∈
          Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨_, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at this)
  have e := RatModel.val_mul (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _))
    (hd'.2 (lab c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1, ← hr, GlobalTheory.GSep.TwistModel.val_stalkHom] at e
  have hS := GlobalTheory.GSep.MemberModel.terms_sum 𝔪 hT c
  rw [show 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ =
    algebraMap V (FractionRing V) (ev r) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ by rw [𝔪.yK_eq, 𝔪.yK_eq, e]] at hS
  have hI := GlobalTheory.Poinc.TwistSum₂.sumI_of_sumF_mul (fun χ => T (𝔪.e₈.symm χ) c) (ev r) _
    (GlobalTheory.GSep.TwistModel.yK_th_ne_zero 𝔪 hd) hS
  simpa only [map_zero] using sub_mem_of_sumI hI 0 fun j hj =>
    GlobalTheory.T.thetaMember_term_nonzero_index_mem_maximalIdeal I X₁ z₁ act x₀ hd V ev X t δ 𝔪 C lab hlab T hT c _
      (𝔪.e₈.symm.map_ne_zero_iff.2 hj)

end GlobalTheory.GSep.ConstTerm
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioMod =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioModStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioModStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioMod\n\n"}
theorem _root_.GlobalTheory.T.thetaMember_index_zero_term_eq_theta_ratio_mod : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (r : X₁.M.Z.presheaf.stalk z₁), X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ → ev1 r - T 0 c ∈ maximalIdeal V1 :=
  GlobalTheory.GSep.ConstTerm.const_term_sub_mem
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioModStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabel =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabel", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZeroStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioModStatement\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermNonzeroIndexMemMaximalIdealStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTwistWeightWellDefinedLatticeStatement\n\n"}
namespace GlobalTheory.GSep.TwistResid

theorem twist_resid : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), lab c ∈ X₁.S.supI X₁.M z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ (sg : ℤˣ) (e : ℕ), GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ e → ∀ s u : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) → X₁.M.stalkHom z₁ u = X₁.S.th (lab c + τ) / X₁.S.th (lab c) → ev1 (s * u) - 1 ∈ maximalIdeal V1 := by
  classical
  intro I X₁ z₁ act x₀ hx₀ V _ _ _ ev Y _ t δ 𝔪 C lab hlab T hT c hc τ hτ sg e hTw s u hs hu
  let r := (X₁.M.stalkEquiv z₁).symm ⟨_, hx₀.2 (lab c)⟩
  have hr : X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ := by
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  have hrU : IsUnit r := ((RatModel.isUnit_O_iff (⟨_, hx₀.2 (lab c)⟩ : X₁.M.O z₁)).2
    ⟨div_ne_zero hc.1 hx₀.1, by rw [inv_div]; exact hc.2 x₀⟩).map (X₁.M.stalkEquiv z₁).symm
  obtain ⟨zt, hs'⟩ := (X₁.M.stalkEquiv z₁).surjective
    ⟨algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)), Subalgebra.algebraMap_mem _ _⟩
  have hzt : X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) := by
    rw [← RatModel.coe_stalkEquiv, hs']
  obtain ⟨wt, hwt⟩ := GlobalTheory.T.thetaMember_twist_weight_wellDefined_lattice I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 sg τ hτ
  let wt' : Y → ZMod (X₁.S.r * X₁.S.N) := fun mu => if mu = 0 then 0 else wt mu
  have hwt' : ∀ a mu, 𝔪.YY a mu → wt' mu = (sg : ℤ) • eStd X₁.S.g _ τ a := fun a mu h => by
    by_cases h0 : mu = 0
    · subst h0
      simp only [wt', ite_true, hτ a ((_root_.GlobalTheory.GSep.mem_HH_iff_yy_zero I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 a).2 h), smul_zero]
    · simp only [wt', ite_eq_right h0]; exact hwt a mu h
  obtain ⟨N, -, -, -, hN⟩ := hTw zt (s * u * r) hzt
    (by rw [map_mul, map_mul, hs, hu, hr]; field_simp [hc.1, hx₀.1]) wt' hwt'
  obtain ⟨S, hS⟩ := hN 1
  have h2 := Submodule.smul_mono le_rfl (le_top : N ≤ ⊤) (hS (insert 0 S) (Finset.subset_insert _ _))
  rw [pow_one, smul_eq_mul, Ideal.mul_top, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self 0 S),
    show ev zt ^ (wt' 0).val * T 0 c = T 0 c by simp [wt']] at h2
  have h3 : ∑ mu ∈ (insert 0 S).erase 0, ev zt ^ (wt' mu).val * T mu c ∈ maximalIdeal V :=
    Ideal.sum_mem _ fun mu hmu => Ideal.mul_mem_left _ _
      (GlobalTheory.T.thetaMember_term_nonzero_index_mem_maximalIdeal I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 C lab hlab T hT c mu (Finset.ne_of_mem_erase hmu))
  have h4 : ev (s * u * r) - T 0 c ∈ maximalIdeal V := by
    simpa [sub_add_eq_sub_sub, sub_add_cancel] using Ideal.add_mem _ h2 h3
  have h5 := GlobalTheory.T.thetaMember_index_zero_term_eq_theta_ratio_mod I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 C lab hlab T hT c r hr
  exact (Ideal.mul_unit_mem_iff_mem _ (hrU.map ev)).1 (by
    have := Ideal.sub_mem _ h4 h5; rw [map_mul] at this; convert this using 1; ring)

end GlobalTheory.GSep.TwistResid
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabel =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabelStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabelStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabel\n\n"}
theorem _root_.GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), lab c ∈ X₁.S.supI X₁.M z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ (sg : ℤˣ) (e : ℕ), GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ e → ∀ s u : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) → X₁.M.stalkHom z₁ u = X₁.S.th (lab c + τ) / X₁.S.th (lab c) → ev1 (s * u) - 1 ∈ maximalIdeal V1 :=
  GlobalTheory.GSep.TwistResid.twist_resid
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabelStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMember =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMember", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaSystemStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsDividingGroupLabelStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTwistWeightWellDefinedLatticeStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsDifferAffineTwoMembersStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabelStatement\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus\n\n"}
namespace GlobalTheory.GSep.TwistIndep

theorem isUnit_one_sub_pow {o : Type} [CommRing o] [IsDomain o] {ζ : o} {M : ℕ} (hζ : IsPrimitiveRoot ζ M)
    (hM : IsUnit (M : o)) {d : ℕ} (hd : ζ ^ d ≠ 1) : IsUnit (1 - ζ ^ d) := by
  have hsum : ∑ k ∈ Finset.range M, (ζ ^ d) ^ k = 0 :=
    (mul_eq_zero.1 (by rw [mul_geom_sum, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self])).resolve_left
      (sub_ne_zero.2 hd)
  refine isUnit_of_dvd_unit ?_ hM
  rw [show (M : o) = ∑ k ∈ Finset.range M, (1 - (ζ ^ d) ^ k) by simp [Finset.sum_sub_distrib, hsum]]
  exact Finset.dvd_sum fun k _ => by simpa using sub_dvd_pow_sub_pow (1 : o) (ζ ^ d) k

theorem mem_maximalIdeal_of_map {R V : Type} [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V]
    (ev : R →+* V) {x : R} (h : ev x ∈ maximalIdeal V) : x ∈ maximalIdeal R :=
  (IsLocalRing.mem_maximalIdeal _).2 fun hu => mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h) (hu.map ev)

theorem stalk_of_base (X₁ : GSet) (z₁ : X₁.M.Z) (a : X₁.o₁) :
    ∃ s : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ a :=
  let ⟨s, hs⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨algebraMap X₁.o₁ X₁.Ω₁ a, Subalgebra.algebraMap_mem _ a⟩
  ⟨s, by rw [← RatModel.coe_stalkEquiv, hs]⟩

theorem stalk_isUnit (X₁ : GSet) (z₁ : X₁.M.Z) {s : X₁.M.Z.presheaf.stalk z₁} {x : X₁.o₁}
    (hs : X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ x) (hx : IsUnit x) : IsUnit s := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨t, ht⟩ := stalk_of_base X₁ z₁ y
  exact IsUnit.of_mul_eq_one t (X₁.M.stalkHom_injective z₁ (by rw [map_mul, hs, ht, ← map_mul, hy, map_one, map_one]))

theorem pow_eq_of_sub_mem (X₁ : GSet) (z₁ : X₁.M.Z) {s₁ s₂ : X₁.M.Z.presheaf.stalk z₁} {e₁ e₂ : ℕ}
    (h₁ : X₁.M.stalkHom z₁ s₁ = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e₁))
    (h₂ : X₁.M.stalkHom z₁ s₂ = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e₂))
    (hm : s₁ - s₂ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)) : X₁.S.ζ ^ e₁ = X₁.S.ζ ^ e₂ := by
  have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  by_contra hne
  set M := (X₁.S.r * X₁.S.N) ^ 2
  have hζ : IsPrimitiveRoot X₁.S.ζ M := X₁.S.prim
  have hM0 : M ≠ 0 := pow_ne_zero _ (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; lia)).ne'
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  have hd : X₁.S.ζ ^ e₂ * X₁.S.ζ ^ (e₁ + k * e₂) = X₁.S.ζ ^ e₁ := by
    rw [← pow_add, show e₂ + (e₁ + k * e₂) = e₁ + M * e₂ by rw [hk, Nat.succ_eq_add_one]; ring,
      pow_add, pow_mul, hζ.pow_eq_one, one_pow, _root_.mul_one]
  have hu : IsUnit (X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂) := by
    rw [show X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂ = -(X₁.S.ζ ^ e₂ * (1 - X₁.S.ζ ^ (e₁ + k * e₂))) by rw [← hd]; ring]
    exact (((hζ.isUnit hM0).pow e₂).mul (isUnit_one_sub_pow hζ (by dsimp [M]; rw [Nat.cast_pow]; exact X₁.S.unit.pow 2)
      (fun h => hne (by rw [← hd, h, _root_.mul_one])))).neg
  exact (IsLocalRing.mem_maximalIdeal _).1 hm (stalk_isUnit X₁ z₁ (by rw [map_sub, h₁, h₂, map_sub]) hu)

theorem pow_eq_iff_cast (X₁ : GSet) (a b : ℕ) :
    X₁.S.ζ ^ a = X₁.S.ζ ^ b ↔ (a : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = (b : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) := by
  have hpos : 0 < (X₁.S.r * X₁.S.N) ^ 2 := pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; lia)) 2
  have hord := X₁.S.prim.eq_orderOf
  rw [ZMod.natCast_eq_natCast_iff']
  exact ⟨fun h => X₁.S.prim.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) (by rwa [hord, pow_mod_orderOf, pow_mod_orderOf]),
    fun h => by rw [← pow_mod_orderOf X₁.S.ζ a, ← pow_mod_orderOf X₁.S.ζ b, ← hord, h]⟩

theorem affine_zero {G : Type} [AddCommGroup G] {M : ℕ} (hM : Odd M) (S : Set G) (hS : ∀ s ∈ S, -s ∈ S)
    (hne : S.Nonempty) (κ : ZMod M) (h : AddSubgroup.closure S →+ ZMod M)
    (hz : ∀ s (hs : s ∈ S), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0) :
    ∀ a (ha : a ∈ AddSubgroup.closure S), κ + h ⟨a, ha⟩ = 0 :=
  _root_.GlobalTheory.Poinc.Sep.TwistIndep.affine_zero hM S hS hne κ h hz

end GlobalTheory.GSep.TwistIndep

namespace GlobalTheory.GSep
open GlobalTheory.GSep.TwistIndep

theorem twistSum_indep : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (t₁ : Y₁ → V₁) (δ₁ : I → Y₁ → Y₁) (𝔪₁ : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : Y₁ → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (t₂ : Y₂ → V₂) (δ₂ : I → Y₂ → Y₂) (𝔪₂ : GlobalTheory.GSep.GMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : Y₂ → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  intro I X₁ z₁ act x₀ hdiv sg hsg hW V₁ _ _ _ ev₁ Y₁ _ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
    V₂ _ _ _ ev₂ Y₂ _ t₂ δ₂ 𝔪₂ C₂ lab₂ hlab₂ T₂ hT₂ c₂ hlab τ hτ e₁ e₂ hS₁ _ ⟨r, hr, hr0⟩
  obtain ⟨ε₁, ε₂, h1, h2, haff⟩ := _root_.GlobalTheory.GSep.twistSum_exp_affine I X₁ z₁ act x₀ hdiv sg hsg hW V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂
  have hφ : ∀ b ∈ X₁.S.HH X₁.M z₁, X₁.S.ζ ^ ε₁ b τ = X₁.S.ζ ^ ε₂ b τ := by
    obtain ⟨κ, h, hκ⟩ := haff τ hτ
    have hsup : ∀ s (hs : s ∈ X₁.S.supI X₁.M z₁), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0 := fun s hs => by
      have hsH : s ∈ X₁.S.HH X₁.M z₁ := AddSubgroup.subset_closure hs
      obtain ⟨U₁, hU₁⟩ := GlobalTheory.T.thetaMember_exists_terms_dividing_group_label I X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ s hsH
      obtain ⟨U₂, hU₂⟩ := GlobalTheory.T.thetaMember_exists_terms_dividing_group_label I X₁ z₁ act x₀ hdiv V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂ s hsH
      obtain ⟨q₁, hq₁⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₁ s τ)
      obtain ⟨q₂, hq₂⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₂ s τ)
      obtain ⟨u, hu⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨_, hs.2 (s + τ)⟩
      have hu' : X₁.M.stalkHom z₁ u = X₁.S.th (s + τ) / X₁.S.th s := by rw [← RatModel.coe_stalkEquiv, hu]
      have m₁' : q₁ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := mem_maximalIdeal_of_map ev₁ (by
        simpa [map_sub, map_one] using GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label I X₁ z₁ act x₀ hdiv
          V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ () hs τ hτ sg _
          (h1 Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ () τ hτ) q₁ u hq₁ hu')
      have m₂' : q₂ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := mem_maximalIdeal_of_map ev₂ (by
        simpa [map_sub, map_one] using GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label I X₁ z₁ act x₀ hdiv
          V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂ Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ () hs τ hτ sg _
          (h2 Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ () τ hτ) q₂ u hq₂ hu')
      have hqu : IsUnit (q₁ * u) := by
        by_contra hn
        exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
          ((Ideal.eq_top_iff_one (maximalIdeal (X₁.M.Z.presheaf.stalk z₁))).2
            (by simpa using sub_mem ((IsLocalRing.mem_maximalIdeal _).2 hn) m₁'))
      have hq : q₁ - q₂ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
        (Ideal.mul_unit_mem_iff_mem _ (isUnit_of_mul_isUnit_right hqu)).1
          (by have h3 := sub_mem m₁' m₂'; rwa [show q₁ * u - 1 - (q₂ * u - 1) = (q₁ - q₂) * u by ring] at h3)
      rw [← hκ s hsH, (pow_eq_iff_cast X₁ _ _).1 (pow_eq_of_sub_mem X₁ z₁ hq₁ hq₂ hq), sub_self]
    have hodd : Odd ((X₁.S.r * X₁.S.N) ^ 2) := by
      obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
      exact (by rw [hj, X₁.ρ.N_eq]; exact X₁.ρ.n_odd.pow.mul X₁.ρ.n_odd.pow.pow : Odd (X₁.S.r * X₁.S.N)).pow
    have hz := affine_zero hodd (X₁.S.supI X₁.M z₁) (GlobalTheory.T.neg_mem_dividingLabels_thetaSystem X₁ z₁) ⟨x₀, hdiv⟩ κ h hsup
    intro b hb
    rw [pow_eq_iff_cast, ← sub_eq_zero, hκ b hb]
    exact hz b hb
  obtain ⟨zt, hzt⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))
  obtain ⟨wt, hwt⟩ := GlobalTheory.T.thetaMember_twist_weight_wellDefined_lattice I X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ sg τ hτ
  obtain ⟨s₁, hs₁⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ e₁)
  obtain ⟨s₀, hs₀⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₁ (lab₁ c₁) τ)
  have : IsNoetherianRing V₁ := 𝔪₁.cn.1
  have hE' : ev₁ s₁ = ev₁ s₀ := mul_right_cancel₀ hr0 (by
    simpa only [map_mul] using GlobalTheory.AdicSum.sumI_unique (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
      (hS₁ zt (s₁ * r) hzt (by rw [map_mul, hs₁, hr, mul_div_assoc]) wt hwt)
      (h1 C₁ lab₁ hlab₁ T₁ hT₁ c₁ τ hτ zt (s₀ * r) hzt (by rw [map_mul, hs₀, hr, mul_div_assoc]) wt hwt))
  have hpe : X₁.S.ζ ^ e₁ = X₁.S.ζ ^ ε₁ (lab₁ c₁) τ := pow_eq_of_sub_mem X₁ z₁ hs₁ hs₀
    (mem_maximalIdeal_of_map ev₁ (by rw [map_sub, hE', sub_self]; exact zero_mem _))
  have hpe2 : X₁.S.ζ ^ ε₂ (lab₂ c₂) τ = X₁.S.ζ ^ e₁ := by rw [hpe, ← hlab]; exact (hφ _ (hlab₁ c₁)).symm
  exact fun zt' h' hzt' hh' wt' hwt' => h2 C₂ lab₂ hlab₂ T₂ hT₂ c₂ τ hτ zt' h' hzt' (by rwa [hpe2]) wt' hwt'

end GlobalTheory.GSep
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMember =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMemberStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMemberStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMember\n\n"}
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMemberStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSums =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSums", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaSumCommonSignMemberStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMemberStatement\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach\n\n"}
theorem GlobalTheory.GSep.twistSum_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : X → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h) := by
  intro I X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg, hweil⟩ := _root_.GlobalTheory.GSep.twistAtEach_exists I X₁ z₁ act x₀ hdiv
  classical
  let Wit : X₁.S.Gam → X₁.S.Gam → ℕ → Prop := fun a τ e =>
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
      (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X)
      (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (_ : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁)
      (T : X → C → V) (_ : 𝔪.Terms x₀ lab T) (c : C), lab c = a ∧
      GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e ∧
      ∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab c + τ) / X₁.S.th x₀ ∧ ev r ≠ 0
  refine ⟨sg, fun a τ => if h : ∃ e, Wit a τ e then h.choose else 0, fun V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c τ hτ zt h hzt hh wt hwt => ?_⟩
  obtain ⟨e₂, he₂⟩ := hsg V ev X t δ 𝔪 C lab hlab T hT c τ hτ
  by_cases hW : ∃ e, Wit (lab c) τ e
  · beta_reduce at hh; rw [dite_eq_left hW] at hh
    obtain ⟨V₁, _, _, _, ev₁, Y₁, _, t₁, δ₁, 𝔪₁, C₁, lab₁, hlab₁, T₁, hT₁, c₁, hc₁, hts, r, hr, hr0⟩ := hW.choose_spec
    exact _root_.GlobalTheory.GSep.twistSum_indep I X₁ z₁ act x₀ hdiv sg hsg hweil V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
      V ev X t δ 𝔪 C lab hlab T hT c hc₁ τ hτ _ e₂ hts he₂ ⟨r, hr, hr0⟩ zt h hzt hh wt hwt
  · beta_reduce at hh; rw [dite_eq_right hW] at hh
    have hh' : X₁.M.stalkHom z₁ h = X₁.S.th (lab c + τ) / X₁.S.th x₀ := by rw [hh]; simp
    have hev : ev h = 0 := by
      by_contra hne
      exact hW ⟨e₂, V, inferInstance, inferInstance, inferInstance, ev, X, inferInstance, t, δ, 𝔪, C, lab, hlab, T, hT, c,
        rfl, he₂, h, hh', hne⟩
    obtain ⟨s, hs⟩ := _root_.GlobalTheory.GSep.TwistIndep.stalk_of_base X₁ z₁ (X₁.S.ζ ^ e₂)
    have := he₂ zt (s * h) hzt (by rw [map_mul, hs, hh', mul_div_assoc]) wt hwt
    rw [map_mul, hev, mul_zero] at this
    rwa [hev]
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSums =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSumsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSumsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSums\n\n"}
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSumsStatement =====
