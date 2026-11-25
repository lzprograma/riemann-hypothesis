module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGaga
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConj
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConjugateLogPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentiableOnStarStar
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMatrix
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLogPeriodFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExponentialConjugate
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodHolomorphicContinuation
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeOnPuncturedDisc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeSpans
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodSetClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPeriodsFiniteQuotient
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroThird, Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramComplexConjugate, Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExists, Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamily

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroThird =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroThird", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

theorem UpperTheory.Reformulated.B.StarRingEndRootEqNeg.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := @_root_.GlobalTheory.CompanionTheory.Ar.HodgeBasic.rt0_conj_neg_ne_zero
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroThird =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramComplexConjugate =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramComplexConjugate", "h": "module\n\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram\npublic import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding\nimport Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal\npublic import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport\nimport Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConj\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Calculus.FDeriv.Star\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback\nimport Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExponentialConjugate\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.GramConj

open GlobalTheory.ArchMetricCompare (cj cjPt cjUnif cj_isAH cj_val isIso_of_cj carry carry_isAH)

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {ψ : A'.left ⟶ A.left} {M : LB A.left} {M' : LB A'.left} {g : ℕ}

theorem isDiff_conj (h : IsGrpPullback A' A cj ψ) (u : HolUnif A M g) (u' : HolUnif A' M' g)
    (hex : ∀ z, u'.ex z = cjPt h (u.ex (star z))) {t : epsR ℂ ⟶ A} {t' : epsR ℂ ⟶ A'}
    (e : t'.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t.left) {w : Fin g → ℂ} (hd : u.IsDiff w t) :
    u'.IsDiff (star w) t' := by
  haveI := isIso_of_cj h
  intro U hU f
  have e2 : t'.left = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv ψ).2 e
  have e4 : (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t'.left := by
    rw [e2, ← Category.assoc, GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.conj_conj_dual, Category.id_comp]
  have h2 : ⊤ ≤ t.left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U) := fun p _ => by
    have q : ((show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ) p ∈ U := by
      rw [e4]
      exact hU (show spMap (dualMap (starRingEnd ℂ)) p ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    exact q
  have e1 : (fun z => valAt' (u'.ex z).left U f) =
      star ∘ (fun z => valAt' (u.ex z).left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) ∘ star :=
    funext fun z => by
      simp only [hex]
      exact cj_val h _ U f
  rw [e1, GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.fderiv_conj_zero]
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ →
      TangentOrigin.evalPt y U hy f = dualMap (starRingEnd ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) t.left _ h2 (((inv ψ).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv ψ).app U).hom f)
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg (starRingEnd ℂ) e3

theorem exists_conjUnif (h : IsGrpPullback A' A cj ψ) (hM : M.IsLB) (u : HolUnif A M g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ) :
    ∃ (u' : HolUnif A' (M.pull ψ) g) (χ' : u'.Λ → ℂ), u'.IsAH (Hm.map star) χ' ∧
      ∀ z, u'.ex z = cjPt h (u.ex (star z)) := by
  have hM1 : (M.pull (𝟙 A.left)).IsLB := pull_isLB hM _
  obtain ⟨w, hw⟩ : LBIso M (M.pull (𝟙 A.left)) :=
    LBIso.chartPull (chartPullId M) (chartPullPull M (𝟙 A.left)) (PolBaseChange.lbIso_refl hM)
  have key : ∀ f, f = ψ ≫ 𝟙 A.left → ∃ (u' : HolUnif A' (M.pull f) g) (χ' : u'.Λ → ℂ),
      u'.IsAH (Hm.map star) χ' ∧ ∀ z, u'.ex z = cjPt h (u.ex (star z)) := by
    rintro _ rfl
    exact ⟨cjUnif h (carry u hM hM1 hw), _, cj_isAH h _ (carry_isAH hM hM1 hw hA), fun _ => rfl⟩
  exact key _ (Category.comp_id _).symm

theorem isHodgeGram_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Spec (CommRingCat.of ℂ) ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ i, (v' i).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left) → Fl.IsHodgeGram G L x v Γ → Fl.IsHodgeGram G L x' v' (Γ.map (starRingEnd ℂ)) := by
  exact @_root_.GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj

end GlobalTheory.CompanionTheory.Ar.GramConj
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramComplexConjugate =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExists =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExists", "h": "module\n\npublic import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConjugateLogPeriods\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LogPer

open GroundTheory.Heights₂.Heights.Regular

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ]

theorem add_single_mem_logCover (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) (i : Fin a) :
    w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  intros
  apply _root_.GlobalTheory.CompanionTheory.Ar.Flat.QuotLoc.add_single_mem_logCover <;> assumption

theorem expCover_add_single (h : a ≤ n) (w : Fin n → ℂ) (i : Fin a) :
    expCover a (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = expCover a w := by
  funext k
  by_cases hk : k = Fin.castLE h i
  · subst hk
    have hi : (Fin.castLE h i).val < a := i.2
    simp only [expCover, Pi.add_apply, Pi.single_eq_same, ite_eq_left hi, Complex.exp_add,
      Complex.exp_two_pi_mul_I]
    exact mul_one _
  · simp [expCover, hk]

theorem exists_mem_logCover (h : a ≤ n) : ∃ w : Fin n → ℂ, w ∈ logCover h := by
  refine ⟨fun k => if k.val < a then -1 else 0, fun i => ?_, fun k hk => ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.2
    simp only [ite_eq_left hi]
    simp
  · simp [not_lt.2 hk]

theorem monodromy_preserves_form (L : Flat.LogPeriods n a g Λ) (i : Fin a) (x y : Λ) :
    L.E (L.T i x) (L.T i y) = L.E x y := by
  obtain ⟨w, hw⟩ := exists_mem_logCover L.a_le
  have h1 := L.im _ (add_single_mem_logCover L.a_le hw i) x y
  rw [L.mono i w hw, L.mono i w hw, expCover_add_single, L.im w hw] at h1
  exact_mod_cast h1

theorem T_bijective (L : Flat.LogPeriods n a g Λ) (i : Fin a) : Function.Bijective (L.T i) := by
  haveI := L.fin
  let e : Λ ≃ₗ[ℤ] Module.Dual ℤ Λ := LinearEquiv.ofBijective L.E L.unimod
  let S : Λ →ₗ[ℤ] Λ := e.symm.toLinearMap ∘ₗ (L.T i).dualMap ∘ₗ e.toLinearMap
  have hE : ∀ x y, L.E (S x) y = L.E x (L.T i y) := by
    intro x y
    have h1 : e (S x) = (L.T i).dualMap (e x) := by simp [S]
    exact congrArg (fun f : Module.Dual ℤ Λ => f y) h1
  have hST : ∀ x, S (L.T i x) = x := fun x =>
    L.unimod.1 (LinearMap.ext fun y => by rw [hE, monodromy_preserves_form])
  have hSs : Function.Surjective S := fun x => ⟨_, hST x⟩
  have hSi : Function.Injective S := OrzechProperty.injective_of_surjective_endomorphism S hSs
  exact ⟨fun x y h => by rw [← hST x, ← hST y, h], fun y => ⟨S y, hSi (hST (S y))⟩⟩

theorem exists_conj_logPeriods : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L' : Flat.LogPeriods n a g Λ),
    ∃ L : Flat.LogPeriods n a g Λ, (∀ w x, L.P w x = star (L'.P (star w) x)) ∧
      ∀ z, L.H z = (L'.H (star z)).map (starRingEnd ℂ) := by
  intro n a g Λ _ L'
  exact ⟨ConjPeriods.conj L' (T_bijective L'), fun _ _ => rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LogPer
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExists =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamily =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamily", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentiableOnStarStar\npublic import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianSchemeLaws\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended\npublic import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroThird\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart\npublic import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMatrix\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLogPeriodFamily\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExponentialConjugate\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramComplexConjugate\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExists\nimport Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodHolomorphicContinuation\nimport Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFree\nimport Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeOnPuncturedDisc\nimport Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeSpans\nimport Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodSetClosed\nimport Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPeriodsFiniteQuotient\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Conj

open GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat.Link

alias spMap_comp' := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp

theorem dualMap_conj_over :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (starRingEnd ℂ) := by
  have h : (dualMap (starRingEnd ℂ)).comp (algebraMap ℂ (DualNumber ℂ)) =
      (algebraMap ℂ (DualNumber ℂ)).comp (starRingEnd ℂ) := by
    ext c
    · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [← spMap_comp', ← spMap_comp', h]

def conjTan {S : Scheme.{0}} {G : Over S} {x x' : Sp ℂ ⟶ S} (h : x' = spMap (starRingEnd ℂ) ≫ x)
    (v : epsAt x ⟶ G) : epsAt x' ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ v.left) (by
    subst h
    have hv := Over.w v
    simp only [Over.mk_hom] at hv ⊢
    rw [Category.assoc, hv, ← Category.assoc]
    have := dualMap_conj_over
    simp only [spMap] at this
    rw [this, Category.assoc])

theorem conj_hermForm' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) :
    hermForm (Hm.map (starRingEnd ℂ)) a b = (starRingEnd ℂ) (hermForm Hm (star a) (star b)) := by
    simp [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem isRiem_of_chart {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) (z : Fin n → ℂ)
    (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) (h : (chart C).IsRiem (star z) Hm) :
    C.IsRiem z (Hm.map (starRingEnd ℂ)) := by
  intro m u v Γ hv
  have hψ : conjPts C.ψ (star z) = (starRingEnd ℂ).comp (C.ψ z) := by simp [conjPts]
  have hx : spMap (conjPts C.ψ (star z)) = spMap (starRingEnd ℂ) ≫ spMap (C.ψ z) := by
    rw [hψ, spMap_comp']
  have hx' : spMap (C.ψ z) = spMap (starRingEnd ℂ) ≫ spMap (conjPts C.ψ (star z)) := by
    rw [hx, ← Category.assoc, _root_.GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.conj_conj_point, Category.id_comp]
  let v' : Fin m → (epsAt (spMap (conjPts C.ψ (star z))) ⟶ C.t.G) := fun i => conjTan hx (v i)
  have hv' : (chart C).IsVal (star z) u v' := by
    intro i
    show spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left = spMap (dualMap (conjPts C.ψ (star z))) ≫ (C.M.pt (u i)).left
    rw [hv i, hψ, _root_.GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.spMap_dualMap_comp, Category.assoc]
  have hback : ∀ i, (v i).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v' i).left := fun i => by
    show (v i).left = spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left
    rw [← Category.assoc, _root_.GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.conj_conj_dual, Category.id_comp]
  have hform : ∀ i j, hermForm Hm (fun b => conjPts C.ψ (star z) (u i b)) (fun b => conjPts C.ψ (star z) (u j b)) =
      (starRingEnd ℂ) (hermForm (Hm.map (starRingEnd ℂ)) (fun b => C.ψ z (u i b)) (fun b => C.ψ z (u j b))) := by
    intro i j
    rw [conj_hermForm', Complex.conj_conj, hψ]
    rfl
  have hform' : ∀ i j, (Real.pi : ℂ) * hermForm Hm (fun b => conjPts C.ψ (star z) (u i b))
      (fun b => conjPts C.ψ (star z) (u j b)) = (starRingEnd ℂ) ((Real.pi : ℂ) *
        hermForm (Hm.map (starRingEnd ℂ)) (fun b => C.ψ z (u i b)) (fun b => C.ψ z (u j b))) := by
    intro i j
    rw [hform, map_mul, Complex.conj_ofReal]
  have key := h m u v' (Γ.map (starRingEnd ℂ)) hv'
  constructor
  · intro hG i j
    have h1 := key.1 (_root_.GlobalTheory.CompanionTheory.Ar.GramConj.isHodgeGram_conj _ _ _ _ _ _ _ _ _ hx (fun _ => rfl) hG) i j
    have h2 : (starRingEnd ℂ) (Γ i j) = _ := h1.trans (hform' i j)
    have h3 := congrArg (starRingEnd ℂ) h2
    simpa only [Complex.conj_conj] using h3
  · intro hE
    have h1 : Fl.IsHodgeGram C.t.G C.t.PP.L (spMap (conjPts C.ψ (star z))) v' (Γ.map (starRingEnd ℂ)) := by
      refine key.2 fun i j => ?_
      exact (congrArg (starRingEnd ℂ) (hE i j)).trans (hform' i j).symm
    have h2 := _root_.GlobalTheory.CompanionTheory.Ar.GramConj.isHodgeGram_conj _ _ _ _ _ _ _ _ _ hx' hback h1
    have h3 : (Γ.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Γ := by
      ext i j
      simp
    rwa [h3] at h2

theorem exists_log_periods_of_root : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a C.g Λ) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ), 0 < ρ ∧ ρ ≤ 1 ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ z ∈ Flat.punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) :=
  fun E _ _ _ H D l Xo σ n a C hpq hσ =>
    let ⟨ρ, Λ, iΛ, L, e, hρ0, hρ1, h1, h2⟩ := exists_logPeriods_famExp_full E H D l Xo σ n a C hpq hσ
    ⟨ρ, Λ, iΛ, L, e, hρ0, hρ1, fun w hw => (h1 w hw).1, h2⟩

theorem exists_logPeriods_famExp_isRiem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a C.g Λ) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ), 0 < ρ ∧ ρ ≤ 1 ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ z ∈ Flat.punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  intro E _ _ _ H D l Xo σ n a C hpq
  have h1 : (σ (baseKA l).ρ) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, (baseKA l).ρ_sq]
    simp
  have h2 : (σ (baseKA l).ρ - H.rt0) * (σ (baseKA l).ρ + H.rt0) = 0 := by
    have := H.sqrt_neg_disc_sq
    linear_combination h1 - this
  rcases mul_eq_zero.1 h2 with h | h
  · exact exists_log_periods_of_root E H D l Xo σ n a C hpq (sub_eq_zero.1 h)
  have hσ' : ((starRingEnd ℂ).comp σ) (baseKA l).ρ = H.rt0 := by
    have h3 : σ (baseKA l).ρ = -H.rt0 := eq_neg_of_add_eq_zero_left h
    show (starRingEnd ℂ) (σ (baseKA l).ρ) = H.rt0
    rw [h3, map_neg, GlobalTheory.CompanionTheory.Ar.HodgeBasic.rt0_conj_neg_ne_zero, neg_neg]
  obtain ⟨ρ, Λ, iΛ, L', e', hρ0, hρ1, hper, hriem⟩ :=
    exists_log_periods_of_root E H D l Xo ((starRingEnd ℂ).comp σ) n a (chart C) hpq hσ'
  obtain ⟨L, hLP, hLH⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods n a C.g Λ L'
  obtain ⟨e, hper'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.exists_famExp_of_conj C.R C.t.G C.g n C.M ρ C.ψ e'
  refine ⟨ρ, Λ, iΛ, L, e, hρ0, hρ1, fun w hw p => ?_, fun z hz => ?_⟩
  · have hw' : star w ∈ logCover L'.a_le := (star_mem_logCover _).2 hw
    rw [hper', star_real_smul, star_expCover]
    have h4 := hper (star w) hw' (star p)
    refine h4.trans ?_
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (hLP w x).trans ((congrArg star hx).trans (star_star p))⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, ((congrArg star (hLP w x)).trans (star_star _)).symm⟩
  · have h := hriem (star z) (star_mem_punct.2 hz)
    rw [hLH]
    refine isRiem_of_chart C _ _ ?_
    rw [star_real_smul]
    exact h

end GlobalTheory.CompanionTheory.Ar.Flat.Conj
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamily =====
