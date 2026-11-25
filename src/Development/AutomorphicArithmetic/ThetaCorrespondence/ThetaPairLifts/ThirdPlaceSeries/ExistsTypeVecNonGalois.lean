module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpenOrbitOfUnramifiedExponents
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivOutsideLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteTypeVectorDetectedLocalComponentEquivarianStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorEqGoodIdempotentTypePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotInDetectByEqvMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionGLSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsAtLevelsFixedPrincipalCongruenceTypePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCompletionSymmContinuous
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivOutsideMul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspace, Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTypeVecNonGalois

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspace =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspace", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivOutsideLoc\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteTypeVectorDetectedLocalComponentEquivarianStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorEqGoodIdempotentTypePlacesStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotInDetectByEqvMap\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionGLSurjective\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsAtLevelsFixedPrincipalCongruenceTypePlacesStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCompletionSymmContinuous\nimport Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesInjective\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivOutsideMul\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypeVec

theorem pi_ind {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type} [∀ i, Group (M i)] (P : (∀ i, M i) → Prop) (h1 : P 1)
    (hm : ∀ g i (m : M i), P g → P (Pi.mulSingle i m * g)) : ∀ g, P g :=
  GlobalTheory.TypeVecConj.pi_ind P h1 hm

def conjL {X : Type} : (X → ℂ) →ₛₗ[starRingEnd ℂ] (X → ℂ) where
  toFun f := fun g => star (f g)
  map_add' f f' := by funext g; simp
  map_smul' c f := by funext g; simp

theorem loc_piece {L : Type} [Field L] [NumberField L] [IsCMField L] {n g : ℕ} [Fact g.Prime] (π : NG.FinTyp L n)
    (s : SplitPlace L) {w : HeightOneSpectrum (𝓞 L)} (h : s.w = w)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion L))) (hτ : GlobalTheory.HeightCounting.IsLocS π.S s (h ▸ τ))
    (ii : ℚ_[g] ≃+* w.adicCompletion L) (hii : Continuous ii) :
    ∃ j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L), Continuous j ∧
      ∀ f ∈ π.S, f ≠ 0 → ∃ p : (GAf L n → ℂ) →ₗ[ℂ] τ.V, p f ≠ 0 ∧
        ∀ (y : GL (Fin n) ℤ_[g]) (x : GAf L n), IsLiftAt s j y x → ∀ f' ∈ π.S,
          p (NG.rt L n x f') = τ.ρ (Matrix.GeneralLinearGroup.map ii.toRingHom (GlobalTheory.GLp.inc g n y)) (p f') :=
  GlobalTheory.TypeVecConj.loc_piece π s h τ hτ ii hii

theorem isotIn_stable {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) (π : NG.FinTyp D.host.E n) (h : GAf D.host.E n) :
    ∀ z ∈ principalLevelFrame.isotIn ρ C π, ρ h z ∈ principalLevelFrame.isotIn ρ C π :=
  GlobalTheory.TypeVecConj.isotIn_stable ρ C π h

theorem detect_conj {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) (π : NG.FinTyp D.host.E n) (c : GAf D.host.E n) (y : A) (hy : y ∈ principalLevelFrame.isotIn ρ C π) (hy0 : y ≠ 0) :
    ∃ q : A →ₗ[ℂ] (GAf D.host.E n → ℂ), q y ≠ 0 ∧ ∀ z ∈ principalLevelFrame.isotIn ρ C π, q z ∈ π.S ∧
      ∀ h, q ((ρ.comp (MulAut.conj c).toMonoidHom) h z) = NG.rt D.host.E n h (q z) := by
  obtain ⟨q, hq0, hq⟩ := GlobalTheory.isotIn_detect_by_eqv_map D A ρ C π y hy hy0
  exact GlobalTheory.TypeVecConj.conj_detect ρ C π c y hy q hq0 hq

theorem mem_KFix {D : D7} {s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E}
    {j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)}
    {A : Type} [AddCommGroup A] [Module ℂ A] {ρA : GAf D.host.E D.R.r →* Module.End ℂ A} {z : A} :
    z ∈ KFix D s j ρA ↔ ∀ (k : Fin 2) (v : D.nd.PlG k) (y : (GlobalTheory.GLp.red (D.host.g k) D.R.r).ker) (x : GAf D.host.E D.R.r),
      IsLiftAt (s k v) (j k v) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) x → ρA x z = z :=
  GlobalTheory.TypeVecConj.mem_KFix

theorem typePrime_finiteGroup_induction_factor (D : D7) (P : G0g D.nd → Prop) (h1 : P 1)
    (hm : ∀ (g : G0g D.nd) (k : Fin 2) (v : D.nd.PlG k) (m : GL (Fin D.R.r) (ZMod (D.host.g k))), P g →
      P (GlobalTheory.GoodTypes.facHom D k v m * g)) : ∀ g, P g :=
  GlobalTheory.TypeVecConj.typePrime_finiteGroup_induction_factor D P h1 hm

theorem intertwine {D : D7} {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    {SA : Submodule ℂ A} {SB : Submodule ℂ B} (ρA : Representation ℂ (G0g D.nd) SA) (ρB : Representation ℂ (G0g D.nd) SB)
    (N : Submodule ℂ A) (q : A →ₗ[ℂ] B)
    (hstep : ∀ (k : Fin 2) (v : D.nd.PlG k) (m : GL (Fin D.R.r) (ZMod (D.host.g k))) (z : SA), (z : A) ∈ N →
      ((ρA (GlobalTheory.GoodTypes.facHom D k v m) z : SA) : A) ∈ N ∧ ∀ z' : SB, (z' : B) = q z →
        ((ρB (GlobalTheory.GoodTypes.facHom D k v m) z' : SB) : B) = q (ρA (GlobalTheory.GoodTypes.facHom D k v m) z)) :
    ∀ (a : MonoidAlgebra ℂ (G0g D.nd)) (z : SA) (z' : SB), (z : A) ∈ N → (z' : B) = q z →
      ((ρA.asAlgebraHom a z : SA) : A) ∈ N ∧ ((ρB.asAlgebraHom a z' : SB) : B) = q (ρA.asAlgebraHom a z) :=
  GlobalTheory.TypeVecConj.intertwine ρA ρB N q hstep

theorem typeVec_rows {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D}
    (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hP : GlobalTheory.Mem.R3.Pins R F cG) (I : Ident D)
    (cp : GlobalTheory.GoodTypes.Comp D) (hcp : IsComp I (fun σ => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) cp) (σ : D.what₂.FT) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V),
      (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x :=
  GlobalTheory.TypeVecConj.typeVec_rows R F cG Y hP I cp hcp σ

section Target

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

end Target

end GlobalTheory.TypeVec

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspace =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTypeVecNonGalois =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTypeVecNonGalois", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic\n\n"}
section -- clump:auto
@[expose] public section



section
section
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG
namespace GlobalTheory.TypeVec
section Target
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem exists_typeVec_nonGalois_ne_zero : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (I : GlobalTheory.TypeRec.Ident (w.st Z).toD7) cp, GlobalTheory.TypeRec.IsComp I (repOf Y) cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g (w.st Z).toD7.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom (w.st Z).toD7 k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom (w.st Z).toD7.ntypes.e0 x = x :=
  fun _ => GlobalTheory.TypeVecConj.typeVec
end Target
end GlobalTheory.TypeVec
end
end
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTypeVecNonGalois =====
