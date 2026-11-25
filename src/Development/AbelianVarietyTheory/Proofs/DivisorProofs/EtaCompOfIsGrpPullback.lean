module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedUniversalHomMatrixSchemeStatement
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory CartesianMonoidalCategory MonObj

open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem act_natCast {E : Type} [Field E] {X' : Scheme.{0}} {G : Over X'} [GrpObj G] (act : OAct (𝓞 E) G) (n : ℕ) :
    act.act (n : 𝓞 E) = mulN G n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    have h0 : act.act 0 = 1 := mul_eq_left.mp h.symm
    rw [Nat.cast_zero, h0, Hom.one_def]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ, act.add, ih, act.one, Hom.mul_def]
    rfl

theorem eta_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  intros
  apply _root_.GlobalTheory.HomFixNorm.one_comp_of_isGrpPullback <;> assumption

theorem exists_lift_torsion {X' : Scheme.{0}} {G : Over X'} [GrpObj G] (n : ℕ) {Y : Over X'} (a : Y ⟶ G)
    (h : a ≫ mulN G n = 1) : ∃ aT : Y ⟶ torsion G n, aT ≫ torsion.ι G n = a :=
  ⟨pullback.lift a (toUnit Y) (by rw [h, Hom.one_def]), pullback.lift_fst _ _ _⟩

theorem mono_torsion_ι {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) : Mono (torsion.ι G n).left := by
  have : Mono (η[G] : 𝟙_ (Over X') ⟶ G) := ⟨fun g h _ => toUnit_unique g h⟩
  have : Mono (torsion.ι G n) := ⟨fun a b hab => pullback.hom_ext hab (toUnit_unique _ _)⟩
  infer_instance

theorem isDomain_stalk_of_etale {X' W : Scheme.{0}} [GlobalTheory.IsNormalScheme X'] (h : W ⟶ X') [Etale h] (q : W) :
    IsDomain (W.presheaf.stalk q) :=
  (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth h
    (fun y => ⟨GlobalTheory.IsNormalScheme.isDomain_stalk y, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk y⟩) q).1

end GlobalTheory.TorsSpec
