module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models.Inhab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def trivTriple (H : Host E) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (a : OAct (𝓞 E) G) : SAB H S where
  G := G
  semi := hG
  act := a
  PP := UU.trivRig G
  cub := UU.trivCub G
  sym := PrimNorm.isSymmetric_of_hasGen _ ⟨UU.unitGen _ _, UU.unitGen_isGen _ _⟩
  adj := fun _ => ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (Out.Inh.linComb_triv_g _ _))⟩
  prim := ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (fun _ _ => rfl))⟩

def zeroTriple (H : Host E) (S : Scheme.{0}) : SAB H S :=
  trivTriple H (𝟙_ (Over S)) (isSemiAbelian_of_isAbelianScheme _ (UU.isAbelianScheme_unit S))
    ⟨fun _ => 𝟙 _, fun _ => inferInstance, rfl, fun _ _ => toUnit_unique _ _, fun _ _ => toUnit_unique _ _⟩

theorem isProper_zeroTriple (S : Scheme.{0}) : IsProper (zeroTriple H S).G.hom :=
  (UU.isAbelianScheme_unit S).proper

theorem abLocus_eq_univ {S : Scheme.{0}} (G : Over S) (h : IsProper G.hom) : abLocus G = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ _ _ _ => inferInstance

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  have := ProjSpace.Model.isIso_str_zero (R := R)
  exact ⟨0, inv (PSpace.str R 0), inferInstance, IsIso.inv_hom_id _⟩

end GlobalTheory.Models.Inhab

end
