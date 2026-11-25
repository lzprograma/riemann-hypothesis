module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroup
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeTateFunctional
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUnique
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateLatticeLeOmega
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiFiniteGroupFinite
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongGroupPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongOrderDivides
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongUniqueUpToIso
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HeightPullbackDominatingMap

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HTPull

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    (dualMap d).comp (dualMap c) = dualMap (d.comp c) := by
  ext r <;> simp [dualMap]

theorem lieBC {S : Scheme.{0}} {G : Over S} [GrpObj G] {A B : Type} [CommRing A] [CommRing B] (c : A →+* B)
    (x : Sp A ⟶ S) (y : Sp B ⟶ S) (hy : y = Spec.map (CommRingCat.ofHom c) ≫ x) (hsm : Smooth G.hom)
    {E E' : Type} [AddCommGroup E] [Module A E] [AddCommGroup E'] [Module B E']
    (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) ∧
      (∀ (a : A) e, j (a • e) = c a • j e) ∧ Submodule.span B (Set.range j) = ⊤ ∧
      ∀ l : Module.Dual A E, ∃ l' : Module.Dual B E', ∀ e, l' (j e) = c (l e) := by
  apply _root_.GlobalTheory.CompanionTheory.Ar.HTPullK.lieBC <;> assumption

section Setup

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
  {X X' : Scheme.{0}} {x : Sp R ⟶ X} {x' : Sp R' ⟶ X'} {f : X' ⟶ X}
  {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}
  {Ω Ω' : Type} [Field Ω] [Field Ω'] {k : R →+* Ω} {k' : R' →+* Ω'} {i : Ω →+* Ω'}
  {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
  {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {j : V →+ V'}

end Setup

section Back

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
  {X X' : Scheme.{0}} {x : Sp R ⟶ X} {x' : Sp R' ⟶ X'} {f : X' ⟶ X}
  {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}
  {Ω Ω' : Type} [Field Ω] [Field Ω'] {k : R →+* Ω} {k' : R' →+* Ω'} {i : Ω →+* Ω'}
  {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
  {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {j : V →+ V'}

end Back

end GlobalTheory.CompanionTheory.Ar.HTPull

theorem GlobalTheory.CompanionTheory.Ar.HTPull.main : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → Smooth G.hom → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → ∀ (jd : Module.Dual Ω V →+ Module.Dual Ω' V'), (∀ w e, jd w (j e) = i (w e)) → ∀ (N : ℕ), 0 < N → ∀ (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), IsIntegrallyClosed (X.presheaf.stalk (f p'.1)) → IsNoetherianRing (X.presheaf.stalk (f p'.1)) → (∃ ζ : Ω, IsPrimitiveRoot ζ N) → M.IsHTFormAt N ⟨f p'.1, h⟩ 0 → M'.htLat N p' = (M.htLat N).pull ξ' f jd p' :=
  GlobalTheory.CompanionTheory.Ar.HTPullK.main
