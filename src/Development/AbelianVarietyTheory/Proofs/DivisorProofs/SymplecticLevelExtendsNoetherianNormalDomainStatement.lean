module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelExtendsNoetherianNormalDomain
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR


theorem _root_.GlobalTheory.T.symplecticLevel_extends_noetherian_normalDomain : ∀ {R₁ : Type} [CommRing R₁] (P₁ : PolAV (Sp R₁)) (R F : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field F] [Algebra R F] [IsFractionRing R F] (h : R₁ →+* R) (Q : PolAV (Sp F)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : Rˣ), 0 < K → IsUnit (K : R) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap R F).comp h)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap R F).toMonoidHom ze))) → ∃ (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ze)) := by
  first | exact @GlobalTheory.SympLevelExt.level_extends
