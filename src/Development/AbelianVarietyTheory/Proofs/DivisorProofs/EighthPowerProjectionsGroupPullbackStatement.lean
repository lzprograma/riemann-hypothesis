module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullback
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.eighthPowerProjections_groupPullback : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ C)), ∃! x : T₁ ⟶ B, ∀ a, x ≫ pr a = y a) → ∃ pr' : Fin 8 → (B' ⟶ C'), (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) ∧ (∀ a, IsMonHom (pr' a)) ∧ ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ C')), ∃! x : T₁ ⟶ B', ∀ a, x ≫ pr' a = y a := by
  first | exact @GlobalTheory.GrpPullPow.pr_pull
