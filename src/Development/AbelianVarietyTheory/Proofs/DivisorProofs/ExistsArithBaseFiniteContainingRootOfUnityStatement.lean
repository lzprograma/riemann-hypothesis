module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_arithBase_finite_containing_rootOfUnity : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (Ω₂ : Type) [Field Ω₂] [Algebra Ω₁ Ω₂] (K : ℕ) (ζ : Ω₂ˣ), 0 < K → IsPrimitiveRoot ζ K → ∃ (o₂ : Type) (_ : CommRing o₂) (_ : Algebra o₂ Ω₂) (_ : ArithBase o₂ Ω₂) (κ : o₁ →+* o₂) (ze : o₂ˣ), κ.Finite ∧ (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) ∧ Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze = ζ := by
  first | exact @GlobalTheory.Poinc.exists_arithBase_rootOfUnity
