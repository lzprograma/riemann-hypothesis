module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivisorOfForallCompleteDvrPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.hasDivisor_of_forall_complete_dvr_points : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (J J' : Type) [Fintype J] (th : J → Ω) (e : J' → Ω) (D : ℕ), 1 ≤ D → Geo.Tor.IsNormalScheme M.Z → M.HasDiv e → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ξ : Sp V ⟶ M.Z) (emb : Ω →+* FractionRing V), jK V ≫ ξ = spMap emb ≫ M.pt → ∀ j₀, e j₀ ≠ 0 → (∀ j, emb (e j / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, emb (th b ^ D / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ emb (e j₀ / th b ^ D) ∈ Set.range (algebraMap V (FractionRing V))) → M.HasDiv th := by
  first | exact @GlobalTheory.ValCmp.hasDiv_of_forall_cDvr
