module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyBasisBijectiveStatement

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersi, Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersiStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersi =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersi", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyBasisBijectiveStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem preRes_bijective : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  intro R' _ X X' φ _ s'
  have hB : ∀ {U : TopologicalSpace.Opens X} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
  refine _root_.GlobalTheory.AbCoh.cohO_basis_bijective R' X' s' X.affineOpens (preU φ) (preU_mono φ) ?_ ?_
  · intro U x hx
    obtain ⟨W, hW, hWU⟩ := (φ.isClosedEmbedding).isInducing.isOpen_iff.mp U.1.2
    have hxW : φ.base x ∈ W := by
      have : x ∈ φ.base ⁻¹' W := by rw [hWU]; exact hx
      exact this
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := ⟨W, hW⟩) hxW
    refine ⟨⟨V, hV⟩, hxV, ?_⟩
    intro y hy
    have : y ∈ φ.base ⁻¹' W := hVW hy
    rw [hWU] at this
    exact this
  · intro a b x ha hb
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := a.1 ⊓ b.1) ⟨ha, hb⟩
    exact ⟨⟨V, hV⟩, fun y hy ↦ (hVW hy).1, fun y hy ↦ (hVW hy).2, hxV⟩

end GlobalTheory.AbCoh
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersi =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersiStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersiStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersi\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

theorem _root_.GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  first | exact @GlobalTheory.AbCoh.preRes_bijective
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersiStatement =====
