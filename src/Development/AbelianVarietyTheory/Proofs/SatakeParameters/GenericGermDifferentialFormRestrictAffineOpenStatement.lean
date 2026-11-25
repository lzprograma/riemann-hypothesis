module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermSecRestrictGlobalAlgebraMap

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpen, Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpenStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpen =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpen", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermSecRestrictGlobalAlgebraMap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeCoh

theorem formGermI_res : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ),
    letI := algΓ p
    ∀ [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p) (j : ℕ) (V V' : Z.Opens)
      (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hη : genericPoint Z ∈ V) (hη' : genericPoint Z ∈ V')
      (h : V' ≤ V) (y : sectionsOn (Omega p j) V),
      formGermI p j hV' hη' hinst (sectionsOn.res ℂ (Omega p j) h y) = formGermI p j hV hη hinst y := by
  intro Z _ p
  letI := algΓ p
  intro inst hinst j V V' hV hV' hη hη' h y
  subst hinst
  letI := ffAlg p
  have key : (toOmEquiv p j hV').symm (sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p j) h y)) =
      formRes p h j ((toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y)) := by
    apply (toOmEquiv p j hV').injective
    rw [LinearEquiv.apply_symm_apply, toOmEquiv_apply, ← res_toOm, ← toOmEquiv_apply p j hV,
      LinearEquiv.apply_symm_apply, sectionsOn.toΓ_res]
  change (semiHom_germSec p hη').mDR
      ((toOmEquiv p j hV').symm (sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p j) h y)) : DR ℂ (Sec p V')) =
    (semiHom_germSec p hη).mDR ((toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y) : DR ℂ (Sec p V))
  rw [key]
  exact congrArg Subtype.val (SemiHom.mOm_mOm (SemiHom.of_algHom (Sec.res p h)) (semiHom_germSec p hη')
    (semiHom_germSec p hη) (fun b ↦ by
      change (Z.presheaf.germ V' (genericPoint Z) hη').hom ((Z.presheaf.map (homOfLE h).op).hom b) =
        (Z.presheaf.germ V (genericPoint Z) hη).hom b
      exact congrArg (fun f ↦ f.hom (show Γ(Z, V) from b))
        (TopCat.Presheaf.germ_res Z.presheaf (homOfLE h) (genericPoint Z) hη')) _)

end GlobalTheory.HodgeCoh
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpen =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpenStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpenStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermSecRestrictGlobalAlgebraMap\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

alias _root_.GlobalTheory.T.genericGerm_differentialForm_restrict_affineOpen := _root_.GlobalTheory.HodgeCoh.formGermI_res
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpenStatement =====
