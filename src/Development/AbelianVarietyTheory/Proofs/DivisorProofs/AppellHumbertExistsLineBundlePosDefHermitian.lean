module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfHolUnif
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannTheoremNonprincipalPolarisedTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannTheoremNonprincipalPolarisedTorus\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall\nimport Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

namespace GlobalTheory.AHPos

theorem smoothOfRelativeDimension_of_holUnif {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (u : HolUnif A L g) : SmoothOfRelativeDimension g A.hom := by
  intros
  apply _root_.GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif <;> assumption

end GlobalTheory.AHPos

theorem GlobalTheory.AHPos.exists_lb_of_posDef : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ), L₀.IsLB → u₀.IsAH H₀ χ₀ →
    ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ u.IsAH Hm χ := by
  intro g A _ hA L₀ u₀ H₀ χ₀ hL₀ hAH Hm hHm hpos hint
  obtain ⟨A', _, hA', hsm, L', u', χ', hL', hΛ, hAH'⟩ :=
    _root_.GlobalTheory.riemann_polarised_torus g u₀.Λ Hm u₀.discrete u₀.full hHm hpos hint
  obtain ⟨f, -, hf⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice A A' g hA hA'
    (GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u₀) hsm L₀ L' u₀ u' LinearMap.id
    (fun x hx => (hΛ x).2 hx)
  obtain ⟨u₁, hex, hΛ₁, hfr⟩ := GlobalTheory.exists_holUnif_linComb A A' L₀ L' g g u₀ u' PUnit (fun _ => f)
    (fun _ => LinearMap.id) (fun _ => 1) (fun _ z => hf z)
  have hmem : ∀ l : u₁.Λ, (l : Fin g → ℂ) ∈ u'.Λ := fun l => (hΛ _).2 (hΛ₁ ▸ l.2)
  refine ⟨_, u₁, fun l => χ' ⟨l.1, hmem l⟩, LB.isLB_linComb hL' _ _, hex, hHm, hpos,
    fun l => hAH'.2.2.1 _, ?_⟩
  intro l j z hz
  rw [hex] at hz
  have hz' : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U (j PUnit.unit) := by
    rw [← LinearMap.id_apply (R := ℂ) z, hf z]
    exact (CubeValues.le_preimage_wchart (u₀.ex z).left L' (fun _ => f.left) j).1 hz PUnit.unit
  have e1 : u₁.fr j z = u'.fr (j PUnit.unit) z := by simpa using hfr j z
  have e2 : u₁.fr j (z + l) = u'.fr (j PUnit.unit) (z + l) := by simpa using hfr j (z + l)
  rw [e1, e2]
  exact hAH'.2.2.2 ⟨l.1, hmem l⟩ (j PUnit.unit) z hz'
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian =====
