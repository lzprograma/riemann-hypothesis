module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestriction, Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestrictionStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestriction =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestriction", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff\npublic import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal\npublic import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

noncomputable section


open Classical in
theorem GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ),
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χ n → ResEta D χ n := by
  intro D χ n h
  refine ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun η hη a => ?_⟩
  have hsq : ∀ x, η x * η x = 1 := GlobalTheory.VolHeckeCompare.IsEta_mul_self hη
  obtain ⟨-, h1, h2, h3⟩ := hη
  set S := (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range ⊔
    (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F)).range with hSdef
  have key : ∀ x, ((χ (idF D x) : Circle) : ℂ) = if x ∈ S then 1 else (-1) ^ n := fun x => h x
  have hS : ∀ x ∈ S, η x = 1 := by
    have : S ≤ η.ker := sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    exact fun x hx => this hx
  apply Circle.ext
  rw [key a, Circle.coe_pow]
  by_cases ha : a ∈ S
  · rw [ite_eq_left ha, hS a ha]; simp
  rw [ite_eq_right ha]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]; simp
  have hn1 : ((-1 : ℂ)) ^ n = -1 := hn.neg_one_pow
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra! hh
    exact h3 (MonoidHom.ext hh)
  have hbS : b ∉ S := fun hm => hb (hS b hm)
  have hab : a * b ∈ S := by
    by_contra hn2
    have e := key (a * b)
    rw [map_mul, map_mul, Circle.coe_mul, key a, key b, ite_eq_right ha, ite_eq_right hbS, ite_eq_right hn2, hn1] at e
    norm_num at e
  have hηb : (η b : ℂ) = -1 := GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb
  have e2 : (η a : ℂ) * η b = 1 := by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp
  rw [hηb] at e2
  have hηa : (η a : ℂ) = -1 := by linear_combination -e2
  rw [hηa]
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestriction =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestrictionStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestrictionStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff\npublic import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestriction\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

theorem _root_.GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ),
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χ n → ResEta D χ n := by
  first | exact @GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestrictionStatement =====
