module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPermOfMapEq, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWEq

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPermOfMapEq =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPermOfMapEq", "h": "module\n\npublic import Mathlib.Basic.Complex.Basic\npublic import Mathlib.Data.Fintype.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Data.Finset.Card\npublic import Mathlib.Data.Fintype.Card\npublic import Mathlib.Data.Fintype.EquivFin\n\n"}
section -- clump:auto
@[expose] public section

theorem UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq :
    ∀ {n : ℕ} (a b : Fin n → ℂ),
    Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val →
      ∃ (e : Equiv.Perm (Fin n)), ∀ (i : Fin n), b ((e : Fin n → Fin n) i) = a i := by
  intro n a b h
  classical
  have key : ∀ (f : Fin n → ℂ) (c : ℂ),
      Fintype.card {i // f i = c} = Multiset.count c (Multiset.map f Finset.univ.val) := by
    intro f c
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun _ _ => eq_comm)
  have hc : ∀ c : ℂ, Fintype.card {i // a i = c} = Fintype.card {i // b i = c} := by
    intro c
    rw [key a c, key b c, h]
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPermOfMapEq =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWEq =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWEq", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPermOfMapEq\npublic import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.schWEq_of :
    SchWEq := by
  intro F _ _ n lam χ g hg
  have h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g := ⟨g, hg⟩
  unfold schW
  rw [dite_eq_left h]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨e, he⟩ := _root_.UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq (h.choose τ) (g τ)
    ((h.choose_spec τ).symm.trans (hg τ))
  have hge : h.choose τ = g τ ∘ e := funext fun i => (he i).symm
  rw [hge]
  unfold UpperTheory.Gal.Schur.sch
  rw [← MvPolynomial.aeval_rename, GroundTheory.Heights₂.Heights.RestTerms.Schur.schur_isSymmetric (lam τ) e]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWEq =====
