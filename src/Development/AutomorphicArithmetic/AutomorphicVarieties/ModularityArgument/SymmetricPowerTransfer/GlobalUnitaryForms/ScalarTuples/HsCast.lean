module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.SymbolEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private theorem hs_cast {F A : Type} [Field F] [NumberField F] [Field A] (φ : F →+* A) (p : GlobalTheory.HilbertRecip.Place F) (x d : Fˣ)
    (h : x ∈ GlobalTheory.HilbertRecip.nrm p d ↔ ∃ a b : A, φ x = a ^ 2 - φ d * b ^ 2) :
    Loc.hs (φ d) (φ x) = (((GlobalTheory.HilbertRecip.hs p x d : ℤˣ) : ℤ) : ℂ) := by
  unfold Loc.hs
  by_cases hx : x ∈ GlobalTheory.HilbertRecip.nrm p d
  · obtain ⟨a, b, e⟩ := h.1 hx
    rw [ite_eq_left ⟨a, b, e.symm⟩, GlobalTheory.HilbertRecip.hs_eq_one_iff.2 hx]
    simp
  · rw [ite_eq_right fun ⟨a, b, e⟩ => hx (h.2 ⟨a, b, e.symm⟩), GlobalTheory.HilbertRecip.hs_eq_neg_one_iff.2 hx]
    simp

theorem UpperTheory.V.Z.Sym.Glob.recip :
    UpperTheory.V.Z.Sym.Glob.Recip := by
  intro F _ _ d x hd hx
  classical
  lift d to Fˣ using hd.isUnit
  lift x to Fˣ using hx.isUnit
  have h1 : ∀ v : Pl F, Loc.hs (cv v d) (cv v x) = (((GlobalTheory.HilbertRecip.hs (.inl v) x d : ℤˣ) : ℤ) : ℂ) :=
    fun v => hs_cast (cv v) (.inl v) x d Iff.rfl
  have h2 : ∀ σ : F →+* ℝ, Loc.hs (σ d) (σ x) = (((GlobalTheory.HilbertRecip.hs (.inr σ) x d : ℤˣ) : ℤ) : ℂ) :=
    fun σ => hs_cast σ (.inr σ) x d Iff.rfl
  have hfin : {v : Pl F | x ∉ GlobalTheory.HilbertRecip.nrm (.inl v) d}.Finite :=
    (GlobalTheory.HilbertRecip.finite_not_mem_nrm x d).preimage (f := Sum.inl) Sum.inl_injective.injOn
  have hsub : {v : Pl F | Loc.hs (cv v d) (cv v x) ≠ 1} ⊆ {v : Pl F | x ∉ GlobalTheory.HilbertRecip.nrm (.inl v) d} := by
    intro v hv hm
    refine hv ?_
    rw [h1, GlobalTheory.HilbertRecip.hs_eq_one_iff.2 hm]
    simp
  refine ⟨hfin.subset hsub, ?_⟩
  have h := GlobalTheory.HilbertRecip.prod_hs x d (hfin.toFinset.disjSum Finset.univ) (by
    rintro (v | σ) hv
    · rw [Finset.inl_mem_disjSum, Set.Finite.mem_toFinset]
      exact hv
    · simp)
  rw [Finset.prod_disjSum, mul_eq_one_iff_eq_inv, Int.units_inv_eq_self] at h
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset]; exact hsub)]
  simp only [h1, h2]
  have h' := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ)) h
  simpa only [Units.coe_prod, Int.cast_prod] using h'
