module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor
public import Mathlib.Algebra.Field.IsField
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechNerveFaceOneZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackZeroCochainsAlgebraMap
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.IsPullbackH2Structure
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DnCompDn
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup0, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup1, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualFunctionalsOfLinearIndependent, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFactorOfExactIsField, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlantProductSecondAction, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValSuccAbove, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1BoundaryOfBoundary

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup0 =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup0", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe

theorem coboundary_cup0 {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {n : ℕ}
    (f : Cn F 0) (z : Cn F n) :
    dn F n (cup0 F f z) = cup1 F (dn F 0 f) z + cup0 F f (dn F n z) := by
  have hs : ∀ i : Fin (n + 1), (Fin.succAboveOrderEmb i.succ).toOrderHom.comp (vert0 n) = vert0 (n + 1) :=
    fun i ↦ DFunLike.ext _ _ fun j ↦ Fin.ext (congrArg Fin.val (Fin.succ_succAbove_zero i))
  have h0 : (Fin.succAboveOrderEmb (0 : Fin (n + 2))).toOrderHom.comp (vert0 n) =
      (front n).comp (Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom :=
    DFunLike.ext _ _ fun j ↦ by obtain rfl : j = 0 := Subsingleton.elim _ _; rfl
  have h1 : (front n).comp (Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom = vert0 (n + 1) :=
    DFunLike.ext _ _ fun j ↦ by obtain rfl : j = 0 := Subsingleton.elim _ _; rfl
  have hL : dn F n (cup0 F f z) = act F (front n) (cof F 0 0 f) * cof F n 0 z +
      ∑ i : Fin (n + 1), ((-1 : R) ^ ((i : ℕ) + 1)) • (act F (vert0 (n + 1)) f * cof F n i.succ z) := by
    simp only [dn, cup0, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Fin.sum_univ_succ]
    simp only [cof_eq, act_mul, ← act_comp, hs, h0, Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  have hd0 : dn F 0 f = cof F 0 0 f - cof F 0 1 f := by simp [dn, Fin.sum_univ_two, sub_eq_add_neg]
  have hR : dn F n z = cof F n 0 z + ∑ i : Fin (n + 1), ((-1 : R) ^ ((i : ℕ) + 1)) • cof F n i.succ z := by
    simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply]; rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  have hf1 : act F (front n) (cof F 0 1 f) = act F (vert0 (n + 1)) f := by rw [cof_eq, ← h1, act_comp]
  rw [hL, cup1, hd0, map_sub, hf1, show act F (back n) z = cof F n 0 z from rfl, cup0, hR, sub_mul, mul_add, Finset.mul_sum]
  simp only [mul_smul_comm]; abel

end GlobalTheory.CompanionTheory.HopfLe
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup0 =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup1 =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup1", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe.DnCup

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

abbrev dl (n : ℕ) (i : Fin (n + 2)) : Fin (n + 1) →o Fin (n + 2) := (Fin.succAboveOrderEmb i).toOrderHom

def incl (n : ℕ) : Fin 3 →o Fin (n + 3) := ⟨Fin.castLE (by omega), fun _ _ h ↦ h⟩

theorem dl_spec (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((j : ℕ) < i ∧ (dl n i j : ℕ) = j) ∨ ((i : ℕ) ≤ j ∧ (dl n i j : ℕ) = j + 1) := by
  change ((j : ℕ) < i ∧ (i.succAbove j : ℕ) = j) ∨ ((i : ℕ) ≤ j ∧ (i.succAbove j : ℕ) = j + 1)
  rcases Nat.lt_or_ge (j : ℕ) i with h | h
  · exact Or.inl ⟨h, by rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), Fin.val_castSucc]⟩
  · exact Or.inr ⟨h, by rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h), Fin.val_succ]⟩

theorem front_val (n : ℕ) (j : Fin 2) : (front n j : ℕ) = j := rfl

theorem back_val (n : ℕ) (j : Fin (n + 1)) : (back n j : ℕ) = j + 1 := by
  simp [back, Fin.succAbove]

theorem incl_val (n : ℕ) (j : Fin 3) : (incl n j : ℕ) = j := rfl

theorem dl_front_high (n : ℕ) (k : Fin (n + 1)) : (dl (n + 1) k.succ.succ).comp (front n) = front (n + 1) := by
  refine DFunLike.ext _ _ fun j ↦ Fin.ext ?_
  have := dl_spec (n + 1) k.succ.succ (front n j); have := front_val n j; have := front_val (n + 1) j; have := j.isLt
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_succ] at *; lia

theorem dl_back_high (n : ℕ) (k : Fin (n + 1)) :
    (dl (n + 1) k.succ.succ).comp (back n) = (back (n + 1)).comp (dl n k.succ) := by
  refine DFunLike.ext _ _ fun j ↦ Fin.ext ?_
  have := dl_spec (n + 1) k.succ.succ (back n j); have := dl_spec n k.succ j
  have := back_val n j; have := back_val (n + 1) (dl n k.succ j)
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_succ] at *; lia

theorem dl_back_zero (n : ℕ) : (dl (n + 1) 0).comp (back n) = (back (n + 1)).comp (dl n 0) := by
  refine DFunLike.ext _ _ fun j ↦ Fin.ext ?_
  have := dl_spec (n + 1) 0 (back n j); have := dl_spec n 0 j
  have := back_val n j; have := back_val (n + 1) (dl n 0 j)
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero] at *; lia

theorem dl_back_one (n : ℕ) : (dl (n + 1) 1).comp (back n) = (back (n + 1)).comp (dl n 0) := by
  refine DFunLike.ext _ _ fun j ↦ Fin.ext ?_
  have := dl_spec (n + 1) 1 (back n j); have := dl_spec n 0 j
  have := back_val n j; have := back_val (n + 1) (dl n 0 j)
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero, Fin.val_one] at *; lia

theorem dl_front_zero (n : ℕ) : (dl (n + 1) 0).comp (front n) = (incl n).comp (dl 1 0) := by
  refine DFunLike.ext _ _ fun j ↦ Fin.ext ?_
  have := dl_spec (n + 1) 0 (front n j); have := dl_spec 1 0 j
  have := front_val n j; have := incl_val n (dl 1 0 j)
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_zero] at *; lia

theorem dl_front_one (n : ℕ) : (dl (n + 1) 1).comp (front n) = (incl n).comp (dl 1 1) := by
  refine DFunLike.ext _ _ fun j ↦ Fin.ext ?_
  have := dl_spec (n + 1) 1 (front n j); have := dl_spec 1 1 j
  have := front_val n j; have := incl_val n (dl 1 1 j)
  simp only [OrderHom.comp_coe, Function.comp_apply, Fin.val_one] at *; lia

theorem front_eq_incl (n : ℕ) : front (n + 1) = (incl n).comp (dl 1 2) := by
  refine DFunLike.ext _ _ fun j ↦ Fin.ext ?_
  have := dl_spec 1 2 j; have := front_val (n + 1) j; have := incl_val n (dl 1 2 j); have := j.isLt
  have h2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  simp only [OrderHom.comp_coe, Function.comp_apply] at *; lia

theorem bracket (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (y : Cn F 1) (hy : dn F 1 y = 0) :
    act F ((dl (n + 1) 0).comp (front n)) y - act F ((dl (n + 1) 1).comp (front n)) y
      + act F (front (n + 1)) y = 0 := by
  have hd : dn F 1 y = act F (dl 1 0) y - act F (dl 1 1) y + act F (dl 1 2) y := by
    rw [dn, LinearMap.sum_apply, Fin.sum_univ_three]
    simp only [cof_eq, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_smul, neg_smul, sub_eq_add_neg]; rfl
  rw [dl_front_zero, dl_front_one, front_eq_incl, act_comp, act_comp, act_comp, ← map_sub, ← map_add, ← hd, hy, map_zero]

theorem coboundary_cup1 (F : C ⥤ CommAlgCat.{0} R) {n : ℕ} (y : Cn F 1) (z : Cn F n) (hy : dn F 1 y = 0) :
    dn F (n + 1) (cup1 F y z) = - cup1 F y (dn F n z) := by
  have hcup : ∀ i : Fin (n + 3), cof F (n + 1) i (cup1 F y z) =
      act F ((dl (n + 1) i).comp (front n)) y * act F ((dl (n + 1) i).comp (back n)) z := fun i ↦ by
    rw [cof_eq, cup1, act_mul, act_comp, act_comp]
  have h' := eq_neg_iff_add_eq_zero.mpr (bracket F n y hy)
  have key : act F ((dl (n + 1) 0).comp (front n)) y * act F (back (n + 1)) (act F (dl n 0) z) =
      act F ((dl (n + 1) 1).comp (front n)) y * act F (back (n + 1)) (act F (dl n 0) z) +
      -(act F (front (n + 1)) y * act F (back (n + 1)) (act F (dl n 0) z)) := by
    rw [← neg_mul, ← add_mul, ← h']; congr 1; abel
  have h0 : cof F (n + 1) 0 (cup1 F y z) =
      act F ((dl (n + 1) 0).comp (front n)) y * act F (back (n + 1)) (act F (dl n 0) z) := by
    rw [hcup, dl_back_zero]; exact congrArg (_ * ·) (act_comp F (dl n 0) (back (n + 1)) z)
  have h1 : cof F (n + 1) 1 (cup1 F y z) =
      act F ((dl (n + 1) 1).comp (front n)) y * act F (back (n + 1)) (act F (dl n 0) z) := by
    rw [hcup, dl_back_one]; exact congrArg (_ * ·) (act_comp F (dl n 0) (back (n + 1)) z)
  have hk : ∀ k : Fin (n + 1), cof F (n + 1) k.succ.succ (cup1 F y z) =
      act F (front (n + 1)) y * act F (back (n + 1)) (act F (dl n k.succ) z) := fun k ↦ by
    rw [hcup, dl_back_high, dl_front_high]; exact congrArg (_ * ·) (act_comp F (dl n k.succ) (back (n + 1)) z)
  simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun i : Fin (n + 2) ↦ _), Fin.sum_univ_succ (f := fun i : Fin (n + 2) ↦ _),
    ← add_assoc, h0, show (Fin.succ 0 : Fin (n + 3)) = 1 from rfl, h1]
  simp only [hk]
  simp only [cof_eq, cup1, map_add (f := _), map_neg, map_sum, map_smul, mul_add, Finset.mul_sum,
    mul_smul_comm, Fin.val_zero, Fin.val_one, Fin.val_succ, pow_zero, pow_succ, one_smul, neg_smul,
    mul_neg, mul_one, neg_neg, Finset.sum_neg_distrib]
  rw [key]; abel

end GlobalTheory.CompanionTheory.HopfLe.DnCup
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup1 =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualFunctionalsOfLinearIndependent =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualFunctionalsOfLinearIndependent", "h": "module\n\npublic import Mathlib.Algebra.Field.IsField\npublic import Mathlib.LinearAlgebra.LinearIndependent.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne\nimport Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor\nimport Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DnCompDn\nimport Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange\npublic import Mathlib.LinearAlgebra.Basis.Basic\npublic import Mathlib.LinearAlgebra.Basis.VectorSpace\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe

theorem exists_dual_functionals_of_linearIndependent :
    ∀ {R V ι : Type} [CommRing R] [AddCommGroup V] [Module R V] [DecidableEq ι], IsField R →
      ∀ x : ι → V, LinearIndependent R x →
        ∃ l : ι → V →ₗ[R] R, ∀ i j, l i (x j) = if i = j then 1 else 0 := by
  intro R V ι _ _ _ _ hR x hx
  let : Field R := hR.toField
  let b := Module.Basis.span hx
  choose l hl using fun i ↦ LinearMap.exists_extend (b.coord i)
  refine ⟨l, fun i j ↦ ?_⟩
  have hb : ∀ k, (b k : V) = x k := fun k ↦ congrArg Subtype.val (Module.Basis.span_apply hx k)
  have h : l i (b j : V) = b.coord i (b j) := LinearMap.congr_fun (hl i) (b j)
  rw [hb j] at h
  rw [h, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]; simp only [eq_comm]

end GlobalTheory.CompanionTheory.HopfLe
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualFunctionalsOfLinearIndependent =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFactorOfExactIsField =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFactorOfExactIsField", "h": "module\n\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor\nimport Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DnCompDn\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe

theorem exists_factor_of_exact_field {K A B D : Type} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup D] [Module K D]
    (f : A →ₗ[K] B) (g : B →ₗ[K] D) (hfg : Function.Exact f g) (μ : B →ₗ[K] K)
    (hμ : ∀ a, μ (f a) = 0) : ∃ ρ : D →ₗ[K] K, μ = ρ ∘ₗ g := by
  have hle : LinearMap.ker g ≤ LinearMap.ker μ := fun b hb ↦ by
    obtain ⟨a, rfl⟩ := (hfg b).1 hb; exact hμ a
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_extend
    ((LinearMap.ker g).liftQ μ hle ∘ₗ (g.quotKerEquivRange.symm : LinearMap.range g →ₗ[K] B ⧸ LinearMap.ker g))
  refine ⟨ρ, LinearMap.ext fun b ↦ ?_⟩
  change (LinearMap.ker g).liftQ μ hle ((LinearMap.ker g).mkQ b) = _
  rw [← LinearMap.quotKerEquivRange_symm_apply_image]
  exact (LinearMap.congr_fun hρ ⟨g b, LinearMap.mem_range_self g b⟩).symm

theorem exists_factor_of_exact_isField {K A B D : Type} [CommRing K] (hK : IsField K)
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup D] [Module K D]
    (f : A →ₗ[K] B) (g : B →ₗ[K] D) (hfg : Function.Exact f g) (μ : B →ₗ[K] K)
    (hμ : ∀ a, μ (f a) = 0) : ∃ ρ : D →ₗ[K] K, μ = ρ ∘ₗ g := by
  let := hK.toField
  exact exists_factor_of_exact_field f g hfg μ hμ

theorem exists_rho_of_exact {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hR : IsField R)
    (hex : Function.Exact (Algebra.linearMap R (Cn F 0)) (dn F 0))
    (ν ν₀ : Cn F 0 →ₗ[R] R) (h1 : ν₀ 1 = 1) :
    ∃ ρ : Cn F 1 →ₗ[R] R, ν = ν 1 • ν₀ + ρ ∘ₗ dn F 0 := by
  obtain ⟨ρ, hρ⟩ := exists_factor_of_exact_isField hR _ _ hex (ν - ν 1 • ν₀) fun r ↦ by
    simp [Algebra.algebraMap_eq_smul_one, h1]
  exact ⟨ρ, by rw [← hρ]; abel⟩

end GlobalTheory.CompanionTheory.HopfLe
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFactorOfExactIsField =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlantProductSecondAction =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlantProductSecondAction", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechNerveFaceOneZero\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackZeroCochainsAlgebraMap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx

namespace GlobalTheory.CompanionTheory.HopfLe

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

section Slant

variable {ι : Type} [Fintype ι] {M : ι → Type} [∀ i, CommRing (M i)] [∀ i, Algebra R (M i)]
  {V : Type} [CommRing V] [Algebra R V]


open Classical in
def slv (Λ : (∀ i, M i) →ₗ[R] R) : (∀ i, M i ⊗[R] V) →ₗ[R] V :=
  ∑ i, (TensorProduct.lid R V).toLinearMap ∘ₗ LinearMap.rTensor V (Λ ∘ₗ LinearMap.single R M i) ∘ₗ
    LinearMap.proj (φ := fun i ↦ M i ⊗[R] V) i

theorem slv_pure (Λ : (∀ i, M i) →ₗ[R] R) (f : ∀ i, M i) (v : V) :
    slv Λ (fun i ↦ f i ⊗ₜ[R] v) = Λ f • v := by
  classical
  simp only [slv, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.rTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul]
  rw [← Finset.sum_smul, ← map_sum]
  congr 2; ext j; simp [Finset.sum_apply]

theorem slv_ext {W : Type} [AddCommGroup W] [Module R W] (A B : (∀ i, M i ⊗[R] V) →ₗ[R] W)
    (h : ∀ (f : ∀ i, M i) (v : V), A (fun i ↦ f i ⊗ₜ[R] v) = B (fun i ↦ f i ⊗ₜ[R] v)) : A = B := by
  classical
  refine LinearMap.pi_ext' fun i ↦ TensorProduct.ext' fun a v ↦ ?_
  have e : (LinearMap.single R (fun i ↦ M i ⊗[R] V) i) (a ⊗ₜ[R] v) =
      fun j ↦ (Pi.single i a : ∀ j, M j) j ⊗ₜ[R] v := funext fun j ↦ by
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  simp only [LinearMap.comp_apply, e, h]

theorem slv_add (Λ Λ' : (∀ i, M i) →ₗ[R] R) (t : ∀ i, M i ⊗[R] V) :
    slv (Λ + Λ') t = slv Λ t + slv Λ' t :=
  LinearMap.congr_fun (slv_ext (slv (Λ + Λ')) (slv Λ + slv Λ') fun f v ↦ by simp [slv_pure, add_smul]) t

theorem slv_smul (r : R) (Λ : (∀ i, M i) →ₗ[R] R) (t : ∀ i, M i ⊗[R] V) :
    slv (r • Λ) t = r • slv Λ t :=
  LinearMap.congr_fun (slv_ext (slv (r • Λ)) (r • slv Λ) fun f v ↦ by simp [slv_pure, mul_smul]) t

theorem slv_zero (t : ∀ i, M i ⊗[R] V) : slv (0 : (∀ i, M i) →ₗ[R] R) t = 0 :=
  LinearMap.congr_fun (slv_ext (slv (0 : (∀ i, M i) →ₗ[R] R)) 0 fun f v ↦ by simp [slv_pure]) t

theorem slv_sub (Λ Λ' : (∀ i, M i) →ₗ[R] R) (t : ∀ i, M i ⊗[R] V) :
    slv (Λ - Λ') t = slv Λ t - slv Λ' t :=
  LinearMap.congr_fun (slv_ext (slv (Λ - Λ')) (slv Λ - slv Λ') fun f v ↦ by simp [slv_pure, sub_smul]) t

theorem map_slv {V' : Type} [CommRing V'] [Algebra R V'] (g : V →ₗ[R] V') (Λ : (∀ i, M i) →ₗ[R] R)
    (t : ∀ i, M i ⊗[R] V) : g (slv Λ t) = slv Λ (fun i ↦ TensorProduct.map LinearMap.id g (t i)) :=
  LinearMap.congr_fun (slv_ext (g ∘ₗ slv Λ)
    ((slv Λ : (∀ i, M i ⊗[R] V') →ₗ[R] V') ∘ₗ LinearMap.pi fun i ↦ TensorProduct.map LinearMap.id g ∘ₗ LinearMap.proj i)
    fun f v ↦ by simp only [LinearMap.comp_apply, slv_pure, map_smul]; exact (slv_pure (V := V') Λ f (g v)).symm) t

theorem slv_mul_right (Λ : (∀ i, M i) →ₗ[R] R) (e : V) (t : ∀ i, M i ⊗[R] V) :
    slv Λ (fun i ↦ ((1 : M i) ⊗ₜ[R] e) * t i) = e * slv Λ t :=
  LinearMap.congr_fun (slv_ext
    ((slv Λ : (∀ i, M i ⊗[R] V) →ₗ[R] V) ∘ₗ LinearMap.pi fun i ↦ LinearMap.mulLeft R ((1 : M i) ⊗ₜ[R] e) ∘ₗ LinearMap.proj i)
    (LinearMap.mulLeft R e ∘ₗ slv Λ) fun f v ↦ by
      simp only [LinearMap.comp_apply, slv_pure, LinearMap.mulLeft_apply, mul_smul_comm]
      rw [← slv_pure]; congr 1; funext i; simp [Algebra.TensorProduct.tmul_mul_tmul]) t

theorem slv_mul_left (Λ : (∀ i, M i) →ₗ[R] R) (x : ∀ i, M i) (t : ∀ i, M i ⊗[R] V) :
    slv Λ (fun i ↦ (x i ⊗ₜ[R] (1 : V)) * t i) = slv (Λ ∘ₗ LinearMap.mulLeft R x) t :=
  LinearMap.congr_fun (slv_ext
    ((slv Λ : (∀ i, M i ⊗[R] V) →ₗ[R] V) ∘ₗ LinearMap.pi fun i ↦ LinearMap.mulLeft R (x i ⊗ₜ[R] (1 : V)) ∘ₗ LinearMap.proj i)
    (slv (Λ ∘ₗ LinearMap.mulLeft R x)) fun f v ↦ by
      simp only [LinearMap.comp_apply, slv_pure, LinearMap.mulLeft_apply]
      rw [← slv_pure]; congr 1; funext i; simp [Algebra.TensorProduct.tmul_mul_tmul]) t

theorem slv_proj (i₀ : ι) (l : M i₀ →ₗ[R] R) (t : ∀ i, M i ⊗[R] V) :
    slv (l ∘ₗ LinearMap.proj i₀) t = TensorProduct.lid R V (LinearMap.rTensor V l (t i₀)) :=
  LinearMap.congr_fun (slv_ext (slv (l ∘ₗ LinearMap.proj i₀))
    ((TensorProduct.lid R V).toLinearMap ∘ₗ LinearMap.rTensor V l ∘ₗ LinearMap.proj i₀) fun f v ↦ by simp [slv_pure]) t

end Slant

section Sl

variable (F : C ⥤ CommAlgCat.{0} R)

theorem sl_eq {p : ℕ} [Fintype (Fin (p + 1) ⥤ C)] (q : ℕ) (Λ : Cn F p →ₗ[R] R) (y : Y F p q)
    (b : Fin (q + 1) ⥤ C) :
    sl F q Λ y b = slv (M := fun c : Fin (p + 1) ⥤ C ↦ F.obj (c.obj (Fin.last p))) Λ (fun c ↦ y c b) := by
  simp [sl, slv, LinearMap.sum_apply]

theorem sl_sub {p : ℕ} [Fintype (Fin (p + 1) ⥤ C)] (q : ℕ) (Λ Λ' : Cn F p →ₗ[R] R) (y : Y F p q) :
    sl F q (Λ - Λ') y = sl F q Λ y - sl F q Λ' y := funext fun b ↦ by
  simp only [sl_eq, Pi.sub_apply]; exact slv_sub _ _ _

theorem slant_product_first_action {p p' : ℕ} [Fintype (Fin (p + 1) ⥤ C)] [Fintype (Fin (p' + 1) ⥤ C)] (q : ℕ)
    (θ : Fin (p + 1) →o Fin (p' + 1)) (ρ : Cn F p' →ₗ[R] R) (y : Y F p q) :
    sl F q ρ (a1 F θ y) = sl F q (ρ ∘ₗ act F θ) y := funext fun b ↦ by
  simp only [sl_eq]
  exact LinearMap.congr_fun (slv_ext
    ((slv (M := fun c : Fin (p' + 1) ⥤ C ↦ F.obj (c.obj (Fin.last p'))) (V := F.obj (b.obj (Fin.last q))) ρ) ∘ₗ
      LinearMap.pi fun c : Fin (p' + 1) ⥤ C ↦
        TensorProduct.map (mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last p)))))).toLinearMap LinearMap.id ∘ₗ
          LinearMap.proj (φ := fun c : Fin (p + 1) ⥤ C ↦ F.obj (c.obj (Fin.last p)) ⊗[R] F.obj (b.obj (Fin.last q)))
            (θ.monotone.functor ⋙ c))
    (slv (M := fun c : Fin (p + 1) ⥤ C ↦ F.obj (c.obj (Fin.last p))) (ρ ∘ₗ act F θ)) fun f v ↦ by
      simp only [LinearMap.comp_apply, slv_pure]; rw [← slv_pure]; congr 1) (fun c ↦ y c b)

theorem slant_product_second_action {p q q' : ℕ} [Fintype (Fin (p + 1) ⥤ C)] (ψ : Fin (q + 1) →o Fin (q' + 1))
    (ρ : Cn F p →ₗ[R] R) (y : Y F p q) :
    sl F q' ρ (a2 F ψ y) = act F ψ (sl F q ρ y) := funext fun b ↦ by
  rw [act_apply, sl_eq, sl_eq]
  exact (map_slv (mp F (b.map (homOfLE (Fin.le_last (ψ (Fin.last q)))))).toLinearMap ρ _).symm

end Sl

section Vertices

theorem th_apply (q : ℕ) (i : Fin (q + 1)) (j : Fin (q + 2)) : th q i j = if j ≤ i.castSucc then 0 else 1 := rfl

theorem sg_apply (q : ℕ) (i : Fin (q + 1)) (j : Fin (q + 2)) : sg q i j = Fin.predAbove i j := rfl

theorem cst_apply (n p : ℕ) (a : Fin (p + 1)) (j : Fin (n + 1)) : cst n a j = a := rfl

theorem front_zero (n : ℕ) : front n 0 = 0 := rfl

theorem front_one (n : ℕ) : front n 1 = 1 := Fin.ext (by simp; rfl)

theorem back_apply (n : ℕ) (j : Fin (n + 1)) : back n j = j.succ := by simp [back]

theorem th_front0 (q : ℕ) : (th (q + 1) 0).comp (front (q + 1)) = OrderHom.id := by
  ext j; fin_cases j <;> simp [th_apply, front_zero, front_one]

theorem th_back0 (q : ℕ) : (th (q + 1) 0).comp (back (q + 1)) = cst (q + 1) 1 := by
  ext j; simp [th_apply, back_apply, cst_apply]

theorem sg_back0 (q : ℕ) : (sg (q + 1) 0).comp (back (q + 1)) = OrderHom.id := by
  ext j; simp [sg_apply, back_apply]

theorem sg_front0 (q : ℕ) : ((sg (q + 1) 0).comp (front (q + 1))) 0 = ((sg (q + 1) 0).comp (front (q + 1))) 1 := by
  simp [sg_apply, front_zero, front_one, Fin.predAbove]

theorem th_frontS (q : ℕ) (i : Fin (q + 1)) :
    ((th (q + 1) i.succ).comp (front (q + 1))) 0 = ((th (q + 1) i.succ).comp (front (q + 1))) 1 := by
  simp [th_apply, front_zero, front_one, Fin.le_def]

theorem sg_frontS (q : ℕ) (i : Fin (q + 1)) : (sg (q + 1) i.succ).comp (front (q + 1)) = front q := by
  ext j; fin_cases j <;> simp [sg_apply, front_zero, front_one, Fin.predAbove, Fin.lt_def]

theorem th_backS (q : ℕ) (i : Fin (q + 1)) : (th (q + 1) i.succ).comp (back (q + 1)) = th q i := by
  ext j; simp [th_apply, back_apply, Fin.le_def]

theorem sg_backS (q : ℕ) (i : Fin (q + 1)) :
    (sg (q + 1) i.succ).comp (back (q + 1)) = (back q).comp (sg q i) := by
  ext j
  simp only [OrderHom.comp_coe, Function.comp_apply, sg_apply, back_apply, Fin.predAbove, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all [Fin.val_pred] <;> lia

end Vertices

section Cup

variable (F : C ⥤ CommAlgCat.{0} R)

theorem S_apply (q : ℕ) (w : Cn (box F) (q + 1)) :
    S F q w = ∑ i : Fin (q + 1), ((-1 : R) ^ (i : ℕ)) • bi F (th q i) (sg q i) w := by
  simp [S, LinearMap.sum_apply]

theorem shuffle_cup1_formula (q : ℕ) (y : Cn (box F) 1) (w : Cn (box F) (q + 1)) :
    S F (q + 1) (cup1 (box F) y w) = ∑ i : Fin (q + 2), ((-1 : R) ^ (i : ℕ)) •
      (bi F ((th (q + 1) i).comp (front (q + 1))) ((sg (q + 1) i).comp (front (q + 1))) y *
        bi F ((th (q + 1) i).comp (back (q + 1))) ((sg (q + 1) i).comp (back (q + 1))) w) := by
  simp only [S_apply, cup1, bi_mul, bi_act]

theorem S_cup_R (q : ℕ) (x : Cn F 1) (hx : dn F 1 x = 0) (w : Cn (box F) (q + 1))
    (c : Fin 2 ⥤ C) (b : Fin (q + 2) ⥤ C) :
    S F (q + 1) (cup1 (box F) (pulln (boxR F) 1 x) w) c b =
      ((1 : F.obj (c.obj (Fin.last 1))) ⊗ₜ[R] (- act F (front q) x b)) * a2 F (back q) (S F q w) c b := by
  rw [shuffle_cup1_formula, Fin.sum_univ_succ]
  have h0 : bi F ((th (q + 1) 0).comp (front (q + 1))) ((sg (q + 1) 0).comp (front (q + 1)))
      (pulln (boxR F) 1 x) = 0 := funext fun c' ↦ funext fun b' ↦ by
    rw [bi_boxR, act_const F x hx _ (sg_front0 q)]; simp
  have hS : a2 F (back q) (S F q w) =
      ∑ i : Fin (q + 1), ((-1 : R) ^ (i : ℕ)) • bi F (th q i) ((back q).comp (sg q i)) w := by
    simp only [S_apply, map_sum, map_smul, bisimplicial_action_second_factor]
  rw [h0, zero_mul, smul_zero, zero_add, hS, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply,
    Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.smul_apply, Pi.mul_apply, bi_boxR, th_backS, sg_backS, Fin.val_succ, pow_succ, mul_neg,
    mul_one, neg_smul, TensorProduct.tmul_neg, neg_mul, mul_smul_comm]
  rw [congrArg (fun θ ↦ act F θ x) (sg_frontS q i), smul_neg]

theorem S_cup_L (q : ℕ) (x : Cn F 1) (hx : dn F 1 x = 0) (w : Cn (box F) (q + 1))
    (c : Fin 2 ⥤ C) (b : Fin (q + 2) ⥤ C) :
    S F (q + 1) (cup1 (box F) (pulln (boxL F) 1 x) w) c b =
      (x c ⊗ₜ[R] (1 : F.obj (b.obj (Fin.last (q + 1))))) * a1 F (cst 0 (1 : Fin 2)) (S0 F (q + 1) w) c b := by
  rw [shuffle_cup1_formula, Fin.sum_univ_succ]
  have h0 : ∀ i : Fin (q + 1), bi F ((th (q + 1) i.succ).comp (front (q + 1)))
      ((sg (q + 1) i.succ).comp (front (q + 1))) (pulln (boxL F) 1 x) = 0 := fun i ↦ funext fun c' ↦ funext fun b' ↦ by
    rw [bi_boxL, act_const F x hx _ (th_frontS q i)]; simp
  have e : (cst 0 (1 : Fin 2)).comp (cst (q + 1) (0 : Fin 1)) = cst (q + 1) (1 : Fin 2) := rfl
  simp only [h0, zero_mul, smul_zero, Finset.sum_const_zero, add_zero, th_back0, sg_back0, Fin.val_zero,
    pow_zero, one_smul, S0, bisimplicial_action_first_factor, e]
  rw [Pi.mul_apply, Pi.mul_apply, bi_boxL, (congrArg (fun θ ↦ act F θ x) (th_front0 q)).trans (act_id F x)]

theorem T_cup_R [Fintype (Fin 2 ⥤ C)] (q : ℕ) (Λ : Cn F 1 →ₗ[R] R) (x : Cn F 1) (hx : dn F 1 x = 0)
    (w : Cn (box F) (q + 1)) :
    T F (q + 1) Λ (cup1 (box F) (pulln (boxR F) 1 x) w) = - cup1 F x (T F q Λ w) := funext fun b ↦ by
  change sl F (q + 1) Λ (S F (q + 1) _) b = _
  rw [sl_eq]; simp only [S_cup_R F q x hx w]
  rw [slv_mul_right, ← sl_eq, slant_product_second_action]
  change _ = -(act F (front q) x b * act F (back q) (sl F q Λ (S F q w)) b); rw [neg_mul]

theorem T_cup_L [Fintype (Fin 1 ⥤ C)] [Fintype (Fin 2 ⥤ C)] (q : ℕ) (Λ : Cn F 1 →ₗ[R] R) (x : Cn F 1)
    (hx : dn F 1 x = 0) (w : Cn (box F) (q + 1)) :
    T F (q + 1) Λ (cup1 (box F) (pulln (boxL F) 1 x) w) = U F (q + 1) (nu F Λ x) w := funext fun b ↦ by
  change sl F (q + 1) Λ (S F (q + 1) _) b = sl F (q + 1) _ (S0 F (q + 1) w) b
  rw [sl_eq]; simp only [S_cup_L F q x hx w]
  rw [slv_mul_left (M := fun c : Fin 2 ⥤ C ↦ F.obj (c.obj (Fin.last 1))), ← sl_eq, slant_product_first_action]; rfl

theorem T_base [Fintype (Fin 2 ⥤ C)] (Λ : Cn F 1 →ₗ[R] R) (x : Cn F 1) (hx : dn F 1 x = 0) :
    T F 0 Λ (pulln (boxL F) 1 x + pulln (boxR F) 1 x) = Λ x • (1 : Cn F 0) := funext fun b ↦ by
  change sl F 0 Λ (S F 0 _) b = _
  rw [sl_eq]
  have e1 : th 0 0 = OrderHom.id := by ext j; fin_cases j <;> simp [th_apply]
  have h : ∀ c : Fin 2 ⥤ C, S F 0 (pulln (boxL F) 1 x + pulln (boxR F) 1 x) c b =
      x c ⊗ₜ[R] (1 : F.obj (b.obj (Fin.last 0))) := fun c ↦ by
    rw [S_apply, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, map_add (f := _), Pi.add_apply, bi_boxL, bi_boxR, e1, act_id]
    rw [act_const F x hx (sg 0 0) (Subsingleton.elim (α := Fin 1) _ _)]; simp
  simp only [h]
  exact slv_pure (M := fun c : Fin 2 ⥤ C ↦ F.obj (c.obj (Fin.last 1))) Λ x _

theorem U_add [Fintype (Fin 1 ⥤ C)] (q : ℕ) (ν ν' : Cn F 0 →ₗ[R] R) (w : Cn (box F) q) :
    U F q (ν + ν') w = U F q ν w + U F q ν' w := funext fun b ↦ by
  change sl F q _ _ b = sl F q _ _ b + sl F q _ _ b; simp only [sl_eq]; exact slv_add _ _ _

theorem U_smul [Fintype (Fin 1 ⥤ C)] (q : ℕ) (r : R) (ν : Cn F 0 →ₗ[R] R) (w : Cn (box F) q) :
    U F q (r • ν) w = r • U F q ν w := funext fun b ↦ by
  change sl F q _ _ b = r • sl F q _ _ b; simp only [sl_eq]; exact slv_smul _ _ _

theorem U_zero [Fintype (Fin 1 ⥤ C)] (q : ℕ) (w : Cn (box F) q) :
    U F q (0 : Cn F 0 →ₗ[R] R) w = 0 := funext fun b ↦ by
  change sl F q _ _ b = 0; simp only [sl_eq]; exact slv_zero _

end Cup

section Tau

variable (F : C ⥤ CommAlgCat.{0} R)

theorem tau_R (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (n : ℕ) (x : Cn F n) :
    pulln (boxE F T₀ ε) n (pulln (boxR F) n x) = x := funext fun b ↦ by
  change evL F T₀ _ ε ((1 : F.obj T₀) ⊗ₜ[R] x b) = x b; simp [evL, Algebra.ofId_apply]

theorem tau_L (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (x : Cn F 1) (hx : dn F 1 x = 0) :
    pulln (boxE F T₀ ε) 1 (pulln (boxL F) 1 x) = 0 := funext fun b ↦ by
  have hz : GlobalTheory.CompanionTheory.Dict.L1 F x ∈ Z1 F := by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, ← GlobalTheory.CompanionTheory.Dict.L2_dn_one_eq_d1_L1, hx, map_zero]
  have h1 : x (ComposableArrows.mk₁ (𝟙 T₀)) = 0 := Z1.id ⟨_, hz⟩ T₀
  have h0 : (x (b ⋙ (boxE F T₀ ε).G ⋙ (boxL F).G) : F.obj T₀) = 0 :=
    eq_of_heq ((GlobalTheory.CompanionTheory.HodgeLow.cn_heq x (GlobalTheory.CompanionTheory.Dict.eq_mk₁ _ _ rfl)).trans (heq_of_eq h1))
  change evL F T₀ _ ε ((x (b ⋙ (boxE F T₀ ε).G ⋙ (boxL F).G) : F.obj T₀) ⊗ₜ[R] 1) = 0
  have h2 : ((0 : F.obj T₀) ⊗ₜ[R] (1 : F.obj (b.obj (Fin.last 1)))) = 0 := TensorProduct.zero_tmul _ _
  rw [h0]
  exact (congrArg (evL F T₀ (b.obj (Fin.last 1)) ε) h2).trans (map_zero _)

theorem lid_evL (T₀ T : C) (ε : F.obj T₀ →ₐ[R] R) (t : F.obj T₀ ⊗[R] F.obj T) :
    TensorProduct.lid R (F.obj T) (LinearMap.rTensor (F.obj T) ε.toLinearMap t) = evL F T₀ T ε t := by
  induction t with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a b => simp [evL, Algebra.ofId_apply, Algebra.smul_def]

theorem U_evz [Fintype (Fin 1 ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (q : ℕ) (w : Cn (box F) q) :
    U F q (evz F T₀ ε) w = pulln (boxE F T₀ ε) q w := funext fun b ↦ by
  change sl F q (evz F T₀ ε) (S0 F q w) b = evL F T₀ _ ε (w (b ⋙ (boxE F T₀ ε).G))
  rw [sl_eq]
  refine (slv_proj (M := fun c : Fin 1 ⥤ C ↦ F.obj (c.obj (Fin.last 0))) (V := F.obj (b.obj (Fin.last q)))
    (ComposableArrows.mk₀ T₀) ε.toLinearMap (fun c ↦ S0 F q w c b)).trans ?_
  have e : pc (cst q 0) OrderHom.id (ComposableArrows.mk₀ T₀) b = b ⋙ (boxE F T₀ ε).G :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) fun i j f ↦ Prod.ext
      (by
        have e1 : 𝟙 T₀ ≫ 𝟙 T₀ ≫ 𝟙 T₀ = 𝟙 T₀ := by simp
        exact ((ComposableArrows.mk₀ T₀).map_id 0).trans e1.symm)
      (by change b.map _ = 𝟙 _ ≫ b.map f ≫ 𝟙 _; rw [Category.id_comp, Category.comp_id]; exact congrArg b.map (Subsingleton.elim _ _))
  have hl : pcLast (cst q 0) OrderHom.id (ComposableArrows.mk₀ T₀) b = 𝟙 ((T₀, b.obj (Fin.last q)) : C × C) :=
    Prod.ext ((ComposableArrows.mk₀ T₀).map_id 0) ((congrArg b.map (Subsingleton.elim _ _)).trans (b.map_id (Fin.last q)))
  have h2 : ∀ (P : Fin (q + 1) ⥤ C × C) (_ : P = b ⋙ (boxE F T₀ ε).G)
      (g : P.obj (Fin.last q) ⟶ (T₀, b.obj (Fin.last q))) (_ : HEq g (𝟙 ((T₀, b.obj (Fin.last q)) : C × C))),
      (mp (box F) g (w P) : F.obj T₀ ⊗[R] F.obj (b.obj (Fin.last q))) = w (b ⋙ (boxE F T₀ ε).G) := by
    intro P h g hg; subst h; obtain rfl := eq_of_heq hg; exact mp_id (box F) _ _
  exact (congrArg (fun z ↦ TensorProduct.lid R (F.obj (b.obj (Fin.last q)))
    (LinearMap.rTensor (F.obj (b.obj (Fin.last q))) ε.toLinearMap z)) (h2 _ e _ (heq_of_eq hl))).trans (lid_evL F T₀ _ ε _)

end Tau

end GlobalTheory.CompanionTheory.HopfLe
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlantProductSecondAction =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValSuccAbove =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValSuccAbove", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe.PrismComb

def stepMap (q n : ℕ) : Fin (q + 2) →o Fin 2 :=
  ⟨fun x ↦ if (x : ℕ) < n then 0 else 1, fun a b h ↦ by
    have : (a : ℕ) ≤ b := h; dsimp only; split_ifs <;> first | exact le_rfl | exact Fin.zero_le _ | lia⟩

theorem th_apply (q : ℕ) (i : Fin (q + 1)) (x : Fin (q + 2)) :
    th q i x = if (x : ℕ) ≤ i then 0 else 1 := by
  change (if x ≤ i.castSucc then (0 : Fin 2) else 1) = _
  simp only [Fin.le_def, Fin.val_castSucc]

theorem val_succAbove {n : ℕ} (j : Fin (n + 1)) (x : Fin n) :
    ((j.succAbove x : Fin (n + 1)) : ℕ) = if (x : ℕ) < j then (x : ℕ) else x + 1 := by
  unfold Fin.succAbove; simp only [Fin.lt_def, Fin.val_castSucc]; split_ifs <;> simp

theorem val_predAbove {n : ℕ} (i : Fin n) (x : Fin (n + 1)) :
    ((Fin.predAbove i x : Fin n) : ℕ) = if (i : ℕ) < x then (x : ℕ) - 1 else x := by
  unfold Fin.predAbove; simp only [Fin.lt_def, Fin.val_castSucc]; split_ifs <;> simp

theorem val_sg (q : ℕ) (i : Fin (q + 1)) (x : Fin (q + 2)) :
    ((sg q i x : Fin (q + 1)) : ℕ) = if (i : ℕ) < x then (x : ℕ) - 1 else x :=
  val_predAbove i x

theorem th_diag (q : ℕ) (i : Fin (q + 2)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom = stepMap q i := by
  ext x; change (th (q + 1) i (i.castSucc.succAbove x) : ℕ) = ((if (x : ℕ) < i then (0 : Fin 2) else 1 : Fin 2) : ℕ)
  rw [th_apply, val_succAbove]; simp only [Fin.val_castSucc]; split_ifs <;> first | rfl | lia

theorem th_next (q : ℕ) (i : Fin (q + 2)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom = stepMap q (i + 1) := by
  ext x; change (th (q + 1) i (i.succ.succAbove x) : ℕ) = ((if (x : ℕ) < i + 1 then (0 : Fin 2) else 1 : Fin 2) : ℕ)
  rw [th_apply, val_succAbove]; simp only [Fin.val_succ]; split_ifs <;> first | rfl | lia

theorem sg_diag (q : ℕ) (i : Fin (q + 2)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom = OrderHom.id := by
  ext x; change (sg (q + 1) i (i.castSucc.succAbove x) : ℕ) = x
  rw [val_sg, val_succAbove]; simp only [Fin.val_castSucc]; split_ifs <;> lia

theorem sg_next (q : ℕ) (i : Fin (q + 2)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom = OrderHom.id := by
  ext x; change (sg (q + 1) i (i.succ.succAbove x) : ℕ) = x
  rw [val_sg, val_succAbove]; simp only [Fin.val_succ]; split_ifs <;> lia

theorem stepMap_zero (q : ℕ) : stepMap q 0 = cst (q + 1) 1 := by ext x; simp [stepMap, cst]; rfl

theorem stepMap_top (q : ℕ) : stepMap q (q + 2) = cst (q + 1) 0 := by
  ext x; have := x.2; simp [stepMap, cst]; rfl

theorem th_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom =
      th q (Fin.predAbove k i) := by
  ext x
  have e : ((th (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) x =
      th (q + 1) i ((i.castSucc.succAbove (i.succAbove k)).succAbove x) := rfl
  rw [e, th_apply, th_apply]; congr 2; simp only [val_succAbove, val_predAbove, Fin.val_castSucc, eq_iff_iff]
  split_ifs <;> lia

theorem sg_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom =
      (Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i)) := by
  ext x
  change (sg (q + 1) i ((i.castSucc.succAbove (i.succAbove k)).succAbove x) : ℕ) =
    ((i.succAbove k).succAbove (sg q (Fin.predAbove k i) x) : ℕ)
  simp only [val_sg, val_succAbove, val_predAbove, Fin.val_castSucc]
  split_ifs <;> lia

theorem sign_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc.succAbove (i.succAbove k) : Fin (q + 3)) : ℕ))) =
      -((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) + ((i.succAbove k : Fin (q + 2)) : ℕ))) := by
  simp only [val_succAbove, val_predAbove, Fin.val_castSucc]
  by_cases h : (k : ℕ) < i
  · obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨(i : ℕ) - 1, by lia⟩
    rw [ite_eq_left h, ite_eq_left h, ite_eq_left (by lia), hm]; simp [pow_add, pow_succ]
  · rw [ite_eq_right h, ite_eq_right (by lia), ite_eq_right (by lia)]; simp [pow_add, pow_succ]

def fwd (q : ℕ) (p : Fin (q + 2) × Fin (q + 1)) : Fin (q + 1) × Fin (q + 2) :=
  (Fin.predAbove p.2 p.1, p.1.succAbove p.2)

def bwd (q : ℕ) (p : Fin (q + 1) × Fin (q + 2)) : Fin (q + 2) × Fin (q + 1) :=
  (⟨if (p.2 : ℕ) ≤ p.1 then (p.1 : ℕ) + 1 else p.1, by have := p.1.2; split_ifs <;> lia⟩,
   ⟨if (p.2 : ℕ) ≤ p.1 then p.2 else (p.2 : ℕ) - 1, by have := p.1.2; have := p.2.2; split_ifs <;> lia⟩)

theorem bwd_fwd (q : ℕ) (p : Fin (q + 2) × Fin (q + 1)) : bwd q (fwd q p) = p := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> · simp only [bwd, fwd, val_succAbove, val_predAbove]; split_ifs <;> lia

theorem fwd_bwd (q : ℕ) (p : Fin (q + 1) × Fin (q + 2)) : fwd q (bwd q p) = p := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> · simp only [bwd, fwd, val_succAbove, val_predAbove]; split_ifs <;> lia

theorem prism_faces {A : Type} [AddCommGroup A] (q : ℕ)
    (B : (Fin (q + 2) →o Fin 2) → (Fin (q + 2) →o Fin (q + 2)) → A) :
    ∑ i : Fin (q + 2), ∑ j : Fin (q + 3), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
        B ((th (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom)
          ((sg (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) =
      B (cst (q + 1) 1) OrderHom.id - B (cst (q + 1) 0) OrderHom.id -
        ∑ j : Fin (q + 2), ∑ i : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
          B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i)) := by
  have h1 : ∀ i : Fin (q + 2), ∑ j : Fin (q + 3), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
        B ((th (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom)
          ((sg (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) =
      (B (stepMap q i) OrderHom.id - B (stepMap q (i + 1)) OrderHom.id) -
        ∑ k : Fin (q + 1), ((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) +
            ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) := fun i ↦ by
    rw [Fin.sum_univ_succAbove _ i.castSucc, Fin.sum_univ_succAbove _ i,
      Fin.succAbove_castSucc_self, th_diag, sg_diag, th_next, sg_next]
    have e1 : ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc : Fin (q + 3)) : ℕ))) = 1 := by simp [← two_mul]
    have e2 : ((-1 : ℤ) ^ ((i : ℕ) + ((i.succ : Fin (q + 3)) : ℕ))) = -1 := by simp [← add_assoc, ← two_mul, pow_succ]
    have e3 : ∀ k : Fin (q + 1),
        ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc.succAbove (i.succAbove k) : Fin (q + 3)) : ℕ))) •
          B ((th (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom)
            ((sg (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) =
        -(((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) + ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i)))) := fun k ↦ by
      rw [th_off, sg_off, sign_off, neg_smul]
    rw [e1, e2, one_smul, neg_smul, one_smul]; simp only [e3, Finset.sum_neg_distrib]; abel
  have h2 : ∑ i : Fin (q + 2), (B (stepMap q i) OrderHom.id - B (stepMap q (i + 1)) OrderHom.id) =
      B (cst (q + 1) 1) OrderHom.id - B (cst (q + 1) 0) OrderHom.id := by
    rw [Fin.sum_univ_eq_sum_range (fun n ↦ B (stepMap q n) OrderHom.id - B (stepMap q (n + 1)) OrderHom.id),
      Finset.sum_range_sub', stepMap_zero, stepMap_top]
  have h3 : ∑ i : Fin (q + 2), ∑ k : Fin (q + 1),
        ((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) + ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) =
      ∑ j : Fin (q + 2), ∑ i : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
          B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i)) := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (q + 2)))) (t := (Finset.univ : Finset (Fin (q + 1))))
        (f := fun j i ↦ ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i))),
      ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    exact Finset.sum_nbij' (fwd q) (bwd q) (fun _ _ ↦ Finset.mem_univ _) (fun _ _ ↦ Finset.mem_univ _)
      (fun p _ ↦ bwd_fwd q p) (fun p _ ↦ fwd_bwd q p) (fun _ _ ↦ rfl)
  simp only [h1, Finset.sum_sub_distrib] at h2 ⊢; rw [h2, h3]

end GlobalTheory.CompanionTheory.HopfLe.PrismComb
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValSuccAbove =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1BoundaryOfBoundary =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1BoundaryOfBoundary", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechNerveFaceOneZero\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackZeroCochainsAlgebraMap\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.IsPullbackH2Structure\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup0\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup1\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualFunctionalsOfLinearIndependent\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFactorOfExactIsField\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlantProductSecondAction\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValSuccAbove\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx

namespace GlobalTheory.CompanionTheory.HopfLe

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

section Prism

variable (F : C ⥤ CommAlgCat.{0} R)

theorem neg_one_pow_smul_int {A : Type} [AddCommGroup A] [Module R A] (k : ℕ) (a : A) :
    ((-1 : R) ^ k) • a = ((-1 : ℤ) ^ k) • a := by
  rcases Nat.even_or_odd k with h | h <;> simp [h.neg_one_pow]

theorem S_dn (q : ℕ) (w : Cn (box F) (q + 1)) :
    S F (q + 1) (dn (box F) (q + 1) w) =
      a1 F (cst 0 (1 : Fin 2)) (S0 F (q + 1) w) - a1 F (cst 0 (0 : Fin 2)) (S0 F (q + 1) w) -
        ∑ j : Fin (q + 2), ((-1 : R) ^ (j : ℕ)) • a2 F (Fin.succAboveOrderEmb j).toOrderHom (S F q w) := by
  have e1 : S F (q + 1) (dn (box F) (q + 1) w) = ∑ i : Fin (q + 2), ∑ j : Fin (q + 3),
      ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • bi F ((th (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom)
        ((sg (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) w := by
    rw [S_apply]; simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply, cof_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [LinearMap.map_smul, bi_act, smul_smul, ← pow_add, neg_one_pow_smul_int (R := R)]
  have e2 : ∑ j : Fin (q + 2), ((-1 : R) ^ (j : ℕ)) • a2 F (Fin.succAboveOrderEmb j).toOrderHom (S F q w) =
      ∑ j : Fin (q + 2), ∑ i : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
        bi F (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i)) w :=
    Finset.sum_congr rfl fun j _ ↦ by
      rw [S_apply, map_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [LinearMap.map_smul, bisimplicial_action_second_factor, smul_smul, ← pow_add, neg_one_pow_smul_int (R := R), Nat.add_comm (j : ℕ) (i : ℕ)]
  have e3 : a1 F (cst 0 (1 : Fin 2)) (S0 F (q + 1) w) = bi F (cst (q + 1) 1) OrderHom.id w := bisimplicial_action_first_factor F _ _ _ w
  have e4 : a1 F (cst 0 (0 : Fin 2)) (S0 F (q + 1) w) = bi F (cst (q + 1) 0) OrderHom.id w := bisimplicial_action_first_factor F _ _ _ w
  rw [e1, e2, e3, e4]
  exact PrismComb.prism_faces q (fun θ ψ ↦ bi F θ ψ w)

theorem T_dn [Fintype (Fin 1 ⥤ C)] [Fintype (Fin 2 ⥤ C)] (q : ℕ) (ρ : Cn F 1 →ₗ[R] R) (w : Cn (box F) (q + 1)) :
    T F (q + 1) ρ (dn (box F) (q + 1) w) = U F (q + 1) (ρ ∘ₗ dn F 0) w - dn F q (T F q ρ w) := by
  have c0 : (Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom = cst 0 (1 : Fin 2) := by ext j; fin_cases j; simp [cst_apply]
  have c1 : (Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom = cst 0 (0 : Fin 2) := by ext j; fin_cases j; simp [cst_apply]
  have e : ρ ∘ₗ dn F 0 = ρ ∘ₗ act F (cst 0 (1 : Fin 2)) - ρ ∘ₗ act F (cst 0 (0 : Fin 2)) := by
    rw [show dn F 0 = act F (cst 0 (1 : Fin 2)) - act F (cst 0 (0 : Fin 2)) by
      rw [← (cof_eq F 0 0).trans (congrArg (act F) c0), ← (cof_eq F 0 1).trans (congrArg (act F) c1)]
      exact LinearMap.ext fun f ↦ funext fun c ↦ GlobalTheory.CompanionTheory.Dict.dn0 F f c, LinearMap.comp_sub]
  change sl F (q + 1) ρ (S F (q + 1) _) = sl F (q + 1) (ρ ∘ₗ dn F 0) (S0 F (q + 1) w) - dn F q (sl F q ρ (S F q w))
  rw [S_dn, e, map_sub, map_sub, map_sum, slant_product_first_action, slant_product_first_action, sl_sub]
  congr 1; simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, slant_product_second_action, cof_eq]

end Prism

section Core

variable (F : C ⥤ CommAlgCat.{0} R)

def IsB {n : ℕ} : Cn F n → Prop :=
  match n with
  | 0 => fun z ↦ z = 0
  | k + 1 => fun z ↦ ∃ y, z = dn F k y

theorem cup1_boundary_of_boundary {n : ℕ} (x : Cn F 1) (hx : dn F 1 x = 0) (z : Cn F n) (h : IsB F z) :
    ∃ y, cup1 F x z = dn F n y := by
  cases n with
  | zero => exact ⟨0, by rw [show z = 0 from h, cup1_zero, map_zero]⟩
  | succ k => obtain ⟨y, rfl⟩ := h; exact ⟨- cup1 F x y, by rw [map_neg, DnCup.coboundary_cup1 F x y hx, neg_neg]⟩

theorem T_cup_L' [Fintype (Fin 1 ⥤ C)] [Fintype (Fin 2 ⥤ C)] (hR : IsField R)
    (hS : Function.Exact (Algebra.linearMap R (Cn F 0)) (dn F 0)) (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (q : ℕ)
    (Λ : Cn F 1 →ₗ[R] R) (x : Cn F 1) (hx : dn F 1 x = 0) (w : Cn (box F) (q + 1))
    (hw : dn (box F) (q + 1) w = 0) :
    ∃ y, T F (q + 1) Λ (cup1 (box F) (pulln (boxL F) 1 x) w) =
      Λ x • pulln (boxE F T₀ ε) (q + 1) w + dn F q y := by
  obtain ⟨ρ, hρ⟩ := exists_rho_of_exact F hR hS (nu F Λ x) (evz F T₀ ε) (map_one ε)
  have hA := T_dn F q ρ w
  rw [hw, map_zero] at hA
  exact ⟨T F q ρ w, by rw [T_cup_L F q Λ x hx w, hρ, U_add, U_smul, U_evz, nu_one, sub_eq_zero.1 hA.symm]⟩

variable {F}
variable {D : Type} [Category.{0} D] {G : D ⥤ CommAlgCat.{0} R}

theorem core_step [Fintype (Fin 1 ⥤ C)] [Fintype (Fin 2 ⥤ C)] (hR : IsField R)
    (hS : Function.Exact (Algebra.linearMap R (Cn F 0)) (dn F 0))
    (π : CoefMap (RingHom.id R) (box F) G) (m : CoefMap (RingHom.id R) F G) (hπ : AllQIso π)
    (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (g : ℕ) (x : Fin (g + 1) → Cn F 1) (hx : ∀ i, dn F 1 (x i) = 0)
    (hprim : ∀ i, ∃ u, pulln π 1 (pulln (boxL F) 1 (x i) + pulln (boxR F) 1 (x i)) - pulln m 1 (x i) = dn G 0 u)
    (Λ : Fin (g + 1) → Cn F 1 →ₗ[R] R) (hΛ : ∀ i, Λ i ∘ₗ dn F 0 = 0) (hΛ1 : ∀ i, Λ i (x i) = 1)
    (hΛ0 : ∀ i j, i ≠ j → Λ i (x j) = 0) (s : ℕ) (hs : s ≤ g) :
    ∃ (z : Cn F (s + 1)) (w : Cn (box F) (s + 1)), dn F (s + 1) z = 0 ∧ dn (box F) (s + 1) w = 0 ∧
      (∃ v, pulln π (s + 1) w - pulln m (s + 1) z = dn G s v) ∧ pulln (boxE F T₀ ε) (s + 1) w = z ∧
      (∀ i : Fin (g + 1), (i : ℕ) + s < g → IsB F (T F s (Λ i) w)) ∧
      ((∃ y, z = dn F s y) → ∃ y, x (Fin.last g) = dn F 0 y) := by
  have cmπ : ∀ n u, pulln π (n + 1) (dn (box F) n u) = dn G n (pulln π n u) := fun n u ↦ LinearMap.congr_fun (pulln_dn π n) u
  have cmm : ∀ n u, pulln m (n + 1) (dn F n u) = dn G n (pulln m n u) := fun n u ↦ LinearMap.congr_fun (pulln_dn m n) u
  have cmL : ∀ y : Cn F 1, dn F 1 y = 0 → dn (box F) 1 (pulln (boxL F) 1 y) = 0 := fun y hy ↦ by
    simpa [hy] using (LinearMap.congr_fun (pulln_dn (boxL F) 1) y).symm
  have cmR : ∀ y : Cn F 1, dn F 1 y = 0 → dn (box F) 1 (pulln (boxR F) 1 y) = 0 := fun y hy ↦ by
    simpa [hy] using (LinearMap.congr_fun (pulln_dn (boxR F) 1) y).symm
  induction s with
  | zero =>
    obtain ⟨u, hu⟩ := hprim (Fin.last g)
    refine ⟨x (Fin.last g), pulln (boxL F) 1 (x (Fin.last g)) + pulln (boxR F) 1 (x (Fin.last g)), hx _,
      by rw [map_add (f := _), cmL _ (hx _), cmR _ (hx _), add_zero], ⟨u, hu⟩,
      by rw [map_add (f := _), tau_L F T₀ ε _ (hx _), tau_R F T₀ ε 1]; exact zero_add _, fun i hi ↦ ?_, id⟩
    have hne : i ≠ Fin.last g := fun e ↦ by simp [e] at hi
    change T F 0 (Λ i) _ = 0
    rw [T_base F _ _ (hx _), hΛ0 i _ hne, zero_smul]
  | succ s ih =>
    obtain ⟨z, w, hz, hw, ⟨v, hv⟩, hτ, hB, hI⟩ := ih (by lia)
    let j : Fin (g + 1) := ⟨g - s - 1, by lia⟩
    set xj := x j; set pj := pulln (boxL F) 1 xj; set qj := pulln (boxR F) 1 xj
    have hpq : dn (box F) 1 (pj + qj) = 0 := by rw [map_add (f := _), cmL _ (hx j), cmR _ (hx j), add_zero]
    have hT : ∀ i : Fin (g + 1), ∃ y, T F (s + 1) (Λ i) (cup1 (box F) (pj + qj) w) =
        Λ i xj • z + dn F s y - cup1 F xj (T F s (Λ i) w) := fun i ↦ by
      obtain ⟨y, hy⟩ := T_cup_L' F hR hS T₀ ε s (Λ i) xj (hx j) w hw
      exact ⟨y, by rw [cup1_add_left, map_add (f := _), hy, T_cup_R F s (Λ i) xj (hx j) w, hτ]; abel⟩
    have hw' : dn (box F) (s + 2) (cup1 (box F) (pj + qj) w) = 0 := by
      rw [DnCup.coboundary_cup1 _ _ _ hpq, hw, cup1_zero, neg_zero]
    have hW : ∃ v', pulln π (s + 2) (cup1 (box F) (pj + qj) w) - pulln m (s + 2) (cup1 F xj z) = dn G (s + 1) v' := by
      obtain ⟨u, hu⟩ := hprim j
      have e1 : pulln π 1 (pj + qj) = pulln m 1 xj + dn G 0 u := by rw [← hu]; abel
      have e2 : pulln π (s + 1) w = pulln m (s + 1) z + dn G s v := by rw [← hv]; abel
      have hmx : dn G 1 (pulln m 1 xj) = 0 := by rw [← cmm, hx j, map_zero]
      have hcup : cup1 G (dn G 0 u) (pulln π (s + 1) w) = dn G (s + 1) (cup0 G u (pulln π (s + 1) w)) := by
        rw [coboundary_cup0, show dn G (s + 1) (pulln π (s + 1) w) = 0 by rw [← cmπ, hw, map_zero]]; simp [cup0]
      refine ⟨- cup1 G (pulln m 1 xj) v + cup0 G u (pulln π (s + 1) w), ?_⟩
      rw [pullback_cup1, pullback_cup1, e1, cup1_add_left, hcup, e2, cup1_add_right, map_add (f := _), map_neg,
        DnCup.coboundary_cup1 G _ _ hmx, ← e2]; abel
    refine ⟨cup1 F xj z, cup1 (box F) (pj + qj) w,
      by rw [DnCup.coboundary_cup1 F _ _ (hx j), hz, cup1_zero, neg_zero], hw', hW,
      by rw [pullback_cup1, map_add (f := _), tau_L F T₀ ε _ (hx j), tau_R F T₀ ε 1, zero_add, hτ],
      fun i hi ↦ ?_, fun ⟨t, ht⟩ ↦ ?_⟩
    · have hij : i ≠ j := fun e ↦ by have := congrArg Fin.val e; dsimp [j] at this; lia
      obtain ⟨y, hy⟩ := hT i
      obtain ⟨y', hy'⟩ := cup1_boundary_of_boundary F xj (hx j) _ (hB i (by lia))
      exact ⟨y - y', by rw [hy, hΛ0 i j hij, zero_smul, hy', map_sub, zero_add]⟩
    · obtain ⟨v', hv'⟩ := hW
      obtain ⟨r, hr⟩ := (hπ.2 (s + 1)).1 _ hw' ⟨pulln m (s + 1) t + v', by rw [map_add (f := _), ← cmm, ← ht, ← hv']; abel⟩
      obtain ⟨y, hy⟩ := hT j
      obtain ⟨y', hy'⟩ := cup1_boundary_of_boundary F xj (hx j) _ (hB j (by dsimp [j]; lia))
      have hA := T_dn F s (Λ j) r
      rw [hr, hy, hΛ j, U_zero, hΛ1, one_smul, hy', zero_sub] at hA
      refine hI ⟨y' - y - T F s (Λ j) r, ?_⟩
      rw [map_sub, map_sub]; linear_combination (exp := 1) hA

end Core

section Top

theorem chains_finite (P : Type) [PartialOrder P] [Finite P] (n : ℕ) : Finite (Fin (n + 1) ⥤ Pᵒᵖ) :=
  have : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  Finite.of_injective (fun c i ↦ c.obj i) fun _ _ h ↦
    CategoryTheory.Functor.ext (congrFun h) fun _ _ _ ↦ Subsingleton.elim _ _

theorem exists_extend_of_isField (hR : IsField R) {V : Type} [AddCommGroup V] [Module R V] (p : Submodule R V)
    (f : p →ₗ[R] R) : ∃ g : V →ₗ[R] R, g ∘ₗ p.subtype = f := by
  let := hR.toField
  exact LinearMap.exists_extend f

variable {D : Type} [Category.{0} D] {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem L1_pullback_naturality (m : CoefMap (RingHom.id R) F G) (f : Cn F 1) :
    GlobalTheory.CompanionTheory.Dict.L1 G (pulln m 1 f) = GlobalTheory.CompanionTheory.HodgeLow.pullbackOneCochains m (GlobalTheory.CompanionTheory.Dict.L1 F f) := by
  funext T T' φ
  change m.α T' (f (ComposableArrows.mk₁ φ ⋙ m.G)) = m.α T' (f (ComposableArrows.mk₁ (m.G.map φ)))
  exact congrArg (m.α T') (eq_of_heq (GlobalTheory.CompanionTheory.HodgeLow.cn_heq f (GlobalTheory.CompanionTheory.HodgeLow.mk₁_comp m.G φ)))

theorem exact_of_stein (hSt : Stein F) : Function.Exact (Algebra.linearMap R (Cn F 0)) (dn F 0) := fun y ↦ by
  have hal : ∀ r : R, GlobalTheory.CompanionTheory.Dict.L0 F (algebraMap R (Cn F 0) r) = algebraMap R (C0 F) r := fun _ ↦ rfl
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨r, hr⟩ := (hSt.1 _).1 (by rw [← GlobalTheory.CompanionTheory.Dict.L1_dn_zero_eq_d0_L0, h, map_zero])
    exact ⟨r, (GlobalTheory.CompanionTheory.Dict.L0_bijective_cochain F).1 ((hal r).trans hr)⟩
  · rintro ⟨r, rfl⟩
    refine (GlobalTheory.CompanionTheory.Dict.L1_bijective_cochain F).1 ?_
    rw [map_zero, GlobalTheory.CompanionTheory.Dict.L1_dn_zero_eq_d0_L0]
    exact (hSt.1 _).2 ⟨r, (hal r).symm⟩

end Top

theorem hopfLeSt : CxSt → DictSt → LowSt → HopfLeSt := by
  intro _ _ _ R _ P _ _ F g hR hSt hvan hH x hx
  obtain ⟨D, _, G, π, m, hπ, hprim, hb⟩ := hH
  obtain ⟨T₀, ε, -⟩ := hb trivial
  have : Nontrivial R := ⟨hR.exists_pair_ne⟩
  let : Fintype (Fin 1 ⥤ Pᵒᵖ) := @Fintype.ofFinite _ (chains_finite P 0)
  let : Fintype (Fin 2 ⥤ Pᵒᵖ) := @Fintype.ofFinite _ (chains_finite P 1)
  choose f hf using fun i ↦ H1.mk_surjective F (x i)
  choose xt hxt using fun i ↦ (GlobalTheory.CompanionTheory.Dict.L1_bijective_cochain F).2 (f i).1
  have hxc : ∀ i, dn F 1 (xt i) = 0 := fun i ↦ (GlobalTheory.CompanionTheory.Dict.L2_bijective_cochain F).1 (by
    rw [GlobalTheory.CompanionTheory.Dict.L2_dn_one_eq_d1_L1, hxt, map_zero]
    exact LinearMap.mem_ker.1 (commAlgFunctorCocyclesOne_eq_ker F ▸ (f i).2))
  obtain ⟨l, hl⟩ := exists_dual_functionals_of_linearIndependent hR x hx
  let Φ : LinearMap.ker (dn F 1) →ₗ[R] H1 F :=
    H1.mk F ∘ₗ ((GlobalTheory.CompanionTheory.Dict.L1 F) ∘ₗ (LinearMap.ker (dn F 1)).subtype).codRestrict (Z1 F) fun t ↦ by
      rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]
      change d1 F (GlobalTheory.CompanionTheory.Dict.L1 F t.1) = 0
      rw [← GlobalTheory.CompanionTheory.Dict.L2_dn_one_eq_d1_L1, LinearMap.mem_ker.1 t.2, map_zero]
  choose Λ hΛ using fun i ↦ exists_extend_of_isField hR (LinearMap.ker (dn F 1)) (l i ∘ₗ Φ)
  have hΛv : ∀ i (t : Cn F 1) (ht : dn F 1 t = 0), Λ i t = l i (Φ ⟨t, ht⟩) := fun i t ht ↦ LinearMap.congr_fun (hΛ i) ⟨t, ht⟩
  have hΦx : ∀ j, Φ ⟨xt j, hxc j⟩ = x j := fun j ↦ by rw [← hf j]; exact congrArg (H1.mk F) (Subtype.ext (hxt j))
  have hdd : ∀ y : Cn F 0, dn F 1 (dn F 0 y) = 0 := fun y ↦ LinearMap.congr_fun (dn_comp_dn F 0) y
  have hΦd : ∀ y : Cn F 0, Φ ⟨dn F 0 y, hdd y⟩ = 0 := fun y ↦
    H1.mk_eq_zero.2 ⟨GlobalTheory.CompanionTheory.Dict.L0 F y, (GlobalTheory.CompanionTheory.Dict.L1_dn_zero_eq_d0_L0 F y).symm⟩
  have hpr : ∀ i, ∃ u, pulln π 1 (pulln (boxL F) 1 (xt i) + pulln (boxR F) 1 (xt i)) - pulln m 1 (xt i) = dn G 0 u := fun i ↦ by
    have h := hprim (x i)
    rw [← hf i, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class,
      ← map_add (f := _), CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at h
    obtain ⟨a, ha⟩ := h
    obtain ⟨u, rfl⟩ := (GlobalTheory.CompanionTheory.Dict.L0_bijective_cochain G).2 a
    refine ⟨-u, (GlobalTheory.CompanionTheory.Dict.L1_bijective_cochain G).1 ?_⟩
    rw [map_neg, map_neg, GlobalTheory.CompanionTheory.Dict.L1_dn_zero_eq_d0_L0, ha, map_sub, L1_pullback_naturality,
      map_add (f := _), L1_pullback_naturality, L1_pullback_naturality, L1_pullback_naturality, hxt, neg_sub]; rfl
  obtain ⟨z, w, hz, -, -, -, -, hI⟩ := core_step hR (exact_of_stein hSt) π m hπ T₀ ε g xt hxc hpr Λ
    (fun i ↦ LinearMap.ext fun y ↦ by rw [LinearMap.comp_apply, hΛv i _ (hdd y), hΦd, map_zero]; rfl)
    (fun i ↦ by rw [hΛv i _ (hxc i), hΦx, hl, ite_eq_left rfl])
    (fun i j h ↦ by rw [hΛv i _ (hxc j), hΦx, hl, ite_eq_right h]) g le_rfl
  obtain ⟨y, hy⟩ := hI (by obtain ⟨y, hy⟩ := (hvan g le_rfl z).1 hz; exact ⟨y, hy.symm⟩)
  refine hx.ne_zero (Fin.last g) ?_
  rw [← hf]
  exact H1.mk_eq_zero.2 ⟨GlobalTheory.CompanionTheory.Dict.L0 F y, by rw [← GlobalTheory.CompanionTheory.Dict.L1_dn_zero_eq_d0_L0, ← hy, hxt]⟩

end GlobalTheory.CompanionTheory.HopfLe
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1BoundaryOfBoundary =====
