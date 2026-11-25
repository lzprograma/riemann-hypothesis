module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem compound_mul {n : ℕ} (l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ) :
    BranchingSupport.cmp l (g * h) = BranchingSupport.cmp l g * BranchingSupport.cmp l h := by
  ext I J
  have e : (g * h).submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2)
      = g.submatrix (I.1.orderEmbOfFin I.2) id * h.submatrix id (J.1.orderEmbOfFin J.2) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [Matrix.mul_apply]
  unfold BranchingSupport.cmp
  rw [e, Formalism.HermitianLatticeCounting.P.ge_cauchyBinet]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [mul_comm]
  rfl

theorem compound_conjTranspose {n : ℕ} (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) :
    BranchingSupport.cmp l gᴴ = (BranchingSupport.cmp l g)ᴴ := by
  ext I J
  rw [Matrix.conjTranspose_apply]
  unfold BranchingSupport.cmp
  rw [← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]

theorem compound_one (n l : ℕ) : BranchingSupport.cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext I J
  unfold BranchingSupport.cmp
  by_cases hIJ : I = J
  · subst hIJ
    rw [Matrix.submatrix_one _ (I.1.orderEmbOfFin I.2).injective, Matrix.det_one, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hIJ]
    have hne : ¬ I.1 ⊆ J.1 := fun hs =>
      hIJ (Subtype.ext (Finset.eq_of_subset_of_card_le hs (by rw [I.2, J.2])))
    obtain ⟨x, hxI, hxJ⟩ := Finset.not_subset.mp hne
    have hx : x ∈ Set.range (I.1.orderEmbOfFin I.2) := by
      rw [Finset.range_orderEmbOfFin]; exact hxI
    obtain ⟨a, ha⟩ := hx
    refine Matrix.det_eq_zero_of_row_eq_zero a fun b => ?_
    rw [Matrix.submatrix_apply, Matrix.one_apply_ne]
    intro hab
    apply hxJ
    rw [← ha, hab]
    exact Finset.orderEmbOfFin_mem _ _ _

theorem compound_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) := by
  apply _root_.GlobalTheory.TensLen.cmp_mulVec_wedge <;> assumption

theorem compound_properties : ∀ (n l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ),
    BranchingSupport.cmp l (g * h) = BranchingSupport.cmp l g * BranchingSupport.cmp l h ∧ BranchingSupport.cmp l gᴴ = (BranchingSupport.cmp l g)ᴴ ∧
      BranchingSupport.cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 ∧
      ∀ f : Fin l → Fin n → ℂ, BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) :=
  fun n l g h => ⟨compound_mul l g h, compound_conjTranspose l g, compound_one n l, compound_mulVec_wedge g⟩

end GlobalTheory
