module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.SymplecticOrthogonalSesquilinear

theorem trace_one_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem eq_zero_of_eq_neg {F R : Type} [Field F] [CharZero F] [CommRing R] [Algebra F R] {a : R} (h : a = -a) :
    a = 0 := by
  have h2 : (2 : F) • a = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.1 h
  exact (smul_eq_zero_iff_right two_ne_zero).1 h2

theorem map_sesq {E A : Type} [CommRing E] [CommRing A] (ι : E →+* A) (c : A →+* A) (s : E → E)
    (hc : ∀ e, c (ι e) = ι (s e)) {m n : ℕ} (ξ : E) (P : Fin m → Fin m → E) (Q : Fin n → Fin n → E)
    (x y : Fin n → Fin m → E) :
    ι ξ * ∑ a, ∑ b, ∑ c', ∑ d, ι (P a b) * c (ι (y c' b)) * ι (Q c' d) * ι (x d a) =
      ι (ξ * ∑ a, ∑ b, ∑ c', ∑ d, P a b * s (y c' b) * Q c' d * x d a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc]

theorem symplO_rat (D : D7) (S T : HSp D) (γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have h : ∃ e : D.host.E, incA D D.host.xi0 * hO S T (ratW T S γ) (ratW T S γ') = incA D e :=
    ⟨_, map_sesq (incA D) (cA D) star GlobalTheory.DualPairCheck.cA_incA D.host.xi0 (fun a b => S.gram⁻¹ a b)
      (fun a b => T.gram a b) γ γ'⟩
  obtain ⟨e, he⟩ := h
  refine ⟨Algebra.trace D.host.F D.host.E e, ?_⟩
  unfold symplO
  rw [he]
  exact trace_one_tmul _ e

theorem symplO_alt : ∀ (D : D7) (S T : HSp D), (∀ x x' y : WO S T, symplO S T (x + x') y = symplO S T x y + symplO S T x' y) ∧ (∀ x y y' : WO S T, symplO S T x (y + y') = symplO S T x y + symplO S T x y') ∧ (∀ x y : WO S T, symplO S T x y = -symplO S T y x) ∧ (∀ x : WO S T, symplO S T x x = 0) ∧ ∀ γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  intro D S T
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun x y => GlobalTheory.WeilVacMove.symplO_skew S T y x,
    fun x => eq_zero_of_eq_neg (F := D.host.F) (GlobalTheory.WeilVacMove.symplO_skew S T x x), symplO_rat D S T⟩
  · unfold symplO hO
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
  · unfold symplO hO
    simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

end GlobalTheory.SymplecticOrthogonalSesquilinear
