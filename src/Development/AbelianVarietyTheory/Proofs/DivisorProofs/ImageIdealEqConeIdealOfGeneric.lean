module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt
open AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G GlobalTheory.Twist GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem form_eq_zero_of_generic {K : Type} [Field K] (S : LinSys K) [IsReduced S.Y] {η : S.Y}
    (hη : IsGenericPoint η Set.univ) {d : ℕ} {g : MvPolynomial (Fin S.N) K} (hg : g.IsHomogeneous d)
    (h : η ∉ nonzeroLocus (S.form hg)) : S.form hg = 0 := by
  refine zglobal_ext fun i => ?_
  rw [zfun_zero, ← basicOpen_eq_bot_iff, basicOpen_zfun, eq_bot_iff]
  intro y hy
  exact (h ((hη.mem_open_set_iff (nonzeroLocus (S.form hg)).isOpen).2 ⟨y, trivial, hy.2⟩)).elim


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem imageIdeal_eq_coneIdeal_of_generic (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (S : LinSys K)
    [IsIntegral S.Y] (x : S.Pt Ω) (hx : IsGenericPoint (ptOf x.1) Set.univ) (a : Ω) (y : Fin S.N → Ω) (ha : a ≠ 0)
    (h : S.coords x.1 = a • y) : S.imageIdeal = coneIdeal K y := by
  rw [← coneIdeal_smul ha y, ← h]
  have key : ∀ {d : ℕ} {g : MvPolynomial (Fin S.N) K} (_ : g.IsHomogeneous d),
      g ∈ S.imageIdeal ↔ g ∈ coneIdeal K (S.coords x.1) := fun {d g} hg => by
    rw [mem_coneIdeal_of_isHomogeneous _ hg, aeval_def,
      ← congrArg (fun φ => eval₂ φ (S.coords x.1) g) (LinSys.baseHom_ptOver x)]
    refine ⟨S.eval₂_coords_eq_zero x.1, fun h0 => (S.mem_imageIdeal_iff hg).2
      (form_eq_zero_of_generic S hx hg fun hm => ?_)⟩
    exact (S.powVal_ne_zero_iff x.1 _).2 hm ((S.powVal_form x.1 hg).trans h0)
  ext g
  rw [S.isHomogeneous_imageIdeal.mem_iff, (isHomogeneous_coneIdeal (K := K) (S.coords x.1)).mem_iff]
  exact forall_congr' fun d => key (DirectSum.decompose (homogeneousSubmodule (Fin S.N) K) g d).2

end GlobalTheory.CompHt
