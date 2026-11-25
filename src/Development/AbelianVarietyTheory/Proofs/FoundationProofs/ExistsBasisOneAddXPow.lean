module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Foundations.FrobLiftWittClosure
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

open PowerSeries in
private theorem one_add_X_pow_eq_sum_fin_choose {R : Type} [CommRing R] (p j : ℕ) (hj : j < p) :
    (1 + X : R⟦X⟧) ^ j = ∑ i : Fin p, ((j.choose i : ℕ) : R⟦X⟧) * X ^ (i : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((j.choose i : ℕ) : R⟦X⟧) * X ^ i) p, add_comm, add_pow]
  have hsub : Finset.range (j + 1) ⊆ Finset.range p := Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub (fun i _ hi => by
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, mul_comm]

open PowerSeries in
private theorem subsingleton_of_isUnit_natCast_of_isAdicComplete {R : Type} [CommRing R] (p : ℕ)
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (hu : IsUnit (p : R)) : Subsingleton R := by
  have htop : Ideal.span {(p : R)} = ⊤ := Ideal.span_singleton_eq_top.2 hu
  exact IsHausdorff.subsingleton (htop ▸ hR.toIsHausdorff)


open PowerSeries in
theorem _root_.GlobalTheory.Col.exists_basis_one_add_X_pow (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) :
    ∃ b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      (@Algebra.toModule _ _ _ _ (_root_.GlobalTheory.Col.phi (R := R) p hp.out.pos).toRingHom.toAlgebra), ∀ i, b i = (1 + X) ^ (i : ℕ) := by
  by_cases hn : (p : R) ∈ nonunits R
  · haveI := hR
    set e := _root_.GlobalTheory.Col.Model.basis (R := R) p hn
    have he : ∀ i, e i = _root_.GlobalTheory.Col.Model.toUp p (X ^ (i : ℕ)) := fun i => by
      show (_root_.GlobalTheory.Col.Model.basis (R := R) p hn) i = _
      unfold _root_.GlobalTheory.Col.Model.basis
      rw [Module.Basis.mk_apply]
      rfl
    let v : Fin p → _root_.GlobalTheory.Col.Model.Up R p :=
      fun j => _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (j : ℕ))
    have hv : ∀ j : Fin p, v j = ∑ i : Fin p, (((j : ℕ).choose i : ℕ) : R⟦X⟧) • e i := by
      intro j
      simp only [he, Algebra.smul_def, map_natCast]
      exact one_add_X_pow_eq_sum_fin_choose p j j.2
    have hrepr : ∀ j i : Fin p, e.repr (v j) i = (((j : ℕ).choose i : ℕ) : R⟦X⟧) := by
      intro j i
      rw [hv, e.repr_sum_self]
    have hdet : e.det v = 1 := by
      rw [Module.Basis.det_apply, Matrix.det_of_upperTriangular]
      · simp [Module.Basis.toMatrix_apply, hrepr]
      · intro i j hij
        simp [Module.Basis.toMatrix_apply, hrepr, Nat.choose_eq_zero_of_lt (show (j : ℕ) < i from hij)]
    obtain ⟨hli, hspan⟩ := (Module.Basis.is_basis_iff_det e).2 (by rw [hdet]; exact isUnit_one)
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) := Module.Basis.mk hli hspan.ge
    have hb : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hli hspan.ge i
    exact ⟨b, hb⟩
  · have hu : IsUnit (p : R) := by simpa [mem_nonunits_iff] using hn
    haveI := subsingleton_of_isUnit_natCast_of_isAdicComplete p hR hu
    haveI : Subsingleton R⟦X⟧ := ⟨fun a b => PowerSeries.ext fun n => Subsingleton.elim _ _⟩
    haveI : Subsingleton (_root_.GlobalTheory.Col.Model.Up R p) := ‹Subsingleton R⟦X⟧›
    haveI : Subsingleton (Fin p →₀ R⟦X⟧) := ⟨fun a b => Finsupp.ext fun i => Subsingleton.elim _ _⟩
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) :=
      Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _)
    have hb : ∀ i, b i = _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (i : ℕ)) := fun i => Subsingleton.elim _ _
    exact ⟨b, hb⟩

end GlobalTheory.Col
