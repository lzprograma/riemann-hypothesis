module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Convex.Contractible
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
public import Mathlib.Algebra.MvPolynomial.Funext
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDefs
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.BasicOpenSteps

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem eval_smul_of_isHomogeneous {ι : Type*} {φ : MvPolynomial ι ℂ} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (c : ℂ) (z : ι → ℂ) :
    eval (c • z) φ = c ^ n * eval z φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = n := by
    have h := hφ (mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem smul_mem_pts_coord {J : Type} [Fintype J] (x : J → Ω) {z : J → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) {c : ℂ} (hc : c ≠ 0) : c • z ∈ pts (coordIdeal ℤ x) := by
  refine ⟨smul_ne_zero hc hz.1, fun f hf => ?_⟩
  have hH := coordIdeal_isHomogIdeal ℤ x

  rw [← sum_homogeneousComponent f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [eval_smul_of_isHomogeneous ((homogeneousComponent_isHomogeneous d f).map _),
    hz.2 _ (hH f hf d), mul_zero]

theorem dense_eval_ne_zero {N : ℕ} {Δ : MvPolynomial (Fin N) ℂ} (hΔ : Δ ≠ 0) :
    Dense {w | eval w Δ ≠ 0} := by
  first
    | exact _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.IrreducibleBasicOpenConnected.dense_ne_zero
    | apply _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.IrreducibleBasicOpenConnected.dense_ne_zero <;> first | assumption | rfl | infer_instance

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
