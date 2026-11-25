module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

namespace GlobalTheory.ThetaLiouville

open Matrix Complex

theorem conj_form {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (w l : Fin g → ℂ) :
    l ⬝ᵥ Hm.mulVec (star w) = (starRingEnd ℂ) (w ⬝ᵥ Hm.mulVec (star l)) := by

  simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (starRingEnd ℂ) (Hm i j) = Hm j i := by
    have := hH.apply j i
    simpa using this
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  rw [h1]
  ring

theorem exists_basis_in {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (s : Set (Fin g → ℂ)) (b : Module.Basis s ℝ (Fin g → ℂ)), Finite s ∧ ∀ i, b i ∈ Λ := by
  obtain ⟨s, hs, hsp, hli⟩ := exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))
  let b := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, hΛ])
  refine ⟨s, b, ?_, ?_⟩
  · exact Module.Finite.finite_basis b
  · intro i
    rw [Module.Basis.mk_apply]
    exact hs i.2

end GlobalTheory.ThetaLiouville

namespace GlobalTheory.ThetaLiouville

open Matrix Complex

theorem im_form_mem_int (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (w : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ)
    (hθ : Differentiable ℂ θ) (hθ0 : ∀ z, θ z ≠ 0)
    (hper : ∀ l ∈ Λ, ∀ z, θ (z + l) = Complex.exp (Real.pi * (w ⬝ᵥ Hm.mulVec (star l))) * θ z) :
    ∀ l ∈ Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n := by
  set u : Fin g → ℂ := Hm.mulVec (star w) with hu
  let ψ : (Fin g → ℂ) → ℂ := fun z => θ z * Complex.exp (-(Real.pi * (z ⬝ᵥ u)))
  have hlin : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ u) := by
    have : (fun z : Fin g → ℂ => z ⬝ᵥ u) = fun z => ∑ i, z i * u i := rfl
    rw [this]
    exact Differentiable.fun_sum fun i _ => (differentiable_apply i).mul_const _
  have hψ : Differentiable ℂ ψ :=
    hθ.mul ((hlin.const_mul _).neg.cexp)

  have hshift : ∀ l ∈ Λ, ∀ z, ψ (z + l) = ψ z *
      Complex.exp (Real.pi * (((2 * (w ⬝ᵥ Hm.mulVec (star l)).im : ℝ) : ℂ) * I)) := by
    intro l hl z
    have hc := conj_form Hm hH w l
    simp only [ψ, hper l hl z, add_dotProduct]
    rw [hc]
    set a := w ⬝ᵥ Hm.mulVec (star l)
    have hsub : a - (starRingEnd ℂ) a = ((2 * a.im : ℝ) : ℂ) * I := by
      rw [Complex.sub_conj]
    rw [← hsub]
    rw [show -(↑Real.pi * (z ⬝ᵥ u + (starRingEnd ℂ) a)) =
        -(↑Real.pi * (z ⬝ᵥ u)) + (-(↑Real.pi * (starRingEnd ℂ) a)) by ring,
      Complex.exp_add,
      show (↑Real.pi * (a - (starRingEnd ℂ) a)) = ↑Real.pi * a + (-(↑Real.pi * (starRingEnd ℂ) a))
        by ring, Complex.exp_add]
    ring
  have hnorm : ∀ l ∈ Λ, ∀ z, ‖ψ (z + l)‖ = ‖ψ z‖ := by
    intro l hl z
    rw [hshift l hl z, norm_mul, Complex.norm_exp]
    simp

  obtain ⟨s, b, hfin, hbΛ⟩ := exists_basis_in Λ hΛ
  haveI : Fintype s := Fintype.ofFinite s
  have hspan : Submodule.span ℤ (Set.range b) ≤ Λ :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hbΛ)
  have hcpt : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hψ.continuous.continuousOn
  have hbd : Bornology.IsBounded (Set.range ψ) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hz : z = ZSpan.fract b z + (ZSpan.floor b z : Fin g → ℂ) := by
      rw [ZSpan.fract_apply]; abel
    rw [hz, hnorm _ (hspan (ZSpan.floor b z).2)]
    exact hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b z))
  intro l hl
  have hconst : ψ (0 + l) = ψ 0 := hψ.apply_eq_apply_of_bounded hbd _ _
  rw [hshift l hl 0] at hconst
  have hψ0 : ψ 0 ≠ 0 := mul_ne_zero (hθ0 0) (Complex.exp_ne_zero _)
  have hexp : Complex.exp (Real.pi * (((2 * (w ⬝ᵥ Hm.mulVec (star l)).im : ℝ) : ℂ) * I)) = 1 := by
    have := hconst
    rw [mul_eq_left₀ hψ0] at this
    exact this
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨n, ?_⟩
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : ((w ⬝ᵥ Hm.mulVec (star l)).im : ℂ) = n := by
    have : (Real.pi : ℂ) * 2 * I * ((w ⬝ᵥ Hm.mulVec (star l)).im : ℂ) =
        (Real.pi : ℂ) * 2 * I * n := by
      push_cast at hn
      linear_combination hn
    have h0 : (Real.pi : ℂ) * 2 * I ≠ 0 := mul_ne_zero (mul_ne_zero hpi two_ne_zero) hI
    exact mul_left_cancel₀ h0 this
  exact_mod_cast h2

end GlobalTheory.ThetaLiouville
