module

public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
public import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-! # ExistsOrthonormalBasisSesquilinear: Preliminary helper declarations for global theta kernels. -/

@[expose] public section

theorem UpperTheory.Reformulated.B.Qh52.exists_orthonormal_basis_sesquilinear :
    ∀ {V : Type} [AddCommGroup V] [_root_.Module ℂ V]
    [FiniteDimensional ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ (a b : V), ((B : V → V →ₗ⋆[ℂ] ℂ) b : V → ℂ) a = Star.star (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) b)) →
      (∀ (a : V), a ≠ (0 : V) → (0 : ℝ) < (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) a).re) →
        ∃ (e : Fin (Module.finrank ℂ V) → V),
          (∀ (i : Fin (Module.finrank ℂ V)), ((B : V → V →ₗ⋆[ℂ] ℂ) (e i) : V → ℂ) (e i) = (1 : ℂ)) ∧
            (∀ (x y : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) y =
                  ∑ i : Fin (Module.finrank ℂ V),
                    ((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) (e i) * ((B : V → V →ₗ⋆[ℂ] ℂ) (e i) : V → ℂ) y) ∧
              ∀ (x y : V),
                ‖((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤
                  (((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) x).re * (((B : V → V →ₗ⋆[ℂ] ℂ) y : V → ℂ) y).re := by
  intro V _ _ _ B hs hp
  let c : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => B y x
      conj_inner_symm := fun x y => (hs x y).symm
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact (hp x h).le
      add_left := fun x y z => map_add (B z) x y
      smul_left := fun x y r => by simp
      definite := fun x h => by
        by_contra hx
        have h1 := hp x hx
        have h2 : B x x = 0 := h
        rw [h2] at h1
        simp at h1 }
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hB : ∀ x y : V, B x y = inner ℂ y x := fun _ _ => rfl
  let b := stdOrthonormalBasis ℂ V
  refine ⟨b, fun i => ?_, fun x y => ?_, fun x y => ?_⟩
  · rw [hB]
    exact b.inner_eq_one i
  · simp only [hB]
    rw [← b.sum_inner_mul_inner y x]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · simp only [hB]
    have h := inner_mul_inner_self_le (𝕜 := ℂ) y x
    rw [norm_inner_symm x y] at h
    rw [sq, mul_comm (inner ℂ x x).re]
    exact h
