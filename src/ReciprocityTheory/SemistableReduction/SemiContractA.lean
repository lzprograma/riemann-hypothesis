module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix
open scoped ComplexOrder

theorem sc_schur_posDef {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k]
    {A : Matrix k k ℂ} (B : Matrix k m ℂ) (D : Matrix m m ℂ) (hA : A.PosDef)
    (h : (fromBlocks A B Bᴴ D).PosDef) : (D - Bᴴ * A⁻¹ * B).PosDef := by
  classical
  let _ := hA.isUnit.invertible
  apply ((PosDef.fromBlocks₁₁ B D hA).mp h.posSemidef).posDef_iff_det_ne_zero.mpr
  intro hz
  exact h.det_pos.ne' (by rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, hz, mul_zero])

end ReciprocityTheory.MultiplicativeHeights
