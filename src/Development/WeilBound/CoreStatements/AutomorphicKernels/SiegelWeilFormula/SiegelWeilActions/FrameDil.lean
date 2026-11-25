module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepMA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitP
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dM {R : Type} [CommRing R] {n : ℕ} (i₀ : Fin n) (x y : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  1 + (x - 1) • Matrix.single (Sum.inl i₀) (Sum.inl i₀) 1 + (y - 1) • Matrix.single (Sum.inr i₀) (Sum.inr i₀) 1

theorem dM_apply {R : Type} [CommRing R] {n : ℕ} (i₀ : Fin n) (x y : R) (u v : Fin n ⊕ Fin n) :
    dM i₀ x y u v = if u = v then (if u = Sum.inl i₀ then x else if u = Sum.inr i₀ then y else 1) else 0 := by
  simp only [dM, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.one_apply, smul_eq_mul]
  rcases u with u | u <;> rcases v with v | v <;> simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
    false_and, ite_false, mul_zero, add_zero, and_self] <;> by_cases h : u = v <;> by_cases h' : u = i₀ <;> subst_vars <;>
    simp_all [eq_comm]

theorem dM_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (i₀ : Fin n) (f : R →+* S) (x y : R) :
    (dM i₀ x y).map f = dM i₀ (f x) (f y) := by
  ext u v
  rw [Matrix.map_apply, dM_apply, dM_apply]
  split_ifs <;> simp

theorem isDil_inv {n : ℕ} {X : Fin n → ℝ} {τ : ℝ} {y : GR n} (h : IsDil X τ y) : IsDil X (-τ) y⁻¹ := by
  unfold IsDil at *
  set M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := Matrix.fromBlocks (Matrix.diagonal fun j => (Real.exp (-τ * X j) : ℂ)) 0 0
    (Matrix.diagonal fun j => (Real.exp (-(-τ * X j)) : ℂ)) with hM'
  have h1 : mR y⁻¹ * mR y = 1 := by
    show ((y⁻¹ : GR n) : GL (Fin n ⊕ Fin n) ℂ).1 * (y : GL (Fin n ⊕ Fin n) ℂ).1 = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have h2 : mR y * M' = 1 := by
    rw [h, hM', Matrix.fromBlocks_multiply]
    simp only [Matrix.diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [← Matrix.fromBlocks_one]
    congr 1 <;> (ext i j; simp only [Matrix.diagonal_apply, Matrix.one_apply]; split_ifs <;>
      simp [← Complex.exp_add])
  calc mR y⁻¹ = mR y⁻¹ * (mR y * M') := by rw [h2, Matrix.mul_one]
    _ = M' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

end PositivityTheory.SiegelWeilFormula.Act.CL

end
