module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import PositivityTheory.AutomorphicForms.PublishedInputs.BorelInjectivity.EquivariantProjections.ExistsEquivariantProjOfLeSumIrreducible

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRatDetPos, Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRatDetPos =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRatDetPos", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField GlobalTheory.BorelCoh UpperTheory.V.TR
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.WeakApproxGL

theorem denseRange_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    DenseRange ((pInf F).comp (algebraMap F (GlobalTheory.CuspRep.Ad F))) := by
  have hc : Continuous (infEq F).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc

theorem exists_rat_det_pos : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ)
    (g : GL (Fin a) (InfinitePlace F → ℝ)), ∃ h : GL (Fin a) F, ∀ v, 0 < ((((Matrix.GeneralLinearGroup.map (pInf F)).comp
      (GlobalTheory.CuspRep.ratGL F a)) h) * g).val.det v := by
  intro F _ _ _ a g
  set φ : F →+* (InfinitePlace F → ℝ) := (pInf F).comp (algebraMap F (GlobalTheory.CuspRep.Ad F)) with hφ
  have hcomp : ∀ h : GL (Fin a) F, (((Matrix.GeneralLinearGroup.map (pInf F)).comp (GlobalTheory.CuspRep.ratGL F a)) h).val
      = (h.val).map φ := fun h => by
    ext i j; rfl
  have hdu : IsUnit g.val.det := Matrix.isUnits_det_units g
  have hd : ∀ v, g.val.det v ≠ 0 := fun v => ((Pi.isUnit_iff.1 hdu) v).ne_zero
  have hopen : IsOpen {y : InfinitePlace F → ℝ | ∀ v, 0 < y v * g.val.det v} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)
  obtain ⟨t, ht⟩ := (denseRange_inf F).exists_mem_open hopen
    ⟨fun v => (g.val.det v)⁻¹, fun v => by simp [hd v]⟩
  have ht' : ∀ v, 0 < φ t v * g.val.det v := ht
  cases a with
  | zero =>
    refine ⟨1, fun v => ?_⟩
    rw [Matrix.det_isEmpty]
    exact one_pos
  | succ n =>
    have ht0 : t ≠ 0 := by
      rintro rfl
      obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
      have := ht' v
      simp at this
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.diagonal (Function.update 1 0 t)
    have hD : D.det = t := by
      rw [Matrix.det_diagonal, Fin.prod_univ_succ]
      simp
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero D (hD ▸ ht0), fun v => ?_⟩
    have e : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, (M.map φ).det = φ M.det := fun M => (RingHom.map_det φ M).symm
    rw [Units.val_mul, Matrix.det_mul, hcomp, e, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hD]
    exact ht' v

end GlobalTheory.WeakApproxGL
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRatDetPos =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRatDetPos\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.RatPts

theorem pInf_algebraMap (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    TR.pInf F (algebraMap F (Ad F) x) = rhom x := by
  funext v
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
    ((algebraMap F (Ad F) x).1 v) = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x
  rw [AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  simpa using InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe
    (IsTotallyReal.isReal v) (WithAbs.toAbs _ x)

theorem pInf_ratGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) = toInf γ := by
  ext i j v
  exact congrFun (pInf_algebraMap F (γ i j)) v

theorem ratGL_real_fin : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F),
    ratGL F 2 γ = TR.infGL F 2 (toInf γ) * finGL F 2 (toFin γ) ∧
      ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), ∃ τ : GL (Fin 2) F, Pos (toInf τ * h) := by
  intro F _ _ _ γ
  refine ⟨?_, fun h => ?_⟩
  · rw [← pInf_ratGL]
    exact (TR.infGL_mul_finGL (ratGL F 2 γ)).symm
  · obtain ⟨τ, hτ⟩ := GlobalTheory.WeakApproxGL.exists_rat_det_pos F 2 h
    refine ⟨τ, fun v => ?_⟩
    have e := hτ v
    rwa [MonoidHom.comp_apply, pInf_ratGL] at e

end GlobalTheory.HilbertThetaSeries.RatPts


end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor =====
