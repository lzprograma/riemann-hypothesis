module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecOnBasicOpenLocalization
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

variable {Y : Scheme.{0}} {M : LB Y} {V : Y.Opens}

noncomputable def SecOn.chartBasicOpen (hM : M.IsLB) (i : M.ι) (a : Γ(Y, V))
    (h : Y.basicOpen a ≤ M.U i) : SecOn M V →ₗ[Γ(Y, V)] Γ(Y, Y.basicOpen a) where
  toFun s := SecOn.chart hM i h (SecOn.restrict M (Y.basicOpen_le a) s)
  map_add' s t := by rw [map_add (f := _), map_add (f := _)]
  map_smul' r s := by
    rw [map_smulₛₗ, map_smul, RingHom.id_apply, Algebra.smul_def r]
    rfl

theorem SecOn.isLocalizedModule_chartBasicOpen (hM : M.IsLB) (hV : IsAffineOpen V) (i : M.ι)
    (a : Γ(Y, V)) (h : Y.basicOpen a ≤ M.U i) :
    IsLocalizedModule (Submonoid.powers a) (SecOn.chartBasicOpen hM i a h) := by
  have := hV.isLocalization_basicOpen a
  obtain ⟨h₁, h₂⟩ := secOn_basicOpen_localization Y M V _ a (Y.basicOpen_le a) hM hV.isCompact
    hV.isQuasiSeparated rfl
  refine ⟨fun x => IsLocalizedModule.map_units
    (Algebra.linearMap Γ(Y, V) Γ(Y, Y.basicOpen a)) x, fun y => ?_, fun {x₁ x₂} e => ?_⟩
  · obtain ⟨k, x, e⟩ := h₂ ((SecOn.chart hM i h).symm y)
    refine ⟨⟨x, ⟨a ^ k, k, rfl⟩⟩, ?_⟩
    change a ^ k • y = SecOn.chart hM i h (SecOn.restrict M (Y.basicOpen_le a) x)
    rw [e, map_smul, LinearEquiv.apply_symm_apply, Algebra.smul_def, map_pow]
    rfl
  · obtain ⟨k, hk⟩ := h₁ (x₁ - x₂) (by
      rw [map_sub, sub_eq_zero]
      exact (SecOn.chart hM i h).injective e)
    refine ⟨⟨a ^ k, k, rfl⟩, ?_⟩
    change a ^ k • x₁ = a ^ k • x₂
    rwa [smul_sub, sub_eq_zero] at hk

theorem secOn_finitePresentation_projective :
    ∀ (Y : Scheme.{0}) (M : LB Y) (V : Y.Opens), M.IsLB → IsAffineOpen V → Module.FinitePresentation Γ(Y, V) (SecOn M V) ∧ Module.Projective Γ(Y, V) (SecOn M V) := by
  intro Y M V hM hV
  let s : Set Γ(Y, V) := {a | ∃ i, Y.basicOpen a ≤ M.U i}
  have hs : Ideal.span s = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
    obtain ⟨f, hf, hxf⟩ := hV.exists_basicOpen_le ⟨x, hi⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, i, hf⟩, hxf⟩
  choose c hc using fun g : s => g.2
  have hl (g : s) := hV.isLocalization_basicOpen g.1
  have hm (g : s) := SecOn.isLocalizedModule_chartBasicOpen hM hV (c g) g.1 (hc g)
  have hfp : Module.FinitePresentation Γ(Y, V) (SecOn M V) :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Rₚ := fun g => Γ(Y, Y.basicOpen g.1))
      (fun g => SecOn.chartBasicOpen hM (c g) g.1 (hc g)) fun _ => inferInstance
  have hfl : Module.Flat Γ(Y, V) (SecOn M V) :=
    Module.flat_of_isLocalized_span Γ(Y, V) (SecOn M V) s hs (fun g => Γ(Y, Y.basicOpen g.1))
      (fun g => SecOn.chartBasicOpen hM (c g) g.1 (hc g))
      fun g => IsLocalization.flat _ (Submonoid.powers g.1)
  exact ⟨hfp, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.AbLaw
