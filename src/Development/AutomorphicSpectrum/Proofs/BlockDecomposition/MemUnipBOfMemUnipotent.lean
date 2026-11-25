module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic Matrix
open scoped ValuativeRel
open PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.JSBound

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem psiOK_of_hasConductor {ψ₁ : AddChar F Circle} (h : GlobalTheory.SplitWeil.HasConductor ψ₁ 1) :
    PsiOK (Circle.coeHom.compAddChar ψ₁) := by
  have h1 : ∀ y : F, ValuativeRel.valuation F y ≤ 1 → ψ₁ y = 1 := fun y hy =>
    (h 1).mpr (by simp) y (by simpa using hy)
  refine ⟨fun x hx => ?_, ?_, fun x => Circle.norm_coe (ψ₁ x)⟩
  · simp [h1 x ((Valuation.mem_integer_iff _ _).mp hx)]
  · have hlt := GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one F
    have hne := GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_ne_zero F
    set ϖ : F := (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) with hϖdef
    have hϖ : ϖ ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
    have hinv : ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hϖ, map_one]
    have hnot : ¬ ValuativeRel.valuation F ϖ⁻¹ ≤ ValuativeRel.valuation F ((1 : Fˣ) : F) := by
      rw [Units.val_one, map_one]
      intro hle
      have h3 : ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ ≤
          ValuativeRel.valuation F ϖ * 1 := by gcongr
      rw [hinv, mul_one] at h3
      exact absurd hlt (not_lt.mpr h3)
    have hex : ¬ ∀ y : F, ValuativeRel.valuation F y ≤ ValuativeRel.valuation F ϖ⁻¹ → ψ₁ y = 1 :=
      fun hall => hnot ((h _).mp hall)
    push Not at hex
    obtain ⟨y, hy, hy1⟩ := hex
    refine ⟨y, ?_, ?_⟩
    · rw [Valuation.mem_integer_iff, map_mul]
      calc ValuativeRel.valuation F ϖ * ValuativeRel.valuation F y
          ≤ ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ := by gcongr
        _ = 1 := hinv
    · intro hc
      apply hy1
      apply Circle.ext
      rw [Circle.coe_one]
      exact hc

theorem mem_unipB_of_mem_unipotent {n : ℕ} {g : GL (Fin n) F} (hg : g ∈ Iwasawa.unipotent F n) :
    g ∈ GlobalTheory.SmGL.unipB F (Fin n) := by
  obtain ⟨hut, hdiag⟩ := hg
  have hp : g ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.points (Fin n)) := by
    intro i j hij
    exact hut (by simpa [GlobalTheory.SmGL.blk, GlobalTheory.SmGL.points] using hij)
  refine ⟨⟨g, hp⟩, ?_, rfl⟩
  show GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.points (Fin n)) ⟨g, hp⟩ = 1
  refine funext fun a => ?_
  show (GlobalTheory.SmGL.diagBlock F (GlobalTheory.SmGL.points (Fin n)) a).toHomUnits ⟨g, hp⟩ = 1
  apply Units.ext
  ext i j
  show (GlobalTheory.SmGL.diagBlock F (GlobalTheory.SmGL.points (Fin n)) a ⟨g, hp⟩) i j = (1 : Matrix Unit Unit F) i j
  obtain rfl : i = j := Subsingleton.elim _ _
  rw [Matrix.one_apply_eq]
  exact hdiag a

theorem superDiag_eq_superdiagSum {n : ℕ} (g : GL (Fin n) F) :
    GlobalTheory.Whittaker.superDiag g = Whittaker.superdiagSum (g : Matrix (Fin n) (Fin n) F) := by
  simp only [GlobalTheory.Whittaker.superDiag, GroundTheory.Automorphic.Whittaker.superdiagSum, Finset.sum_filter]

theorem whit_of_isFunctional {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} {ψ₁ : AddChar F Circle} {l : Module.Dual ℂ V}
    (h : GlobalTheory.Whittaker.IsFunctional ψ₁ ρ l) : Whit ρ (Circle.coeHom.compAddChar ψ₁) l := by
  intro g hg u
  rw [h g (mem_unipB_of_mem_unipotent hg) u, GroundTheory.Automorphic.Whittaker.psiN,
    ← superDiag_eq_superdiagSum]
  all_goals rfl

end Local

private theorem continuous_of_hasConductor_one {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ψ₁ : AddChar k Circle}
    (h : GlobalTheory.SplitWeil.HasConductor ψ₁ 1) : Continuous ψ₁ := by
  have h1 : ∀ y : k, ValuativeRel.valuation k y ≤ 1 → ψ₁ y = 1 := fun y hy =>
    (h 1).mpr (by simp) y (by simpa using hy)
  have hopen : IsOpen ((ValuativeRel.valuation k).integer : Set k) := Valuation.isOpen_integer
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' ((ValuativeRel.valuation k).integer : Set k),
    hopen.preimage (continuous_sub_right x), ?_, ?_⟩
  · show x - x ∈ (ValuativeRel.valuation k).integer
    rw [sub_self]
    exact zero_mem _
  · intro y hy
    have hy' : ψ₁ (y - x) = 1 := h1 _ ((Valuation.mem_integer_iff _ _).mp hy)
    calc ψ₁ y = ψ₁ ((y - x) + x) := by rw [sub_add_cancel]
      _ = ψ₁ (y - x) * ψ₁ x := AddChar.map_add_eq_mul _ _ _
      _ = ψ₁ x := by rw [hy', one_mul]

theorem global_character_holds : G4 := by
  intro E _ _ _ a ha π w
  obtain ⟨ψ₁, hψ⟩ := GlobalTheory.SplitWeil.Model.exists_hasConductor (k := w.adicCompletion E)
  have hne : ψ₁ ≠ 1 := by
    rintro rfl
    exact GlobalTheory.SplitWeil.Model.not_hasConductor_one 1 hψ
  obtain ⟨l, hl0, hl⟩ := GlobalTheory.Published.cuspidalGeneric_holds E a ha π w ψ₁
    (continuous_of_hasConductor_one hψ) hne
  exact ⟨_, psiOK_of_hasConductor hψ, l, hl0, whit_of_isFunctional hl⟩

end GlobalTheory.CompanionTheory.JSBound
