module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

noncomputable section

namespace GlobalTheory.MeanDual.Alg

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def halfTraceForm : LinearMap.BilinForm ℚ (Fin j → E) :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (x ⬝ᵥ y) / 2)
    (fun x x' y => by rw [add_dotProduct, map_add (f := _), add_div])
    (fun c x y => by rw [smul_dotProduct, map_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc])
    (fun x y y' => by rw [dotProduct_add, map_add (f := _), add_div])
    (fun c x y => by rw [dotProduct_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc])

theorem halfTraceForm_apply (x y : Fin j → E) :
    halfTraceForm E j x y = Algebra.trace ℚ E (x ⬝ᵥ y) / 2 := rfl

theorem halfTraceForm_symm : (halfTraceForm E j).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [halfTraceForm_apply, halfTraceForm_apply, dotProduct_comm]

theorem halfTraceForm_left (x : Fin j → E) (h : ∀ y, halfTraceForm E j x y = 0) : x = 0 := by
  ext i
  rw [Pi.zero_apply]
  by_contra hx

  have h1 := h (Pi.single i (x i)⁻¹)
  rw [halfTraceForm_apply, dotProduct_single, mul_inv_cancel₀ hx, ← map_one (algebraMap ℚ E),
    Algebra.trace_algebraMap, nsmul_eq_mul, mul_one] at h1
  have h2 : (0 : ℚ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  linarith

theorem halfTraceForm_nondegenerate : (halfTraceForm E j).Nondegenerate := by
  refine ⟨halfTraceForm_left E j, fun y hy => halfTraceForm_left E j y fun x => ?_⟩
  rw [(halfTraceForm_symm E j).eq]
  exact hy x

theorem restrict_trDual (Λ : Submodule (𝓞 E) (Fin j → E)) :
    (trDual E j Λ).restrictScalars ℤ =
      (halfTraceForm E j).dualSubmodule (Λ.restrictScalars ℤ) := by
  ext y
  simp only [Submodule.restrictScalars_mem, mem_trDual, LinearMap.BilinForm.mem_dualSubmodule,
    Submodule.mem_one, halfTraceForm_apply, eq_intCast]
  constructor
  · intro hy x hx
    obtain ⟨z, hz⟩ := hy x hx
    refine ⟨z, ?_⟩
    rw [dotProduct_comm, hz]
    ring
  · intro hy x hx
    obtain ⟨z, hz⟩ := hy x hx
    refine ⟨z, ?_⟩
    rw [dotProduct_comm]
    linarith

theorem isLattice_restrict (Λ : Submodule (𝓞 E) (Fin j → E)) (h : Submodule.IsFullLattice E Λ) :
    Submodule.IsFullLattice ℚ (Λ.restrictScalars ℤ) := by
  first | exact _root_.GlobalTheory.LatFacts.isLattice_int | exact @_root_.GlobalTheory.LatFacts.isLattice_int | apply _root_.GlobalTheory.LatFacts.isLattice_int <;> assumption

theorem exists_basis (Λ : Submodule (𝓞 E) (Fin j → E)) (h : Submodule.IsFullLattice E Λ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ (Fin j → E)),
      Λ.restrictScalars ℤ = Submodule.span ℤ (Set.range b) := by

  have := isLattice_restrict E j Λ h
  have := Submodule.IsLattice.free ℚ (Λ.restrictScalars ℤ)
  have := Submodule.IsLattice.finite ℚ (Λ.restrictScalars ℤ)
  let bF := Module.finBasis ℤ (Λ.restrictScalars ℤ)
  refine ⟨_, bF.extendOfIsFullLattice ℚ, ?_⟩
  have hb : ⇑(bF.extendOfIsFullLattice ℚ) = (Λ.restrictScalars ℤ).subtype ∘ bF :=
    funext fun k => bF.extendOfIsFullLattice_apply ℚ k
  rw [hb, Set.range_comp, ← Submodule.map_span, bF.span_eq, Submodule.map_top,
    Submodule.range_subtype]

theorem isLattice_trDual_and_trDual_trDual :
    ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)),
      Submodule.IsFullLattice E Λ →
        Submodule.IsFullLattice E (trDual E j Λ) ∧ trDual E j (trDual E j Λ) = Λ := by
  intro E _ _ j Λ h
  obtain ⟨n, b, hb⟩ := exists_basis E j Λ h
  have hB := halfTraceForm_nondegenerate E j
  have hS := halfTraceForm_symm E j

  have hD : (trDual E j Λ).restrictScalars ℤ =
      Submodule.span ℤ (Set.range ((halfTraceForm E j).dualBasis hB b)) := by
    rw [restrict_trDual, hb, LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB]
  refine ⟨{ toIsLattice := ?_, span_eq_top := ?_ }, ?_⟩
  · apply Submodule.IsLattice.of_fg E
    apply Submodule.FG.of_restrictScalars ℤ
    rw [hD]
    exact Submodule.fg_span (Set.finite_range _)
  · refine eq_top_iff.mpr fun v _ => ?_
    have hv : v ∈ Submodule.span ℚ (Set.range ((halfTraceForm E j).dualBasis hB b)) := by
      rw [((halfTraceForm E j).dualBasis hB b).span_eq]
      trivial
    have h1 : Set.range ((halfTraceForm E j).dualBasis hB b) ⊆ (trDual E j Λ : Set (Fin j → E)) := by
      rintro _ ⟨k, rfl⟩
      have hk : (halfTraceForm E j).dualBasis hB b k ∈ (trDual E j Λ).restrictScalars ℤ := by
        rw [hD]
        exact Submodule.subset_span ⟨k, rfl⟩
      exact hk
    exact Submodule.span_le_restrictScalars ℚ E _ (Submodule.span_mono h1 hv)
  · apply Submodule.restrictScalars_injective ℤ _ _
    rw [restrict_trDual, restrict_trDual, hb,
      LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ hB hS]

end GlobalTheory.MeanDual.Alg
