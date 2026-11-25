module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.Development
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
import Mathlib.Tactic.TypeStar
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

noncomputable section

open MeasureTheory Measure Topology
open scoped ENNReal NNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def subOf (H : Set G) (h1 : (1 : G) ∈ H) (hm : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) (hi : ∀ x ∈ H, x⁻¹ ∈ H) :
    Subgroup G where
  carrier := H
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hm a ha b hb
  inv_mem' := fun {a} ha => hi a ha

theorem pull (S : Subgroup G) (hS : IsClosed (S : Set G)) (ν : Measure G) (hνc : ν (S : Set G)ᶜ = 0)
    (hνi : ∀ s ∈ S, ν.map (fun x => s * x) = ν) (hνf : IsFiniteMeasureOnCompacts ν) :
    (ν.comap (Subtype.val : S → G)).IsMulLeftInvariant ∧
      IsFiniteMeasureOnCompacts (ν.comap (Subtype.val : S → G)) ∧
      (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := by
  apply _root_.PI.NMeasInv.UnitaryGroupMassFormula.pull <;> assumption

theorem haar_unique (S : Subgroup G) (hS : IsClosed (S : Set G)) (μ m : Measure G) (hμ0 : μ ≠ 0)
    (hμc : μ (S : Set G)ᶜ = 0) (hμi : ∀ s ∈ S, μ.map (fun x => s * x) = μ) (hμf : IsFiniteMeasureOnCompacts μ)
    (hmc : m (S : Set G)ᶜ = 0) (hmi : ∀ s ∈ S, m.map (fun x => s * x) = m) (hmf : IsFiniteMeasureOnCompacts m) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ m = c • μ := by
  apply _root_.PI.NMeasInv.UnitaryGroupMassFormula.haar_unique <;> assumption

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore
