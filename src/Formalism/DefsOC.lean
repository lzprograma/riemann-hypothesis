module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.Basic

@[expose] public section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def Sa (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (x / n - 1)

def MellinSgen : Prop :=
  ∀ (a : ℕ → ℝ) (K : ℝ), (∀ n : ℕ, |a n| ≤ K * ArithmeticFunction.vonMangoldt n) →
    Measurable (Sa a) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |Sa a x| * x ^ (-σ - 1)) (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (Sa a x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => (a n : ℂ)) s / (s * (s - 1))

end Formalism
