module

public import Formalism.PeriodIntegrals.IsLowUnitH
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.PeriodIntegrals.BesselPeriodGGP
public import Formalism.HermitianCurvature.StatementB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap

open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU IsOrthProjOnto InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def dimV (k r : ℕ) : ℝ := 2 * (r : ℝ) + k + 1

def decExp (r : ℕ) (h : ℝ) : ℝ := h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))

def DecGap (k r : ℕ) (h : ℝ) : Prop := 120 * dimV k r * ((r : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤ h

def mulP {k r : ℕ} (p : Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

theorem measurable_mulP {k r : ℕ} : Measurable (mulP (k := k) (r := r)) := by
  unfold mulP
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  fun_prop

def muS {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) := (μW.prod μN).map mulP

section Side

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

def IsSide (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r)) : Prop :=
  1 ≤ k ∧
  (IsHCParam lam ∧ IsDSHpk k r ε lam σ ∧ GapAtLeast ε lam h) ∧
  IsLowUnitH k r ε lam σ w₀ ∧
  (inWb k r z ∧ 0 < Tz k r z) ∧
  c ≠ 0 ∧
  (IsHCParam u ∧ IsHCTypeW k r z u π) ∧
  (PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW ∧ PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN ∧
    PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) ∧
  (SigmaFinite ν ∧ PI.BesselPeriodGGP.IsQuotMeas μG (muS μW μN) ν)

def IsSideNormalised (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r)) : Prop :=
  IsSide k r ε lam h σ w₀ z c u π μW μN μG ν ∧ μW Set.univ = 1

def KFinDecay (k r : ℕ) (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ v v' : H, IsKFinHpk (k := k) (r := r) σ v → IsKFinHpk (k := k) (r := r) σ v' →
    ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪v', σ x v⟫_ℂ‖ ≤ C * gN x ^ (-a)

def wordSeminorm {k r : ℕ} (σ : Mat k r → (H →L[ℂ] H)) (Ws : List (List (Mat k r))) (w : H) : ℝ :=
  (Ws.map fun D => ‖dsigW (k := k) (r := r) σ D w‖).sum

end Side

def DecKFin : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    1 ≤ k → IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → DecGap k r h →
    KFinDecay k r σ (decExp r h)

def DecSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ),
    IsHCParam lam → IsDSHpk k r ε lam σ → KFinDecay k r σ a →
    ∀ v₀ : H, IsKFinHpk (k := k) (r := r) σ v₀ →
      ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ D ∈ Ws, ∀ X ∈ D, InLieHpk k r X) ∧
        ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
          ‖⟪v₀, σ x w⟫_ℂ‖ ≤ C * wordSeminorm σ Ws w * gN x ^ (1 - a)

end GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap
