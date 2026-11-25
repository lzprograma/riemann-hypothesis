module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical
namespace GlobalTheory.AdTh
variable {D : D7} {r g : ℕ}

theorem isMod_of (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) (hm : Formalism.L2.Pj.ModelW W hr X)
    (hp : ∀ ρ, tauE D ρ ∈ X.Ψ) : IsMod W hr X := by
  have hpsi : ∀ τ : D.host.E →+* ℂ, τ ∈ X.Ψ ↔ ∃ ρ, τ = tauE D ρ := by
    intro τ
    refine ⟨fun h => ?_, fun ⟨ρ, h⟩ => h ▸ hp ρ⟩
    have h1 := (X.cmType τ).1 h
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.StdRat.tauE_cm D τ).2 (fun ⟨ρ, hρ⟩ => h1 (hρ ▸ hp ρ))
    exact ⟨ρ, hρ.symm⟩
  obtain ⟨ρ⟩ : Nonempty D.what₂.Tau := by
    by_contra hne
    have h := GlobalTheory.StdRat.tauE_cm D D.host.φ₀
    obtain ⟨ρ, -⟩ := h.2 (fun ⟨ρ, _⟩ => hne ⟨ρ⟩)
    exact hne ⟨ρ⟩
  refine ⟨hm, hpsi, ?_⟩
  have h1 := X.κ0_sign ⟨tauE D ρ, hp ρ⟩
  have h2 := xi_zero_im_pos D ρ
  rcases X.κ0_xi with h | h
  · rw [h, hm.2]; ring
  · exfalso
    rw [h, hm.2] at h1
    simp [map_ofNat] at h1
    linarith

end GlobalTheory.AdTh
