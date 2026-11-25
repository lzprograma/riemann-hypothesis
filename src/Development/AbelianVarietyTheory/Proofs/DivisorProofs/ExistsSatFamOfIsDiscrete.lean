module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.ResW

theorem exists_satFam_of_isDiscrete : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), (∀ x : CuspSub E N, ∀ᶠ v in Filter.cofinite, ∃ C, (CG.mk x).HasSat v C) ∧ ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∃ B, SatFam V B := by
  intro E _ _ _ N
  have hF := GlobalTheory.automorphicFormsFiniteGL
  refine ⟨fun x => UnrSat.eventually_hasSatGL_locRep hF E N x, fun V hV => ?_⟩
  choose σ hσ using GlobalTheory.DiscLocEx.exists_isLocCompGL hF E N V hV
  have h : ∀ w, ∃ B, GlobalTheory.LGrp.IsSpherical (σ w).ρ (GlobalTheory.LFun.KGL w (n := N)) → GlobalTheory.LFun.HasSatGL w (σ w).ρ B := fun w => by
    by_cases hs : GlobalTheory.LGrp.IsSpherical (σ w).ρ (GlobalTheory.LFun.KGL w (n := N))
    · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (σ w).smooth (σ w).irred hs
      exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose B hB using h
  refine ⟨B, fun φ hφ h0 => ?_⟩
  filter_upwards [GlobalTheory.SpehPair.eventually_spherical hV,
    LocSph.eventually_mem ((hV.aut φ hφ).level.mem_nhds (by simp))] with w hw hK
  refine GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (σ w).irred (hB w (hw _ (hσ w)))
    (fun f : GlobalTheory.LocDual.Maps V w (σ w) => f.1) (fun f => f.2.2) ?_ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_) h0
  · rw [GlobalTheory.LocDual.iSup_range_eq V hV.stable hV.irred w (σ w) (hσ w)]
    exact hφ
  · obtain ⟨g, rfl⟩ := hk
    exact hK g

end GlobalTheory.ResW
