module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import GroundTheory.GlobalFields.TateThesis.LocalConductor
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Filter
open GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

namespace GlobalTheory.CompanionTheory.MuOpen

theorem isOpen_ker_loc {L : Type} [Field L] [NumberField L] (χ : HChar L) (w : HeightOneSpectrum (𝓞 L)) :
    IsOpen ((χ.loc w).ker : Set (w.adicCompletion L)ˣ) :=
  GroundTheory.Global.isOpen_ker_of_continuous w GroundTheory.Global.Complex.units_noSmallSubgroups (χ.loc w)
    (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele w))

theorem unrChar_apply_of_isUnitAt {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (α : ℂˣ)
    (x : (w.adicCompletion L)ˣ) (hx : IsUnitAt w x) : GlobalTheory.SmGL.unrChar (w.adicCompletion L) α x = 1 := by
  rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion]
  have hx' : Valued.v (x : w.adicCompletion L) = 1 := hx
  rw [hx']
  simp

end GlobalTheory.CompanionTheory.MuOpen


open GlobalTheory.CompanionTheory.MuOpen in
theorem GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e) → MuEx := by
  intro h E _ _ _ hU
  obtain ⟨μ, e, hμ⟩ := h E hU
  refine ⟨μ, e, hμ, fun w hw x hx => ?_, GlobalTheory.Mem.UnrAe.unr_ae_and_level E μ |>.1, fun w => isOpen_ker_loc μ w⟩
  rw [hμ.2.2.1 w hw]
  exact unrChar_apply_of_isUnitAt w _ x hx

end
