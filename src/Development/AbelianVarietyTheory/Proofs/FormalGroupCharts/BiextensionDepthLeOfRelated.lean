module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValuesEqOfRelatedBiextensions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotInPsiConj
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.BiextensionDepthLeOfRelated

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.BiextensionDepthLeOfRelated =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.BiextensionDepthLeOfRelated", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotInPsiConj\npublic import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity\npublic import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValuesEqOfRelatedBiextensions\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp

theorem inPsi_or_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : E →+* ℂ) :
    InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ) := by
  apply GlobalTheory.LabSelf.inPsi_or_conj

theorem nuAlg_le_of_jrel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (_ : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (d : ℕ) (B B' : FB T.V d (𝓞 E)) (φ φi : Pt T.V 1 d) (h h' : PS T.Fr 2 d) (u u' : Lt1 Dw → Fin d → T.Fr), (∀ m, ∃ ε : PS T.V 2 d, JRel m B B' φ φi ε) → B.IsCanonGauge T.Fr h → B'.IsCanonGauge T.Fr h' → (∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct T.Fr B' a).mulVec (u' ℓ) = io (embK c ℓ.1 a) • u' ℓ) → (∀ ℓ, u ℓ = ((dLin φ).map (algebraMap T.V T.Fr)).mulVec (u' ℓ)) → ∀ (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuAlg Dw T B h u e k a n ≤ nuAlg Dw T B' h' u' e k a n := by
  intro E _ _ _ H Dw l Xo c _ hstar T io d B B' φ φi h h' u u' hrel hB hB' heig hu e k a n
  unfold nuAlg
  refine le_iInf fun P => le_iInf fun hP => le_iInf fun f' => ?_
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.ChartVal.exists_nabValN_eq T.V d (𝓞 E) T.Fr B B' φ φi hrel h h' hB hB' (E →+* ℂ) Dw.mult
    ComplexEmbedding.conjugate (InPsi H) (fun τ => io.comp (embK c τ)) (fun τ => by ext x; simp)
    (inPsi_or_conjugate H)
    (fun τ a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hstar]
      congr 1
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj])
    (fun σ τ hne => by
      have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
        by_contra hc
        push Not at hc
        exact hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by simpa using hc a))
      obtain ⟨a, ha⟩ := hex
      refine ⟨a, ?_⟩
      have h0 : embK c σ a - embK c τ a ≠ 0 := by
        rw [sub_ne_zero]
        intro h1
        apply ha
        rw [← embK_coe c, ← embK_coe c, h1]
      rw [RingHom.comp_apply, RingHom.comp_apply, ← map_sub]
      exact (Ne.isUnit h0).map _)
    u u' (fun ℓ a => heig a ℓ) hu n P hP.1.1 H.w0 k f'
  refine iInf_le_of_le P (iInf_le_of_le hP (iInf_le_of_le f ?_))
  exact le_of_eq (congrArg (nval T.V e) hf)

end GlobalTheory.ChartCmp
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.BiextensionDepthLeOfRelated =====
