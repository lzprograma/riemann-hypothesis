module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Unimod
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ConjDesc
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NormInj
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OpenNear
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.QuotDesc
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RigidNear
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.TwOrbConj
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ValuationNatCastLeOne
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MatchOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.HoweType
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.WeilBound.CuspidalAdmissibility.OccursIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TypedEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.OffStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitMatch
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStableAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.T2SpaceGlCompletionsOver
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootConj
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NearDown, Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.PlaceDown, Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.AtDown, Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SbInv, Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.InertData, Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitLev, Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyExOf, Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyEx

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NearDown =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NearDown", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarComm\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarConj\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Unimod\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ConjDesc\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NormInj\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OpenNear\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.QuotDesc\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RigidNear\nimport Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootConj\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.TwOrbConj\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ValuationNatCastLeOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.NearIdentityDescent

open UpperTheory.ConvolutionTheory.Loc.BallG
open UpperTheory.ConvolutionTheory.Loc.NearIdentityCentralizer (incl_inj sigma_incl root_conj)
open UpperTheory.ConvolutionTheory.Loc.NearIdentityAscent (sb_of_push avg_locConst set_left)

section Loc

variable {k E : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] {σ : E ≃ₐ[k] E}
  (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {n : ℕ} {r : ValueGroupWithZero E}
  (hr : r < valuation E (Module.finrank k E : E))

include hgen hr in
private theorem near {g : GL (Fin n) E} (hg : g ∈ ball n (r * valuation E (Module.finrank k E : E))) :
    ∃ κ ∈ ball n r, ∃ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ g = κ⁻¹ * incl u * sigmaGL σ κ := by
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  obtain ⟨κ, hκ, u, hu, hf, e⟩ := openNear E n σ _ hc r r hr le_rfl 1 (fun i j => by simp) (map_one _) g hg
  obtain ⟨u, rfl⟩ := ((hb n).2.2.1 hgen u).mp hf
  rw [one_mul, one_mul] at e
  exact ⟨κ, hκ, u, hu, e⟩

include hgen hr in
private theorem exists_push (hr0 : 0 < r) {a : GL (Fin n) k → ℂ} (ha : IsLocallyConstant a) :
    ∃ f ∈ SB (GL (Fin n) k), (∀ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r → f (u ^ Module.finrank k E) = a u) ∧
      ∀ γ, (¬ ∃ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ u ^ Module.finrank k E = γ) → f γ = 0 := by
  classical
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  have hj := (hb n).2.2.2.1
  haveI := (UpperTheory.V.Z.Tf.Orb.gLTop k n).2.2.1
  have hr1 : r < 1 := hr.trans_le (valuation_natCast_le_one _)
  let f : GL (Fin n) k → ℂ := fun γ =>
    if h : ∃ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ u ^ Module.finrank k E = γ then a h.choose else 0
  have h1 : ∀ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r → f (u ^ Module.finrank k E) = a u := by
    intro u hu
    have h : ∃ u' : GL (Fin n) k, (incl u' : GL (Fin n) E) ∈ ball n r ∧ u' ^ Module.finrank k E = u ^ Module.finrank k E :=
      ⟨u, hu, rfl⟩
    have := root_conj hr (y := 1) h.choose_spec.1 hu (by simpa using h.choose_spec.2)
    simp only [f, dite_eq_left h]
    rw [inv_one, one_mul, mul_one] at this
    exact congrArg a this
  have h2 : ∀ γ, (¬ ∃ u : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ u ^ Module.finrank k E = γ) → f γ = 0 :=
    fun γ h => dite_eq_right h
  refine ⟨f, sb_of_push (U := incl ⁻¹' ball (E := E) n r) (hj.isCompact_preimage (isCompact_ball hr1))
    (p := fun u => u ^ Module.finrank k E) (continuous_pow _) ?_ ha h1 h2, h1, h2⟩
  have e : (fun u : GL (Fin n) k => u ^ Module.finrank k E) '' (incl ⁻¹' ball (E := E) n r) =
      incl ⁻¹' ball (E := E) n (r * valuation E (Module.finrank k E : E)) := by
    ext γ
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Set.mem_preimage, map_pow]
      exact pow_mem_ball hr hu
    · intro hγ
      obtain ⟨u, hu, hf, huq⟩ := exists_fixed_root hc.isom hr hγ (sigma_incl σ γ)
      obtain ⟨u, rfl⟩ := ((hb n).2.2.1 hgen u).mp hf
      exact ⟨u, hu, incl_inj (by rw [map_pow, huq])⟩
  rw [e]
  exact (isOpen_ball (mul_pos hr0 (hr0.trans hr)).ne').preimage hj.continuous

end Loc

end UpperTheory.ConvolutionTheory.Loc.NearIdentityDescent

open UpperTheory.ConvolutionTheory.Loc.NearIdentityDescent UpperTheory.ConvolutionTheory.Loc.NearIdentityCentralizer UpperTheory.ConvolutionTheory.Loc.NearIdentityAscent UpperTheory.ConvolutionTheory.Loc.BallG UpperTheory.V.Z.Tf.Orb in
theorem UpperTheory.ConvolutionTheory.Loc.nearDown :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure → ∃ ρ : ValueGroupWithZero E, 0 < ρ ∧ ∀ φ ∈ SB (GL (Fin n) E), Function.support φ ⊆ ball n ρ →
        ∃ f ∈ SB (GL (Fin n) k), Match σ μE μk φ f := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ _ _ μE μk hμE hμk
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  have hj := (hb n).2.2.2.1
  obtain ⟨_, _, _, -⟩ := gLTop E n
  obtain ⟨_, _, _, -⟩ := gLTop k n
  have hθ : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((extCont k E).2.2 n).2 σ
  obtain ⟨r, hr0, hr⟩ := exists_radius (w := valuation E (Module.finrank k E : E))
    ((Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hc.pos.ne'))
  have hq1 := valuation_natCast_le_one (E := E) (Module.finrank k E)
  have hr1 : r < 1 := hr.trans_le hq1
  refine ⟨r * valuation E (Module.finrank k E : E), mul_pos hr0 (hr0.trans hr), fun φ hφ hs => ?_⟩
  set K := ballSub n r hr1 with hK
  have hKo : IsOpen (K : Set (GL (Fin n) E)) := isOpen_ball hr0.ne'
  have hKc : IsCompact (K : Set (GL (Fin n) E)) := isCompact_ball hr1
  have hKo' : IsOpen ((K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
    hKo.preimage hj.continuous
  have hKc' : IsCompact ((K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
    hj.isCompact_preimage hKc
  set c : ℂ := (((μk (K.comap (incl : GL (Fin n) k →* GL (Fin n) E))).toReal⁻¹ : ℝ) : ℂ) with hcdef
  set A : GL (Fin n) E → ℂ := fun u => ∫ κ in (K : Set (GL (Fin n) E)), φ (κ⁻¹ * u * sigmaGL σ κ) ∂μE with hA
  have hAl : IsLocallyConstant A := avg_locConst μE hθ hKc hKo.measurableSet hφ.1
  obtain ⟨f, hf, h1, h2⟩ := exists_push hgen hr hr0 (a := fun u => c * A (incl u))
    ((hAl.comp_continuous hj.continuous).comp fun z => c * z)
  refine ⟨f, hf, UpperTheory.ConvolutionTheory.Loc.nearCore k E σ hgen n μE μk hμE hμk r hr K rfl hKo hKc φ hφ f hf
    (fun g hg => near hgen hr (hs hg))
    (fun g hg => by by_contra h; exact hg (h2 g fun ⟨u, hu, e⟩ => h ⟨u, hu, e.symm⟩))
    (fun u hu => ?_)⟩
  have hμpos : (μk (K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Set (GL (Fin n) k))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(hKo'.measure_pos μk ⟨1, one_mem _⟩).ne', hKc'.measure_lt_top.ne⟩
  have hcongr : ∀ κ ∈ (K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Set (GL (Fin n) k)),
      f (κ⁻¹ * u ^ Module.finrank k E * κ) = c * A (incl u) := by
    intro κ hκ
    have hκK : (incl κ : GL (Fin n) E) ∈ K := hκ
    have hconj : (incl (κ⁻¹ * u * κ) : GL (Fin n) E) ∈ K := by
      rw [map_mul, map_mul, map_inv]
      exact K.mul_mem (K.mul_mem (K.inv_mem hκK) hu) hκK
    have e1 : κ⁻¹ * u ^ Module.finrank k E * κ = (κ⁻¹ * u * κ) ^ Module.finrank k E := by
      have := conj_pow (a := κ⁻¹) (b := u) (i := Module.finrank k E)
      rw [inv_inv] at this
      exact this.symm
    rw [e1, h1 _ hconj]
    congr 1
    have e2 : ∀ κ' : GL (Fin n) E, κ'⁻¹ * incl (κ⁻¹ * u * κ) * sigmaGL σ κ' =
        (incl κ * κ')⁻¹ * incl u * sigmaGL σ (incl κ * κ') := fun κ' => by
      simp only [map_mul, map_inv, sigma_incl, mul_inv_rev, mul_assoc]
    simp_rw [hA, e2]
    exact set_left μE K hKo.measurableSet (fun κ' => φ (κ'⁻¹ * incl u * sigmaGL σ κ')) hκK
  rw [setIntegral_congr_fun hKo'.measurableSet hcongr, setIntegral_const, Measure.real, Complex.real_smul]
  simp only [hcdef, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hμpos,
    Complex.ofReal_one, one_mul]
  rfl
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NearDown =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.PlaceDown =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.PlaceDown", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NearDown\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)

theorem UpperTheory.ConvolutionTheory.Loc.placeDown :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
      (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
        [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
        (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))), mE.IsHaarMeasure → mF.IsHaarMeasure →
      ∃ ρ : ValueGroupWithZero (w.1.adicCompletion E), 0 < ρ ∧ ∀ φ ∈ SB (GL (Fin n) (w.1.adicCompletion E)), Function.support φ ⊆ ball n ρ →
        ∃ f ∈ SB (GL (Fin n) (v.adicCompletion F)), PositivityTheory.Rg.Tf.Geo.Match (incFin E v) (galFin σ v) (Module.finrank F E) mE mF 1 (fun g => φ (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) g)) f := by
  intro F E _ _ _ _ _ _ σ hσ v w hw n _ _ _ _ mE mF hE hF
  obtain ⟨iA, iV, iF, iG, s, hs, hrk, hinc, hgal, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData_holds F E σ hσ v w hw
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  obtain ⟨hH, hM⟩ := UpperTheory.V.Z.Tf.Orb.placeOfLocal_holds F E σ hσ v w hw s hs hrk hinc hgal n mE mF hE hF
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨ρ, hρ, h⟩ := UpperTheory.ConvolutionTheory.Loc.nearDown (v.adicCompletion F) (w.1.adicCompletion E) s hs n _ mF hH hF
  refine ⟨ρ, hρ, fun φ hφ hsup => ?_⟩
  obtain ⟨f, hf, hm⟩ := h φ hφ hsup
  exact ⟨f, hf, hM φ hφ f hf hm⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.PlaceDown =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.AtDown =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.AtDown", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MatchOne\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.PlaceDown\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)

theorem UpperTheory.ConvolutionTheory.Loc.atDown :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
      (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) → ∀ n : ℕ,
      ∃ ρ : ValueGroupWithZero (w.1.adicCompletion E), 0 < ρ ∧ ∀ φ ∈ SB (GL (Fin n) (w.1.adicCompletion E)), Function.support φ ⊆ ball n ρ →
        ∃ f ∈ SB (GL (Fin n) (v.adicCompletion F)), UpperTheory.ConvolutionTheory.GM.MatchAt σ v 1 (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) f := by
  intro F E _ _ _ _ _ _ σ hσ v w hw n
  obtain ⟨i1, i2, i3, i4, mE, mF, hE, hF, h1, h2⟩ := (UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).1
  obtain ⟨ρ, hρ, h⟩ := UpperTheory.ConvolutionTheory.Loc.placeDown F E σ hσ v w hw n mE mF hE hF
  refine ⟨ρ, hρ, fun φ ha hs => ?_⟩
  obtain ⟨f, hb, hm⟩ := h φ ha hs
  exact ⟨f, hb, @(UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).2 i1 i2 i3 i4 mE mF hE hF h1 h2 _ _ _ hm⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.AtDown =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SbInv =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SbInv", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\npublic import Mathlib.Topology.Algebra.ClopenNhdofOne\nimport Mathlib.Topology.Separation.Connected\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open GlobalTheory.SplitWeil

theorem UpperTheory.ConvolutionTheory.Loc.sbInv :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], ∀ φ ∈ SB G, ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → TotallyDisconnectedSpace G →
      ∃ U : Subgroup G, IsOpen (U : Set G) ∧ U ≤ K ∧ ∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g := by
  intro G _ _ _ φ hφ K hKo hKc hG
  obtain ⟨hl, hc⟩ := hφ
  have key : ∀ ψ : G × G → G, Continuous ψ → (∀ g, ψ (1, g) = g) → ∀ᶠ u in nhds (1 : G), ∀ g ∈ tsupport φ, φ (ψ (u, g)) = φ g := by
    intro ψ hψ h1
    apply IsCompact.eventually_forall_of_forall_eventually hc
    intro g _
    have a := (hl.comp_continuous hψ).eventually_eq (1, g)
    have b := (hl.comp_continuous continuous_snd).eventually_eq ((1 : G), g)
    filter_upwards [a, b] with z ha hb
    simp only [Function.comp, h1] at ha hb
    rw [ha, hb]
  have a := key (fun p => p.1 * p.2) (by fun_prop) (by simp)
  have b := key (fun p => p.2 * p.1) (by fun_prop) (by simp)
  obtain ⟨W, hW, hWo, hW1⟩ := mem_nhds_iff.1 (a.and b)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := K) (U := Subtype.val ⁻¹' W) (hWo.preimage continuous_subtype_val) hW1
  have hU : ∀ u ∈ N.toSubgroup.map K.subtype, u ∈ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hN hx
  refine ⟨N.toSubgroup.map K.subtype, ?_, Subgroup.map_subtype_le _, fun u hu g => ⟨?_, ?_⟩⟩
  · exact hKo.isOpenMap_subtype_val _ N.isOpen
  · by_cases h : g ∈ tsupport φ
    · exact (hW (hU u hu)).1 g h
    · by_cases h' : u * g ∈ tsupport φ
      · have := (hW (hU _ (inv_mem hu))).1 _ h'
        simpa using this.symm
      · rw [image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']
  · by_cases h : g ∈ tsupport φ
    · exact (hW (hU u hu)).2 g h
    · by_cases h' : g * u ∈ tsupport φ
      · have := (hW (hU _ (inv_mem hu))).2 _ h'
        simpa using this.symm
      · rw [image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SbInv =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.InertData =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.InertData", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.HoweType\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.AtDown\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SbInv\nimport Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ValuationNatCastLeOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected\nimport Mathlib.Topology.Separation.Connected\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal\nimport Mathlib.Topology.Connected.Separation\nimport Mathlib.Topology.MetricSpace.Ultra.TotallySeparated\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Filter
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.Loc GlobalTheory.SplitWeil
open Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped ComplexConjugate

private theorem lc_ind {G : Type} [TopologicalSpace G] {U : Set G} (hU : IsClopen U) {h : G → ℂ}
    (hh : IsLocallyConstant h) : IsLocallyConstant (U.indicator h) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  by_cases hx : x ∈ U
  · filter_upwards [hU.isOpen.mem_nhds hx, hh.eventually_eq x] with y hy e
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, e]
  · filter_upwards [hU.compl.isOpen.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem td_gl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    TotallyDisconnectedSpace (GL (Fin n) k) := by
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem cmp_homeo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) {v : HeightOneSpectrum (𝓞 F)}
    (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w) :
    ∃ e : GL (Fin n) (CompletionsOver E v) ≃ₜ GL (Fin n) (w.1.adicCompletion E), ∀ g, e g = UpperTheory.ConvolutionTheory.GM.cmp w g := by
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  let r : CompletionsOver E v ≃+* w.1.adicCompletion E :=
    RingEquiv.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)
  have hr : Continuous r := continuous_apply _
  have hs : Continuous r.symm :=
    (Homeomorph.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)).symm.continuous
  refine ⟨{ toEquiv := (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin n) r).toMulEquiv).toEquiv
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun g => ?_⟩
  · exact Continuous.units_map _ (continuous_id.matrix_map hr)
  · exact Continuous.units_map _ (continuous_id.matrix_map hs)
  · exact Units.ext (Matrix.ext fun i j => rfl)

theorem UpperTheory.ConvolutionTheory.T.inertData :
    UpperTheory.ConvolutionTheory.T.InertData := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hns
  obtain ⟨-, -, hne, huniq, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨w⟩ := hne v
  have hw : ∀ w' : PlacesOver E v, w' = w := huniq v hns w
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  obtain ⟨ρ, hρ, hdown⟩ := UpperTheory.ConvolutionTheory.Loc.atDown F E σ hσ v w hw n
  have hN : ball n ρ ∈ nhds (1 : Gw n w.1) :=
    (UpperTheory.ConvolutionTheory.Loc.BallG.isOpen_ball hρ.ne').mem_nhds (fun i j => by simp)
  obtain ⟨J, χ, hCO, hchr, hJN, hrank, hne0, hst⟩ := UpperTheory.ConvolutionTheory.T.howeType F E σ hσ hp n hn μ V hV v w hw _ hN
  haveI : T2Space (Gw n w.1) := (UpperTheory.V.Z.Tf.Orb.gLTop (w.1.adicCompletion E) n).2.2.1
  haveI : T2Space (Gw n v) := (UpperTheory.V.Z.Tf.Orb.gLTop (v.adicCompletion F) n).2.2.1
  have hJc : IsClopen (J : Set (Gw n w.1)) := ⟨hCO.1.isClosed, hCO.2⟩
  let φ : Gw n w.1 → ℂ := (J : Set (Gw n w.1)).indicator fun x => conj (χ x)
  have hφl : IsLocallyConstant φ := lc_ind hJc (hchr.1.comp fun z => conj z)
  have hφc : HasCompactSupport φ := HasCompactSupport.intro hCO.1 fun x hx => Set.indicator_of_notMem hx _
  have hφS : φ ∈ SB (GL (Fin n) (w.1.adicCompletion E)) := ⟨hφl, hφc⟩
  have hsupp : Function.support φ ⊆ ball n ρ := fun x hx => hJN (Set.mem_of_indicator_ne_zero hx)
  obtain ⟨f, hfS, hmatch⟩ := hdown φ hφS hsupp
  obtain ⟨e, he⟩ := cmp_homeo (F := F) n w hw
  have hec : (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) = φ ∘ e := funext fun g => by simp [he]
  have hTE : Test (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) := by
    rw [hec]
    exact ⟨hφl.comp_continuous e.continuous, hφc.comp_homeomorph e⟩
  have hTF : Test f := hfS
  obtain ⟨U₁, hU₁o, hU₁K, hU₁⟩ := UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n w.1) φ hφS (GLnLocal.integralGL (w.1.adicCompletion E) n)
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)
  obtain ⟨U₂, hU₂o, hU₂K, hU₂⟩ := UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n v) f hfS (GLnLocal.integralGL (v.adicCompletion F) n)
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)
  let J' : ∀ u : PlacesOver E v, Subgroup (Gw n u.1) := fun u => (hw u).symm ▸ J
  let χ' : ∀ u : PlacesOver E v, Gw n u.1 → ℂ := fun u => (hw u).symm ▸ χ
  have all : ∀ P : PlacesOver E v → Prop, P w → ∀ u, P u := fun P h u => (hw u).symm ▸ h
  have hprod : (UpperTheory.ConvolutionTheory.GM.prodFn fun u : PlacesOver E v => (J' u : Set (Gw n u.1)).indicator fun x => conj (χ' u x)) =
      fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g) := funext fun g => by
    unfold UpperTheory.ConvolutionTheory.GM.prodFn
    exact finprod_unique (fun u : PlacesOver E v =>
      (J' u : Set (Gw n u.1)).indicator (fun x => conj (χ' u x)) (UpperTheory.ConvolutionTheory.GM.cmp u g))
  refine ⟨J', χ', f, U₁.comap (UpperTheory.ConvolutionTheory.GM.cmp w), U₂, ?_, ?_, by rw [hprod]; exact hmatch, by rw [hprod]; exact hTE, hTF, ?_, ?_, hU₂o, hU₂K, ?_, ?_⟩
  · exact all _ ⟨hCO, hchr, hrank, hne0⟩
  · intro x hx
    have hxw : UpperTheory.ConvolutionTheory.GM.cmp w x ∈ J := hx w
    obtain ⟨h1, h2⟩ := hst x hxw
    refine ⟨all _ h1, ?_⟩
    rw [finprod_unique, finprod_unique]
    exact h2
  · have : (UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) = e := funext fun g => (he g).symm
    change IsOpen ((UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) ⁻¹' (U₁ : Set (Gw n w.1)))
    rw [this]
    exact hU₁o.preimage e.continuous
  · intro g hg u
    have hu := hw u
    subst hu
    exact hU₁K hg
  · intro y hy g
    rw [hprod]
    change φ (UpperTheory.ConvolutionTheory.GM.cmp w (y * g)) = φ (UpperTheory.ConvolutionTheory.GM.cmp w g)
    rw [map_mul]
    exact (hU₁ _ hy _).1
  · intro y hy g
    exact (hU₂ y hy g).1
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.InertData =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitLev =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitLev", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor\npublic import Development.WeilBound.CuspidalAdmissibility.OccursIff\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal\nimport Mathlib.Topology.Connected.Separation\nimport Mathlib.Topology.MetricSpace.Ultra.TotallySeparated\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

private theorem mem_fixL' {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (Gw n w)) (x : LL μ) (h : ∀ g ∈ J, rhoL μ w g x = x) : x ∈ fixL μ w J := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]
  rintro _ ⟨g, hg, rfl⟩
  exact h g hg

private theorem exists_fixed {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (w : Pl K) :
    ∃ (S : Subgroup (Gw n w)) (x : LL μ), IsOpen (S : Set (Gw n w)) ∧ x ∈ V ∧ x ≠ 0 ∧ ∀ g ∈ S, rhoL μ w g x = x := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  obtain ⟨⟨σ, f, hf0, hfV, hfe⟩, -, -⟩ := _root_.PositivityTheory.TfC.OccursBasics_holds K n μ V w (Measure.haar) hV
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! hc
    exact hf0 (LinearMap.ext hc)
  refine ⟨{ carrier := {g | σ.ρ g x = x}
            mul_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq] at ha hb ⊢
              rw [map_mul, Module.End.mul_apply, hb, ha]
            one_mem' := by simp
            inv_mem' := fun {a} ha => by
              simp only [Set.mem_setOf_eq] at ha ⊢
              conv_lhs => rw [← ha]
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] },
    f x, σ.smooth x, hfV x, hx, fun g hg => ?_⟩
  rw [← hfe g x]
  exact congrArg f hg

theorem splitLev : SplitLev := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hv
  choose S x hSo hxV hx0 hxS using fun u : PlacesOver E v => exists_fixed μ V hV u.1
  have hsp := fun u : PlacesOver E v => (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hv u) n).1
  choose e he using hsp
  let U : Subgroup (Gw n v) := GLnLocal.integralGL (v.adicCompletion F) n ⊓
    ⨅ u : PlacesOver E v, (S u).comap (mapGL n (completionMap v u.1))
  have hUo : IsOpen (U : Set (Gw n v)) := by
    have h2 : IsOpen (⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1))) := by
      refine isOpen_iInter_of_finite fun u => ?_
      have : (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)) = (e u) ⁻¹' (S u : Set (Gw n u.1)) := by
        ext g; simp only [Set.mem_preimage, he]
      rw [this]
      exact (hSo u).preimage (e u).continuous
    have h3 : (U : Set (Gw n v)) = (GLnLocal.integralGL (v.adicCompletion F) n : Set (Gw n v)) ∩
        ⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)) := by
      ext g
      simp [U]
    rw [h3]
    exact (GLnLocal.isOpen_integralGL _ n).inter h2
  have hUle : U ≤ GLnLocal.integralGL (v.adicCompletion F) n := inf_le_left
  have hUc : IsCompact (U : Set (Gw n v)) :=
    (GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo) hUle
  have hinj : ∀ u : PlacesOver E v, Function.Injective (mapGL n (completionMap v u.1)) := fun u a b h =>
    (e u).injective (by rw [he, he, h])
  refine ⟨U, fun u => U.map (mapGL n (completionMap v u.1)), ⟨hUc, hUo⟩, hUle, fun u => ?_⟩
  have himg : ((U.map (mapGL n (completionMap v u.1)) : Subgroup (Gw n u.1)) : Set (Gw n u.1)) = (e u) '' (U : Set (Gw n v)) := by
    ext y
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, he]
  refine ⟨⟨?_, ?_⟩, fun g => ?_, ?_⟩
  · rw [himg]
    exact hUc.image (e u).continuous
  · rw [himg]
    exact (e u).toHomeomorph.isOpenMap _ hUo
  · exact (Subgroup.mem_map_iff_mem (hinj u)).symm
  · intro hbot
    have hmem : x u ∈ V ⊓ fixL μ u.1 (U.map (mapGL n (completionMap v u.1))) := by
      refine ⟨hxV u, mem_fixL' μ u.1 _ _ ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      exact hxS u _ ((Subgroup.mem_iInf.1 hg.2) u)
    rw [hbot, Submodule.mem_bot] at hmem
    exact hx0 u hmem

end UpperTheory.ConvolutionTheory.T
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitLev =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyExOf =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyExOf", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T


theorem tyEx_of (hLev : SplitLev) (hSt : SplitStable) (hMa : SplitMatch) (hIn : InertData) (hOff : OffStable)
    (hTyp : TypedEx) (hEig : EigBasic) : TyEx := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV q w₀ hq S hqS hunr hsph mk
  have h1 : ∀ {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G), IsChr J 1 := fun J =>
    ⟨IsLocallyConstant.const 1, fun _ _ => norm_one, fun _ _ _ _ => (mul_one _).symm⟩
  have hu : ∀ (v : Pl F) (u : PlacesOver E v), u.1.under (𝓞 F) = v := fun v u => HeightOneSpectrum.ext u.2.over.symm
  have key : ∀ v : Pl F, ∃ (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (χ : ∀ u : PlacesOver E v, Gw n u.1 → ℂ)
      (c : ℂ) (f₀ : Gw n v → ℂ) (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)),
      (∀ u, CO (J u) ∧ IsChr (J u) (χ u) ∧ V ⊓ eigL μ u.1 (J u) (χ u) ≠ ⊥) ∧
      (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → (∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u) ∧
          ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u (mapGL n (galFin σ v) x)) = ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u x)) ∧
      (GM.Split E v → ∀ u, χ u = 1) ∧
      (v ∉ S → v ≠ q → (∀ u, J u = GLnLocal.integralGL (u.1.adicCompletion E) n ∧ χ u = 1) ∧
        (UE : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v ∧ UF = GLnLocal.integralGL (v.adicCompletion F) n) ∧
      (v = q → (∀ u, J u = GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
        (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
        UF = GLnLocal.iwahori (v.adicCompletion F) n) ∧
      (v ∈ S → IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧
        (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v ∧ IsOpen (UF : Set (Gw n v)) ∧
        UF ≤ GLnLocal.integralGL (v.adicCompletion F) n) ∧
      (v ∈ S → ¬ GM.Split E v → (∀ u, RankOne μ V u.1 (J u) (χ u)) ∧
        GM.MatchAt σ v c (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) f₀ ∧
        Test (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) ∧ Test f₀ ∧
        (∀ y ∈ UE, ∀ g, (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) (y * g) =
          (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) g) ∧
        ∀ y ∈ UF, ∀ g, f₀ (y * g) = f₀ g) ∧
      (v ∈ S → GM.Split E v → (∀ g, g ∈ UF ↔ mapGL n (completionMap v (mk v).1) g ∈ J (mk v)) ∧
        (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ J u) ∧
        ∀ ψ : Gw n (mk v).1 → ℂ, Test ψ → (∀ u ∈ J (mk v), ∀ g, ψ (u * g) = ψ g ∧ ψ (g * u) = ψ g) →
        GM.MatchAt σ v c
          (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ))
          (fun g => ψ (mapGL n (completionMap v (mk v).1) g)) ∧
        Test (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ)) ∧
        Test (fun g => ψ (mapGL n (completionMap v (mk v).1) g)) ∧
        (∀ y : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u y ∈ J u) → ∀ g,
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ) (y * g) =
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) ψ) g) ∧
        ∀ y ∈ UF, ∀ g, ψ (mapGL n (completionMap v (mk v).1) (y * g)) = ψ (mapGL n (completionMap v (mk v).1) g)) := by
    intro v
    obtain ⟨o1, o2, ⟨U1, o3⟩, ⟨U2, o4⟩, o5⟩ := hOff F E σ hσ hp n hn v
    by_cases hvS : v ∈ S
    · have hvq : v ≠ q := fun h => hqS (h ▸ hvS)
      by_cases hv : GM.Split E v
      · obtain ⟨U, J, hU, hUle, hJ⟩ := hLev F E σ hσ hp n hn μ V hV v hv
        obtain ⟨s1, s2⟩ := hSt F E σ hσ hp n hn v hv U J fun u => (hJ u).2.1
        obtain ⟨UE, e1, e2, e3⟩ := s2 hU hUle
        obtain ⟨c, hc⟩ := hMa F E σ hσ hp n hn v (mk v) hv U J hU fun u => ⟨(hJ u).1, (hJ u).2.1⟩
        refine ⟨J, fun _ => 1, c, 0, UE, U, fun u => ⟨(hJ u).1, h1 _, ?_⟩, fun x hx => ⟨s1 x hx, rfl⟩, fun _ _ => rfl,
          fun h => absurd hvS h, fun h => absurd h hvq, fun _ => ⟨e2, e3, hU.2, hUle⟩, fun _ h => absurd hv h,
          fun _ _ => ⟨(hJ _).2.1, e1, hc⟩⟩
        rw [(hEig E n μ u.1 _ _ (hJ u).1 (h1 _)).2.1]; exact (hJ u).2.2
      · obtain ⟨J, χ, f, UE, UF, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hIn F E σ hσ hp n hn μ V hV v hv
        exact ⟨J, χ, 1, f, UE, UF, fun u => ⟨(i1 u).1, (i1 u).2.1, (i1 u).2.2.2⟩, i2, fun h => absurd h hv,
          fun h => absurd hvS h, fun h => absurd h hvq, fun _ => ⟨i6, i7, i8, i9⟩,
          fun _ _ => ⟨fun u => (i1 u).2.2.1, i3, i4, i5, i10, i11⟩, fun _ h => absurd h hv⟩
    · have hs : ∀ u : PlacesOver E v, V ⊓ fixL μ u.1 (GLnLocal.integralGL (u.1.adicCompletion E) n) ≠ ⊥ := fun u =>
        hsph u.1 (by rw [show u.1.under (𝓞 F) = v from hu v u]; exact hvS)
      by_cases hvq : v = q
      · refine ⟨fun u => GLnLocal.iwahori (u.1.adicCompletion E) n, fun _ => 1, 0, 0, U2, GLnLocal.iwahori (v.adicCompletion F) n,
          fun u => ⟨(o5 u.1).2.1, h1 _, ?_⟩, fun x hx => ⟨o2 x hx, rfl⟩, fun _ _ => rfl, fun _ h => absurd hvq h,
          fun _ => ⟨fun _ => rfl, o4, rfl⟩, fun h => absurd h hvS, fun h => absurd h hvS, fun h => absurd h hvS⟩
        rw [(hEig E n μ u.1 _ _ (o5 u.1).2.1 (h1 _)).2.1]
        refine fun h => hs u (eq_bot_iff.2 (h ▸ inf_le_inf_left _ ?_))
        exact biInf_mono fun y hy => Subgroup.map_mono (o5 u.1).2.2 hy
      · refine ⟨fun u => GLnLocal.integralGL (u.1.adicCompletion E) n, fun _ => 1, 0, 0, U1,
          GLnLocal.integralGL (v.adicCompletion F) n, fun u => ⟨(o5 u.1).1, h1 _, ?_⟩, fun x hx => ⟨o1 x hx, rfl⟩,
          fun _ _ => rfl, fun _ _ => ⟨fun _ => ⟨rfl, rfl⟩, o3, rfl⟩, fun h => absurd h hvq,
          fun h => absurd h hvS, fun h => absurd h hvS, fun h => absurd h hvS⟩
        rw [(hEig E n μ u.1 _ _ (o5 u.1).1 (h1 _)).2.1]; exact hs u
  choose J χ c f₀ UE UF k1 k2 k3 k4 k5 k6 k7 k8 using key
  let J' : ∀ w : Pl E, Subgroup (Gw n w) := fun w => J (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  let χ' : ∀ w : Pl E, Gw n w → ℂ := fun w => χ (w.under (𝓞 F)) ⟨w, ⟨rfl⟩⟩
  have eJ : ∀ v (u : PlacesOver E v), J' u.1 = J v u := by rintro v ⟨w, hw⟩; obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩; rfl
  have eχ : ∀ v (u : PlacesOver E v), χ' u.1 = χ v u := by rintro v ⟨w, hw⟩; obtain rfl : w.under (𝓞 F) = v := hu v ⟨w, hw⟩; rfl
  let T : Ty σ n q w₀ :=
    { S := S, q_not := hqS, J := J', χ := χ', mk' := mk
      co := fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).1
      chr := fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).2.1
      off := fun w a b => (k4 _ a b).1 ⟨w, ⟨rfl⟩⟩
      at_q := fun w => (eJ q w).trans ((k5 q rfl).1 w)
      triv := fun v hv w => (eχ v w).trans (k3 v hv w)
      stable := fun v x hx => by simp only [eJ, eχ] at hx ⊢; exact k2 v x hx }
  have hsp : ∀ v, v ∈ T.sp ↔ v ∈ S ∧ GM.Split E v := fun v => Finset.mem_filter
  refine ⟨T, rfl, rfl, hTyp E n μ V hV J' χ' (fun w => ⟨T.co w, T.chr w⟩) ?_ (fun w => (k1 _ ⟨w, ⟨rfl⟩⟩).2.2),
    fun v hv hn u => ?_, c, f₀, UF, fun v hv g => ?_, fun ψ hψ => ?_⟩
  · have hf : {w : Pl E | w.under (𝓞 F) ∈ insert q S}.Finite := by
      refine ((insert q S).finite_toSet.biUnion fun v _ => Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_
      exact Set.mem_biUnion hw ⟨⟨w, ⟨rfl⟩⟩, rfl⟩
    refine Filter.mem_of_superset hf.compl_mem_cofinite fun w hw => ?_
    have hw' : w.under (𝓞 F) ∉ insert q S := hw
    rw [Finset.mem_insert, not_or] at hw'
    exact T.off w hw'.2 hw'.1
  · change RankOne μ V u.1 (J' u.1) (χ' u.1)
    rw [eJ, eχ]; exact (k7 v hv hn).1 u
  · change _ ↔ _ ∈ J' (mk v).1
    rw [eJ]; exact (k8 v ((hsp v).1 hv).1 ((hsp v).1 hv).2).1 g
  · have hψ' : ∀ v ∈ S, GM.Split E v → _ := fun v a b => (k8 v a b).2.2 (ψ v) (hψ v ((hsp v).2 ⟨a, b⟩)).1 (by
      have := (hψ v ((hsp v).2 ⟨a, b⟩)).2
      change ∀ u ∈ J' (mk v).1, _ at this
      rw [eJ] at this; exact this)
    let φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ := fun v =>
      if v ∈ S then (if GM.Split E v then GM.prodFn (Function.update
          (fun u : PlacesOver E v => ((J v u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (mk v) (ψ v))
        else GM.prodFn fun u : PlacesOver E v => (J v u : Set (Gw n u.1)).indicator fun x => conj (χ v u x))
      else if h : v = q then GM.iwFn (h ▸ w₀) 0 else (unitSet E n v).indicator 1
    let f : ∀ v : Pl F, Gw n v → ℂ := fun v =>
      if v ∈ S then (if GM.Split E v then fun g => ψ v (mapGL n (completionMap v (mk v).1) g) else f₀ v)
      else if v = q then (GM.iwCoset v 0).indicator 1 else (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1
    let L : GM.Loc σ n q w₀ :=
      { S := S, q_not := hqS, unr := hunr, φ := φ, f := f, c := c, UE := UE, UF := UF
        test := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, ite_eq_left hv, ite_eq_left b]
            exact ⟨(hψ' v hv b).2.1.1, (hψ' v hv b).2.1.2, (hψ' v hv b).2.2.1.1, (hψ' v hv b).2.2.1.2⟩
          · simp only [φ, f, ite_eq_left hv, ite_eq_right b]
            exact ⟨(k7 v hv b).2.2.1.1, (k7 v hv b).2.2.1.2, (k7 v hv b).2.2.2.1.1, (k7 v hv b).2.2.2.1.2⟩
        lev := k6
        inv := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, ite_eq_left hv, ite_eq_left b]
            exact ⟨fun y hy => (hψ' v hv b).2.2.2.1 y (((k8 v hv b).2.1 y).1 hy), (hψ' v hv b).2.2.2.2⟩
          · simp only [φ, f, ite_eq_left hv, ite_eq_right b]
            exact (k7 v hv b).2.2.2.2
        mat := fun v hv => by
          by_cases b : GM.Split E v
          · simp only [φ, f, ite_eq_left hv, ite_eq_left b]
            exact (hψ' v hv b).1
          · simp only [φ, f, ite_eq_left hv, ite_eq_right b]
            exact (k7 v hv b).2.1
        at_q := ⟨by simp only [φ, ite_eq_right hqS, dite_eq_left], by simp only [f, ite_eq_right hqS, ite_eq_left], (k5 q rfl).2⟩
        off := fun v a b => ⟨by simp only [φ, ite_eq_right a, dite_eq_right b], by simp only [f, ite_eq_right a, ite_eq_right b], (k4 v a b).2⟩ }
    refine ⟨L, ⟨rfl, hψ, fun v hv => ?_, fun v a b => ?_⟩, fun _ _ => ⟨rfl, rfl⟩, fun v hv => ?_, fun v a b => ?_⟩
    · obtain ⟨a, b⟩ := (hsp v).1 hv
      change φ v = GM.prodFn (Function.update (fun u : PlacesOver E v => ((J' u.1 : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ))
        (mk v) (ψ v)) ∧ ∀ g, g ∈ UE v ↔ ∀ u, GM.cmp u g ∈ J' u.1
      simp only [eJ, φ, ite_eq_left a, ite_eq_left b, true_and]
      exact (k8 v a b).2.1
    · change φ v = GM.prodFn fun u : PlacesOver E v => (J' u.1 : Set (Gw n u.1)).indicator fun x => conj (χ' u.1 x)
      have a' : v ∈ S := a
      simp only [eJ, eχ, φ, ite_eq_left a', ite_eq_right b]
    · obtain ⟨a, b⟩ := (hsp v).1 hv
      change f v = _
      simp only [f, ite_eq_left a, ite_eq_left b]
      rfl
    · change f v = _
      simp only [f, ite_eq_left a, ite_eq_right b]

end UpperTheory.ConvolutionTheory.T
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyExOf =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyEx =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyEx", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TypedEx\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.InertData\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.OffStable\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitLev\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitMatch\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStableAlt\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyExOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T in
theorem UpperTheory.ConvolutionTheory.T.tyEx :
    UpperTheory.ConvolutionTheory.T.TyEx :=
  tyEx_of splitLev splitStable splitMatch inertData offStable L1.typedEx L1.eigBasic
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyEx =====
