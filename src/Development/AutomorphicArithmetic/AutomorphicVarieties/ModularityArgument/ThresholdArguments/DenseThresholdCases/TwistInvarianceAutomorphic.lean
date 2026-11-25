module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharAlgebraicOfSign
import all Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistRealSelfDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RChar2

@[expose] public section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
section Real
variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]
private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))
private theorem expo_intR {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (v : InfinitePlace E) :
    ∃ k : ℤ, TR.expo χ v = k := by
  apply _root_.expo_intR <;> assumption
end Real
private theorem expo_intC {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {χ : HChar E} {n : (E →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (τ : E →+* ℂ) : expo χ τ = n τ := by
  refine (GlobalTheory.CuspRep.InfType.expo_of_infType E χ).1 n (fun k => h k fun φ => ?_) τ
  exact absurd (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_ofReal (φ x))))
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (Complex.ofRealHom.comp φ))))
private theorem sys_twist {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {R : G K Ω →* GL (Fin n) (Qbar l)}
    {sat sat' : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop} (hA : AttachedSys ι R sat) {art : Ideles K →* Gab K Ω}
    {κ : HChar K} {m : (K →+* ℂ) → ℤ} {μ : G K Ω →* (Qbar l)ˣ} (ha : IsGlobalArtin art) (h : IsLAdicOf art ι κ m μ)
    (hs : ∀ w B, sat w B → κ.UnrAt w → sat' w (B.map (· * κ.val w))) : AttachedSys ι (tw R μ) sat' := by
  apply _root_.sys_twist <;> assumption
private theorem reg_shift {n : ℕ} {m : Multiset ℂ} (h2 : m.Nodup) (h3 : ∀ z ∈ m, ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2)
    {s : ℂ} (hs : ∃ k : ℤ, s = k) :
    (m.map (· + s)).Nodup ∧ ∀ z ∈ m.map (· + s), ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2 := by
  obtain ⟨j, rfl⟩ := hs
  refine ⟨h2.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := h3 y hy
  exact ⟨k + j, by push_cast; ring⟩
theorem UpperTheory.V.Af.twist_invariance_automorphic :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.Twi := by
  rintro - F Ω _ _ _ _ _ l _ ι n r κ ⟨sat, inf, hc, hr, hA⟩ ⟨χ, -, art, a, ha, hχ, hL⟩
  rcases hc with ⟨_, π, rfl, rfl⟩ | ⟨_, π, rfl, rfl⟩
  · refine ⟨_, _, Or.inl ⟨inferInstance, π.twist χ, rfl, rfl⟩, fun τ => ?_,
      UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hA art χ a κ ha hL⟩
    obtain ⟨m, h1, h2, h3⟩ := hr τ
    exact ⟨_, h1.twist χ, reg_shift h2 h3 ⟨_, expo_intC hχ τ⟩⟩
  · refine ⟨_, _, Or.inr ⟨inferInstance, π.twist χ, rfl, rfl⟩, fun τ => ?_,
      sys_twist hA ha hL fun w B hB hu => hB.twist hu⟩
    obtain ⟨m, h1, h2, h3⟩ := hr τ
    exact ⟨_, h1.twist χ, reg_shift h2 h3 (expo_intR hχ _)⟩
end
