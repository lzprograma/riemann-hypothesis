module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharAlgebraicOfSign
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
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
private theorem denseRange_diagR : DenseRange (diagR E) := by
  have hc : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (TR.infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc
private theorem chiInf_pos {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (u : (TR.Rinf E)ˣ)
    (hu : ∀ v, 0 < u.val v) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ := by
  apply _root_.chiInf_pos <;> assumption
private theorem expo_intR {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (v : InfinitePlace E) :
    ∃ k : ℤ, TR.expo χ v = k := by
  classical
  refine ⟨∑ φ : E →+* ℂ, if InfinitePlace.mk φ = v then n φ else 0, TR.expo_eq_of_exp χ v _ fun t => ?_⟩
  rw [chiInf_pos h _ fun w => Real.exp_pos _]
  simp only [TR.expU_val, Complex.ofReal_exp, ← Complex.exp_int_mul]
  rw [← Complex.exp_sum, Int.cast_sum, Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun φ _ => ?_)
  split_ifs with e
  · rw [e, Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne e]
end Real
private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)
private theorem sys_twist {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {R : G K Ω →* GL (Fin n) (Qbar l)}
    {sat sat' : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop} (hA : AttachedSys ι R sat) {art : Ideles K →* Gab K Ω}
    {κ : HChar K} {m : (K →+* ℂ) → ℤ} {μ : G K Ω →* (Qbar l)ˣ} (ha : IsGlobalArtin art) (h : IsLAdicOf art ι κ m μ)
    (hs : ∀ w B, sat w B → κ.UnrAt w → sat' w (B.map (· * κ.val w))) : AttachedSys ι (tw R μ) sat' := by
  refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G K Ω) _ n R).2.2 μ hA.1, ?_⟩
  filter_upwards [hA.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified κ), ev_notMem (K := K) l]
    with w ⟨B, hB, hE⟩ hu hl
  refine ⟨_, hs w B hB hu, ?_⟩
  have hc : UpperTheory.V.Af.Bc.CharEig ι μ w (κ.val w : ℂ) := by
    refine fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have h4 := UpperTheory.frobenius_eigenvalues_twist K Ω l ι n R μ w _ _ hE hc
  convert h4 using 1
  simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, mul_assoc]
theorem UpperTheory.V.Sd.twist_real_selfDual :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.TwR := by
  rintro - F Ω _ _ _ _ _ _ l _ ι n r κ ⟨-, art, χ, a, ha, hχ, hL⟩ ⟨π, hr, hA⟩
  exact ⟨π.twist χ, hr.twist (expo_intR hχ), sys_twist hA ha hL fun w B hB hu => hB.twist hu⟩
end
