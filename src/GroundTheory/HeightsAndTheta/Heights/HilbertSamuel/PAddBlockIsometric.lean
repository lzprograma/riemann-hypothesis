module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionPointValue
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockMetric
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Points
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAddBlockIsometric
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue, GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LiftOldChartMonomialMemPrimeCompl, GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAddBlockIsometric

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionPointValue\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\npublic import Mathlib.Topology.Algebra.MvPolynomial\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBounded

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionPointValue

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

abbrev IsRep := @PowerBlockMetric.IsRep
abbrev y_ne_zero := @PowerBlockMetric.y_ne_zero
abbrev cross := @PowerBlockMetric.cross
abbrev exists_rep_at := @PowerBlockMetric.exists_rep_at
abbrev metric_ne := @PowerBlockMetric.metric_ne
abbrev val := @PowerBlockMetric.val
abbrev val_spec := @PowerBlockMetric.val_spec
abbrev val_eq := @PowerBlockMetric.val_eq
abbrev rep_add := @PowerBlockMetric.rep_add

theorem rep_mul {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n m : ℕ} {s t : Ω} {g₁ h₁ g₂ h₂ : MRing ι}
    (r₁ : IsRep y a n s g₁ h₁) (r₂ : IsRep y a m t g₂ h₂) :
    IsRep y a (n + m) (s * t) (g₁ * g₂) (h₁ * h₂) := by
  obtain ⟨dg₁, dh₁, hg₁, hh₁, hd₁, hy₁⟩ := r₁
  obtain ⟨dg₂, dh₂, hg₂, hh₂, hd₂, hy₂⟩ := r₂
  refine ⟨dg₁ + dg₂, dh₁ + dh₂, homog_mul hg₁ hg₂, homog_mul hh₁ hh₂, fun k => ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    linear_combination hd₁ k + hd₂ k
  · rw [map_mul, map_mul, hy₁, hy₂]
    ring

abbrev w := @PowerBlockMetric.w

theorem val_continuousOn {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hA : ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n) :
    ContinuousOn (val y A n s) (mcPts (mCoordIdeal y)) := by
  intro z₀ hz₀
  obtain ⟨⟨g, h⟩, r, hne⟩ := exists_rep_at hs hz₀
  have hcont : ∀ f : MRing ι, Continuous fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) f) :=
    fun f => MvPolynomial.continuous_eval _
  have hAc : ContinuousWithinAt (fun z => (A.h z : ℂ) ^ n) (mcPts (mCoordIdeal y)) z₀ :=
    (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
      ((hA z₀ hz₀.1).mono fun z (hz : z ∈ mcPts (mCoordIdeal y)) => hz.1)).pow n
  have hF : ContinuousWithinAt (fun z => eval z (map (Int.castRingHom ℂ) g) /
      (eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n)) (mcPts (mCoordIdeal y)) z₀ :=
    (hcont g).continuousWithinAt.div ((hcont h).continuousWithinAt.mul hAc)
      (mul_ne_zero hne (metric_ne hz₀ n))
  refine hF.congr_of_eventuallyEq ?_ (val_eq hs hz₀ r hne)
  have hopen : {z | eval z (map (Int.castRingHom ℂ) h) ≠ 0} ∈ nhds z₀ :=
    (isOpen_ne_fun (hcont h) continuous_const).mem_nhds hne
  filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with z hz hz'
  exact val_eq hs hz' r hz

abbrev secNormAt_eq := @PowerBlockMetric.secNormAt_eq

theorem val_mul {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {n m : ℕ} {s t st : Ω} (hs : s ∈ chartLat y A.a n)
    (ht : t ∈ chartLat y A.a m) (hst : st ∈ chartLat y A.a (n + m)) (he : st = s * t)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    val y A (n + m) st z = val y A n s z * val y A m t z := by
  obtain ⟨⟨g₁, h₁⟩, r₁, n₁⟩ := exists_rep_at hs hz
  obtain ⟨⟨g₂, h₂⟩, r₂, n₂⟩ := exists_rep_at ht hz
  have r := rep_mul r₁ r₂
  rw [← he] at r
  dsimp only [val]
  rw [val_eq hst hz r (by simpa using mul_ne_zero n₁ n₂), val_eq hs hz r₁ n₁, val_eq ht hz r₂ n₂]
  simp only [map_mul]
  rw [pow_add]
  ring

theorem exists_chart {y : (Σ k, ι k) → Ω} (hrel : IsRelevant (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  refine ⟨fun k => (hrel k).choose, fun k h0 => (hrel k).choose_spec ?_⟩
  show X _ ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem common_denom {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n r : ℕ} (hrel : IsRelevant (mCoordIdeal y))
    (s : Fin r → Ω) (hs : ∀ i, s i ∈ chartLat y a n) :
    ∃ (e e' : K → ℕ) (h : MRing ι) (g : Fin r → MRing ι),
      IsMultiHomog h e' ∧ (∀ i, IsMultiHomog (g i) e) ∧ (∀ k, (e k : ℤ) = e' k + n * a k) ∧
      aeval y h ≠ 0 ∧ ∀ i, aeval y (g i) = s i * aeval y h := by
  obtain ⟨c, hc⟩ := exists_chart hrel
  choose N δ G hG hdeg hGv using fun i => exists_chartForm y c hc (fun k => (n : ℤ) * a k) (hs i c hc)
  have hN : ∀ i k, N i k ≤ ∑ j, N j k := fun i k =>
    Finset.single_le_sum (f := fun j => N j k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set L : K → ℕ := fun k => ∑ j, N j k + ((n : ℤ) * a k).natAbs with hL
  refine ⟨fun k => ((L k : ℤ) + n * a k).toNat, L, chartMon c L, fun i => G i * chartMon c (L - N i),
    homog_chartMon c L, fun i => homog_congr (homog_mul (hG i) (homog_chartMon c _)) fun k => ?_,
    fun k => ?_, ?_, fun i => ?_⟩
  · have h1 := hdeg i k
    have h2 := hN i k
    simp only [Pi.add_apply, Pi.sub_apply, hL]
    generalize (n : ℤ) * a k = q at *
    generalize ∑ j, N j k = S at *
    omega
  · simp only [hL]
    generalize (n : ℤ) * a k = q
    generalize ∑ j, N j k = S
    omega
  · rw [aeval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  · rw [map_mul, hGv i, aeval_chartMon, aeval_chartMon, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add, Pi.sub_apply]
    congr 1
    have h2 := hN i k
    simp only [hL]
    omega

end SectionPointValue


open SectionPointValue in
theorem SectionPointValue.proof : SectionPointValue.Statement := by
  intro K _ ι _ Ω _ y A hrel hA
  refine ⟨fun n => w y A n, fun n s => val_continuousOn hA s.2, ?_, ?_, ?_, ?_⟩
  · intro n s dg dh g h z hg hh hd hy hz
    exact val_spec s.2 hz ⟨dg, dh, hg, hh, hd, hy⟩
  · intro n s z hz
    exact secNormAt_eq s.2 hz
  · intro n k s t st he z hz
    exact val_mul s.2 t.2 st.2 he hz
  · intro n r s
    exact common_denom hrel (fun i => s i) fun i => (s i).2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LiftOldChartMonomialMemPrimeCompl =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LiftOldChartMonomialMemPrimeCompl", "h": "module\n\npublic import Mathlib.RingTheory.Length\npublic import Mathlib.RingTheory.Localization.AtPrime.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Points\npublic import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SectionCycle

section Local

variable {S : Type*} [CommRing S]

theorem length_localized_eq {J J₁ W : Ideal S} [W.IsPrime] (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J₁)) := by
  let q : (S ⧸ J) →ₗ[S] (S ⧸ J₁) := Submodule.mapQ J J₁ LinearMap.id hJ
  let φ := IsLocalizedModule.map W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J))
    (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J₁)) q
  have hφ : ∀ (x : S) (s : W.primeCompl), φ (LocalizedModule.mk (Submodule.Quotient.mk x) s) =
      LocalizedModule.mk (Submodule.Quotient.mk x) s := by
    intro x s
    rw [IsLocalizedModule.map_LocalizedModules]
    rfl
  have htW : t ∈ W.primeCompl := ht
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y
    refine LocalizedModule.induction_on (fun m s hy ↦ ?_) y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J m
    rw [hφ, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hy
    obtain ⟨u, hu⟩ := hy
    simp only [smul_zero, one_smul] at hu
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul] at hu
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
    refine ⟨⟨t, htW⟩ * u, ?_⟩
    simp only [smul_zero, one_smul]
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul, Submonoid.coe_mul, mul_assoc]
    exact hmul _ hu
  have hsurj : Function.Surjective φ := by
    intro y
    refine LocalizedModule.induction_on (fun m s ↦ ?_) y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J₁ m
    exact ⟨LocalizedModule.mk (Submodule.Quotient.mk x) s, hφ x s⟩
  exact ((LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq

theorem mem_minimalPrimes_iff {J J₁ W : Ideal S} (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) : W ∈ J.minimalPrimes ↔ W ∈ J₁.minimalPrimes := by
  have key : ∀ Q : Ideal S, Q.IsPrime → Q ≤ W → (J ≤ Q ↔ J₁ ≤ Q) := fun Q hQ hQW ↦
    ⟨fun h x hx ↦ (hQ.mem_or_mem (h (hmul x hx))).resolve_left fun htQ ↦ ht (hQW htQ), hJ.trans⟩
  simp only [Ideal.minimalPrimes, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hWp, hJW⟩, hmin⟩
    exact ⟨⟨hWp, (key W hWp le_rfl).mp hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mpr hQ.2⟩ hQW⟩
  · rintro ⟨⟨hWp, hJW⟩, hmin⟩
    exact ⟨⟨hWp, (key W hWp le_rfl).mpr hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mp hQ.2⟩ hQW⟩

end Local

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

end SectionCycle

end

end GroundTheory.Heights₂.Heights
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LiftOldChartMonomialMemPrimeCompl =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAddBlockIsometric =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAddBlockIsometric", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAddBlockIsometric\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded\npublic import Mathlib.RingTheory.RegularLocalRing.Defs\npublic import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing\npublic import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord\npublic import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LiftOldChartMonomialMemPrimeCompl\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBounded SectionPointValue

noncomputable section

set_option linter.unusedSectionVars false

namespace AddBlockIsometric

section Cycle

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_eq_zero_of_not {P W : Ideal (MRing ι)} (f : MRing ι)
    (h : ¬ (W.IsPrime ∧ IsRelevant W ∧ P ≤ W)) : divCycle P f W = 0 := by
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  rw [ite_eq_right]
  intro hW
  simp only [divSupp, Set.mem_ofPred_eq] at hW
  exact h ⟨hW.1.1.1, hW.2, le_sup_left.trans hW.1.1.2⟩

theorem divCycle_apply_eq_of_cross (P : Ideal (MRing ι)) {f g f' g' : MRing ι} {W : Ideal (MRing ι)} [hW : W.IsPrime]
    (hf' : f' ∉ W) (hg' : g' ∉ W) (hrel : f * g' - f' * g ∈ P) : divCycle P f W = divCycle P g W := by
  set J := P ⊔ Ideal.span {f * g'} with hJdef
  have hfg : f * g' ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hIJ : P ≤ J := le_sup_left
  have hf'g : f' * g ∈ J := by
    have h := J.sub_mem hfg (hIJ hrel)
    rwa [sub_sub_cancel] at h
  have h1 : J ≤ P ⊔ Ideal.span {f} := sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
    (Ideal.mem_sup_right (Ideal.mul_mem_right g' _ (Ideal.mem_span_singleton_self f))))
  have h2 : J ≤ P ⊔ Ideal.span {g} := by
    refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    have h := Ideal.add_mem _ (Ideal.mem_sup_left hrel : _ ∈ P ⊔ Ideal.span {g})
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ f' (Ideal.mem_span_singleton_self g)) :
        _ ∈ P ⊔ Ideal.span {g})
    rwa [sub_add_cancel] at h
  have hm1 : ∀ x ∈ P ⊔ Ideal.span {f}, g' * x ∈ J := by
    intro x hx
    obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mul_add, show g' * (r * f) = r * (f * g') by ring]
    exact J.add_mem (hIJ (P.mul_mem_left _ hi)) (J.mul_mem_left _ hfg)
  have hm2 : ∀ x ∈ P ⊔ Ideal.span {g}, f' * x ∈ J := by
    intro x hx
    obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mul_add, show f' * (r * g) = r * (f' * g) by ring]
    exact J.add_mem (hIJ (P.mul_mem_left _ hi)) (J.mul_mem_left _ hf'g)
  have e1 := SectionCycle.mem_minimalPrimes_iff h1 hg' hm1
  have e2 := SectionCycle.mem_minimalPrimes_iff h2 hf' hm2
  have l1 := SectionCycle.length_localized_eq h1 hg' hm1
  have l2 := SectionCycle.length_localized_eq h2 hf' hm2
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  by_cases hc : W ∈ divSupp P f
  · have hc' : W ∈ divSupp P g := by
      simp only [divSupp, Set.mem_ofPred_eq] at hc ⊢
      exact ⟨e2.mp (e1.mpr hc.1), hc.2⟩
    rw [ite_eq_left hc, ite_eq_left hc', multAt, multAt, dite_eq_left hW, dite_eq_left hW]
    exact congrArg ENat.toNat (l1.symm.trans l2)
  · have hc' : W ∉ divSupp P g := by
      intro h
      simp only [divSupp, Set.mem_ofPred_eq] at hc h
      exact hc ⟨e1.mp (e2.mpr h.1), h.2⟩
    rw [ite_eq_right hc, ite_eq_right hc']

theorem divCycle_eq_of_forall_cross (P : Ideal (MRing ι)) {f g : MRing ι}
    (h : ∀ W : Ideal (MRing ι), W.IsPrime → IsRelevant W → P ≤ W →
      ∃ f' g' : MRing ι, f' ∉ W ∧ g' ∉ W ∧ f * g' - f' * g ∈ P) :
    divCycle P f = divCycle P g := by
  ext W
  by_cases hW : W.IsPrime ∧ IsRelevant W ∧ P ≤ W
  · obtain ⟨hp, hr, hle⟩ := hW
    obtain ⟨f', g', hf', hg', hrel⟩ := h W hp hr hle
    exact divCycle_apply_eq_of_cross P hf' hg' hrel
  · rw [divCycle_eq_zero_of_not f hW, divCycle_eq_zero_of_not g hW]

theorem mem_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {F : MRing ι} {d : K → ℕ} (hF : IsMultiHomog F d) :
    F ∈ mCoordIdeal y ↔ aeval y F = 0 := by
  show F ∈ RingHom.ker (mConeMap y) ↔ _
  rw [RingHom.mem_ker]
  erw [mConeMap_homog y hF]
  constructor
  · intro h
    have hM : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)
    exact MvPolynomial.C_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)
  · intro h
    rw [h, map_zero, zero_mul]

end Cycle

section Block

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem extend_some_none {α : Type} [Zero α] (a : K → α) :
    Function.extend (some : K → Option K) a 0 none = 0 :=
  Function.extend_apply' _ _ _ fun ⟨_, h⟩ => Option.some_ne_none _ h

theorem extend_some_some {α : Type} [Zero α] (a : K → α) (k : K) :
    Function.extend (some : K → Option K) a 0 (some k) = a k :=
  (Option.some_injective K).extend_apply a 0 k

theorem rename_mem {N : ℕ} {y : (Σ k, ι k) → Ω} (v : Fin N → Ω) {F : MRing ι} (hF : F ∈ mCoordIdeal y) :
    rename (oldV (ι := ι) N) F ∈ mCoordIdeal (addBlock y v) := by
  show _ ∈ RingHom.ker (mConeMap (addBlock y v))
  rw [RingHom.mem_ker, Targets.ImageCoord.mConeMap_rename some (oldV N) (fun _ => rfl)]
  have h0 : mConeMap (addBlock y v ∘ oldV N) F = 0 := RingHom.mem_ker.mp hF
  rw [h0, map_zero]

theorem aeval_rename_old {N : ℕ} (y : (Σ k, ι k) → Ω) (v : Fin N → Ω) (F : MRing ι) :
    aeval (addBlock y v) (rename (oldV (ι := ι) N) F) = aeval y F := by
  rw [aeval_rename]
  rfl

theorem eval_rename_old {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) (F : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename (oldV (ι := ι) N) F)) = eval (basePart₂ z) (map (Int.castRingHom ℂ) F) := by
  rw [map_rename, eval_rename]
  rfl

theorem not_mem_rename_chartMon {N : ℕ} {W : Ideal (MRing (addIdx ι N))} [hW : W.IsPrime] {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨some k, c k⟩ : MRing (addIdx ι N)) ∉ W) (e : K → ℕ) :
    rename (oldV (ι := ι) N) (chartMon c e) ∉ W := by
  intro h
  rw [chartMon, map_prod] at h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).mp h
  rw [map_pow, rename_X] at hk
  exact hc k (hW.mem_of_pow_mem _ hk)

theorem cross_mem {N : ℕ} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {m : ℕ} {v : Fin N → Ω} {i i' : Fin N}
    {G H G' H' : MRing ι} (r : IsRep y A.a m (v i) G H) (r' : IsRep y A.a m (v i') G' H') :
    (X ⟨none, i⟩ : MRing (addIdx ι N)) * rename (oldV N) H * rename (oldV N) G' -
      X ⟨none, i'⟩ * rename (oldV N) H' * rename (oldV N) G ∈ mCoordIdeal (addBlock y v) := by
  obtain ⟨dg, dh, hg, hh, hd, hy⟩ := r
  obtain ⟨dg', dh', hg', hh', hd', hy'⟩ := r'
  have hb := isBlockMap_oldV (ι := ι) N
  refine (mem_iff _ (homog_sub (homog_mul (homog_mul (homog_X _) (Inter.rename_isMultiHomog hb hh))
    (Inter.rename_isMultiHomog hb hg')) (homog_congr (homog_mul (homog_mul (homog_X _)
      (Inter.rename_isMultiHomog hb hh')) (Inter.rename_isMultiHomog hb hg)) fun k => ?_))).mpr ?_
  · cases k with
    | none => simp only [Pi.add_apply, extend_some_none]
    | some k =>
      simp only [Pi.add_apply, extend_some_some]
      have e1 := hd k
      have e2 := hd' k
      zify
      linarith
  · rw [map_sub, map_mul, map_mul, map_mul, map_mul, aeval_X, aeval_X, aeval_rename_old, aeval_rename_old,
      aeval_rename_old, aeval_rename_old, hy, hy']
    show v i * _ * (v i' * _) - v i' * _ * (v i * _) = 0
    ring

end Block

end AddBlockIsometric


open AddBlockIsometric in
theorem AddBlockIsometric.proof : AddBlockIsometric.Statement := by
  intro K _ _ ι _ Ω _ _ y D A m N v B L hY hm hv hgen hBa hLa hLh hBh
  classical
  have hrel : IsRelevant (mCoordIdeal y) := hY.2.1.2.2
  obtain ⟨c₀, hc₀⟩ := SectionPointValue.exists_chart hrel
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    obtain ⟨u, -, hu⟩ := hgen c₀ hc₀
    simp [h] at hu
  obtain ⟨e₀, δ₀, G₀, hG₀, hδ₀, hG₀v⟩ :=
    exists_chartForm y c₀ hc₀ (fun k => (m : ℤ) * A.a k) (hv j c₀ hc₀)
  have hrep₀ : IsRep y A.a m (v j) G₀ (chartMon c₀ e₀) :=
    ⟨δ₀, e₀, hG₀, homog_chartMon c₀ e₀, fun k => by linear_combination hδ₀ k, by rw [aeval_chartMon]; exact hG₀v⟩
  have hb := isBlockMap_oldV (ι := ι) N
  have hprod₀ : ∏ k, y ⟨k, c₀ k⟩ ^ e₀ k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc₀ k)
  refine ⟨X ⟨none, j⟩ * rename (oldV N) (chartMon c₀ e₀), rename (oldV N) G₀,
    Pi.single none 1 + Function.extend some e₀ 0, Function.extend some δ₀ 0,
    homog_mul (homog_X _) (Inter.rename_isMultiHomog hb (homog_chartMon c₀ e₀)),
    Inter.rename_isMultiHomog hb hG₀, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [mem_iff _ (homog_mul (homog_X _) (Inter.rename_isMultiHomog hb (homog_chartMon c₀ e₀))), map_mul, aeval_X,
      aeval_rename_old, aeval_chartMon]
    exact mul_ne_zero hj hprod₀
  ·
    rw [mem_iff _ (Inter.rename_isMultiHomog hb hG₀), aeval_rename_old, hG₀v]
    exact mul_ne_zero hj hprod₀
  ·
    intro k
    rw [hBa, hLa]
    cases k with
    | none =>
      simp [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, unitDeg]
    | some k =>
      simp only [Pi.add_apply, extend_some_some, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg]
      have := hδ₀ k
      simp [unitDeg]
      linarith
  ·
    refine divCycle_eq_of_forall_cross _ fun W hWp hWr hPW => ?_
    have hWr' : ∀ k : K, ∃ i : ι k, (X ⟨some k, i⟩ : MRing (addIdx ι N)) ∉ W := fun k => hWr (some k)
    choose c hc using hWr'
    obtain ⟨i₀, hi₀⟩ : ∃ i : Fin N, (X ⟨none, i⟩ : MRing (addIdx ι N)) ∉ W := hWr none
    have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
      intro k h0
      apply hc k
      apply hPW
      have hX : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y :=
        (mem_iff y (homog_X _)).mpr (by rw [aeval_X]; exact h0)
      have := rename_mem v hX
      rwa [rename_X] at this
    choose Ns δs Gs hGs hδs hGsv using
      fun i => exists_chartForm y c hyc (fun k => (m : ℤ) * A.a k) (hv i c hyc)
    have hrep : ∀ i, IsRep y A.a m (v i) (Gs i) (chartMon c (Ns i)) := fun i =>
      ⟨δs i, Ns i, hGs i, homog_chartMon c _, fun k => by linear_combination hδs i k,
        by rw [aeval_chartMon]; exact hGsv i⟩
    refine ⟨X ⟨none, i₀⟩ * rename (oldV N) (chartMon c (Ns i₀)), rename (oldV N) (Gs i₀), ?_, ?_, ?_⟩
    · intro h
      rcases hWp.mem_or_mem h with h | h
      · exact hi₀ h
      · exact not_mem_rename_chartMon hc _ h
    · intro hG
      have hall : ∀ i, rename (oldV N) (Gs i) ∈ W := by
        intro i
        have hr := hPW (cross_mem (hrep i₀) (hrep i))
        have h2 : (X ⟨none, i⟩ : MRing (addIdx ι N)) * rename (oldV N) (chartMon c (Ns i)) *
            rename (oldV N) (Gs i₀) ∈ W := W.mul_mem_left _ hG
        have h3 := W.add_mem hr h2
        rw [sub_add_cancel] at h3
        rcases hWp.mem_or_mem h3 with h4 | h4
        · rcases hWp.mem_or_mem h4 with h5 | h5
          · exact absurd h5 hi₀
          · exact absurd h5 (not_mem_rename_chartMon hc _)
        · exact h4
      obtain ⟨u, hu, hsum⟩ := hgen c hyc
      have hsum' : ∑ i, u i * (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) = 1 := hsum
      choose ε U hU hUv using fun i => exists_form_of_mem_chartRingZ y c hyc (hu i)
      obtain ⟨Dt, hle⟩ : ∃ Dt : K → ℕ, ∀ i k, ε i k + δs i k ≤ Dt k :=
        ⟨fun k => ∑ i, (ε i k + δs i k), fun i k =>
          Finset.single_le_sum (f := fun i => ε i k + δs i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)⟩
      have key : ∀ i, (∏ k, y ⟨k, c k⟩ ^ ε i k) * (∏ k, y ⟨k, c k⟩ ^ Ns i k) *
          (∏ k, y ⟨k, c k⟩ ^ (Dt k - (ε i k + δs i k))) =
            (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ Dt k := by
        intro i
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        simp only [← zpow_natCast, ← zpow_add₀ (hyc k)]
        congr 1
        have h1 := hδs i k
        have h2 := hle i k
        push_cast [Nat.cast_sub h2]
        linarith
      have hΦ : (∑ i, U i * Gs i * chartMon c (fun k => Dt k - (ε i k + δs i k))) - chartMon c Dt ∈
          mCoordIdeal y := by
        refine (mem_iff y (homog_sub (homog_sum _ fun i _ => homog_congr (homog_mul (homog_mul (hU i) (hGs i))
          (homog_chartMon c _)) fun k => ?_) (homog_chartMon c Dt))).mpr ?_
        · simp only [Pi.add_apply]
          have := hle i k
          omega

        · rw [map_sub, map_sum, aeval_chartMon, sub_eq_zero]
          calc ∑ i, aeval y (U i * Gs i * chartMon c (fun k => Dt k - (ε i k + δs i k)))
              = ∑ i, u i * (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ Dt k := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [map_mul, map_mul, hUv i, hGsv i, aeval_chartMon]
                calc (u i * ∏ k, y ⟨k, c k⟩ ^ ε i k) * (v i * ∏ k, y ⟨k, c k⟩ ^ Ns i k) *
                      ∏ k, y ⟨k, c k⟩ ^ (Dt k - (ε i k + δs i k))
                    = u i * v i * ((∏ k, y ⟨k, c k⟩ ^ ε i k) * (∏ k, y ⟨k, c k⟩ ^ Ns i k) *
                      (∏ k, y ⟨k, c k⟩ ^ (Dt k - (ε i k + δs i k)))) := by ring
                  _ = _ := by rw [key i]; ring
            _ = ∏ k, y ⟨k, c k⟩ ^ Dt k := by rw [← Finset.sum_mul, hsum', one_mul]
      have hΦW := hPW (rename_mem v hΦ)
      have hS : rename (oldV N) (∑ i, U i * Gs i * chartMon c (fun k => Dt k - (ε i k + δs i k))) ∈ W := by

        rw [map_sum]
        exact W.sum_mem fun i _ => by
          rw [map_mul, map_mul]
          exact W.mul_mem_right _ (W.mul_mem_left _ (hall i))
      have hT := W.sub_mem hS hΦW
      rw [map_sub, sub_sub_cancel] at hT
      exact not_mem_rename_chartMon hc Dt hT
    · exact cross_mem hrep₀ (hrep i₀)
  ·
    intro z hz
    have hzo : basePart₂ z ∈ mcPts (mCoordIdeal y) := by
      refine ⟨fun k => hz.1 (some k), fun F hF => ?_⟩
      have h1 := hz.2 _ (rename_mem v hF)
      rwa [eval_rename_old] at h1
    have hval := val_spec (hv j) hzo hrep₀
    have hsec := secNormAt_eq (hv j) hzo
    have hB := hBh z hz j
    have hA := A.pos _ hzo.1
    rw [hLh z, map_mul, map_mul, eval_rename_old, eval_rename_old, hval, map_X, eval_X]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hA.le, ← hsec,
      ← hB]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAddBlockIsometric =====
