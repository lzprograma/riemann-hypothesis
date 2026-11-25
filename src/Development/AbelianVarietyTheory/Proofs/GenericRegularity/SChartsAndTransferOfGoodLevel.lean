module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CombinedBoundAtTrivialValuationsOfCharts
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RegModelC
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NoCommonZeroOfFiniteValues
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralityTrivialValuationsOfNormalAffineCharts, Development.AbelianVarietyTheory.Proofs.GenericRegularity.RegularAtCentre, Development.AbelianVarietyTheory.Proofs.GenericRegularity.RegularAtCentreChart, Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferLawOfNormalCharts, Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferBoundsAlgebraicToAllPointsOfModels, Development.AbelianVarietyTheory.Proofs.GenericRegularity.SChartsAndTransferOfGoodLevel

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralityTrivialValuationsOfNormalAffineCharts =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralityTrivialValuationsOfNormalAffineCharts", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.GenericRegularity.CombinedBoundAtTrivialValuationsOfCharts\npublic import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts\npublic import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree\npublic import Formalism.LocalToGlobal.ProjectiveLattices.RegModelC\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.Reg.ChartInt

open IsLocalRing Formalism.L2.PjFree

section Charts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem nonneg_at {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) (j : S.J) (x : S.A j) (hxE : x ∈ S.Eb j)
    (hx0 : x ≠ 0) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra S.O V]
    (φ : S.A j →ₐ[S.O] V) (e : ℕ) (rr : EReal) (hch : ChV φ.toRingHom e (S.ch j F) rr)
    (hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤) :
    0 ≤ rr := by
  obtain ⟨a', s', hs', hfs'⟩ := TrivBound.transfer'' (O := S.O) (S.ch j F) x hx0 (fun V _ _ _ _ _ φ hφx => by
    obtain ⟨ioV, e', hov, -, v, hv, hChV⟩ := S.pts j V φ ⟨x, hxE, hφx⟩
    exact ⟨e', v F, hov.1, hChV a n F hF, h0 v hv⟩) ((maximalIdeal V).comap φ.toRingHom) hqq
  exact TrivBound.chval_nonneg φ.toRingHom e (S.ch j F) rr hch a' s' hfs' hs'

theorem nonneg_at_all_points {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v F := by
  intro v hv
  obtain ⟨j, V, _, _, _, _, φ, ioV, e, hov, ⟨x, hxE, hφx⟩, -, hmap, hChV⟩ := S.cover v hv
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  refine nonneg_at S hF h0 j x hxE hx0 V φ e (v F) (hChV a n F hF) ?_
  rw [sup_eq_left.2 hmap]
  exact (Ideal.IsPrime.ne_top inferInstance)

end Charts

end GlobalTheory.Reg.ChartInt

namespace GlobalTheory

theorem integrality_at_trivial_valuations_of_charts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) → ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR1Quotient Xo c C ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n, ∀ la, (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, 0 ≤ v f) → ∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.trivialClassCondition Xo c) la, 0 ≤ v f := by
  intro E _ _ _ H Dw l Xo c hS C hC
  refine ⟨?_, ?_⟩
  · rintro a n f hf ⟨la, h0⟩ q
    obtain ⟨S, hQ⟩ := (hS la).1
    exact GlobalTheory.Reg.TrivBound.nonneg_triv S hQ (hC a n hf) h0 _ (GlobalTheory.Reg.TrivBound.ordQ_mem_trivSet q)
  · intro a n f hf la h0
    obtain ⟨S, -⟩ := (hS la).1
    exact GlobalTheory.Reg.ChartInt.nonneg_at_all_points S (hC a n hf) h0

end GlobalTheory
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralityTrivialValuationsOfNormalAffineCharts =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.GenericRegularity.RegularAtCentreChart =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.GenericRegularity.RegularAtCentreChart", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.GenericRegularity.CombinedBoundAtTrivialValuationsOfCharts\npublic import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RegularAtCentre\nimport Formalism.LocalToGlobal.ProjectiveLattices.RegModelC\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.Reg.Transfer

open IsLocalRing NumberField IsDedekindDomain Formalism.L2.Pj Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Reg GlobalTheory.Reg.TrivBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem vr_of_over {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (eO e : ℕ) (heO : 0 < eO)
    (he : 0 < e) (y : V) (hy : vV (K' := FractionRing V) V (algebraMap V (FractionRing V) y) * (eO : ℤ) = e) :
    vr e y = 1 / eO := by
  unfold vr
  have hv : ((vV (K' := FractionRing V) V (algebraMap V (FractionRing V) y) : ℤ) : ℝ) * eO = e := by exact_mod_cast hy
  have heOr : (0 : ℝ) < eO := by exact_mod_cast heO
  have her : (0 : ℝ) < e := by exact_mod_cast he
  field_simp
  linarith

theorem combined_place {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {m : ℕ} (ws : Fin m → Rul Xo c) (hF : S.FamW ws)
    {aL nL} (hws : ∀ k, ws k ∈ sec Xo c aL nL)
    {aE nE} {et : Rul Xo c} (het : et ∈ sec Xo c aE nE)
    (nu c' : ℝ) (hc' : 0 ≤ c')
    (hyp : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v et ∧
      (v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu : EReal) + (c' : EReal) * v et)) :
    ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu : EReal) + (c' : EReal) * v et := by
  intro v hv hT
  obtain ⟨kj, hkj⟩ := hF
  obtain ⟨j, V, _, _, _, _, φ, ioV, e, hov, ⟨x, hxE, hφx⟩, hϖv, hmap, hChV⟩ := S.cover v hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  have he : 0 < e := hov.1
  have heO : 0 < S.eO := S.overO.1
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  have hϖ0 : algebraMap S.O V ϖ ≠ 0 := by
    intro h0
    have := hϖv ϖ hϖ
    rw [h0, map_zero, vV_zero', zero_mul] at this
    lia
  obtain ⟨hfw0, hrat, hinv⟩ := hkj j
  obtain ⟨yw, tw, hyw⟩ := hinv x hxE ϖ hϖ
  obtain ⟨ye, te, hye⟩ := S.reg j aE nE et het x hxE ϖ hϖ
  have hP : ∀ k : ℕ, φ ((algebraMap S.O (S.A j) ϖ * x) ^ k) ≠ 0 := fun k => by
    rw [map_pow, map_mul, AlgHom.commutes]; exact pow_ne_zero _ (mul_ne_zero hϖ0 hφx)
  have hWc := hChV aL nL (ws (kj j)) (hws _)
  have hTc := hChV aE nE et het
  obtain ⟨w, hw⟩ := w_fin hWc _ yw hyw hfw0 (hP tw)
  obtain ⟨t, ht⟩ := fin_of_ne_top hT (chval_ne_bot hTc)
  have hye0 : ye ≠ 0 := by
    rintro rfl
    rw [map_zero] at hye
    have hPK : algebraMap (S.A j) (FractionRing (S.A j)) ((algebraMap S.O (S.A j) ϖ * x) ^ te) ≠ 0 := by
      intro h0
      apply hP te
      rw [IsFractionRing.injective (S.A j) (FractionRing (S.A j)) (h0.trans (map_zero _).symm), map_zero]
    have hfe0 : S.ch j et = 0 := (mul_eq_zero.1 hye).resolve_right hPK
    rw [hfe0] at hTc
    exact hT (chval_zero hTc)
  have ht0 : 0 ≤ t := by
    have := ChartInt.nonneg_at_all_points S het (fun v' hv' => (hyp v' hv').1) v hv
    rw [ht] at this
    exact_mod_cast this
  have hκ : vr e (algebraMap S.O V ϖ) = 1 / S.eO := vr_of_over S.eO e heO he _ (hϖv ϖ hϖ)
  have hqq : (maximalIdeal V).comap φ.toRingHom ⊔
      Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤ := by
    rw [sup_eq_left.2 hmap]; exact Ideal.IsPrime.ne_top inferInstance
  have key : ∀ N : ℕ, 0 < N → (N : ℝ) * w ≤
      (⌈(S.eO : ℝ) * N * nu⌉ : ℝ) * (1 / S.eO) + (⌈(N : ℝ) * c'⌉₊ : ℝ) * t := by
    intro N _
    rw [← hκ]
    exact comb_core ϖ S.eO heO (S.ch j (ws (kj j))) (S.ch j et) hfw0 x hx0 ye hye0 te hye yw tw hyw
      nu c' N ⌈(S.eO : ℝ) * N * nu⌉ ⌈(N : ℝ) * c'⌉₊ (Int.le_ceil _) (Nat.le_ceil _)
      (fun V' _ _ _ _ _ φ' hφ'x => by
        obtain ⟨ioV', e', hov', hϖ', v', hv', hch'⟩ := S.pts j V' φ' ⟨x, hxE, hφ'x⟩
        refine ⟨e', v' (ws (kj j)), v' et, hov'.1, hϖ' ϖ hϖ, hch' aL nL _ (hws _),
          hch' aE nE et het, (hyp v' hv').1, fun hT' => ?_⟩
        refine le_trans (le_iInf fun k => ?_) ((hyp v' hv').2 hT')
        obtain ⟨xk, hxk⟩ := hrat k
        have h2 := hch' aL nL (ws k) (hws k)
        rw [hxk] at h2
        exact ratio_ge (hch' aL nL _ (hws _)) h2)
      V φ hφx hϖ0 hqq e w t (hw ▸ hWc) (ht ▸ hTc)
  have hlim := limit_lam w t nu c' S.eO heO ht0 hc' key
  calc (⨅ k, v (ws k)) ≤ v (ws (kj j)) := iInf_le _ _
    _ = (w : EReal) := hw
    _ ≤ ((nu + c' * t : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hlim
    _ = (nu : EReal) + (c' : EReal) * v et := by rw [ht, EReal.coe_add, EReal.coe_mul]

theorem family_place {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {m : ℕ} (ws : Fin m → Rul Xo c) (hF : S.FamW ws)
    {aL nL} (hws : ∀ k, ws k ∈ sec Xo c aL nL) (nu : ℝ)
    (hyp : ∀ v ∈ valSet Xo c (algCls Xo c) la, (⨅ k, v (ws k)) ≤ (nu : EReal)) :
    ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, (⨅ k, v (ws k)) ≤ (nu : EReal) := by
  intro v hv
  obtain ⟨kj, hkj⟩ := hF
  obtain ⟨j, V, _, _, _, _, φ, ioV, e, hov, ⟨x, hxE, hφx⟩, hϖv, hmap, hChV⟩ := S.cover v hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  have he : 0 < e := hov.1
  have heO : 0 < S.eO := S.overO.1
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  have hϖ0 : algebraMap S.O V ϖ ≠ 0 := by
    intro h0
    have := hϖv ϖ hϖ
    rw [h0, map_zero, vV_zero', zero_mul] at this
    lia
  obtain ⟨hfw0, hrat, hinv⟩ := hkj j
  obtain ⟨yw, tw, hyw⟩ := hinv x hxE ϖ hϖ
  have hP : ∀ k : ℕ, φ ((algebraMap S.O (S.A j) ϖ * x) ^ k) ≠ 0 := fun k => by
    rw [map_pow, map_mul, AlgHom.commutes]; exact pow_ne_zero _ (mul_ne_zero hϖ0 hφx)
  have hWc := hChV aL nL (ws (kj j)) (hws _)
  obtain ⟨w, hw⟩ := w_fin hWc _ yw hyw hfw0 (hP tw)
  have hκ : vr e (algebraMap S.O V ϖ) = 1 / S.eO := vr_of_over S.eO e heO he _ (hϖv ϖ hϖ)
  have hqq : (maximalIdeal V).comap φ.toRingHom ⊔
      Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤ := by
    rw [sup_eq_left.2 hmap]; exact Ideal.IsPrime.ne_top inferInstance
  have h1fe : (1 : FractionRing (S.A j)) * algebraMap (S.A j) (FractionRing (S.A j))
      ((algebraMap S.O (S.A j) ϖ * x) ^ 0) = algebraMap (S.A j) (FractionRing (S.A j)) 1 := by
    rw [pow_zero, one_mul]
  have key : ∀ N : ℕ, 0 < N → (N : ℝ) * w ≤
      (⌈(S.eO : ℝ) * N * nu⌉ : ℝ) * (1 / S.eO) + (⌈(N : ℝ) * 0⌉₊ : ℝ) * 0 := by
    intro N _
    rw [← hκ]
    exact comb_core ϖ S.eO heO (S.ch j (ws (kj j))) 1 hfw0 x hx0 1 one_ne_zero 0 h1fe yw tw hyw
      nu 0 N ⌈(S.eO : ℝ) * N * nu⌉ ⌈(N : ℝ) * 0⌉₊ (Int.le_ceil _) (Nat.le_ceil _)
      (fun V' _ _ _ _ _ φ' hφ'x => by
        obtain ⟨ioV', e', hov', hϖ', v', hv', hch'⟩ := S.pts j V' φ' ⟨x, hxE, hφ'x⟩
        refine ⟨e', v' (ws (kj j)), 0, hov'.1, hϖ' ϖ hϖ, hch' aL nL _ (hws _),
          by simpa using chval_fin_one φ'.toRingHom e', le_rfl, fun _ => ?_⟩
        rw [EReal.coe_zero, zero_mul, add_zero]
        refine le_trans (le_iInf fun k => ?_) (hyp v' hv')
        obtain ⟨xk, hxk⟩ := hrat k
        have h2 := hch' aL nL (ws k) (hws k)
        rw [hxk] at h2
        exact ratio_ge (hch' aL nL _ (hws _)) h2)
      V φ hφx hϖ0 hqq e w 0 (hw ▸ hWc) (by simpa using chval_fin_one φ.toRingHom e)
  have hlim := limit_lam w 0 nu 0 S.eO heO le_rfl le_rfl key
  calc (⨅ k, v (ws k)) ≤ v (ws (kj j)) := iInf_le _ _
    _ = (w : EReal) := hw
    _ ≤ (nu : EReal) := EReal.coe_le_coe_iff.2 (by linarith)

end GlobalTheory.Reg.Transfer
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.GenericRegularity.RegularAtCentreChart =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferLawOfNormalCharts =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferLawOfNormalCharts", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts\npublic import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RegularAtCentreChart\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.Transfer

theorem nonempty_place (K : Type) [Field K] [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩⟩

theorem transferLaw_of_normalCharts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.regular₂ Xo c U := by
  intro E _ _ _ H Dw l Xo c h r U
  have hs : ∀ {a n} {f : Rul Xo c}, f ∈ Formalism.L2.PjFree.cusp Xo c U a n → f ∈ sec Xo c a n :=
    fun hf => Formalism.L2.PjFree.cusp_le_sec Xo c U _ _ hf
  obtain ⟨la0⟩ := nonempty_place c.F
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro w F h0
    refine ⟨fun la y' => ?_, fun q => ?_⟩
    · obtain ⟨S, -⟩ := (h la).1
      exact ChartInt.nonneg_at_all_points S (hs F.2) (fun v hv => h0 la ⟨v, hv⟩) y'.1 y'.2
    · obtain ⟨S, hQ⟩ := (h la0).1
      exact TrivBound.nonneg_triv S hQ (hs F.2) (fun v hv => h0 la0 ⟨v, hv⟩) q.1 q.2
  · intro wL wE n ws et nu c' hc' hNZ hyp
    refine ⟨fun la y' => ?_, fun q => ?_⟩
    · obtain ⟨S, hSF, -⟩ := (h la).2 wL.1.1 wL.1.2 n (fun i => (ws i).1) (fun i => hs (ws i).2) hNZ
      exact ⟨ChartInt.nonneg_at_all_points S (hs et.2) (fun v hv => (hyp la ⟨v, hv⟩).1) y'.1 y'.2,
        fun hT => combined_place S _ hSF (fun k => hs (ws k).2) (hs et.2) (nu la) c' hc'
          (fun v hv => hyp la ⟨v, hv⟩) y'.1 y'.2 hT⟩
    · obtain ⟨S, hSF, hQ⟩ := (h la0).2 wL.1.1 wL.1.2 n (fun i => (ws i).1) (fun i => hs (ws i).2) hNZ
      exact ⟨TrivBound.nonneg_triv S hQ (hs et.2) (fun v hv => (hyp la0 ⟨v, hv⟩).1) q.1 q.2,
        fun hT => TrivBound.comb_triv S hQ _ hSF (fun k => hs (ws k).2) (hs et.2) (nu la0) c' hc'
          (fun v hv => hyp la0 ⟨v, hv⟩) q.1 q.2 hT⟩
  · intro a n _ m ws hws hNZ nu hyp la v hv
    obtain ⟨S, hSF, -⟩ := (h la).2 a n m ws (fun i => hs (hws i)) hNZ
    exact family_place S ws hSF (fun i => hs (hws i)) (nu la) (hyp la) v hv

end GlobalTheory.Reg.Transfer
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferLawOfNormalCharts =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferBoundsAlgebraicToAllPointsOfModels =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferBoundsAlgebraicToAllPointsOfModels", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt\npublic import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree\npublic import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree\npublic import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CombinedBoundAtTrivialValuationsOfCharts\npublic import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts\npublic import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsEveryFinitePlace\npublic import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralityTrivialValuationsOfNormalAffineCharts\npublic import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NoCommonZeroOfFiniteValues\npublic import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferLawOfNormalCharts\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem transfer_of_models : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → (∀ la, ModelAt Xo c la) → (∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.regular₂ Xo c U) ∧ ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR1Quotient Xo c C ∧ Formalism.L2.PjFree.RegularityR2Quotient Xo c C := by
  intro hS E _ _ _ H Dw l Xo c hEv hInt hM
  have hN := fun la => _root_.GlobalTheory.Reg.exists_sCharts hS E H Dw l Xo c hEv hInt la (hM la)
  refine ⟨GlobalTheory.Reg.Transfer.transferLaw_of_normalCharts E H Dw l Xo c hN, fun C hC => ⟨?_, ?_⟩⟩
  · exact (_root_.GlobalTheory.integrality_at_trivial_valuations_of_charts E H Dw l Xo c hN C hC).1
  · exact combined_bound_at_trivial_valuations_of_charts E H Dw l Xo c hN
      (fun la a n m ws hws hv => _root_.GlobalTheory.Reg.noCommonZero_of_finite_values hS E H Dw l Xo c hEv la (hM la) a n m ws hws hv) C hC

end GlobalTheory.Reg
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferBoundsAlgebraicToAllPointsOfModels =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.GenericRegularity.SChartsAndTransferOfGoodLevel =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.GenericRegularity.SChartsAndTransferOfGoodLevel", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion\npublic import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional\npublic import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt\npublic import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe\npublic import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt\npublic import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsEveryFinitePlace\npublic import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits\npublic import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree\npublic import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferBoundsAlgebraicToAllPointsOfModels\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem sCharts_and_transfer_of_good_level : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) ∧ (∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.regular₂ Xo c U) ∧ ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR1Quotient Xo c C ∧ Formalism.L2.PjFree.RegularityR2Quotient Xo c C := by
  intro hP hN E _ _ _ H Dw l Xo c hr hg
  classical
  have hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨hE, hI, -⟩ := _root_.GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hM : ∀ la, ModelAt Xo c la := by
    intro la
    have h := modelAt_of_good_level hP E H Dw hr
      (Function.update (fun l' => Classical.choice (hN E H Dw l' hr)) l Xo) l c la (fun p hp _ => hg p hp)
    rwa [Function.update_self] at h
  exact ⟨fun la => _root_.GlobalTheory.Reg.exists_sCharts hT E H Dw l Xo c hE hI la (hM la), _root_.GlobalTheory.Reg.transfer_of_models hT E H Dw l Xo c hE hI hM⟩

end GlobalTheory.Reg
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.GenericRegularity.SChartsAndTransferOfGoodLevel =====
