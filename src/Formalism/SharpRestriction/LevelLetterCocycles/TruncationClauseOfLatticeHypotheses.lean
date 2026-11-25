module

public import Formalism.SharpRestriction.LevelLetterCocycles.IsTruncIff
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.HermFlagUnipotentAnisotropicVectorSubMem
public import Formalism.SharpRestriction.LevelLetterCocycles.CompleteOfPow
import Formalism.SharpRestriction.LevelLetterCocycles.JumpsLetOfWin
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.LevelLetterCocycles.EqUniformizerSmulOfLevelOne, Formalism.SharpRestriction.LevelLetterCocycles.TruncationClauseOfLatticeHypotheses

-- ===== clump member: Formalism.SharpRestriction.LevelLetterCocycles.EqUniformizerSmulOfLevelOne =====
-- clump-header: {"m": "Formalism.SharpRestriction.LevelLetterCocycles.EqUniformizerSmulOfLevelOne", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.IsTruncIff\npublic import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup\npublic import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace\npublic import Formalism.SharpRestriction.LevelLetterCocycles.HermFlagUnipotentAnisotropicVectorSubMem\nimport Formalism.SharpRestriction.LevelLetterCocycles.JumpsLetOfWin\nimport Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Classical

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.Relay2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem eq_uniformizer_smul_of_level_one (T : LocLat G Qp LL O) (i : ZMod n) {ζ : W.DD T} (hD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i ζ)
    (h1 : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 ζ) : ∃ z', Formalism.MainNotions.LiftingTheory.InNΔi W T i z' ∧ ζ = W.π₀ • z' := by
  obtain ⟨y, hy, hyΔ, e⟩ := h1
  obtain ⟨h, e'⟩ := let_fix W T i 1 hy hyΔ hD.1 e
  exact ⟨_, h, by rw [e', pow_one]⟩

def P0 (T : LocLat G Qp LL O) (K : ℕ) (c : ℕ → W.DD T) : W.DD T :=
  ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) • (W.π₀ ^ y • c y)

theorem partialSum_pow_shift (T : LocLat G Qp LL O) (K t : ℕ) (c : ℕ → W.DD T) :
    ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K + t - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
      (W.π₀ ^ y • c y) = ((PD.p : ℕ) : O) ^ t • P0 W T K c := by
  rw [P0, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [← mul_smul, ← pow_add]
  congr 2
  have := eY_mono (PD := PD) (le_of_lt (Finset.mem_range.1 hy)) (Y := K)
  omega

theorem partialSum_gamma_sub (T : LocLat G Qp LL O) (K : ℕ) (c : ℕ → W.DD T) :
    W.γ T (P0 W T K c) - P0 W T K c = ∑ y ∈ Finset.range K,
      ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
        (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y) := by

  rw [P0, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [(W.γ T).map_smul, smul_sub]

theorem P0_sub_P0_eq_sum_smul_sub (T : LocLat G Qp LL O) (K : ℕ) (c c' : ℕ → W.DD T) :
    P0 W T K c - P0 W T K c' = ∑ y ∈ Finset.range K,
      ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) • (W.π₀ ^ y • (c y - c' y)) := by
  rw [P0, P0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_sub, smul_sub]

theorem partialSum_linear (T : LocLat G Qp LL O) (K : ℕ) (a a' : O) (c c' : ℕ → W.DD T) :
    P0 W T K (fun y => a • c y + a' • c' y) = a • P0 W T K c + a' • P0 W T K c' := by
  simp only [P0, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_add, smul_add, smul_comm (W.π₀ ^ y) a, smul_comm (W.π₀ ^ y) a', smul_comm _ a, smul_comm _ a']

theorem idempotent_smul_partialSum (T : LocLat G Qp LL O) (i : ZMod n) (K : ℕ) {c : ℕ → W.DD T}
    (hc : ∀ y, (letE i : LetA O n) • c y = c y) : (letE i : LetA O n) • P0 W T K c = P0 W T K c :=
  L_sum W _ _ fun y _ => L_osmul W _ (L_smul W _ (hc y))

theorem serZ_exists [NeZero n] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (i : ZMod n) (ζ : W.DD T) (hD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i ζ) (h1 : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 ζ) :
    ∃ c, Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsSerZ W T i ζ c :=
  ser_exists_of W hinj hO2 h9 hH hA T hT i ζ (eq_uniformizer_smul_of_level_one W T i hD h1)

theorem serZ_unique [NeZero n] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (i : ZMod n) (ζ : W.DD T) (c c' : ℕ → W.DD T) (hc : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsSerZ W T i ζ c)
    (hc' : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsSerZ W T i ζ c') (K : ℕ) : ∃ j : ℕ,
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T K (((PD.p : ℕ) : O) ^ j • ∑ y ∈ Finset.range K,
        ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
          (W.π₀ ^ y • (c y - c' y))) :=
  ser_unique_of W hinj hO2 h9 hH hA T hT i ζ c c' hc hc' K

theorem serZ_lin (T : LocLat G Qp LL O) (i : ZMod n) (a a' : O) {ζ ζ' : W.DD T} {c c' : ℕ → W.DD T}
    (hc : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsSerZ W T i ζ c) (hc' : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsSerZ W T i ζ' c') :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsSerZ W T i (a • ζ + a' • ζ') (fun y => a • c y + a' • c' y) :=
  ser_lin_of W T i a a' hc hc'

theorem redT (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (T : LocLat G Qp LL O) (i : ZMod n) {j M X σ : ℕ}
    {c : ℕ → W.DD T} {r s : ℕ → LetA O n} (hc : ∀ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i (c y))
    (hrs : ∀ y, Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) (t : ℕ) :
    ∃ Gv ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j,
      ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p (max M X + 1) + t) •
        ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c y) =
      ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (((PD.p : ℕ) : O) ^ t • P0 W T (max M X + 1) c) -
        Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • Gv := by
  obtain ⟨Gv, hGv, hsum⟩ := red_sum W hR T i hc hrs t
  rw [partialSum_pow_shift] at hsum
  exact ⟨Gv, hGv, hsum⟩

theorem Pp_tt [IsDomain O] (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (T : LocLat G Qp LL O) (i : ZMod n)
    {j M X σ : ℕ} {c : ℕ → W.DD T} {r s : ℕ → LetA O n} (hc : ∀ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i (c y))
    (hrs : ∀ y, Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) :
    ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c y) ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j :=
  (Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sum_mem fun y _ => Pp_gen W T i j
    (s_mem W (_root_.Formalism.MainNotions.LiftingTheory.tr_p_ne W) (rem_mem W hR.πΔ (hrs y).1) (hrs y).2) (hc y)

theorem hc_of {T : LocLat G Qp LL O} {i : ZMod n} {ζ : W.DD T} {c : ℕ → W.DD T}
    (hc : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsSerZ W T i ζ c) (y : ℕ) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (c y) :=
  InNΔi_of_DL W T i (hc.2.1 y).1 (hc.2.1 y).2

theorem zb [NeZero n] [IsDomain O] (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j)
    {ζ t : W.DD T} (hD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i ζ) (h1 : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 ζ)
    (ht : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsTrZ W T i j M X σ ζ t) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T (i + (j : ZMod n)) t ∧ t ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i j ∧
      ∃ p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i j,
        ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) ζ - (W.γ T t - t) = Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • p := by
  obtain ⟨c, r, s, hc, hrs, rfl⟩ := ht
  have hcN := hc_of W hc
  have hsA : ∀ y, s y ∈ W.AΔ := fun y => s_mem W (_root_.Formalism.MainNotions.LiftingTheory.tr_p_ne W) (rem_mem W hR.πΔ (hrs y).1) (hrs y).2
  refine ⟨⟨L_sum W _ _ fun y _ => L_smul W (s y)
      (Formalism.MainNotions.UnusedSlot80.PhiPowers.φD_pow_letter W T i (c y) (InNΔi_letter W T i (hcN y)) j), fun δ hδ => ?_⟩,
    Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨c y, ⟨(hc.2.1 y).2, (hc.2.1 y).1⟩, rfl⟩), ?_⟩

  · rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [_root_.Formalism.MainNotions.LiftingTheory.gammaD_semilinear, hsA y δ hδ,
      Formalism.MainNotions.UnusedSlot80.PhiPowers.φD_pow_Δ W T (hcN y).1.2 j δ hδ]
  obtain ⟨z', hz', hζ⟩ := eq_uniformizer_smul_of_level_one W T i hD h1
  set K0 := max M X + 1
  obtain ⟨t0, a, ha, haΔ, hae⟩ := hc.2.2 K0
  rw [← partialSum_gamma_sub] at hae
  obtain ⟨Gv, hGv, hred⟩ := redT W hR T i hcN hrs t0
  set tt := ∑ y ∈ Finset.range K0, s y • ((W.φD T) ^ j) (c y)
  have hPl := idempotent_smul_partialSum W T i K0 (fun y => InNΔi_letter W T i (hcN y))
  obtain ⟨ha', hva⟩ := let_fix W T i K0 ha haΔ
    (L_osmul W _ (L_sub W (L_osmul W _ hD.1) (L_sub W (L_γ W hPl) hPl))) hae
  have hS : tt ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j := Pp_tt W hR T i hcN hrs
  have hV : ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) ζ - (W.γ T tt - tt) ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j := by
    rw [hζ, φpow_smul]
    exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sub_mem (Pp_osmul W T i j _ _
      (Pp_gen W T i j (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W hR.πΔ j) hz'))
      ((Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sub_mem (Pp_γ W T i j tt hS) hS)
  have hF := sat W hsp hA T hT i j M X hV (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t0) ?_
  · obtain ⟨p, hp, hpe⟩ := fp_pull W T i j _ hF
    exact ⟨p, hp, hpe⟩
  have g2 : W.γ T (((W.φD T) ^ j) (((PD.p : ℕ) : O) ^ t0 • P0 W T K0 c)) =
      ((W.φD T) ^ j) (((PD.p : ℕ) : O) ^ t0 • W.γ T (P0 W T K0 c)) := by
    rw [← (W.γ T).map_smul]; exact γ_φpow W T W.gam j _
  have A1 : ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t0) • (((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) ζ) =
      ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j)
        (((PD.p : ℕ) : O) ^ t0 • (((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 • ζ)) := by
    rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, smul_smul, smul_smul, smul_smul,
      ← pow_add, ← pow_add, ← pow_add]
    congr 2
    ring
  have A2 : ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t0) • (W.γ T tt - tt) =
      ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (((PD.p : ℕ) : O) ^ t0 • (W.γ T (P0 W T K0 c) - P0 W T K0 c)) -
        (W.γ T (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • Gv) - Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • Gv) := by
    rw [smul_sub, ← (W.γ T).map_smul, hred, map_sub, (W.γ T).map_smul, g2, smul_sub (((PD.p : ℕ) : O) ^ t0),
      map_sub, smul_sub]
    abel
  have e2 : ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t0) •
      (((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) ζ - (W.γ T tt - tt)) =
      ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (W.π₀ ^ K0 • ((letE i : LetA O n) • a)) +
        (W.γ T (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • Gv) - Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • Gv) := by
    rw [smul_sub, A1, A2, ← hva]
    simp only [smul_sub, map_sub]
    abel
  rw [e2]
  exact inMultiple_add W T i j _ (InFP_osmul W T i j _ _ (keyF W hR.πΔ h2 T i hj M X ha'))
    (inMultiple_sub W T i j _ (InFP_γ W T i j (f_γ W hR M X) (inMultiple_of_mem W T i j _ hGv)) (inMultiple_of_mem W T i j _ hGv))

theorem zc [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j) (a a' : O)
    {ζ ζ' t t' t'' : W.DD T} (ht : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsTrZ W T i j M X σ ζ t)
    (ht' : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsTrZ W T i j M X σ ζ' t')
    (ht'' : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsTrZ W T i j M X σ (a • ζ + a' • ζ') t'') :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) (t'' - (a • t + a' • t')) := by
  obtain ⟨c, r, s, hc, hrs, rfl⟩ := ht
  obtain ⟨c', r', s', hc', hrs', rfl⟩ := ht'
  obtain ⟨c'', r'', s'', hc'', hrs'', rfl⟩ := ht''
  set K0 := max M X + 1
  have hc3 := serZ_lin W T i a a' hc hc'
  obtain ⟨t0, b, hb, hbΔ, hbe⟩ := serZ_unique W hinj hO2 h9 hH hA T hT i _ c'' _ hc'' hc3 K0
  rw [← P0_sub_P0_eq_sum_smul_sub] at hbe
  obtain ⟨Gv, hGv, hred⟩ := redT W hR T i (hc_of W hc) hrs t0
  obtain ⟨Gv', hGv', hred'⟩ := redT W hR T i (hc_of W hc') hrs' t0
  obtain ⟨Gv'', hGv'', hred''⟩ := redT W hR T i (hc_of W hc'') hrs'' t0
  have hl3 : ∀ y, (letE i : LetA O n) • (a • c y + a' • c' y) = a • c y + a' • c' y := fun y =>
    L_add W (L_osmul W _ (InNΔi_letter W T i (hc_of W hc y))) (L_osmul W _ (InNΔi_letter W T i (hc_of W hc' y)))
  obtain ⟨hb', hvb⟩ := let_fix W T i K0 hb hbΔ
    (L_osmul W _ (L_sub W (idempotent_smul_partialSum W T i K0 fun y => InNΔi_letter W T i (hc_of W hc'' y))
      (idempotent_smul_partialSum W T i K0 hl3))) hbe
  have hD : ∑ y ∈ Finset.range K0, s'' y • ((W.φD T) ^ j) (c'' y) -
      (a • ∑ y ∈ Finset.range K0, s y • ((W.φD T) ^ j) (c y) +
        a' • ∑ y ∈ Finset.range K0, s' y • ((W.φD T) ^ j) (c' y)) ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j :=
    (Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sub_mem (Pp_tt W hR T i (hc_of W hc'') hrs'')
      ((Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).add_mem (Pp_osmul W T i j a _ (Pp_tt W hR T i (hc_of W hc) hrs))
        (Pp_osmul W T i j a' _ (Pp_tt W hR T i (hc_of W hc') hrs')))
  refine sat W hsp hA T hT i j M X hD (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t0) ?_
  have hsm : ∀ (o : O) (Y : W.DD T), o • (((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) Y) =
      ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (o • Y) := fun o Y => by
    rw [LinearMap.map_smul_of_tower, smul_comm]
  have hE : ((PD.p : ℕ) : O) ^ t0 • P0 W T K0 c'' =
      a • (((PD.p : ℕ) : O) ^ t0 • P0 W T K0 c) + a' • (((PD.p : ℕ) : O) ^ t0 • P0 W T K0 c') +
        W.π₀ ^ K0 • ((letE i : LetA O n) • b) := by
    rw [← hvb, partialSum_linear]
    simp only [smul_sub, smul_add]
    rw [smul_comm (((PD.p : ℕ) : O) ^ t0) a, smul_comm (((PD.p : ℕ) : O) ^ t0) a']
    abel
  have e : ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t0) •
      (∑ y ∈ Finset.range K0, s'' y • ((W.φD T) ^ j) (c'' y) -
        (a • ∑ y ∈ Finset.range K0, s y • ((W.φD T) ^ j) (c y) +
          a' • ∑ y ∈ Finset.range K0, s' y • ((W.φD T) ^ j) (c' y))) =
      ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (W.π₀ ^ K0 • ((letE i : LetA O n) • b)) -
        Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • (Gv'' - (a • Gv + a' • Gv')) := by
    rw [smul_sub, smul_add, smul_comm _ a, smul_comm _ a', hred, hred', hred'', hE, smul_sub a, smul_sub a',
      hsm a, hsm a', smul_comm a (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) Gv, smul_comm a' (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) Gv',
      map_add, map_add, smul_add, smul_add, smul_sub, smul_add]
    abel
  rw [e]
  exact inMultiple_sub W T i j _ (InFP_osmul W T i j _ _ (keyF W hR.πΔ h2 T i hj M X hb'))
    (inMultiple_of_mem W T i j _ ((Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sub_mem hGv'' ((Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).add_mem
      (Pp_osmul W T i j a _ hGv) (Pp_osmul W T i j a' _ hGv'))))

theorem keyF' (hπ : W.π₀ ∈ W.AΔ)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (i : ZMod n) {j : ℕ} (hj : 1 ≤ j) {M X K : ℕ} (hMK : M ≤ K)
    (hXK : X ≤ (PD.p - 1) * K) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) (((W.φD T) ^ j) (W.π₀ ^ K • x)) := by
  obtain ⟨y, hy, hyx⟩ := phij_pi0pow W T i hπ h2 j X K hXK hx
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  set e : LetA O n := W.π₀ ^ (K - M) * ∏ k ∈ Finset.range j', Formalism.MainNotions.LiftingTheory.pk W (k + 1) ^ X
  have he : e ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hπ _)
    (W.AΔ.prod_mem fun k _ => W.AΔ.pow_mem (pk_mem_AΔ W hπ _) _)
  have hJ : Formalism.MainNotions.LiftingTheory.JJ W (j' + 1) X K = Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X * e := by
    rw [Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_succ', Formalism.MainNotions.CrystallineLiftingInputs.fMX]
    have hp0 : Formalism.MainNotions.LiftingTheory.pk W 0 = Formalism.MainNotions.LiftingTheory.qp W := by simp [Formalism.MainNotions.LiftingTheory.pk]
    rw [hp0]
    have : W.π₀ ^ K = W.π₀ ^ M * W.π₀ ^ (K - M) := by rw [← pow_add]; congr 1; omega
    rw [this]
    ring
  refine ⟨e • y, Pp_smul W T i _ he y hy, ?_⟩
  rw [hyx, hJ, mul_smul]

theorem partialSum_mem_uniformizer_mul (hπ : W.π₀ ∈ W.AΔ) (T : LocLat G Qp LL O) (i : ZMod n) (K : ℕ) {c : ℕ → W.DD T}
    (hc0 : c 0 = 0) (hc : ∀ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i (c y)) :
    ∃ E', Formalism.MainNotions.LiftingTheory.InNΔi W T i E' ∧ P0 W T K c = W.π₀ • E' := by
  refine ⟨∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
      (W.π₀ ^ (y - 1) • c y),
    InNΔi_sum W T i _ _ fun y _ => InNΔi_osmul W T i _ (InNΔi_smul W T i (W.AΔ.pow_mem hπ _) (hc y)), ?_⟩
  rw [P0, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [hc0]
  · rw [smul_comm W.π₀, smul_smul, ← pow_succ', Nat.sub_add_cancel hy]

theorem zd [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j)
    (hXM : X ≤ (PD.p - 1) * M) {ζ t : W.DD T} (hD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i ζ)
    (hMζ : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T M ζ) (ht : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.IsTrZ W T i j M X σ ζ t) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) t := by
  obtain ⟨c, r, s, hc, hrs, rfl⟩ := ht
  have hr9 := (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hT).1
  have hcN := hc_of W hc
  set K0 := max M X + 1
  have hMK : M ≤ K0 := by omega
  obtain ⟨t1, a, ha, haΔ, hae⟩ := hc.2.2 M
  rw [← partialSum_gamma_sub] at hae
  obtain ⟨ζ0, hζ0, hζ0Δ, hζ⟩ := hMζ

  have hPl := idempotent_smul_partialSum W T i M (fun y => InNΔi_letter W T i (hcN y))
  have hγP : W.γ T (((PD.p : ℕ) : O) ^ t1 • P0 W T M c) - ((PD.p : ℕ) : O) ^ t1 • P0 W T M c =
      W.π₀ ^ M • (((PD.p : ℕ) : O) ^ (t1 + Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p M) • ζ0 - a) := by
    rw [(W.γ T).map_smul, ← smul_sub]
    rw [show ((PD.p : ℕ) : O) ^ t1 • (W.γ T (P0 W T M c) - P0 W T M c) =
        ((PD.p : ℕ) : O) ^ t1 • (((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p M • ζ) - W.π₀ ^ M • a by
      rw [← hae]; simp only [smul_sub]; abel]
    rw [hζ, smul_smul, ← pow_add, smul_comm (((PD.p : ℕ) : O) ^ (t1 + Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p M)) (W.π₀ ^ M) ζ0,
      smul_sub]
  obtain ⟨hz, hzv⟩ := let_fix W T i M
    ((W.N T).sub_mem ((W.N T).smul_of_tower_mem _ hζ0) ha)
    (fun δ hδ => by rw [map_sub, map_smul, hζ0Δ δ hδ, haΔ δ hδ])
    (L_sub W (L_γ W (L_osmul W _ hPl)) (L_osmul W _ hPl)) hγP
  obtain ⟨E', hE', hPE⟩ := partialSum_mem_uniformizer_mul W hr9.1 T i M hc.1 hcN
  obtain ⟨k, x, hx, hkx⟩ := formal_unique W T i hinj hO2 hr9.1 hr9.2.2.1 (hH hA T hT i).1
    (hH hA T hT i).2.1 M _ ⟨((PD.p : ℕ) : O) ^ t1 • E', InNΔi_osmul W T i _ hE', by rw [hPE, smul_comm]⟩
    ⟨_, hz, hzv⟩

  obtain ⟨Gv, hGv, hred⟩ := redT W hR T i hcN hrs (t1 + k)
  have hS : ∑ y ∈ Finset.range K0, s y • ((W.φD T) ^ j) (c y) ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j :=
    Pp_tt W hR T i hcN hrs
  refine sat W hsp hA T hT i j M X hS (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + (t1 + k)) ?_
  rw [hred]
  refine inMultiple_sub W T i j _ (InFP_osmul W T i j _ _ ?_) (inMultiple_of_mem W T i j _ hGv)

  have hsplit : ((PD.p : ℕ) : O) ^ (t1 + k) • P0 W T K0 c =
      ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p M) •
        (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (((PD.p : ℕ) : O) ^ t1 • P0 W T M c)) +
      ∑ y ∈ Finset.Ico M K0, ((PD.p : ℕ) : O) ^ (t1 + k +
        (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y)) • (W.π₀ ^ y • c y) := by
    rw [P0, ← Finset.sum_range_add_sum_Ico _ hMK, smul_add, Finset.smul_sum, Finset.smul_sum, P0,
      Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun y hy => ?_
      have hyM := Finset.mem_range.1 hy
      have h1 := eY_mono (PD := PD) (le_of_lt hyM)
      have h2' := eY_mono (PD := PD) hMK
      have h3 := h1.trans h2'
      rw [← lsmul_eq]
      simp only [smul_smul, ← pow_add]
      congr 2
      zify [h1, h2', h3]
      ring
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [smul_smul, ← pow_add]

  rw [hsplit, hkx, map_add (f := _), map_sum]
  refine inMultiple_add W T i j _ (?_) (inMultiple_sum W T i j _ _ _ fun y hy => ?_)
  · rw [LinearMap.map_smul_of_tower]
    exact InFP_osmul W T i j _ _ (keyF' W hr9.1 h2 T i hj le_rfl hXM hx)
  · have hy := Finset.mem_Ico.1 hy
    rw [LinearMap.map_smul_of_tower]
    refine InFP_osmul W T i j _ _ (keyF' W hr9.1 h2 T i hj hy.1 ?_ (hcN y))
    exact le_trans hXM (Nat.mul_le_mul_left _ hy.1)

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData


noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.Relay2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem tTool2Z_of [NeZero n] [IsDomain O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.TTool2Z W := by
  intro hA hl j M X σ hc T hT i
  have hj : 1 ≤ j := by rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> omega
  have hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W :=
    Formalism.MainNotions.UnusedSlot80.SatPW.satPCore_of W hinj (fun T hT => h9 T hT)
  have h2 := (hTr hA).2.1
  have h9r := (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hT).1
  have hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W := Formalism.MainNotions.LiftingTheory.lifta_ring_of W h9r
  obtain ⟨r, s, hrs⟩ := rs_ex W hTr hlm h9r hA hl hc
  refine ⟨fun ζ hD h1 => ?_, fun ζ t hD h1 ht => zb W hR hsp hA h2 T hT i hj hD h1 ht,
    fun a a' ζ ζ' t t' t'' _ _ _ _ ht ht' ht'' =>
      fp_pull W T i j _ (zc W hinj hO2 h9 hH hR hsp hA h2 T hT i hj a a' ht ht' ht''),
    fun ζ t hD hM _ hXM ht => fp_pull W T i j _ (zd W hinj hO2 h9 hH hR hsp hA h2 T hT i hj hXM hD hM ht)⟩
  obtain ⟨c, hcs⟩ := serZ_exists W hinj hO2 h9 hH hA T hT i ζ hD h1
  exact ⟨_, c, r, s, hcs, hrs, rfl⟩

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

end -- clump:auto
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.LevelLetterCocycles.EqUniformizerSmulOfLevelOne =====

-- ===== clump member: Formalism.SharpRestriction.LevelLetterCocycles.TruncationClauseOfLatticeHypotheses =====
-- clump-header: {"m": "Formalism.SharpRestriction.LevelLetterCocycles.TruncationClauseOfLatticeHypotheses", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.IsTruncIff\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CompleteOfPow\npublic import Formalism.SharpRestriction.LevelLetterCocycles.EqUniformizerSmulOfLevelOne\nimport Formalism.SharpRestriction.LevelLetterCocycles.HermFlagUnipotentAnisotropicVectorSubMem\nimport Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem truncation_clause_of_lattice_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h8 : Formalism.MainNotions.CrystallineLiftingInputs.adm8 D HW F) (h9 : Formalism.MainNotions.CrystallineLiftingInputs.adm9 D HW F) :
    Formalism.MainNotions.CrystallineLiftingInputs.adm15 D HW F Cm := by
  refine ⟨Formalism.MainNotions.CrystallineLiftingInputs.TToolAlg_holds, fun l _ K LL hg _ => ?_⟩
  have hP9W : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hg) := hP9 l K 1 LL hg
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hO2 : ∀ x : ↥LL.1, 0 ≤ (D.loc l).v LL x → ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = x :=
    fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩
  letI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.CrystallineLiftingInputs.OL.OL_complete_max (D.loc l) LL
  have hlm : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.CrystallineLiftingInputs.OL.l_mem_max (D.loc l) LL
  exact ⟨tTool1_of _ hinj hO2 hP9W (h8 l K 1 LL hg),
    tTool2_of _ hinj hO2 hlm hP9W (h8 l K 1 LL hg) (h9 l K 1 LL hg)⟩

theorem tTool2Z_DU (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h8 : Formalism.MainNotions.CrystallineLiftingInputs.adm8 D HW F) (h9 : Formalism.MainNotions.CrystallineLiftingInputs.adm9 D HW F) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.TTool2Z ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  have hP9W : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hg) := hP9 l K 1 LL hg
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hO2 : ∀ x : ↥LL.1, 0 ≤ (D.loc l).v LL x → ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = x :=
    fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩
  letI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.CrystallineLiftingInputs.OL.OL_complete_max (D.loc l) LL
  have hlm : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.CrystallineLiftingInputs.OL.l_mem_max (D.loc l) LL
  exact tTool2Z_of _ hinj hO2 hlm hP9W (h8 l K 1 LL hg) (h9 l K 1 LL hg)

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.LevelLetterCocycles.TruncationClauseOfLatticeHypotheses =====
