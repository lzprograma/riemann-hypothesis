module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCpFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlowUpFibreSemilocal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfIsIntegralInt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwJumps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatPol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.MapInvMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsStepHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CharPolEqRootPol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.SatCard
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSSLeft
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.TypeStar
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxUnramifiedSubfieldConjIff
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PContLeft

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.AevalSmulProd, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.JumpsOf, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCutStep, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBridge, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RichOf, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwCrys, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwJ, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.UnrPolNegOne, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.StepsMain

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.AevalSmulProd =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.AevalSmulProd", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCpFacts\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)

private theorem aeval_smul_prod {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : K) (S : Multiset K) :
    aeval (c • M) ((S.map fun b => X - C (b * c)).prod) =
      c ^ Multiset.card S • aeval M ((S.map fun b => X - C b).prod) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, map_mul (aeval (c • M)), map_mul (aeval M), ih]
    simp only [map_sub, aeval_X, aeval_C]
    have e : (algebraMap K (Matrix (Fin n) (Fin n) K)) (z * c) = c • (algebraMap K (Matrix (Fin n) (Fin n) K)) z := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]
    rw [e, ← smul_sub, smul_mul_smul_comm, pow_succ']

theorem UpperTheory.Gal.Int.Geo.twES :
    UpperTheory.Gal.Int.Geo.TwES := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ _ _ w c m hCl hw R hES A hA
  have hχ := hCl.1 hw A hA
  obtain ⟨hi, hf⟩ := hES A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 := (hχ.1 s hs)
    have h2 : (χ s : Qbar l) = 1 := by
      have h3 : ((GlobalTheory.TripleGal.rk1 χ s : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 = (χ s : Qbar l) := by
        simp [GlobalTheory.TripleGal.rk1]
      rw [h1] at h3
      simpa using h3.symm
    apply Units.ext
    rw [UpperTheory.V.Af.tw_val, hi s hs, h2]
    simp
  · have hk : ι ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = c := by
      have h1 := (hχ.2 σ hσ)
      have h2 := (UpperTheory.Gal.TP.Sub.cpFacts_holds (G E Ω) (Qbar l) 0 0).2.1 χ σ⁻¹
      simp only [UpperTheory.Gal.TP.Sub.cp] at h2
      rw [h2] at h1
      simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C] at h1
      exact C_injective (sub_right_injective h1)
    have hs : ∀ T : Multiset ℂ, ((T.map fun b => X - C b).prod).map ι.symm.toRingHom =
        ((T.map ι.symm).map fun b => X - C b).prod := by
      intro T
      rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
      refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
      simp
    have hc : ι.symm c = ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      rw [← hk]; simp
    have hfin := hf σ hσ
    rw [hs] at hfin
    have hR : (R.map (· * c)).map ι.symm = (R.map ι.symm).map (· * ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l)) := by
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun x _ => ?_
      simp [map_mul, hc]
    rw [UpperTheory.V.Af.tw_val, hs, hR, Multiset.map_map]
    have := aeval_smul_prod (ρ σ⁻¹ : Matrix (Fin dd) (Fin dd) (Qbar l)) ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) (R.map ι.symm)
    rw [hfin, smul_zero] at this
    exact this
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.AevalSmulProd =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.JumpsOf =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.JumpsOf", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlowUpFibreSemilocal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)

theorem UpperTheory.Gal.Int.Geo.jumpsOf :
    UpperTheory.Gal.Int.Geo.JumpsOf := by
  intro E Ω _ _ _ _ _ _ l _ ι a dd U ρ w Q hQ hJ P AI hT A hA O _ _ _ Bw hBw τ LL' τ' hi lam J hl hJm
  obtain ⟨J', h1, h2⟩ := hJ P AI hT A hA O Bw hBw τ LL' τ' hi
  have e : J = (GlobalTheory.RoadWGeo.wtJumps lam).val :=
    Multiset.map_injective Int.cast_injective (hJm.trans (GlobalTheory.RoadWGeo.wtJumps_val lam).symm)
  refine ⟨J', h1, fun j hj => h2 j (hQ _ (GlobalTheory.CongL.LimAtLU.overPl_of_induced ι hA hBw hi) lam hl j ?_)⟩
  rw [e] at hj
  exact hj
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.JumpsOf =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCutStep =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCutStep", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)

namespace UpperTheory.Gal.Int.Geo

open Cut

private theorem cut {k L O : Type} [Field k] [Field L] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O k]
    [IsFractionRing O k] {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) :
    ∃ (C' : Cover H θ O) (j : C'.Y ⟶ C.Y), Part j ∧ C'.p = j ≫ C.p ∧ C'.π ≫ j = C.π ∧ C'.Onto ∧
      ∀ y ∈ Set.range j, (C.p y).asIdeal = ⊥ → y ∈ Set.range C.π := by
  have := C.finπ
  have := C.etπ
  have hU : IsClopen (Set.range (pullback.lift C.π H.q C.ov)) :=
    ⟨(Scheme.Hom.isClosedMap _).isClosed_range, (Scheme.Hom.isOpenMap _).isOpen_range⟩
  obtain ⟨V, hVc, hVpre⟩ := clopenExt O k C.Y C.p C.smooth _ hU
  obtain ⟨C', j, hj, hrj, hp, hπ, hon⟩ := coverCut k L O H θ C V hVc hVpre
  refine ⟨C', j, hj, hp, hπ, hon, ?_⟩
  intro y hy hgen
  have hyV : y ∈ (V : Set C.Y) := hrj ▸ hy
  have hy' : y ∈ Set.range (pullback.fst C.p (gen O k)) := by
    rw [(genRange O k C.Y C.p).1]
    exact hgen
  obtain ⟨z, rfl⟩ := hy'
  have hz : z ∈ Set.range (pullback.lift C.π H.q C.ov) := by
    rw [← hVpre]
    exact hyV
  obtain ⟨x, rfl⟩ := hz
  exact ⟨x, by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩

private theorem over_eq {Y' Y T' T S : Scheme.{0}} {j : Y' ⟶ Y} {s t : T ⟶ Y} {i : T' ⟶ T} {s' t' : T' ⟶ Y'}
    (h : Res j s t i s' t') {p : Y ⟶ S} (e : t ≫ p = s ≫ p) : t' ≫ j ≫ p = s' ≫ j ≫ p := by
  rw [← Category.assoc, h.et, Category.assoc, e, ← Category.assoc, ← h.es, Category.assoc]

private theorem mem_range_of_lies_of_mem_range_of_asIdeal_bot {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k}
    {θ : H.Γ → L} {C C' : Cover H θ O} {j : C'.Y ⟶ C.Y} (hj : Part j) (hπ : C'.π ≫ j = C.π)
    (hgen : ∀ y ∈ Set.range j, (C.p y).asIdeal = ⊥ → y ∈ Set.range C.π) {g : H.Γ} {T : Scheme}
    {s t : T ⟶ C.Y} {m : ℕ} (hl : C.Lies g s t m) (x : T) (hx : s x ∈ Set.range j)
    (hxg : (C.p (s x)).asIdeal = ⊥) : t x ∈ Set.range j := by
  obtain ⟨z, hz⟩ := (liesCut k L O H θ C C' j hj hπ g T s t m hl).1 x (hgen _ hx hxg)
  exact ⟨C'.π z, by rw [← Scheme.Hom.comp_apply, hπ, hz]⟩

private theorem mem_range_of_fEt_of_lies_of_mem_range {k L O : Type} [Field k] [Field L] [CommRing O] [IsDomain O] [Algebra O k]
    {H : HTower k} {θ : H.Γ → L} {C C' : Cover H θ O} {j : C'.Y ⟶ C.Y} (hj : Part j)
    (hπ : C'.π ≫ j = C.π) (hgen : ∀ y ∈ Set.range j, (C.p y).asIdeal = ⊥ → y ∈ Set.range C.π)
    {g : H.Γ} {T : Scheme} {s t : T ⟶ C.Y} {d m : ℕ} (hs : FEt s d) (hl : C.Lies g s t m) :
    ∀ x, s x ∈ Set.range j → t x ∈ Set.range j := by
  have : Etale s := hs.2.1
  have := C.smooth
  have := hj.op
  have hD := genDense O T (s ≫ C.p) inferInstance
  by_contra! hne
  obtain ⟨x, hx, hxt⟩ := hne
  have hopen : IsOpen ({x | s x ∈ Set.range j} ∩ {x | t x ∈ Set.range j}ᶜ) :=
    IsOpen.inter (j.isOpenEmbedding.isOpen_range.preimage s.continuous)
      (hj.cl.preimage t.continuous).isOpen_compl
  obtain ⟨y, ⟨hy1, hy2⟩, hyg⟩ := hD.inter_open_nonempty _ hopen ⟨x, hx, hxt⟩
  rw [Set.mem_ofPred_eq, Scheme.Hom.comp_apply] at hyg
  exact hy2 (mem_range_of_lies_of_mem_range_of_asIdeal_bot hj hπ hgen hl y hy1 hyg)

private theorem asIdeal_eq_bot_of_mem_basicOpen_natCast {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {Y : Scheme}
    (q : Y ⟶ Spec (CommRingCat.of (Ow w))) (p : ℕ) (hp : (p : 𝓞 E) ∈ w.asIdeal) (y : Y)
    (hy : y ∈ Y.basicOpen (p : Γ(Y, ⊤))) : (q y).asIdeal = ⊥ := by
  have hmax : (p : Ow w) ∈ IsLocalRing.maximalIdeal (Ow w) := by
    rw [ValuationSubring.valuation_lt_one_iff]
    have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (p : 𝓞 E)).2 hp
    have h2 := (Valuation.isEquiv_iff_val_lt_one.1
      (Valuation.isEquiv_valuation_valuationSubring (w.valuation E))).1 h1
    convert h2 using 2
    push_cast
    rfl
  have h3 : (p : Γ(Y, ⊤)) =
      (q.appTop) ((Scheme.ΓSpecIso (CommRingCat.of (Ow w))).inv (p : Ow w)) := by
    simp
  rw [h3, ← Scheme.Hom.preimage_basicOpen_top] at hy
  have h5 : q y ∈ ((Spec (CommRingCat.of (Ow w))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Ow w))).inv (p : Ow w)) : Set _) := hy
  rw [basicOpen_eq_of_affine] at h5
  have h6 : (p : Ow w) ∉ (q y).asIdeal := h5
  by_contra hne
  have hM := IsLocalRing.eq_maximalIdeal ((q y).isPrime.isMaximal hne)
  exact h6 (hM ▸ hmax)

theorem cutStep_holds : CutStep := by
  intro E _ _ L _ H θ _ w
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨C', j, hj, hp, hπ, hon, hgen⟩ := cut C
    refine ⟨C', hon, fun g => ?_⟩
    obtain ⟨T, s, t, d, m, hs, ht, hl⟩ := hC g
    obtain ⟨T', i, s', t', hR⟩ := resEx _ _ _ j s t hj
    have hst := mem_range_of_fEt_of_lies_of_mem_range hj hπ hgen hs hl
    refine ⟨T', s', t', d, m, fEtCut _ _ _ _ j s t i s' t' d hj hR hst hs, ?_, ?_⟩
    · rw [hp]
      exact over_eq hR ht
    · exact (liesCut _ _ _ H θ C C' j hj hπ g T s t m hl).2 T' i s' t' hR
  · rintro n ϑ ⟨C, p, f, hpr, hpw, hnorm, ϖ, T, γ, m, hirr, hpt, hT⟩
    obtain ⟨C', j, hj, hp, hπ, hon, hgen⟩ := cut C
    have hres := fun a => resEx _ _ _ j (T a).p (T a).r hj
    choose Z i s' t' hR using hres
    have hcond : ∀ a (x : (T a).Z), (T a).p x ∈ Set.range j →
        (T a).p x ∈ C.Y.basicOpen (p : Γ(C.Y, ⊤)) → (T a).r x ∈ Set.range j :=
      fun a x hx hb => mem_range_of_lies_of_mem_range_of_asIdeal_bot hj hπ hgen (hT a).2.1 x hx (asIdeal_eq_bot_of_mem_basicOpen_natCast w C.p p hpw _ hb)
    have hc := fun a => corrCut p _ _ _ j (T a) (i a) (s' a) (t' a) hj (hR a) (hcond a)
    let T' : Fin (n + 1) → crystallineComparison.Corr p C'.Y := fun a =>
      ⟨Z a, s' a, t' a, (T a).d, (hc a).1, (hc a).2.1, (hc a).2.2⟩
    refine ⟨C', p, f, hpr, hpw, hnorm, hon, ϖ, T', γ, m, hirr, ?_, fun a => ⟨?_, ?_, (hT a).2.2⟩⟩
    · have := ptIdCut p (p ^ f) n _ _ j (crystallineComparison.fn C.p ϖ) T T' i hj hR hcond hpt
      convert this using 2
      rw [hp]
      simp only [crystallineComparison.fn, Scheme.Hom.comp_appTop]
      rfl
    · show t' a ≫ C'.p = s' a ≫ C'.p
      rw [hp]
      exact over_eq (hR a) (hT a).1
    · exact (liesCut _ _ _ H θ C C' j hj hπ (γ a) _ _ _ (m a) (hT a).2.1).2 _ (i a) _ _ (hR a)

end UpperTheory.Gal.Int.Geo
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCutStep =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBridge =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBridge", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc\npublic import ReciprocityTheory.GaloisValuations.Global\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxUnramifiedSubfieldConjIff\nimport Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar\n\n"}
section -- clump:auto
@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 NumberField IsDedekindDomain Module GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.PhtCompare

section
variable {l : ℕ} [Fact l.Prime]
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}

theorem exists_bridge (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j ∧ Bw.Kw.1 ≤ Bw.LL.1 ∧
      Bw.Kw.1 = IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)) := by
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl
  exact ⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩,
    { Kw := K
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec
      LL := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
      LL_split := fun τ x => AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, rfl, IntermediateField.le_normalClosure _, rfl⟩

end

end GlobalTheory.PhtCompare

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBridge =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RichOf =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RichOf", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfIsIntegralInt\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBridge\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)

private theorem norm_lt_one_iff_mem {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime] (τ : E →+* Om l)
    (v : HeightOneSpectrum (𝓞 E)) (hv : ∀ x ∈ v.asIdeal, ‖τ (x : E)‖ < 1) (x : 𝓞 E) :
    ‖τ (x : E)‖ < 1 ↔ x ∈ v.asIdeal := by
  refine ⟨fun hx => ?_, hv x⟩
  by_contra hn
  obtain ⟨y, i, hi, e⟩ := v.isMaximal.exists_inv hn
  have hy : ‖τ (y : E)‖ ≤ 1 :=
    GlobalTheory.CongW.PlaceEmb.norm_le_one_of_isIntegral_int ((NumberField.RingOfIntegers.isIntegral_coe y).map τ.toIntAlgHom)
  have h1 : τ (y : E) * τ (x : E) + τ (i : E) = 1 := by
    have := congrArg (fun z : 𝓞 E => τ (z : E)) e
    simpa using this
  have h2 : ‖τ (y : E) * τ (x : E)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hy) hx
  have h3 := IsUltrametricDist.norm_add_le_max (τ (y : E) * τ (x : E)) (τ (i : E))
  rw [h1, norm_one] at h3
  exact absurd h3 (not_le.2 (max_lt h2 (hv i hi)))

private theorem exists_place {Ω : Type} [Field Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) :
    ∃ A : ValuationSubring Ω, ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 :=
  ⟨{ carrier := {x | ‖j x‖ ≤ 1}
     mul_mem' := fun {a b} ha hb => by
       simp only [Set.mem_ofPred_eq, map_mul, norm_mul] at *; exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hb
     one_mem' := by simp
     add_mem' := fun {a b} ha hb => by
       simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
       exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
     zero_mem' := by simp
     neg_mem' := fun {a} ha => by simpa using ha
     mem_or_inv_mem' := fun x => by
       simp only [Set.mem_ofPred_eq, map_inv₀, norm_inv]
       rcases le_total ‖j x‖ 1 with h | h
       · exact Or.inl h
       · exact Or.inr (inv_le_one_of_one_le₀ h) }, fun _ => Iff.rfl⟩

theorem UpperTheory.Gal.Int.Geo.richOf :
    UpperTheory.Gal.Int.Geo.RichOf := by
  intro E Ω _ _ _ _ _ _ l _ ι a dd U ρ v hv hlac hJ
  obtain ⟨τc, hover, lam, hw, hl⟩ := hlac
  obtain ⟨P, AI, hT⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  let τ₀ : E →+* Om l := ι.symm.toRingHom.comp τc
  have hτ₀ : ι.toRingHom.comp τ₀ = τc := by
    ext x
    simp [τ₀]
  have hsmall : ∀ x ∈ v.asIdeal, ‖τ₀ (x : E)‖ < 1 := hover
  let : Algebra E (Om l) := τ₀.toAlgebra
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  let jA : Ω →ₐ[E] Om l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let j : Ω →+* Om l := jA.toRingHom
  have hjτ : ∀ x : E, j (algebraMap E Ω x) = τ₀ x := fun x => jA.commutes x
  obtain ⟨A, hA⟩ := exists_place j
  obtain ⟨L, Bw, hBj, -, -⟩ := GlobalTheory.PhtCompare.exists_bridge (E := E) (A := A) j hA
  have hBw : Induces Bw := fun x => by rw [hBj]; exact hA x
  have hP : IsPlaceOver A v := fun x => by
    rw [hBw.valuation_lt_one_iff, hBj, hjτ]
    exact norm_lt_one_iff_mem τ₀ v hsmall x
  have hi : IsInduced Bw τ₀ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := fun x => by
    show τ₀ x = Bw.j (algebraMap E Ω x)
    rw [hBj, hjτ]
  obtain ⟨J', hJ', hsub⟩ := hJ P AI hT A hP _ Bw hBw τ₀ Bw.Kw (AlgHom.id ℚ_[l] ↥Bw.Kw.1) hi lam (wtJumps lam).val
    (by rw [hτ₀]; exact hw) (wtJumps_val lam)
  exact ⟨P, AI, hT, v, A, hv, hP, _, inferInstance, inferInstance, inferInstance, Bw, hBw, τ₀, J', hJ',
    wtJumps lam, card_wtJumps lam, fun j hj => hsub j hj, hl⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RichOf =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwCrys =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwCrys", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwLoc\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)

theorem UpperTheory.Gal.Int.Geo.twCrys :
    UpperTheory.Gal.Int.Geo.TwCrys := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ _ _ w c m hχ hρ P AI hT A h O _ _ _ Bw hj
  obtain ⟨c1, -, -, -⟩ := hχ.2 P AI hT A h O Bw hj
  have c2 := hρ P AI hT A h O Bw hj
  have e1 : (rk1 χ).comp (Dec (F := E) A).subtype = rk1 (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw ρ χ).comp (Dec (F := E) A).subtype =
      tw (ρ.comp (Dec (F := E) A).subtype) (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  rw [e1] at c1
  rw [e2]
  exact (UpperTheory.Gal.TP.Sub.twLoc_holds l P AI hT E Ω A O Bw dd (ρ.comp (Dec (F := E) A).subtype)
    (χ.comp (Dec (F := E) A).subtype)).2 c2 c1
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwCrys =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwJ =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwJ", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwJumps\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)

theorem UpperTheory.Gal.Int.Geo.twJ :
    UpperTheory.Gal.Int.Geo.TwJ := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ hρ hχ w c m h1 Q hQ P AI hT A hA O _ _ _ Bw hj τ LL' τ' hi
  obtain ⟨J, hJ, hJQ⟩ := hQ P AI hT A hA O Bw hj τ LL' τ' hi
  obtain ⟨-, -, j1, -⟩ := h1.2 P AI hT A hA O Bw hj
  have e1 : (rk1 χ).comp (Dec (F := E) A).subtype = rk1 (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw ρ χ).comp (Dec (F := E) A).subtype =
      tw (ρ.comp (Dec (F := E) A).subtype) (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  have j2 := j1 τ LL' τ' hi
  rw [e1] at j2
  have cs : Continuous (ρ.comp (Dec (F := E) A).subtype) := hρ.comp continuous_subtypeVal
  have cμ : Continuous (χ.comp (Dec (F := E) A).subtype) := hχ.comp continuous_subtypeVal
  refine ⟨J.map (· + m (ι.toRingHom.comp τ)), ?_, fun j hj' => ?_⟩
  · rw [e2]
    exact UpperTheory.Gal.TP.Sub.twJumps_holds l P AI hT E Ω A O Bw dd _ _ cs cμ τ J _ hJ j2
  · exact Multiset.mem_map.2 ⟨_, hJQ _ hj', by simp⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwJ =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.UnrPolNegOne =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.UnrPolNegOne", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatPol\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)

private theorem unrPol_neg_one (S : Multiset ℂ) : unrPol S (-1) = rootPol S := by
  simp [unrPol, rootPol]

theorem UpperTheory.Gal.Int.Geo.phiOf :
    UpperTheory.Gal.Int.Geo.PhiOf := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ w a B _ hK P AI hT A h O _ _ _ Bw hj
  obtain ⟨hc, g, hg, m, hd⟩ := hK P AI hT A h O Bw hj
  refine ⟨hc, g, hg, m, ?_⟩
  rw [UpperTheory.Gal.TP.Sub.satPol_holds E Ω A w h a B g, hg, unrPol_neg_one]
  exact hd
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.UnrPolNegOne =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.StepsMain =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.StepsMain", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.MapInvMul\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsStepHolds\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.AevalSmulProd\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CharPolEqRootPol\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.JumpsOf\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCutStep\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepMain\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RichOf\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.SatCard\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwCrys\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwJ\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.UnrPolNegOne\nimport Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PContLeft\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSSLeft\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

namespace UpperTheory.Gal.Int.Geo

theorem steps_of (hC : CrysStep) (hJ : JumpStep) (hP : PhiStep) : Steps :=
  ⟨repEx_holds, Mod.esStep_holds, hC, hJ, hP, cutStep_holds, twES, twCrys, twJ, twPhi, phiOf, satCard, jumpsOf, richOf,
    TP.Sub.charEx, TP.Sub.sSLeft_holds, TP.Sub.contLeft_holds⟩

end UpperTheory.Gal.Int.Geo
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.StepsMain =====
