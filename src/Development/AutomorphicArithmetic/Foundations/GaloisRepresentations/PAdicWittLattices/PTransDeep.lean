module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubAFiniteFree
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateLatticeSystem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeTranslateLocallyNoetherianBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDeep

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDeep =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDeep", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeTranslateLocallyNoetherianBaseStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateWeilLocal\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem oActN_act_natCast_eq_one_pow {S : Scheme} {O : Type} [Ring O] {G : Over S} [GrpObj G]
    (a : GlobalTheory.UPel.HT.OActN O G) (n : ℕ) : a.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    have h2 := congrArg (· * (a.act 0)⁻¹) h
    simp only [mul_inv_cancel, mul_inv_cancel_right] at h2
    rw [Nat.cast_zero, pow_zero]
    exact h2.symm
  | succ n ih =>
    rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

theorem UpperTheory.Gal.G3.pTransDeep :
    SysOf → AdmOf → FullOf → RelArith → TransDeep := by
  intro hSys hAdm hFull hRel p _ D G L R _ _ gb h hI
  obtain ⟨f, u, c, k, hsys, hm, hk, hf⟩ := hSys p D G L h hI
  obtain ⟨hc, hkp, hck, hlin, hcomp, hEF, hsurj⟩ := hsys
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Nat.coprime_zero_left p |>.mp hkp) (Fact.out : Nat.Prime p).one_lt.ne'
    · exact hpos
  refine ⟨k, hkp, fun N => hAdm p D G L h k N hI hk0 hk, ?_⟩
  intro N S _ s o'
  have hρ : gb.ρ = (RingHom.id R) (GenCmp.baseOf gb).ρ := rfl
  have ht : ∀ i, gb.t i = (RingHom.id R).comp ((GenCmp.baseOf gb).t i) := fun i => rfl
  let o1 := GenCmp.toObj hρ ht o' (GenCmp.genericObject_kernelCondition o')
  obtain ⟨o2, ψ, hψm, hψa, hψe, hgal, ⟨hlb⟩, -⟩ :=
    _root_.GlobalTheory.UPel.HT.HeckeAd.exists_isTranslA p D R (GenCmp.baseOf gb) f u c k N N.2.1 N.2.2 hc hkp hck hlin hcomp hEF hsurj S _ o1
  let o3 := GenCmp.rebase (t := s) hρ ht rfl o2
  let o : GObj gb N s := GenCmp.toGObj o3 (GenCmp.geomFull N.2.2 o3)
  refine ⟨o, ψ, ?_⟩
  unfold UpperTheory.Gal.Int.Geo.IsTrans
  haveI := hψm
  haveI : Epi (Over.Hom.left ψ) := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
  haveI : Epi ψ := Over.epi_of_epi_left ψ
  obtain ⟨ψ', hψ'm, hψψ'⟩ := GlobalTheory.HomDescent.exists_desc S o1.A o2.A o1.A
    (HeckeAd.heckeSubA o1 (f (↑N * k)) ↑N) ψ hψm hgal (o1.act.act (k : D.O)) (o1.act.hom _)
    (fun g hg => by
      rw [oActN_act_natCast_eq_one_pow, comp_pow, Category.comp_id, HeckeAd.pow_eq_one_of_mem o1 _ g hg])
  refine ⟨hψm, hψa, ⟨ψ', k, hψ'm, ?_, ?_, ?_, hkp⟩, ?_, ?_⟩
  · intro a
    change o2.act.act a ≫ ψ' = ψ' ≫ o1.act.act a
    apply (cancel_epi ψ).1
    rw [← Category.assoc, ← hψa a, Category.assoc, hψψ', ← Category.assoc, hψψ',
      ← o1.act.mul, ← o1.act.mul, Nat.cast_comm]
  · change ψ ≫ ψ' = 𝟙 o1.A ^ k
    rw [hψψ', oActN_act_natCast_eq_one_pow]
  · change ψ' ≫ ψ = 𝟙 o2.A ^ k
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψψ', oActN_act_natCast_eq_one_pow, pow_comp, comp_pow, Category.id_comp,
      Category.comp_id]
  · obtain ⟨t, t', ht1, ht2, ht3, ht4⟩ := hm
    exact ⟨k ^ 2 / c, Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hck) (Nat.Coprime.pow_left 2 hkp),
      ⟨hlb⟩, t, t', ht1, ht2, ht3, ht4⟩
  · intro kk _ _ t β htβ
    obtain ⟨I', hI'⟩ := o'.geom kk t β htβ
    obtain ⟨J0, hJ0e, hJ0r⟩ := HeckeAd.TateTranslSys.exists_tateIsoO_of_given D (GenCmp.baseOf gb) f u c k
      N hc hkp N.2.1 N.2.2 hck hlin hcomp hEF hsurj o1 o2.A o2.act ψ o2.ab hψm hgal hψa o2.P o2.isLB hlb
      kk t β (GenCmp.tateRestrict I') (fun y => hI' y)
    obtain ⟨I'', hI''⟩ := hFull p D R gb S s N o kk t J0
    have hNpos : 0 < (N : ℕ) := lt_of_lt_of_le (by norm_num) N.2.1
    refine ⟨I', I'', hI', fun y => ?_, ?_⟩
    · rw [hI'' _ hNpos N.2.2, ← hJ0e y]
      change toUnit (Over.mk t) ≫ o2.eta y = _
      rw [hψe y]
    · exact hRel p D G L R gb S s N (↑N * k) o' o kk t I' I'' ψ h f u c k hψm hI
        ⟨hc, hkp, hck, hlin, hcomp, hEF, hsurj⟩ hf
        (fun n hn hnp x => by rw [hI'' n hn hnp]; exact hJ0r n hn hnp x)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDeep =====
