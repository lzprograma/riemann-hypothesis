module

public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstantCoeffAeval
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.CycloSimple
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PiSeries
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCycloStatement
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCoprimeDvdSub
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.AlgHomPowerSeriesCoeEqAeval, Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EqZeroOfBlockSumEqZero, Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.CycloDist, Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.MapEvalRingHomOfPiFamily, Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PolynomialCoePowerSeriesEqAevalX, Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.RhoUnit, Formalism.SharpRestriction.LevelLetterCocycles.RingStepsOf

-- ===== clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.AlgHomPowerSeriesCoeEqAeval =====
-- clump-header: {"m": "Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.AlgHomPowerSeriesCoeEqAeval", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\npublic import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem rhoUnique : RhoUniqueStatement := by
  intro O S _ _ _ _ _ P hP ρ ρ' hX h0
  have hpoly : ∀ r : Polynomial O, ρ (r : PowerSeries O) = ρ' (r : PowerSeries O) := by
    intro r
    rw [algHom_coe_eq_aeval, algHom_coe_eq_aeval, hX]
  have hdvd : X ∣ ρ (P : PowerSeries O) := by
    rw [PowerSeries.X_dvd_iff, algHom_coe_eq_aeval]
    exact h0
  apply AlgHom.ext
  intro a
  ext n
  have hne : PowerSeries.map (residue O) ((P ^ (n + 1) : Polynomial O) : PowerSeries O) ≠ 0 := by
    rw [← Polynomial.polynomial_map_coe, Ne, Polynomial.coe_eq_zero_iff]
    exact ((hP.monic.pow _).map _).ne_zero
  obtain ⟨q, r, _, hqr⟩ := exists_isWeierstrassDivision a hne
  rw [Polynomial.coe_pow] at hqr
  have hd : ρ a - ρ' a = ρ (P : PowerSeries O) ^ (n + 1) * (ρ q - ρ' q) := by
    rw [hqr, map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, hpoly r, ← hpoly P]
    ring
  have hX' : X ^ (n + 1) ∣ ρ a - ρ' a := by
    rw [hd]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hdvd _) _
  have h1 := (PowerSeries.X_pow_dvd_iff.mp hX') n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at h1
  exact h1

end LevelStatements.Lv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.AlgHomPowerSeriesCoeEqAeval =====

-- ===== clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EqZeroOfBlockSumEqZero =====
-- clump-header: {"m": "Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EqZeroOfBlockSumEqZero", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries

theorem descendDvd : DescendDvdStatement := by
  intro O _ ι m hm hex
  obtain ⟨w, hw⟩ := hex
  let s : Module.End O (PowerSeries O) :=
    ⟨⟨(fun R => w.inv * mk (fun k => coeff (k + m) R)), fun _ _ => mul_add ..⟩,
      fun r _ => mul_smul_comm r ..⟩
  have hX (R : PowerSeries O) : s (ι X * R) = R := by
    have hshift : mk (fun k => coeff (k + m) (ι X * R)) = w * R := by
      ext k
      simp [hw, mul_right_comm]
    change w.inv * _ = R
    rw [hshift]
    exact w.inv_mul_cancel_left R
  let π (Q : PowerSeries O) := mk (fun k => constantCoeff ((s ^ k) Q))
  have hπm (f Q : PowerSeries O) : π (ι f * Q) = f * π Q := by
    ext n
    induction n generalizing f with
    | zero =>
      rw [eq_X_mul_shift_add_const f]
      simp [π, hm.ne', hw, ← algebraMap_eq]
    | succ n ih =>
      rw [eq_X_mul_shift_add_const f]
      simp_all [π, pow_succ, add_mul, mul_assoc,
        ← algebraMap_eq, ← Algebra.smul_def]
  have hπ1 : π 1 = 1 := by
    ext n
    cases n with
    | zero => simp [π]
    | succ n =>
      have hs : s 1 = 0 := by
        change w.inv * _ = 0
        suffices mk (fun k => coeff (k + m) (1 : PowerSeries O)) = 0 by
          rw [this, mul_zero]
        ext k
        simp [hm.ne']
      simp [π, pow_succ, hs]
  have hπι (f : PowerSeries O) : π (ι f) = f := by
    simpa [hπ1] using hπm f 1
  refine ⟨fun f g h => ?_, ?_⟩
  · simpa only [hπι] using congrArg π h
  · rintro p a ⟨Q, hQ⟩
    exact ⟨π Q, by rw [← hπι a, hQ, hπm]⟩

end LevelStatements.Lv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EqZeroOfBlockSumEqZero =====

-- ===== clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.CycloDist =====
-- clump-header: {"m": "Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.CycloDist", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\npublic import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem cycloDist : CycloDistStatement := by
  unfold CycloDistStatement
  intro O _ _ l s hl hlm
  have : Fact l.Prime := ⟨hl⟩
  have hE := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt (p := l) s
  have hXmon : (Polynomial.X + 1 : Polynomial ℤ).Monic := by
    simpa using Polynomial.monic_X_add_C (1 : ℤ)
  have hXdeg : (Polynomial.X + 1 : Polynomial ℤ).natDegree ≠ 0 := by
    rw [← Polynomial.C_1, Polynomial.natDegree_X_add_C]; exact one_ne_zero
  have hPmon : ((Polynomial.cyclotomic (l ^ (s + 1)) ℤ).comp (Polynomial.X + 1)).Monic :=
    (Polynomial.cyclotomic.monic _ ℤ).comp hXmon hXdeg
  have hQ : (Polynomial.cyclotomic (l ^ (s + 1)) O).comp (Polynomial.X + 1) =
      ((Polynomial.cyclotomic (l ^ (s + 1)) ℤ).comp (Polynomial.X + 1)).map (Int.castRingHom O) := by
    simp [Polynomial.map_comp]
  rw [hQ]
  refine { mem := fun {n} hn => ?_, monic := hPmon.map _ }
  rw [hPmon.natDegree_map] at hn
  rw [Polynomial.coeff_map]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hE.mem hn)
  rw [← ha, smul_eq_mul, map_mul]
  exact Ideal.mul_mem_left _ _ (by simpa using hlm)

end LevelStatements.Lv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.CycloDist =====

-- ===== clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.MapEvalRingHomOfPiFamily =====
-- clump-header: {"m": "Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.MapEvalRingHomOfPiFamily", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstantCoeffAeval\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.CycloDist\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.CycloSimple\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PiSeries\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

def ofPiFamily {LL ι : Type} [CommRing LL] (f : ι → PowerSeries LL) :
    PowerSeries (ι → LL) :=
  PowerSeries.mk fun n i => coeff n (f i)

theorem map_evalRingHom_ofPiFamily {LL ι : Type} [CommRing LL] (f : ι → PowerSeries LL) (i : ι) :
    PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) (ofPiFamily f) = f i := by
  ext n
  simp [ofPiFamily, PowerSeries.coeff_map, PowerSeries.coeff_mk]

theorem ext_evalRingHom {LL ι : Type} [CommRing LL] {F G : PowerSeries (ι → LL)}
    (h : ∀ i, PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F =
      PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) G) : F = G := by
  ext n i
  have h' : coeff n (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F) =
      coeff n (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) G) := by rw [h i]
  simpa [PowerSeries.coeff_map] using h'

def piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) : PowerSeries O →ₐ[O] PowerSeries (ι → LL) where
  toFun a := ofPiFamily fun i => ρ i a
  map_one' := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_mul' a b := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_zero' := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_add' a b := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  commutes' c := ext_evalRingHom fun i => by
    rw [map_evalRingHom_ofPiFamily, AlgHom.commutes]
    ext n
    simp [PowerSeries.algebraMap_apply, coeff_C]

theorem map_evalRingHom_piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) (i : ι) (a : PowerSeries O) :
    PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) (piAlgHom ρ a) = ρ i a := by
  first
    | exact map_evalRingHom_ofPiFamily (fun i => ρ i a) i

theorem constantCoeff_piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) (i : ι) (a : PowerSeries O) :
    constantCoeff (piAlgHom ρ a) i = constantCoeff (ρ i a) := by
  rw [← map_evalRingHom_piAlgHom ρ i a, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
  rfl

theorem cyclotomic_comp_dvd {LL : Type} [Field LL] (n : ℕ) (hn : 0 < n) (ζ₀ : LL)
    (hζ₀ : IsPrimitiveRoot ζ₀ n) (r : Polynomial LL)
    (hr : ∀ ζ, IsPrimitiveRoot ζ n → r.eval (ζ - 1) = 0) :
    (Polynomial.cyclotomic n LL).comp (Polynomial.X + 1) ∣ r := by
  classical
  have hdiv : Polynomial.cyclotomic n LL ∣ r.comp (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ₀]
    apply Finset.prod_dvd_of_coprime
    · exact (Polynomial.pairwise_coprime_X_sub_C Function.injective_id).set_pairwise _
    · intro μ hμ
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_comp]
      simpa using hr μ ((mem_primitiveRoots hn).mp hμ)
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c.comp (Polynomial.X + 1), ?_⟩
  have hback : (r.comp (Polynomial.X - 1)).comp (Polynomial.X + 1) = r := by
    rw [Polynomial.comp_assoc]
    simp
  rw [← hback, hc, Polynomial.mul_comp]

private theorem cyclotomic_comp_pow_dvd_of_X_pow_dvd {O LL : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Field LL] [CharZero LL]
    [Algebra O LL] [IsFractionRing O LL] (n : ℕ) (hn : 0 < n) (ζ₀ : LL)
    (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hP : ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).IsDistinguishedAt (maximalIdeal O))
    (ρ : LL → (PowerSeries O →ₐ[O] PowerSeries LL))
    (hρ : ∀ ζ, IsPrimitiveRoot ζ n → 1 + ρ ζ X = C ζ * PowerSeries.exp LL)
    (k : ℕ) (a : PowerSeries O)
    (hk : ∀ ζ, IsPrimitiveRoot ζ n → (X : PowerSeries LL) ^ k ∣ ρ ζ a) :
    (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) ^ k ∣ a := by
  classical
  have hexp0 : constantCoeff (PowerSeries.exp LL) = 1 := PowerSeries.constantCoeff_exp
  have hcyc : ∀ z : PowerSeries LL, Polynomial.aeval z (Polynomial.cyclotomic n O) =
      Polynomial.aeval z (Polynomial.cyclotomic n LL) := by
    intro z
    first
      | rw [← Polynomial.map_cyclotomic n (algebraMap O LL), Polynomial.aeval_map_algebraMap]
  have hunit : ∀ ζ, IsPrimitiveRoot ζ n → ∃ w : (PowerSeries LL)ˣ,
      ρ ζ (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
        (w : PowerSeries LL) * X := by
    intro ζ hζ
    have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic n LL) = 0 := by
      rw [Polynomial.coe_aeval_eq_eval]
      have : NeZero (n : LL) := ⟨by exact_mod_cast hn.ne'⟩
      first
        | exact Polynomial.isRoot_cyclotomic_iff.mpr hζ
    obtain ⟨w, hw⟩ := cycloSimple LL LL n hn ζ (PowerSeries.exp LL) hroot hexp0
      (PowerSeries.derivative_exp LL)
    refine ⟨w, ?_⟩
    rw [algHom_coe_eq_aeval, Polynomial.aeval_comp]
    have h1 : Polynomial.aeval (ρ ζ X) (Polynomial.X + 1 : Polynomial O) =
        C ζ * PowerSeries.exp LL := by
      rw [map_add (f := _), Polynomial.aeval_X, map_one, add_comm]
      exact hρ ζ hζ
    rw [h1, hcyc]
    exact hw
  choose! w hw using hunit
  have hWu : IsUnit (ofPiFamily fun i : {ζ : LL // IsPrimitiveRoot ζ n} => (w i.1 : PowerSeries LL)) :=
    ((piSeries LL {ζ : LL // IsPrimitiveRoot ζ n}).2 _).2.mpr fun i => by
      rw [map_evalRingHom_ofPiFamily]
      exact (w i.1).isUnit
  have hρP : piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1)
      (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
        (hWu.unit : PowerSeries ({ζ : LL // IsPrimitiveRoot ζ n} → LL)) * X := by
    rw [IsUnit.unit_spec]
    apply ext_evalRingHom
    intro i
    rw [map_evalRingHom_piAlgHom, map_mul, map_evalRingHom_ofPiFamily, PowerSeries.map_X]
    exact hw i.1 i.2
  have hcc : ∀ i : {ζ : LL // IsPrimitiveRoot ζ n},
      constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X) i = i.1 - 1 := by
    intro i
    rw [constantCoeff_piAlgHom]
    have h : constantCoeff (1 + ρ i.1 X) = constantCoeff (C i.1 * PowerSeries.exp LL) := by
      rw [hρ i.1 i.2]
    rw [map_add (f := _), map_one, map_mul, constantCoeff_C, hexp0, mul_one] at h
    linear_combination h
  have hroots : ∀ r : Polynomial LL,
      Polynomial.aeval (constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r = 0 →
        ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).map (algebraMap O LL) ∣ r := by
    intro r hr
    have hmap : ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).map (algebraMap O LL) =
        (Polynomial.cyclotomic n LL).comp (Polynomial.X + 1) := by
      rw [Polynomial.map_comp, Polynomial.map_cyclotomic, Polynomial.map_add (f := _), Polynomial.map_X,
        Polynomial.map_one]
    rw [hmap]
    apply cyclotomic_comp_dvd n hn ζ₀ hζ₀ r
    intro ζ hζ
    have h : (Polynomial.aeval (constantCoeff (piAlgHom
        (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r) ⟨ζ, hζ⟩ = 0 := by
      rw [hr]
      rfl
    rw [show (Polynomial.aeval (constantCoeff (piAlgHom
        (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r) ⟨ζ, hζ⟩ =
        Polynomial.aeval (constantCoeff (piAlgHom
          (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X) ⟨ζ, hζ⟩) r from
        (Polynomial.aeval_algHom_apply (Pi.evalAlgHom LL (fun _ : {ζ : LL // IsPrimitiveRoot ζ n} => LL)
          ⟨ζ, hζ⟩) _ r).symm, hcc, Polynomial.coe_aeval_eq_eval] at h
    exact h
  have hXk : (X : PowerSeries ({ζ : LL // IsPrimitiveRoot ζ n} → LL)) ^ k ∣
      piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) a :=
    (((piSeries LL {ζ : LL // IsPrimitiveRoot ζ n}).2 _).1 k).mpr fun i => by
      rw [map_evalRingHom_piAlgHom]
      exact hk i.1 i.2
  exact rhoCompl O LL ({ζ : LL // IsPrimitiveRoot ζ n} → LL) _ hP
    (piAlgHom fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) ⟨hWu.unit, hρP⟩ hroots k a hXk

theorem splitCompl : SplitComplStatement := by
  unfold SplitComplStatement
  intro O LL _ _ _ _ _ _ _ _ l s hl hlm hζ0 ρ hρ k a hk
  obtain ⟨ζ₀, hζ₀⟩ := hζ0
  exact cyclotomic_comp_pow_dvd_of_X_pow_dvd (l ^ (s + 1)) (pow_pos hl.pos _) ζ₀ hζ₀
    (cycloDist O l s hl hlm) ρ hρ k a hk

end LevelStatements.Lv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.MapEvalRingHomOfPiFamily =====

-- ===== clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PolynomialCoePowerSeriesEqAevalX =====
-- clump-header: {"m": "Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PolynomialCoePowerSeriesEqAevalX", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCycloStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries

theorem polynomial_coe_powerSeries_eq_aeval_X {O : Type*} [CommRing O] (P : Polynomial O) :
    (P : PowerSeries O) = Polynomial.aeval (X : PowerSeries O) P := by
  rw [Polynomial.aeval_def]
  exact Polynomial.eval₂_C_X_eq_coe.symm

theorem psCyclo_step {O : Type*} [CommRing O] (l : ℕ) (hl : l.Prime)
    (φ : PowerSeries O →ₐ[O] PowerSeries O) (hφ : φ X = (1 + X) ^ l - 1) (m : ℕ) (hm : l ∣ m) :
    φ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
      (((Polynomial.cyclotomic (m * l) O).comp (Polynomial.X + 1) : Polynomial O) :
        PowerSeries O) := by
  rw [algHom_coe_eq_aeval, polynomial_coe_powerSeries_eq_aeval_X,
    ← Polynomial.cyclotomic_expand_eq_cyclotomic hl hm]
  simp only [Polynomial.aeval_comp, Polynomial.expand_aeval, hφ, map_add (f := _), Polynomial.aeval_X,
    map_one]
  exact congrArg (fun y => Polynomial.aeval y (Polynomial.cyclotomic m O)) (by ring)

theorem psCyclo : PsCycloStatement := by
  unfold PsCycloStatement
  intro O _ l hl φ hφ q w hq s
  induction s with
  | zero => exact ⟨w, by rw [Function.iterate_zero_apply, zero_add, pow_one]; exact hq⟩
  | succ s ih =>
    obtain ⟨w', hw'⟩ := ih
    refine ⟨Units.map (φ : PowerSeries O →* PowerSeries O) w', ?_⟩
    rw [Function.iterate_succ_apply', hw', map_mul,
      psCyclo_step l hl φ hφ (l ^ (s + 1)) (dvd_pow_self l (Nat.succ_ne_zero s)),
      ← pow_succ]
    simp

end LevelStatements.Lv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PolynomialCoePowerSeriesEqAevalX =====

-- ===== clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.RhoUnit =====
-- clump-header: {"m": "Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.RhoUnit", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem rhoUnit : RhoUnitStatement := by
  unfold RhoUnitStatement
  intro O S _ _ _ ρ p a c hp hc hmem
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hmem
  have hcc : constantCoeff (ρ (C c)) = algebraMap O S c := by
    rw [PowerSeries.C_eq_algebraMap, AlgHom.commutes, PowerSeries.algebraMap_apply,
      constantCoeff_C]
  have h2 : constantCoeff (ρ v) * constantCoeff (ρ a) = algebraMap O S c := by
    rw [← hcc, ← huv]
    simp only [map_add (f := _), map_mul, hp, mul_zero, zero_add]
  rw [← h2] at hc
  exact PowerSeries.isUnit_iff_constantCoeff.mpr (IsUnit.mul_iff.mp hc).2

end LevelStatements.Lv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.RhoUnit =====

-- ===== clump member: Formalism.SharpRestriction.LevelLetterCocycles.RingStepsOf =====
-- clump-header: {"m": "Formalism.SharpRestriction.LevelLetterCocycles.RingStepsOf", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.AlgHomPowerSeriesCoeEqAeval\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.CycloSimple\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EqZeroOfBlockSumEqZero\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.MapEvalRingHomOfPiFamily\nimport Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PiSeries\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PolynomialCoePowerSeriesEqAevalX\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCoprimeDvdSub\npublic import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.RhoUnit\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G PowerSeries IsLocalRing

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem ringSteps_of [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {Λ κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (f' : PowerSeries O) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (η : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (hℓ2 : PD.p ≠ 2) (hℓm : (PD.p : O) ∈ maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n0))
    (G1 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι X = (w : PowerSeries O) * X ^ (PD.p - 1))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ X = (1 + X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL, 1 + rhoZ W c ζ X = PowerSeries.C ζ * exp LL)
    (huZ : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a) :
    (lvModel Hy f' kind b η).K1b ∧ (lvModel Hy f' kind b η).HasU (W.χΓ W.gam) ∧
      (∀ s < ell, ((lvModel Hy f' kind b η).lev s).FiniteOrderFixed (baseIdOf hR).Bs.ℓ s ∧
        ((lvModel Hy f' kind b η).lev s).PhiGammaCommute) ∧
      (lvModel Hy f' kind b η).UnitsAt ∧ (lvModel Hy f' kind b η).Compl ϖ := by
  obtain ⟨w, hw⟩ := G1
  exact LevelStatements.Link.linkRing LevelStatements.Lv.rhoUnique LevelStatements.Lv.splitCompl LevelStatements.Lv.cycloSimple
    LevelStatements.Lv.psCoprime LevelStatements.Lv.rhoUnit LevelStatements.Lv.descendDvd LevelStatements.Lv.piSeries ϖ hϖ
    (lvData Hy f' kind b η) (hℓ := ⟨PD.hp⟩) hℓ2 hℓm n0 hn0 hroot (baseIdOf hR).ι w hw W.φ₀ hφ
    (baseIdOf hR).ι_φ LevelStatements.Lv.psCyclo G2 (rhoZ W c) hρζ (lvModel Hy f' kind b η)
    (fun s _ a ζ => map_eval_rhoL hR c s a ζ) (W.χΓ W.gam) (uZ : ℤ_[PD.p]) huZ ιZ hutie
    (fun _ _ => rfl)
    (fun s _ f ζ ζ' h => by
      change f (powR LL PD.p s _ ζ) = f ζ'
      congr 1
      apply Subtype.ext
      rw [h]
      rfl)
    (fun j => (j.1 : ℤ_[PD.p]))
    (fun j => (by simpa using congrArg (fun x : ℤ_[PD.p]ˣ => (x : ℤ_[PD.p])) j.2 :
      ((j.1 : ℤ_[PD.p])) ^ (PD.p - 1) = 1))
    hom'
    (fun s _ j f ζ ζ' h => by
      change f (powR LL PD.p s _ ζ) = f ζ'
      congr 1
      apply Subtype.ext
      rw [h]
      rfl)

end Formalism.MainNotions.N.Ln03
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.LevelLetterCocycles.RingStepsOf =====
