module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramSchmidtLengths
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
public import Formalism.FormalDegreeBessel.FinalG
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationAbsoluteSidePieceBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselZhatInvAndRegularIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableAndNormAmplitudeLeOfPairings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeDegenerateOperatorNormLeRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormRootMeasureHaarUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberAndFibreSetsMeasurable
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLe, Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBoundByDyadicSummation, Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopMinorAndGramNumberLeMajorantLengths, Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberMulTopMinorNormLeTwoPow, Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeAbsolutelyConvergentOperatorNormLe

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLe =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLe", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\npublic import Mathlib.Analysis.Complex.ExponentialBounds\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem absArith_const (r : ℕ) (hr : 1 ≤ r) :
    (4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r) *
      Real.exp 1 ^ (r * (r + 2)) ≤ (4 * r : ℝ) ^ (44 * r ^ 3) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h4 : (4 : ℝ) ≤ 4 * r := by linarith
  have h1 : ((r : ℝ) + 1) * 24 ≤ (4 * r : ℝ) ^ 3 := by
    have : (r : ℝ) ≤ (r : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
    nlinarith
  have he : Real.exp 1 ≤ 4 * r := by
    have := Real.exp_one_lt_d9
    linarith
  have hexp : 11 * r ^ 2 + 3 + (24 * r ^ 3 + 1) + 2 * r + r * (r + 2) ≤ 44 * r ^ 3 := by
    have a1 : r ≤ r ^ 3 := Nat.le_self_pow (by norm_num) r
    have a2 : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right hr (by norm_num)
    nlinarith
  calc _ ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * (4 * r : ℝ) ^ 3 * (4 * r : ℝ) ^ (24 * r ^ 3 + 1) *
        (4 * r : ℝ) ^ (2 * r) * (4 * r : ℝ) ^ (r * (r + 2)) := by
        gcongr
        linarith
    _ = (4 * r : ℝ) ^ (11 * r ^ 2 + 3 + (24 * r ^ 3 + 1) + 2 * r + r * (r + 2)) := by
        simp only [pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hexp

theorem absArith_shift (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ m * (2 ^ r) ^ m ≤
      Real.exp 1 ^ (r * (r + 2)) *
        (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < ((m + r + 2 : ℕ) : ℝ) := by positivity
  have hpe : 0 < Real.pi * Real.exp 1 := by positivity
  have h1 : (((m + r + 2 : ℕ) : ℝ) / m) ^ m ≤ Real.exp 1 ^ (r + 2) := by
    have h2 : ((m + r + 2 : ℕ) : ℝ) / m ≤ Real.exp (((r + 2 : ℕ) : ℝ) / m) := by
      have := Real.add_one_le_exp (((r + 2 : ℕ) : ℝ) / m)
      refine le_trans (le_of_eq ?_) this
      push_cast
      field_simp
      ring
    calc _ ≤ Real.exp (((r + 2 : ℕ) : ℝ) / m) ^ m := by gcongr
      _ = Real.exp 1 ^ (r + 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        field_simp
  have h3 : (((m + r + 2 : ℕ) : ℝ) / m) ^ (r * m) ≤ Real.exp 1 ^ (r * (r + 2)) := by
    rw [mul_comm r m, mul_comm r (r + 2), pow_mul, pow_mul]
    gcongr
  have h4 : (4 : ℝ) ^ m ≤ 4 ^ (r * m) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left m hr)
  calc _ ≤ (Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ (r * m) * (2 ^ r) ^ m := by gcongr
    _ = (((m + r + 2 : ℕ) : ℝ) / m) ^ (r * m) *
        (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) := by
        rw [← pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]
        congr 1
        field_simp
        ring
    _ ≤ _ := by gcongr

theorem absArith : ∀ (k r : ℕ) (H₁ De D : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 1 ≤ H₁ → 1 ≤ De → 0 < D → ((4 * r : ℝ) ^ (11 * r ^ 2) * De ^ (12 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * 4 ^ (k - 2 - r) * ((r + 1) * 4 ^ (24 * r ^ 3 + 1))) * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ (k - 2 - r) ≤ absBd k r H₁ De D := by
  intro k r H₁ De D hr hk hH hDe hD
  obtain ⟨m, rfl⟩ : ∃ m, k = m + r + 2 := ⟨k - 2 - r, by omega⟩
  have hm : 1 ≤ m := by omega
  have hmk : m + r + 2 - 2 - r = m := by omega
  unfold absBd
  rw [hmk]
  have hA := absArith_const r hr
  have hB := absArith_shift r m hr hm
  have hC : De ^ (12 * r ^ 2) * De ^ (2 * r) ≤ De ^ (14 * r ^ 2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hDe (by nlinarith)
  have hH0 : 0 ≤ H₁ := by linarith
  have hDe0 : 0 ≤ De := by linarith
  calc _ = ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r)) *
        ((Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ m * (2 ^ r) ^ m) *
        (De ^ (12 * r ^ 2) * De ^ (2 * r)) * H₁ ^ (24 * r ^ 3) * (D ^ m)⁻¹ := by
        rw [div_pow (2 ^ r : ℝ) D m, div_eq_mul_inv ((2 ^ r : ℝ) ^ m)]
        ring
    _ ≤ ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r)) *
        (Real.exp 1 ^ (r * (r + 2)) *
          (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m)) *
        De ^ (14 * r ^ 2) * H₁ ^ (24 * r ^ 3) * (D ^ m)⁻¹ := by gcongr
    _ = ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r) *
        Real.exp 1 ^ (r * (r + 2))) * H₁ ^ (24 * r ^ 3) * De ^ (14 * r ^ 2) *
          (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) * (D ^ m)⁻¹ := by
        ac_rfl
    _ ≤ _ := by gcongr

end GlobalTheory.Amp
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLe =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBoundByDyadicSummation =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBoundByDyadicSummation", "h": "module\n\npublic import Mathlib.Analysis.Real.Sqrt\npublic import Mathlib.MeasureTheory.Integral.Lebesgue.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.MeasureTheory.Integral.Lebesgue.Add\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.Dyadic

theorem exists_shell (s H : ℝ) (hH : 0 < H) :
    ∃ i : ℕ, s ≤ 2 ^ i * H ∧ (i = 0 ∨ 2 ^ i * H / 2 < s) := by
  have hex : ∃ i : ℕ, s ≤ 2 ^ i * H := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / H) (one_lt_two (α := ℝ))
    exact ⟨n, ((div_lt_iff₀ hH).1 hn).le⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | j
  · exact Or.inl rfl
  · right
    have := Nat.find_min hex (m := j) (by omega)
    push Not at this
    rw [pow_succ]; linarith

theorem piece_bound (r kk : ℕ) (H De D l l' u v : ℝ) (hr : 1 ≤ r) (hkk : 1 ≤ kk) (hH : 1 ≤ H)
    (hDe : 1 ≤ De) (hD : 0 < D) (hl : 1 ≤ l) (hl' : 1 ≤ l') (hu : 0 < u) (hv : 0 < v)
    (h1 : (r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / u *
      ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / v) * D ≤ 2 ^ r)
    (h2 : D ≤ (l * l' * H) ^ (2 * r)) :
    ((l * l' * H) ^ (10 * r ^ 3) * ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / u) ^ kk *
        (l ^ (24 * r ^ 3 + 1))⁻¹) *
      ((l * l' * H) ^ (10 * r ^ 3) * ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / v) ^ kk *
        (l' ^ (24 * r ^ 3 + 1))⁻¹) ≤
      (r : ℝ) ^ (2 * r) * H ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ kk *
        (l⁻¹ * l'⁻¹ * u⁻¹ * v⁻¹) := by
  have hR : 1 ≤ l * l' * H := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hl hl') hH
  have hRe : (l * l' * H) ^ (24 * r ^ 3) = l ^ (24 * r ^ 3) * l' ^ (24 * r ^ 3) * H ^ (24 * r ^ 3) := by
    rw [mul_pow, mul_pow]
  generalize l * l' * H = R at *
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hT2 : (r * R ^ (2 * r - 1) * De) ^ r * (r * R ^ (2 * r - 1) * De) ^ r * R ^ (2 * r)
      = (r : ℝ) ^ (2 * r) * De ^ (2 * r) * R ^ (4 * r ^ 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [this]
    generalize ((m + 1 : ℕ) : ℝ) = c
    ring
  have hTpos : 0 < (r * R ^ (2 * r - 1) * De) ^ r := by positivity
  generalize (r * R ^ (2 * r - 1) * De) ^ r = T at *
  set P : ℝ := 2 ^ r / D with hP
  have hPpos : 0 < P := by positivity
  set w : ℝ := T / u * (T / v) with hw
  have hwpos : 0 < w := by positivity
  have hwP : w ≤ P := by rw [hP, le_div_iff₀ hD]; exact h1
  have h3 : w ^ kk ≤ P ^ kk * (T * T * R ^ (2 * r) * (u⁻¹ * v⁻¹)) := by
    obtain ⟨m, rfl⟩ : ∃ m, kk = m + 1 := ⟨kk - 1, by omega⟩
    have h4 : w ^ m ≤ P ^ m := pow_le_pow_left₀ hwpos.le hwP m
    have h5 : 1 ≤ P * R ^ (2 * r) := by
      have : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ one_le_two
      calc (1 : ℝ) ≤ 2 ^ r := this
        _ = P * D := by rw [hP]; field_simp
        _ ≤ P * R ^ (2 * r) := by gcongr
    calc w ^ (m + 1) = w ^ m * w * 1 := by ring
      _ ≤ P ^ m * w * (P * R ^ (2 * r)) := by gcongr
      _ = _ := by rw [hw]; ring
  rw [hT2] at h3
  have h6 : R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * R ^ (4 * r ^ 2) ≤ R ^ (24 * r ^ 3) := by
    rw [← pow_add, ← pow_add]
    refine pow_le_pow_right₀ hR ?_
    have : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right hr (by norm_num)
    omega
  have hl0 : 0 < l := by linarith
  have hl0' : 0 < l' := by linarith
  have hR0 : 0 < R := by linarith
  have hDe0 : 0 < De := by linarith
  calc _ = R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * w ^ kk *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by
          rw [hw, mul_pow]; ring
    _ ≤ R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * R ^ (4 * r ^ 2) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by gcongr
    _ = (R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * R ^ (4 * r ^ 2)) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by ac_rfl
    _ ≤ R ^ (24 * r ^ 3) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by gcongr
    _ = _ := by
      rw [hRe, pow_succ l, pow_succ l']
      have e1 : 0 < l ^ (24 * r ^ 3) := by positivity
      have e2 : 0 < l' ^ (24 * r ^ 3) := by positivity
      generalize l ^ (24 * r ^ 3) = a at *
      generalize l' ^ (24 * r ^ 3) = b at *
      generalize H ^ (24 * r ^ 3) = c
      generalize P ^ kk = d
      generalize (r : ℝ) ^ (2 * r) = e
      generalize De ^ (2 * r) = f
      field_simp

theorem dyadic_summation : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r kk : ℕ) (H₁ De D K K' : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ r ∧ D ≤ max (S x) (S' x) ^ (2 * r) ∧ Y x ≤ (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r ∧ Y' x ≤ (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ i * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < S x) ∧ S' x ≤ 2 ^ i' * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * (24 * r ^ 3 + 1)))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ i' * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ / 2 < S' x) ∧ S x ≤ 2 ^ i * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * (24 * r ^ 3 + 1)))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (Real.sqrt (K * K') * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ kk) := by
  intro X _ ν A B S S' Y Y' r kk H De D K K' hA hB hS hS' hY hY' hr hkk hH hDe hD hK hK' hae h1 h2
  have hH0 : 0 < H := by linarith
  have hDe0 : 0 < De := by linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  let T : ℕ → ℕ → ℝ := fun i i' => (r * ((2 : ℝ) ^ i * 2 ^ i' * H) ^ (2 * r - 1) * De) ^ r
  have hT : ∀ i i', 0 < T i i' := fun i i' => by positivity
  let Q : ℕ × ℕ × ℕ × ℕ → Set X := fun p => {x | (0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ r ∧
      D ≤ ((2 : ℝ) ^ p.1 * 2 ^ p.2.1 * H) ^ (2 * r)) ∧
      S x ≤ 2 ^ p.1 * H ∧ (p.1 = 0 ∨ 2 ^ p.1 * H / 2 < S x) ∧
      S' x ≤ 2 ^ p.2.1 * H ∧ (p.2.1 = 0 ∨ 2 ^ p.2.1 * H / 2 < S' x) ∧
      (T p.1 p.2.1 / 2 ^ (p.2.2.1 + 1) < Y x ∧ Y x ≤ 2 * (T p.1 p.2.1 / 2 ^ (p.2.2.1 + 1))) ∧
      (T p.1 p.2.1 / 2 ^ (p.2.2.2 + 1) < Y' x ∧ Y' x ≤ 2 * (T p.1 p.2.1 / 2 ^ (p.2.2.2 + 1)))}
  have hcov : ∀ᵐ x ∂ν, x ∈ ⋃ p, Q p := by
    filter_upwards [hae] with x ⟨_, _, s1, s2, y1, y2, hyy, hd, t1, t2⟩
    obtain ⟨i, hi, hi2⟩ := exists_shell (S x) H hH0
    obtain ⟨i', hi', hi2'⟩ := exists_shell (S' x) H hH0
    have a1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
    have a2 : (1 : ℝ) ≤ 2 ^ i' := one_le_pow₀ one_le_two
    have hm : max (S x) (S' x) ≤ (2 : ℝ) ^ i * 2 ^ i' * H := by
      refine max_le (hi.trans ?_) (hi'.trans ?_)
      · gcongr; exact le_mul_of_one_le_right (by positivity) a2
      · gcongr; exact le_mul_of_one_le_left (by positivity) a1
    have hm0 : 0 ≤ max (S x) (S' x) := le_max_of_le_left (by linarith)
    have hmT : (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r ≤ T i i' := by
      simp only [T]; gcongr
    obtain ⟨a, ha⟩ := GlobalTheory.Amp.dyad_exists_down (T i i') (Y x) y1 (t1.trans hmT)
    obtain ⟨b, hb⟩ := GlobalTheory.Amp.dyad_exists_down (T i i') (Y' x) y2 (t2.trans hmT)
    exact Set.mem_iUnion.2 ⟨(i, i', a, b),
      ⟨y1, y2, hyy, hd.trans (pow_le_pow_left₀ hm0 hm _)⟩, hi, hi2, hi', hi2', ha, hb⟩
  set C : ℝ := Real.sqrt (K * K') * ((r : ℝ) ^ (2 * r) * H ^ (24 * r ^ 3) * De ^ (2 * r) *
    (2 ^ r / D) ^ kk) with hC
  have hC0 : 0 ≤ C := by positivity
  have hpiece : ∀ p : ℕ × ℕ × ℕ × ℕ, ∫⁻ x in Q p, ENNReal.ofReal (A x * B x) ∂ν ≤
      ENNReal.ofReal C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2))) := by
    rintro ⟨i, i', a, b⟩
    rcases (Q (i, i', a, b)).eq_empty_or_nonempty with h | ⟨x0, hx0⟩
    · rw [h]; simp
    obtain ⟨⟨y1, y2, hyy, hd⟩, -, -, -, -, ⟨ha, -⟩, ⟨hb, -⟩⟩ := hx0
    dsimp only at hd ha hb ⊢
    have hTi := hT i i'
    have hyy' : T i i' / 2 ^ (a + 1) * (T i i' / 2 ^ (b + 1)) * D ≤ 2 ^ r := by
      refine le_trans ?_ hyy
      gcongr
    have key := piece_bound r kk H De D (2 ^ i) (2 ^ i') (2 ^ (a + 1)) (2 ^ (b + 1)) hr hkk hH hDe hD
      (one_le_pow₀ one_le_two) (one_le_pow₀ one_le_two) (by positivity) (by positivity) hyy' hd
    have cs := GlobalTheory.Amp.dyad_cauchySchwarz (ν.restrict (Q (i, i', a, b))) A B hA hB
      (Real.sqrt K * (((2 : ℝ) ^ i * 2 ^ i' * H) ^ (10 * r ^ 3) * (T i i' / 2 ^ (a + 1)) ^ kk *
        (((2 : ℝ) ^ i) ^ (24 * r ^ 3 + 1))⁻¹))
      (Real.sqrt K' * (((2 : ℝ) ^ i * 2 ^ i' * H) ^ (10 * r ^ 3) * (T i i' / 2 ^ (b + 1)) ^ kk *
        (((2 : ℝ) ^ i') ^ (24 * r ^ 3 + 1))⁻¹)) (by positivity) (by positivity)
      (by
        refine (lintegral_mono_set ?_).trans
          ((h1 i i' (T i i' / 2 ^ (a + 1)) (by positivity)).trans (le_of_eq ?_))
        · rintro x ⟨-, q1, q2, q3, -, ⟨q4, q5⟩, -⟩
          exact ⟨q1, q2, q3, q4, q5⟩
        · congr 1
          rw [mul_pow (Real.sqrt K), Real.sq_sqrt hK.le, pow_add (2 : ℝ) i i']
          generalize (2 : ℝ) ^ i * 2 ^ i' * H = R
          generalize T i i' / 2 ^ (a + 1) = y
          generalize (2 : ℝ) ^ i = l
          generalize 24 * r ^ 3 + 1 = q
          ring)
      (by
        refine (lintegral_mono_set ?_).trans
          ((h2 i i' (T i i' / 2 ^ (b + 1)) (by positivity)).trans (le_of_eq ?_))
        · rintro x ⟨-, q1, -, q2, q3, -, ⟨q4, q5⟩⟩
          exact ⟨q2, q3, q1, q4, q5⟩
        · congr 1
          rw [mul_pow (Real.sqrt K'), Real.sq_sqrt hK'.le, pow_add (2 : ℝ) i i']
          generalize (2 : ℝ) ^ i * 2 ^ i' * H = R
          generalize T i i' / 2 ^ (b + 1) = y
          generalize (2 : ℝ) ^ i' = l
          generalize 24 * r ^ 3 + 1 = q
          ring)
    refine cs.trans ?_
    have e : ∀ n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = ENNReal.ofReal ((2 ^ n)⁻¹) := fun n => by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.inv_pow]
      simp
    rw [e, e, e, e, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_mul_mul_comm, ← Real.sqrt_mul hK.le, hC, mul_assoc (Real.sqrt (K * K'))]
    refine mul_le_mul_of_nonneg_left (key.trans ?_) (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [mul_assoc, mul_assoc]
    gcongr <;> simp
  calc ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν
      = ∫⁻ x in ⋃ p, Q p, ENNReal.ofReal (A x * B x) ∂ν := by
        rw [Measure.restrict_eq_self_of_ae_mem hcov]
    _ ≤ ∑' p, ∫⁻ x in Q p, ENNReal.ofReal (A x * B x) ∂ν := lintegral_iUnion_le _ _
    _ ≤ _ := ENNReal.tsum_le_tsum hpiece
    _ = ENNReal.ofReal C * 16 := by rw [GlobalTheory.Amp.dyad_tsum_four, mul_comm]
    _ = ENNReal.ofReal (C * 16) := by rw [ENNReal.ofReal_mul hC0]; simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc C * 16 ≤ C * 24 := by gcongr; norm_num
          _ = _ := by rw [hC]; ring

end GlobalTheory.Dyadic
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBoundByDyadicSummation =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeAbsolutelyConvergentOperatorNormLe =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeAbsolutelyConvergentOperatorNormLe", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationAbsoluteSidePieceBound\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLe\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselZhatInvAndRegularIff\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableAndNormAmplitudeLeOfPairings\npublic import Mathlib.Analysis.Real.Sqrt\npublic import Mathlib.MeasureTheory.Integral.Lebesgue.Basic\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBoundByDyadicSummation\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopMinorAndGramNumberLeMajorantLengths\npublic import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberMulTopMinorNormLeTwoPow\nimport Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeDegenerateOperatorNormLeRealPlace\nimport Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormRootMeasureHaarUnimodular\nimport Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberAndFibreSetsMeasurable\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.Monotonicity.Lemmas\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Presheaf\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsConv

variable {k r : ℕ}

theorem dr_inv (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (hγ : γ ∈ GG k r) :
    Dr k r z' z γ⁻¹ = Dr k r z z' γ := by
  unfold Dr
  rw [_root_.GlobalTheory.SgInf.RegInv.dmin_inv z z' hγ, norm_star]

theorem twoFl_inv {z z' : Fin (2 * r + k + 1) → ℂ} {γ : Mat k r} (h : TwoFl k r z z' γ) : TwoFl k r z' z γ⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h2, h1, h4, h3, isClosedSub_GG.2.2.2.2 _ h5, ?_, by rwa [dr_inv z z' h5]⟩
  unfold Gf at h6 ⊢
  rw [_root_.GlobalTheory.SgInf.RegInv.dmin_inv z z' h5, _root_.GlobalTheory.SgInf.RegInv.dmin_inv z z' h5, mul_comm (Tz k r z')]
  simpa only [Complex.star_def, Complex.normSq_conj] using h6

theorem deOK_inv {z z' : Fin (2 * r + k + 1) → ℂ} {γ : Mat k r} {De : ℝ} (hγ : γ ∈ GG k r)
    (h : DeOK k r z z' γ De) : DeOK k r z' z γ⁻¹ De := by
  refine ⟨h.1, fun l hl h0 => ?_⟩
  rw [_root_.GlobalTheory.SgInf.RegInv.dmin_inv z z' hγ] at h0 ⊢
  rw [norm_star]
  exact h.2 l hl fun h' => h0 (by rw [h', star_zero])

def Kc (k r : ℕ) (De : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (11 * r ^ 2) * De ^ (12 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) *
    4 ^ (k - 2 - r) * ((r + 1) * 4 ^ (24 * r ^ 3 + 1))

private theorem side {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {z z' : Fin (2 * r + k + 1) → ℂ} {π' : Mat k r → (Wq →L[ℂ] Wq)} {ψ' : Mat k r → ℂ}
    {μG μW' νS' μR νR : Measure (Mt k r)} {Φ' : Mat k r → Wq} {γ : Mat k r} {c κ s H₁ De : ℝ}
    (hr : 1 ≤ r) (hk : 2 * r + 6 ≤ k) (hκ : 0 < κ) (hs : 0 < s) (hH : 1 ≤ H₁)
    (h1 : OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c) (h2 : MomBd z' νS' Φ' (24 * r ^ 3 + 1) H₁)
    (h3 : TwoFl k r z z' γ) (h4 : DeOK k r z z' γ De) (h5 : NormR k r γ s μR) (h6 : IsQuotMeas μG μR νR)
    (w : Wq) (hw : ‖w‖ = 1) (i i' : ℕ) (y : ℝ) (hy : 0 < y) :
    ∫⁻ x in {x | DegConv.ext0 (Sg k r z') x ≤ 2 ^ i' * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ / 2 < DegConv.ext0 (Sg k r z') x) ∧
        DegConv.ext0 (Sg k r z) (lmulM γ x) ≤ 2 ^ i * H₁ ∧ y < DegConv.ext0 (Yv k r z z' γ) x ∧
        DegConv.ext0 (Yv k r z z' γ) x ≤ 2 * y},
      ENNReal.ofReal (DegConv.ext0 (fun g => ‖⟪w, Φ' g⟫_ℂ‖) x ^ 2) ∂νR ≤
    ENNReal.ofReal (κ / s * Kc k r De * c * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * (k - 2 - r)) *
      (((2 : ℝ) ^ i') ^ (2 * (24 * r ^ 3 + 1)))⁻¹) := by
  have p1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
  have p2 : (1 : ℝ) ≤ 2 ^ i' := one_le_pow₀ one_le_two
  have q1 : (2 : ℝ) ^ i * H₁ ≤ 2 ^ (i + i') * H₁ := by
    rw [pow_add]; gcongr; exact le_mul_of_one_le_right (by positivity) p2
  have q2 : (2 : ℝ) ^ i' * H₁ ≤ 2 ^ (i + i') * H₁ := by
    rw [pow_add]; gcongr; exact le_mul_of_one_le_left (by positivity) p1
  have hR : (1 : ℝ) ≤ 2 ^ (i + i') * H₁ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hH
  have key := (_root_.GlobalTheory.Amp.AbsSide.abs_side k r z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De _ hr hk hκ hs hH h1 h2 h3 h4 h5 h6).2
    w hw i' _ y hR hy
  refine le_trans (lintegral_mono' (Measure.restrict_mono ?_ le_rfl) fun x => ?_) (key.trans (le_of_eq ?_))
  · rintro x ⟨a1, a2, a3, a4, a5⟩
    have hx : Matrix.of x ∈ GG k r := by
      by_contra hx
      rw [DegConv.amplifierAbsConvExtendByZero_of_not_mem _ hx] at a4
      exact lt_asymm hy a4
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ h3.2.2.2.2.1 _ hx
    rw [DegConv.cochainExtendByZeroSubgroup_of_mem _ hx] at a1 a2 a4 a5
    rw [DegConv.cochainExtendByZeroSubgroup_of_mem _ hx'] at a3
    exact ⟨⟨hx, a1.trans q2, a3.trans q1, a4, a5⟩, a2⟩
  · by_cases hx : Matrix.of x ∈ GG k r
    · simp only [DegConv.cochainExtendByZeroSubgroup_of_mem _ hx, le_refl]
    · simp [DegConv.amplifierAbsConvExtendByZero_of_not_mem _ hx]
  · congr 1
    unfold fibVol Kc
    rw [mul_pow 2 y, pow_mul (2 : ℝ) 2]
    norm_num only
    ring

theorem max_bounds {r : ℕ} {S S' D De Y T : ℝ} (hr : 1 ≤ r) (hS : 1 ≤ S) (hDe : 1 ≤ De)
    (hD : D⁻¹ ≤ De) (hT : 0 ≤ T) (hT' : T ≤ max S S') (hY : Y ≤ T ^ r / D) :
    Y ≤ (r * max S S' ^ (2 * r - 1) * De) ^ r := by
  have hM : 1 ≤ max S S' := hS.trans (le_max_left _ _)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : max S S' ≤ r * max S S' ^ (2 * r - 1) :=
    (le_self_pow₀ hM (by omega)).trans (le_mul_of_one_le_left (by positivity) hr')
  calc Y ≤ T ^ r * De := hY.trans (by rw [div_eq_mul_inv]; gcongr)
    _ ≤ (r * max S S' ^ (2 * r - 1)) ^ r * De ^ r := by
        gcongr
        · exact hT'.trans h1
        · exact le_self_pow₀ hDe (by omega)
    _ = _ := (mul_pow _ _ _).symm

theorem abs_core : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (z z' : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → MomBd z νS Φ (24 * r ^ 3 + 1) H₁ → MomBd z' νS' Φ' (24 * r ^ 3 + 1) H₁ → TwoFl k r z z' γ → DeOK k r z z' γ De → NormR k r γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * absBd k r H₁ De (Dr k r z z' γ) := by
  intro k r Wp _ _ _ Wq _ _ _ z z' π π' ψ ψ' μG μW μW' νS νS' μR νR Φ Φ' γ c κ s H₁ De hr hk hκ hs hH o1 o2 m1 m2
    tf de nr qm
  have hγ : γ ∈ GG k r := tf.2.2.2.2.1
  have hG : IsHaarOn (GG k r) μG := o1.2.2.2.2.2.1
  have hc : 0 < c := o1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ : ContinuousOn Φ (GG k r) := o1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ' : ContinuousOn Φ' (GG k r) := o2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have tf' := twoFl_inv tf
  have de' := deOK_inv hγ de
  have nr' := (_root_.GlobalTheory.Amp.RootMeas.normR_facts k r γ s μR hs nr).2.2.2
  have qm' := DegConv.quot_map hγ hG qm
  have hD0 : Dr k r z z' γ ≠ 0 := tf.2.2.2.2.2.2
  have hD : 0 < Dr k r z z' γ := lt_of_le_of_ne (norm_nonneg _) hD0.symm
  have hDe : (Dr k r z z' γ)⁻¹ ≤ De := de.2 ⟨r, by omega⟩ le_rfl (norm_ne_zero_iff.1 hD0)
  have hDe1 : 1 ≤ De := de.1
  have n1 := (_root_.GlobalTheory.Amp.AbsSide.abs_side k r z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De _ hr hk hκ hs hH o2 m2 tf de nr qm).1
  have n2 := (_root_.GlobalTheory.Amp.AbsSide.abs_side k r z' z π ψ μG μW νS _ _ Φ γ⁻¹ c κ s H₁ De _ hr hk hκ hs hH o1 m1 tf' de' nr' qm').1
  rw [MeasurableEquiv.map_apply] at n2
  have a1 : ∀ᵐ x ∂νR, Matrix.of x ∈ GG k r ∧ Yv k r z z' γ (Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n1] with x hx
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not] using hx
  have a2 : ∀ᵐ x ∂νR, Yv k r z' z γ⁻¹ (γ * Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n2] with x hx
    exact fun h => hx (Or.inr h)
  have n0 : νR {x | Matrix.of x ∉ GG k r} = 0 := measure_mono_null (fun x hx => Or.inl hx) n1
  have hkk : 1 ≤ k - 2 - r := by omega
  have hK : 0 < κ / s * Kc k r De * c := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    have : (0 : ℝ) < ((k - 2 - r : ℕ) : ℝ) := by exact_mod_cast hkk
    unfold Kc
    positivity
  have me : Measurable (lmulM γ : Mt k r → Mt k r) := (_root_.GlobalTheory.Amp.StabMeas.cont_lmul γ).measurable
  have main := _root_.GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le k r νR Φ Φ' γ c (κ / s * Kc k r De * c * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) *
    De ^ (2 * r) * (2 ^ r / Dr k r z z' γ) ^ (k - 2 - r)) hγ n0 cΦ cΦ' hc (by positivity) ?_
  · refine ⟨main.1, main.2.trans ?_⟩
    have := _root_.GlobalTheory.Amp.absArith k r H₁ De _ hr hk hH hDe1 hD
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ κ / s))
    unfold Kc
    field_simp
  intro v w hv hw
  have mA : Measurable (DegConv.ext0 fun g => ‖⟪v, Φ g⟫_ℂ‖) := DegConv.measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ).norm
  have mB : Measurable (DegConv.ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) := DegConv.measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ').norm
  have mS : ∀ z, Measurable (DegConv.ext0 (Sg k r z)) := fun z => DegConv.measurable_amplifierAbsConvExtendByZero (_root_.GlobalTheory.Amp.LenCont.lA_Sg_continuousOn k r z).2
  have mY : Measurable (DegConv.ext0 (Yv k r z' z γ⁻¹)) := (_root_.GlobalTheory.Amp.YMeas.yv_measurable k r z' z γ⁻¹ tf'.2.2.2.2.1).1
  have mY' : Measurable (DegConv.ext0 (Yv k r z z' γ)) := (_root_.GlobalTheory.Amp.YMeas.yv_measurable k r z z' γ hγ).1
  have dy := _root_.GlobalTheory.Dyadic.dyadic_summation (Mt k r) νR (fun x => DegConv.ext0 (fun g => ‖⟪v, Φ g⟫_ℂ‖) (lmulM γ x))
    (DegConv.ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) (fun x => DegConv.ext0 (Sg k r z) (lmulM γ x)) (DegConv.ext0 (Sg k r z'))
    (fun x => DegConv.ext0 (Yv k r z' z γ⁻¹) (lmulM γ x)) (DegConv.ext0 (Yv k r z z' γ)) r (k - 2 - r) H₁ De (Dr k r z z' γ) _ _
    (mA.comp me) mB ((mS z).comp me) (mS z') (mY.comp me) mY' hr hkk hH hDe1 hD hK hK ?_ ?_
    (fun i i' y hy => side hr hk hκ hs hH o2 m2 tf de nr qm w hw i i' y hy)
  · rw [Real.sqrt_mul_self hK.le] at dy
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) dy
    filter_upwards [a1] with x hx
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    rw [DegConv.cochainExtendByZeroSubgroup_of_mem _ hx.1, DegConv.cochainExtendByZeroSubgroup_of_mem _ hx']
    rfl
  · filter_upwards [a1, a2] with x hx hx2
    have hx' : γ * Matrix.of x ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    have e1 : ∀ f : Mat k r → ℝ, DegConv.ext0 f (lmulM γ x) = f (γ * Matrix.of x) := fun f => DegConv.cochainExtendByZeroSubgroup_of_mem f hx'
    simp only [e1, DegConv.cochainExtendByZeroSubgroup_of_mem _ hx.1]
    have s1 : 1 ≤ Sg k r z (γ * Matrix.of x) := ((_root_.GlobalTheory.Amp.LInv.lengths_basic k r z tf.1).2.2 _).1
    have s2 : 1 ≤ Sg k r z' (Matrix.of x) := ((_root_.GlobalTheory.Amp.LInv.lengths_basic k r z' tf.2.1).2.2 _).1
    obtain ⟨b1, b2, b3, -⟩ := _root_.GlobalTheory.Amp.MinorBound.minor_gram_bound k r r le_rfl z z' γ tf.1 tf.2.1 hγ _ hx.1
    obtain ⟨-, b5, b6, -⟩ := _root_.GlobalTheory.Amp.MinorBound.minor_gram_bound k r r le_rfl z' z γ⁻¹ tf'.1 tf'.2.1 tf'.2.2.2.2.1 _ hx'
    change Yv k r z' z γ⁻¹ (γ * Matrix.of x) ≤ Sg k r z' (γ⁻¹ * (γ * Matrix.of x)) ^ r / Dr k r z' z γ⁻¹ at b6
    rw [Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ), dr_inv z z' hγ] at b6
    refine ⟨norm_nonneg _, norm_nonneg _, s1, s2, lt_of_le_of_ne b5 hx2.symm, lt_of_le_of_ne b2 hx.2.symm, ?_, ?_,
      max_bounds hr s1 hDe1 hDe (zero_le_one.trans s2) (le_max_right _ _) b6,
      max_bounds hr s1 hDe1 hDe (zero_le_one.trans s1) (le_max_left _ _) b3⟩
    · rw [mul_comm (Yv k r z' z γ⁻¹ _)]
      exact _root_.GlobalTheory.Amp.ExtPow.bound_of_split le_rfl tf.1 tf.2.2.1 hγ
        (fun v hv => ⟨v, hv, by simp [_root_.GlobalTheory.Amp.ExtPow.Low]⟩)
        (fun v hv => ⟨v, hv, by simp [_root_.GlobalTheory.Amp.ExtPow.Low]⟩) hx.1
    · refine (b1 (Fin.last r)).trans ?_
      rw [mul_pow, show ∀ t : ℝ, t ^ (2 * r) = t ^ r * t ^ r from fun t => by ring]
      exact mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans s2) (le_max_right _ _) _)
        (pow_le_pow_left₀ (zero_le_one.trans s1) (le_max_left _ _) _) (pow_nonneg (zero_le_one.trans s1) _)
        (pow_nonneg ((zero_le_one.trans s1).trans (le_max_left _ _)) _)
  · intro i i' y hy
    have h := side hr hk hκ hs hH o1 m1 tf' de' nr' qm' v hv i' i y hy
    rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, add_comm i' i] at h
    refine le_trans (le_of_eq ?_) h
    congr 2
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [show DegConv.lmulEquiv hγ x = lmulM γ x from rfl, DegConv.lmul_inv_lmul hγ]

end GlobalTheory.Amp.AbsConv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeAbsolutelyConvergentOperatorNormLe =====
