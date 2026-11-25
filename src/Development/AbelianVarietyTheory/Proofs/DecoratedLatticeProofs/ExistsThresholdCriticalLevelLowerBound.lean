module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory.CritLevelSize

open Formalism.FourierDecayAlt Finset GlobalTheory.CritLevel

theorem num_bound_pow (k m r e : ℕ) (B P ae c ka : ℝ) (hm : m = 2 * r + 2) (he : 2 * e + 40 ≤ m) (hk : 5 ≤ k)
    (hB : (k : ℝ) ^ 40 ≤ B) (hP : B ^ m ≤ P) (ha0 : 0 < ae) (ha : ae ≤ B ^ e) (hc : 1 / 8 ≤ c) (hka0 : 0 < ka)
    (hka : ka ≤ 4) : (k : ℝ) ^ (3 * r) ≤ c * (ka ^ (m - 1))⁻¹ * P / ae :=
  GlobalTheory.CritLevel.num_bound_pow k m r e B P ae c ka hm (by omega) (by omega) hk hB hP ha0 ha hc hka0 hka

theorem le_pow_ceil (b B u cb Cu : ℝ) (hcb : 0 < cb) (hb : 1 ≤ b) (hB : b ^ cb ≤ B) (hu : u ≤ b ^ Cu) :
    u ≤ B ^ ⌈max Cu 0 / cb⌉₊ := by
  have hB1 : 1 ≤ B := le_trans (Real.one_le_rpow hb hcb.le) hB
  have hM : 0 ≤ max Cu 0 / cb := div_nonneg (le_max_right _ _) hcb.le
  calc u ≤ b ^ Cu := hu
    _ ≤ b ^ max Cu 0 := Real.rpow_le_rpow_of_exponent_le hb (le_max_left _ _)
    _ = (b ^ cb) ^ (max Cu 0 / cb) := by
        rw [← Real.rpow_mul (by linarith)]; congr 1; field_simp
    _ ≤ B ^ (max Cu 0 / cb) := Real.rpow_le_rpow (by positivity) hB hM
    _ ≤ B ^ ((⌈max Cu 0 / cb⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (Nat.le_ceil _)
    _ = B ^ ⌈max Cu 0 / cb⌉₊ := Real.rpow_natCast _ _



theorem tcrit_low_of_sizes (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hcb : 0 < cb)
    (hCl : 2 * ((⌈max Cu 0 / cb⌉₊ + 4 : ℕ) : ℝ) + 40 ≤ Cl)
    (hVV : ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) :
    UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  set e : ℕ := ⌈max Cu 0 / cb⌉₊ + 4 with he
  have hCl40 : (40 : ℝ) ≤ Cl := by linarith [Nat.cast_nonneg (α := ℝ) e]
  refine GlobalTheory.CritLevel.tcrit_low_core D large₂ C' Cl Cg cb Cu cT CT C0 e (by omega) hCl40
    (fun ⟨hH, _, _⟩ => ?_) hVV fun ⟨hH, _, _⟩ u τ ht hB hb hbp hbtop => ?_
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClm, -⟩ := hH
    have hm := GlobalTheory.CritLevel.m_eq D.R
    have hme : 2 * e + 40 ≤ D.R.m := by
      have : ((2 * e + 40 : ℕ) : ℝ) ≤ D.R.m := by push_cast; linarith
      exact_mod_cast this
    omega
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbj, -, hu, -, -, -, -, -, -, -⟩ := hH
    set B := bOne D τ 1
    have hk := D.R.m_add_three_le_k
    have hm2 := D.R.two_le_m
    have hBcb : large₂.sc.b ^ cb ≤ B := (le_max_right _ _).trans (hbj τ 1 le_rfl (by omega)).1
    have hB1 : 1 ≤ B := le_trans (Real.one_le_rpow hb hcb.le) hBcb
    have hu1 : uOne D u τ 1 ≤ B ^ ⌈max Cu 0 / cb⌉₊ := le_pow_ceil _ _ _ _ _ hcb hb hBcb (hu u τ)
    have hpe : B ^ ⌈max Cu 0 / cb⌉₊ * B ≤ B ^ e := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hB1 (by omega)
    calc uOne D u τ 1 * bTop D τ ≤ B ^ ⌈max Cu 0 / cb⌉₊ * B := by gcongr
      _ ≤ B ^ e := hpe

end GlobalTheory.CritLevelSize

theorem GlobalTheory.CritLevelSize.tcritLow_sizes : ∀ cb Cu : ℝ, 0 < cb → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cT CT C0 : ℝ), thr ≤ Cl → (∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) → UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro cb Cu hcb
  exact ⟨2 * ((⌈max Cu 0 / cb⌉₊ + 4 : ℕ) : ℝ) + 40, fun D large₂ C' Cl Cg cT CT C0 hCl hVV =>
    GlobalTheory.CritLevelSize.tcrit_low_of_sizes D large₂ C' Cl Cg cb Cu cT CT C0 hcb hCl hVV⟩
