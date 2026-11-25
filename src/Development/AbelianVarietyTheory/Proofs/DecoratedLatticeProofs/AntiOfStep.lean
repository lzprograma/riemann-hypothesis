module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizesLe
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Core.Rk.HdNc

theorem anti_of_step {r : ℕ} (f : Fin r → ℝ) (h : ∀ (i : Fin r) (hi : i.1 + 1 < r), f ⟨i.1 + 1, hi⟩ < f i) :
    ∀ a b : Fin r, a ≤ b → f b ≤ f a := by
  cases r with
  | zero => exact fun a => Fin.elim0 a
  | succ r => exact (Fin.strictAnti_iff_succ_lt.mpr fun i => h i.castSucc i.succ.isLt).antitone

theorem lamS_node (R : Ranks) (P : HCParam R) (j : ℕ) (hj : j < R.m) (hi : R.k - 1 + j < R.r) :
    lamS R P ⟨R.k - 1 + j, hi⟩ = -(((P.b ⟨j, hj⟩ : ℚ)) : ℝ) := by
  unfold lamS
  rw [dite_eq_right (by simp only []; omega)]
  have e : R.k - 1 + j - (R.k - 1) = j := by omega
  simp only [e, dite_eq_left hj]

theorem node_of_sign (R : Ranks) (a b : Fin R.r) (hab : a < b) (hne : epsS R a ≠ epsS R b) : R.k ≤ b.1 := by
  by_contra! hb
  apply hne
  have ha : a.1 < R.k - 1 := by
    have : a.1 < b.1 := hab
    omega
  unfold epsS
  rw [ite_eq_left ha]
  by_cases h1 : b.1 < R.k - 1
  · rw [ite_eq_left h1]
  · rw [ite_eq_right h1]
    have : b.1 - (R.k - 1) = 0 := by omega
    simp [this]

theorem gap_lt {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (a b : Fin D.R.r) (hab : a < b) (hne : epsS D.R a ≠ epsS D.R b) :
    Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤ lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b := by
  have hkb := node_of_sign D.R a b hab hne
  have hbr : b.1 < D.R.r := b.2
  have hm2 := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hgap := GlobalTheory.Core.Rk.HdGap.gap_of H τ (b.1 - D.R.k) (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlam, -, -, hCl⟩ := H
  have hstep : ∀ (i : Fin D.R.r) (hi : i.1 + 1 < D.R.r),
      lamS D.R (D.hc τ) ⟨i.1 + 1, hi⟩ < lamS D.R (D.hc τ) i := by
    intro i hi
    have := hlam τ i hi
    have h0 : (0 : ℝ) ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by positivity
    linarith
  set j := b.1 - D.R.k with hj
  have hj1 : j + 1 < D.R.m := by omega
  have e1 : b = ⟨D.R.k - 1 + (j + 1), by omega⟩ := by ext; simp only []; omega
  have hc : (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) ≤ b := by
    rw [Fin.le_def]; simp only []; omega
  have hac : a ≤ (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) := by
    rw [Fin.le_def]; simp only []; have : a.1 < b.1 := hab; omega
  have h1 := anti_of_step _ hstep _ _ hac
  have h2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤
      (((D.hc τ).b ⟨j + 1, hj1⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := hgap
  rw [lamS_node D.R (D.hc τ) j (by omega) (by omega)] at h1
  rw [e1, lamS_node D.R (D.hc τ) (j + 1) hj1 (by omega)]
  linarith

theorem hd_nc : ∃ Cl₀ : ℝ, ∀ (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ), Cl₀ ≤ Cl → HD D L C' Cl Cg cb Cu cT CT →
    ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
  refine ⟨1801, fun D L C' Cl Cg cb Cu cT CT hCl H X => ?_⟩
  have HL := H.2.2.1
  obtain ⟨hS, hr⟩ := GlobalTheory.Core.Rk.HdGap.scale_of hCl HL
  have hr1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast (show 1 ≤ D.R.r by omega)
  have h4 : 100 * (D.R.r : ℝ) ^ 4 ≤ 1801 * (D.R.r : ℝ) ^ 19 := by
    have : (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hr1 (by norm_num)
    have : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 4 := by positivity
    linarith
  have key : ∀ (τ : D.what₂.Tau) (a b : Fin D.R.r), epsS D.R a ≠ epsS D.R b →
      100 * (D.R.r : ℝ) ^ 4 ≤ |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b| := by
    intro τ a b hne
    have hp : (0 : ℝ) ≤ 100 * (D.R.r : ℝ) ^ 4 := by positivity
    rcases lt_trichotomy a b with h | h | h
    · have := gap_lt HL τ a b h hne
      rw [abs_of_nonneg (by linarith)]
      linarith
    · exact absurd (by rw [h]) hne
    · have := gap_lt HL τ b a h (Ne.symm hne)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
  intro v a b hab
  rw [X.eps_eq, X.eps_eq] at hab
  rw [X.lam_eq, X.lam_eq]
  exact key _ _ _ hab

end GlobalTheory.Core.Rk.HdNc
