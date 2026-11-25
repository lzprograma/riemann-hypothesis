module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTateMaximalIdealKillsFirstCohomology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerGeneratorMatrixPerturbation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1BallCocycleLogCyclotomic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.TwistKill

variable {l : ℕ} [Fact l.Prime]

open GlobalTheory.Cyc.LogClass

theorem chiC_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (j : ℤ) {h : GQ l}
    (hh : h ∈ Hinf K) : chiC χ j h = 1 := by
  simp [chiC, chi_hinf hχ K hh]


theorem solve {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) (hs : Lev l s) (j : ℤ) (hj : j ≠ 0)
    (γ : GQ l) (hγ : IsGen χ K s γ) (w : PadicComplex l) (hw : w ∈ Ohat K) :
    ∃ z : PadicComplex l, ‖z‖ ≤ 1 ∧ (∀ h ∈ Hinf K, act h z = z) ∧
      chiC χ j γ * act γ z - z = (l : PadicComplex l) ^ (s + padicValInt l j) * w := by
  have hp : l.Prime := Fact.out
  obtain ⟨T1a, -, T1c, -⟩ := _root_.GlobalTheory.TateDecomp.tate_decomposition l act χ ha hχ K s hs.1
  obtain ⟨y, hy, x, hx, rfl⟩ := T1a w hw
  obtain ⟨ζ, hζ, hζK, hζn⟩ := exists_zeta K s hs.1
  have hrho : 0 < rho1 l := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  obtain ⟨v, hv, hv2⟩ := (_root_.GlobalTheory.CycPerturb.perturbation l act χ ha hχ K s hs γ hγ 1 (fun _ => 1)
    (by
      intro a b
      rw [Subsingleton.elim a b, Matrix.one_apply_eq]
      exact ⟨⟨1, (Ks K s).one_mem, by simp⟩, by simp⟩)
    (by intro a b; simpa using hrho) j).2 ζ hζ (fun _ => x) (fun _ => hx)
  have hv3 : chiC χ j γ * act γ (v 0) - v 0 = (ζ - 1) * x := by
    simpa [twAct] using congrFun hv2 0
  have hvO := T1c _ (hv 0)
  set n := s + padicValInt l j with hn
  have hval : ‖chiC χ j γ - 1‖ = ‖(l : PadicComplex l) ^ n‖ := by
    have := _root_.GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l s hs _ hγ.2 j hj
    rw [norm_l_pow, chiC, ← map_one (algebraMap ℚ_[l] (PadicComplex l)), ← map_sub,
      norm_algMap, Units.val_zpow_eq_zpow_val, this, hn]
    push_cast; rfl
  have hl0 : (l : PadicComplex l) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hu0 : chiC χ j γ - 1 ≠ 0 := by
    rw [← norm_ne_zero_iff, hval, norm_ne_zero_iff]; exact pow_ne_zero _ hl0
  have hζ0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one hp.one_lt)
  have hfix : ∀ g ∈ Gj K s, act g ((l : PadicComplex l) ^ n / (chiC χ j γ - 1) * y) =
      (l : PadicComplex l) ^ n / (chiC χ j γ - 1) * y := by
    intro g hg
    have h1 : act g (chiC χ j γ) = chiC χ j γ := act_algebraMap ha g _
    simp only [map_mul, map_div₀, map_pow, map_natCast, map_sub, map_one, h1,
      act_inC ha hg hy.1]
  have hfix2 : ∀ g ∈ Gj K s, act g ((l : PadicComplex l) ^ n / (ζ - 1)) =
      (l : PadicComplex l) ^ n / (ζ - 1) := by
    intro g hg
    simp only [map_div₀, map_pow, map_natCast, map_sub, map_one, act_inC ha hg hζK]
  refine ⟨(l : PadicComplex l) ^ n / (chiC χ j γ - 1) * y + (l : PadicComplex l) ^ n / (ζ - 1) * v 0,
    ?_, ?_, ?_⟩
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_div, hval, div_self (norm_ne_zero_iff.2 (pow_ne_zero _ hl0)), one_mul]
      exact hy.2
    · rw [norm_mul, norm_div]
      refine mul_le_one₀ ?_ (norm_nonneg _) (ohat_norm K hvO)
      rw [div_le_one (norm_pos_iff.2 hζ0), norm_pow]
      refine le_trans ?_ hζn
      have := hs.1
      exact pow_le_of_le_one (norm_nonneg _) norm_l_lt.le (by omega)
  · intro h hh
    rw [map_add (f := _), hfix h (hinf_le_gj K s hh), map_mul (act h) _ (v 0), hfix2 h (hinf_le_gj K s hh),
      (_root_.GlobalTheory.CycInvariants.fixed_iff_mem_Ohat l act ha K _ (ohat_norm K hvO)).2 hvO h hh]
  · rw [map_add (f := _), hfix γ hγ.1, map_mul (act γ) _ (v 0), hfix2 γ hγ.1]
    have e : chiC χ j γ * act γ (v 0) = v 0 + (ζ - 1) * x := by rw [← hv3]; ring
    have e1 : (l : PadicComplex l) ^ n / (chiC χ j γ - 1) * (chiC χ j γ - 1) = l ^ n :=
      div_mul_cancel₀ _ hu0
    have e2 : (l : PadicComplex l) ^ n / (ζ - 1) * (ζ - 1) = l ^ n := div_mul_cancel₀ _ hζ0
    linear_combination y * e1 + x * e2 + ((l : PadicComplex l) ^ n / (ζ - 1)) * e

theorem pow_kills_cyclotomic_H1 (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l))
    (χ : GQ l →* ℚ_[l]ˣ) (ha : IsActC act) (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) (hs : Lev l s)
    (j : ℤ) (hj : j ≠ 0) (c : GQ l → PadicComplex l)
    (hc : CocOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1} c) :
    CobOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1}
      (fun g => (l : PadicComplex l) ^ (1 + s + padicValInt l j) * c g) := by
  have hle := hinf_le_gj K s
  obtain ⟨x, hx, hx2⟩ := _root_.GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary l act ha K 1 (l : PadicComplex l)
    ⟨l, natCast_mem (Kinf K) l, by simp⟩ norm_l_lt (fun g _ => c g)
    ⟨continuousOn_pi.2 fun _ => hc.1.mono hle, fun g hg _ => hc.2.1 g (hle hg),
      fun g hg h hh => by
        funext k
        have := hc.2.2 g (hle hg) h (hle hh)
        simpa [chiC_hinf hχ K j hg] using this⟩
  have hx3 : ∀ h ∈ Hinf K, (l : PadicComplex l) * c h = act h (x 0) - x 0 := fun h hh => by
    simpa using congrFun (hx2 h hh) 0
  have hc1 := modify ha hχ (Gj K s) j 1 c hc (x 0) (hx 0)
  set c1 : GQ l → PadicComplex l :=
    fun g => (l : PadicComplex l) ^ 1 * c g - (chiC χ j g * act g (x 0) - x 0) with hc1def
  have hc1H : ∀ h ∈ Hinf K, c1 h = 0 := fun h hh => by
    simp only [hc1def, pow_one, hx3 h hh, chiC_hinf hχ K j hh, one_mul, sub_self]
  obtain ⟨⟨γ, hγ⟩, hgen⟩ := _root_.GlobalTheory.Cyc.gen_dense l act χ ha hχ K s hs
  have hO : c1 γ ∈ Ohat K := by
    refine (_root_.GlobalTheory.CycInvariants.fixed_iff_mem_Ohat l act ha K _ (hc1.2.1 γ hγ.1)).1 fun h hh => ?_
    have hconj := conj_hinf hχ K s hγ.1 hh
    have e1 := hc1.2.2 h (hle hh) γ hγ.1
    have e2 := hc1.2.2 γ hγ.1 _ (hle hconj)
    have e3 : γ * (γ⁻¹ * h * γ) = h * γ := by group
    rw [e3, e1, hc1H h hh, hc1H _ hconj] at e2
    simpa [chiC_hinf hχ K j hh] using e2
  obtain ⟨z, hz, hzH, hzγ⟩ := solve ha hχ K s hs j hj γ hγ _ hO
  have hc2 := modify ha hχ (Gj K s) j (s + padicValInt l j) c1 hc1 z hz
  have key := vanish (Gj K s) (Hinf K) hle (fun g y => chiC χ j g * act g y)
    (fun g => by simp) _ hc2.1 hc2.2.2 γ hγ.1
    (hgen γ hγ).2.2
    (fun h hh => by simp [hc1H h hh, hzH h hh, chiC_hinf hχ K j hh])
    (by simp only [hzγ, sub_self])
  refine ⟨(l : PadicComplex l) ^ (s + padicValInt l j) * x 0 + z, ?_, fun g hg => ?_⟩
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hz)
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) norm_l_lt.le) (norm_nonneg _) (hx 0)
  · have := key g hg
    simp only [hc1def] at this
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    linear_combination this

end GlobalTheory.Cyc.TwistKill
