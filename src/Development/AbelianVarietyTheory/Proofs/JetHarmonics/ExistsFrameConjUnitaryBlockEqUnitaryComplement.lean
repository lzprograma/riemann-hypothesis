module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AdaptExists
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.FrameInvMulVecNegativeVector
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFrame

open Formalism.FourierDecayAlt.P.SettingConstruction

section forms
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)

lemma quasi_reflection (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v)
    (hne : Formalism.QuantumDeterminants.herm H u u ≠ Formalism.QuantumDeterminants.herm H u v) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  set d := u - v with hd
  set s := Formalism.QuantumDeterminants.herm H u d with hs
  have hs' : s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H u v := by rw [hs, hd, herm_sub_right]
  have hs0 : s ≠ 0 := by rw [hs']; exact sub_ne_zero.mpr hne
  have hss : star s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H v u := by
    rw [hs, herm_symm H hH, hd, herm_sub_left]
  have hq : Formalism.QuantumDeterminants.herm H d d = s + star s := by
    rw [hss, hs', hd]
    simp only [herm_sub_left, herm_sub_right]
    linear_combination -huv
  set a : ℂ := s⁻¹ with ha'
  have ha : a * s = 1 := inv_mul_cancel₀ hs0
  have hsa : star a * star s = 1 := by rw [← star_mul', ha, star_one]
  refine ⟨rk H d 1 (-a), unitary_of_form H _ fun x y => ?_, ?_, fun x hxu hxv => ?_⟩
  · rw [rk_mulVec, rk_mulVec]
    have hY : star (Formalism.QuantumDeterminants.herm H y d) = Formalism.QuantumDeterminants.herm H d y := herm_symm H hH y d
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, star_mul', hY, hq,
      star_neg, star_one]
    linear_combination (star a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * ha +
      (a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * hsa
  · rw [rk_mulVec, ← hs, neg_mul, ha, hd]
    simp
  · rw [rk_mulVec, hd, herm_sub_right, hxu, hxv]
    simp

lemma exists_isometry (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v) (h0 : Formalism.QuantumDeterminants.herm H u u ≠ 0) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  apply GlobalTheory.CompanionTheory.BmuAdapt.exists_move <;> assumption

end forms

open PI.UpqRep PI.HwUniqW

variable {k r : ℕ}

lemma herm_right_bvec (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.herm (Hpk k r) y (bvec i) = epsI k r i * y (piI k r i) := by
  rw [← Hpk_mulVec_apply]
  simp [Formalism.QuantumDeterminants.herm, bvec, Pi.star_single]

lemma herm_bvec_eq_zero {y : Fin (2 * r + k + 1) → ℂ} (hy : inWb k r y) {i : Fin (2 * r + k + 1)}
    (hi : i.val < r ∨ r + k < i.val) : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec i) y = 0 := by
  rw [← herm_symm _ Hpk_conjTranspose, herm_right_bvec, hy (piI k r i), mul_zero, star_zero]
  rw [piI_val]
  have := i.isLt
  split_ifs <;> omega

lemma exists_isFrameW (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ g, IsFrameW k r z g := by
  set T := Tz k r z with hTdef
  set u : Fin (2 * r + k + 1) → ℂ := ((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)) with hu
  have hw : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) = -1 := by
    have hp : piI k r (wI k r (Fin.last k)) = wI k r (Fin.last k) := by
      unfold piI; rw [ite_eq_left (by simp [wI])]
    rw [herm_right_bvec, hp, bvec_apply, ite_eq_left rfl]
    simp [epsI, wI]
  have huu : Formalism.QuantumDeterminants.herm (Hpk k r) u u = -(T : ℂ) := by
    rw [hu, herm_smul_left, herm_smul_right, hw]
    have h1 : star ((Real.sqrt T : ℝ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ) := Complex.conj_ofReal _
    have h2 : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]
    rw [h1]
    linear_combination -h2
  have hzz : Formalism.QuantumDeterminants.herm (Hpk k r) z z = -(T : ℂ) := by
    have h1 : star (Formalism.QuantumDeterminants.herm (Hpk k r) z z) = Formalism.QuantumDeterminants.herm (Hpk k r) z z :=
      herm_symm _ Hpk_conjTranspose z z
    have h2 : T = -(Formalism.QuantumDeterminants.herm (Hpk k r) z z).re := rfl
    rw [h2, Complex.ofReal_neg, neg_neg]
    exact (Complex.conj_eq_iff_re.mp h1).symm
  have huW : inWb k r u := by
    intro i hi
    rw [hu, Pi.smul_apply, bvec_apply, ite_eq_right, smul_zero]
    rintro rfl
    simp [wI] at hi
  obtain ⟨g, h1, h2, h3⟩ := exists_isometry (Hpk k r) Hpk_conjTranspose u z (huu.trans hzz.symm) (by
    rw [huu, neg_ne_zero]; exact_mod_cast hT.ne')
  refine ⟨g, h1, fun a => ⟨?_, ?_⟩, h2⟩
  · have ha : (eI k r a).val < r ∨ r + k < (eI k r a).val := Or.inl a.isLt
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)
  · have ha : (esI k r a).val < r ∨ r + k < (esI k r a).val := by
      have := a.isLt
      right; simp only [esI]; omega
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)

lemma blockW_fix (x : Matrix (Fin k) (Fin k) ℂ) {j : Fin (2 * r + k + 1)} (hj : ¬ InB k r j) :
    blockW k r x *ᵥ bvec j = bvec j := by
  funext i
  rw [mulVec_bvec_apply, bvec_apply]
  by_cases hi : InB k r i
  · rw [blockW_in_out _ hi hj, ite_eq_right (ne_of_inB hi hj)]
  · rw [blockW_out _ hi]

lemma blockW_mem_UH {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    blockW k r x ∈ UH (Hpk k r) := by
  show (blockW k r x)ᴴ * Hpk k r * blockW k r x = Hpk k r
  rw [blockW_conjTranspose, ← Hpk_blockW_comm, Matrix.mul_assoc, blockW_mul, mem_UJset_allPos.mp hx,
    blockW_one, Matrix.mul_one]

lemma conj_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : IsFrameW k r z g) {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    g * blockW k r x * g⁻¹ ∈ UWset k r z := by
  refine ⟨mul_mem_UH (mul_mem_UH hg.1 (blockW_mem_UH hx)) (inv_mem_UH hg.1), fun a => ⟨?_, ?_⟩, ?_⟩
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).1,
      blockW_fix x (by unfold InB eI; simp only; omega), (hg.2.1 a).1]
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).2,
      blockW_fix x (by unfold InB esI; simp only; omega), (hg.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, frame_inv_mulVec_negativeVector hg, Matrix.mulVec_smul,
      blockW_fix x (by unfold InB wI; simp), hg.2.2]

theorem frame_exists : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∃ g, PI.UpqRep.IsFrameW k r z g ∧ (∀ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), g * PI.UpqRep.blockW k r x * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z) ∧ ∀ y ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), y = g * PI.UpqRep.blockW k r x * g⁻¹ := by
  intro k r z hz hT
  have hT' : 0 < PI.UpqRep.Tz k r z := hT
  obtain ⟨g, hg⟩ := exists_isFrameW z hz hT'
  refine ⟨g, hg, fun x hx => conj_mem_UW hg hx, fun y hy => ?_⟩
  obtain ⟨x, hx, -, e⟩ := UW_eq_conj hT' hg hy
  exact ⟨x, hx, e⟩

end GlobalTheory.BesselFrame
