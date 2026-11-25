module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXLeb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameRow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCR
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXN
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NShear
import Mathlib.CategoryTheory.Countable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNMapKapL, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNBoxOf

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNMapKapL =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNMapKapL", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXLeb\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPlace\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPf\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXMeas\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXN\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NShear\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.CategoryTheory.Countable\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

theorem det_LyM {r k : ℕ} {T : ℝ} (hT : 0 < T) : LinearMap.det (LyM (k := k) (r := r) T) = T ^ r := by
  rw [LyM, LinearMap.det_toLin', Matrix.det_diagonal]
  simp only [Fintype.prod_sum_type, dY, Finset.prod_const_one, one_mul, mul_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [show r * 2 = 2 * r by ring, pow_mul, Real.sq_sqrt hT.le]

theorem refN_map_kapL {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (w a) = 0) :
    AEMeasurable (kapL ε e f w z) (refNg hn ε e f w (z0v T z)) ∧
      (refNg hn ε e f w (z0v T z)).map (kapL ε e f w z) =
        ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k) * (T ^ r)⁻¹) • volume := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hFJ
  obtain ⟨-, hmeasK, hlamK⟩ := lebLoc_core ε e f w z hT hee hff hef hww hew hfw hez hfz hzz hzw
  let Φ : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => WlocSk.NB.phi0 t.1 t.2
  have hH : Formalism.MainNotions.S.haarLie (Nset k r) 1 = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) •
      (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))).map Φ :=
    exponential_chart_haar k r
  have hrefN : refNg rfl ε e f w (z0v T z) = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) •
      Measure.comap (cM (ε := ε) (Qi ε e f w (z0v T z)) (Qm e f w (z0v T z)))
        ((volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))).map Φ) := by
    rw [refNg_rfl]
    ext s _
    show (Measure.comap _ (Formalism.MainNotions.S.haarLie (Nset k r) 1)) s = _
    rw [emb.comap_apply, hH, Measure.smul_apply, Measure.smul_apply, emb.comap_apply]
  refine ⟨?_, ?_⟩
  · rw [hrefN]
    exact hmeasK.smul_measure _
  · rw [hrefN, Measure.map_smul, hlamK, smul_smul, det_LyM hT, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [abs_of_pos (by positivity)]
    exact hmeasK

end Formalism.L2.SG.Pf.NcReal.JX
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNMapKapL =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNBoxOf =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNBoxOf", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameRow\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCR\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNMapKapL\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.CategoryTheory.Countable\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

theorem refNBox_of (hF : FrameRow) : RefNBox := by
  intro D X u w
  choose L hL hdet using fun v => hF X u w v
  have hTu := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u
  have hTw := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) w
  have hdet0 : ∀ v, LinearMap.det (L v) ≠ 0 := fun v h0 => by
    have h1 := hdet v
    rw [h0, abs_zero] at h1
    exact (pow_pos (div_pos hTw hTu) _).ne' h1.symm
  have key : ∀ (s : X.B.I.Ginf) v i, LsNc5.kapV X w v s i =
      L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (s v)) i := fun s v i => by
    have h1 := congrFun (hL v s) i
    rw [kapV_eq (X := X) u v s] at h1
    exact h1
  have hbox : LsNc5.boxN X w = X.NinfU w ∩ Set.univ.pi (fun v =>
      (fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) := by
    rw [LsNc5.boxN_eq]
    congr 1
    ext s
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h v i
      rw [← key s v i]
      exact h (v, i)
    · rintro h ⟨v, i⟩
      show LsNc5.kapV X w v s i ∈ _
      rw [key s v i]
      exact h v i
  have hv : ∀ v, refNX X u v ((fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹'
      Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) =
      ENNReal.ofReal ((2 : ℝ) ^ (D.R.rS ^ 2 + D.R.rS * D.R.k) * (Tw w ^ D.R.rS)⁻¹) := fun v => by
    obtain ⟨hae, hmap⟩ := refN_map_kapL (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v)
      (ProductExactness.zV X u v) hTu (fX_ee (X := X) (v := v)) (fX_ff (X := X) (v := v))
      (fX_ef (X := X) (v := v)) (fX_ww (X := X) (u := u) (v := v)) (fX_ew (X := X) (u := u) (v := v))
      (fX_fw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))
      (fX_fz (X := X) (u := u) (v := v)) (frame_real_z_z_eq_neg (X := X) (u := u) (v := v))
      (fX_zw (X := X) (u := u) (v := v))
    have hmeas : MeasurableSet ((L v) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) :=
      (L v).continuous_of_finiteDimensional.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    have hpre : (fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) =
        kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) ⁻¹' ((L v) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) := rfl
    rw [hpre, show refNX X u v = refNg (nX X) _ _ _ _ _ from rfl, ← Measure.map_apply_of_aemeasurable hae hmeas, hmap,
      Measure.smul_apply, smul_eq_mul, Measure.addHaar_preimage_linearMap _ (hdet0 v), Real.volume_pi_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, mul_one]
    rw [abs_inv, hdet v, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow]
    field_simp
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) hTu (fX_ee (X := X) (v := v)) (fX_ff (X := X) (v := v))
      (fX_ef (X := X) (v := v)) (fX_ww (X := X) (u := u) (v := v)) (fX_ew (X := X) (u := u) (v := v))
      (fX_fw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))
      (fX_fz (X := X) (u := u) (v := v)) (frame_real_z_z_eq_neg (X := X) (u := u) (v := v))
      (fX_zw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))).1
  rw [hbox, Set.inter_comm, measure_inter_conull (refNX_haar X u w).2.2.1, Measure.pi_pi]
  simp only [hv, Finset.prod_const, Finset.card_univ]
  rw [← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [inv_pow, ← inv_pow]
  ring

end Formalism.L2.SG.Pf.NcReal.JX
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNBoxOf =====
