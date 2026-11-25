module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.StatementTBB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactCoefficientAppend
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityConstantOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableBesselFunctionContinuousFami, Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBessel, Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousFrameSection, Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorAestronglyMeasurable, Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftedWordContinuousOnGPos, Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficient

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableBesselFunctionContinuousFami =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableBesselFunctionContinuousFami", "h": "module\n\npublic import Formalism.HermitianCurvature.StatementB\npublic import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory


set_option synthInstance.maxSize 2000 in
theorem besselJ_family_aestronglyMeasurable : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (α : Type) [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α] (μ : Measure α) [SFinite μ] (U : Set α) (γ : α → B.Mat k r) (V : Set (B.Mat k r)) (H : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U → ContinuousOn γ U → (∀ x ∈ U, ∀ q, Bs.inSS q → B.sgs q (γ x) ∈ V) → ContinuousOn H V → AEStronglyMeasurable (fun x => B.JF Bs H (γ x)) (μ.restrict U) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs α _ _ _ _ μ _ U γ V H hU hγ hV hH
  set S : Set (B.SS k r) := {p | Bs.inSS p} with hS
  have hWc := (P.weyl_subgroup_closed k r Bs.z).closed
  have hWc' := (P.weyl_subgroup_closed k r Bs.z').closed
  have hNc := (P.unipotent_radical_closed k r).closed
  have hSc : IsClosed S := by
    have e : S = (fun p : B.SS k r => (p.1.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z) ∩
        ((fun p : B.SS k r => (p.1.2 : B.Mat k r)) ⁻¹' (Nset k r) ∩
          ((fun p : B.SS k r => (p.2.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z') ∩
            (fun p : B.SS k r => (p.2.2 : B.Mat k r)) ⁻¹' (Nset k r))) := by
      ext p; rfl
    rw [e]
    exact (hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter
      ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))
  have hxi : Continuous fun p : B.SS k r => B.xiTau Bs (1, 1) p :=
    (P.B7.continuous_xi Bs).comp (by fun_prop : Continuous fun p : B.SS k r => (((1 : ℝ), (1 : ℝ)), p))
  have hπ : ContinuousOn (fun p : B.SS k r => Bs.π (Matrix.of p.1.1)) S :=
    Bs.π_cont.comp (continuous_fst.fst).continuousOn (fun p hp => hp.1)
  have hinv1 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)
  have hinv2 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)
  have hinv3 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_snd.fst).continuousOn (fun p hp => hp.2.2.1.1)
  have hπ' : ContinuousOn (fun p : B.SS k r => Bs.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    Bs.π'_cont.comp hinv3 (fun p hp => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1)
  have hc4 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) S :=
    (continuous_snd.snd).continuousOn
  have hc5 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) S :=
    (continuous_snd.fst).continuousOn
  have up : ∀ {β : Type} [TopologicalSpace β] {f : B.SS k r → β}, ContinuousOn f S →
      ContinuousOn (fun y : α × B.SS k r => f y.2) (U ×ˢ S) :=
    fun hf => hf.comp continuous_snd.continuousOn (fun y hy => hy.2)
  have hγ' : ContinuousOn (fun y : α × B.SS k r => γ y.1) (U ×ˢ S) :=
    hγ.comp continuous_fst.continuousOn (fun y hy => hy.1)
  have hsgs : ContinuousOn (fun y : α × B.SS k r => B.sgs y.2 (γ y.1)) (U ×ˢ S) :=
    (((((up hinv1).mul (up hinv2)).mul hγ').mul (up hc4)).mul (up hc5))
  have hFs : ContinuousOn (fun y : α × B.SS k r => H (B.sgs y.2 (γ y.1))) (U ×ˢ S) :=
    hH.comp hsgs (fun y hy => hV y.1 hy.1 y.2 hy.2)
  have hcont : ContinuousOn (fun y : α × B.SS k r => D.orbIntegrand Bs (γ y.1) H y.2) (U ×ˢ S) := by
    unfold D.orbIntegrand B.rho
    exact (up hxi.continuousOn).smul ((up hπ).clm_comp (hFs.clm_comp (up hπ')))
  have hW : SigmaFinite Bs.μW := P.Dx2.MN.sigma_of_haar Bs.haarW
  have hW' : SigmaFinite Bs.μW' := P.Dx2.MN.sigma_of_haar Bs.haarW'
  have hN : SigmaFinite Bs.μN := P.Dx2.MN.sigma_of_haar Bs.haarN
  have hsf : SFinite Bs.μSS := by unfold B.RealPlaceData.μSS; infer_instance
  have h1 := hcont.aestronglyMeasurable (μ := μ.prod Bs.μSS) (hU.measurableSet.prod hSc.measurableSet)
  have hae : ∀ᵐ p ∂Bs.μSS, p ∈ S := P.Dx2.OrbJ.ae_inSS Bs
  rw [← Measure.prod_restrict, Measure.restrict_eq_self_of_ae_mem hae] at h1
  have h2 := h1.integral_prod_right'
  have e : (fun x => B.JF Bs H (γ x)) = fun x => ∫ p, D.orbIntegrand Bs (γ x) H p ∂Bs.μSS := by
    funext x
    rw [← P.bessel_function_trivial_index k r Wp Wq Bs H (γ x)]
    rfl
  rw [e]
  exact h2

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableBesselFunctionContinuousFami =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBessel =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBessel", "h": "module\n\npublic import Formalism.HermitianCurvature.StatementTBB\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactCoefficientAppend\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityConstantOfParts\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem vec_bigPt_eq_bessel : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬ ((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → p.V H (TBB.bigPt P.r c) = 0) ∧ (((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → 0 < TBB.Gp p (TBB.bigPt P.r c) ∧ ∀ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) → D.IsDFrame p.T.base p.ν' p.m₀ γ → γ ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H γ) := by
  intro Wp Wq _ _ _ _ _ _ P p H c
  refine ⟨fun hn => ?_, fun ⟨hd, hlt⟩ => ?_⟩
  · show D.vecV p.T.base p.ν' p.m₀ H (TBB.bigPt P.r c) = 0
    unfold D.vecV
    rw [dite_eq_right]
    rintro ⟨hl, hG⟩
    refine hn ⟨fun a => ?_, Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG⟩
    exact (hl.1 (1, c a) (List.mem_ofFn.2 ⟨a, rfl⟩)).2
  · have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hd _
    have hG : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r
        (Formalism.FourierDecayAlt.P.PBJ.bigPt c) := by
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      have hlt' : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) := hlt
      nlinarith [mul_lt_mul_of_pos_left hlt' hp]
    have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    refine ⟨hG, fun γ hγ hZ hD => ?_⟩
    have hZ' : Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := hZ
    have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' γ := by
      rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt c) _ hl hZ']; exact hG
    refine ⟨⟨hγ, hpos⟩, ?_⟩
    show D.vecV p.T.base p.ν' p.m₀ H (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep P.k P.r Wp Wq p.T.base p.ν' p.m₀ H _ hl γ p.hF hG hγ hZ' hD]
    have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt c) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
      Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt c hd)
    obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) hl.2 hl.1
    rw [hw] at hmono
    rw [hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ hpos hnz (hZ'.trans hmono) H]

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBessel =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousFrameSection =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousFrameSection", "h": "module\n\npublic import Formalism.HermitianCurvature.StatementTBB\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityConstantOfParts\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.Finiteness.ModuleFinitePresentation\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

set_option linter.unusedSimpArgs false

noncomputable section

namespace GlobalTheory.FrameSection

def secDiag (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ) :
    Fin (r + 1) → ℂ :=
  fun b => if π b = Fin.last r then ((Real.sqrt (Tz k r z' / Tz k r z) : ℝ) : ℂ) * d0 b else d0 b

def secKappa (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ) : ℝ :=
  Real.sqrt (1 / Real.sqrt (Tz k r z') ^ 2 -
    Real.sqrt (Tz k r z') ^ 2 / Complex.normSq (secDiag k r z z' π d0 (Fin.last r)))

def secMat (k r : ℕ) (z z' ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (π : Equiv.Perm (Fin (r + 1)))
    (d0 : Fin (r + 1) → ℂ) : B.Mat k r :=
  m₀ * smat (Hpk k r) (uB z' ν') (wB z' ν' (Real.sqrt (Tz k r z')))
    (YB π (secDiag k r z z' π d0) z' ν' (Real.sqrt (Tz k r z')) (secKappa k r z z' π d0))

variable {k r : ℕ}

theorem sec_spec {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ)
    (hd0 : ∀ a, d0 a ≠ 0) (hB : π (Fin.last r) = Fin.last r)
    (hG : Tz k r S.z * Tz k r S.z' < Complex.normSq (d0 (Fin.last r))) :
    secMat k r S.z S.z' ν' m₀ π d0 ∈ B.GV k r ∧ Zhat k r S.z S.z' (secMat k r S.z S.z' ν' m₀ π d0) = C2.monoP π d0 ∧
      Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (secMat k r S.z S.z' ν' m₀ π d0) := by
  obtain ⟨hGV, hZ, hFrame, -⟩ := Formalism.FourierDecayAlt.P.Dx2.DF.frameFixLast_spec S ν' m₀ hbase π d0 hd0 hB hG
  exact ⟨hGV, hZ, hFrame⟩

theorem secDiag_cont (z z' : Fin (2 * r + k + 1) → ℂ) (π : Equiv.Perm (Fin (r + 1))) (b : Fin (r + 1)) :
    Continuous fun d0 => secDiag k r z z' π d0 b := by
  unfold secDiag
  split_ifs <;> fun_prop

theorem secDiag_ne {z z' : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (π : Equiv.Perm (Fin (r + 1))) {d0 : Fin (r + 1) → ℂ} (hd0 : ∀ a, d0 a ≠ 0) (b : Fin (r + 1)) :
    secDiag k r z z' π d0 b ≠ 0 := by
  have hμ : 0 < Real.sqrt (Tz k r z' / Tz k r z) := Real.sqrt_pos.2 (div_pos hT' hT)
  have hμ' : ((Real.sqrt (Tz k r z' / Tz k r z) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  unfold secDiag
  split_ifs
  · exact mul_ne_zero hμ' (hd0 b)
  · exact hd0 b

theorem secKappa_cont {z z' : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (π : Equiv.Perm (Fin (r + 1))) :
    ContinuousOn (fun d0 => secKappa k r z z' π d0) {c | ∀ a, c a ≠ 0} := by
  unfold secKappa
  refine ContinuousOn.sqrt (continuousOn_const.sub (continuousOn_const.div ?_ ?_))
  · exact (Complex.continuous_normSq.comp (secDiag_cont z z' π _)).continuousOn
  · intro c hc
    exact (Complex.normSq_pos.2 (secDiag_ne hT hT' π hc _)).ne'

theorem secY_cont {z z' : Fin (2 * r + k + 1) → ℂ} (ν' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') (π : Equiv.Perm (Fin (r + 1))) (s : ℝ) (i : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    ContinuousOn (fun d0 => YB π (secDiag k r z z' π d0) z' ν' s (secKappa k r z z' π d0) i)
      {c | ∀ a, c a ≠ 0} := by
  have hd := fun b => (secDiag_cont z z' π b).continuousOn (s := {c : Fin (r + 1) → ℂ | ∀ a, c a ≠ 0})
  have hκ : ContinuousOn (fun d0 => ((secKappa k r z z' π d0 : ℝ) : ℂ)) {c | ∀ a, c a ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn (secKappa_cont hT hT' π)
  rcases i with ((b | b) | i)
  · simp only [YB]
    fun_prop
  · have h : ContinuousOn (fun d0 => (conj (secDiag k r z z' π d0 b.castSucc))⁻¹)
        {c : Fin (r + 1) → ℂ | ∀ a, c a ≠ 0} := by
      refine ContinuousOn.inv₀ (Complex.continuous_conj.comp_continuousOn (hd _)) ?_
      intro c hc
      simpa using secDiag_ne hT hT' π hc _
    simp only [YB]
    fun_prop
  · fin_cases i
    · simp only [YB, Fin.zero_eta, Matrix.cons_val_zero]
      fun_prop
    · simp only [YB, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      fun_prop

theorem secMat_cont {z z' : Fin (2 * r + k + 1) → ℂ} (ν' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') (m₀ : B.Mat k r) (π : Equiv.Perm (Fin (r + 1))) :
    ContinuousOn (secMat k r z z' ν' m₀ π) {c | ∀ a, c a ≠ 0} := by
  unfold secMat
  refine continuousOn_const.mul ?_
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  simp only [smat, Matrix.of_apply]
  refine continuousOn_pi.1 ?_ a
  unfold smap
  refine continuousOn_const.add (continuousOn_finsetSum _ fun i _ => ?_)
  have h := secY_cont ν' hT hT' π (Real.sqrt (Tz k r z')) i
  fun_prop

theorem ptMatN_bigPt_eq (r : ℕ) (c : Fin (r + 1) → ℂ) :
    D.ptMatN (TBB.bigPt r c) (r + 1) = C2.monoP 1 c := by
  have h : D.ptMatN (TBB.bigPt r c) (r + 1) = U.hMat 1 c := Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt c
  rw [h]
  ext a b
  unfold U.hMat
  rw [Matrix.mul_diagonal]
  by_cases h : a = b
  · subst h; simp [U.wP, C2.monoP]
  · simp [U.wP, C2.monoP, h]

theorem exists_continuous_frame_section :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
      (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r), D.IsBaseFrame Bs ν' m₀ →
      ∃ γ : (Fin (r + 1) → ℂ) → B.Mat k r,
        ContinuousOn γ {c | (∀ a, c a ≠ 0) ∧ Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq (c (Fin.last r))} ∧
        ∀ c : Fin (r + 1) → ℂ, (∀ a, c a ≠ 0) → Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq (c (Fin.last r)) →
          γ c ∈ B.GV k r ∧ Zhat k r Bs.z Bs.z' (γ c) = D.ptMatN (TBB.bigPt r c) (r + 1) ∧
            D.IsDFrame Bs ν' m₀ (γ c) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs ν' m₀ hbase
  refine ⟨secMat k r Bs.z Bs.z' ν' m₀ 1, (secMat_cont ν' Bs.T_pos Bs.T'_pos m₀ 1).mono fun c hc => hc.1, ?_⟩
  intro c hc hG
  rw [ptMatN_bigPt_eq]
  exact sec_spec Bs ν' m₀ hbase 1 c hc rfl hG

end GlobalTheory.FrameSection
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousFrameSection =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorAestronglyMeasurable =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorAestronglyMeasurable", "h": "module\n\npublic import Formalism.HermitianCurvature.StatementTBB\npublic import Formalism.HermitianCurvature.StatementB\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableBesselFunctionContinuousFami\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBessel\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousFrameSection\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem bigCell_vector_aestronglyMeasurable :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ContinuousOn H (B.GPos p.T.base) →
      AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => p.V H (TBB.bigPt P.r c)) volume := by
  intro Wp Wq _ _ _ _ _ _ P p H hH
  classical
  obtain ⟨γ, hγc, hγ⟩ := _root_.GlobalTheory.FrameSection.exists_continuous_frame_section P.k P.r Wp Wq p.T.base p.ν' p.m₀ p.hF
  set U : Set (Fin (P.r + 1) → ℂ) := {c | (∀ a, c a ≠ 0) ∧
    Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r))} with hU
  have hUo : IsOpen U := by
    have h1 : IsOpen {c : Fin (P.r + 1) → ℂ | ∀ a, c a ≠ 0} := by
      rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun a => isOpen_ne_fun (continuous_apply a) continuous_const
    have h2 : IsOpen {c : Fin (P.r + 1) → ℂ |
        Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r))} :=
      isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply _))
    exact h1.inter h2
  have key : ∀ c ∈ U, γ c ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H (γ c) := by
    intro c hc
    obtain ⟨g1, g2, g3⟩ := hγ c hc.1 hc.2
    exact ((_root_.GlobalTheory.vec_bigPt_eq_bessel Wp Wq P p H c).2 hc).2 (γ c) g1 g2 g3
  have hm : AEStronglyMeasurable (fun c => B.JF p.T.base H (γ c)) (volume.restrict U) := by
    refine _root_.GlobalTheory.besselJ_family_aestronglyMeasurable P.k P.r Wp Wq p.T.base _ volume U γ (B.GPos p.T.base) H hUo hγc ?_ hH
    intro c hc q hq
    have h := (key c hc).1
    exact ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem _ hq h.1, by
      rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs _ hq]; exact h.2⟩
  have he : (fun c : Fin (P.r + 1) → ℂ => p.V H (TBB.bigPt P.r c)) =
      U.indicator (fun c => B.JF p.T.base H (γ c)) := by
    funext c
    by_cases hc : c ∈ U
    · rw [Set.indicator_of_mem hc]; exact (key c hc).2
    · rw [Set.indicator_of_notMem hc]; exact (_root_.GlobalTheory.vec_bigPt_eq_bessel Wp Wq P p H c).1 hc
  rw [he]
  exact (aestronglyMeasurable_indicator_iff hUo.measurableSet).2 hm

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorAestronglyMeasurable =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftedWordContinuousOnGPos =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftedWordContinuousOnGPos", "h": "module\n\npublic import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem liftedWord_continuousOn_GPos : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → B.CkOn ⊤ (B.GV P.k P.r) F → ContinuousOn (p.Θ.Θ w e F) (B.GPos p.T.base) := by
  intro Wp Wq _ _ _ _ _ _ P0 p Cb w e F hDD hw hF
  obtain ⟨nf, fib, o, κ, Dop, -, hIn, -, -, hEq⟩ := hDD w hw e
  have hsub : B.GPos p.T.base ⊆ C6.domL p.T.base ∅ :=
    fun g hg => ⟨hg.1, hg.2, fun l hl => by simp at hl⟩
  have hGPG : B.GPos p.T.base ⊆ B.GV P0.k P0.r := fun g hg => hg.1
  have hcont : ContinuousOn (B.opApply Dop F) (B.GPos p.T.base) := by
    apply Formalism.FourierDecayAlt.P.PBE.opApply_continuousOn
    intro T hT
    have h1 : ContinuousOn T.coef (B.GPos p.T.base) :=
      (Formalism.FourierDecayAlt.P.PBE.ckOn_continuousOn' (UU := C6.domL p.T.base ∅) (fun g hg => hg.1) (hIn.1 T hT).1).mono hsub
    have h2 : ContinuousOn (B.Rw T.word F) (B.GPos p.T.base) :=
      (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxG.ckOn_Rw_top hF T.word T.word_lie)).mono hGPG
    exact h1.clm_apply h2
  exact hcont.congr (fun g hg => hEq F g (hsub hg))

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftedWordContinuousOnGPos =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficient =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficient", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorAestronglyMeasurable\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftedWordContinuousOnGPos\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem aesm_pi_of_finite {α ι E : Type} [MeasurableSpace α] {μ : Measure α} [Finite ι] [NormedAddCommGroup E]
    (f : α → ι → E) (hf : ∀ i, AEStronglyMeasurable (fun a => f a i) μ) : AEStronglyMeasurable f μ := by
  classical
  have := Fintype.ofFinite ι
  have e : f = fun a => ∑ i, (Pi.single i (f a i) : ι → E) := by
    funext a; rw [Finset.univ_sum_single]
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (continuous_single (A := fun _ : ι => E) i).comp_aestronglyMeasurable (hf i)

theorem measurable_nPt_bigPt (k r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) = fun c =>
      ∏ i : Fin (r + 1), (if 1 + (i : ℕ) = r + 1 then (‖c (Fin.last r)‖ ^ 2 - TT) ^ (k - 1)
        else ‖c i‖ ^ (2 * (C.Mlev k r (1 + (i : ℕ)) - 2))) := by
    funext c
    unfold TBB.nPt D.ptGG
    rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt, Complex.normSq_eq_norm_sq]
    unfold TBB.bigPt
    rw [Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights]
  rw [e]
  refine Finset.measurable_prod _ fun i _ => ?_
  split_ifs
  · fun_prop
  · exact ((measurable_pi_apply i).norm).pow_const _

theorem measurable_wPt_bigPt (r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c)) = fun c =>
      ‖∏ i, c i‖ ^ 2 / (‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2) := by
    funext c
    show Top.wPt TT r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold Top.wPt D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [e]
  refine Measurable.div ?_ ?_
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ => ‖∏ i, c i‖ ^ 2).measurable
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ =>
      ‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2).measurable

theorem aestronglyMeasurable_tv : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → B.CkOn ⊤ (B.GV P.k P.r) H →
    AEStronglyMeasurable (tv p H w) volume := by
  intro Wp Wq _ _ _ _ _ _ P p Cb H w hD hw hH
  unfold tv
  refine (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable (aesm_pi_of_finite _ fun x => ?_)
  have hV := GlobalTheory.bigCell_vector_aestronglyMeasurable Wp Wq P p _ (GlobalTheory.liftedWord_continuousOn_GPos Wp Wq P p Cb w x.1 H hD hw hH)
  have hc : Continuous fun X : Wq →L[ℂ] Wp => B.hsVec ((p.TP.E x.2).comp X) := by
    unfold B.hsVec
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (p.TP.E x.2).continuous.comp
      (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous
  refine AEStronglyMeasurable.smul (f := fun c : Fin (P.r + 1) → ℂ =>
    ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) x.1 x.2 : ℝ) : ℂ)) ?_ (hc.comp_aestronglyMeasurable hV)
  refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
  refine (measurable_nPt_bigPt _ _ _).sqrt.mul ?_
  unfold Top.dH
  exact (((measurable_wPt_bigPt _ _).pow_const _).mul_const _).sqrt

end GlobalTheory.TopVec
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficient =====
