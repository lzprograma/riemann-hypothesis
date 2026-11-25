module

import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensAtD
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LamGEqOneOfOrtho
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DensLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AbsNormSmallFinite
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Assemble
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensJordanL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensProdValOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FieldDictionaryHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingMassHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsAdmissibleIntegralBasisChangeOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsometryFixFlagAnisotropicVectorOfFixFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocGlobInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalFormIntegralOnLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcArithG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PerpendicularDefinitionHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TotallyPositiveAll
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocDensCorank
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanDecompositionExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ResCharLeAbsNorm
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Summable

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt.AtD

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def EtaLocAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : PlF D, (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then (-1 : ℝ) else 1) = etaF D.host.E D.host.F p.asIdeal

def DensProdValAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D) (c : ℕ), c ≤ 2 * (D.R.rS + 1) →
      Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[(D.s.atP p).Fp])
                (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then -1 else 1) D.R.r (2 * (D.R.rS + 1)) c =
        alphaStd D.host.E p.asIdeal D.R.r / alphaStd D.host.E p.asIdeal (D.R.k - 1 - c)

def DensAllAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) → ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        (Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') →
          (∀ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = alphaStd D.host.E p.asIdeal D.R.r /
            alphaStd D.host.E p.asIdeal (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal)) ∧
          Multipliable (densP L δ ϖ (Tn u) (Tn u') Z)) ∧
        (¬ Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∃ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = 0)

def FormulaExplicitAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) → ∀ Z : MatZ D,
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
          nu (Tn u') F0 what₂ Z = cExpl D F0 what₂ * sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z ^ (D.R.k - 1) *
            ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p

theorem densProdValAt_of (D : Formalism.BasicNotions.D7) (hη : EtaLocAt D) : DensProdValAt D :=
  Formalism.L2.SG.Pf.Cnt.densProdValAt_of hη

theorem densValAt_of (D : Formalism.BasicNotions.D7) (hF : DualityBasisChange.FrameBasisL) (h5 : DensProdValAt D) :
    ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∀ p : PlF D,
          densP L δ ϖ (Tn u) (Tn u') Z p =
            alphaStd D.host.E p.asIdeal D.R.r /
              alphaStd D.host.E p.asIdeal (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal) :=
  Formalism.L2.SG.Pf.Cnt.densValAt_of local_self_dual_holds
    (DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds) h5

theorem densMultIntAt_of (D : Formalism.BasicNotions.D7) (hF : DualityBasisChange.FrameBasisL) (h5 : DensProdValAt D) :
    ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → Multipliable (densP L δ ϖ (Tn u) (Tn u') Z) :=
  Formalism.L2.SG.Pf.Cnt.densMultIntAt_of local_self_dual_holds
    (DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds) h5

theorem densAllAt_of (D : Formalism.BasicNotions.D7) (hF : DualityBasisChange.FrameBasisL) (hη : EtaLocAt D) : DensAllAt D := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP
  have h5 := densProdValAt_of D hη
  exact ⟨fun hI => ⟨fun p => densValAt_of D hF h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p,
      densMultIntAt_of D hF h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI⟩,
    DualityBasisChange.notIntDens_of_steps local_self_dual_holds hF DualityBasisChange.locGlobIntE
      D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP⟩

end Formalism.L2.SG.Pf.Cnt.AtD

namespace Formalism.L2.SG.Pf

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.Asm Formalism.L2.SG.Pf.Cnt.AtD

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem formulaExplicitAt_of (D : Formalism.BasicNotions.D7) (h5 : DensAllAt D) : FormulaExplicitAt D := by
  intro δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z hP
  have h0 := Formalism.L2.SG.Pf.Cnt.field_dictionary_holds
  have h1 := Formalism.L2.SG.Pf.Cnt.rational_pair_holds
  have h2 := Formalism.L2.SG.Pf.Cnt.perpendicular_definition_holds
  have h3 := Formalism.L2.SG.Pf.Cnt.mmChar_of Formalism.L2.SG.Pf.Cnt.local_unimodular_holds
  have h4 := Formalism.L2.SG.Pf.Cnt.lattice_groupoid_holds
  have h6 := PI.UnitaryGroupMassFormula.CntFormula.R6.norm_mass_of_jordan
  have g7 := Formalism.L2.SG.Pf.Cnt.glueExists_holds
  have g9 := Formalism.L2.SG.Pf.Cnt.gluing_mass_holds
  obtain ⟨hK, hF, hN⟩ := h0 D
  obtain ⟨F', hz, hZ⟩ := h1 D u u' hT F0 what₂ hR Z hP
  obtain ⟨hC, hPD, hUr, hWr⟩ := h2 D u u' hT F0 what₂ hR Z F' hz hZ hP
  obtain ⟨hLat, -⟩ := h3 D u u' hT F0 what₂ hR Z F' hz hZ hP
  have e4 := h4 D u u' hT F0 what₂ hR Z F' hz hZ hP
  obtain ⟨h5i, h5n⟩ := h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hnu0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0 → Formalism.L2.SG.CntLocal.nu (Tn u') F0 what₂ Z = 0 := by
    intro h0
    unfold Formalism.L2.SG.CntLocal.nu
    rw [show (∑ Λ ∈ what₂, wRow D F0 Λ) = Formalism.MainNotions.S.Cnt.massRows D F0 what₂ from rfl, h0, div_zero]
  by_cases hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F')
  ·
    have hcJ : ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsMaximal →
        cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭 <
          finrank D.host.E (orthK (VS D).hT (UPair D F0 F')) := by
      intro 𝔭 _
      have := cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭
      rw [hWr]
      omega
    have hne := g7 D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN (UPair D F0 F') hC hPD
      ⟨(VS D).L0, (VS D).standardTuple_isLattice, (VS D).baseLattice_isUnimodular⟩ (MMof D F0 F') hLat hI hcJ
    have hMC : MassConst D.host.E D.host.F (finrank D.host.E (orthK (VS D).hT (UPair D F0 F')))
        (cMass D.host.E D.host.F (D.R.k - 1)) := by
      rw [hWr]
      exact (cMass_spec hK hF (D.R.k - 1) (by omega)).2
    obtain ⟨s, hs1, hs2, hs3, hsum⟩ := g9 D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN
      (UPair D F0 F') hC hPD (MMof D F0 F') hLat hI hne _ hMC
    have e4' := e4 s ⟨hs1, hs2, hs3⟩
    rw [hsum, hWr] at e4'
    obtain ⟨hd, hmult⟩ := h5i hI
    have h6' := h6 D u u' hT F0 what₂ hR Z F' hz hZ hP hI

    have hg : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} =>
        alphaStd D.host.E 𝔭.1 D.R.r /
          alphaStd D.host.E 𝔭.1 (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭.1))
        (∏' p, densP L δ ϖ (Tn u) (Tn u') Z p) := by
      refine (plEquiv (F := D.host.F)).hasProd_iff.mp ?_
      have hh := hmult.hasProd
      convert hh using 1
      funext p
      exact (hd p).symm
    have hl : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} =>
        ∏ i ∈ Finset.Icc D.R.k D.R.r,
          (1 - etaF D.host.E D.host.F 𝔭.1 ^ i * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(i : ℤ)))⁻¹)
        (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i) :=
      hasProd_prod fun i hi => hasProd_lF hK hF i (by simp only [Finset.mem_Icc] at hi; omega)
    have hrk : D.R.k - 1 ≤ D.R.r := by
      show D.R.k - 1 ≤ D.R.k + D.R.m - 1
      omega
    have hT1 : (∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
        alphaStd D.host.E 𝔭.1 (D.R.k - 1) /
          alphaStd D.host.E 𝔭.1 (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭.1)) =
        (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i) *
          ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p := by
      refine HasProd.tprod_eq ?_
      convert hl.mul hg using 1
      funext 𝔭
      rw [alpha_split hK hF 𝔭.2 (by omega) hrk]
      ring
    rw [hT1, h6'] at e4'
    by_cases hm0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0
    · rw [hnu0 hm0]
      unfold cExpl
      rw [hm0, div_zero, zero_mul, zero_mul]
    · have e1 : (|(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ))) ^ (D.R.k - 1) =
          |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ)) := by
        rw [← zpow_natCast, ← zpow_mul]
        congr 1
        push_cast
        ring
      rw [mul_pow, e1] at e4'
      unfold cExpl
      field_simp
      linear_combination e4'
  ·
    have hE := glueSet_eq_empty (U := UPair D F0 F') hI
    have e4' := e4 ∅ (isGlueReps_empty hE)
    rw [Finset.sum_empty] at e4'
    obtain ⟨p, hp⟩ := h5n hI
    have hz0 : ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p = 0 :=
      (hasProd_zero_of_exists_eq_zero ⟨p, hp⟩).tprod_eq
    rw [hz0, mul_zero]
    by_cases hm0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0
    · exact hnu0 hm0
    · exact (mul_eq_zero.mp e4').resolve_right hm0

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem formulaExplicitAt_of_eta (D : Formalism.BasicNotions.D7) (hF : DualityBasisChange.FrameBasisL) (hη : EtaLocAt D) : FormulaExplicitAt D :=
  formulaExplicitAt_of D (densAllAt_of D hF hη)

end Formalism.L2.SG.Pf
