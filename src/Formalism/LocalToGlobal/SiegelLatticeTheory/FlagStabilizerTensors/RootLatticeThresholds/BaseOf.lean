module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BuiltPf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TopsChoicePartA

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BaseOf

variable {k r : ℕ}

section Place

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

variable {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ)

def Qc (v : InfinitePlace X.B.I.F) : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ := Qcs C (X.pl v)
def Qic (v : InfinitePlace X.B.I.F) : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ := Qics C (X.pl v)

theorem transpC (v : InfinitePlace X.B.I.F) : IsTranspC X v (cfS D) D.R.k D.R.rS (Qc X C v) (Qic X C v) := by
  have h := Formalism.L2.SG.Pf.torTie X (vOf X (X.pl v)) (C.Q (X.pl v)) (C.Qi (X.pl v))
    (C.isT (X.pl v))
  rwa [show vOf X (X.pl v) = v from X.pl.symm_apply_apply v] at h

def zc (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Fin (2 * D.R.rS + D.R.k + 1) → ℂ :=
  Qic X C v *ᵥ rv X.B.I v (X.zR u)

theorem zc_spec (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    inWb D.R.k D.R.rS (zc X C u v) ∧ Tz D.R.k D.R.rS (zc X C u v) = Tr D u :=
  zTr_of X (transpC X C v) u

theorem zc_pos (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : 0 < Tz D.R.k D.R.rS (zc X C u v) := by
  rw [(zc_spec X C u v).2]
  unfold Tr
  exact_mod_cast (D.mem u).A.T_prime.pos

def πc (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (m : Matrix (Fin (2 * D.R.rS + D.R.k + 1))
    (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) : X.Vloc u v →L[ℂ] X.Vloc u v :=
  X.piLoc u v (Formalism.L2.SG.RealObj.matQ (X.B.I.ε v) (X.wfr u v) (Qc X C v * m * Qic X C v))

theorem πc_type (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    IsHCTypeW D.R.k D.R.rS (zc X C u v) (fun i => ((D.hcW u (X.pl v)).u i : ℝ)) (πc X C u v) :=
  colsTypeTr_of X (Formalism.L2.SG.Pf.cfS_ne D) (transpC X C v) u

theorem πc_rep (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    IsCRepOn (UWset D.R.k D.R.rS (zc X C u v)) (πc X C u v) ∧
      (∀ h ∈ UWset D.R.k D.R.rS (zc X C u v), ∀ x, ‖πc X C u v h x‖ = ‖x‖) ∧
      ContinuousOn (πc X C u v) (UWset D.R.k D.R.rS (zc X C u v)) :=
  Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS (zc X C u v) _ (X.Vloc u v) (πc X C u v) (zc_spec X C u v).1
    (zc_pos X C u v) (πc_type X C u v)

def μGc (v : InfinitePlace X.B.I.F) : Measure (Mt D.R.k D.R.rS) :=
  (Formalism.REAL.muG (X.B.I.ε v)).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ))

theorem μGc_haar (v : InfinitePlace X.B.I.F) : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS) (μGc X C v) :=
  haarG_B (n_eq' X) (X.B.I.ε v) (transpC X C v).2.1 (transpC X C v).2.2.1

theorem μW_exists (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ∃ μ : Measure (Mt D.R.k D.R.rS), Formalism.MainNotions.S.IsHaarOn (UWset D.R.k D.R.rS (zc X C u v)) μ ∧ μ Set.univ = 1 :=
  Formalism.MainNotions.S.Inh.haar_probability_compact_subgroup _ (Formalism.MainNotions.S.Inh.one_mem_unitary_stabilizer_set _) (Formalism.MainNotions.S.Inh.unitary_stabilizer_mul_mem _)
    (fun a => Hpk D.R.k D.R.rS * aᴴ * Hpk D.R.k D.R.rS)
    ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const)
    (fun a ha => Formalism.MainNotions.S.Inh.unitary_stabilizer_inv_mem _ a ha)
    (PI.QuotSetU.UnitaryGroupMassFormula.unitary_weyl_compact _ _ _ (zc_spec X C u v).1 (zc_pos X C u v))

def μWc (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measure (Mt D.R.k D.R.rS) := (μW_exists X C u v).choose

theorem sec_c (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ∃ μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ, IsSection D.R.k D.R.rS (zc X C u v) (zc X C u' v) μsec :=
  sec_exists (k_pos D) _ _ (zc_pos X C u v) (zc_pos X C u' v)
    (let ⟨g, hg, _⟩ := πc_type X C u v; ⟨g, hg⟩) (let ⟨g, hg, _⟩ := πc_type X C u' v; ⟨g, hg⟩)

def baseOf (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Formalism.FourierDecayAlt.B.RealPlaceData D.R.k D.R.rS (X.Vloc u v) (X.Vloc u' v) where
  z := zc X C u v
  z' := zc X C u' v
  π := πc X C u v
  π' := πc X C u' v
  μG := μGc X C v
  μW := μWc X C u v
  μN := Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS
  μW' := μWc X C u' v
  μsec := (sec_c X C u u' v).choose
  χ := Formalism.FourierDecayAlt.P.character_exists_alt.choose
  k_pos := k_pos D
  z_mem := (zc_spec X C u v).1
  z'_mem := (zc_spec X C u' v).1
  T_pos := zc_pos X C u v
  T'_pos := zc_pos X C u' v
  π_rep := (πc_rep X C u v).1
  π'_rep := (πc_rep X C u' v).1
  π_unitary := (πc_rep X C u v).2.1
  π'_unitary := (πc_rep X C u' v).2.1
  π_cont := (πc_rep X C u v).2.2
  π'_cont := (πc_rep X C u' v).2.2
  haarG := μGc_haar X C v
  haarW := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zc_spec X C u v).1 (zc_pos X C u v) (μW_exists X C u v).choose_spec.1
  haarN := Formalism.FourierDecayAlt.P.Dx2.MN.haar D.R.rS
  haarW' := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zc_spec X C u' v).1 (zc_pos X C u' v)
    (μW_exists X C u' v).choose_spec.1
  sec := (sec_c X C u u' v).choose_spec
  χ_smooth := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.1
  χ_supp := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.2.1
  χ_int := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.2.2

end Place

section Carrier

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice Formalism.L2.SG.Pf.Carrier

variable {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem baseOf_μW1 (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) : (baseOf X C u u' v).μW Set.univ = 1 := (μW_exists X C u v).choose_spec.2

theorem baseOf_μW'1 (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) : (baseOf X C u u' v).μW' Set.univ = 1 := (μW_exists X C u' v).choose_spec.2

def towersOf (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) :
    Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)) :=
  Formalism.L2.SG.Pf.Built.towerOf (baseOf X C u u' (tauE X e j)) (baseOf_μW1 X C u u' _) (baseOf_μW'1 X C u u' _) rfl

theorem towersOf_base (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) :
    (towersOf X C u u' e j).base = baseOf X C u u' (tauE X e j) :=
  (_root_.Formalism.FourierDecayAlt.P.Dx2.Tower.towerExists _ _ _ _ (baseOf X C u u' (tauE X e j)) (baseOf_μW1 X C u u' _)
    (baseOf_μW'1 X C u u' _) rfl).choose_spec.1

theorem Tz_towersOf_base_eq_T (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) :
    Tz D.R.k D.R.rS (towersOf X C u u' e j).base.z = ((D.mem u).A.T : ℝ) ∧
      Tz D.R.k D.R.rS (towersOf X C u u' e j).base.z' = ((D.mem u').A.T : ℝ) := by
  rw [towersOf_base]
  exact ⟨(zc_spec X C u _).2, (zc_spec X C u' _).2⟩

theorem cast_conj (u : D.what₂.Word) {w v : InfinitePlace X.B.I.F} (h : w = v)
    (m : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) :
    (((castLoc X u h).symm.toContinuousLinearEquiv : X.Vloc u v →L[ℂ] X.Vloc u w).comp
      ((πc X C u v m).comp ((castLoc X u h).toContinuousLinearEquiv : X.Vloc u w →L[ℂ] X.Vloc u v))) = πc X C u w m := by
  subst h
  ext x
  rfl

def carrierIn (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ) : CarrierIn X u u' :=
  carrierInOf X u u' e he hv C CA de de' l grid grid1 (towersOf X C u u' e) (Tz_towersOf_base_eq_T X C u u' e) fc χ sg ν' m₀
    top A₀

theorem fromX (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    : (CarrierOf (carrierIn X C u u' e he hv CA de de' l grid grid1 fc χ sg ν' m₀ top A₀)).FromX := by
  intro v
  have hw : tauE X e ((tauE X e).symm v) = v := Equiv.apply_symm_apply _ v
  have hT := transpC X C v
  refine ⟨?_, ?_, ?_, fun m => ?_, fun m => ?_, ?_, ?_⟩
  · have h := isTransp_cs (Formalism.L2.SG.Pf.torTie X) C (X.pl v)
    rwa [show vOf X (X.pl v) = v from X.pl.symm_apply_apply v] at h
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.z = zc X C u v
    rw [towersOf_base]
    show zc X C u (tauE X e ((tauE X e).symm v)) = zc X C u v
    rw [hw]
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.z' = zc X C u' v
    rw [towersOf_base]
    show zc X C u' (tauE X e ((tauE X e).symm v)) = zc X C u' v
    rw [hw]
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.π m = _
    rw [towersOf_base]
    exact (cast_conj X C u (tauE_symm X e v) m).symm
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.π' m = _
    rw [towersOf_base]
    exact (cast_conj X C u' (tauE_symm X e v) m).symm
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.μG = μGc X C v
    rw [towersOf_base]
    show μGc X C (tauE X e ((tauE X e).symm v)) = μGc X C v
    rw [hw]
  · show ∃ μS : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.RealObj.IsHaarLoc {γ | Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ ∈
        Sset D.R.k D.R.rS (towersOf X C u u' e ((tauE X e).symm v)).base.z} μS ∧
      μS.map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ)) =
        ((towersOf X C u u' e ((tauE X e).symm v)).base.μN.prod
          (towersOf X C u u' e ((tauE X e).symm v)).base.μW).map
          (fun p => Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2))
    rw [towersOf_base]
    show ∃ μS : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.RealObj.IsHaarLoc {γ | Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ ∈
        Sset D.R.k D.R.rS (zc X C u (tauE X e ((tauE X e).symm v)))} μS ∧
      μS.map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ)) =
        ((Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS).prod (μWc X C u (tauE X e ((tauE X e).symm v)))).map
          (fun p => Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2))
    rw [hw]
    exact muS_loc (n_eq' X) (X.B.I.ε v) hT.1 hT.2.1 hT.2.2.1 (zc_spec X C u v).1 (zc_pos X C u v)
      (μW_exists X C u v).choose_spec.1 (μW_exists X C u v).choose_spec.2 (Formalism.FourierDecayAlt.P.Dx2.MN.haar D.R.rS)

end Carrier

end Formalism.L2.SG.Pf.BaseOf
