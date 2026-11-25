module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementZ
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementT

@[expose] public section

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R]

theorem subst_neg' {a : R⟦X⟧} (ha : HasSubst a) (f : R⟦X⟧) : (-f).subst a = -f.subst a := by
  first
    | (rw [← PowerSeries.coe_substAlgHom ha]; exact map_neg _ f)

theorem subst_one' {a : R⟦X⟧} (ha : HasSubst a) : (1 : R⟦X⟧).subst a = 1 := by
  first
    | (rw [← PowerSeries.coe_substAlgHom ha]; exact map_one _)

theorem subst_injective_of_leftInverse {l e a b : R⟦X⟧} (hl : HasSubst l) (ha : HasSubst a)
    (hb : HasSubst b) (hel : e.subst l = X) (h : l.subst a = l.subst b) : a = b := by
  calc a = e.subst (l.subst a) := by
        rw [← PowerSeries.subst_comp_subst_apply hl ha, hel, PowerSeries.subst_X ha]
    _ = e.subst (l.subst b) := by rw [h]
    _ = b := by rw [← PowerSeries.subst_comp_subst_apply hl hb, hel, PowerSeries.subst_X hb]

end SlopeTestRemainingChoices

theorem logSpec_of (hI : IntegSpec.{u}) (hU : UnitSpec.{u}) : LogSpec.{u} := by
  intro K _ _ W
  obtain ⟨hc, hd, -⟩ := hI K (om W)
  obtain ⟨-, hfo, ho0, -⟩ := hU K W
  refine ⟨hc, ?_, hd, ?_⟩
  · simp only [logSer, integ, coeff_mk]
    simp [ho0]
  · simp only [D, logSer, Derivation.smul_apply, smul_eq_mul, hd, hfo]

theorem expSpec_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u}) :
    ExpSpec.{u} := by
  intro K _ _ W
  obtain ⟨hL0, hL1, hLd, -⟩ := logSpec_of hI hU K W
  obtain ⟨-, hfo, -⟩ := hU K W
  obtain ⟨hE0, hLE, hEL, hcoef, -⟩ := hC K (logSer W) hL0 (by rw [hL1]; exact isUnit_one)
  have hE0' : constantCoeff (expSer W) = 0 := hE0
  have hLE' : (logSer W).subst (expSer W) = X := hLE
  have hs : HasSubst (expSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' hE0'
  refine ⟨hE0, ?_, hLE, hEL, ?_⟩
  · have h : coeff 1 (expSer W) * coeff 1 (logSer W) = 1 := hcoef
    rwa [hL1, mul_one] at h
  · have h1 := congrArg (fun f : K⟦X⟧ => PowerSeries.derivative (R := K) f) hLE'
    rw [derivative_subst hs, hLd, derivative_X] at h1
    have h2 : (fw W).subst (expSer W) * (om W).subst (expSer W) = 1 := by
      rw [← PowerSeries.subst_mul hs, hfo, subst_one' hs]
    calc PowerSeries.derivative (R := K) (expSer W)
        = ((fw W).subst (expSer W) * (om W).subst (expSer W)) * PowerSeries.derivative (R := K) (expSer W) := by
          rw [h2, one_mul]
      _ = (fw W).subst (expSer W) := by rw [mul_assoc, h1, mul_one]

theorem chainZ_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u}) :
    ChainZ.{u} := by
  intro K _ _ W f
  obtain ⟨hE0, -, -, -, hEd⟩ := expSpec_of hI hC hU K W
  have hs : HasSubst (expSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' hE0
  rw [derivative_subst hs, hEd]
  simp only [D, Derivation.smul_apply, smul_eq_mul]
  rw [PowerSeries.subst_mul hs, mul_comm]

theorem logNeg_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u})
    (hS : ISerSpec.{u}) : LogNeg.{u} := by
  intro K _ _ W
  obtain ⟨hL0, -, hLd, -⟩ := logSpec_of hI hU K W
  obtain ⟨hE0, -, hLE, hEL, -⟩ := expSpec_of hI hC hU K W
  obtain ⟨hi0, -, -, -, -, -, -, hiom⟩ := hS K W
  have hsi : HasSubst (iSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' hi0
  have hsE : HasSubst (expSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' hE0
  have hL' : (logSer W).subst (iSer W) = -logSer W := by
    obtain ⟨-, -, huniq⟩ := hI K (-om W)
    have e1 := huniq ((logSer W).subst (iSer W)) (PowerSeries.constantCoeff_subst_eq_zero hi0 (logSer W) hL0)
      (by rw [derivative_subst hsi, hLd, hiom])
    have e2 := huniq (-logSer W) (by rw [map_neg, hL0, neg_zero]) (by rw [map_neg, hLd])
    rw [e1, e2]
  refine ⟨hL', ?_⟩
  have hnX0 : constantCoeff (-X : K⟦X⟧) = 0 := by simp
  have hsn : HasSubst (-X : K⟦X⟧) := PowerSeries.HasSubst.of_constantCoeff_zero' hnX0
  apply subst_injective_of_leftInverse (l := logSer W) (e := expSer W) (PowerSeries.HasSubst.of_constantCoeff_zero' hL0)
    (PowerSeries.HasSubst.of_constantCoeff_zero' (PowerSeries.constantCoeff_subst_eq_zero hnX0 (expSer W) hE0)) (PowerSeries.HasSubst.of_constantCoeff_zero' (PowerSeries.constantCoeff_subst_eq_zero hE0 (iSer W) hi0)) hEL
  rw [← PowerSeries.subst_comp_subst_apply hsE hsn, hLE, PowerSeries.subst_X hsn, ← PowerSeries.subst_comp_subst_apply hsi hsE, hL',
    subst_neg' hsE, hLE]

end Formalism.L2.Th1.A
