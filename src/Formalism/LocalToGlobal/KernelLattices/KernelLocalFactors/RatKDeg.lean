module

public import Formalism.LocalToGlobal.KernelLattices.RatKDeg
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.JetsRationalOfKernelRationality
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions

theorem natW_cast {n : ℕ} (lam : DomWeight n) (i : Fin n) : ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.detShift := by
  unfold DomWeight.natW
  have h : lam.detShift ≤ lam.w i := by
    unfold DomWeight.detShift
    have hn : 0 < n := Fin.pos i
    rw [dite_eq_left hn]
    exact lam.anti (show i ≤ ⟨n - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
  omega

theorem chain_degree_eq : StepDegIs := by
  intro X Pr R W u i hi τ
  unfold stepDeg opDeg
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [natW_cast, nuLast_eq W u i hi τ]
  have hN : 0 < R.N i := R.N_pos i
  have d0 : (W.lamTrue u i τ).detShift = (W.lamTrue u i τ).w ⟨R.N i - 1, by omega⟩ := by
    unfold DomWeight.detShift
    exact dite_eq_left hN
  have d1 : (W.nuW u (i + 1) τ).detShift = (W.nuW u (i + 1) τ).w ⟨R.N i - 1, by show R.N i - 1 < R.N i; omega⟩ := by
    unfold DomWeight.detShift
    exact dite_eq_left hN
  rw [d0, d1]
  show (W.lamN u i τ).w r + _ - ((W.lamN u i τ).w _ + _) + ((W.lamN u i τ).w _ + _) = (W.lamN u i τ).w r + _
  ring

section Props

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)

theorem jetK_spec_deg (dg : X.Tau → ℕ) (hrat : A.JetsRatDeg a b Sall D dg) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ)
    (x : HomE X.E a b) (hR : InRange Sall D c N N' x) (m : DVar X.Tau a b →₀ ℕ) (hm : ∀ τ, degAt m τ = dg τ) :
    A.σ₀ (A.jetK Sall N N' c x m) = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m := by
  obtain ⟨k, hk⟩ := hrat N N' c x hR m hm
  unfold Amb.jetK
  rw [← hk, desc_map]

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)

theorem thDistC_ok_deg (hD : 0 < D) (rho : UF X.E a →* Module.End X.K (DIV.VV X.K lam)) (rho' : UF X.E b →* Module.End X.K (DIV.VV X.K lam'))
    (sS sT : SB → X.E → X.K)
    (heq : ThEquivP (thDistC A Sall SB D sel mU mI lam lam' n) Sall D rho rho')
    (ha : MuDetLaw a mI sS) (hb : MuDetLaw b mI sS) (hi : UnitInv sS sT) :
    ThDist.Ok (thDistC A Sall SB D sel mU mI lam lam' n) Sall D rho rho' sS sT :=
  { cong := fun N fr N' fr' c x x' _ _ h => thDistC_cong A Sall SB sel mU mI lam lam' n D N fr N' fr' c x x' h
    equiv := thDistC_equiv A Sall SB sel mU mI lam lam' n D hD rho rho' heq
    det := fun N fr N' fr' c x κ κ' _ _ => thDistC_det A Sall SB sel mU mI lam lam' n D sS sT ha hb hi N fr N' fr' c x κ κ' }

end Props

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

theorem stepC_ok_deg (i : ℕ) (hi : i < R.m) {b : ℕ} (lam' : X.Tau → DomWeight b) (hT : 0 < Pr.T u)
    (rho : UF X.E (R.N i) →* Module.End X.K (DIV.VV X.K (W.lamTrue u i))) (rho' : UF X.E b →* Module.End X.K (DIV.VV X.K lam'))
    (hq : MuqTie Ch sel mu cst)
    (heqT : ThEquivP (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho') :
    ThDist.Ok (stepC W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho'
      (rhoS Ch sel mu i) (rhoT Ch sel mu i) :=
  have heq : ThEquivP (stepC W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho' := by
    rw [stepC_eq_stepT W Ch sel mu cst hq A u i hi lam']; exact heqT
  thDistC_ok_deg A (Sall sel mu u) (rowSG Pr sel mu) _ sel (mUof Ch mu i) (muAt Ch sel mu cst i) (W.lamTrue u i) lam' (nuLast W u i)
    (modulus_pos sel mu cst u hT) rho rho' _ _ heq
    (muDetLaw_chain Ch sel mu cst i _) (muDetLaw_chain Ch sel mu cst i _) (unitInv_rho Ch sel mu i)

theorem chTh_ok_ambD (hm : m2 + 1 < R.m) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst) (h : ThHypD W Ch sel mu cst A u m2) :
    ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2) :=
  { th i hi := stepC_ok_deg W Ch sel mu cst A u i (by omega) _ hT _ _ hq (h.1 i hi)
    top := stepC_ok_deg W Ch sel mu cst A u (m2 + 1) hm _ hT _ _ hq h.2 }

end Chain



end Formalism.L2.Ker
