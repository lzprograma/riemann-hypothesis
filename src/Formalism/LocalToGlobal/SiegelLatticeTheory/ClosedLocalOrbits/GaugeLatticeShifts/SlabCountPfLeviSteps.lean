module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfStabFlag

@[expose] public section

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

def LeviStabFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u',
    ∃ T : Finset ((VS D).V ≃ₗ[D.host.E] (VS D).V),
      (∀ τ ∈ T, τ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap τ Λ = Λ ∧ ∃ t : X.B.I.GA, RatLink X t τ ∧ t ∈ Srat X u') ∧
      ∀ (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : X.B.I.GA), RatLink X s σ → σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
        s ∈ Srat X u' → Formalism.HermitianLatticesTheory.gmap σ Λ = Λ →
        ∃ τ ∈ T, ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), (τ⁻¹ * σ) x - x ∈ Xsp (lf D (X.Fu u'))

def Usp {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) : Submodule D.host.E (VS D).V :=
  Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u'})

def Wsp {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) : Submodule D.host.E (VS D).V :=
  orth (VS D) (Usp X u')

def LeviPosC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word), ∀ w ∈ Wsp X u', w ≠ 0 →
    0 < Algebra.trace ℚ D.host.E ((VS D).hT w w)

def SratZC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (s : X.B.I.GA)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ → s ∈ Srat X u' →
      σ (X.zu u') - X.zu u' ∈ Xsp (lf D (X.Fu u'))

def piWL {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) :
    (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ a, ((VS D).hT (X.fY a)).smulRight (X.eX a) - ∑ a, ((VS D).hT (X.eX a)).smulRight (X.fY a) -
    ((VS D).hT (X.zu u')).smulRight (((VS D).hT (X.zu u') (X.zu u'))⁻¹ • X.zu u')

def hW {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) :
    Wsp X u' →ₗ⋆[D.host.E] Wsp X u' →ₗ[D.host.E] D.host.E :=
  ((VS D).hT.comp (Wsp X u').subtype).compl₂ (Wsp X u').subtype

def LW {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Submodule (𝓞 D.host.E) (Wsp X u') :=
  ((Λ ⊓ (orth (VS D) (Xsp (lf D (X.Fu u')))).restrictScalars (𝓞 D.host.E)).map
    ((piWL X u').restrictScalars (𝓞 D.host.E))).comap ((Wsp X u').subtype.restrictScalars (𝓞 D.host.E))

def LeviWFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u',
    Set.Finite {g : Wsp X u' ≃ₗ[D.host.E] Wsp X u' | g ∈ Formalism.HermitianLatticesTheory.isom (hW X u') ∧ Formalism.HermitianLatticesTheory.gmap g (LW X u' Λ) = LW X u' Λ}

theorem srat_flag {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {u' : D.what₂.Word} {s : X.B.I.GA}
    {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : RatLink X s σ) (hS : s ∈ Srat X u') :
    ∀ j, ∀ x ∈ Xflag (lf D (X.Fu u')) (j + 1), σ x - x ∈ Xflag (lf D (X.Fu u')) j := by
  have hX : ∀ j : ℕ, Xflag (lf D (X.Fu u')) j = Submodule.span D.host.E (X.eX '' {b | b.1 < j}) := by
    intro j
    unfold Formalism.MainNotions.S.Lat.Xflag Formalism.MainNotions.S.FlagG.Xa
    simp only [X.Fu_e]
  intro j x hx
  rw [hX (j + 1)] at hx
  rw [hX j]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    have h := Formalism.L2.SG.Pf.RegroupPf.StabFlagPf.flag_e (X := X) hs hS b
    refine Submodule.span_mono ?_ h
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, lt_of_lt_of_le hc (Nat.lt_succ_iff.mp hb), rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add (f := _), add_sub_add_comm]
    exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ a hy

theorem leviFinC_of (h : LeviStabFinC) : LeviFinC := by
  intro D X Y u'
  let P : Submodule (𝓞 D.host.E) (VS D).V → Submodule (𝓞 D.host.E) (VS D).V → Prop := fun Λ₁ Λ₂ =>
    Λ₂ ∈ Y.what₂ u' ∧ ∃ (σ₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s₀ : X.B.I.GA), RatLink X s₀ σ₀ ∧
      σ₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ s₀ ∈ Srat X u' ∧ Formalism.HermitianLatticesTheory.gmap σ₀ Λ₂ = Λ₁
  refine ⟨fun Λ₁ Λ₂ => if hP : P Λ₁ Λ₂ then
      (h D X Y u' Λ₂ hP.1).choose.image (fun τ => hP.2.choose * τ) else ∅, ?_⟩
  intro Λ₁ _ Λ₂ hΛ₂ σ s hs hσ hS hmap
  have hP : P Λ₁ Λ₂ := ⟨hΛ₂, σ, s, hs, hσ, hS, hmap⟩
  simp only [dite_eq_left hP]
  obtain ⟨s₀, hs₀, hσ₀, hS₀, hmap₀⟩ := hP.2.choose_spec
  obtain ⟨hT1, hT2⟩ := (h D X Y u' Λ₂ hP.1).choose_spec
  generalize hP.2.choose = σ₀ at hs₀ hσ₀ hmap₀ ⊢
  generalize (h D X Y u' Λ₂ hP.1).choose = T at hT1 hT2 ⊢

  have hρL : RatLink X (s₀⁻¹ * s) (σ₀⁻¹ * σ) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hs₀) hs
  have hρI : σ₀⁻¹ * σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hσ₀) hσ
  have hρS : s₀⁻¹ * s ∈ Srat X u' := (Srat X u').mul_mem ((Srat X u').inv_mem hS₀) hS
  have hρΛ : Formalism.HermitianLatticesTheory.gmap (σ₀⁻¹ * σ) Λ₂ = Λ₂ := by
    rw [gmap_mul, hmap]
    exact gmap_inv hmap₀
  obtain ⟨τ, hτ, hτo⟩ := hT2 (σ₀⁻¹ * σ) (s₀⁻¹ * s) hρL hρI hρS hρΛ
  obtain ⟨hτI, hτΛ, t, ht, htS⟩ := hT1 τ hτ
  refine ⟨σ₀ * τ, Finset.mem_image.mpr ⟨τ, hτ, rfl⟩, ?_⟩
  have heq : (σ₀ * τ)⁻¹ * σ = τ⁻¹ * (σ₀⁻¹ * σ) := by
    rw [mul_inv_rev, mul_assoc]
  rw [heq]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hτI) hρI, ?_⟩, ?_, hτo⟩
  · rw [gmap_mul, hρΛ]
    exact gmap_inv hτΛ
  · exact srat_flag X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X ht) hρL)
      ((Srat X u').mul_mem ((Srat X u').inv_mem htS) hρS)

end Formalism.L2.SG.Pf.SlabCount
