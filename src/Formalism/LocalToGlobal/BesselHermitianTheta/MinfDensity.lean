module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

def minfDensity (N : ℕ) : ENNReal := ((2 : ENNReal) ^ (N * (N - 1) / 2))⁻¹

def petCOf (D : D7) (petF : HSp D → ℝ) (petR : ℕ → ℕ → ℝ) (V : HSp D) : ℝ :=
  petF V * ∏ τ : D.what₂.Tau, petR (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2

structure ThetaTied (D : D7) (X : ThetaX D) where

  ev : ∀ V, X.AF V →ₗ[ℂ] (GA D V → ℂ)

  eGf : ∀ V, X.Gf V ≃* GfC V

  petF : HSp D → ℝ

  petR : ℕ → ℕ → ℝ

  pet : ∀ V : HSp D, V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 → ∀ (F : X.AF V) (G : X.cusp V),
    X.pet V F G = (petCOf D petF petR V : ℂ) * ∫ h in 𝓕, star (ev V F h) * ev V (G : X.AF V) h ∂μ

  eChr : X.Chr →* ((AE D)ˣ →* Circle)
  eChr_inj : Function.Injective eChr
  eChr_range : Set.range eChr = {χ | IsHeckeChar D χ ∧ ∀ τ, ∃ a, HasInfExp D χ τ a}

  infTy : ∀ χ τ, HasInfExp D (eChr χ) τ (X.infTy χ τ)

  chrOf_res : ∀ μ j, 1 ≤ j → j ≤ D.R.m → ResEta D (eChr (X.chrOf μ j)) 0

  etaT_res : ResEta D (eChr X.etaT) 1

def ThetaTied.petC {D : D7} {X : ThetaX D} (T : ThetaTied D X) (V : HSp D) : ℝ := petCOf D T.petF T.petR V

structure RealTied (D : D7) : Prop where

  cdScale : cdScaleTie D

  dsig : ∀ τ, IsDsig D τ (D.dsig τ)

  dsig_all : dsigTie D

  vol : VolTieG D

structure ProvisionCompatibility (D : D7) (A : TH.ProvA) : Prop where

  haar : TH.HaarCd D A

  ds : ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → NoncompactGapAtLeastRange p q lam → HasParam (A.ds p q lam) lam

end Formalism.L2.Theta

end
