module

public import Formalism.SharpRestriction.ParConsts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.placeRankTwoOne

open Formalism.BasicNotions NumberField IsDedekindDomain

def NN (D : D7) : ℝ := (D.R.N D.R.m : ℝ)

def degLine (D : D7) (r : (D.what₂.LL →+* ℂ) → ℝ) (ρ : D.what₂.places.Pl → ℝ) : ℝ :=
  (∑ᶠ w, ρ w * lw D.what₂.LL (D.plEq w)) - (∑ σ, Real.log (r σ)) / (Module.finrank ℚ D.what₂.LL : ℝ)

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

open Classical in
def detW (D : D7) (τ : D.what₂.Tau) : D.what₂.Tau → Fin D.R.r → ℤ :=
  fun τ' _ => if τ' = τ then -1 else 0

variable (D : D7) (large₂ : SizeData₂ D) (X : DivX D)

def LL0 : ℝ :=
  Real.log (large₂.sc.b * D.host.rdE) * Real.log (Real.log large₂.sc.x) + |large₂.logDerivativeAtOne| + Real.log large₂.sc.x

def dimY : ℕ := D.R.f * (D.R.r.choose 2)

end Formalism.MainNotions.placeRankTwoOne

end
