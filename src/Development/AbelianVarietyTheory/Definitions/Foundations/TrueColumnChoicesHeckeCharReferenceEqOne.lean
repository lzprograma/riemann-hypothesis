module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder
public import Formalism.LocalRingCardinality.DataNChoice

@[expose] public section

noncomputable section
section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG)

def eExp (D : D7) (j : Fin D.R.m) (g : D.R.Psi) : ℚ := (D.hc (D.eTau.symm g)).e j

structure CharFrame (D : D7) where

  P : PiBar D.host

  W : Omg D.host

  mu0 : Fin D.R.m → HChar D.host.E
  eta : HChar D.host.E
  chiPsi : HChar D.host.E
  del : HChar D.host.E
  del' : HChar D.host.E
  isMu0 : ∀ j, IsMu0 P W (eExp D j) j.1 (mu0 j)
  isEta : IsEtaT D.host eta
  isChi : IsChiPsi D.host chiPsi
  isDel : IsDelta D.host.pde del
  isDel' : IsDelta D.host.pde' del'

def CharFrame.delAt {D : D7} (C : CharFrame D) (l : ℕ) : HChar D.host.E := if l = D.host.pde then C.del' else C.del

end GlobalTheory.Mem.Chr

end
