module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmFonOfPoints
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AtQDTypes

theorem l_not_mem_gset {D : D7} (i : D.nd.Loc) (h : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) :
    D.nd.l i ∉ TwistedPlaces.gset D := by
  unfold TwistedPlaces.gset
  intro hm
  rw [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm <;> rcases h with h | h
  · exact (GlobalTheory.HubFon.g_ne_q_d D 0).1 (hm ▸ h)
  · exact (GlobalTheory.HubFon.g_ne_q_d D 0).2 (hm ▸ h)
  · exact (GlobalTheory.HubFon.g_ne_q_d D 1).1 (hm ▸ h)
  · exact (GlobalTheory.HubFon.g_ne_q_d D 1).2 (hm ▸ h)

end GlobalTheory.AtQDTypes
