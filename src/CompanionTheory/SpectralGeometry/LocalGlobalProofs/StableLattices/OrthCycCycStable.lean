module
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP

@[expose] public section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.LowKType
open CompanionTheory.D.LK CompanionTheory.D.DSIC Formalism.REAL

theorem orthCyc_cyc_stable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (a b : Fin n) {x : V} (hx : x ∈ Cyc E v) :
    E a b x ∈ Cyc E v := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨FreeAlgebra.ι ℂ (a, b) * t, by simp [ev]⟩

theorem orthCyc : CompanionTheory.D.LK.OrthCyc := by
  intro n ε V _ _ E μ v u _ hU hL h1 hu hvu m hm
  obtain ⟨S, hS, hSst, hmS⟩ := hL m
  let W : Submodule ℂ V := S ⊓ Cyc E v
  letI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (inf_le_left : W ≤ S)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.exists_add_mem_mem_orthogonal (K := W) u
  have ortho := (Submodule.mem_orthogonal W q).1 hq
  have stable (a b : Fin n) (hab : ε a = ε b) (x : V) (hx : x ∈ W) : E a b x ∈ W :=
    ⟨hSst a b hab x hx.1, orthCyc_cyc_stable E v a b hx.2⟩
  have key (a b : Fin n) (hab : ε a = ε b) (c : ℂ) (hc : E a b u = c • u) : E a b p = c • p := by
    suffices h : E a b p - c • p ∈ W ⊓ Wᗮ by
      simpa only [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] using h
    refine ⟨W.sub_mem (stable a b hab p hp) (W.smul_mem c hp), ?_⟩
    rw [hpq, map_add (f := _), smul_add] at hc
    rw [show E a b p - c • p = c • q - E a b q by rw [sub_eq_sub_iff_add_eq_add, hc, add_comm]]
    refine Wᗮ.sub_mem (Wᗮ.smul_mem c hq) ((Submodule.mem_orthogonal W _).2 fun w hw => ?_)
    simpa only [← hU b a hab.symm] using ortho _ (stable b a hab.symm w hw)
  obtain ⟨c, hc⟩ := h1 p hp.2 ⟨fun a => key a a rfl _ (hu.1 a),
    fun a b hab hε => by simpa using key a b hε 0 (by simpa using hu.2 a b hab hε)⟩
  suffices p = 0 by simpa only [hpq, this, zero_add] using ortho m ⟨hmS, hm⟩
  exact inner_self_eq_zero.1 <| calc
    ⟪p, p⟫_ℂ = ⟪p, u⟫_ℂ := by rw [hpq, inner_add_right, ortho p hp, add_zero]
    _ = 0 := by rw [hc, inner_smul_left, hvu, mul_zero]

end GlobalTheory.CompanionTheory.LowKType
