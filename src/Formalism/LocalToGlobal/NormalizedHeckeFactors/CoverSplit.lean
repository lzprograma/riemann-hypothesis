module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Automorphisms.InstMainA
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2

variable {D : D7}

local notation "cO" => IsCMField.ringOfIntegersComplexConj D.host.E

def conjPlE (P : PlE D.host) : PlE D.host where
  asIdeal := P.asIdeal.comap (cO : 𝓞 D.host.E →+* 𝓞 D.host.E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    refine (Submodule.ne_bot_iff _).2 ⟨cO y, ?_, ?_⟩
    · show (cO : 𝓞 D.host.E →+* 𝓞 D.host.E) (cO y) ∈ P.asIdeal
      rw [RingHom.coe_coe, GlobalTheory.SplitConjPlace.cO_cO]; exact hy
    · intro h0
      apply hy0
      rw [← GlobalTheory.SplitConjPlace.cO_cO y, h0, map_zero]

theorem mem_conjPlE (P : PlE D.host) (x : 𝓞 D.host.E) : x ∈ (conjPlE P).asIdeal ↔ cO x ∈ P.asIdeal := Iff.rfl

theorem eq_or_eq_conjPlE (P w : PlE D.host)
    (hw : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) :
    w = P ∨ w = conjPlE P := by
  apply GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE <;> assumption

def conjSplit (s : SplitPlace D.host.E) : SplitPlace D.host.E :=
  ⟨s.v, s.i.comp (IsCMField.complexConj D.host.E).toAlgHom⟩

end Formalism.L2

namespace Formalism.L2

variable {D : D7}

local notation "cO" => IsCMField.ringOfIntegersComplexConj D.host.E
local notation "Fp" => maximalRealSubfield D.host.E

def belowE (v : PlE D.host) : HeightOneSpectrum (𝓞 Fp) where
  asIdeal := v.asIdeal.comap (algebraMap (𝓞 Fp) (𝓞 D.host.E))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hy0 hy (Algebra.IsIntegral.isIntegral y)

theorem exists_splitPlace (v : PlE D.host) (x0 : 𝓞 D.host.E) (hx0 : x0 ∈ v.asIdeal) (hc0 : cO x0 ∉ v.asIdeal) :
    ∃ s : SplitPlace D.host.E, s.v = belowE v :=
  _root_.GlobalTheory.SplitConjPlace.exists_splitPlace v x0 hx0 hc0

theorem splitEx_of_star (hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x) : SplitEx D := by
  apply GlobalTheory.SplitConjPlace.splitEx_of_star <;> assumption

end Formalism.L2
