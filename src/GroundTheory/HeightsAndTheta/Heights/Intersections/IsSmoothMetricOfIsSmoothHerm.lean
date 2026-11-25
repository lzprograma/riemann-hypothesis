module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]




theorem isProjVarQ_of_isArithVar {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {e : ℕ}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) :
    IsProjVarQ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) e := by
  obtain ⟨-, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have := hprime
  have hch : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have hm' : m ∈ P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := Ideal.mem_comap.mpr hm
    rw [show P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) = ⊥ from hhor, Ideal.mem_bot] at hm'
    exact hm'
  obtain ⟨hQ, hcomap, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mpr
    ⟨hQ, ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, MvPolynomial.map_X]
    exact h
  · have hd' : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
        P.map (MvPolynomial.map (Int.castRingHom ℚ))) + 1 =
        ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← hdim]
      exact hd
    rw [Nat.add_right_comm e 1 (Fintype.card K), Nat.cast_add, Nat.cast_one] at hd'
    exact ENat.WithBot.add_one_cancel.mp hd'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
