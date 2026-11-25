module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
public import Mathlib.RingTheory.LittleWedderburn
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointResidue
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace VerticalPointResidue

variable {T : Type} [Fintype T]

theorem isMultiHomog_iff {g : MRing (fun _ : Unit => T)} {n : ℕ} :
    IsMultiHomog g (fun _ => n) ↔
      IsWeightedHomogeneous (blockWeight (ι := fun _ : Unit => T) ()) g n := by
  constructor
  · intro h
    exact isWeightedHomogeneous_of_isMultiHomog h ()
  · intro h m hm k
    cases k
    exact (weight_blockWeight (ι := fun _ : Unit => T) () m).symm.trans (h (mem_support_iff.mp hm))

theorem exists_homog {S : Type*} [CommRing S] (χ : MRing (fun _ : Unit => T) →+* S) (c : T)
    (hχ : χ (X ⟨(), c⟩) = 1) (f : MRing (fun _ : Unit => T)) :
    ∃ (n : ℕ) (G : MRing (fun _ : Unit => T)), IsMultiHomog G (fun _ => n) ∧ χ G = χ f := by
  obtain ⟨d, G, hG, hGf⟩ := Targets.CurveVerticalPointResidue.exists_homog χ (fun _ => c) (fun _ => hχ) f
  exact ⟨d (), G, by rwa [show (fun _ : Unit => d ()) = d from funext fun k => by cases k; rfl], hGf⟩

theorem aeval_div {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K') (c : T)
    (G : MRing (fun _ : Unit => T)) (n : ℕ) (hG : IsMultiHomog G (fun _ => n)) :
    aeval (fun p => y p / y ⟨(), c⟩) G = aeval y G * (y ⟨(), c⟩ ^ n)⁻¹ := by
  simpa [Fintype.prod_unique] using
    Targets.CurveVerticalPointResidue.aeval_div (K := Unit) (ι := fun _ => T) y (fun _ => c) G (fun _ => n) hG

end VerticalPointResidue

theorem VertPointResidue.proof (hC : CurveCharts.Statement) : VertPointResidue.Statement := by
  intro T _ K' _ _ y s hP hs hsP W hW
  exact Targets.CurveVertPointResidue.of_single (K := Unit) (ι := fun _ => T) y s (fun _ => 1)
    hP hs hsP W hW fun m hm => by
      obtain ⟨t, hyt, hrat⟩ := (hC T K' y hP).2.2 m hm
      exact ⟨fun _ => t, fun _ => hyt, fun p => hrat p.2⟩

end

end GroundTheory.Heights₂.Heights
