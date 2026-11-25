module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.MBLow.TanExp

def termV {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (J : (Sp (DualNumber R) ⟶ D.P.A.left) → D.P.L.ι)
    (g : GtPt D (epsR R)) {k : ℕ} {α : D.X} (f : D.SecB k α) : DualNumber R :=
  valR g.b.left (LB.wchart D.P.L (D.famφB α) fun i => J (g.b.left ≫ D.famφB α i))
      (f.f fun i => J (g.b.left ≫ D.famφB α i)) *
    valR (𝟙 (Sp (DualNumber R))) (LB.wchart D.P.L (DegPre.gtφT D (epsR R) g.b α) fun i => J (DegPre.gtφT D (epsR R) g.b α i))
      ((g.s α).s fun i => J (DegPre.gtφT D (epsR R) g.b α i)).val

def rigVal {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (j : L.L.ι) : S :=
  valR (𝟙 (Sp S)) ((L.L.pull (eSec G)).U fun _ => j) (L.rig.s fun _ => j).val

def rigValD {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (j : D.P.L.ι) : R :=
  valR (𝟙 (Sp R)) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) fun _ => j) (D.rig.s fun _ => j).val

end GlobalTheory.MBLow.TanExp

end
