module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

noncomputable section

namespace GlobalTheory.FrameGlue.Pull

open GlobalTheory.Cartier GlobalTheory.TrueGeo.SmallSec

section
variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
  (hη : j (genericPoint Y) ⤳ genericPoint X)

theorem fnMap_algebraMap (y : Y) (a : X.presheaf.stalk (j y)) :
    fnMap j hη (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (j.stalkMap y a) := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [algebraMap_germ hx s, fnMap_fnOf j hη _ (gen_mem hy), ← algebraMap_germ hy]
  exact congrArg _ (Scheme.Hom.germ_stalkMap_apply j U _ _ s).symm

theorem regAt_fnMap {y : Y} {t : X.functionField} (h : RegAt (j y) t) : RegAt y (fnMap j hη t) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨_, (fnMap_algebraMap j hη y a).symm⟩

theorem unitAt_fnMap {y : Y} {t : X.functionField} (h : UnitAt (j y) t) : UnitAt y (fnMap j hη t) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨_, ha.map _, (fnMap_algebraMap j hη y a).symm⟩

end

end GlobalTheory.FrameGlue.Pull

end
