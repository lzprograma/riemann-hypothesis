module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory

theorem dense_open_eq_top_of_smoothOfRelativeDimension_zero : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k), SmoothOfRelativeDimension 0 p → ∀ (U : Y.Opens), Dense (U : Set Y) → U = ⊤ := by
  intro k _ Y p hp U hU
  have he : Etale p := (Etale.iff_smoothOfRelativeDimension_zero p).2 hp
  have hq : LocallyQuasiFinite p := by
    refine ⟨fun {V} hV {W} hW e ↦ ?_⟩
    have h := p.etale_appLE hV hW e
    letI := (p.appLE V W e).hom.toAlgebra
    have : Algebra.Etale Γ(Sp k, V) Γ(Y, W) := h
    exact (inferInstance : Algebra.QuasiFinite Γ(Sp k, V) Γ(Y, W))
  have hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hopen : ∀ y : Y, IsOpen ({y} : Set Y) := by
    intro y
    have hd : _root_.IsDiscrete (p ⁻¹' {p y}) := p.isDiscrete_preimage_singleton (p y)
    have huniv : p ⁻¹' {p y} = Set.univ := by
      ext z; simp [Subsingleton.elim (p z) (p y)]
    rw [huniv] at hd
    have : DiscreteTopology Y := by
      have h2 := hd.to_subtype
      exact (Homeomorph.Set.univ Y).symm.isEmbedding.discreteTopology
    exact isOpen_discrete _
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨z, hz1, hz2⟩ := hU.inter_open_nonempty {y} (hopen y) ⟨y, rfl⟩
  rw [Set.mem_singleton_iff] at hz1
  subst hz1
  exact hz2

end GlobalTheory
