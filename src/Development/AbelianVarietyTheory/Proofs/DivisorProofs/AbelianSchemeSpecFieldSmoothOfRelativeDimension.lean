module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AbFieldDim

theorem exists_smoothOfRelativeDimension : ∀ (k : Type) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A],
    IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  intro k _ A _ hA
  exact GlobalTheory.AbelianDim.exists_relDim k A hA

end GlobalTheory.AbFieldDim
