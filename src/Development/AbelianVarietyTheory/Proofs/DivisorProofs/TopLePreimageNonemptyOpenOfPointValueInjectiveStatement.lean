module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjective, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjectiveStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjective =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjective", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff\npublic import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral\nimport Mathlib.Tactic.Linter.HaveILetI\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan\npublic import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior\nimport Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat

noncomputable section

namespace GlobalTheory.GenPtOpen

theorem top_le_preimage_of_valR_injective : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ O : P₀.A.left.Opens, (O : Set P₀.A.left).Nonempty → ⊤ ≤ ξ ⁻¹ᵁ O := by
  intro K _ P₀ F _ ψ ξ _ H O hO
  haveI : IsIntegral P₀.A.left := GlobalTheory.isIntegral_left_of_isAbelianScheme_field P₀.A P₀.isAb
  by_contra hno
  haveI : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have key : ∀ V : P₀.A.left.Opens, ξ p ∈ V → ⊤ ≤ ξ ⁻¹ᵁ V := fun V hV y _ => by
    rw [Subsingleton.elim y p]; exact hV
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    P₀.A.left.isBasis_affineOpens) (show ξ p ∈ (⊤ : P₀.A.left.Opens) from trivial)
  obtain ⟨y, hyU, hyO⟩ := nonempty_preirreducible_inter U.isOpen O.isOpen ⟨_, hxU⟩ hO
  obtain ⟨f, hfO, hyf⟩ := (show IsAffineOpen U from hU).exists_basicOpen_le (V := O) ⟨y, hyO⟩ hyU
  have hUt : ⊤ ≤ ξ ⁻¹ᵁ U := key U hxU
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyf
    exact hyf
  refine hf0 (H U f hUt ?_)
  by_contra hv
  have hu : IsUnit (valR ξ U f) := isUnit_iff_ne_zero.mpr hv
  have hb := (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff ξ U hUt f).mp hu
  exact hno (hb.trans (ξ.preimage_mono hfO))

end GlobalTheory.GenPtOpen
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjective =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjectiveStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjectiveStatement", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjective\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan\npublic import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjectiveStatement =====
