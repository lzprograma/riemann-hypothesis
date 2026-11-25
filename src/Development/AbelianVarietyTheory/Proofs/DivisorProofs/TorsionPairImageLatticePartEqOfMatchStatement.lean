module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfNonempty
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatch, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatchStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatch =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatch", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfNonempty\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj
attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qImg_lattice : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (J : Ideal V), AdmBase V J → ∀ (D₁ D₂ : DegData V J) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], Match D₁.toPre D₂.toPre b φ F → ∀ (k : ℕ) (p : QkPt D₁.toPre F k) (p' : QkPt D₂.toPre F k), Act D₁.toPre D₂.toPre b φ.symm.toAddMonoidHom p.g p'.g → p'.y = φ p.y := by
  intro V _ _ _ J hJ D₁ D₂ b φ F _ _ _ hM k p p' hA
  obtain ⟨hmon, -, -, hnrm, hlast⟩ := hM
  obtain ⟨hex, hadd, -⟩ := GlobalTheory.Mum.Two.act_two_hom V D₁.toPre D₂.toPre b φ.symm.toAddMonoidHom hmon hnrm F
  choose α hα hαu using hex
  let f : GtPtF D₁.toPre F →+ GtPtF D₂.toPre F := AddMonoidHom.mk' α fun x y =>
    (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1
      (hadd x y (x + y) (α x) (α y) (α (x + y)) ((GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl) (hα x) (hα y) (hα _))
  obtain ⟨h₁, hn₁, hi₁⟩ := p.eq
  obtain ⟨h₂, hn₂, hi₂⟩ := p'.eq
  obtain ⟨g', hg'A, hg'I⟩ := hlast p.y h₁ hi₁
  have e₁ : h₁ = k • p.g := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn₁
  have e₂ : h₂ = k • p'.g := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn₂
  have ep : p'.g = f p.g := hαu p.g p'.g hA
  have eg : g' = f h₁ := hαu h₁ g' hg'A
  have : g' = h₂ := by rw [eg, e₁, map_nsmul, ← ep, e₂]
  rw [← this] at hi₂
  exact GlobalTheory.IotaInj.main GlobalTheory.firstFiveLaws V J hJ D₂ F p'.y (φ p.y) g' hi₂ hg'I

end GlobalTheory.TInj

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatch =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatchStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatchStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatch\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatchStatement =====
