module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndRaw
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn

namespace GlobalTheory.AnVal

theorem exists_ortho_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r), ∀ x ∈ X.dom, ∃ b ∈ FD.Bor X.Ψ r, FD.rmul x b ∈ X.dom ∧ X.IsOrtho (FD.rmul x b) ∧ (∀ τ i, ‖FD.dmin X.Gm (FD.rmul x b) τ i‖ = 1) ∧ (∀ th, I2.phiFD X th (FD.rmul x b) = I2.phiFD X th x) ∧ ∀ (la : FD.Wt X.Ψ r) (P : FD.Frame X.Ψ r → ℂ), X.IsSec la P → X.pnorm la P x = ‖P (FD.rmul x b)‖ := by
  intro E _ _ _ r X x hx
  have hb := FD.FrameDegreeData.bOf_mem X hx
  have ho := FD.FrameDegreeData.ortho_bOf X hx
  have hd : ∀ τ i, ‖FD.dmin X.Gm (FD.rmul x (FD.FrameDegreeData.bOf X x)) τ i‖ = 1 := by
    intro τ i
    unfold FD.dmin
    rw [ho τ, FD.FrameDegreeData.lminor_diagonal, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Complex.norm_real]
    rcases FD.FrameDegreeData.sgn_sq X.p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) j : Fin r) with h | h <;>
      rw [h] <;> simp
  have hl : X.la1 (FD.rmul x (FD.FrameDegreeData.bOf X x)) = X.la1 x := by
    unfold FD.Data.la1
    rw [ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimumSq_rightBorel X hx hb]
  refine ⟨_, hb, FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb, ho, hd, fun th => ?_, fun la P hP => ?_⟩
  · unfold I2.phiFD
    rw [hl]
  · rw [← FD.FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx _ hb]
    unfold FD.Data.pnorm
    simp only [norm_div, hd, div_one, Real.one_rpow, Finset.prod_const_one, _root_.mul_one]

end GlobalTheory.AnVal
