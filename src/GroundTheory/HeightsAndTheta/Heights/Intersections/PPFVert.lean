module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFVert
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import Mathlib.Order.CompletePartialOrder
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ProjectionFormulaVertical

open PointVertical

theorem geoNum_mixed_eq_zero
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCMF : ContractMixedFieldStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d r : ℕ}
    (hP : IsArithVar (imageZ v P') d) {W : Ideal (MRing ι')} (hPW : P' ≤ W)
    (hWm : IsMultiProjPrime W) (hpr : (charOf W).Prime)
    (hWd : ringKrullDim (MRing ι' ⧸ W) = ((d + r + Fintype.card K' : ℕ) : WithBot ℕ∞))
    (L : Fin d → K → ℤ) (N : Fin r → K' → ℤ) :
    geoNum (d + r) W (Fin.append (fun j => pullDeg κ (L j)) N) = 0 := by
  have : Fact (charOf W).Prime := ⟨hpr⟩
  obtain ⟨hpW, hWp, m, hmd, hVi⟩ := exists_red_projVarF hv hP hPW hWm hpr hWd
  obtain ⟨I, hI, -⟩ := hR4 (ZMod (charOf W)) K' ι'
  rw [hGeo K' ι' (charOf W) I hI W (d + r) _ hWm hpW hWp]
  unfold ContractMixedFieldStatement at hCMF
  exact hCMF (ZMod (charOf W)) K ι K' ι' I hI κ v _ m d r L N hv hWp hVi hmd

end ProjectionFormulaVertical


open ProjectionFormulaVertical in
theorem PFVert.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCMF : ContractMixedFieldStatement) :
    PFVert.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r L L' N s a W hv hP' hP hL hs hsP hW hh
  classical
  have hsec : IsSectionOn P' (HermLine.sqMetric (ι := ι') a) s := ⟨a, fun _ => rfl, hs, hsP⟩
  obtain ⟨hWm, hpr, hWd⟩ :=
    (divSuppArith K' ι' P' (d + r) (HermLine.sqMetric (ι := ι') a) s W hP' hsec hW).2 hh
  have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
  have e : (fun j => (Fin.append L' N j).a) =
      Fin.append (fun j => pullDeg κ (L j).a) (fun j => (N j).a) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [(hL i).1]
    · simp
  rw [e]
  exact geoNum_mixed_eq_zero hGeo hR4 hCMF hv hP hPW hWm hpr hWd _ _

end GroundTheory.Heights₂.Heights.Inter
