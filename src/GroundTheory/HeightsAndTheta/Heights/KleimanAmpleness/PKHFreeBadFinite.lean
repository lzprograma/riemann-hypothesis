module
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeBadFiniteSt
import Mathlib.Algebra.Order.Star.Int

@[expose] public section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section

theorem KHFreeBadFinite.full : KHFreeBadFinite.Statement := by
  intro K _ ι _ e
  refine (Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Icc (-|e p.1|) |e p.1|)
    (fun p => Set.finite_Icc _ _)).subset ?_
  rintro a ⟨hsum, hneg⟩ ⟨k, i⟩ -
  apply abs_le.mp
  calc
    |a ⟨k, i⟩| ≤ ∑ j, |a ⟨k, j⟩| :=
      Finset.single_le_sum (f := fun j => |a ⟨k, j⟩|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ = |e k| := by
      rw [← (show ∑ j, a ⟨k, j⟩ = e k from congrFun hsum k)]
      rcases hneg k with h | h
      · have hn (j : ι k) : 0 ≤ a ⟨k, j⟩ := by
          simpa [negSet] using (Finset.ext_iff.mp h j)
        simp only [abs_of_nonneg (hn _), abs_of_nonneg (Finset.sum_nonneg fun j _ => hn j)]
      · have hn (j : ι k) : a ⟨k, j⟩ < 0 := by
          simpa [negSet] using (Finset.ext_iff.mp h j)
        simp only [abs_of_neg (hn _), Finset.sum_neg_distrib,
          abs_of_nonpos (Finset.sum_nonpos fun j _ => (hn j).le)]

end
end GroundTheory.Heights₂.Heights.Kleiman
