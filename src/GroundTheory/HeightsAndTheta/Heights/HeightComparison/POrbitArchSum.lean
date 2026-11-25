module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
import GroundTheory.HeightsAndTheta.Heights.BlockScaling

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem eval_smul_of_isMultiHomog (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ)
    (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (c : ι → ℂ) (z : Coord n → ℂ) :
    eval (fun p ↦ c p.1 * z p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  rw [eval_map, eval_map]
  exact BlockScaling.eval₂_mul_block_left (Int.castRingHom ℂ) c z hs

end GroundTheory.Heights₂.Heights
