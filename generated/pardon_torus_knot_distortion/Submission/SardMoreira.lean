/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Submission.SardMoreira.ContDiff
import Submission.SardMoreira.ContDiffMoreiraHolder
import Submission.SardMoreira.ContinuousMultilinearMap
import Submission.SardMoreira.Chart
import Submission.SardMoreira.ChartEstimates
import Submission.SardMoreira.ImplicitFunction
import Submission.SardMoreira.LebesgueDensity
import Submission.SardMoreira.LinearAlgebra
import Submission.SardMoreira.LocalEstimates
import Submission.SardMoreira.MainTheorem
import Submission.SardMoreira.MeasureBallSemicontinuous
import Submission.SardMoreira.MeasureComap
import Submission.SardMoreira.MeasureNNReal
import Submission.SardMoreira.NormedSpace
import Submission.SardMoreira.OuterMeasureDeriv
import Submission.SardMoreira.Planar
import Submission.SardMoreira.ToMathlib
import Submission.SardMoreira.Topology
import Submission.SardMoreira.UnifDoublingCover
import Submission.SardMoreira.Unused
import Submission.SardMoreira.UpperLowerSemicontinuous
import Submission.SardMoreira.WithRPowDist

/-!
# Moreira's version of Sard's theorem

Source: doi:10.5565/PUBLMAT_45101_06
Authors: Yury G. Kudryashov
Status: verified
Main declarations: `dimH_image_le_sardMoreiraBound_of_finrank_le`
Tags: analysis, measure-theory, sard-theorem, hausdorff-measure
MSC: 28A78, 58C25
-/

/-!
## Mathematical overview

Moreira's strengthening of Sard's theorem on the Hausdorff dimension
of the critical-value set of a sufficiently differentiable map.

## Main results

- `hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le` —
  Hausdorff measure vanishing for the image of a set whose derivative
  rank is bounded by `p`.
- `dimH_image_le_sardMoreiraBound_of_finrank_le` — the corresponding
  Hausdorff-dimension bound for critical-value images.
- `ContDiffMoreiraHolderAt` — the pointwise `C^{k+α}` predicate
  (function is `C^k` at a point and the `k`-th derivative is locally
  Hölder of exponent `α`).
- `WithRPowDist` — metric-space wrapper giving `dist x y ^ α` as the
  metric, used to apply Vitali covering arguments to product spaces
  with mixed scaling.
-/
