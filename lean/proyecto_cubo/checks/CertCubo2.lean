import RequestProject.MainTheorem.All
import RequestProject.BaiCounts.All
import RequestProject.PodiumCor.All
import RequestProject.Mirror.All
import RequestProject.FoldLaw.All
import RequestProject.OddParts.All
import RequestProject.Windows.All
import RequestProject.SmallCases.All

/-! Print file for the Lean certificate of «The Dancing Sand Theorem» (paper v8).
Grepy Escribano, 11 October 2026. Nothing is proved here: Lean prints, verbatim, the statements of
the headline theorems (`#check`) and the definitions their statements use (`#print`), so that the
certificate can quote them exactly. -/

-- ## The headline theorems
#check @MainTheorem.M1
#check @MainTheorem.M2
#check @MainTheorem.G2
#check @MainTheorem.M3_support
#check @MainTheorem.M3_shift
#check @MainTheorem.M3_self
#check @MainTheorem.M3_zero
#check @Windows.theorem_D_i
#check @BaiCounts.B1
#check @BaiCounts.B2
#check @PodiumCor.P1
#check @PodiumCor.P2
#check @PodiumCor.P3
#check @PodiumCor.G1
#check @PodiumCor.G2
#check @PodiumCor.G3
#check @Mirror.Y2
#check @FoldLaw.H
#check @FoldLaw.DW
#check @FoldLaw.DW'
#check @FoldLaw.L1
#check @FoldLaw.R
#check @OddParts.B1
#check @OddParts.C5
#check @SmallCases.DW'_all
#check @SmallCases.L1_all
#check @SmallCases.R_all
#check @SmallCases.G1_all

-- ## The cube, the sandpile group and the 2-part
#print CubeLaplacian.G
#print CubeLaplacian.e
#print CubeLaplacian.lap
#print CubeLaplacian.coker
#print CubeLaplacian.K
#print CubeLaplacian.Syl2
#print OddParts.Sylp
-- ## The folded cube
#print Fold.aElt
#print Fold.Gbar
#print Fold.mk
#print Fold.lapBar
#print Fold.KBar
#print FoldGroup.twoM
-- ## The multiplicities
#print FamDec.Vdot
#print FamDec.L
#print FamDec.m
-- ## The family of λ and its dancers
#print Families.ds
#print Windows.Ids
#print Dance.mCount
#print TheoremF.dancer
#print Houses.bit
-- ## The raw clocks
#print Rulers.s2
#print Rulers.v2
#print Rulers.kappa
#print Rulers.phi
#print Rulers.oE
#print Rulers.minOr
#print Rulers.next
#print Rulers.h
#print Rulers.hSum
#print Rulers.lam
#print Rulers.xi
#print Rulers.clock
-- ## The integer antitonic fit
#print AntitonicFit.NonIncr
#print AntitonicFit.sqDist
#print AntitonicFit.IsFit
#print AntitonicFit.fit
#print AntitonicFit.levelSet
#print AntitonicFit.toR
#print AntitonicFit.blockF
#print AntitonicFit.ifit
-- ## The group of a family
#print FamilyGroup.SC
#print FamilyGroup.Q
#print FamilyGroup.yPool
#print FamilyGroup.yPool0
#print MainTheorem.XFam
-- ## The counts and the exponents
#print BaiCounts.aN
#print BaiCounts.twoPow
#print BaiCounts.l0
#print BaiCounts.l1
#print PodiumCor.layer
#print PodiumCor.cExp
#print PodiumCor.gmax
-- ## Axioms of the three cases of Corollary 1.6
#print axioms PodiumCor.P1
#print axioms PodiumCor.P2
#print axioms PodiumCor.P3
