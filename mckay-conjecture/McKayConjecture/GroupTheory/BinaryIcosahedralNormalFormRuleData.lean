/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules00
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules01
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules02
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules03
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules04
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules05
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules06
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules07
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules08
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules09
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules10
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules11
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules12

/-!
# All binary-icosahedral rewrite rules
-/

namespace McKayConjecture
namespace GroupTheory

/-- The 122 oriented rules used by the normal-form checker. -/
def binaryIcosahedralRewriteRules :
    Fin 122 → BinaryIcosahedralRewriteRule :=
  fun i =>
    match i.val with
    | 0 => binaryIcosahedralRewriteRule000
    | 1 => binaryIcosahedralRewriteRule001
    | 2 => binaryIcosahedralRewriteRule002
    | 3 => binaryIcosahedralRewriteRule003
    | 4 => binaryIcosahedralRewriteRule004
    | 5 => binaryIcosahedralRewriteRule005
    | 6 => binaryIcosahedralRewriteRule006
    | 7 => binaryIcosahedralRewriteRule007
    | 8 => binaryIcosahedralRewriteRule008
    | 9 => binaryIcosahedralRewriteRule009
    | 10 => binaryIcosahedralRewriteRule010
    | 11 => binaryIcosahedralRewriteRule011
    | 12 => binaryIcosahedralRewriteRule012
    | 13 => binaryIcosahedralRewriteRule013
    | 14 => binaryIcosahedralRewriteRule014
    | 15 => binaryIcosahedralRewriteRule015
    | 16 => binaryIcosahedralRewriteRule016
    | 17 => binaryIcosahedralRewriteRule017
    | 18 => binaryIcosahedralRewriteRule018
    | 19 => binaryIcosahedralRewriteRule019
    | 20 => binaryIcosahedralRewriteRule020
    | 21 => binaryIcosahedralRewriteRule021
    | 22 => binaryIcosahedralRewriteRule022
    | 23 => binaryIcosahedralRewriteRule023
    | 24 => binaryIcosahedralRewriteRule024
    | 25 => binaryIcosahedralRewriteRule025
    | 26 => binaryIcosahedralRewriteRule026
    | 27 => binaryIcosahedralRewriteRule027
    | 28 => binaryIcosahedralRewriteRule028
    | 29 => binaryIcosahedralRewriteRule029
    | 30 => binaryIcosahedralRewriteRule030
    | 31 => binaryIcosahedralRewriteRule031
    | 32 => binaryIcosahedralRewriteRule032
    | 33 => binaryIcosahedralRewriteRule033
    | 34 => binaryIcosahedralRewriteRule034
    | 35 => binaryIcosahedralRewriteRule035
    | 36 => binaryIcosahedralRewriteRule036
    | 37 => binaryIcosahedralRewriteRule037
    | 38 => binaryIcosahedralRewriteRule038
    | 39 => binaryIcosahedralRewriteRule039
    | 40 => binaryIcosahedralRewriteRule040
    | 41 => binaryIcosahedralRewriteRule041
    | 42 => binaryIcosahedralRewriteRule042
    | 43 => binaryIcosahedralRewriteRule043
    | 44 => binaryIcosahedralRewriteRule044
    | 45 => binaryIcosahedralRewriteRule045
    | 46 => binaryIcosahedralRewriteRule046
    | 47 => binaryIcosahedralRewriteRule047
    | 48 => binaryIcosahedralRewriteRule048
    | 49 => binaryIcosahedralRewriteRule049
    | 50 => binaryIcosahedralRewriteRule050
    | 51 => binaryIcosahedralRewriteRule051
    | 52 => binaryIcosahedralRewriteRule052
    | 53 => binaryIcosahedralRewriteRule053
    | 54 => binaryIcosahedralRewriteRule054
    | 55 => binaryIcosahedralRewriteRule055
    | 56 => binaryIcosahedralRewriteRule056
    | 57 => binaryIcosahedralRewriteRule057
    | 58 => binaryIcosahedralRewriteRule058
    | 59 => binaryIcosahedralRewriteRule059
    | 60 => binaryIcosahedralRewriteRule060
    | 61 => binaryIcosahedralRewriteRule061
    | 62 => binaryIcosahedralRewriteRule062
    | 63 => binaryIcosahedralRewriteRule063
    | 64 => binaryIcosahedralRewriteRule064
    | 65 => binaryIcosahedralRewriteRule065
    | 66 => binaryIcosahedralRewriteRule066
    | 67 => binaryIcosahedralRewriteRule067
    | 68 => binaryIcosahedralRewriteRule068
    | 69 => binaryIcosahedralRewriteRule069
    | 70 => binaryIcosahedralRewriteRule070
    | 71 => binaryIcosahedralRewriteRule071
    | 72 => binaryIcosahedralRewriteRule072
    | 73 => binaryIcosahedralRewriteRule073
    | 74 => binaryIcosahedralRewriteRule074
    | 75 => binaryIcosahedralRewriteRule075
    | 76 => binaryIcosahedralRewriteRule076
    | 77 => binaryIcosahedralRewriteRule077
    | 78 => binaryIcosahedralRewriteRule078
    | 79 => binaryIcosahedralRewriteRule079
    | 80 => binaryIcosahedralRewriteRule080
    | 81 => binaryIcosahedralRewriteRule081
    | 82 => binaryIcosahedralRewriteRule082
    | 83 => binaryIcosahedralRewriteRule083
    | 84 => binaryIcosahedralRewriteRule084
    | 85 => binaryIcosahedralRewriteRule085
    | 86 => binaryIcosahedralRewriteRule086
    | 87 => binaryIcosahedralRewriteRule087
    | 88 => binaryIcosahedralRewriteRule088
    | 89 => binaryIcosahedralRewriteRule089
    | 90 => binaryIcosahedralRewriteRule090
    | 91 => binaryIcosahedralRewriteRule091
    | 92 => binaryIcosahedralRewriteRule092
    | 93 => binaryIcosahedralRewriteRule093
    | 94 => binaryIcosahedralRewriteRule094
    | 95 => binaryIcosahedralRewriteRule095
    | 96 => binaryIcosahedralRewriteRule096
    | 97 => binaryIcosahedralRewriteRule097
    | 98 => binaryIcosahedralRewriteRule098
    | 99 => binaryIcosahedralRewriteRule099
    | 100 => binaryIcosahedralRewriteRule100
    | 101 => binaryIcosahedralRewriteRule101
    | 102 => binaryIcosahedralRewriteRule102
    | 103 => binaryIcosahedralRewriteRule103
    | 104 => binaryIcosahedralRewriteRule104
    | 105 => binaryIcosahedralRewriteRule105
    | 106 => binaryIcosahedralRewriteRule106
    | 107 => binaryIcosahedralRewriteRule107
    | 108 => binaryIcosahedralRewriteRule108
    | 109 => binaryIcosahedralRewriteRule109
    | 110 => binaryIcosahedralRewriteRule110
    | 111 => binaryIcosahedralRewriteRule111
    | 112 => binaryIcosahedralRewriteRule112
    | 113 => binaryIcosahedralRewriteRule113
    | 114 => binaryIcosahedralRewriteRule114
    | 115 => binaryIcosahedralRewriteRule115
    | 116 => binaryIcosahedralRewriteRule116
    | 117 => binaryIcosahedralRewriteRule117
    | 118 => binaryIcosahedralRewriteRule118
    | 119 => binaryIcosahedralRewriteRule119
    | 120 => binaryIcosahedralRewriteRule120
    | _ => binaryIcosahedralRewriteRule121

/-- The certified rules have exactly the patterns used by the
executable traces. -/
theorem binaryIcosahedralRewriteRules_pattern
    (i : Fin 122) :
    (binaryIcosahedralRewriteRules i).pattern =
      binaryIcosahedralRewritePatterns i := by
  fin_cases i <;> rfl

end GroupTheory
end McKayConjecture
