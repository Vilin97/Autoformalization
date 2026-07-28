/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralOrderSixData
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions00
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions01
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions02
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions03
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions04
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions05
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions06
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions07
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions08
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions09
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions10
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions11

/-!
# Machine-checkable normal-form data for the binary icosahedral group

The certificate is split into small generated files so every file checks
within Lean's default elaboration and heartbeat limits.
-/

namespace McKayConjecture
namespace GroupTheory

/-- The full 120-by-4 right-multiplication certificate. -/
def binaryIcosahedralNormalFormTransitions :
    Fin 120 → Fin 4 → BinaryIcosahedralNormalFormTransition :=
  fun i =>
    match i.val with
    | 0 => binaryIcosahedralNormalFormTransitionRow000
    | 1 => binaryIcosahedralNormalFormTransitionRow001
    | 2 => binaryIcosahedralNormalFormTransitionRow002
    | 3 => binaryIcosahedralNormalFormTransitionRow003
    | 4 => binaryIcosahedralNormalFormTransitionRow004
    | 5 => binaryIcosahedralNormalFormTransitionRow005
    | 6 => binaryIcosahedralNormalFormTransitionRow006
    | 7 => binaryIcosahedralNormalFormTransitionRow007
    | 8 => binaryIcosahedralNormalFormTransitionRow008
    | 9 => binaryIcosahedralNormalFormTransitionRow009
    | 10 => binaryIcosahedralNormalFormTransitionRow010
    | 11 => binaryIcosahedralNormalFormTransitionRow011
    | 12 => binaryIcosahedralNormalFormTransitionRow012
    | 13 => binaryIcosahedralNormalFormTransitionRow013
    | 14 => binaryIcosahedralNormalFormTransitionRow014
    | 15 => binaryIcosahedralNormalFormTransitionRow015
    | 16 => binaryIcosahedralNormalFormTransitionRow016
    | 17 => binaryIcosahedralNormalFormTransitionRow017
    | 18 => binaryIcosahedralNormalFormTransitionRow018
    | 19 => binaryIcosahedralNormalFormTransitionRow019
    | 20 => binaryIcosahedralNormalFormTransitionRow020
    | 21 => binaryIcosahedralNormalFormTransitionRow021
    | 22 => binaryIcosahedralNormalFormTransitionRow022
    | 23 => binaryIcosahedralNormalFormTransitionRow023
    | 24 => binaryIcosahedralNormalFormTransitionRow024
    | 25 => binaryIcosahedralNormalFormTransitionRow025
    | 26 => binaryIcosahedralNormalFormTransitionRow026
    | 27 => binaryIcosahedralNormalFormTransitionRow027
    | 28 => binaryIcosahedralNormalFormTransitionRow028
    | 29 => binaryIcosahedralNormalFormTransitionRow029
    | 30 => binaryIcosahedralNormalFormTransitionRow030
    | 31 => binaryIcosahedralNormalFormTransitionRow031
    | 32 => binaryIcosahedralNormalFormTransitionRow032
    | 33 => binaryIcosahedralNormalFormTransitionRow033
    | 34 => binaryIcosahedralNormalFormTransitionRow034
    | 35 => binaryIcosahedralNormalFormTransitionRow035
    | 36 => binaryIcosahedralNormalFormTransitionRow036
    | 37 => binaryIcosahedralNormalFormTransitionRow037
    | 38 => binaryIcosahedralNormalFormTransitionRow038
    | 39 => binaryIcosahedralNormalFormTransitionRow039
    | 40 => binaryIcosahedralNormalFormTransitionRow040
    | 41 => binaryIcosahedralNormalFormTransitionRow041
    | 42 => binaryIcosahedralNormalFormTransitionRow042
    | 43 => binaryIcosahedralNormalFormTransitionRow043
    | 44 => binaryIcosahedralNormalFormTransitionRow044
    | 45 => binaryIcosahedralNormalFormTransitionRow045
    | 46 => binaryIcosahedralNormalFormTransitionRow046
    | 47 => binaryIcosahedralNormalFormTransitionRow047
    | 48 => binaryIcosahedralNormalFormTransitionRow048
    | 49 => binaryIcosahedralNormalFormTransitionRow049
    | 50 => binaryIcosahedralNormalFormTransitionRow050
    | 51 => binaryIcosahedralNormalFormTransitionRow051
    | 52 => binaryIcosahedralNormalFormTransitionRow052
    | 53 => binaryIcosahedralNormalFormTransitionRow053
    | 54 => binaryIcosahedralNormalFormTransitionRow054
    | 55 => binaryIcosahedralNormalFormTransitionRow055
    | 56 => binaryIcosahedralNormalFormTransitionRow056
    | 57 => binaryIcosahedralNormalFormTransitionRow057
    | 58 => binaryIcosahedralNormalFormTransitionRow058
    | 59 => binaryIcosahedralNormalFormTransitionRow059
    | 60 => binaryIcosahedralNormalFormTransitionRow060
    | 61 => binaryIcosahedralNormalFormTransitionRow061
    | 62 => binaryIcosahedralNormalFormTransitionRow062
    | 63 => binaryIcosahedralNormalFormTransitionRow063
    | 64 => binaryIcosahedralNormalFormTransitionRow064
    | 65 => binaryIcosahedralNormalFormTransitionRow065
    | 66 => binaryIcosahedralNormalFormTransitionRow066
    | 67 => binaryIcosahedralNormalFormTransitionRow067
    | 68 => binaryIcosahedralNormalFormTransitionRow068
    | 69 => binaryIcosahedralNormalFormTransitionRow069
    | 70 => binaryIcosahedralNormalFormTransitionRow070
    | 71 => binaryIcosahedralNormalFormTransitionRow071
    | 72 => binaryIcosahedralNormalFormTransitionRow072
    | 73 => binaryIcosahedralNormalFormTransitionRow073
    | 74 => binaryIcosahedralNormalFormTransitionRow074
    | 75 => binaryIcosahedralNormalFormTransitionRow075
    | 76 => binaryIcosahedralNormalFormTransitionRow076
    | 77 => binaryIcosahedralNormalFormTransitionRow077
    | 78 => binaryIcosahedralNormalFormTransitionRow078
    | 79 => binaryIcosahedralNormalFormTransitionRow079
    | 80 => binaryIcosahedralNormalFormTransitionRow080
    | 81 => binaryIcosahedralNormalFormTransitionRow081
    | 82 => binaryIcosahedralNormalFormTransitionRow082
    | 83 => binaryIcosahedralNormalFormTransitionRow083
    | 84 => binaryIcosahedralNormalFormTransitionRow084
    | 85 => binaryIcosahedralNormalFormTransitionRow085
    | 86 => binaryIcosahedralNormalFormTransitionRow086
    | 87 => binaryIcosahedralNormalFormTransitionRow087
    | 88 => binaryIcosahedralNormalFormTransitionRow088
    | 89 => binaryIcosahedralNormalFormTransitionRow089
    | 90 => binaryIcosahedralNormalFormTransitionRow090
    | 91 => binaryIcosahedralNormalFormTransitionRow091
    | 92 => binaryIcosahedralNormalFormTransitionRow092
    | 93 => binaryIcosahedralNormalFormTransitionRow093
    | 94 => binaryIcosahedralNormalFormTransitionRow094
    | 95 => binaryIcosahedralNormalFormTransitionRow095
    | 96 => binaryIcosahedralNormalFormTransitionRow096
    | 97 => binaryIcosahedralNormalFormTransitionRow097
    | 98 => binaryIcosahedralNormalFormTransitionRow098
    | 99 => binaryIcosahedralNormalFormTransitionRow099
    | 100 => binaryIcosahedralNormalFormTransitionRow100
    | 101 => binaryIcosahedralNormalFormTransitionRow101
    | 102 => binaryIcosahedralNormalFormTransitionRow102
    | 103 => binaryIcosahedralNormalFormTransitionRow103
    | 104 => binaryIcosahedralNormalFormTransitionRow104
    | 105 => binaryIcosahedralNormalFormTransitionRow105
    | 106 => binaryIcosahedralNormalFormTransitionRow106
    | 107 => binaryIcosahedralNormalFormTransitionRow107
    | 108 => binaryIcosahedralNormalFormTransitionRow108
    | 109 => binaryIcosahedralNormalFormTransitionRow109
    | 110 => binaryIcosahedralNormalFormTransitionRow110
    | 111 => binaryIcosahedralNormalFormTransitionRow111
    | 112 => binaryIcosahedralNormalFormTransitionRow112
    | 113 => binaryIcosahedralNormalFormTransitionRow113
    | 114 => binaryIcosahedralNormalFormTransitionRow114
    | 115 => binaryIcosahedralNormalFormTransitionRow115
    | 116 => binaryIcosahedralNormalFormTransitionRow116
    | 117 => binaryIcosahedralNormalFormTransitionRow117
    | 118 => binaryIcosahedralNormalFormTransitionRow118
    | _ => binaryIcosahedralNormalFormTransitionRow119

end GroupTheory
end McKayConjecture
