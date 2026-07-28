/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyChecks35

/-!
# Complete checked conjugacy data for the sixfold cover of `A₆`

The blockwise computations are assembled into quantified generator
invariance and orbit-witness statements.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- The blockwise checks imply `alternatingSixSchurClassIndex_conjugateA` globally. -/
theorem alternatingSixSchurClassIndex_conjugateA
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateA * coordinate *
          alternatingSixSchurCoordinateA⁻¹) =
      alternatingSixSchurClassIndex coordinate := by
  rcases coordinate with ⟨state, central⟩
  let centralIndex : Fin 6 :=
    (ZMod.finEquiv 6).symm central
  fin_cases state
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state000 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state001 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state002 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state003 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state004 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state005 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state006 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state007 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state008 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state009 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state010 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state011 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state012 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state013 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state014 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state015 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state016 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state017 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state018 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state019 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state020 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state021 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state022 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state023 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state024 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state025 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state026 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state027 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state028 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state029 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state030 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state031 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state032 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state033 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state034 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state035 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state036 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state037 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state038 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state039 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state040 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state041 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state042 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state043 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state044 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state045 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state046 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state047 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state048 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state049 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state050 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state051 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state052 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state053 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state054 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state055 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state056 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state057 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state058 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state059 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state060 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state061 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state062 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state063 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state064 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state065 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state066 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state067 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state068 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state069 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state070 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state071 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state072 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state073 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state074 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state075 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state076 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state077 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state078 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state079 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state080 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state081 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state082 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state083 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state084 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state085 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state086 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state087 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state088 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state089 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state090 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state091 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state092 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state093 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state094 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state095 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state096 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state097 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state098 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state099 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state100 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state101 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state102 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state103 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state104 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state105 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state106 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state107 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state108 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state109 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state110 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state111 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state112 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state113 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state114 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state115 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state116 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state117 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state118 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state119 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state120 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state121 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state122 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state123 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state124 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state125 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state126 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state127 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state128 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state129 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state130 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state131 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state132 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state133 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state134 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state135 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state136 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state137 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state138 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state139 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state140 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state141 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state142 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state143 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state144 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state145 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state146 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state147 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state148 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state149 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state150 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state151 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state152 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state153 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state154 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state155 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state156 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state157 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state158 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state159 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state160 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state161 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state162 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state163 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state164 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state165 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state166 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state167 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state168 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state169 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state170 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state171 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state172 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state173 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state174 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state175 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state176 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state177 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state178 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state179 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state180 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state181 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state182 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state183 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state184 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state185 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state186 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state187 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state188 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state189 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state190 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state191 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state192 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state193 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state194 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state195 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state196 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state197 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state198 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state199 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state200 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state201 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state202 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state203 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state204 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state205 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state206 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state207 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state208 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state209 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state210 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state211 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state212 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state213 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state214 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state215 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state216 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state217 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state218 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state219 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state220 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state221 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state222 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state223 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state224 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state225 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state226 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state227 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state228 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state229 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state230 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state231 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state232 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state233 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state234 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state235 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state236 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state237 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state238 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state239 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state240 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state241 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state242 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state243 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state244 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state245 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state246 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state247 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state248 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state249 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state250 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state251 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state252 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state253 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state254 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state255 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state256 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state257 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state258 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state259 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state260 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state261 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state262 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state263 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state264 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state265 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state266 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state267 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state268 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state269 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state270 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state271 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state272 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state273 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state274 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state275 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state276 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state277 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state278 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state279 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state280 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state281 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state282 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state283 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state284 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state285 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state286 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state287 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state288 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state289 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state290 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state291 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state292 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state293 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state294 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state295 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state296 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state297 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state298 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state299 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state300 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state301 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state302 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state303 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state304 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state305 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state306 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state307 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state308 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state309 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state310 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state311 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state312 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state313 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state314 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state315 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state316 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state317 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state318 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state319 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state320 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state321 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state322 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state323 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state324 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state325 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state326 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state327 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state328 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state329 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state330 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state331 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state332 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state333 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state334 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state335 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state336 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state337 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state338 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state339 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state340 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state341 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state342 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state343 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state344 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state345 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state346 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state347 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state348 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state349 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state350 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state351 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state352 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state353 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state354 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state355 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state356 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state357 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state358 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateA_state359 centralIndex

/-- The blockwise checks imply `alternatingSixSchurClassIndex_conjugateB` globally. -/
theorem alternatingSixSchurClassIndex_conjugateB
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurCoordinateB * coordinate *
          alternatingSixSchurCoordinateB⁻¹) =
      alternatingSixSchurClassIndex coordinate := by
  rcases coordinate with ⟨state, central⟩
  let centralIndex : Fin 6 :=
    (ZMod.finEquiv 6).symm central
  fin_cases state
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state000 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state001 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state002 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state003 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state004 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state005 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state006 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state007 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state008 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state009 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state010 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state011 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state012 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state013 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state014 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state015 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state016 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state017 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state018 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state019 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state020 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state021 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state022 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state023 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state024 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state025 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state026 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state027 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state028 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state029 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state030 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state031 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state032 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state033 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state034 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state035 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state036 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state037 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state038 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state039 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state040 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state041 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state042 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state043 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state044 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state045 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state046 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state047 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state048 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state049 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state050 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state051 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state052 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state053 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state054 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state055 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state056 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state057 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state058 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state059 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state060 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state061 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state062 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state063 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state064 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state065 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state066 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state067 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state068 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state069 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state070 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state071 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state072 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state073 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state074 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state075 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state076 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state077 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state078 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state079 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state080 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state081 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state082 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state083 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state084 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state085 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state086 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state087 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state088 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state089 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state090 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state091 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state092 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state093 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state094 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state095 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state096 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state097 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state098 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state099 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state100 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state101 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state102 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state103 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state104 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state105 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state106 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state107 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state108 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state109 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state110 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state111 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state112 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state113 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state114 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state115 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state116 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state117 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state118 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state119 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state120 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state121 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state122 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state123 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state124 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state125 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state126 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state127 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state128 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state129 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state130 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state131 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state132 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state133 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state134 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state135 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state136 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state137 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state138 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state139 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state140 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state141 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state142 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state143 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state144 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state145 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state146 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state147 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state148 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state149 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state150 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state151 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state152 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state153 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state154 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state155 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state156 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state157 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state158 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state159 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state160 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state161 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state162 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state163 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state164 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state165 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state166 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state167 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state168 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state169 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state170 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state171 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state172 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state173 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state174 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state175 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state176 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state177 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state178 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state179 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state180 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state181 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state182 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state183 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state184 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state185 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state186 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state187 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state188 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state189 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state190 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state191 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state192 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state193 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state194 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state195 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state196 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state197 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state198 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state199 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state200 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state201 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state202 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state203 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state204 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state205 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state206 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state207 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state208 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state209 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state210 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state211 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state212 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state213 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state214 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state215 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state216 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state217 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state218 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state219 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state220 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state221 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state222 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state223 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state224 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state225 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state226 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state227 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state228 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state229 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state230 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state231 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state232 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state233 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state234 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state235 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state236 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state237 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state238 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state239 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state240 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state241 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state242 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state243 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state244 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state245 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state246 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state247 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state248 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state249 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state250 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state251 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state252 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state253 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state254 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state255 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state256 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state257 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state258 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state259 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state260 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state261 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state262 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state263 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state264 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state265 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state266 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state267 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state268 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state269 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state270 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state271 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state272 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state273 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state274 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state275 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state276 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state277 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state278 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state279 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state280 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state281 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state282 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state283 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state284 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state285 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state286 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state287 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state288 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state289 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state290 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state291 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state292 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state293 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state294 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state295 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state296 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state297 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state298 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state299 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state300 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state301 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state302 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state303 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state304 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state305 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state306 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state307 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state308 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state309 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state310 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state311 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state312 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state313 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state314 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state315 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state316 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state317 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state318 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state319 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state320 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state321 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state322 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state323 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state324 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state325 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state326 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state327 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state328 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state329 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state330 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state331 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state332 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state333 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state334 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state335 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state336 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state337 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state338 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state339 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state340 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state341 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state342 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state343 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state344 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state345 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state346 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state347 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state348 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state349 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state350 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state351 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state352 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state353 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state354 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state355 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state356 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state357 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state358 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassIndex_conjugateB_state359 centralIndex

/-- The blockwise checks imply `alternatingSixSchurOrbitMiddle_spec` globally. -/
theorem alternatingSixSchurOrbitMiddle_spec
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassConjugator coordinate *
          alternatingSixSchurClassRepresentative
            (alternatingSixSchurClassIndex coordinate) =
      alternatingSixSchurOrbitMiddle coordinate := by
  rcases coordinate with ⟨state, central⟩
  let centralIndex : Fin 6 :=
    (ZMod.finEquiv 6).symm central
  fin_cases state
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state000 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state001 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state002 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state003 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state004 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state005 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state006 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state007 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state008 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state009 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state010 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state011 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state012 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state013 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state014 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state015 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state016 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state017 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state018 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state019 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state020 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state021 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state022 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state023 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state024 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state025 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state026 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state027 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state028 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state029 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state030 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state031 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state032 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state033 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state034 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state035 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state036 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state037 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state038 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state039 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state040 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state041 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state042 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state043 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state044 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state045 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state046 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state047 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state048 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state049 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state050 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state051 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state052 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state053 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state054 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state055 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state056 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state057 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state058 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state059 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state060 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state061 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state062 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state063 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state064 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state065 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state066 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state067 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state068 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state069 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state070 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state071 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state072 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state073 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state074 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state075 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state076 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state077 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state078 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state079 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state080 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state081 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state082 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state083 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state084 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state085 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state086 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state087 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state088 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state089 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state090 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state091 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state092 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state093 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state094 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state095 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state096 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state097 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state098 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state099 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state100 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state101 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state102 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state103 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state104 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state105 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state106 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state107 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state108 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state109 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state110 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state111 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state112 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state113 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state114 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state115 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state116 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state117 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state118 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state119 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state120 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state121 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state122 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state123 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state124 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state125 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state126 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state127 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state128 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state129 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state130 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state131 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state132 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state133 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state134 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state135 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state136 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state137 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state138 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state139 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state140 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state141 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state142 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state143 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state144 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state145 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state146 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state147 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state148 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state149 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state150 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state151 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state152 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state153 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state154 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state155 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state156 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state157 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state158 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state159 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state160 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state161 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state162 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state163 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state164 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state165 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state166 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state167 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state168 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state169 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state170 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state171 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state172 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state173 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state174 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state175 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state176 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state177 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state178 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state179 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state180 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state181 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state182 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state183 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state184 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state185 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state186 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state187 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state188 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state189 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state190 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state191 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state192 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state193 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state194 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state195 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state196 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state197 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state198 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state199 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state200 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state201 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state202 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state203 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state204 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state205 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state206 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state207 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state208 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state209 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state210 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state211 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state212 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state213 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state214 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state215 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state216 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state217 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state218 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state219 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state220 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state221 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state222 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state223 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state224 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state225 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state226 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state227 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state228 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state229 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state230 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state231 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state232 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state233 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state234 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state235 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state236 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state237 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state238 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state239 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state240 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state241 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state242 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state243 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state244 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state245 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state246 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state247 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state248 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state249 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state250 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state251 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state252 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state253 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state254 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state255 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state256 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state257 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state258 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state259 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state260 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state261 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state262 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state263 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state264 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state265 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state266 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state267 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state268 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state269 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state270 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state271 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state272 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state273 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state274 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state275 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state276 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state277 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state278 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state279 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state280 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state281 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state282 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state283 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state284 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state285 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state286 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state287 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state288 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state289 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state290 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state291 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state292 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state293 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state294 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state295 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state296 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state297 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state298 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state299 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state300 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state301 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state302 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state303 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state304 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state305 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state306 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state307 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state308 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state309 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state310 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state311 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state312 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state313 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state314 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state315 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state316 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state317 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state318 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state319 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state320 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state321 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state322 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state323 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state324 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state325 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state326 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state327 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state328 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state329 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state330 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state331 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state332 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state333 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state334 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state335 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state336 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state337 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state338 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state339 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state340 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state341 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state342 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state343 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state344 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state345 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state346 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state347 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state348 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state349 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state350 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state351 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state352 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state353 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state354 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state355 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state356 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state357 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state358 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitMiddle_state359 centralIndex

/-- The blockwise checks imply `alternatingSixSchurClassConjugatorInverse_spec` globally. -/
theorem alternatingSixSchurClassConjugatorInverse_spec
    (coordinate : AlternatingSixSchurCoordinates) :
    (alternatingSixSchurClassConjugator coordinate)⁻¹ =
      alternatingSixSchurClassConjugatorInverse coordinate := by
  rcases coordinate with ⟨state, central⟩
  let centralIndex : Fin 6 :=
    (ZMod.finEquiv 6).symm central
  fin_cases state
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state000 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state001 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state002 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state003 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state004 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state005 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state006 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state007 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state008 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state009 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state010 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state011 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state012 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state013 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state014 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state015 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state016 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state017 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state018 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state019 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state020 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state021 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state022 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state023 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state024 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state025 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state026 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state027 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state028 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state029 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state030 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state031 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state032 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state033 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state034 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state035 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state036 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state037 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state038 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state039 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state040 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state041 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state042 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state043 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state044 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state045 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state046 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state047 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state048 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state049 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state050 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state051 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state052 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state053 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state054 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state055 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state056 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state057 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state058 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state059 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state060 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state061 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state062 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state063 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state064 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state065 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state066 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state067 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state068 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state069 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state070 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state071 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state072 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state073 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state074 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state075 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state076 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state077 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state078 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state079 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state080 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state081 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state082 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state083 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state084 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state085 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state086 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state087 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state088 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state089 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state090 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state091 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state092 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state093 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state094 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state095 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state096 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state097 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state098 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state099 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state100 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state101 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state102 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state103 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state104 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state105 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state106 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state107 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state108 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state109 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state110 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state111 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state112 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state113 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state114 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state115 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state116 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state117 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state118 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state119 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state120 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state121 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state122 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state123 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state124 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state125 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state126 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state127 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state128 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state129 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state130 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state131 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state132 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state133 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state134 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state135 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state136 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state137 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state138 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state139 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state140 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state141 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state142 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state143 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state144 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state145 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state146 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state147 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state148 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state149 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state150 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state151 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state152 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state153 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state154 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state155 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state156 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state157 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state158 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state159 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state160 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state161 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state162 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state163 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state164 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state165 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state166 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state167 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state168 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state169 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state170 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state171 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state172 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state173 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state174 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state175 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state176 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state177 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state178 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state179 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state180 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state181 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state182 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state183 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state184 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state185 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state186 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state187 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state188 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state189 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state190 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state191 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state192 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state193 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state194 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state195 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state196 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state197 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state198 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state199 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state200 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state201 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state202 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state203 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state204 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state205 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state206 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state207 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state208 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state209 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state210 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state211 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state212 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state213 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state214 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state215 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state216 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state217 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state218 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state219 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state220 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state221 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state222 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state223 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state224 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state225 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state226 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state227 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state228 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state229 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state230 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state231 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state232 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state233 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state234 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state235 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state236 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state237 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state238 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state239 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state240 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state241 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state242 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state243 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state244 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state245 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state246 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state247 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state248 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state249 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state250 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state251 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state252 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state253 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state254 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state255 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state256 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state257 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state258 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state259 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state260 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state261 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state262 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state263 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state264 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state265 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state266 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state267 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state268 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state269 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state270 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state271 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state272 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state273 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state274 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state275 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state276 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state277 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state278 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state279 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state280 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state281 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state282 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state283 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state284 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state285 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state286 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state287 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state288 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state289 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state290 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state291 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state292 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state293 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state294 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state295 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state296 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state297 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state298 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state299 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state300 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state301 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state302 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state303 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state304 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state305 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state306 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state307 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state308 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state309 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state310 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state311 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state312 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state313 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state314 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state315 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state316 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state317 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state318 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state319 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state320 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state321 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state322 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state323 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state324 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state325 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state326 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state327 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state328 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state329 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state330 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state331 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state332 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state333 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state334 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state335 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state336 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state337 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state338 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state339 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state340 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state341 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state342 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state343 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state344 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state345 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state346 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state347 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state348 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state349 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state350 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state351 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state352 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state353 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state354 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state355 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state356 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state357 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state358 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurClassConjugatorInverse_state359 centralIndex

/-- The blockwise checks imply `alternatingSixSchurInverseFactor_spec` globally. -/
theorem alternatingSixSchurInverseFactor_spec
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurInverseFactorLeft coordinate *
          alternatingSixSchurInverseFactorRight coordinate =
      alternatingSixSchurClassConjugatorInverse coordinate := by
  rcases coordinate with ⟨state, central⟩
  let centralIndex : Fin 6 :=
    (ZMod.finEquiv 6).symm central
  fin_cases state
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state000 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state001 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state002 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state003 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state004 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state005 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state006 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state007 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state008 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state009 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state010 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state011 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state012 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state013 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state014 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state015 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state016 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state017 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state018 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state019 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state020 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state021 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state022 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state023 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state024 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state025 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state026 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state027 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state028 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state029 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state030 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state031 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state032 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state033 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state034 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state035 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state036 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state037 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state038 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state039 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state040 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state041 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state042 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state043 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state044 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state045 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state046 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state047 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state048 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state049 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state050 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state051 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state052 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state053 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state054 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state055 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state056 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state057 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state058 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state059 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state060 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state061 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state062 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state063 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state064 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state065 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state066 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state067 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state068 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state069 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state070 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state071 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state072 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state073 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state074 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state075 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state076 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state077 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state078 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state079 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state080 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state081 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state082 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state083 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state084 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state085 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state086 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state087 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state088 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state089 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state090 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state091 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state092 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state093 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state094 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state095 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state096 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state097 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state098 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state099 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state100 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state101 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state102 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state103 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state104 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state105 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state106 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state107 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state108 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state109 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state110 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state111 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state112 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state113 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state114 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state115 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state116 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state117 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state118 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state119 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state120 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state121 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state122 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state123 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state124 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state125 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state126 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state127 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state128 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state129 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state130 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state131 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state132 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state133 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state134 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state135 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state136 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state137 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state138 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state139 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state140 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state141 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state142 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state143 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state144 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state145 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state146 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state147 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state148 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state149 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state150 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state151 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state152 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state153 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state154 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state155 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state156 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state157 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state158 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state159 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state160 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state161 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state162 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state163 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state164 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state165 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state166 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state167 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state168 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state169 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state170 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state171 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state172 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state173 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state174 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state175 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state176 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state177 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state178 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state179 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state180 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state181 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state182 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state183 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state184 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state185 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state186 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state187 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state188 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state189 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state190 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state191 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state192 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state193 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state194 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state195 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state196 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state197 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state198 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state199 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state200 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state201 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state202 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state203 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state204 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state205 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state206 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state207 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state208 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state209 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state210 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state211 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state212 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state213 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state214 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state215 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state216 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state217 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state218 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state219 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state220 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state221 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state222 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state223 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state224 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state225 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state226 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state227 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state228 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state229 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state230 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state231 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state232 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state233 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state234 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state235 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state236 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state237 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state238 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state239 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state240 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state241 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state242 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state243 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state244 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state245 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state246 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state247 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state248 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state249 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state250 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state251 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state252 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state253 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state254 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state255 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state256 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state257 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state258 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state259 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state260 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state261 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state262 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state263 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state264 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state265 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state266 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state267 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state268 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state269 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state270 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state271 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state272 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state273 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state274 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state275 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state276 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state277 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state278 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state279 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state280 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state281 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state282 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state283 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state284 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state285 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state286 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state287 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state288 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state289 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state290 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state291 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state292 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state293 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state294 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state295 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state296 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state297 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state298 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state299 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state300 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state301 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state302 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state303 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state304 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state305 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state306 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state307 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state308 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state309 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state310 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state311 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state312 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state313 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state314 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state315 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state316 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state317 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state318 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state319 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state320 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state321 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state322 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state323 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state324 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state325 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state326 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state327 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state328 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state329 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state330 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state331 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state332 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state333 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state334 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state335 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state336 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state337 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state338 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state339 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state340 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state341 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state342 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state343 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state344 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state345 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state346 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state347 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state348 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state349 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state350 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state351 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state352 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state353 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state354 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state355 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state356 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state357 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state358 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurInverseFactor_state359 centralIndex

/-- The blockwise checks imply `alternatingSixSchurOrbitPenultimate_spec` globally. -/
theorem alternatingSixSchurOrbitPenultimate_spec
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurOrbitMiddle coordinate *
          alternatingSixSchurInverseFactorLeft coordinate =
      alternatingSixSchurOrbitPenultimate coordinate := by
  rcases coordinate with ⟨state, central⟩
  let centralIndex : Fin 6 :=
    (ZMod.finEquiv 6).symm central
  fin_cases state
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state000 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state001 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state002 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state003 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state004 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state005 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state006 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state007 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state008 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state009 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state010 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state011 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state012 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state013 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state014 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state015 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state016 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state017 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state018 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state019 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state020 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state021 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state022 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state023 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state024 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state025 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state026 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state027 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state028 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state029 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state030 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state031 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state032 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state033 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state034 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state035 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state036 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state037 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state038 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state039 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state040 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state041 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state042 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state043 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state044 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state045 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state046 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state047 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state048 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state049 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state050 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state051 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state052 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state053 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state054 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state055 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state056 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state057 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state058 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state059 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state060 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state061 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state062 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state063 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state064 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state065 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state066 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state067 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state068 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state069 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state070 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state071 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state072 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state073 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state074 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state075 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state076 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state077 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state078 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state079 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state080 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state081 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state082 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state083 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state084 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state085 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state086 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state087 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state088 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state089 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state090 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state091 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state092 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state093 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state094 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state095 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state096 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state097 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state098 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state099 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state100 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state101 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state102 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state103 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state104 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state105 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state106 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state107 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state108 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state109 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state110 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state111 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state112 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state113 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state114 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state115 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state116 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state117 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state118 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state119 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state120 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state121 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state122 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state123 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state124 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state125 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state126 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state127 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state128 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state129 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state130 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state131 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state132 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state133 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state134 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state135 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state136 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state137 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state138 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state139 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state140 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state141 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state142 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state143 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state144 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state145 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state146 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state147 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state148 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state149 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state150 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state151 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state152 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state153 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state154 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state155 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state156 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state157 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state158 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state159 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state160 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state161 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state162 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state163 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state164 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state165 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state166 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state167 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state168 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state169 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state170 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state171 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state172 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state173 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state174 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state175 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state176 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state177 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state178 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state179 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state180 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state181 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state182 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state183 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state184 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state185 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state186 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state187 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state188 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state189 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state190 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state191 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state192 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state193 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state194 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state195 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state196 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state197 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state198 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state199 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state200 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state201 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state202 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state203 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state204 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state205 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state206 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state207 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state208 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state209 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state210 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state211 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state212 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state213 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state214 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state215 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state216 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state217 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state218 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state219 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state220 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state221 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state222 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state223 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state224 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state225 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state226 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state227 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state228 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state229 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state230 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state231 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state232 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state233 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state234 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state235 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state236 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state237 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state238 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state239 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state240 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state241 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state242 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state243 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state244 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state245 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state246 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state247 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state248 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state249 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state250 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state251 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state252 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state253 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state254 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state255 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state256 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state257 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state258 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state259 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state260 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state261 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state262 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state263 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state264 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state265 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state266 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state267 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state268 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state269 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state270 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state271 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state272 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state273 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state274 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state275 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state276 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state277 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state278 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state279 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state280 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state281 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state282 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state283 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state284 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state285 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state286 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state287 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state288 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state289 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state290 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state291 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state292 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state293 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state294 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state295 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state296 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state297 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state298 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state299 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state300 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state301 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state302 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state303 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state304 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state305 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state306 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state307 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state308 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state309 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state310 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state311 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state312 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state313 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state314 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state315 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state316 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state317 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state318 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state319 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state320 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state321 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state322 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state323 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state324 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state325 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state326 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state327 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state328 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state329 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state330 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state331 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state332 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state333 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state334 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state335 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state336 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state337 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state338 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state339 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state340 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state341 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state342 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state343 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state344 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state345 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state346 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state347 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state348 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state349 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state350 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state351 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state352 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state353 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state354 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state355 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state356 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state357 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state358 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitPenultimate_state359 centralIndex

/-- The blockwise checks imply `alternatingSixSchurOrbitFinish_spec` globally. -/
theorem alternatingSixSchurOrbitFinish_spec
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurOrbitPenultimate coordinate *
          alternatingSixSchurInverseFactorRight coordinate =
      coordinate := by
  rcases coordinate with ⟨state, central⟩
  let centralIndex : Fin 6 :=
    (ZMod.finEquiv 6).symm central
  fin_cases state
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state000 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state001 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state002 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state003 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state004 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state005 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state006 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state007 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state008 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state009 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state010 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state011 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state012 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state013 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state014 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state015 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state016 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state017 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state018 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state019 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state020 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state021 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state022 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state023 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state024 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state025 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state026 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state027 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state028 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state029 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state030 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state031 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state032 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state033 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state034 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state035 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state036 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state037 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state038 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state039 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state040 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state041 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state042 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state043 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state044 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state045 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state046 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state047 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state048 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state049 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state050 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state051 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state052 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state053 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state054 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state055 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state056 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state057 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state058 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state059 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state060 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state061 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state062 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state063 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state064 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state065 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state066 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state067 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state068 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state069 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state070 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state071 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state072 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state073 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state074 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state075 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state076 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state077 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state078 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state079 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state080 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state081 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state082 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state083 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state084 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state085 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state086 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state087 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state088 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state089 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state090 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state091 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state092 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state093 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state094 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state095 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state096 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state097 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state098 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state099 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state100 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state101 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state102 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state103 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state104 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state105 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state106 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state107 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state108 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state109 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state110 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state111 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state112 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state113 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state114 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state115 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state116 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state117 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state118 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state119 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state120 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state121 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state122 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state123 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state124 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state125 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state126 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state127 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state128 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state129 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state130 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state131 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state132 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state133 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state134 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state135 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state136 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state137 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state138 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state139 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state140 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state141 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state142 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state143 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state144 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state145 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state146 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state147 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state148 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state149 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state150 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state151 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state152 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state153 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state154 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state155 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state156 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state157 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state158 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state159 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state160 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state161 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state162 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state163 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state164 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state165 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state166 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state167 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state168 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state169 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state170 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state171 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state172 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state173 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state174 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state175 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state176 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state177 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state178 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state179 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state180 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state181 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state182 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state183 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state184 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state185 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state186 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state187 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state188 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state189 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state190 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state191 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state192 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state193 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state194 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state195 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state196 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state197 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state198 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state199 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state200 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state201 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state202 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state203 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state204 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state205 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state206 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state207 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state208 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state209 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state210 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state211 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state212 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state213 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state214 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state215 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state216 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state217 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state218 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state219 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state220 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state221 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state222 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state223 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state224 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state225 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state226 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state227 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state228 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state229 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state230 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state231 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state232 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state233 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state234 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state235 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state236 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state237 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state238 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state239 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state240 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state241 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state242 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state243 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state244 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state245 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state246 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state247 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state248 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state249 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state250 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state251 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state252 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state253 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state254 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state255 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state256 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state257 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state258 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state259 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state260 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state261 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state262 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state263 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state264 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state265 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state266 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state267 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state268 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state269 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state270 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state271 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state272 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state273 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state274 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state275 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state276 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state277 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state278 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state279 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state280 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state281 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state282 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state283 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state284 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state285 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state286 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state287 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state288 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state289 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state290 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state291 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state292 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state293 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state294 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state295 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state296 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state297 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state298 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state299 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state300 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state301 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state302 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state303 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state304 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state305 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state306 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state307 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state308 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state309 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state310 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state311 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state312 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state313 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state314 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state315 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state316 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state317 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state318 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state319 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state320 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state321 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state322 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state323 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state324 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state325 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state326 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state327 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state328 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state329 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state330 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state331 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state332 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state333 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state334 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state335 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state336 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state337 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state338 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state339 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state340 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state341 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state342 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state343 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state344 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state345 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state346 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state347 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state348 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state349 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state350 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state351 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state352 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state353 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state354 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state355 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state356 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state357 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state358 centralIndex
  · simpa [centralIndex] using
      alternatingSixSchurOrbitFinish_state359 centralIndex

/-- Every coordinate is conjugate to its advertised class
representative. -/
theorem alternatingSixSchurClassConjugator_spec
    (coordinate : AlternatingSixSchurCoordinates) :
    alternatingSixSchurClassConjugator coordinate *
          alternatingSixSchurClassRepresentative
            (alternatingSixSchurClassIndex coordinate) *
          (alternatingSixSchurClassConjugator coordinate)⁻¹ =
      coordinate := by
  rw [alternatingSixSchurOrbitMiddle_spec,
    alternatingSixSchurClassConjugatorInverse_spec]
  rw [← alternatingSixSchurInverseFactor_spec, ← mul_assoc,
    alternatingSixSchurOrbitPenultimate_spec,
    alternatingSixSchurOrbitFinish_spec]


end GroupTheory
end McKayConjecture
