/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData00
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData01
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData02
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData03
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData04
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData05
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData06
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData07
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData08
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData09
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData10
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData11
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData12
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData13
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData14
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData15
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData16
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData17
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData18
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData19
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData20
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData21
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData22
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData23
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData24
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData25
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData26
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData27
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData28
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData29
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData30
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData31
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData32
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData33
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData34
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyData35

/-!
# Finite conjugacy data for the sixfold cover of `A₆`

This generated interface combines the blockwise class labels and orbit
witnesses.  Its companion check files verify that labels are invariant under
the two noncentral presentation generators and that every coordinate is
conjugate to its advertised representative.
-/

namespace McKayConjecture
namespace GroupTheory

open AlternatingSixSchurCoordinates

set_option linter.style.longLine false

/-- The coordinate of the presentation generator `a`. -/
def alternatingSixSchurCoordinateA :
    AlternatingSixSchurCoordinates :=
  ⟨1, 0⟩

/-- The coordinate of the presentation generator `b`. -/
def alternatingSixSchurCoordinateB :
    AlternatingSixSchurCoordinates :=
  ⟨2, 0⟩

/-- The canonical representative of each advertised conjugacy class. -/
def alternatingSixSchurClassRepresentative :
    Fin 31 → AlternatingSixSchurCoordinates :=
  fun index =>
    match index.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨0, 1⟩
    | 2 => ⟨0, 2⟩
    | 3 => ⟨0, 3⟩
    | 4 => ⟨0, 4⟩
    | 5 => ⟨0, 5⟩
    | 6 => ⟨1, 0⟩
    | 7 => ⟨1, 1⟩
    | 8 => ⟨1, 2⟩
    | 9 => ⟨2, 0⟩
    | 10 => ⟨2, 1⟩
    | 11 => ⟨2, 2⟩
    | 12 => ⟨2, 3⟩
    | 13 => ⟨2, 4⟩
    | 14 => ⟨2, 5⟩
    | 15 => ⟨4, 0⟩
    | 16 => ⟨4, 1⟩
    | 17 => ⟨4, 2⟩
    | 18 => ⟨4, 3⟩
    | 19 => ⟨4, 4⟩
    | 20 => ⟨4, 5⟩
    | 21 => ⟨10, 0⟩
    | 22 => ⟨10, 1⟩
    | 23 => ⟨10, 2⟩
    | 24 => ⟨10, 3⟩
    | 25 => ⟨10, 4⟩
    | 26 => ⟨10, 5⟩
    | 27 => ⟨77, 0⟩
    | 28 => ⟨77, 1⟩
    | 29 => ⟨79, 0⟩
    | _ => ⟨79, 1⟩

/-- The externally discovered size of each advertised class.
These values are metadata; class completeness is proved from checked orbit
witnesses rather than assumed from their sum. -/
def alternatingSixSchurClassSize :
    Fin 31 → Nat :=
  ![1, 1, 1, 1, 1, 1, 90, 90, 90, 90, 90, 90, 90, 90, 90, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 120, 120, 120, 120]

/-- The packed checked data attached to a coordinate. -/
def alternatingSixSchurConjugacyDatum
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurConjugacyDatum :=
  let central := (ZMod.finEquiv 6).symm coordinate.central
  match coordinate.state.val with
  | 0 => alternatingSixSchurConjugacyDatumRow000 central
  | 1 => alternatingSixSchurConjugacyDatumRow001 central
  | 2 => alternatingSixSchurConjugacyDatumRow002 central
  | 3 => alternatingSixSchurConjugacyDatumRow003 central
  | 4 => alternatingSixSchurConjugacyDatumRow004 central
  | 5 => alternatingSixSchurConjugacyDatumRow005 central
  | 6 => alternatingSixSchurConjugacyDatumRow006 central
  | 7 => alternatingSixSchurConjugacyDatumRow007 central
  | 8 => alternatingSixSchurConjugacyDatumRow008 central
  | 9 => alternatingSixSchurConjugacyDatumRow009 central
  | 10 => alternatingSixSchurConjugacyDatumRow010 central
  | 11 => alternatingSixSchurConjugacyDatumRow011 central
  | 12 => alternatingSixSchurConjugacyDatumRow012 central
  | 13 => alternatingSixSchurConjugacyDatumRow013 central
  | 14 => alternatingSixSchurConjugacyDatumRow014 central
  | 15 => alternatingSixSchurConjugacyDatumRow015 central
  | 16 => alternatingSixSchurConjugacyDatumRow016 central
  | 17 => alternatingSixSchurConjugacyDatumRow017 central
  | 18 => alternatingSixSchurConjugacyDatumRow018 central
  | 19 => alternatingSixSchurConjugacyDatumRow019 central
  | 20 => alternatingSixSchurConjugacyDatumRow020 central
  | 21 => alternatingSixSchurConjugacyDatumRow021 central
  | 22 => alternatingSixSchurConjugacyDatumRow022 central
  | 23 => alternatingSixSchurConjugacyDatumRow023 central
  | 24 => alternatingSixSchurConjugacyDatumRow024 central
  | 25 => alternatingSixSchurConjugacyDatumRow025 central
  | 26 => alternatingSixSchurConjugacyDatumRow026 central
  | 27 => alternatingSixSchurConjugacyDatumRow027 central
  | 28 => alternatingSixSchurConjugacyDatumRow028 central
  | 29 => alternatingSixSchurConjugacyDatumRow029 central
  | 30 => alternatingSixSchurConjugacyDatumRow030 central
  | 31 => alternatingSixSchurConjugacyDatumRow031 central
  | 32 => alternatingSixSchurConjugacyDatumRow032 central
  | 33 => alternatingSixSchurConjugacyDatumRow033 central
  | 34 => alternatingSixSchurConjugacyDatumRow034 central
  | 35 => alternatingSixSchurConjugacyDatumRow035 central
  | 36 => alternatingSixSchurConjugacyDatumRow036 central
  | 37 => alternatingSixSchurConjugacyDatumRow037 central
  | 38 => alternatingSixSchurConjugacyDatumRow038 central
  | 39 => alternatingSixSchurConjugacyDatumRow039 central
  | 40 => alternatingSixSchurConjugacyDatumRow040 central
  | 41 => alternatingSixSchurConjugacyDatumRow041 central
  | 42 => alternatingSixSchurConjugacyDatumRow042 central
  | 43 => alternatingSixSchurConjugacyDatumRow043 central
  | 44 => alternatingSixSchurConjugacyDatumRow044 central
  | 45 => alternatingSixSchurConjugacyDatumRow045 central
  | 46 => alternatingSixSchurConjugacyDatumRow046 central
  | 47 => alternatingSixSchurConjugacyDatumRow047 central
  | 48 => alternatingSixSchurConjugacyDatumRow048 central
  | 49 => alternatingSixSchurConjugacyDatumRow049 central
  | 50 => alternatingSixSchurConjugacyDatumRow050 central
  | 51 => alternatingSixSchurConjugacyDatumRow051 central
  | 52 => alternatingSixSchurConjugacyDatumRow052 central
  | 53 => alternatingSixSchurConjugacyDatumRow053 central
  | 54 => alternatingSixSchurConjugacyDatumRow054 central
  | 55 => alternatingSixSchurConjugacyDatumRow055 central
  | 56 => alternatingSixSchurConjugacyDatumRow056 central
  | 57 => alternatingSixSchurConjugacyDatumRow057 central
  | 58 => alternatingSixSchurConjugacyDatumRow058 central
  | 59 => alternatingSixSchurConjugacyDatumRow059 central
  | 60 => alternatingSixSchurConjugacyDatumRow060 central
  | 61 => alternatingSixSchurConjugacyDatumRow061 central
  | 62 => alternatingSixSchurConjugacyDatumRow062 central
  | 63 => alternatingSixSchurConjugacyDatumRow063 central
  | 64 => alternatingSixSchurConjugacyDatumRow064 central
  | 65 => alternatingSixSchurConjugacyDatumRow065 central
  | 66 => alternatingSixSchurConjugacyDatumRow066 central
  | 67 => alternatingSixSchurConjugacyDatumRow067 central
  | 68 => alternatingSixSchurConjugacyDatumRow068 central
  | 69 => alternatingSixSchurConjugacyDatumRow069 central
  | 70 => alternatingSixSchurConjugacyDatumRow070 central
  | 71 => alternatingSixSchurConjugacyDatumRow071 central
  | 72 => alternatingSixSchurConjugacyDatumRow072 central
  | 73 => alternatingSixSchurConjugacyDatumRow073 central
  | 74 => alternatingSixSchurConjugacyDatumRow074 central
  | 75 => alternatingSixSchurConjugacyDatumRow075 central
  | 76 => alternatingSixSchurConjugacyDatumRow076 central
  | 77 => alternatingSixSchurConjugacyDatumRow077 central
  | 78 => alternatingSixSchurConjugacyDatumRow078 central
  | 79 => alternatingSixSchurConjugacyDatumRow079 central
  | 80 => alternatingSixSchurConjugacyDatumRow080 central
  | 81 => alternatingSixSchurConjugacyDatumRow081 central
  | 82 => alternatingSixSchurConjugacyDatumRow082 central
  | 83 => alternatingSixSchurConjugacyDatumRow083 central
  | 84 => alternatingSixSchurConjugacyDatumRow084 central
  | 85 => alternatingSixSchurConjugacyDatumRow085 central
  | 86 => alternatingSixSchurConjugacyDatumRow086 central
  | 87 => alternatingSixSchurConjugacyDatumRow087 central
  | 88 => alternatingSixSchurConjugacyDatumRow088 central
  | 89 => alternatingSixSchurConjugacyDatumRow089 central
  | 90 => alternatingSixSchurConjugacyDatumRow090 central
  | 91 => alternatingSixSchurConjugacyDatumRow091 central
  | 92 => alternatingSixSchurConjugacyDatumRow092 central
  | 93 => alternatingSixSchurConjugacyDatumRow093 central
  | 94 => alternatingSixSchurConjugacyDatumRow094 central
  | 95 => alternatingSixSchurConjugacyDatumRow095 central
  | 96 => alternatingSixSchurConjugacyDatumRow096 central
  | 97 => alternatingSixSchurConjugacyDatumRow097 central
  | 98 => alternatingSixSchurConjugacyDatumRow098 central
  | 99 => alternatingSixSchurConjugacyDatumRow099 central
  | 100 => alternatingSixSchurConjugacyDatumRow100 central
  | 101 => alternatingSixSchurConjugacyDatumRow101 central
  | 102 => alternatingSixSchurConjugacyDatumRow102 central
  | 103 => alternatingSixSchurConjugacyDatumRow103 central
  | 104 => alternatingSixSchurConjugacyDatumRow104 central
  | 105 => alternatingSixSchurConjugacyDatumRow105 central
  | 106 => alternatingSixSchurConjugacyDatumRow106 central
  | 107 => alternatingSixSchurConjugacyDatumRow107 central
  | 108 => alternatingSixSchurConjugacyDatumRow108 central
  | 109 => alternatingSixSchurConjugacyDatumRow109 central
  | 110 => alternatingSixSchurConjugacyDatumRow110 central
  | 111 => alternatingSixSchurConjugacyDatumRow111 central
  | 112 => alternatingSixSchurConjugacyDatumRow112 central
  | 113 => alternatingSixSchurConjugacyDatumRow113 central
  | 114 => alternatingSixSchurConjugacyDatumRow114 central
  | 115 => alternatingSixSchurConjugacyDatumRow115 central
  | 116 => alternatingSixSchurConjugacyDatumRow116 central
  | 117 => alternatingSixSchurConjugacyDatumRow117 central
  | 118 => alternatingSixSchurConjugacyDatumRow118 central
  | 119 => alternatingSixSchurConjugacyDatumRow119 central
  | 120 => alternatingSixSchurConjugacyDatumRow120 central
  | 121 => alternatingSixSchurConjugacyDatumRow121 central
  | 122 => alternatingSixSchurConjugacyDatumRow122 central
  | 123 => alternatingSixSchurConjugacyDatumRow123 central
  | 124 => alternatingSixSchurConjugacyDatumRow124 central
  | 125 => alternatingSixSchurConjugacyDatumRow125 central
  | 126 => alternatingSixSchurConjugacyDatumRow126 central
  | 127 => alternatingSixSchurConjugacyDatumRow127 central
  | 128 => alternatingSixSchurConjugacyDatumRow128 central
  | 129 => alternatingSixSchurConjugacyDatumRow129 central
  | 130 => alternatingSixSchurConjugacyDatumRow130 central
  | 131 => alternatingSixSchurConjugacyDatumRow131 central
  | 132 => alternatingSixSchurConjugacyDatumRow132 central
  | 133 => alternatingSixSchurConjugacyDatumRow133 central
  | 134 => alternatingSixSchurConjugacyDatumRow134 central
  | 135 => alternatingSixSchurConjugacyDatumRow135 central
  | 136 => alternatingSixSchurConjugacyDatumRow136 central
  | 137 => alternatingSixSchurConjugacyDatumRow137 central
  | 138 => alternatingSixSchurConjugacyDatumRow138 central
  | 139 => alternatingSixSchurConjugacyDatumRow139 central
  | 140 => alternatingSixSchurConjugacyDatumRow140 central
  | 141 => alternatingSixSchurConjugacyDatumRow141 central
  | 142 => alternatingSixSchurConjugacyDatumRow142 central
  | 143 => alternatingSixSchurConjugacyDatumRow143 central
  | 144 => alternatingSixSchurConjugacyDatumRow144 central
  | 145 => alternatingSixSchurConjugacyDatumRow145 central
  | 146 => alternatingSixSchurConjugacyDatumRow146 central
  | 147 => alternatingSixSchurConjugacyDatumRow147 central
  | 148 => alternatingSixSchurConjugacyDatumRow148 central
  | 149 => alternatingSixSchurConjugacyDatumRow149 central
  | 150 => alternatingSixSchurConjugacyDatumRow150 central
  | 151 => alternatingSixSchurConjugacyDatumRow151 central
  | 152 => alternatingSixSchurConjugacyDatumRow152 central
  | 153 => alternatingSixSchurConjugacyDatumRow153 central
  | 154 => alternatingSixSchurConjugacyDatumRow154 central
  | 155 => alternatingSixSchurConjugacyDatumRow155 central
  | 156 => alternatingSixSchurConjugacyDatumRow156 central
  | 157 => alternatingSixSchurConjugacyDatumRow157 central
  | 158 => alternatingSixSchurConjugacyDatumRow158 central
  | 159 => alternatingSixSchurConjugacyDatumRow159 central
  | 160 => alternatingSixSchurConjugacyDatumRow160 central
  | 161 => alternatingSixSchurConjugacyDatumRow161 central
  | 162 => alternatingSixSchurConjugacyDatumRow162 central
  | 163 => alternatingSixSchurConjugacyDatumRow163 central
  | 164 => alternatingSixSchurConjugacyDatumRow164 central
  | 165 => alternatingSixSchurConjugacyDatumRow165 central
  | 166 => alternatingSixSchurConjugacyDatumRow166 central
  | 167 => alternatingSixSchurConjugacyDatumRow167 central
  | 168 => alternatingSixSchurConjugacyDatumRow168 central
  | 169 => alternatingSixSchurConjugacyDatumRow169 central
  | 170 => alternatingSixSchurConjugacyDatumRow170 central
  | 171 => alternatingSixSchurConjugacyDatumRow171 central
  | 172 => alternatingSixSchurConjugacyDatumRow172 central
  | 173 => alternatingSixSchurConjugacyDatumRow173 central
  | 174 => alternatingSixSchurConjugacyDatumRow174 central
  | 175 => alternatingSixSchurConjugacyDatumRow175 central
  | 176 => alternatingSixSchurConjugacyDatumRow176 central
  | 177 => alternatingSixSchurConjugacyDatumRow177 central
  | 178 => alternatingSixSchurConjugacyDatumRow178 central
  | 179 => alternatingSixSchurConjugacyDatumRow179 central
  | 180 => alternatingSixSchurConjugacyDatumRow180 central
  | 181 => alternatingSixSchurConjugacyDatumRow181 central
  | 182 => alternatingSixSchurConjugacyDatumRow182 central
  | 183 => alternatingSixSchurConjugacyDatumRow183 central
  | 184 => alternatingSixSchurConjugacyDatumRow184 central
  | 185 => alternatingSixSchurConjugacyDatumRow185 central
  | 186 => alternatingSixSchurConjugacyDatumRow186 central
  | 187 => alternatingSixSchurConjugacyDatumRow187 central
  | 188 => alternatingSixSchurConjugacyDatumRow188 central
  | 189 => alternatingSixSchurConjugacyDatumRow189 central
  | 190 => alternatingSixSchurConjugacyDatumRow190 central
  | 191 => alternatingSixSchurConjugacyDatumRow191 central
  | 192 => alternatingSixSchurConjugacyDatumRow192 central
  | 193 => alternatingSixSchurConjugacyDatumRow193 central
  | 194 => alternatingSixSchurConjugacyDatumRow194 central
  | 195 => alternatingSixSchurConjugacyDatumRow195 central
  | 196 => alternatingSixSchurConjugacyDatumRow196 central
  | 197 => alternatingSixSchurConjugacyDatumRow197 central
  | 198 => alternatingSixSchurConjugacyDatumRow198 central
  | 199 => alternatingSixSchurConjugacyDatumRow199 central
  | 200 => alternatingSixSchurConjugacyDatumRow200 central
  | 201 => alternatingSixSchurConjugacyDatumRow201 central
  | 202 => alternatingSixSchurConjugacyDatumRow202 central
  | 203 => alternatingSixSchurConjugacyDatumRow203 central
  | 204 => alternatingSixSchurConjugacyDatumRow204 central
  | 205 => alternatingSixSchurConjugacyDatumRow205 central
  | 206 => alternatingSixSchurConjugacyDatumRow206 central
  | 207 => alternatingSixSchurConjugacyDatumRow207 central
  | 208 => alternatingSixSchurConjugacyDatumRow208 central
  | 209 => alternatingSixSchurConjugacyDatumRow209 central
  | 210 => alternatingSixSchurConjugacyDatumRow210 central
  | 211 => alternatingSixSchurConjugacyDatumRow211 central
  | 212 => alternatingSixSchurConjugacyDatumRow212 central
  | 213 => alternatingSixSchurConjugacyDatumRow213 central
  | 214 => alternatingSixSchurConjugacyDatumRow214 central
  | 215 => alternatingSixSchurConjugacyDatumRow215 central
  | 216 => alternatingSixSchurConjugacyDatumRow216 central
  | 217 => alternatingSixSchurConjugacyDatumRow217 central
  | 218 => alternatingSixSchurConjugacyDatumRow218 central
  | 219 => alternatingSixSchurConjugacyDatumRow219 central
  | 220 => alternatingSixSchurConjugacyDatumRow220 central
  | 221 => alternatingSixSchurConjugacyDatumRow221 central
  | 222 => alternatingSixSchurConjugacyDatumRow222 central
  | 223 => alternatingSixSchurConjugacyDatumRow223 central
  | 224 => alternatingSixSchurConjugacyDatumRow224 central
  | 225 => alternatingSixSchurConjugacyDatumRow225 central
  | 226 => alternatingSixSchurConjugacyDatumRow226 central
  | 227 => alternatingSixSchurConjugacyDatumRow227 central
  | 228 => alternatingSixSchurConjugacyDatumRow228 central
  | 229 => alternatingSixSchurConjugacyDatumRow229 central
  | 230 => alternatingSixSchurConjugacyDatumRow230 central
  | 231 => alternatingSixSchurConjugacyDatumRow231 central
  | 232 => alternatingSixSchurConjugacyDatumRow232 central
  | 233 => alternatingSixSchurConjugacyDatumRow233 central
  | 234 => alternatingSixSchurConjugacyDatumRow234 central
  | 235 => alternatingSixSchurConjugacyDatumRow235 central
  | 236 => alternatingSixSchurConjugacyDatumRow236 central
  | 237 => alternatingSixSchurConjugacyDatumRow237 central
  | 238 => alternatingSixSchurConjugacyDatumRow238 central
  | 239 => alternatingSixSchurConjugacyDatumRow239 central
  | 240 => alternatingSixSchurConjugacyDatumRow240 central
  | 241 => alternatingSixSchurConjugacyDatumRow241 central
  | 242 => alternatingSixSchurConjugacyDatumRow242 central
  | 243 => alternatingSixSchurConjugacyDatumRow243 central
  | 244 => alternatingSixSchurConjugacyDatumRow244 central
  | 245 => alternatingSixSchurConjugacyDatumRow245 central
  | 246 => alternatingSixSchurConjugacyDatumRow246 central
  | 247 => alternatingSixSchurConjugacyDatumRow247 central
  | 248 => alternatingSixSchurConjugacyDatumRow248 central
  | 249 => alternatingSixSchurConjugacyDatumRow249 central
  | 250 => alternatingSixSchurConjugacyDatumRow250 central
  | 251 => alternatingSixSchurConjugacyDatumRow251 central
  | 252 => alternatingSixSchurConjugacyDatumRow252 central
  | 253 => alternatingSixSchurConjugacyDatumRow253 central
  | 254 => alternatingSixSchurConjugacyDatumRow254 central
  | 255 => alternatingSixSchurConjugacyDatumRow255 central
  | 256 => alternatingSixSchurConjugacyDatumRow256 central
  | 257 => alternatingSixSchurConjugacyDatumRow257 central
  | 258 => alternatingSixSchurConjugacyDatumRow258 central
  | 259 => alternatingSixSchurConjugacyDatumRow259 central
  | 260 => alternatingSixSchurConjugacyDatumRow260 central
  | 261 => alternatingSixSchurConjugacyDatumRow261 central
  | 262 => alternatingSixSchurConjugacyDatumRow262 central
  | 263 => alternatingSixSchurConjugacyDatumRow263 central
  | 264 => alternatingSixSchurConjugacyDatumRow264 central
  | 265 => alternatingSixSchurConjugacyDatumRow265 central
  | 266 => alternatingSixSchurConjugacyDatumRow266 central
  | 267 => alternatingSixSchurConjugacyDatumRow267 central
  | 268 => alternatingSixSchurConjugacyDatumRow268 central
  | 269 => alternatingSixSchurConjugacyDatumRow269 central
  | 270 => alternatingSixSchurConjugacyDatumRow270 central
  | 271 => alternatingSixSchurConjugacyDatumRow271 central
  | 272 => alternatingSixSchurConjugacyDatumRow272 central
  | 273 => alternatingSixSchurConjugacyDatumRow273 central
  | 274 => alternatingSixSchurConjugacyDatumRow274 central
  | 275 => alternatingSixSchurConjugacyDatumRow275 central
  | 276 => alternatingSixSchurConjugacyDatumRow276 central
  | 277 => alternatingSixSchurConjugacyDatumRow277 central
  | 278 => alternatingSixSchurConjugacyDatumRow278 central
  | 279 => alternatingSixSchurConjugacyDatumRow279 central
  | 280 => alternatingSixSchurConjugacyDatumRow280 central
  | 281 => alternatingSixSchurConjugacyDatumRow281 central
  | 282 => alternatingSixSchurConjugacyDatumRow282 central
  | 283 => alternatingSixSchurConjugacyDatumRow283 central
  | 284 => alternatingSixSchurConjugacyDatumRow284 central
  | 285 => alternatingSixSchurConjugacyDatumRow285 central
  | 286 => alternatingSixSchurConjugacyDatumRow286 central
  | 287 => alternatingSixSchurConjugacyDatumRow287 central
  | 288 => alternatingSixSchurConjugacyDatumRow288 central
  | 289 => alternatingSixSchurConjugacyDatumRow289 central
  | 290 => alternatingSixSchurConjugacyDatumRow290 central
  | 291 => alternatingSixSchurConjugacyDatumRow291 central
  | 292 => alternatingSixSchurConjugacyDatumRow292 central
  | 293 => alternatingSixSchurConjugacyDatumRow293 central
  | 294 => alternatingSixSchurConjugacyDatumRow294 central
  | 295 => alternatingSixSchurConjugacyDatumRow295 central
  | 296 => alternatingSixSchurConjugacyDatumRow296 central
  | 297 => alternatingSixSchurConjugacyDatumRow297 central
  | 298 => alternatingSixSchurConjugacyDatumRow298 central
  | 299 => alternatingSixSchurConjugacyDatumRow299 central
  | 300 => alternatingSixSchurConjugacyDatumRow300 central
  | 301 => alternatingSixSchurConjugacyDatumRow301 central
  | 302 => alternatingSixSchurConjugacyDatumRow302 central
  | 303 => alternatingSixSchurConjugacyDatumRow303 central
  | 304 => alternatingSixSchurConjugacyDatumRow304 central
  | 305 => alternatingSixSchurConjugacyDatumRow305 central
  | 306 => alternatingSixSchurConjugacyDatumRow306 central
  | 307 => alternatingSixSchurConjugacyDatumRow307 central
  | 308 => alternatingSixSchurConjugacyDatumRow308 central
  | 309 => alternatingSixSchurConjugacyDatumRow309 central
  | 310 => alternatingSixSchurConjugacyDatumRow310 central
  | 311 => alternatingSixSchurConjugacyDatumRow311 central
  | 312 => alternatingSixSchurConjugacyDatumRow312 central
  | 313 => alternatingSixSchurConjugacyDatumRow313 central
  | 314 => alternatingSixSchurConjugacyDatumRow314 central
  | 315 => alternatingSixSchurConjugacyDatumRow315 central
  | 316 => alternatingSixSchurConjugacyDatumRow316 central
  | 317 => alternatingSixSchurConjugacyDatumRow317 central
  | 318 => alternatingSixSchurConjugacyDatumRow318 central
  | 319 => alternatingSixSchurConjugacyDatumRow319 central
  | 320 => alternatingSixSchurConjugacyDatumRow320 central
  | 321 => alternatingSixSchurConjugacyDatumRow321 central
  | 322 => alternatingSixSchurConjugacyDatumRow322 central
  | 323 => alternatingSixSchurConjugacyDatumRow323 central
  | 324 => alternatingSixSchurConjugacyDatumRow324 central
  | 325 => alternatingSixSchurConjugacyDatumRow325 central
  | 326 => alternatingSixSchurConjugacyDatumRow326 central
  | 327 => alternatingSixSchurConjugacyDatumRow327 central
  | 328 => alternatingSixSchurConjugacyDatumRow328 central
  | 329 => alternatingSixSchurConjugacyDatumRow329 central
  | 330 => alternatingSixSchurConjugacyDatumRow330 central
  | 331 => alternatingSixSchurConjugacyDatumRow331 central
  | 332 => alternatingSixSchurConjugacyDatumRow332 central
  | 333 => alternatingSixSchurConjugacyDatumRow333 central
  | 334 => alternatingSixSchurConjugacyDatumRow334 central
  | 335 => alternatingSixSchurConjugacyDatumRow335 central
  | 336 => alternatingSixSchurConjugacyDatumRow336 central
  | 337 => alternatingSixSchurConjugacyDatumRow337 central
  | 338 => alternatingSixSchurConjugacyDatumRow338 central
  | 339 => alternatingSixSchurConjugacyDatumRow339 central
  | 340 => alternatingSixSchurConjugacyDatumRow340 central
  | 341 => alternatingSixSchurConjugacyDatumRow341 central
  | 342 => alternatingSixSchurConjugacyDatumRow342 central
  | 343 => alternatingSixSchurConjugacyDatumRow343 central
  | 344 => alternatingSixSchurConjugacyDatumRow344 central
  | 345 => alternatingSixSchurConjugacyDatumRow345 central
  | 346 => alternatingSixSchurConjugacyDatumRow346 central
  | 347 => alternatingSixSchurConjugacyDatumRow347 central
  | 348 => alternatingSixSchurConjugacyDatumRow348 central
  | 349 => alternatingSixSchurConjugacyDatumRow349 central
  | 350 => alternatingSixSchurConjugacyDatumRow350 central
  | 351 => alternatingSixSchurConjugacyDatumRow351 central
  | 352 => alternatingSixSchurConjugacyDatumRow352 central
  | 353 => alternatingSixSchurConjugacyDatumRow353 central
  | 354 => alternatingSixSchurConjugacyDatumRow354 central
  | 355 => alternatingSixSchurConjugacyDatumRow355 central
  | 356 => alternatingSixSchurConjugacyDatumRow356 central
  | 357 => alternatingSixSchurConjugacyDatumRow357 central
  | 358 => alternatingSixSchurConjugacyDatumRow358 central
  | _ => alternatingSixSchurConjugacyDatumRow359 central

/-- The checked-data label of a coordinate. -/
def alternatingSixSchurClassIndex
    (coordinate : AlternatingSixSchurCoordinates) :
    Fin 31 :=
  (alternatingSixSchurConjugacyDatum coordinate).classIndex

/-- A checked-data conjugator carrying the representative of a
coordinate's label to that coordinate.  Its central coordinate can be chosen
to be zero because central factors do not affect conjugation. -/
def alternatingSixSchurClassConjugator
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  ⟨(alternatingSixSchurConjugacyDatum coordinate).conjugatorState, 0⟩

/-- The tabulated first product in an orbit witness. -/
def alternatingSixSchurOrbitMiddle
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  let datum := alternatingSixSchurConjugacyDatum coordinate
  ⟨datum.orbitMiddleState,
    (ZMod.finEquiv 6) datum.orbitMiddleCentral⟩

/-- The tabulated inverse of an orbit conjugator. -/
def alternatingSixSchurClassConjugatorInverse
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  let datum := alternatingSixSchurConjugacyDatum coordinate
  ⟨datum.conjugatorInverseState,
    (ZMod.finEquiv 6) datum.conjugatorInverseCentral⟩

/-- The left short factor of the inverse conjugator. -/
def alternatingSixSchurInverseFactorLeft
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  let datum := alternatingSixSchurConjugacyDatum coordinate
  ⟨datum.inverseFactorLeftState,
    (ZMod.finEquiv 6) datum.inverseFactorLeftCentral⟩

/-- The right short factor of the inverse conjugator. -/
def alternatingSixSchurInverseFactorRight
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  let datum := alternatingSixSchurConjugacyDatum coordinate
  ⟨datum.inverseFactorRightState,
    (ZMod.finEquiv 6) datum.inverseFactorRightCentral⟩

/-- The penultimate product in the split orbit witness. -/
def alternatingSixSchurOrbitPenultimate
    (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurCoordinates :=
  let datum := alternatingSixSchurConjugacyDatum coordinate
  ⟨datum.orbitPenultimateState,
    (ZMod.finEquiv 6) datum.orbitPenultimateCentral⟩


end GroupTheory
end McKayConjecture
