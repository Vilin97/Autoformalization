# Reproducible generator-matrix data for the ordinary characters of 6.A6.
#
# Run with GAP 4.16.0 and AtlasRep:
#
#   gap -q scripts/a6_character_matrices.g
#
# The output is deliberately plain GAP syntax.  It is consumed by the Lean
# certificate generator; GAP is only a data generator, and all relations,
# character inner products, and completeness claims are checked again in
# Lean.
#
# Dixon's generic construction is compact through degree nine, but its
# degree-twelve output is unnecessarily dense. For the four degree-twelve
# rows we use the sparse characteristic-zero ATLAS representation
# `6A6G1-Ar12B0` and the four distinct Galois conjugates represented by
# exponents 1, 2, 7, and 11 modulo 15.  The other unit exponents give
# duplicate characters.  Lean independently checks irreducibility and
# completeness, so this choice is only a certificate-size optimization.

if GAPInfo.Version <> "4.16.0" then
  Error("expected GAP 4.16.0, found ", GAPInfo.Version);
fi;

if LoadPackage("atlasrep") <> true then
  Error("the AtlasRep package is required");
fi;

SizeScreen([1000000, 1000000]);

EmitMatrix := function(matrix)
  local rowIndex, columnIndex;
  Print("[");
  for rowIndex in [1 .. Length(matrix)] do
    if rowIndex > 1 then
      Print(",");
    fi;
    Print("[");
    for columnIndex in [1 .. Length(matrix[rowIndex])] do
      if columnIndex > 1 then
        Print(",");
      fi;
      Print(String(matrix[rowIndex][columnIndex]));
    od;
    Print("]");
  od;
  Print("]");
end;

RelationValues := function(a, b)
  return [a^2, b^4, (a * b)^5, (a * b^2)^5];
end;

CorrectedGenerators := function(rawA, rawB)
  local relationValues, firstLatticeValue;
  relationValues := RelationValues(rawA, rawB);
  firstLatticeValue :=
    relationValues[1]^3 * relationValues[3]^-2 * relationValues[4];
  return [rawA * firstLatticeValue^-1, rawB];
end;

CheckSchurRelations := function(a, b)
  local one, relationValues, generator, centralValue;
  one := a^0;
  relationValues := RelationValues(a, b);
  for centralValue in relationValues do
    for generator in Concatenation([a, b], relationValues) do
      if centralValue * generator <> generator * centralValue then
        Error("a corrected central relation value does not commute");
      fi;
    od;
  od;
  if relationValues[1]^3 * relationValues[3]^-2 *
      relationValues[4] <> one then
    Error("the first relation-module row failed");
  fi;
  if relationValues[2]^4 * relationValues[3]^3 *
      relationValues[4]^-3 <> one then
    Error("the second relation-module row failed");
  fi;
end;

group := AtlasGroup("6.A6", IsPermGroup);
characters := Irr(CharacterTable(group));
pPrimeIndices :=
  Filtered([1 .. Length(characters)],
    index -> characters[index][1] mod 5 <> 0);
dixonIndices :=
  Filtered([1 .. Length(characters)],
    index -> characters[index][1] <> 12);

Print("GAP_VERSION ", GAPInfo.Version, "\n");
Print("GROUP_SIZE ", Size(group), "\n");
Print("P5_INDICES ", pPrimeIndices, "\n");
Print("DIXON_INDICES ", dixonIndices, "\n");

for index in dixonIndices do
  representation :=
    IrreducibleRepresentationsDixon(group, characters[index]);
  images :=
    CorrectedGenerators(
      Image(representation, GeneratorsOfGroup(group)[1]),
      Image(representation, GeneratorsOfGroup(group)[2]));
  CheckSchurRelations(images[1], images[2]);

  Print("ROW ", index, "\n");
  Print("DEGREE ", characters[index][1], "\n");
  Print("FIELD ", String(FieldOfMatrixGroup(Image(representation))), "\n");
  Print("CHARACTER ", String(characters[index]), "\n");
  Print("GENERATOR_A ");
  EmitMatrix(images[1]);
  Print("\n");
  Print("GENERATOR_B ");
  EmitMatrix(images[2]);
  Print("\n");
  Print("END_ROW\n");
od;

atlasTwelve := AtlasGenerators("6.A6", 8);
if atlasTwelve = fail then
  Error("the sparse characteristic-zero degree-twelve ATLAS model is required");
fi;
if atlasTwelve.repname <> "6A6G1-Ar12B0" then
  Error("unexpected degree-twelve ATLAS representation: ",
    atlasTwelve.repname);
fi;

for exponent in [1, 2, 7, 11] do
  images :=
    CorrectedGenerators(
      GaloisCyc(atlasTwelve.generators[1], exponent),
      GaloisCyc(atlasTwelve.generators[2], exponent));
  CheckSchurRelations(images[1], images[2]);

  Print("ROW ATLAS12_", exponent, "\n");
  Print("DEGREE 12\n");
  Print("FIELD NF(15,[ 1, 4 ])\n");
  Print("GALOIS_EXPONENT ", exponent, "\n");
  Print("GENERATOR_A ");
  EmitMatrix(images[1]);
  Print("\n");
  Print("GENERATOR_B ");
  EmitMatrix(images[2]);
  Print("\n");
  Print("END_ROW\n");
od;

QUIT;
