# Reproducible GAP/CTblLib audit for the outer actions used in the A6 case.
#
# Tested with GAP 4.16.0 and CTblLib 1.3.11.  Run from the repository root as
#
#   gap -q mckay-conjecture/scripts/a6_outer_action_audit.g
#
# This script proves computational facts about explicit finite groups and
# character tables.  It does *not* prove that the finite permutations copied
# into Lean arise from automorphisms of the Lean groups.  That bridge is a
# separate formalization obligation.

if LoadPackage("ctbllib") = fail then
  Error("the CTblLib package is required");
fi;

AuditAssert := function(condition, message)
  if not condition then
    Error(message);
  fi;
end;

AuditAssertEqual := function(message, actual, expected)
  if actual <> expected then
    Error(Concatenation(
      message, "\nactual: ", String(actual),
      "\nexpected: ", String(expected)));
  fi;
end;

# Find all lifts of an automorphism through a central cover.  In the case at
# hand there are only 6^2 possible central corrections to inspect.
AllCentralLifts := function(coverGroup, coverProjection, quotientAutomorphism)
  local coverGenerators, kernelElements, baseImages, result, correction,
        images, candidate;
  coverGenerators := GeneratorsOfGroup(coverGroup);
  kernelElements := Elements(Kernel(coverProjection));
  baseImages := List(
    coverGenerators,
    generator -> PreImagesRepresentative(
      coverProjection,
      Image(quotientAutomorphism, Image(coverProjection, generator))));
  result := [];
  for correction in Cartesian(
      List(coverGenerators, generator -> kernelElements)) do
    images := List(
      [1 .. Length(coverGenerators)],
      index -> baseImages[index] * correction[index]);
    candidate := GroupHomomorphismByImages(
      coverGroup, coverGroup, coverGenerators, images);
    if candidate <> fail and IsBijective(candidate) then
      Add(result, candidate);
    fi;
  od;
  return result;
end;

ClassPermutationFromAutomorphism := function(group, automorphism)
  local classes;
  classes := ConjugacyClasses(group);
  return PermList(List(
    classes,
    class -> PositionProperty(
      classes,
      imageClass ->
        Image(automorphism, Representative(class)) in imageClass)));
end;

# If classPermutation sends a class to its automorphic image, this is the
# induced permutation of Irr(table) in GAP's stored row order.
RowPermutationFromClassPermutation := function(table, classPermutation)
  local irreducibles;
  irreducibles := Irr(table);
  return PermList(List(
    [1 .. Length(irreducibles)],
    index -> Position(
      irreducibles,
      Permuted(irreducibles[index], classPermutation))));
end;

# A column alignment maps computed class indices to CTblLib class indices.
# Character rows have no repetitions, so their induced alignment is unique.
RowAlignmentFromColumns := function(computedTable, storedTable, columns)
  return PermList(List(
    [1 .. Length(Irr(computedTable))],
    index -> Position(
      Irr(storedTable),
      Permuted(Irr(computedTable)[index], columns))));
end;

# Convert a fusion in computed class orders to the two chosen stored orders.
TransportedFusion := function(computedFusion, sourceColumns, targetColumns)
  return List(
    [1 .. Length(computedFusion)],
    storedSourceIndex ->
      computedFusion[storedSourceIndex ^ (sourceColumns^-1)]
        ^ targetColumns);
end;

CompatibleColumnAlignments := function(
    computedSourceTable, storedSourceTable, computedTargetTable,
    storedTargetTable, computedFusion, storedFusion, targetColumns)
  local transformation, candidates;
  transformation := TransformingPermutationsCharacterTables(
    computedSourceTable, storedSourceTable);
  AuditAssert(
    transformation <> fail,
    "computed and stored character tables are not isomorphic");
  candidates := List(
    Elements(transformation.group),
    tableAutomorphism -> transformation.columns * tableAutomorphism);
  return Filtered(
    candidates,
    sourceColumns ->
      TransportedFusion(
        computedFusion, sourceColumns, targetColumns) = storedFusion);
end;

TransportedClassPermutation := function(classPermutation, columns)
  return columns^-1 * classPermutation * columns;
end;

TransportedRowPermutation := function(
    computedTable, storedTable, rowPermutation, columns)
  local rows;
  rows := RowAlignmentFromColumns(computedTable, storedTable, columns);
  return rows^-1 * rowPermutation * rows;
end;

AdjustAutomorphismToSylow := function(
    coverGroup, coverGenerators, automorphism, sylowSubgroup)
  local conjugator, adjusted;
  conjugator := RepresentativeAction(
    coverGroup, Image(automorphism, sylowSubgroup), sylowSubgroup);
  AuditAssert(
    conjugator <> fail,
    "the automorphic image of the Sylow subgroup is not conjugate to it");
  adjusted := GroupHomomorphismByImages(
    coverGroup,
    coverGroup,
    coverGenerators,
    List(
      coverGenerators,
      generator -> Image(automorphism, generator) ^ conjugator));
  AuditAssert(
    adjusted <> fail and IsBijective(adjusted),
    "failed to construct the Sylow-stabilizing adjustment");
  AuditAssert(
    Image(adjusted, sylowSubgroup) = sylowSubgroup,
    "the adjusted automorphism does not stabilize the Sylow subgroup");
  return adjusted;
end;

PPrimeRows := function(table, prime)
  return Filtered(
    [1 .. Length(Irr(table))],
    index -> Irr(table)[index][1] mod prime <> 0);
end;

PPrimeImages := function(rowPermutation, rows)
  return List(rows, row -> row ^ rowPermutation);
end;

CentralScalarExponent := function(table, centralClass, row)
  local scalar, sixthRoots, position;
  scalar := Irr(table)[row][centralClass] / Irr(table)[row][1];
  sixthRoots := List([0 .. 5], exponent -> E(6)^exponent);
  position := Position(sixthRoots, scalar);
  AuditAssert(
    position <> fail,
    "a central scalar is not a sixth root of unity");
  return position - 1;
end;

CheckCandidateBijection := function(
    caseData, ambientTable, localTable, ambientRowActions, localRowActions,
    localFusion)
  local pairs, ambientRows, localRows, imageOfAmbient, generatorIndex,
        pair, ambientImage, localImage, localCentralClasses;
  pairs := caseData.candidatePairs;
  ambientRows := List(pairs, pair -> pair[1]);
  localRows := List(pairs, pair -> pair[2]);
  AuditAssertEqual(
    Concatenation("wrong ambient p-prime rows for p=", String(caseData.prime)),
    Set(ambientRows),
    Set(PPrimeRows(ambientTable, caseData.prime)));
  AuditAssertEqual(
    Concatenation("wrong local p-prime rows for p=", String(caseData.prime)),
    Set(localRows),
    Set(PPrimeRows(localTable, caseData.prime)));
  AuditAssertEqual(
    Concatenation("candidate is not injective for p=", String(caseData.prime)),
    Length(Set(localRows)),
    Length(localRows));

  imageOfAmbient := function(ambientRow)
    local position;
    position := Position(ambientRows, ambientRow);
    AuditAssert(position <> fail, "candidate queried outside its domain");
    return localRows[position];
  end;

  for generatorIndex in [1, 2] do
    for pair in pairs do
      ambientImage := pair[1] ^ ambientRowActions[generatorIndex];
      localImage := pair[2] ^ localRowActions[generatorIndex];
      AuditAssertEqual(
        Concatenation(
          "generator equivariance failed for p=", String(caseData.prime),
          ", generator=", String(generatorIndex)),
        imageOfAmbient(ambientImage),
        localImage);
    od;
  od;

  localCentralClasses := Filtered(
    [1 .. Length(localFusion)],
    classIndex -> localFusion[classIndex] = 2);
  AuditAssertEqual(
    Concatenation(
      "the local table does not have a unique class over central class 2, p=",
      String(caseData.prime)),
    Length(localCentralClasses),
    1);
  for pair in pairs do
    AuditAssertEqual(
      Concatenation(
        "central scalar preservation failed for p=",
        String(caseData.prime)),
      CentralScalarExponent(ambientTable, 2, pair[1]),
      CentralScalarExponent(localTable, localCentralClasses[1], pair[2]));
  od;
end;

# Select the unique lifts of the project's exact permutations
#
#   a = (1,2)(3,4),  b = (1,2,3,5)(4,6)
#
# for which the two relation-module rows hold.  Central corrections of the
# two initial preimages give only 6^2 pairs to inspect.
CanonicalSchurPresentationImages := function(
    coverGroup, coverProjection, quotientA, quotientB)
  local kernelElements, initialA, initialB, candidates, correctionA,
        correctionB, imageA, imageB, centralImages;
  kernelElements := Elements(Kernel(coverProjection));
  initialA := PreImagesRepresentative(coverProjection, quotientA);
  initialB := PreImagesRepresentative(coverProjection, quotientB);
  candidates := [];
  for correctionA in kernelElements do
    for correctionB in kernelElements do
      imageA := initialA * correctionA;
      imageB := initialB * correctionB;
      centralImages := [
        imageA^2,
        imageB^4,
        (imageA * imageB)^5,
        (imageA * imageB^2)^5
      ];
      if centralImages[1]^3 * centralImages[3]^-2 *
            centralImages[4] = One(coverGroup) and
          centralImages[2]^4 * centralImages[3]^3 *
            centralImages[4]^-3 = One(coverGroup) and
          Size(Group(imageA, imageB)) = Size(coverGroup) then
        Add(candidates, rec(
          imageA := imageA,
          imageB := imageB,
          centralImages := centralImages));
      fi;
    od;
  od;
  AuditAssertEqual(
    "the project Schur presentation does not have a unique lift alignment",
    Length(candidates),
    1);
  return candidates[1];
end;

# Construct the same six-generator fp presentation used in Lean and check
# that the selected assignment is an isomorphism onto GAP's Schur cover.
CheckSchurPresentationIsomorphism := function(
    coverGroup, presentationImages)
  local freeGroup, freeGenerators, relators, centralIndex, generatorIndex,
        presentedGroup, presentedGenerators, comparison;
  freeGroup := FreeGroup("a", "b", "k0", "k1", "k2", "k3");
  freeGenerators := GeneratorsOfGroup(freeGroup);
  relators := [
    freeGenerators[1]^2 * freeGenerators[3]^-1,
    freeGenerators[2]^4 * freeGenerators[4]^-1,
    (freeGenerators[1] * freeGenerators[2])^5 *
      freeGenerators[5]^-1,
    (freeGenerators[1] * freeGenerators[2]^2)^5 *
      freeGenerators[6]^-1,
    freeGenerators[3]^3 * freeGenerators[5]^-2 * freeGenerators[6],
    freeGenerators[4]^4 * freeGenerators[5]^3 * freeGenerators[6]^-3
  ];
  for centralIndex in [3 .. 6] do
    for generatorIndex in [1 .. 6] do
      Add(
        relators,
        Comm(freeGenerators[centralIndex], freeGenerators[generatorIndex]));
    od;
  od;
  presentedGroup := freeGroup / relators;
  presentedGenerators := GeneratorsOfGroup(presentedGroup);
  AuditAssertEqual(
    "the copied six-generator fp presentation has the wrong order",
    Size(presentedGroup),
    2160);
  comparison := GroupHomomorphismByImages(
    presentedGroup,
    coverGroup,
    presentedGenerators,
    Concatenation(
      [presentationImages.imageA, presentationImages.imageB],
      presentationImages.centralImages));
  AuditAssert(
    comparison <> fail and IsBijective(comparison),
    "the copied six-generator presentation is not isomorphic to the cover");
  return comparison;
end;

# The project's 360 noncentral states are its shortlex representatives in
# the alphabet [a,a^-1,b,b^-1].  Breadth-first insertion in that alphabet
# order reproduces the state enumeration.
ShortlexSchurEnumeration := function(
    quotientGroup, quotientA, quotientB, coverGroup, coverA, coverB,
    coverProjection)
  local quotientLetters, coverLetters, tokens, quotientElements,
        coverElements, words, queuePosition, letterIndex, quotientElement,
        coverElement;
  quotientLetters := [quotientA, quotientA^-1, quotientB, quotientB^-1];
  coverLetters := [coverA, coverA^-1, coverB, coverB^-1];
  tokens := [1, -1, 2, -2];
  quotientElements := [One(quotientGroup)];
  coverElements := [One(coverGroup)];
  words := [[]];
  queuePosition := 1;
  while Length(quotientElements) < Size(quotientGroup) do
    for letterIndex in [1 .. 4] do
      quotientElement :=
        quotientElements[queuePosition] * quotientLetters[letterIndex];
      if Position(quotientElements, quotientElement) = fail then
        coverElement :=
          coverElements[queuePosition] * coverLetters[letterIndex];
        Add(quotientElements, quotientElement);
        Add(coverElements, coverElement);
        Add(
          words,
          Concatenation(words[queuePosition], [tokens[letterIndex]]));
        AuditAssertEqual(
          "a shortlex cover word has the wrong quotient",
          Image(coverProjection, coverElement),
          quotientElement);
      fi;
    od;
    queuePosition := queuePosition + 1;
  od;
  AuditAssertEqual(
    "shortlex enumeration did not find all A6 elements",
    Length(quotientElements),
    360);
  return rec(
    quotientElements := quotientElements,
    coverElements := coverElements,
    words := words);
end;

# Return [zero-based shortlex state, exponent of k0].
SchurCoordinatesOfElement := function(
    enumeration, centralGenerator, element)
  local state, exponent;
  for state in [1 .. Length(enumeration.coverElements)] do
    for exponent in [0 .. 5] do
      if enumeration.coverElements[state] * centralGenerator^exponent =
          element then
        return [state - 1, exponent];
      fi;
    od;
  od;
  Error("an element was not found in the 360 x 6 Schur coordinates");
end;

ambientSimpleGroup := AlternatingGroup(6);
ambientAutomorphismGroup := AutomorphismGroup(ambientSimpleGroup);
ambientAutomorphismGenerators :=
  GeneratorsOfGroup(ambientAutomorphismGroup);

# These are GAP's standard representatives for the two named index-two
# extensions A6.2_1 and A6.2_2.
alpha1OnQuotient := ambientAutomorphismGenerators[3];
alpha2OnQuotient :=
  alpha1OnQuotient * ambientAutomorphismGenerators[4];

coverProjection := EpimorphismSchurCover(ambientSimpleGroup);
coverGroup := Source(coverProjection);
coverGenerators := GeneratorsOfGroup(coverGroup);

AuditAssertEqual("unexpected order for 6.A6", Size(coverGroup), 2160);
AuditAssertEqual(
  "unexpected kernel order for 6.A6 -> A6",
  Size(Kernel(coverProjection)),
  6);

alpha1Lifts := AllCentralLifts(
  coverGroup, coverProjection, alpha1OnQuotient);
alpha2Lifts := AllCentralLifts(
  coverGroup, coverProjection, alpha2OnQuotient);
AuditAssertEqual("alpha1 does not have a unique lift", Length(alpha1Lifts), 1);
AuditAssertEqual("alpha2 does not have a unique lift", Length(alpha2Lifts), 1);
alpha1OnCover := alpha1Lifts[1];
alpha2OnCover := alpha2Lifts[1];

centralGenerator := First(
  Elements(Center(coverGroup)),
  element -> Order(element) = 6);
AuditAssert(centralGenerator <> fail, "the cover center has no generator");
AuditAssertEqual(
  "alpha1 should invert the chosen central generator",
  Image(alpha1OnCover, centralGenerator),
  centralGenerator^5);
AuditAssertEqual(
  "alpha2 should invert the chosen central generator",
  Image(alpha2OnCover, centralGenerator),
  centralGenerator^5);
AuditAssertEqual(
  "the product of alpha1 and alpha2 should fix the center",
  Image(alpha1OnCover, Image(alpha2OnCover, centralGenerator)),
  centralGenerator);

# Align GAP's cover with the exact presentation and shortlex coordinate
# convention used by `AlternatingSixSchurCoordinates`.
projectQuotientA := (1,2)(3,4);
projectQuotientB := (1,2,3,5)(4,6);
presentationImages := CanonicalSchurPresentationImages(
  coverGroup, coverProjection, projectQuotientA, projectQuotientB);
presentationIsomorphism := CheckSchurPresentationIsomorphism(
  coverGroup, presentationImages);
AuditAssertEqual(
  "the selected a lift has the wrong quotient",
  Image(coverProjection, presentationImages.imageA),
  projectQuotientA);
AuditAssertEqual(
  "the selected b lift has the wrong quotient",
  Image(coverProjection, presentationImages.imageB),
  projectQuotientB);
AuditAssert(
  ForAll(
    presentationImages.centralImages,
    element -> element in Center(coverGroup)),
  "an advertised presentation relator value is not central");
AuditAssertEqual(
  "wrong powers of k0 for k0,k1,k2,k3",
  List(
    presentationImages.centralImages,
    element -> Position(
      List(
        [0 .. 5],
        exponent -> presentationImages.centralImages[1]^exponent),
      element) - 1),
  [1, 3, 5, 1]);

shortlexEnumeration := ShortlexSchurEnumeration(
  ambientSimpleGroup,
  projectQuotientA,
  projectQuotientB,
  coverGroup,
  presentationImages.imageA,
  presentationImages.imageB,
  coverProjection);
# Fingerprints against `alternatingSixRewriteNormalWords`.
AuditAssertEqual(
  "shortlex state 1 does not equal a",
  shortlexEnumeration.words[1 + 1],
  [1]);
AuditAssertEqual(
  "shortlex state 2 does not equal b",
  shortlexEnumeration.words[2 + 1],
  [2]);
AuditAssertEqual(
  "shortlex state 52 fingerprint changed",
  shortlexEnumeration.words[52 + 1],
  [1, 2, 1, -2, 1, -2]);
AuditAssertEqual(
  "shortlex state 63 fingerprint changed",
  shortlexEnumeration.words[63 + 1],
  [2, 1, -2, 1, 2, 1]);
AuditAssertEqual(
  "shortlex state 317 fingerprint changed",
  shortlexEnumeration.words[317 + 1],
  [2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1, 2]);

presentationGeneratorImages := Concatenation(
  [presentationImages.imageA, presentationImages.imageB],
  presentationImages.centralImages);
alpha1GeneratorCoordinates := List(
  presentationGeneratorImages,
  element -> SchurCoordinatesOfElement(
    shortlexEnumeration,
    presentationImages.centralImages[1],
    Image(alpha1OnCover, element)));
alpha2GeneratorCoordinates := List(
  presentationGeneratorImages,
  element -> SchurCoordinatesOfElement(
    shortlexEnumeration,
    presentationImages.centralImages[1],
    Image(alpha2OnCover, element)));
alpha2InverseGeneratorCoordinates := List(
  presentationGeneratorImages,
  element -> SchurCoordinatesOfElement(
    shortlexEnumeration,
    presentationImages.centralImages[1],
    Image(alpha2OnCover^-1, element)));
AuditAssertEqual(
  "wrong alpha1 presentation-generator coordinates",
  alpha1GeneratorCoordinates,
  [[1,2],[63,2],[0,5],[0,3],[0,1],[0,5]]);
AuditAssertEqual(
  "wrong alpha2 presentation-generator coordinates",
  alpha2GeneratorCoordinates,
  [[317,1],[52,4],[0,5],[0,3],[0,1],[0,5]]);
AuditAssertEqual(
  "wrong alpha2 inverse presentation-generator coordinates",
  alpha2InverseGeneratorCoordinates,
  [[355,2],[345,0],[0,5],[0,3],[0,1],[0,5]]);
AuditAssert(
  ForAll(
    presentationGeneratorImages,
    element ->
      Image(alpha1OnCover, Image(alpha1OnCover, element)) = element),
  "alpha1 is not involutive on the presentation generators");
AuditAssert(
  ForAll(
    presentationGeneratorImages,
    element ->
      Image(
        alpha2OnCover^-1,
        Image(alpha2OnCover, element)) = element),
  "the recorded alpha2 inverse is not a left inverse on the generators");
AuditAssert(
  ForAll(
    presentationGeneratorImages,
    element ->
      Image(
        alpha2OnCover,
        Image(alpha2OnCover^-1, element)) = element),
  "the recorded alpha2 inverse is not a right inverse on the generators");
AuditAssertEqual(
  "the chosen alpha1 representative should have order two",
  Order(alpha1OnCover),
  2);
AuditAssertEqual(
  "the chosen alpha2 representative should have order eight",
  Order(alpha2OnCover),
  8);

Print("\npresentation alpha1 generator coordinates: ",
  alpha1GeneratorCoordinates, "\n");
Print("presentation alpha2 generator coordinates: ",
  alpha2GeneratorCoordinates, "\n");
Print("presentation alpha2 inverse-generator coordinates: ",
  alpha2InverseGeneratorCoordinates, "\n\n");

coverAutomorphismGroup := AutomorphismGroup(coverGroup);
coverInnerAutomorphisms :=
  InnerAutomorphismsAutomorphismGroup(coverAutomorphismGroup);
AuditAssertEqual(
  "unexpected automorphism-group order", Size(coverAutomorphismGroup), 1440);
AuditAssertEqual(
  "unexpected inner-automorphism order", Size(coverInnerAutomorphisms), 360);

computedAmbientTable := CharacterTable(coverGroup);
storedAmbientTable := CharacterTable("6.A6");
computedQuotientTable := CharacterTable(ambientSimpleGroup);
storedQuotientTable := CharacterTable("A6");
ambientTransformation := TransformingPermutationsCharacterTables(
  computedAmbientTable, storedAmbientTable);
quotientTransformation := TransformingPermutationsCharacterTables(
  computedQuotientTable, storedQuotientTable);
AuditAssert(
  ambientTransformation <> fail and quotientTransformation <> fail,
  "failed to align a computed table with CTblLib");

computedQuotientFusion := FusionConjugacyClasses(
  coverProjection, computedAmbientTable, computedQuotientTable);
storedQuotientFusion := GetFusionMap(
  storedAmbientTable, storedQuotientTable);
ambientColumnAlignments := CompatibleColumnAlignments(
  computedAmbientTable,
  storedAmbientTable,
  computedQuotientTable,
  storedQuotientTable,
  computedQuotientFusion,
  storedQuotientFusion,
  quotientTransformation.columns);
AuditAssertEqual(
  "unexpected number of quotient-compatible ambient table alignments",
  Length(ambientColumnAlignments),
  4);

ambientComputedClassActions := List(
  [alpha1OnCover, alpha2OnCover],
  automorphism ->
    ClassPermutationFromAutomorphism(coverGroup, automorphism));
ambientComputedRowActions := List(
  ambientComputedClassActions,
  classPermutation ->
    RowPermutationFromClassPermutation(
      computedAmbientTable, classPermutation));

ambientClassActionSets := List(
  [1, 2],
  generatorIndex -> Set(List(
    ambientColumnAlignments,
    columns -> TransportedClassPermutation(
      ambientComputedClassActions[generatorIndex], columns))));
ambientRowActionSets := List(
  [1, 2],
  generatorIndex -> Set(List(
    ambientColumnAlignments,
    columns -> TransportedRowPermutation(
      computedAmbientTable,
      storedAmbientTable,
      ambientComputedRowActions[generatorIndex],
      columns))));
AuditAssert(
  ForAll(ambientClassActionSets, set -> Length(set) = 1),
  "ambient class action depends on a fusion-compatible table alignment");
AuditAssert(
  ForAll(ambientRowActionSets, set -> Length(set) = 1),
  "ambient row action depends on a fusion-compatible table alignment");

ambientClassActions := List(ambientClassActionSets, set -> set[1]);
ambientRowActions := List(ambientRowActionSets, set -> set[1]);
AuditAssertEqual(
  "wrong ambient alpha1 class action",
  ambientClassActions[1],
  (2,6)(3,5)(8,9)(14,17)(15,16)(18,19)(20,26)(21,31)(22,30)(23,29)
    (24,28)(25,27));
AuditAssertEqual(
  "wrong ambient alpha2 class action",
  ambientClassActions[2],
  (2,6)(3,5)(8,9)(10,12)(11,13)(15,19)(16,18)(21,25)(22,24)(27,31)
    (28,30));
AuditAssertEqual(
  "wrong ambient alpha1 row action",
  ambientRowActions[1],
  (4,5)(10,11)(12,13)(14,17)(15,16)(18,19)(20,21)(22,23)(24,27)
    (25,26)(28,31)(29,30));
AuditAssertEqual(
  "wrong ambient alpha2 row action",
  ambientRowActions[2],
  (2,3)(8,9)(14,15)(16,17)(18,19)(20,21)(22,23)(24,25)(26,27)
    (28,29)(30,31));

Print("ambient alpha1 class action: ", ambientClassActions[1], "\n");
Print("ambient alpha2 class action: ", ambientClassActions[2], "\n");
Print("ambient alpha1 row action:   ", ambientRowActions[1], "\n");
Print("ambient alpha2 row action:   ", ambientRowActions[2], "\n");

localCases := [
  rec(
    prime := 2,
    tableName := "6.A6N2",
    expectedClassActions := [
      (2,3)(5,6)(7,11)(8,12)(9,10)(13,14)(17,18)(19,20),
      (2,3)(5,6)(7,12)(8,11)(13,14)(16,21)(17,20)(18,19)
    ],
    expectedRowActions := [
      (5,6)(7,8)(9,10)(11,12)(14,15)(16,17)(18,20)(19,21),
      (2,3)(5,8)(6,7)(9,10)(11,12)(14,15)(18,21)(19,20)
    ],
    expectedPPrimeImages := [
      [1,2,3,4,6,5,8,7,10,9,12,11],
      [1,3,2,4,8,7,6,5,10,9,12,11]
    ],
    stabilizerOrder := 32,
    innerStabilizerOrder := 8,
    candidatePairs := [
      [1,1],[2,2],[3,3],[6,4],[14,6],[15,7],
      [16,8],[17,5],[20,10],[21,9],[22,12],[23,11]
    ]),
  rec(
    prime := 3,
    tableName := "6.A6M3",
    expectedClassActions := [
      (2,26)(3,4)(5,22)(6,7)(8,9)(14,16)(15,24)(17,21)(18,28)(19,20)
        (23,27),
      (2,6)(7,26)(8,27)(9,23)(10,12)(11,13)(15,20)(17,21)(18,28)(19,24)
    ],
    expectedRowActions := [
      (3,4)(5,6)(7,8)(9,15)(10,16)(11,13)(12,14)(17,20)(18,19)(21,22)
        (23,24),
      (9,13)(10,14)(11,15)(12,16)(17,19)(18,20)(21,22)(23,24)(25,27)
        (26,28)
    ],
    expectedPPrimeImages := [
      [1,2,4,3,6,5,8,7,25,26,27,28],
      [1,2,3,4,5,6,7,8,27,28,25,26]
    ],
    stabilizerOrder := 144,
    innerStabilizerOrder := 36,
    candidatePairs := [
      [1,1],[2,25],[3,27],[4,3],[5,4],[7,2],
      [8,26],[9,28],[10,5],[11,6],[12,7],[13,8]
    ]),
  rec(
    prime := 5,
    tableName := "3x2.D10",
    expectedClassActions := [
      (2,3)(5,6)(8,9)(11,12)(13,16)(14,18)(15,17)(19,22)(20,24)(21,23),
      (2,3)(4,7)(5,9)(6,8)(11,12)(14,15)(17,18)(20,21)(23,24)
    ],
    expectedRowActions := [
      (2,3)(5,6)(8,9)(11,12)(13,22)(14,24)(15,23)(16,19)(17,21)(18,20),
      (2,3)(5,6)(7,10)(8,12)(9,11)(14,15)(17,18)(20,21)(23,24)
    ],
    expectedPPrimeImages := [
      [1,3,2,4,6,5,7,9,8,10,12,11,22,24,23,19,21,20,16,18,17,13,15,14],
      [1,3,2,4,6,5,10,12,11,7,9,8,13,15,14,16,18,17,19,21,20,22,24,23]
    ],
    stabilizerOrder := 40,
    innerStabilizerOrder := 10,
    candidatePairs := [
      [1,1],[4,16],[5,19],[6,4],[8,7],[9,10],
      [10,13],[11,22],[14,17],[15,18],[16,20],[17,21],
      [18,2],[19,3],[20,5],[21,6],[24,8],[25,12],
      [26,11],[27,9],[28,14],[29,15],[30,23],[31,24]
    ])
];

AuditLocalCase := function(
    caseData, coverGroup, coverGenerators, coverAutomorphismGroup,
    coverInnerAutomorphisms, computedAmbientTable, storedAmbientTable,
    ambientColumnAlignment, coverActions, ambientRowActions)
  local sylowSubgroup, localNormalizer, computedLocalTable, storedLocalTable,
        computedLocalFusion, storedLocalFusion, localColumnAlignments,
        adjustedCoverActions, computedLocalClassActions,
        computedLocalRowActions, localClassActionSets, localRowActionSets,
        localClassActions, localRowActions, localPPrimeRows,
        sylowStabilizer, innerSylowStabilizer;
  sylowSubgroup := SylowSubgroup(coverGroup, caseData.prime);
  localNormalizer := Normalizer(coverGroup, sylowSubgroup);
  computedLocalTable := CharacterTable(localNormalizer);
  storedLocalTable := CharacterTable(caseData.tableName);
  computedLocalFusion := FusionConjugacyClasses(
    localNormalizer, coverGroup);
  storedLocalFusion := GetFusionMap(
    storedLocalTable, storedAmbientTable);

  localColumnAlignments := CompatibleColumnAlignments(
    computedLocalTable,
    storedLocalTable,
    computedAmbientTable,
    storedAmbientTable,
    computedLocalFusion,
    storedLocalFusion,
    ambientColumnAlignment);
  AuditAssertEqual(
    Concatenation(
      "unexpected number of fusion-compatible local alignments for p=",
      String(caseData.prime)),
    Length(localColumnAlignments),
    2);

  adjustedCoverActions := List(
    coverActions,
    automorphism -> AdjustAutomorphismToSylow(
      coverGroup, coverGenerators, automorphism, sylowSubgroup));
  computedLocalClassActions := List(
    adjustedCoverActions,
    automorphism ->
      ClassPermutationFromAutomorphism(localNormalizer, automorphism));
  computedLocalRowActions := List(
    computedLocalClassActions,
    classPermutation ->
      RowPermutationFromClassPermutation(
        computedLocalTable, classPermutation));

  localClassActionSets := List(
    [1, 2],
    generatorIndex -> Set(List(
      localColumnAlignments,
      columns -> TransportedClassPermutation(
        computedLocalClassActions[generatorIndex], columns))));
  localRowActionSets := List(
    [1, 2],
    generatorIndex -> Set(List(
      localColumnAlignments,
      columns -> TransportedRowPermutation(
        computedLocalTable,
        storedLocalTable,
        computedLocalRowActions[generatorIndex],
        columns))));
  AuditAssert(
    ForAll(localClassActionSets, set -> Length(set) = 1),
    Concatenation(
      "local class action depends on the table alignment for p=",
      String(caseData.prime)));
  AuditAssert(
    ForAll(localRowActionSets, set -> Length(set) = 1),
    Concatenation(
      "local row action depends on the table alignment for p=",
      String(caseData.prime)));

  localClassActions := List(localClassActionSets, set -> set[1]);
  localRowActions := List(localRowActionSets, set -> set[1]);
  AuditAssertEqual(
    Concatenation("wrong local class actions for p=", String(caseData.prime)),
    localClassActions,
    caseData.expectedClassActions);
  AuditAssertEqual(
    Concatenation("wrong local row actions for p=", String(caseData.prime)),
    localRowActions,
    caseData.expectedRowActions);

  localPPrimeRows := PPrimeRows(storedLocalTable, caseData.prime);
  AuditAssertEqual(
    Concatenation(
      "wrong local p-prime images for p=", String(caseData.prime)),
    List(
      localRowActions,
      action -> PPrimeImages(action, localPPrimeRows)),
    caseData.expectedPPrimeImages);

  sylowStabilizer := Stabilizer(
    coverAutomorphismGroup,
    sylowSubgroup,
    function(subgroup, automorphism)
      return Image(automorphism, subgroup);
    end);
  innerSylowStabilizer := Intersection(
    sylowStabilizer, coverInnerAutomorphisms);
  AuditAssertEqual(
    Concatenation(
      "wrong automorphism stabilizer order for p=", String(caseData.prime)),
    Size(sylowStabilizer),
    caseData.stabilizerOrder);
  AuditAssertEqual(
    Concatenation(
      "wrong inner stabilizer order for p=", String(caseData.prime)),
    Size(innerSylowStabilizer),
    caseData.innerStabilizerOrder);
  AuditAssertEqual(
    Concatenation(
      "the local outer stabilizer is not a four-group for p=",
      String(caseData.prime)),
    Size(sylowStabilizer) / Size(innerSylowStabilizer),
    4);

  CheckCandidateBijection(
    caseData,
    storedAmbientTable,
    storedLocalTable,
    ambientRowActions,
    localRowActions,
    storedLocalFusion);

  Print("\np=", caseData.prime, " table=", caseData.tableName, "\n");
  Print("  alpha1 class action: ", localClassActions[1], "\n");
  Print("  alpha2 class action: ", localClassActions[2], "\n");
  Print("  alpha1 row action:   ", localRowActions[1], "\n");
  Print("  alpha2 row action:   ", localRowActions[2], "\n");
  Print("  p-prime rows:        ", localPPrimeRows, "\n");
  Print("  candidate bijection: ", caseData.candidatePairs, "\n");
end;

for caseData in localCases do
  AuditLocalCase(
    caseData,
    coverGroup,
    coverGenerators,
    coverAutomorphismGroup,
    coverInnerAutomorphisms,
    computedAmbientTable,
    storedAmbientTable,
    ambientColumnAlignments[1],
    [alpha1OnCover, alpha2OnCover],
    ambientRowActions);
od;

Print(
  "\nAll group/table audits passed.\n",
  "HONESTY BOUNDARY: the copied Lean permutations remain finite CTblLib data;\n",
  "this script does not construct their realization by Lean automorphisms.\n");

QUIT_GAP(0);
