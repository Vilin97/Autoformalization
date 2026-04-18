#!/usr/bin/env python3
r"""Update \uses{} in content.tex based on extracted Lean dependency graph.

Reads the transitive dependency output from dep_graph_gv.lean and rewrites
the \uses{} lines in blueprint/src/content.tex to match.
"""

import re
import sys

# Mapping: Lean declaration name → blueprint label
LEAN_TO_LABEL = {
    "IsFlasqueSheaf": "def:isFlasqueSheaf",
    "isFlasque_of_injective": "lem:isFlasque_of_injective",
    "isFlasque_X₃_of_shortExact": "lem:isFlasque_X3_of_shortExact",
    "sheafH0EquivSections": "lem:sheafH0EquivSections",
    "ext_zero_map_surjective": "lem:ext_zero_map_surjective",
    "sheafH_dimension_shift": "lem:sheafH_dimension_shift",
    "FlasqueVanishing": "thm:FlasqueVanishing",
    "ext_dimension_shift": "lem:ext_dimension_shift",
    "ext_dimension_shift_X₃": "lem:ext_dimension_shift_X3",
    "closedIncl_pushforward_shortExact": "lem:closedIncl_pushforward_shortExact",
    "PushforwardHVanishing": "thm:PushforwardHVanishing",
    "TopCat.closedIncl_counit_isIso": "lem:closedIncl_counit_isIso",
    "epi_unit_of_closedImmersion": "lem:epi_unit_of_closedImmersion",
    "closedImmersionSES": "thm:closedImmersionSES",
    "opens_eq_bot_or_top_of_irreducibleSpace_dim_zero": "lem:opens_eq_bot_or_top",
    "topologicalKrullDim_nonneg": "lem:dim_nonneg_irreducible",
    "topologicalKrullDim_lt_of_isIrreducible_of_isClosed": "lem:dim_lt_of_closed",
    "TopCat.Presheaf.zeroOutside": "def:zeroOutside",
    "TopCat.Sheaf.zeroOutsideInt": "def:zeroOutsideInt",
    "TopCat.Sheaf.zeroOutsideInt.sHom": "def:sHom",
    "stalk_zeroOutsideInt_eq_zsmul_generator": "lem:stalk_zsmul_generator",
    "zsmul_generator_injective": "lem:zsmul_generator_injective",
    "constantSheaf_flasque_of_irreducible": "thm:constantSheaf_flasque",
    "sheaf_restriction_epi_of_irreducible_dim_zero": "lem:sheaf_restriction_epi_dim_zero",
    "grothendieck_vanishing_dim_zero": "thm:grothendieck_vanishing_dim_zero",
    "createsFilteredColimit": "thm:createsFilteredColimit",
    "sheafH_preserves_filtered_colimits": "thm:sheafH_preserves_filtered_colimits",
    "cohomology_vanishing_of_finitelyGenerated_vanishing": "thm:cohomology_vanishing_fg",
    "zeroOutsideInt_vanishing": "thm:zeroOutsideInt_vanishing",
    "zeroOutsideInt_cohomology_vanishing": "thm:zeroOutsideInt_cohomology_vanishing",
    "finsetGeneratedSheaf_vanishing": "thm:finsetGeneratedSheaf_vanishing",
    "directLimit_cohomology_vanishing": "thm:directLimit_cohomology_vanishing",
    "exists_closed_subset_lt_dim_of_irreducible_pos": "lem:exists_closed_subset",
    "exists_good_section": "lem:exists_good_section",
    "IrreduciblePosVanishing": "thm:IrreduciblePosVanishing",
    "ReducibleVanishing'": "thm:ReducibleVanishing",
    "grothendieck_vanishing_of_irreducible": "lem:grothendieck_vanishing_of_irreducible",
    "GrothendieckVanishing": "thm:GrothendieckVanishing",
}

LABEL_TO_LEAN = {v: k for k, v in LEAN_TO_LABEL.items()}

# Transitive dependencies extracted from Lean (paste from dep_graph_gv.lean output)
TRANSITIVE_DEPS = {
    "IsFlasqueSheaf": [],
    "isFlasque_of_injective": ["IsFlasqueSheaf"],
    "isFlasque_X₃_of_shortExact": ["IsFlasqueSheaf"],
    "sheafH0EquivSections": [],
    "ext_zero_map_surjective": ["IsFlasqueSheaf"],
    "sheafH_dimension_shift": [],
    "FlasqueVanishing": ["IsFlasqueSheaf", "ext_zero_map_surjective", "isFlasque_X₃_of_shortExact", "isFlasque_of_injective", "sheafH_dimension_shift"],
    "ext_dimension_shift": [],
    "ext_dimension_shift_X₃": [],
    "closedIncl_pushforward_shortExact": [],
    "PushforwardHVanishing": ["FlasqueVanishing", "IsFlasqueSheaf", "closedIncl_pushforward_shortExact", "isFlasque_of_injective", "sheafH0EquivSections"],
    "TopCat.closedIncl_counit_isIso": [],
    "epi_unit_of_closedImmersion": ["TopCat.closedIncl_counit_isIso"],
    "closedImmersionSES": ["epi_unit_of_closedImmersion"],
    "opens_eq_bot_or_top_of_irreducibleSpace_dim_zero": [],
    "topologicalKrullDim_nonneg": [],
    "topologicalKrullDim_lt_of_isIrreducible_of_isClosed": [],
    "TopCat.Presheaf.zeroOutside": [],
    "TopCat.Sheaf.zeroOutsideInt": ["TopCat.Presheaf.zeroOutside"],
    "TopCat.Sheaf.zeroOutsideInt.sHom": ["TopCat.Presheaf.zeroOutside", "TopCat.Sheaf.zeroOutsideInt"],
    "stalk_zeroOutsideInt_eq_zsmul_generator": ["TopCat.Presheaf.zeroOutside", "TopCat.Sheaf.zeroOutsideInt"],
    "zsmul_generator_injective": ["TopCat.Presheaf.zeroOutside", "TopCat.Sheaf.zeroOutsideInt"],
    "constantSheaf_flasque_of_irreducible": [],
    "sheaf_restriction_epi_of_irreducible_dim_zero": ["opens_eq_bot_or_top_of_irreducibleSpace_dim_zero"],
    "grothendieck_vanishing_dim_zero": ["FlasqueVanishing", "sheaf_restriction_epi_of_irreducible_dim_zero"],
    "createsFilteredColimit": [],
    "sheafH_preserves_filtered_colimits": ["FlasqueVanishing", "IsFlasqueSheaf", "createsFilteredColimit", "ext_dimension_shift", "ext_dimension_shift_X₃", "isFlasque_of_injective", "sheafH0EquivSections"],
    "cohomology_vanishing_of_finitelyGenerated_vanishing": ["TopCat.Presheaf.zeroOutside", "TopCat.Sheaf.zeroOutsideInt", "TopCat.Sheaf.zeroOutsideInt.sHom", "sheafH_preserves_filtered_colimits"],
    "zeroOutsideInt_vanishing": ["FlasqueVanishing", "IsFlasqueSheaf", "TopCat.Presheaf.zeroOutside", "TopCat.Sheaf.zeroOutsideInt", "constantSheaf_flasque_of_irreducible"],
    "zeroOutsideInt_cohomology_vanishing": ["PushforwardHVanishing", "TopCat.Presheaf.zeroOutside", "TopCat.Sheaf.zeroOutsideInt", "TopCat.closedIncl_counit_isIso", "epi_unit_of_closedImmersion", "topologicalKrullDim_lt_of_isIrreducible_of_isClosed", "zeroOutsideInt_vanishing"],
    "finsetGeneratedSheaf_vanishing": ["TopCat.Sheaf.zeroOutsideInt", "TopCat.Sheaf.zeroOutsideInt.sHom"],
    "directLimit_cohomology_vanishing": ["TopCat.Sheaf.zeroOutsideInt", "cohomology_vanishing_of_finitelyGenerated_vanishing", "finsetGeneratedSheaf_vanishing"],
    "exists_closed_subset_lt_dim_of_irreducible_pos": ["topologicalKrullDim_lt_of_isIrreducible_of_isClosed"],
    "exists_good_section": ["TopCat.Presheaf.zeroOutside", "TopCat.Sheaf.zeroOutsideInt", "TopCat.Sheaf.zeroOutsideInt.sHom", "stalk_zeroOutsideInt_eq_zsmul_generator", "zsmul_generator_injective"],
    "IrreduciblePosVanishing": ["closedImmersionSES", "PushforwardHVanishing", "TopCat.Presheaf.zeroOutside", "TopCat.Sheaf.zeroOutsideInt", "TopCat.Sheaf.zeroOutsideInt.sHom", "TopCat.closedIncl_counit_isIso", "directLimit_cohomology_vanishing", "epi_unit_of_closedImmersion", "exists_closed_subset_lt_dim_of_irreducible_pos", "exists_good_section", "topologicalKrullDim_lt_of_isIrreducible_of_isClosed", "zeroOutsideInt_cohomology_vanishing"],
    "ReducibleVanishing'": ["PushforwardHVanishing", "TopCat.closedIncl_counit_isIso", "epi_unit_of_closedImmersion"],
    "grothendieck_vanishing_of_irreducible": ["ReducibleVanishing'"],
    "GrothendieckVanishing": ["IrreduciblePosVanishing", "grothendieck_vanishing_dim_zero", "grothendieck_vanishing_of_irreducible", "topologicalKrullDim_nonneg"],
}

def lean_deps_to_labels(lean_name):
    """Convert transitive Lean deps to blueprint labels."""
    deps = TRANSITIVE_DEPS.get(lean_name, [])
    labels = []
    for d in deps:
        if d in LEAN_TO_LABEL:
            labels.append(LEAN_TO_LABEL[d])
    return sorted(labels)


def update_content(filepath):
    with open(filepath) as f:
        content = f.read()

    # For each \lean{...} block, find the corresponding \uses{} and update it
    # Pattern: we look for blocks of the form:
    #   \lean{NAME}
    #   \leanok
    #   \uses{...}   (may or may not exist)

    # Build a map: for each \lean{NAME} position, what are the correct \uses labels?
    lean_pattern = re.compile(r'\\lean\{([^}]+)\}')

    lines = content.split('\n')
    new_lines = []
    i = 0
    while i < len(lines):
        line = lines[i]
        lean_match = lean_pattern.search(line)
        if lean_match:
            lean_name = lean_match.group(1)
            labels = lean_deps_to_labels(lean_name)
            new_lines.append(line)
            i += 1

            # Check if next line is \leanok
            if i < len(lines) and '\\leanok' in lines[i]:
                new_lines.append(lines[i])
                i += 1

                # Check if next line is \uses{...}
                if i < len(lines) and '\\uses{' in lines[i]:
                    # Replace it with the correct \uses
                    if labels:
                        indent = re.match(r'(\s*)', lines[i]).group(1)
                        new_lines.append(f'{indent}\\uses{{{", ".join(labels)}}}')
                    # else: remove the \uses line (no deps)
                    i += 1
                else:
                    # No \uses line exists — add one if there are deps
                    if labels:
                        # Use same indent as \leanok line
                        indent = re.match(r'(\s*)', new_lines[-1]).group(1)
                        new_lines.append(f'{indent}\\uses{{{", ".join(labels)}}}')
        else:
            new_lines.append(line)
            i += 1

    result = '\n'.join(new_lines)

    with open(filepath, 'w') as f:
        f.write(result)

    # Print summary of changes
    print("Updated \\uses{} based on extracted Lean dependencies.")
    print(f"\nDeclarations with dependencies:")
    for lean_name in sorted(TRANSITIVE_DEPS.keys()):
        labels = lean_deps_to_labels(lean_name)
        if labels:
            print(f"  {lean_name}: {', '.join(labels)}")


if __name__ == '__main__':
    update_content('blueprint/src/content.tex')
